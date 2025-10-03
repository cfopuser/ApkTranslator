# -*- coding: utf-8 -*-

# --- Imports ---
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext, OptionMenu, StringVar, Checkbutton, BooleanVar, Toplevel, Text, Label, ttk
import subprocess
import os
import shutil
import xml.etree.ElementTree as ET
import threading
import configparser
import google.generativeai as genai
import sys
import time
import requests
from urllib3.exceptions import InsecureRequestWarning
import logging
from enum import Enum, auto

# --- Constants ---
BATCH_SIZE = 100
XML_SEPARATOR = "\n---\n"
API_MAX_RETRIES = 3
API_RATE_LIMIT_WAIT_SEC = 60
CONFIG_FILE_NAME = "config.ini"
LOG_FILE_NAME = "apk_translator.log"
APP_TITLE = "APK Translator v17.1 (Robust & Responsive)"

# --- Application State Definition ---
class AppState(Enum):
    INITIAL = auto()
    APK_SELECTED = auto()
    DECOMPILED = auto()
    STRINGS_EXTRACTED = auto()
    TRANSLATION_COMPLETE = auto()
    SAVED = auto()
    RECOMPILED = auto()

# --- Professional Logging Setup ---
class TkinterLogHandler(logging.Handler):
    """Custom logging handler to redirect logs to a tkinter Text widget."""
    def __init__(self, text_widget):
        logging.Handler.__init__(self)
        self.text_widget = text_widget

    def emit(self, record):
        msg = self.format(record)
        self.text_widget.config(state=tk.NORMAL)
        self.text_widget.insert(tk.END, msg + "\n")
        self.text_widget.see(tk.END)
        self.text_widget.config(state=tk.DISABLED)
        self.text_widget.update_idletasks()

def setup_logging(log_widget):
    """Configures both file and GUI logging."""
    log_format = '%(asctime)s - %(levelname)s - %(message)s'
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)

    if logger.hasHandlers():
        logger.handlers.clear()

    file_handler = logging.FileHandler(LOG_FILE_NAME, mode='w', encoding='utf-8')
    file_handler.setFormatter(logging.Formatter(log_format))
    logger.addHandler(file_handler)

    gui_handler = TkinterLogHandler(log_widget)
    gui_handler.setFormatter(logging.Formatter(log_format))
    logger.addHandler(gui_handler)
    return logger

# --- Secure API Call Wrapper ---
original_request = requests.sessions.Session.request

def safe_api_call(func, *args, **kwargs):
    """A thread-safe wrapper to display message boxes from worker threads."""
    try:
        return func(*args, **kwargs)
    except Exception as e:
        logging.error(f"An unexpected error occurred in worker thread: {e}", exc_info=True)
        root.after(0, lambda: messagebox.showerror("שגיאה קריטית בתהליכון", f"אירעה שגיאה בלתי צפויה:\n{e}"))
        return None

def translate_text_with_ai(xml_snippets_text, api_key, model_name):
    """
    Sends a batch of XML snippets to the AI for translation.
    Includes retry logic for rate limiting and timeouts.
    """
    if not xml_snippets_text or xml_snippets_text.isspace():
        return ""

    genai.configure(api_key=api_key, transport='rest')
    model = genai.GenerativeModel(model_name)
    prompt = f"""You are an expert XML translator for Android apps. Your task is to translate the text content within a batch of <string> tags from English to Hebrew.

**CRITICAL INSTRUCTIONS:**
1.  **Translate UI Text Only:** Only translate strings that are clearly user-interface text (e.g., button labels, messages, titles). Do NOT translate strings that look like code, placeholders, or format specifiers (e.g., \"%1$s\", \"auth_token_error\", \"https://...\"). If a string should not be translated, return it unchanged.
2.  **Preserve XML Structure:** You MUST preserve the XML structure, including the `name` attribute and all other attributes, exactly as they are.
3.  **Strict Output Format:** The input is a list of XML tags separated by '{XML_SEPARATOR}'. Your output MUST be ONLY the translated XML tags, also separated by the same '{XML_SEPARATOR}' separator. Do not add any explanations, introductory text, or XML declarations.

**EXAMPLE INPUT:**
<string name=\"app_name\">My App</string>
{XML_SEPARATOR}
<string name=\"account_sync_interval\" translatable=\"false\">3600</string>
{XML_SEPARATOR}
<string name=\"welcome_message\">Welcome, %1$s!</string>

**EXAMPLE OUTPUT:**
<string name=\"app_name\">האפליקציה שלי</string>
{XML_SEPARATOR}
<string name=\"account_sync_interval\" translatable=\"false\">3600</string>
{XML_SEPARATOR}
<string name=\"welcome_message\">ברוך הבא, %1$s!</string>

Now, translate the following batch:
{xml_snippets_text}"""

    for attempt in range(API_MAX_RETRIES):
        try:
            response = model.generate_content(prompt)
            return response.text.strip()
        # --- שינוי: הוספת טיפול בשגיאות Timeout ---
        except (requests.exceptions.ReadTimeout, requests.exceptions.ConnectionError) as e:
            logging.error(f"API call failed on attempt {attempt + 1} with a network error: {type(e).__name__}", exc_info=True)
            if attempt < API_MAX_RETRIES - 1:
                logging.warning(f"Retrying after {API_RATE_LIMIT_WAIT_SEC} seconds...")
                time.sleep(API_RATE_LIMIT_WAIT_SEC)
                continue
            else:
                return f"ERROR_TIMEOUT: {str(e)}"
        except Exception as e:
            logging.error(f"API call failed on attempt {attempt + 1}", exc_info=True)
            error_str = str(e).lower()
            if "resource_exhausted" in error_str or "rate limit" in error_str:
                if attempt < API_MAX_RETRIES - 1:
                    logging.warning(f"Rate limit exceeded. Waiting {API_RATE_LIMIT_WAIT_SEC} seconds...")
                    time.sleep(API_RATE_LIMIT_WAIT_SEC)
                    continue
                else:
                     return "ERROR_RATE_LIMIT"
            else:
                return f"ERROR_UNEXPECTED: {str(e)}"
    return "ERROR_MAX_RETRIES_REACHED"


# --- Main Application Class ---
class APKTranslatorApp:
    def __init__(self, root):
        self.root = root
        self.root.title(APP_TITLE)
        self.root.geometry("900x950")

        self._define_paths()
        self._init_state_vars()
        self._setup_gui()
        self._post_init_tasks()

    def _define_paths(self):
        if getattr(sys, 'frozen', False) and hasattr(sys, '_MEIPASS'):
            self.bundle_dir = sys._MEIPASS
            self.executable_dir = os.path.dirname(sys.executable)
        else:
            self.bundle_dir = os.path.dirname(os.path.abspath(__file__))
            self.executable_dir = self.bundle_dir

        java_executable = "java.exe" if os.name == 'nt' else "java"
        self.java_path = os.path.join(self.bundle_dir, "jre", "bin", java_executable)
        self.apktool_path = os.path.join(self.bundle_dir, "apktool.jar")
        self.apksigner_path = os.path.join(self.bundle_dir, "apksigner.jar")
        self.config_file = os.path.join(self.executable_dir, CONFIG_FILE_NAME)
        self.work_dir = os.path.join(self.executable_dir, "apk_temp_work")

    def _init_state_vars(self):
        self.dependencies_ok = False
        self.apk_path = None
        self.decompiled_dir = None
        self.original_strings_xml_path = None
        self.unsigned_apk_path = None
        self.xml_tree = None
        self.xml_root = None
        self.config = configparser.ConfigParser()
        self.expert_mode = BooleanVar(value=False)
        self.overwrite_original = BooleanVar(value=False)
        self.progress_text = StringVar()
        self.current_state = None
        
        # SSL Security State
        self.ssl_option = StringVar(value="secure")
        self.ssl_custom_cert_path = StringVar()

    def _setup_gui(self):
        self.main_frame = tk.Frame(self.root, padx=10, pady=10)
        self.main_frame.pack(fill=tk.BOTH, expand=True)

        # --- API Settings ---
        api_frame = tk.LabelFrame(self.main_frame, text="הגדרות Gemini API")
        api_frame.pack(fill=tk.X, pady=5)
        
        api_key_frame = tk.Frame(api_frame)
        api_key_frame.pack(fill=tk.X, padx=5, pady=2)
        tk.Label(api_key_frame, text="API Key:").pack(side=tk.LEFT, padx=(0, 5))
        self.api_key_entry = tk.Entry(api_key_frame, width=50, show="*")
        self.api_key_entry.pack(side=tk.LEFT, expand=True, fill=tk.X)
        tk.Button(api_key_frame, text="הדבק", command=self.paste_api_key).pack(side=tk.LEFT, padx=(5, 2))
        self.save_key_btn = tk.Button(api_key_frame, text="שמור וטען מודלים", command=self.save_and_fetch_models)
        self.save_key_btn.pack(side=tk.LEFT, padx=(0, 5))
        
        model_frame = tk.Frame(api_frame)
        model_frame.pack(fill=tk.X, padx=5, pady=2)
        tk.Label(model_frame, text="Model:").pack(side=tk.LEFT, padx=(0, 5))
        self.selected_model = StringVar(self.root)
        self.selected_model.set("טען מפתח API תחילה...")
        self.model_menu = OptionMenu(model_frame, self.selected_model, "")
        self.model_menu.config(state=tk.DISABLED)
        self.model_menu.pack(side=tk.LEFT, expand=True, fill=tk.X)

        # --- SSL Security Settings ---
        ssl_frame = tk.LabelFrame(self.main_frame, text="הגדרות אבטחה (SSL)")
        ssl_frame.pack(fill=tk.X, pady=5)
        
        tk.Radiobutton(ssl_frame, text="מאובטח (מומלץ)", variable=self.ssl_option, value="secure").pack(anchor=tk.W)
        tk.Radiobutton(ssl_frame, text="אפשר חיבור לא מאובטח (מסוכן)", variable=self.ssl_option, value="insecure").pack(anchor=tk.W)
        
        custom_cert_frame = tk.Frame(ssl_frame)
        custom_cert_frame.pack(fill=tk.X)
        tk.Radiobutton(custom_cert_frame, text="שימוש בתעודה מותאמת אישית:", variable=self.ssl_option, value="custom").pack(side=tk.LEFT)
        self.cert_path_entry = tk.Entry(custom_cert_frame, textvariable=self.ssl_custom_cert_path)
        self.cert_path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        tk.Button(custom_cert_frame, text="בחר קובץ...", command=self.select_cert_file).pack(side=tk.LEFT)
        
        # --- Workflow ---
        workflow_frame = tk.LabelFrame(self.main_frame, text="שלבי עבודה")
        workflow_frame.pack(fill=tk.X, pady=10)
        
        self.step1_btn = tk.Button(workflow_frame, text="1. בחר קובץ APK...", command=self.run_step1_select_apk)
        self.step1_btn.pack(fill=tk.X, padx=5, pady=2)

        step2_frame = tk.Frame(workflow_frame)
        step2_frame.pack(fill=tk.X, padx=5, pady=2)
        self.step2_btn = tk.Button(step2_frame, text="2. בצע דיקומפילציה", command=self.run_step2_decompile)
        self.step2_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 5))
        self.step2b_btn = tk.Button(step2_frame, text="או בחר תיקייה קיימת...", command=self.run_step2_decompile)
        self.step2b_btn.pack(side=tk.LEFT, expand=True, fill=tk.X)
        
        self.step3_btn = tk.Button(workflow_frame, text="3. חלץ קובץ strings.xml", command=self.run_step3_extract_strings)
        self.step3_btn.pack(fill=tk.X, padx=5, pady=2)

        self.step4_frame = tk.Frame(workflow_frame)
        self.step4_frame.pack(fill=tk.X, padx=5, pady=2)
        self.step4a_btn = tk.Button(self.step4_frame, text="4a. תרגם באצווה (מהיר)", command=self.run_step4_translate)
        self.step4a_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)

        step5_frame = tk.Frame(workflow_frame)
        step5_frame.pack(fill=tk.X, padx=5, pady=2)
        self.step5_btn = tk.Button(step5_frame, text="5. שמור קובץ מתורגם", command=self.run_step5_save_translated)
        self.step5_btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 5))
        self.overwrite_check = Checkbutton(step5_frame, text="החלף את strings.xml המקורי", variable=self.overwrite_original)
        self.overwrite_check.pack(side=tk.LEFT)
        
        self.step6_btn = tk.Button(workflow_frame, text="6. קמפל את ה-APK מחדש", command=self.run_step6_recompile)
        self.step6_btn.pack(fill=tk.X, padx=5, pady=2)
        
        self.step7_btn = tk.Button(workflow_frame, text="7. חתום על ה-APK המקומפל", command=self.run_step7_sign)
        self.step7_btn.pack(fill=tk.X, padx=5, pady=2)

        expert_frame = tk.Frame(workflow_frame)
        expert_frame.pack(fill=tk.X, padx=5, pady=3)
        self.expert_mode_check = Checkbutton(expert_frame, text="בטל נעילת שלבים (מצב מומחה)", variable=self.expert_mode, command=self.toggle_expert_mode)
        self.expert_mode_check.pack(side=tk.LEFT)

        progress_frame = tk.Frame(self.main_frame)
        progress_frame.pack(fill=tk.X, padx=5, pady=(5, 0))
        self.progress_bar = ttk.Progressbar(progress_frame, orient='horizontal', mode='determinate')
        self.progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.progress_label = Label(progress_frame, textvariable=self.progress_text, width=15, anchor='e')
        self.progress_label.pack(side=tk.RIGHT, padx=(5, 0))
        
        self.editor_frame = tk.LabelFrame(self.main_frame, text="עורך strings.xml")
        self.editor_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        self.text_editor = scrolledtext.ScrolledText(self.editor_frame, wrap=tk.WORD)
        self.text_editor.pack(fill=tk.BOTH, expand=True)
        
        self.log_frame = tk.LabelFrame(self.main_frame, text="לוג פעולות")
        self.log_frame.pack(fill=tk.X, pady=5)
        self.log_text_widget = scrolledtext.ScrolledText(self.log_frame, height=8, wrap=tk.WORD, state=tk.DISABLED)
        self.log_text_widget.pack(fill=tk.X, expand=True)

    def _post_init_tasks(self):
        self.logger = setup_logging(self.log_text_widget)
        self.load_config()
        self.set_state(AppState.INITIAL)
        self.root.after(100, self.check_dependencies_silently)
    
    def set_state(self, new_state: AppState):
        self.current_state = new_state
        self.logger.info(f"Application state changed to: {new_state.name}")
        self._update_ui_for_state()

    def _update_ui_for_state(self):
        buttons = [self.step2_btn, self.step2b_btn, self.step3_btn, self.step4a_btn,
                   self.step5_btn, self.step6_btn, self.step7_btn]
        for btn in buttons:
            btn.config(state=tk.DISABLED)

        if self.expert_mode.get():
            for btn in buttons:
                btn.config(state=tk.NORMAL)
            return

        state_map = {
            AppState.INITIAL: [],
            AppState.APK_SELECTED: [self.step2_btn, self.step2b_btn],
            AppState.DECOMPILED: [self.step3_btn],
            AppState.STRINGS_EXTRACTED: [self.step4a_btn],
            AppState.TRANSLATION_COMPLETE: [self.step5_btn],
            AppState.SAVED: [self.step6_btn],
            AppState.RECOMPILED: [self.step7_btn],
        }
        
        if self.current_state in state_map:
            for btn in state_map[self.current_state]:
                btn.config(state=tk.NORMAL)

    def toggle_expert_mode(self):
        self.logger.info(f"מצב מומחה {'הופעל' if self.expert_mode.get() else 'בוטל'}.")
        self._update_ui_for_state()

    def select_cert_file(self):
        filepath = filedialog.askopenfilename(title="בחר קובץ תעודת אבטחה", filetypes=[("PEM files", "*.pem"), ("All files", "*.*")])
        if filepath:
            self.ssl_custom_cert_path.set(filepath)
            self.ssl_option.set("custom")

    def _apply_ssl_configuration(self):
        requests.sessions.Session.request = original_request
        requests.packages.urllib3.disable_warnings(InsecureRequestWarning)
        
        option = self.ssl_option.get()
        if option == "insecure":
            self.logger.warning("SSL verification is DISABLED. This is insecure.")
            def insecure_request(self, method, url, **kwargs):
                kwargs['verify'] = False
                return original_request(self, method, url, **kwargs)
            requests.sessions.Session.request = insecure_request
        elif option == "custom":
            cert_path = self.ssl_custom_cert_path.get()
            if os.path.exists(cert_path):
                self.logger.info(f"Using custom SSL certificate: {cert_path}")
                def custom_cert_request(self, method, url, **kwargs):
                    kwargs['verify'] = cert_path
                    return original_request(self, method, url, **kwargs)
                requests.sessions.Session.request = custom_cert_request
            else:
                self.logger.error(f"Custom certificate file not found: {cert_path}. Reverting to secure default.")
                self.root.after(0, lambda: messagebox.showerror("שגיאת תעודה", f"קובץ התעודה לא נמצא בנתיב:\n{cert_path}\nחוזר למצב מאובטח."))
        else:
            self.logger.info("Using secure SSL verification (system default).")

    def run_in_thread(self, target_func, *args):
        thread = threading.Thread(target=safe_api_call, args=(target_func, *args))
        thread.daemon = True
        thread.start()

    def run_step1_select_apk(self):
        source_apk_path = filedialog.askopenfilename(title="בחר קובץ APK", filetypes=[("Android Package", "*.apk")])
        if not source_apk_path: return
        try:
            if os.path.isdir(self.work_dir): shutil.rmtree(self.work_dir)
            os.makedirs(self.work_dir, exist_ok=True)
            apk_filename = os.path.basename(source_apk_path)
            self.apk_path = os.path.join(self.work_dir, apk_filename)
            shutil.copy(source_apk_path, self.apk_path)
            self.logger.info(f"שלב 1: קובץ הועתק לתיקיית העבודה: {self.apk_path}")
            self.set_state(AppState.APK_SELECTED)
        except Exception as e:
            self.logger.error("Failed to copy APK file.", exc_info=True)
            messagebox.showerror("שגיאה", f"לא ניתן להעתיק את הקובץ.\n{e}")

    def run_step2_decompile(self):
        if not self._ensure_dependencies_ok(): return
        if not self.apk_path: messagebox.showerror("שגיאה", "יש לבחור קובץ APK תחילה (שלב 1)."); return
        self.run_in_thread(self._worker_decompile)

    def _worker_decompile(self):
        self.logger.info("שלב 2: מתחיל דיקומפילציה...")
        apk_name = os.path.basename(self.apk_path); decompiled_name = os.path.splitext(apk_name)[0]
        self.decompiled_dir = os.path.join(self.work_dir, decompiled_name)
        if os.path.isdir(self.decompiled_dir): shutil.rmtree(self.decompiled_dir)
        decompile_cmd = [self.java_path, "-jar", self.apktool_path, "d", self.apk_path, "-f", "-o", self.decompiled_dir]
        if self.run_command(decompile_cmd):
            self.logger.info("שלב 2: דיקומפילציה הושלמה.")
            self.root.after(0, lambda: self.set_state(AppState.DECOMPILED))
        else: self.logger.error("שלב 2: דיקומפילציה נכשלה.")

    def run_step3_extract_strings(self):
        if not self.decompiled_dir or not os.path.isdir(self.decompiled_dir): messagebox.showerror("שגיאה", "יש לבחור תיקייה תחילה (שלב 2)."); return
        self.run_in_thread(self._worker_extract_strings)

    def _worker_extract_strings(self):
        self.logger.info("שלב 3: מחפש וטוען strings.xml...")
        self.original_strings_xml_path = os.path.join(self.decompiled_dir, "res", "values", "strings.xml")
        if not os.path.exists(self.original_strings_xml_path):
            self.logger.error("קובץ strings.xml לא נמצא."); 
            self.root.after(0, lambda: messagebox.showerror("שגיאה", "לא נמצא קובץ strings.xml."))
            return
        try:
            self.xml_tree = ET.parse(self.original_strings_xml_path); self.xml_root = self.xml_tree.getroot()
            xml_content = ET.tostring(self.xml_root, encoding='unicode', method='xml')
            self.root.after(0, self.update_editor, xml_content)
            self.logger.info("שלב 3: הקובץ נטען בהצלחה לעורך.")
            self.root.after(0, lambda: self.set_state(AppState.STRINGS_EXTRACTED))
        except Exception as e: 
            self.logger.error("Failed to parse strings.xml.", exc_info=True)
            self.root.after(0, lambda e=e: messagebox.showerror("שגיאת XML", f"לא ניתן היה לפענח את קובץ ה-XML.\n{e}"))
            
    def run_step4_translate(self):
        if self.xml_root is None: messagebox.showerror("שגיאה", "יש לחלץ קובץ strings.xml תחילה."); return
        api_key = self.api_key_entry.get(); model_name = self.selected_model.get()
        if not api_key or "טען" in model_name: messagebox.showerror("שגיאה", "חובה להזין מפתח API ולבחור מודל."); return
        
        self.step4a_btn.config(state=tk.DISABLED)
        self.run_in_thread(self._worker_translate, api_key, model_name)

    def _get_translatable_strings(self):
        return [tag for tag in self.xml_root.findall('string') if tag.text and not ('%' in tag.text and ('s' in tag.text or 'd' in tag.text))]

    def _update_tags_from_response(self, original_tags, translated_xml_response):
        split_translations = translated_xml_response.split(XML_SEPARATOR)
        if len(split_translations) != len(original_tags):
            self.logger.error(f"Mismatch: Model returned {len(split_translations)} items, but {len(original_tags)} were sent.")
            self.root.after(0, lambda: messagebox.showerror("שגיאת API", "המודל החזיר מספר שונה של תרגומים מהמקור."))
            return False

        for original_tag, translated_xml in zip(original_tags, split_translations):
            try:
                translated_tag = ET.fromstring(translated_xml.strip())
                original_tag.text = translated_tag.text
            except ET.ParseError:
                self.logger.warning(f"Skipping due to malformed XML from API: {translated_xml[:100]}")
                original_tag.text = f"TRANSLATION_ERROR: {original_tag.text}"
        return True

    def _worker_translate(self, api_key, model_name):
        self.logger.info("שלב 4: מתחיל תרגום מהיר באצוות...")
        self._apply_ssl_configuration()
        
        strings_to_translate = self._get_translatable_strings()
        if not strings_to_translate:
            self.logger.info("לא נמצאו מחרוזות לתרגום."); 
            self.root.after(0, self.step4a_btn.config, {'state': tk.NORMAL})
            return

        total_strings = len(strings_to_translate)
        self.root.after(0, lambda: self.progress_bar.config(maximum=total_strings))
        self.root.after(0, lambda t=total_strings: self.progress_text.set(f"0 / {t}"))
        
        all_xml_snippets = [ET.tostring(tag, encoding='unicode').strip() for tag in strings_to_translate]
        translated_count = 0

        for i in range(0, total_strings, BATCH_SIZE):
            batch_tags = strings_to_translate[i:i + BATCH_SIZE]
            batch_xml_snippets = all_xml_snippets[i:i + BATCH_SIZE]
            
            start_num, end_num = i + 1, min(i + BATCH_SIZE, total_strings)
            self.logger.info(f"מתרגם אצווה ({start_num}-{end_num} / {total_strings})...")
            
            combined_text = XML_SEPARATOR.join(batch_xml_snippets)
            combined_translation = translate_text_with_ai(combined_text, api_key, model_name)

            if "ERROR_" in combined_translation:
                self.logger.error(f"שגיאה קריטית בתרגום האצווה: {combined_translation}")
                self.root.after(0, lambda ct=combined_translation: messagebox.showerror("שגיאת API", f"לא ניתן היה לתרגם אצווה.\nהשגיאה: {ct}"))
                self.root.after(0, self._update_ui_for_state)
                return

            if not self._update_tags_from_response(batch_tags, combined_translation):
                self.root.after(0, self._update_ui_for_state)
                return

            translated_count += len(batch_tags)
            self.root.after(0, lambda v=translated_count: self.progress_bar.config(value=v))
            self.root.after(0, lambda v=translated_count, t=total_strings: self.progress_text.set(f"{v} / {t}"))
            
            # --- שינוי: עדכון חלון העורך אחרי כל אצווה מוצלחת ---
            self.root.after(0, self.update_editor_from_root)

        # self.root.after(0, self.update_editor_from_root) # כבר לא נחוץ כאן
        self.logger.info(f"שלב 4: תרגום באצוות הושלם. {translated_count} מחרוזות עובדו.")
        self.root.after(0, lambda: self.progress_text.set("הושלם!"))
        self.root.after(0, lambda: self.set_state(AppState.TRANSLATION_COMPLETE))

    def run_step5_save_translated(self):
        if not self.decompiled_dir: messagebox.showerror("שגיאה", "אין תיקיית עבודה (שלב 2)."); return
        self.run_in_thread(self._worker_save_translated)

    def _worker_save_translated(self):
        edited_content = self.text_editor.get("1.0", tk.END)

        self.logger.info("שלב 5: שומר את הקובץ המתורגם...")
        try:
            if self.overwrite_original.get():
                if not self.original_strings_xml_path: self.logger.error("לא ידוע מיקום הקובץ המקורי."); return
                save_path = self.original_strings_xml_path; self.logger.info(f"מצב החלפה: הקובץ יישמר ב-{save_path}")
            else:
                hebrew_values_dir = os.path.join(self.decompiled_dir, "res", "values-he-rIL")
                os.makedirs(hebrew_values_dir, exist_ok=True)
                save_path = os.path.join(hebrew_values_dir, "strings.xml"); self.logger.info(f"מצב יצירה: הקובץ יישמר ב-{save_path}")
            
            with open(save_path, 'w', encoding='utf-8') as f: f.write(edited_content)
            self.logger.info("שלב 5: הקובץ נשמר בהצלחה.")
            self.root.after(0, lambda: self.set_state(AppState.SAVED))
        except Exception as e: 
            self.logger.error("Failed to save translated file.", exc_info=True)
            self.root.after(0, lambda e=e: messagebox.showerror("שגיאת שמירה", f"לא ניתן היה לשמור את הקובץ.\n{e}"))
            
    def run_step6_recompile(self):
        if not self._ensure_dependencies_ok(): return
        if not self.decompiled_dir: messagebox.showerror("שגיאה", "אין תיקיית עבודה (שלב 2)."); return
        self.run_in_thread(self._worker_recompile)

    def _worker_recompile(self):
        self.logger.info("שלב 6: מתחיל קימפול מחדש...");
        decompiled_name = os.path.basename(self.decompiled_dir)
        self.unsigned_apk_path = os.path.join(self.work_dir, f"{decompiled_name}_unsigned.apk")
        recompile_cmd = [self.java_path, "-jar", self.apktool_path, "b", self.decompiled_dir, "-o", self.unsigned_apk_path]
        if self.run_command(recompile_cmd):
            self.logger.info("שלב 6: הקימפול הושלם בהצלחה.")
            self.root.after(0, lambda: self.set_state(AppState.RECOMPILED))
        else: self.logger.error("שלב 6: הקימפול נכשל.")

    def run_step7_sign(self):
        if not self._ensure_dependencies_ok(): return
        if not self.unsigned_apk_path or not os.path.exists(self.unsigned_apk_path): messagebox.showerror("שגיאה", "לא נמצא קובץ APK לא חתום (שלב 6)."); return
        self.run_in_thread(self._worker_sign)

    def _worker_sign(self):
        self.logger.info("שלב 7: מתחיל חתימה...");
        keystore_path = os.path.join(self.bundle_dir, "key.jks")
        if not os.path.exists(keystore_path): 
            self.logger.error("קובץ מפתח key.jks לא נמצא!"); 
            self.root.after(0, lambda: messagebox.showerror("שגיאה", "לא נמצא קובץ המפתח key.jks."))
            return
            
        base_name = os.path.basename(self.decompiled_dir)
        signed_apk_path = os.path.join(self.executable_dir, f"{base_name}_signed_translated.apk")
        sign_cmd = [self.java_path, "-jar", self.apksigner_path, "sign", "--ks", keystore_path, "--ks-key-alias", "yossi", "--ks-pass", "pass:yossi", "--key-pass", "pass:yossi", "--out", signed_apk_path, self.unsigned_apk_path]
        
        if self.run_command(sign_cmd):
            self.logger.info(f"*** התהליך כולו הושלם! הקובץ הסופי: {signed_apk_path} ***")
            self.root.after(0, lambda path=signed_apk_path: messagebox.showinfo("הצלחה!", f"האפליקציה נחתמה בהצלחה!\nהקובץ החדש נמצא ב:\n{path}"))
            if os.path.exists(self.work_dir): shutil.rmtree(self.work_dir)
            self.logger.info("ניקוי תיקיית העבודה הושלם.")
            self.root.after(0, lambda: self.set_state(AppState.INITIAL))
        else: self.logger.error("שלב 7: החתימה נכשלה.")

    def update_editor(self, content):
        self.text_editor.delete('1.0', tk.END)
        self.text_editor.insert('1.0', content)

    def update_editor_from_root(self):
        self.update_editor(ET.tostring(self.xml_root, encoding='unicode', method='xml'))

    def run_command(self, command):
        try:
            self.logger.info(f"מריץ פקודה: {' '.join(command)}")
            startupinfo = None
            if os.name == 'nt':
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace', cwd=self.bundle_dir, startupinfo=startupinfo)
            stdout, stderr = process.communicate()
            if stdout: self.logger.debug("--- פלט התהליך ---\n" + stdout)
            if stderr: self.logger.warning("--- שגיאות התהליך ---\n" + stderr)
            if process.returncode == 0:
                self.logger.info("הפקודה הושלמה בהצלחה."); return True
            else:
                self.logger.error(f"הפקודה נכשלה עם קוד יציאה: {process.returncode}")
                self.root.after(0, lambda: messagebox.showerror("שגיאה בתהליך", f"הפקודה נכשלה.\n{stderr[:500]}"))
                return False
        except Exception as e:
            self.logger.critical("Critical error running command.", exc_info=True)
            self.root.after(0, lambda: messagebox.showerror("שגיאה קריטית", f"אירעה שגיאה:\n{e}"))
            return False

    def paste_api_key(self):
        try:
            self.api_key_entry.delete(0, tk.END)
            self.api_key_entry.insert(0, self.root.clipboard_get())
            self.logger.info("מפתח API הודבק מלוח הגזירים.")
        except tk.TclError:
            self.logger.warning("לוח הגזירים ריק או אינו מכיל טקסט.")
            messagebox.showwarning("שגיאת הדבקה", "לוח הגזירים ריק או אינו מכיל טקסט.", parent=self.root)

    def check_dependencies_silently(self):
        missing_files = []
        if not os.path.exists(self.java_path): missing_files.append("סביבת Java ניידת (תיקיית jre)")
        if not os.path.exists(self.apktool_path): missing_files.append("apktool.jar")
        if not os.path.exists(self.apksigner_path): missing_files.append("apksigner.jar")
        
        if not missing_files:
            self.logger.info("כל קבצי התלות נמצאו בהצלחה.")
            self.dependencies_ok = True
        else:
            self.logger.error("שגיאה קריטית: קבצי תלות חסרים:")
            for f in missing_files: self.logger.error(f"  - {f}")
            self.dependencies_ok = False
    
    def _ensure_dependencies_ok(self):
        if not self.dependencies_ok:
            messagebox.showerror("שגיאת תלות", "קובץ תלות אחד או יותר (jre, apktool, etc.) חסר.\nבדוק את הלוג לפרטים.", parent=self.root)
            return False
        return True

    def load_config(self):
        self.config.read(self.config_file)
        if 'API' in self.config and 'GeminiKey' in self.config['API']:
            api_key = self.config['API']['GeminiKey']
            self.api_key_entry.insert(0, api_key)
            self.run_in_thread(self.fetch_models, api_key)
        
        ssl_opt = self.config.get('Security', 'SSLOption', fallback='secure')
        self.ssl_option.set(ssl_opt)
        cert_path = self.config.get('Security', 'CustomCertPath', fallback='')
        self.ssl_custom_cert_path.set(cert_path)

    def save_config(self):
        if 'API' not in self.config: self.config.add_section('API')
        self.config.set('API', 'GeminiKey', self.api_key_entry.get())
        selected_model_value = self.selected_model.get()
        if selected_model_value and "טען" not in selected_model_value:
            self.config.set('API', 'SelectedModel', selected_model_value)
        
        if 'Security' not in self.config: self.config.add_section('Security')
        self.config.set('Security', 'SSLOption', self.ssl_option.get())
        self.config.set('Security', 'CustomCertPath', self.ssl_custom_cert_path.get())

        with open(self.config_file, 'w') as configfile:
            self.config.write(configfile)

    def save_and_fetch_models(self):
        api_key = self.api_key_entry.get()
        if not api_key: messagebox.showwarning("שגיאה", "שדה מפתח ה-API ריק."); return
        self.save_config()
        self.logger.info("הגדרות נשמרו. טוען מודלים..."); 
        self.run_in_thread(self.fetch_models, api_key)

    def fetch_models(self, api_key):
        self.logger.info("טוען מודלים מה-API...")
        self._apply_ssl_configuration()
        try:
            genai.configure(api_key=api_key, transport='rest')
            models = [m.name for m in genai.list_models() if 'generateContent' in m.supported_generation_methods]
            if not models:
                self.logger.warning("לא נמצאו מודלים תואמים."); return
            self.logger.info(f"נמצאו {len(models)} מודלים תואמים.")
            self.root.after(0, self.update_model_dropdown, models)
        except Exception as e:
            self.logger.critical("Failed to fetch models from API.", exc_info=True)
            self.root.after(0, lambda e=e: messagebox.showerror("שגיאת API", f"לא ניתן היה לטעון מודלים.\n{e}"))

    def update_model_dropdown(self, models):
        menu = self.model_menu['menu']
        menu.delete(0, 'end')
        for model in models:
            friendly_name = model.split('/')[-1]
            menu.add_command(label=friendly_name, command=lambda value=model: self.selected_model.set(value))
        
        self.model_menu.config(state=tk.NORMAL)
        previous_model = self.config.get('API', 'SelectedModel', fallback=models[0] if models else "")
        if previous_model in models: self.selected_model.set(previous_model)
        elif models: self.selected_model.set(models[0])
        else: self.selected_model.set("לא נמצאו מודלים")
        
        selected_val = self.selected_model.get()
        if selected_val and "לא" not in selected_val:
             self.logger.info(f"מודל נבחר: {selected_val.split('/')[-1]}")


if __name__ == "__main__":
    root = tk.Tk()
    app = APKTranslatorApp(root)
    root.protocol("WM_DELETE_WINDOW", lambda: (app.save_config(), root.destroy()))
    root.mainloop()
