import os
import re
import json
import shutil
import queue
import threading
import subprocess
import urllib.request
import xml.etree.ElementTree as ET

from pathlib import Path
from datetime import datetime
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser
import copy

import customtkinter as ctk

# ================= НАСТРОЙКИ =================
APP_NAME = "SanieApk Engine Pro"
VERSION = "4.0"

ANDROID_NS = "http://schemas.android.com/apk/res/android"
A = "{" + ANDROID_NS + "}"

BASE = Path(__file__).resolve().parent
TOOLS = BASE / "tools"
APKTOOL = TOOLS / "apktool.jar"
APKTOOL_URL = (
    "https://github.com/iBotPeaches/Apktool/"
    "releases/download/v2.9.3/apktool_2.9.3.jar"
)
HISTORY = BASE / "sanie_projects.json"

COLOR_BG = "#1e1e1e"
COLOR_PANEL = "#252526"
COLOR_PANEL_HOVER = "#2d2d2d"
COLOR_TEXT = "#cccccc"
COLOR_TEXT_MUTED = "#858585"
COLOR_ACCENT = "#007acc"
COLOR_ACCENT_HOVER = "#005999"
COLOR_SUCCESS = "#2ea043"
COLOR_DANGER = "#da3633"
COLOR_CANVAS_BG = "#111111"
COLOR_GRID = "#1a1a1a"
COLOR_SELECT = "#00d9ff"

ctk.set_appearance_mode("dark")

# ================= УТИЛИТЫ =================

def run_cmd(args, cwd=None, timeout=900):
    try:
        result = subprocess.run(
            [str(x) for x in args], cwd=str(cwd) if cwd else None,
            capture_output=True, text=True, timeout=timeout,
            encoding="utf-8", errors="replace", shell=False
        )
        return result.returncode, result.stdout, result.stderr
    except Exception as error:
        return -1, "", str(error)


def ensure_apktool():
    TOOLS.mkdir(parents=True, exist_ok=True)
    if APKTOOL.exists() and APKTOOL.stat().st_size > 100_000:
        return True, "Apktool уже установлен."
    temp = APKTOOL.with_suffix(".download")
    try:
        urllib.request.urlretrieve(APKTOOL_URL, temp)
        if temp.stat().st_size < 100_000:
            raise RuntimeError("Скачанный файл слишком маленький.")
        temp.replace(APKTOOL)
        return True, "Apktool скачан."
    except Exception as error:
        temp.unlink(missing_ok=True)
        return False, str(error)


def find_sdk_tool(name):
    found = shutil.which(name)
    if found:
        return Path(found)
    roots = [
        os.environ.get("ANDROID_HOME"),
        os.environ.get("ANDROID_SDK_ROOT"),
        str(Path.home() / "AppData/Local/Android/Sdk"),
    ]
    candidates = []
    for root in roots:
        if not root or not Path(root).exists():
            continue
        candidates.extend(Path(root).glob(f"build-tools/*/{name}"))
        candidates.extend(Path(root).glob(f"build-tools/*/{name}.exe"))
    return sorted(candidates, reverse=True)[0] if candidates else None


def pretty_xml(root):
    ET.indent(root, space="    ")
    return ET.tostring(root, encoding="unicode", xml_declaration=True)


def parse_dp(value, default=0.0):
    if not value:
        return default
    m = re.match(r"^\s*(-?\d+(?:\.\d+)?)\s*(dp|dip|px|sp)?\s*$", str(value))
    if not m:
        return default
    return float(m.group(1))


def xml_color(value, default="#E5E7EB"):
    if not value:
        return default
    value = value.strip()
    if re.fullmatch(r"#[0-9a-fA-F]{6}", value):
        return value
    if re.fullmatch(r"#[0-9a-fA-F]{8}", value):
        return "#" + value[-6:]
    return {"@android:color/white": "#FFFFFF", "@android:color/black": "#000000"}.get(value, default)


def valid_package(value):
    pattern = r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)+"
    if not re.fullmatch(pattern, value.strip()):
        raise ValueError("Пример: com.example.app")
    return value.strip()


# ================= ОСНОВНОЙ КЛАСС =================

class SanieApkEngine(ctk.CTk):
    def __init__(self):
        super().__init__(fg_color=COLOR_BG)
        self.title(f"{APP_NAME} v{VERSION}")
        self.geometry("1500x950")
        self.minsize(1150, 720)

        self.project = None
        self.layout_file = None
        self.root_xml = None
        self.selected = None
        self.canvas_nodes = []
        self.drag = None
        self.busy = False

        self.zoom = 1.0
        self.pan_x = 0
        self.pan_y = 0

        self.undo_stack = []
        self.redo_stack = []
        self.clipboard = None

        self.widget_tree_nodes = {}
        self.prop_entries = {}

        self.events = queue.Queue()
        self.history = self.load_history()

        self.bind("<Control-s>", lambda e: self.save_xml())
        self.bind("<Control-z>", lambda e: self.undo())
        self.bind("<Control-y>", lambda e: self.redo())
        self.bind("<Control-Shift-Z>", lambda e: self.redo())
        self.bind("<Delete>", lambda e: self.delete_node())
        self.bind("<Control-d>", lambda e: self.duplicate_node())
        self.bind("<Control-c>", lambda e: self.copy_node())
        self.bind("<Control-v>", lambda e: self.paste_node())

        self.home()
        self.after(100, self.poll_events)

    # ================= ИСТОРИЯ =================
    def load_history(self):
        try:
            if HISTORY.exists():
                return json.loads(HISTORY.read_text(encoding="utf-8"))
        except Exception:
            pass
        return []

    def remember(self, path, kind="project"):
        path = str(Path(path).resolve())
        self.history = [i for i in self.history if i.get("path") != path]
        self.history.insert(0, {"path": path, "kind": kind,
                                "opened": datetime.now().isoformat(timespec="seconds")})
        self.history = self.history[:25]
        try:
            HISTORY.write_text(json.dumps(self.history, ensure_ascii=False, indent=2),
                               encoding="utf-8")
        except Exception:
            pass

    # ================= СОБЫТИЯ/ЛОГ =================
    def log(self, text):
        if text:
            self.events.put(("log", str(text)))

    def _safe_widget(self, name):
        w = getattr(self, name, None)
        if w is None:
            return None
        try:
            if w.winfo_exists():
                return w
        except Exception:
            pass
        return None

    def poll_events(self):
        try:
            while True:
                kind, value = self.events.get_nowait()
                if kind == "log":
                    lb = self._safe_widget("log_box")
                    if lb is not None:
                        lb.configure(state="normal")
                        lb.insert("end", value + "\n")
                        lb.see("end")
                        lb.configure(state="disabled")
                elif kind == "done":
                    self.busy = False
                    st = self._safe_widget("status")
                    if st is not None:
                        st.configure(text="✓ Готово", text_color=COLOR_SUCCESS)
                    if value:
                        messagebox.showinfo("Готово", value)
                elif kind == "error":
                    self.busy = False
                    st = self._safe_widget("status")
                    if st is not None:
                        st.configure(text="✗ Ошибка", text_color=COLOR_DANGER)
                    messagebox.showerror("Ошибка", value)
        except queue.Empty:
            pass
        self.after(100, self.poll_events)

    def worker(self, function, *args):
        if self.busy:
            messagebox.showwarning("Подожди", "Другая операция ещё выполняется.")
            return
        self.busy = True
        st = self._safe_widget("status")
        if st is not None:
            st.configure(text="⏳ Выполняется...", text_color=COLOR_ACCENT)

        def run():
            try:
                result = function(*args)
                self.events.put(("done", result if isinstance(result, str) else None))
            except Exception as error:
                self.log(f"ОШИБКА: {error}")
                self.events.put(("error", str(error)))

        threading.Thread(target=run, daemon=True).start()

    def run_cmd_stream(self, args, cwd=None, timeout=1800):
        """Запускает процесс со стримингом вывода в лог."""
        try:
            proc = subprocess.Popen(
                [str(x) for x in args], cwd=str(cwd) if cwd else None,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", errors="replace",
                shell=False, bufsize=1
            )
            for line in proc.stdout:
                self.log(line.rstrip())
            try:
                code = proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                proc.kill()
                code = -1
            return code
        except Exception as error:
            self.log(f"Process error: {error}")
            return -1

    def clear(self):
        for widget in self.winfo_children():
            widget.destroy()

    # ================= ГЛАВНЫЙ ЭКРАН =================
    def home(self):
        self.clear()
        frame = ctk.CTkFrame(self, fg_color=COLOR_BG, corner_radius=0)
        frame.pack(fill="both", expand=True, padx=50, pady=40)

        ctk.CTkLabel(frame, text=APP_NAME,
                     font=ctk.CTkFont(size=42, weight="bold"),
                     text_color=COLOR_TEXT).pack(anchor="w", pady=(10, 4))
        ctk.CTkLabel(frame, text=f"v{VERSION}  •  Android APK  •  Визуальный XML-редактор  •  Сборка",
                     text_color=COLOR_TEXT_MUTED,
                     font=ctk.CTkFont(size=14)).pack(anchor="w", pady=(0, 30))

        panel = ctk.CTkFrame(frame, fg_color=COLOR_PANEL, corner_radius=16)
        panel.pack(fill="x", pady=(0, 24))

        actions = [
            ("➕  Создать новый проект", "Шаблон с LinearLayout и двумя элементами", self.create_template),
            ("📦  Открыть APK для декомпиляции", "Распаковка через apktool", self.open_apk),
            ("📁  Открыть папку проекта", "Уже распакованный проект", self.open_folder),
        ]
        for title, subtitle, cmd in actions:
            btn = ctk.CTkButton(
                panel, text=f"{title}\n{subtitle}", command=cmd,
                height=64, corner_radius=12,
                fg_color=COLOR_BG, hover_color=COLOR_PANEL_HOVER,
                text_color=COLOR_TEXT, font=ctk.CTkFont(size=14),
                anchor="w"
            )
            btn.pack(fill="x", padx=20, pady=8)

        recent = ctk.CTkFrame(frame, fg_color=COLOR_PANEL, corner_radius=16)
        recent.pack(fill="both", expand=True)

        ctk.CTkLabel(recent, text="🕒 Недавние проекты",
                     font=ctk.CTkFont(size=18, weight="bold"),
                     text_color=COLOR_TEXT).pack(anchor="w", padx=20, pady=15)

        if not self.history:
            ctk.CTkLabel(recent, text="История пуста — создайте или откройте проект.",
                         text_color=COLOR_TEXT_MUTED).pack(anchor="w", padx=20, pady=8)
        else:
            for item in self.history[:12]:
                path = Path(item.get("path", ""))
                kind = item.get("kind", "project")
                label = f"{'📦' if kind == 'apk' else '📁'}  {path.name}   —  {path.parent}"
                ctk.CTkButton(
                    recent, text=label, anchor="w",
                    fg_color=COLOR_BG, hover_color=COLOR_PANEL_HOVER,
                    text_color=COLOR_TEXT,
                    command=lambda p=path, k=kind: self.open_recent(p, k)
                ).pack(fill="x", padx=20, pady=3)

    def open_recent(self, path, kind):
        if not path.exists():
            messagebox.showwarning("Не найдено", str(path))
            return
        if kind == "apk":
            self.worker(self.decompile, path)
        else:
            self.load_project(path)

    # ================= ПРОЕКТ =================
    def create_template(self):
        parent = filedialog.askdirectory(title="Где создать проект?")
        if not parent:
            return
        name = ctk.CTkInputDialog(text="Название проекта (латиницей):",
                                  title="Новый проект").get_input()
        if not name:
            return

        slug = re.sub(r"[^A-Za-z0-9_-]+", "_", name).strip("_") or "SanieApp"
        project = Path(parent) / slug

        try:
            (project / "res/layout").mkdir(parents=True, exist_ok=True)
            (project / "res/values").mkdir(parents=True, exist_ok=True)

            pkg = f"com.example.{slug.lower().replace('-', '_')}"
            manifest = f'''<?xml version="1.0" encoding="utf-8"?>
<manifest xmlns:android="http://schemas.android.com/apk/res/android"
    package="{pkg}">
    <application android:label="@string/app_name"
        android:theme="@android:style/Theme.Material.Light.NoActionBar">
        <activity android:name=".MainActivity" android:exported="true">
            <intent-filter>
                <action android:name="android.intent.action.MAIN" />
                <category android:name="android.intent.category.LAUNCHER" />
            </intent-filter>
        </activity>
    </application>
</manifest>'''

            layout = '''<?xml version="1.0" encoding="utf-8"?>
<LinearLayout xmlns:android="http://schemas.android.com/apk/res/android"
    android:layout_width="match_parent"
    android:layout_height="match_parent"
    android:orientation="vertical"
    android:gravity="center"
    android:padding="20dp"
    android:background="#FFFFFF">

    <TextView
        android:layout_width="wrap_content"
        android:layout_height="wrap_content"
        android:text="Привет, Sanie!"
        android:textSize="24sp"
        android:textColor="#111111"
        android:layout_marginBottom="16dp" />

    <Button
        android:layout_width="wrap_content"
        android:layout_height="wrap_content"
        android:text="Нажми меня" />
</LinearLayout>'''

            strings = '''<?xml version="1.0" encoding="utf-8"?>
<resources>
    <string name="app_name">''' + name + '''</string>
</resources>'''

            (project / "AndroidManifest.xml").write_text(manifest, encoding="utf-8")
            (project / "res/layout/activity_main.xml").write_text(layout, encoding="utf-8")
            (project / "res/values/strings.xml").write_text(strings, encoding="utf-8")
            (project / "apktool.yml").write_text(
                "version: 2.9.3\napkFileName: template.apk\n"
                "isFrameworkApk: false\nusesFramework:\n  ids:\n  - 1\n"
                "sdkInfo:\n  minSdkVersion: '23'\n  targetSdkVersion: '33'\n",
                encoding="utf-8")

            self.load_project(project)
            self.remember(project)
        except Exception as error:
            messagebox.showerror("Ошибка", str(error))

    def open_folder(self):
        folder = filedialog.askdirectory(title="Выбери папку проекта")
        if folder:
            self.load_project(Path(folder))
            self.remember(folder)

    def open_apk(self):
        filename = filedialog.askopenfilename(title="Выбери APK",
                                              filetypes=[("Android APK", "*.apk")])
        if filename:
            apk = Path(filename)
            self.remember(apk, "apk")
            self.worker(self.decompile, apk)

    def decompile(self, apk):
        code, _, _ = run_cmd(["java", "-version"])
        if code != 0:
            raise RuntimeError("Java не найдена. Установи JDK.")
        ok, message = ensure_apktool()
        if not ok:
            raise RuntimeError(message)

        output = apk.with_name(apk.stem + "_decoded")
        if output.exists():
            output = apk.with_name(apk.stem + "_decoded_" + datetime.now().strftime("%Y%m%d_%H%M%S"))

        self.log(f"📦 Распаковка {apk.name}...")
        code = self.run_cmd_stream(["java", "-jar", APKTOOL, "d", apk, "-o", output], timeout=1200)
        if code != 0:
            raise RuntimeError("Ошибка распаковки. Смотри журнал.")
        self.after(0, lambda: self.load_project(output))
        return f"APK распакован:\n{output}"

    def load_project(self, path):
        path = Path(path).resolve()
        if not path.is_dir():
            return
        self.project = path
        self.layout_file = None
        self.root_xml = None
        self.selected = None
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.editor()
        self.populate_file_tree()

        candidates = sorted(path.glob("res/layout*/*.xml"))
        if candidates:
            self.load_xml(candidates[0])
        else:
            self.log("XML-макеты не найдены.")
        self.remember(path)

    # ================= РЕДАКТОР =================
    def editor(self):
        self.clear()

        # Топ-бар
        top = ctk.CTkFrame(self, fg_color=COLOR_PANEL, corner_radius=0, height=60)
        top.pack(fill="x")
        top.pack_propagate(False)

        ctk.CTkButton(top, text="← На главную", command=self.home,
                      fg_color="transparent", hover_color=COLOR_PANEL_HOVER,
                      text_color=COLOR_TEXT, width=110).pack(side="left", padx=15)
        ctk.CTkLabel(top, text=f"⚡ {APP_NAME}",
                     font=ctk.CTkFont(size=18, weight="bold"),
                     text_color=COLOR_TEXT).pack(side="left", padx=10)

        ctk.CTkButton(top, text="🔨 Собрать APK", command=self.build_apk,
                      fg_color=COLOR_SUCCESS, hover_color="#238636",
                      text_color="#ffffff", width=140).pack(side="right", padx=15, pady=10)
        ctk.CTkButton(top, text="💾 Сохранить", command=self.save_xml,
                      fg_color=COLOR_ACCENT, hover_color=COLOR_ACCENT_HOVER,
                      width=120).pack(side="right", padx=5, pady=10)
        ctk.CTkButton(top, text="↶", command=self.undo, width=40,
                      fg_color=COLOR_BG).pack(side="right", padx=2, pady=10)
        ctk.CTkButton(top, text="↷", command=self.redo, width=40,
                      fg_color=COLOR_BG).pack(side="right", padx=2, pady=10)

        ctk.CTkButton(top, text="📝 Имя", command=self.change_app_name,
                      fg_color=COLOR_BG, width=80).pack(side="right", padx=4, pady=10)
        ctk.CTkButton(top, text="🖼 Иконка", command=self.change_app_icon,
                      fg_color=COLOR_BG, width=80).pack(side="right", padx=4, pady=10)
        ctk.CTkButton(top, text="📦 Пакет", command=self.change_package,
                      fg_color=COLOR_BG, width=80).pack(side="right", padx=4, pady=10)

        # Основная область
        body = ctk.CTkFrame(self, fg_color=COLOR_BG, corner_radius=0)
        body.pack(fill="both", expand=True)

        # Левая панель
        left = ctk.CTkFrame(body, width=300, fg_color=COLOR_PANEL, corner_radius=0)
        left.pack(side="left", fill="y")
        left.pack_propagate(False)

        self.left_tabs = ctk.CTkTabview(left, fg_color=COLOR_PANEL,
                                        segmented_button_selected_color=COLOR_ACCENT)
        self.left_tabs.pack(fill="both", expand=True, padx=8, pady=8)
        self.left_tabs.add("📁 Файлы")
        self.left_tabs.add("🌳 Виджеты")

        # Файлы
        files_tab = self.left_tabs.tab("📁 Файлы")
        search_frame = ctk.CTkFrame(files_tab, fg_color="transparent")
        search_frame.pack(fill="x", pady=(0, 5))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self.populate_file_tree())
        ctk.CTkEntry(search_frame, textvariable=self.search_var,
                     placeholder_text="🔍 Поиск...", fg_color=COLOR_BG,
                     text_color=COLOR_TEXT).pack(fill="x")

        tree_frame = tk.Frame(files_tab, bg=COLOR_PANEL)
        tree_frame.pack(fill="both", expand=True)
        self.file_tree = ttk.Treeview(tree_frame, show="tree", selectmode="browse")
        self.file_tree.pack(fill="both", expand=True)
        self.file_tree.bind("<<TreeviewSelect>>", self.file_selected)

        style = ttk.Style()
        style.theme_use("default")
        style.configure("Treeview", background=COLOR_PANEL, foreground=COLOR_TEXT,
                        fieldbackground=COLOR_PANEL, rowheight=26, borderwidth=0,
                        font=("Segoe UI", 10))
        style.map("Treeview", background=[("selected", COLOR_ACCENT)],
                  foreground=[("selected", "#ffffff")])
        style.layout("Treeview", [('Treeview.treearea', {'sticky': 'nswe'})])

        # Виджеты
        widgets_tab = self.left_tabs.tab("🌳 Виджеты")
        wtree_frame = tk.Frame(widgets_tab, bg=COLOR_PANEL)
        wtree_frame.pack(fill="both", expand=True)
        self.widget_tree = ttk.Treeview(wtree_frame, show="tree", selectmode="browse")
        self.widget_tree.pack(fill="both", expand=True)
        self.widget_tree.bind("<<TreeviewSelect>>", self.widget_tree_selected)

        # Правая панель
        right = ctk.CTkFrame(body, fg_color=COLOR_PANEL, corner_radius=0, width=340)
        right.pack(side="right", fill="y")
        right.pack_propagate(False)

        self.tabs = ctk.CTkTabview(right, fg_color=COLOR_PANEL,
                                   segmented_button_selected_color=COLOR_ACCENT)
        self.tabs.pack(fill="both", expand=True, padx=8, pady=8)
        self.tabs.add("⚙ Свойства")
        self.tabs.add("📄 XML")
        self.tabs.add("📜 Лог")

        self.setup_properties_tab(self.tabs.tab("⚙ Свойства"))

        code_tab = self.tabs.tab("📄 XML")
        self.code = ctk.CTkTextbox(code_tab, font=("Consolas", 12),
                                   fg_color=COLOR_BG, text_color=COLOR_TEXT, wrap="none")
        self.code.pack(fill="both", expand=True, pady=(0, 5))
        btn_row = ctk.CTkFrame(code_tab, fg_color="transparent")
        btn_row.pack(fill="x")
        ctk.CTkButton(btn_row, text="Применить код", command=self.apply_code,
                      fg_color=COLOR_ACCENT).pack(side="right")

        log_tab = self.tabs.tab("📜 Лог")
        self.log_box = ctk.CTkTextbox(log_tab, font=("Consolas", 11),
                                      fg_color=COLOR_BG, text_color=COLOR_TEXT_MUTED)
        self.log_box.pack(fill="both", expand=True)
        self.log_box.configure(state="disabled")

        # Центр
        center = ctk.CTkFrame(body, fg_color=COLOR_BG, corner_radius=0)
        center.pack(side="left", fill="both", expand=True, padx=10, pady=10)

        # Тулбар
        toolbar = ctk.CTkFrame(center, fg_color=COLOR_PANEL, height=48, corner_radius=8)
        toolbar.pack(fill="x", pady=(0, 8))

        components = [
            ("Текст", "TextView"), ("Кнопка", "Button"), ("Поле", "EditText"),
            ("Изображ.", "ImageView"), ("Чекбокс", "CheckBox"),
            ("Контейнер", "LinearLayout"), ("Frame", "FrameLayout"),
        ]
        for label, tag in components:
            ctk.CTkButton(toolbar, text=f"+ {label}",
                          command=lambda t=tag: self.add_node(t),
                          width=85, height=32, fg_color=COLOR_BG,
                          hover_color=COLOR_PANEL_HOVER,
                          font=ctk.CTkFont(size=11)).pack(side="left", padx=2, pady=8)

        ctk.CTkButton(toolbar, text="🎨 Фон", command=self.pick_bg,
                      width=70, height=32, fg_color=COLOR_BG,
                      hover_color=COLOR_PANEL_HOVER,
                      font=ctk.CTkFont(size=11)).pack(side="left", padx=2, pady=8)

        # Зум-панель
        ctk.CTkButton(toolbar, text="−", command=lambda: self.set_zoom(self.zoom / 1.2),
                      width=32, height=32, fg_color=COLOR_BG).pack(side="right", padx=2, pady=8)
        ctk.CTkLabel(toolbar, text="", width=1, fg_color="transparent").pack(side="right")
        self.zoom_label = ctk.CTkLabel(toolbar, text="100%", width=50,
                                       text_color=COLOR_TEXT_MUTED,
                                       font=ctk.CTkFont(size=11))
        self.zoom_label.pack(side="right", padx=2)
        ctk.CTkButton(toolbar, text="+", command=lambda: self.set_zoom(self.zoom * 1.2),
                      width=32, height=32, fg_color=COLOR_BG).pack(side="right", padx=2, pady=8)
        ctk.CTkButton(toolbar, text="100%", command=lambda: self.set_zoom(1.0),
                      width=56, height=32, fg_color=COLOR_BG).pack(side="right", padx=2, pady=8)

        # Canvas
        canvas_wrap = ctk.CTkFrame(center, fg_color=COLOR_CANVAS_BG, corner_radius=8)
        canvas_wrap.pack(fill="both", expand=True)
        self.canvas = tk.Canvas(canvas_wrap, bg=COLOR_CANVAS_BG,
                                highlightthickness=0)
        self.canvas.pack(fill="both", expand=True, padx=2, pady=2)
        self.canvas.bind("<Button-1>", self.canvas_click)
        self.canvas.bind("<B1-Motion>", self.canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.canvas_release)
        self.canvas.bind("<Configure>", lambda e: self.render())
        self.canvas.bind("<Button-2>", self.pan_start)
        self.canvas.bind("<B2-Motion>", self.pan_move)
        self.canvas.bind("<ButtonRelease-2>", self.pan_end)
        self.canvas.bind("<MouseWheel>", self.on_mousewheel)

        # Статус-бар
        self.status = ctk.CTkLabel(self, text="✓ Готово", anchor="w",
                                   text_color=COLOR_TEXT_MUTED,
                                   fg_color=COLOR_PANEL, height=28,
                                   font=ctk.CTkFont(size=11))
        self.status.pack(fill="x", side="bottom")

        self._pan_start = None
        self._pan_origin = None

    # ================= СВОЙСТВА =================
    def setup_properties_tab(self, parent):
        scroll = ctk.CTkScrollableFrame(parent, fg_color="transparent")
        scroll.pack(fill="both", expand=True)

        self.type_label = ctk.CTkLabel(scroll, text="Элемент не выбран",
                                       font=ctk.CTkFont(size=14, weight="bold"),
                                       text_color=COLOR_TEXT)
        self.type_label.pack(anchor="w", padx=6, pady=(8, 12))

        fields = [
            ("ID", "id", "text"),
            ("Текст", "text", "text"),
            ("Ширина", "width", "text"),
            ("Высота", "height", "text"),
            ("Размер текста", "textSize", "text"),
            ("Цвет текста", "textColor", "color"),
            ("Фон", "background", "color"),
            ("Padding", "padding", "text"),
            ("Gravity", "gravity", "text"),
            ("Orientation", "orientation", "text"),
        ]

        for label, key, kind in fields:
            row = ctk.CTkFrame(scroll, fg_color="transparent")
            row.pack(fill="x", padx=4, pady=4)
            ctk.CTkLabel(row, text=label, width=100, anchor="w",
                         text_color=COLOR_TEXT_MUTED,
                         font=ctk.CTkFont(size=11)).pack(side="left")
            entry = ctk.CTkEntry(row, fg_color=COLOR_BG, text_color=COLOR_TEXT,
                                 border_color=COLOR_PANEL_HOVER)
            entry.pack(side="left", fill="x", expand=True)
            self.prop_entries[key] = entry
            if kind == "color":
                ctk.CTkButton(row, text="🎨", width=28,
                              command=lambda k=key: self.pick_prop_color(k),
                              fg_color=COLOR_BG,
                              hover_color=COLOR_PANEL_HOVER).pack(side="left", padx=2)

        ctk.CTkButton(scroll, text="✓ Применить", command=self.apply_props,
                      fg_color=COLOR_ACCENT, hover_color=COLOR_ACCENT_HOVER,
                      height=36).pack(fill="x", padx=4, pady=(14, 4))
        ctk.CTkButton(scroll, text="🗑 Удалить элемент", command=self.delete_node,
                      fg_color=COLOR_DANGER, hover_color="#b32d2a",
                      height=36).pack(fill="x", padx=4, pady=4)
        ctk.CTkButton(scroll, text="📋 Дублировать", command=self.duplicate_node,
                      fg_color=COLOR_BG, hover_color=COLOR_PANEL_HOVER,
                      height=36).pack(fill="x", padx=4, pady=4)

    def pick_prop_color(self, key):
        if self.selected is None:
            return
        chosen = colorchooser.askcolor(title="Выбор цвета")[1]
        if chosen:
            self.prop_entries[key].delete(0, "end")
            self.prop_entries[key].insert(0, chosen)

    # ================= ФАЙЛЫ =================
    def populate_file_tree(self):
        if self.project is None:
            return
        self.file_tree.delete(*self.file_tree.get_children())
        query = self.search_var.get().lower().strip() if hasattr(self, "search_var") else ""
        root_id = self.file_tree.insert("", "end", text=f"📁 {self.project.name}",
                                        open=True, values=(str(self.project),))
        self._insert_children(root_id, self.project, 0, query)

    def _insert_children(self, parent, folder, depth, query):
        if depth > 5:
            return
        try:
            items = sorted(folder.iterdir(), key=lambda p: (not p.is_dir(), p.name.lower()))
        except OSError:
            return
        for path in items:
            if path.name.startswith(".") or path.name in {"build", ".gradle", "__pycache__"}:
                continue
            if query and query not in path.name.lower() and not path.is_dir():
                continue
            icon = "📁" if path.is_dir() else ("📄" if path.suffix == ".xml" else "📃")
            item_id = self.file_tree.insert(parent, "end", text=f"{icon} {path.name}",
                                            values=(str(path),),
                                            open=depth == 0)
            if path.is_dir():
                self._insert_children(item_id, path, depth + 1, query)

    def file_selected(self, _event=None):
        selection = self.file_tree.selection()
        if not selection:
            return
        values = self.file_tree.item(selection[0], "values")
        if not values:
            return
        path = Path(values[0])
        if not path.is_file():
            return
        if path.suffix.lower() == ".xml":
            self.load_xml(path)
        elif path.suffix.lower() in {".smali", ".txt", ".json", ".yml", ".properties", ".java", ".kt"}:
            self.layout_file = path
            self.root_xml = None
            self.code.delete("1.0", "end")
            try:
                self.code.insert("1.0", path.read_text(encoding="utf-8", errors="replace"))
            except Exception as e:
                self.log(f"Не удалось открыть: {e}")
            self.tabs.set("📄 XML")

    # ================= ВИДЖЕТ-ДЕРЕВО =================
    def populate_widget_tree(self):
        if not hasattr(self, "widget_tree"):
            return
        self.widget_tree.delete(*self.widget_tree.get_children())
        self.widget_tree_nodes = {}
        if self.root_xml is None:
            return
        root_id = self._insert_widget_node("", self.root_xml)
        if root_id:
            self.widget_tree.item(root_id, open=True)

    def _insert_widget_node(self, parent_id, node):
        tag = node.tag.split("}")[-1] if isinstance(node.tag, str) else "?"
        text = node.get(A + "text", "")
        label = f"▸ {tag}" + (f'  "{text[:22]}"' if text else "")
        item_id = self.widget_tree.insert(parent_id, "end", text=label, open=True)
        self.widget_tree_nodes[item_id] = node
        for child in node:
            if isinstance(child.tag, str):
                self._insert_widget_node(item_id, child)
        return item_id

    def widget_tree_selected(self, _event=None):
        sel = self.widget_tree.selection()
        if not sel:
            return
        node = self.widget_tree_nodes.get(sel[0])
        if node is not None:
            self.selected = node
            self.show_props(node)
            self.render()

    def sync_widget_tree_selection(self):
        if not hasattr(self, "widget_tree"):
            return
        for item_id, node in self.widget_tree_nodes.items():
            if node is self.selected:
                self.widget_tree.selection_set(item_id)
                self.widget_tree.see(item_id)
                return

    # ================= XML =================
    def load_xml(self, path):
        try:
            text = Path(path).read_text(encoding="utf-8", errors="replace")
            root = ET.fromstring(text)
            self.layout_file = Path(path)
            self.root_xml = root
            self.selected = None
            self.undo_stack.clear()
            self.redo_stack.clear()
            self.sync_code()
            self.populate_widget_tree()
            self.render()
            self.tabs.set("⚙ Свойства")
            self.status.configure(text=f"Открыт: {path.name}", text_color=COLOR_TEXT_MUTED)
        except Exception as error:
            messagebox.showerror("XML Ошибка", f"{error}\n\n{path}")

    def sync_code(self):
        if self.root_xml is None or not hasattr(self, "code"):
            return
        self.code.delete("1.0", "end")
        self.code.insert("1.0", pretty_xml(self.root_xml))

    def apply_code(self):
        try:
            text = self.code.get("1.0", "end-1c")
            self.snapshot()
            self.root_xml = ET.fromstring(text)
            self.selected = None
            self.populate_widget_tree()
            self.render()
            self.log("XML применён из кода.")
        except ET.ParseError as error:
            messagebox.showerror("XML Ошибка", str(error))

    def save_xml(self):
        if not self.layout_file:
            return
        try:
            if self.root_xml is not None and self.layout_file.suffix.lower() == ".xml":
                self.layout_file.write_text(pretty_xml(self.root_xml), encoding="utf-8")
            else:
                self.layout_file.write_text(self.code.get("1.0", "end-1c"), encoding="utf-8")
            st = self._safe_widget("status")
            if st is not None:
                st.configure(text=f"💾 Сохранено: {self.layout_file.name}",
                             text_color=COLOR_SUCCESS)
        except Exception as error:
            messagebox.showerror("Ошибка сохранения", str(error))

    # ================= RENDER (рекурсивный) =================
    def set_zoom(self, z):
        self.zoom = max(0.3, min(3.0, z))
        if hasattr(self, "zoom_label"):
            self.zoom_label.configure(text=f"{int(self.zoom * 100)}%")
        self.render()

    def on_mousewheel(self, event):
        if event.state & 0x0004:
            factor = 1.1 if event.delta > 0 else 1 / 1.1
            self.set_zoom(self.zoom * factor)

    def pan_start(self, event):
        self._pan_start = (event.x, event.y)
        self._pan_origin = (self.pan_x, self.pan_y)

    def pan_move(self, event):
        if self._pan_start is None:
            return
        dx = event.x - self._pan_start[0]
        dy = event.y - self._pan_start[1]
        self.pan_x = self._pan_origin[0] + dx
        self.pan_y = self._pan_origin[1] + dy
        self.render()

    def pan_end(self, _event):
        self._pan_start = None

    def is_container(self, node):
        if not isinstance(node.tag, str):
            return False
        tag = node.tag.split("}")[-1]
        return tag in {
            "LinearLayout", "FrameLayout", "RelativeLayout", "ConstraintLayout",
            "AbsoluteLayout", "TableLayout", "TableRow", "ScrollView",
            "HorizontalScrollView", "NestedScrollView", "RadioGroup", "GridLayout",
            "CardView", "CoordinatorLayout",
        }

    def estimate_wrap_size(self, node):
        tag = node.tag.split("}")[-1] if isinstance(node.tag, str) else ""
        text = node.get(A + "text", "")
        text_size = parse_dp(node.get(A + "textSize", "14sp"), 14)
        if text:
            char_w = text_size * 0.55 * self.zoom
            w = max(60 * self.zoom, len(text) * char_w + 24 * self.zoom)
            h = max(40 * self.zoom, text_size * 1.6 * self.zoom + 12 * self.zoom)
            return w, h
        defaults = {
            "Button": (120, 44), "EditText": (200, 44),
            "ImageView": (80, 80), "CheckBox": (140, 40),
            "Switch": (120, 40), "ProgressBar": (140, 24),
            "SeekBar": (160, 24), "RadioButton": (140, 40),
            "TextView": (100, 32),
        }
        dw, dh = defaults.get(tag, (100, 40))
        return dw * self.zoom, dh * self.zoom

    def measure(self, node, avail_w, avail_h):
        w_attr = node.get(A + "layout_width", "wrap_content")
        h_attr = node.get(A + "layout_height", "wrap_content")
        ww, wh = self.estimate_wrap_size(node)

        if w_attr in ("match_parent", "fill_parent"):
            w = avail_w
        elif w_attr == "wrap_content":
            w = ww
        else:
            w = parse_dp(w_attr, 100) * self.zoom

        if h_attr in ("match_parent", "fill_parent"):
            h = avail_h
        elif h_attr == "wrap_content":
            h = wh
        else:
            h = parse_dp(h_attr, 40) * self.zoom

        w = max(16, min(w, avail_w))
        h = max(16, min(h, avail_h))
        return w, h

    def render(self):
        if not hasattr(self, "canvas") or self.root_xml is None:
            return

        self.canvas.delete("all")
        self.canvas_nodes = []

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw < 10 or ch < 10:
            return

        # Сетка
        grid = int(20 * self.zoom)
        if grid >= 8:
            for i in range(0, cw, grid):
                self.canvas.create_line(i, 0, i, ch, fill=COLOR_GRID)
            for i in range(0, ch, grid):
                self.canvas.create_line(0, i, cw, i, fill=COLOR_GRID)

        # Телефон
        base_w, base_h = 360, 640
        phone_w = base_w * self.zoom
        phone_h = base_h * self.zoom

        px = max(10, (cw - phone_w) / 2 + self.pan_x)
        py = max(10, (ch - phone_h) / 2 + self.pan_y)

        # Тень
        self.canvas.create_rectangle(px + 6, py + 6, px + phone_w + 6, py + phone_h + 6,
                                     fill="#000000", outline="")
        # Корпус
        self.canvas.create_rectangle(px, py, px + phone_w, py + phone_h,
                                     fill="#1a1a1a", outline="#3a3a3a",
                                     width=max(1, int(3 * self.zoom)))
        # Экран
        screen_x = px + 10 * self.zoom
        screen_y = py + 42 * self.zoom
        screen_w = phone_w - 20 * self.zoom
        screen_h = phone_h - 52 * self.zoom

        # Фон экрана (берем из корневого layout'а если есть background)
        bg = xml_color(self.root_xml.get(A + "background"), "#FFFFFF")
        self.canvas.create_rectangle(screen_x, screen_y,
                                     screen_x + screen_w, screen_y + screen_h,
                                     fill=bg, outline="")
        # Notch
        notch_w = 120 * self.zoom
        self.canvas.create_rectangle(
            px + (phone_w - notch_w) / 2, py + 10 * self.zoom,
            px + (phone_w + notch_w) / 2, py + 28 * self.zoom,
            fill="#000000", outline="")
        # Кнопка home внизу
        self.canvas.create_oval(
            px + phone_w / 2 - 20 * self.zoom, py + phone_h - 10 * self.zoom,
            px + phone_w / 2 + 20 * self.zoom, py + phone_h + 10 * self.zoom,
            fill="#2a2a2a", outline="")

        # Рендерим корневой layout
        self._render_children(self.root_xml, screen_x, screen_y,
                              screen_w, screen_h, depth=0)

        if self.selected is not None:
            if not self._node_exists(self.root_xml, self.selected):
                self.selected = None
            else:
                self.show_props(self.selected)
                self.sync_widget_tree_selection()

    def _node_exists(self, root, target):
        if root is target:
            return True
        for child in root:
            if self._node_exists(child, target):
                return True
        return False

    def _render_children(self, parent, px, py, pw, ph, depth):
        if depth > 12:
            return

        tag = parent.tag.split("}")[-1] if isinstance(parent.tag, str) else ""
        orientation = parent.get(A + "orientation", "vertical")

        # Padding контейнера
        pad = parse_dp(parent.get(A + "padding", "0"), 0) * self.zoom
        pad_l = pad + parse_dp(parent.get(A + "paddingLeft", "0"), 0) * self.zoom
        pad_t = pad + parse_dp(parent.get(A + "paddingTop", "0"), 0) * self.zoom
        pad_r = pad + parse_dp(parent.get(A + "paddingRight", "0"), 0) * self.zoom
        pad_b = pad + parse_dp(parent.get(A + "paddingBottom", "0"), 0) * self.zoom

        cx = px + pad_l
        cy = py + pad_t
        cw = pw - pad_l - pad_r
        chh = ph - pad_t - pad_b
        if cw <= 4 or chh <= 4:
            return

        is_horizontal = (tag == "LinearLayout" and orientation == "horizontal") or tag == "TableRow"
        is_linear = tag in ("LinearLayout", "RadioGroup", "TableRow")

        cursor_x = cx
        cursor_y = cy
        row_height = 0

        for child in list(parent):
            if not isinstance(child.tag, str):
                continue

            ml = parse_dp(child.get(A + "layout_marginLeft",
                                     child.get(A + "layout_margin", "0")), 0) * self.zoom
            mt = parse_dp(child.get(A + "layout_marginTop",
                                     child.get(A + "layout_margin", "0")), 0) * self.zoom
            mr = parse_dp(child.get(A + "layout_marginRight",
                                     child.get(A + "layout_margin", "0")), 0) * self.zoom
            mb = parse_dp(child.get(A + "layout_marginBottom",
                                     child.get(A + "layout_margin", "0")), 0) * self.zoom

            avail_w = cw - ml - mr
            avail_h = chh - mt - mb
            ew, eh = self.measure(child, max(16, avail_w), max(16, avail_h))

            if is_linear and is_horizontal:
                if cursor_x + ml + ew + mr > cx + cw and cursor_x > cx:
                    cursor_x = cx
                    cursor_y += row_height
                    row_height = 0
                ex = cursor_x + ml
                ey = cursor_y + mt
                cursor_x = ex + ew + mr
                row_height = max(row_height, mt + eh + mb)
            else:
                ex = cursor_x + ml
                ey = cursor_y + mt
                if is_linear:
                    cursor_y = ey + eh + mb
                else:
                    # FrameLayout/Relative/Constraint: накладываем
                    pass

            # Clip
            draw_x = max(cx, ex)
            draw_y = max(cy, ey)
            draw_w = min(ex + ew, cx + cw) - draw_x
            draw_h = min(ey + eh, cy + chh) - draw_y
            if draw_w < 4 or draw_h < 4:
                continue

            self._draw_element(child, draw_x, draw_y, draw_w, draw_h)

            if self.is_container(child):
                self._render_children(child, draw_x, draw_y, draw_w, draw_h, depth + 1)

    def _draw_element(self, node, x, y, w, h):
        tag = node.tag.split("}")[-1] if isinstance(node.tag, str) else "?"
        text = node.get(A + "text", "")

        # Цвета
        bg_attr = node.get(A + "background")
        if bg_attr is None and node.get(A + "backgroundTint"):
            bg_attr = node.get(A + "backgroundTint")

        if tag == "Button":
            fill = xml_color(bg_attr, "#2563EB")
        elif tag in ("LinearLayout", "FrameLayout", "RelativeLayout", "ConstraintLayout"):
            fill = xml_color(bg_attr, "")
            if not fill:
                fill = ""  # прозрачный
        elif tag in ("ImageView",):
            fill = xml_color(bg_attr, "#374151")
        else:
            fill = xml_color(bg_attr, "") or "#2a2a2a"

        outline_color = COLOR_SELECT if node is self.selected else "#4b5563"
        outline_width = max(1, int(2 * self.zoom)) if node is self.selected else 1

        if fill:
            self.canvas.create_rectangle(x, y, x + w, y + h,
                                         fill=fill, outline=outline_color,
                                         width=outline_width)
        else:
            self.canvas.create_rectangle(x, y, x + w, y + h,
                                         fill="", outline=outline_color,
                                         width=outline_width,
                                         dash=(4, 2) if node is not self.selected else ())

        # Текст
        if not text:
            text = node.get(A + "hint", "")
        if not text and tag in ("TextView", "EditText", "Button", "CheckBox"):
            text = tag

        if text and w > 20 and h > 12:
            text_color = xml_color(node.get(A + "textColor"),
                                   "#FFFFFF" if tag == "Button" else "#E5E7EB")
            font_size = max(7, int(parse_dp(node.get(A + "textSize", "13sp"), 13) * self.zoom))
            try:
                self.canvas.create_text(x + 6, y + h / 2, text=text,
                                        fill=text_color, anchor="w",
                                        font=("Segoe UI", font_size),
                                        width=max(20, w - 12))
            except Exception:
                pass

        # Маркер типа для контейнеров
        if tag in ("LinearLayout", "FrameLayout", "RelativeLayout", "ConstraintLayout"):
            label = tag[0] + ("↓" if node.get(A + "orientation", "vertical") == "vertical" else "→")
            try:
                self.canvas.create_text(x + 4, y + 4, text=label, anchor="nw",
                                        fill=outline_color,
                                        font=("Consolas", max(7, int(9 * self.zoom))))
            except Exception:
                pass

        # Ручка ресайза
        hsize = max(8, int(10 * self.zoom))
        self.canvas.create_rectangle(x + w - hsize, y + h - hsize, x + w, y + h,
                                     fill=COLOR_SELECT if node is self.selected else "#555",
                                     outline="")

        self.canvas_nodes.append({
            "node": node,
            "box": (x, y, x + w, y + h),
            "w": w, "h": h,
        })

    # ================= СОБЫТИЯ CANVAS =================
    def hit_test(self, x, y):
        for item in reversed(self.canvas_nodes):
            x1, y1, x2, y2 = item["box"]
            if x2 - 15 <= x <= x2 + 5 and y2 - 15 <= y <= y2 + 5:
                return item, "resize"
            if x1 <= x <= x2 and y1 <= y <= y2:
                return item, "move"
        return None, None

    def canvas_click(self, event):
        hit, mode = self.hit_test(event.x, event.y)
        if not hit:
            self.selected = None
            self.drag = None
            self.render()
            return
        self.selected = hit["node"]
        self.drag = {"node": hit["node"], "mode": mode,
                     "sx": event.x, "sy": event.y, "box": hit["box"]}
        self.sync_widget_tree_selection()
        self.render()

    def canvas_drag(self, event):
        if not self.drag:
            return
        data = self.drag
        x1, y1, x2, y2 = data["box"]
        dx = event.x - data["sx"]
        dy = event.y - data["sy"]
        self.canvas.delete("drag-preview")
        if data["mode"] == "resize":
            new_w = max(20, (x2 - x1) + dx)
            new_h = max(20, (y2 - y1) + dy)
            self.canvas.create_rectangle(x1, y1, x1 + new_w, y1 + new_h,
                                         outline=COLOR_SELECT, width=2, dash=(4, 2),
                                         tags="drag-preview")
        else:
            self.canvas.create_rectangle(x1 + dx, y1 + dy, x2 + dx, y2 + dy,
                                         outline=COLOR_SELECT, width=2, dash=(4, 2),
                                         tags="drag-preview")

    def canvas_release(self, event):
        if not self.drag:
            return
        data = self.drag
        x1, y1, x2, y2 = data["box"]
        dx = event.x - data["sx"]
        dy = event.y - data["sy"]
        node = data["node"]

        if abs(dx) < 2 and abs(dy) < 2:
            self.drag = None
            self.canvas.delete("drag-preview")
            return

        self.snapshot()

        if data["mode"] == "resize":
            new_w = max(20, (x2 - x1) + dx)
            new_h = max(20, (y2 - y1) + dy)
            node.set(A + "layout_width", f"{int(new_w / self.zoom)}dp")
            node.set(A + "layout_height", f"{int(new_h / self.zoom)}dp")
        else:
            node.set(A + "layout_marginLeft", f"{max(0, int(dx / self.zoom))}dp")
            node.set(A + "layout_marginTop", f"{max(0, int(dy / self.zoom))}dp")

        self.drag = None
        self.sync_code()
        self.render()

    # ================= СВОЙСТВА ЭЛЕМЕНТА =================
    def show_props(self, node):
        tag = node.tag.split("}")[-1] if isinstance(node.tag, str) else "?"
        self.type_label.configure(text=f"▸ {tag}")

        mapping = {
            "id": node.get(A + "id", ""),
            "text": node.get(A + "text", ""),
            "width": node.get(A + "layout_width", "wrap_content"),
            "height": node.get(A + "layout_height", "wrap_content"),
            "textSize": node.get(A + "textSize", ""),
            "textColor": node.get(A + "textColor", ""),
            "background": node.get(A + "background", ""),
            "padding": node.get(A + "padding", ""),
            "gravity": node.get(A + "gravity", ""),
            "orientation": node.get(A + "orientation", ""),
        }
        for key, entry in self.prop_entries.items():
            entry.delete(0, "end")
            entry.insert(0, mapping.get(key, ""))

    def apply_props(self):
        if self.selected is None:
            messagebox.showinfo("Внимание", "Сначала выбери элемент!")
            return
        self.snapshot()
        node = self.selected

        mapping = {
            "id": (A + "id", None),
            "text": (A + "text", None),
            "width": (A + "layout_width", "wrap_content"),
            "height": (A + "layout_height", "wrap_content"),
            "textSize": (A + "textSize", None),
            "textColor": (A + "textColor", None),
            "background": (A + "background", None),
            "padding": (A + "padding", None),
            "gravity": (A + "gravity", None),
            "orientation": (A + "orientation", None),
        }

        for key, (attr, default) in mapping.items():
            entry = self.prop_entries.get(key)
            if not entry:
                continue
            val = entry.get().strip()
            if val:
                if key == "id" and not val.startswith("@"):
                    val = "@+id/" + val
                node.set(attr, val)
            elif default is None:
                node.attrib.pop(attr, None)
            else:
                node.set(attr, default)

        self.sync_code()
        self.populate_widget_tree()
        self.render()

    def pick_bg(self):
        if self.selected is None:
            return
        chosen = colorchooser.askcolor(title="Цвет фона")[1]
        if chosen:
            self.snapshot()
            self.selected.set(A + "background", chosen)
            self.sync_code()
            self.render()

    # ================= ОПЕРАЦИИ С NODE =================
    def find_parent(self, target):
        if self.root_xml is None:
            return None
        for parent in self.root_xml.iter():
            if target in list(parent):
                return parent
        return None

    def add_node(self, kind):
        if self.root_xml is None:
            return
        self.snapshot()

        node = ET.Element(kind)
        if kind in ("LinearLayout", "FrameLayout", "RelativeLayout"):
            node.set(A + "layout_width", "match_parent")
            node.set(A + "layout_height", "wrap_content")
            node.set(A + "orientation", "vertical" if kind == "LinearLayout" else "")
            if not node.get(A + "orientation"):
                node.attrib.pop(A + "orientation", None)
            node.set(A + "padding", "8dp")
        else:
            node.set(A + "layout_width", "wrap_content")
            node.set(A + "layout_height", "wrap_content")

        if kind == "TextView":
            node.set(A + "text", "Новый текст")
            node.set(A + "textSize", "16sp")
            node.set(A + "textColor", "#E5E7EB")
        elif kind == "Button":
            node.set(A + "text", "Кнопка")
            node.set(A + "textColor", "#FFFFFF")
            node.set(A + "backgroundTint", "#2563EB")
        elif kind == "EditText":
            node.set(A + "hint", "Введите текст")
            node.set(A + "textColor", "#E5E7EB")
        elif kind == "ImageView":
            node.set(A + "layout_width", "80dp")
            node.set(A + "layout_height", "80dp")
        elif kind in ("CheckBox", "Switch", "RadioButton"):
            node.set(A + "text", kind)
            node.set(A + "textColor", "#E5E7EB")

        # Выбираем родителя
        if self.selected is None:
            parent = self.root_xml
        elif self.is_container(self.selected):
            parent = self.selected
        else:
            parent = self.find_parent(self.selected) or self.root_xml

        parent.append(node)
        self.selected = node
        self.sync_code()
        self.populate_widget_tree()
        self.render()

    def delete_node(self):
        if self.selected is None:
            return
        if self.selected is self.root_xml:
            messagebox.showwarning("Нельзя", "Корневой элемент нельзя удалить.")
            return
        parent = self.find_parent(self.selected)
        if parent is None:
            return
        if not messagebox.askyesno("Удалить", "Удалить этот элемент?"):
            return
        self.snapshot()
        parent.remove(self.selected)
        self.selected = None
        self.sync_code()
        self.populate_widget_tree()
        self.render()

    def duplicate_node(self):
        if self.selected is None or self.selected is self.root_xml:
            return
        parent = self.find_parent(self.selected)
        if parent is None:
            return
        self.snapshot()
        clone = copy.deepcopy(self.selected)
        parent.append(clone)
        self.selected = clone
        self.sync_code()
        self.populate_widget_tree()
        self.render()

    def copy_node(self):
        if self.selected is not None:
            self.clipboard = copy.deepcopy(self.selected)
            self.status.configure(text="📋 Скопировано", text_color=COLOR_TEXT_MUTED)

    def paste_node(self):
        if self.clipboard is None or self.root_xml is None:
            return
        self.snapshot()
        if self.selected is None or not self.is_container(self.selected):
            parent = self.root_xml
        else:
            parent = self.selected
        clone = copy.deepcopy(self.clipboard)
        parent.append(clone)
        self.selected = clone
        self.sync_code()
        self.populate_widget_tree()
        self.render()

    # ================= UNDO / REDO =================
    def snapshot(self):
        if self.root_xml is None:
            return
        try:
            self.undo_stack.append(pretty_xml(self.root_xml))
            if len(self.undo_stack) > 50:
                self.undo_stack.pop(0)
            self.redo_stack.clear()
        except Exception:
            pass

    def undo(self):
        if not self.undo_stack:
            return
        try:
            self.redo_stack.append(pretty_xml(self.root_xml))
            self.root_xml = ET.fromstring(self.undo_stack.pop())
            self.selected = None
            self.sync_code()
            self.populate_widget_tree()
            self.render()
            self.status.configure(text="↶ Отмена", text_color=COLOR_TEXT_MUTED)
        except Exception as e:
            self.log(f"Undo error: {e}")

    def redo(self):
        if not self.redo_stack:
            return
        try:
            self.undo_stack.append(pretty_xml(self.root_xml))
            self.root_xml = ET.fromstring(self.redo_stack.pop())
            self.selected = None
            self.sync_code()
            self.populate_widget_tree()
            self.render()
            self.status.configure(text="↷ Повтор", text_color=COLOR_TEXT_MUTED)
        except Exception as e:
            self.log(f"Redo error: {e}")

    # ================= НАСТРОЙКИ ПРОЕКТА =================
    def change_package(self):
        if not self.project:
            return
        manifest = self.project / "AndroidManifest.xml"
        if not manifest.exists():
            messagebox.showerror("Ошибка", "AndroidManifest.xml не найден.")
            return
        try:
            root = ET.parse(manifest).getroot()
            current = root.get("package", "com.example.app")
            value = ctk.CTkInputDialog(text=f"Текущий пакет:\n{current}\n\nНовый:",
                                       title="Пакет").get_input()
            if value:
                root.set("package", valid_package(value))
                manifest.write_text(pretty_xml(root), encoding="utf-8")
                messagebox.showinfo("Успех", "Имя пакета изменено!")
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def change_app_name(self):
        if not self.project:
            return
        strings_xml = self.project / "res" / "values" / "strings.xml"
        if not strings_xml.exists():
            messagebox.showerror("Ошибка", "strings.xml не найден!")
            return
        try:
            tree = ET.parse(strings_xml)
            root = tree.getroot()
            app_name_node = root.find("string[@name='app_name']")
            current = app_name_node.text if app_name_node is not None else ""
            new_name = ctk.CTkInputDialog(
                text=f"Текущее: {current}\nНовое имя:", title="Имя"
            ).get_input()
            if new_name:
                if app_name_node is not None:
                    app_name_node.text = new_name
                else:
                    new_node = ET.SubElement(root, "string")
                    new_node.set("name", "app_name")
                    new_node.text = new_name
                tree.write(strings_xml, encoding="utf-8", xml_declaration=True)
                messagebox.showinfo("Успех", f"Имя: {new_name}")
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def change_app_icon(self):
        if not self.project:
            return
        new_icon = filedialog.askopenfilename(
            title="Иконка (PNG)", filetypes=[("PNG", "*.png")])
        if not new_icon:
            return
        count = 0
        for mipmap in (self.project / "res").glob("mipmap-*"):
            for icon in mipmap.glob("ic_launcher.*"):
                try:
                    if icon.suffix.lower() in (".png", ".webp"):
                        shutil.copy2(new_icon, icon)
                        count += 1
                except Exception:
                    pass
        if count:
            messagebox.showinfo("Успех", f"Иконка обновлена в {count} папках!")
        else:
            messagebox.showwarning("Не найдено", "mipmap-* с ic_launcher не найдены.")

    # ================= СБОРКА =================
    def build_apk(self):
        if not self.project:
            return
        if self.layout_file and self.layout_file.exists():
            self.save_xml()

        if not ((self.project / "apktool.yml").exists()
                or (self.project / "AndroidManifest.xml").exists()):
            messagebox.showwarning("Ошибка", "Не найден apktool.yml или AndroidManifest.xml.")
            return

        if messagebox.askyesno("Сборка", f"Собрать APK из:\n{self.project}?"):
            self.worker(self.build_worker, self.project)

    def build_worker(self, project):
        code, _, _ = run_cmd(["java", "-version"])
        if code != 0:
            raise RuntimeError("Java не найдена.")

        ok, message = ensure_apktool()
        if not ok:
            raise RuntimeError(message)

        unsigned = project.with_name(project.name + "_unsigned.apk")
        self.log("═" * 60)
        self.log(" 1/3 — Сборка через Apktool...")
        self.log("═" * 60)
        code = self.run_cmd_stream(["java", "-jar", APKTOOL, "b", project, "-o", unsigned],
                                   timeout=1800)
        if code != 0 or not unsigned.exists():
            raise RuntimeError("Ошибка сборки Apktool.")

        align = find_sdk_tool("zipalign")
        signer = find_sdk_tool("apksigner")
        if not align or not signer:
            return f"APK собран без подписи (нет SDK):\n{unsigned}"

        aligned = project.with_name(project.name + "_aligned.apk")
        signed = project.with_name(project.name + "_signed.apk")

        self.log("═" * 60)
        self.log(" 2/3 — Выравнивание (zipalign)...")
        self.log("═" * 60)
        code = self.run_cmd_stream([align, "-f", "4", unsigned, aligned], timeout=600)
        if code != 0:
            raise RuntimeError("Ошибка zipalign.")

        key = Path.home() / ".android" / "sanie-debug.keystore"
        if not key.exists():
            key.parent.mkdir(parents=True, exist_ok=True)
            self.log("🔑 Создание ключа...")
            run_cmd(["keytool", "-genkeypair", "-keystore", key,
                     "-storepass", "android", "-alias", "saniekey",
                     "-keypass", "android", "-keyalg", "RSA",
                     "-keysize", "2048", "-validity", "10000",
                     "-dname", "CN=SanieApk Debug,O=SanieApk,C=US"], timeout=120)

        self.log("═" * 60)
        self.log(" 3/3 — Подпись (apksigner)...")
        self.log("═" * 60)
        code = self.run_cmd_stream(
            [signer, "sign", "--ks", key, "--ks-pass", "pass:android",
             "--key-pass", "pass:android", "--ks-key-alias", "saniekey",
             "--out", signed, aligned], timeout=600)
        if code != 0:
            raise RuntimeError("Ошибка подписи APK.")

        try:
            unsigned.unlink(missing_ok=True)
            aligned.unlink(missing_ok=True)
        except Exception:
            pass

        return f"✅ APK собран и подписан!\n\n{signed}"


if __name__ == "__main__":
    app = SanieApkEngine()
    app.mainloop()