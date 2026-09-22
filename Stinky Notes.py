#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Sticky Notes Lite
------------------
Notas adesivas leves, sempre por cima de todas as janelas, com cor,
tamanho, opacidade e conteúdo (texto + imagem) customizáveis.

Barra de controle: +Nota, -Nota (apaga a mais recente), Fechar (fecha o
programa inteiro, notas incluídas) e Grade (grade visual + encaixe
automático para alinhar as notas ao mover/redimensionar).

Atalho global Ctrl+Alt+X: liga/desliga o modo "clique-através" em TODAS
as notas ao mesmo tempo (o mouse passa pelas notas e interage com o que
está por baixo, mesmo com as notas continuando visíveis e no topo).
Cada nota também tem essa opção individual no menu do botão direito.

Atalho global Ctrl+Alt+L: esconde/mostra a barra de controle.

Os atalhos globais usam a API nativa do Windows (RegisterHotKey), sem
biblioteca externa — mais estável do que hooks de teclado de terceiros.

Requisitos:
  - Python 3.9+ no Windows (usa API do Windows para o clique-através e os atalhos)
  - Opcional: Pillow            -> pip install Pillow   (imagens JPEG e redimensionamento)

Executar:
  python sticky_notes.py
"""

import os
import sys
import json
import shutil
import uuid
import ctypes
import logging
import threading
import tkinter as tk
from ctypes import wintypes
from tkinter import colorchooser, filedialog, messagebox

IS_WINDOWS = sys.platform.startswith("win")

try:
    from PIL import Image, ImageTk
    HAS_PIL = True
    try:
        RESAMPLE = Image.Resampling.LANCZOS
    except AttributeError:
        RESAMPLE = Image.LANCZOS
except ImportError:
    HAS_PIL = False
    RESAMPLE = None


APP_DIR = os.path.join(os.path.expanduser("~"), ".sticky_notes_lite")
IMG_DIR = os.path.join(APP_DIR, "imagens")
DATA_FILE = os.path.join(APP_DIR, "notas.json")
LOG_FILE = os.path.join(APP_DIR, "sticky_notes.log")
os.makedirs(IMG_DIR, exist_ok=True)

logging.basicConfig(
    filename=LOG_FILE,
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    encoding="utf-8",
)
log = logging.getLogger("sticky_notes")


GWL_EXSTYLE = -20
WS_EX_LAYERED = 0x00080000
WS_EX_TRANSPARENT = 0x00000020


def _get_toplevel_hwnd(win: tk.Toplevel):
    """Devolve o HWND real da janela de nível superior, ou None.

    O winfo_id() do Tk normalmente é o HWND de uma janela filha, cujo pai é
    o wrapper de nível superior (por isso GetParent). Mas com
    overrideredirect(True), ou dependendo da versão do Tk, o winfo_id() já
    pode ser o próprio nível superior e GetParent devolve 0 (ou a janela
    errada). Aqui tentamos GetParent e caímos no próprio id se vier nulo."""
    user32 = ctypes.windll.user32
    user32.GetParent.argtypes = [wintypes.HWND]
    user32.GetParent.restype = wintypes.HWND

    own = win.winfo_id()
    parent = user32.GetParent(own)
    return parent or own or None


def set_click_through(win: tk.Toplevel, enable: bool):
    """Ativa/desativa o clique-através de uma janela Toplevel no Windows."""
    if not IS_WINDOWS:
        return
    try:
        win.update_idletasks()
        hwnd = _get_toplevel_hwnd(win)
        if not hwnd:
            log.warning("set_click_through: não foi possível obter o HWND da janela.")
            return

        user32 = ctypes.windll.user32
        # Tipos explícitos: sem isso o HWND é truncado para 32 bits em Python 64 bits.
        user32.GetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int]
        user32.GetWindowLongW.restype = ctypes.c_long
        user32.SetWindowLongW.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_long]
        user32.SetWindowLongW.restype = ctypes.c_long

        ctypes.windll.kernel32.SetLastError(0)
        style = user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
        if style == 0 and ctypes.GetLastError() != 0:
            log.warning("set_click_through: GetWindowLongW falhou (erro %s).",
                        ctypes.GetLastError())
            return

        if enable:
            style |= (WS_EX_LAYERED | WS_EX_TRANSPARENT)
        else:
            style = (style | WS_EX_LAYERED) & ~WS_EX_TRANSPARENT

        ctypes.windll.kernel32.SetLastError(0)
        user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style)
        if ctypes.GetLastError() != 0:
            log.warning("set_click_through: SetWindowLongW falhou (erro %s).",
                        ctypes.GetLastError())
    except Exception:
        log.exception("set_click_through falhou")


WM_HOTKEY = 0x0312
WM_QUIT = 0x0012
PM_NOREMOVE = 0x0000
MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_NOREPEAT = 0x4000


class _POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class _MSG(ctypes.Structure):
    _fields_ = [
        ("hwnd", ctypes.c_void_p),
        ("message", ctypes.c_uint),
        ("wParam", ctypes.c_size_t),
        ("lParam", ctypes.c_ssize_t),
        ("time", ctypes.c_uint32),
        ("pt", _POINT),
    ]


class GlobalHotkeys:
    """Registra atalhos globais via RegisterHotKey e escuta as mensagens
    WM_HOTKEY numa thread própria (é preciso ser a mesma thread que
    registrou os atalhos). Cada disparo é repassado para a thread
    principal do Tkinter com root.after(0, callback), que é a forma segura
    de mexer na interface a partir de outra thread.

    UnregisterHotKey também precisa ser chamado na thread que registrou,
    então stop() não desregistra diretamente: ele posta WM_QUIT na thread
    do listener, que sai do loop e desregistra tudo no bloco finally."""

    def __init__(self, root):
        self.root = root
        self._bindings = {}
        self._registered = []
        self._next_id = 1
        self._thread = None
        self._thread_id = None
        self._ready = threading.Event()

    def add(self, modifiers, vk_code, callback):
        hk_id = self._next_id
        self._next_id += 1
        self._bindings[hk_id] = (modifiers, vk_code, callback)
        return hk_id

    def start(self):
        if not IS_WINDOWS or not self._bindings:
            return
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()

    def stop(self, timeout=1.0):
        """Encerra o listener e libera os atalhos registrados."""
        if not IS_WINDOWS or self._thread is None:
            return
        # Espera a thread ter criado a fila de mensagens; sem isso o
        # PostThreadMessageW poderia falhar se stop() fosse chamado logo
        # depois de start().
        self._ready.wait(timeout)
        if self._thread_id:
            ctypes.windll.user32.PostThreadMessageW(self._thread_id, WM_QUIT, 0, 0)
        self._thread.join(timeout)
        self._thread = None
        self._thread_id = None

    def _run(self):
        user32 = ctypes.windll.user32
        self._thread_id = ctypes.windll.kernel32.GetCurrentThreadId()
        msg = _MSG()
        # Força a criação da fila de mensagens desta thread antes de
        # sinalizar que ela está pronta para receber WM_QUIT.
        user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, PM_NOREMOVE)
        self._ready.set()

        try:
            for hk_id, (mods, vk, _cb) in self._bindings.items():
                if user32.RegisterHotKey(None, hk_id, mods | MOD_NOREPEAT, vk):
                    self._registered.append(hk_id)
                else:
                    log.warning("Não foi possível registrar o atalho global id=%s "
                                "(outro programa pode já estar usando essa combinação).", hk_id)

            while True:
                ret = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if ret <= 0:  # 0 = WM_QUIT, -1 = erro
                    break
                if msg.message == WM_HOTKEY:
                    binding = self._bindings.get(msg.wParam)
                    if binding:
                        try:
                            self.root.after(0, binding[2])
                        except Exception:
                            # root já destruído durante o encerramento
                            log.debug("Atalho disparado com a interface já encerrada.")
                user32.TranslateMessage(ctypes.byref(msg))
                user32.DispatchMessageW(ctypes.byref(msg))
        finally:
            for hk_id in self._registered:
                user32.UnregisterHotKey(None, hk_id)
            self._registered.clear()


DEFAULT_COLOR = "#FFF59D"
DEFAULT_OPACITY = 0.95
DEFAULT_W, DEFAULT_H = 240, 220
MIN_W, MIN_H = 140, 120
GRID_SIZE = 20
RESIZE_RENDER_DELAY_MS = 80


class StickyNote:
    def __init__(self, app, data=None):
        data = data or {}
        self.app = app
        self.color = data.get("color", DEFAULT_COLOR)
        self.opacity = data.get("opacity", DEFAULT_OPACITY)
        self.image_path = data.get("image")
        self.image_only = data.get("image_only", False)
        self.click_through = False
        self._save_job = None
        self._render_job = None
        self._photo_ref = None
        self._pil_full_image = None

        x = data.get("x", 100)
        y = data.get("y", 100)
        w = data.get("w", DEFAULT_W)
        h = data.get("h", DEFAULT_H)

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.attributes("-topmost", True)
        try:
            self.win.attributes("-alpha", self.opacity)
        except tk.TclError:
            pass
        self.win.geometry(f"{w}x{h}+{x}+{y}")
        self.win.configure(bg=self.color)
        self.win.minsize(MIN_W, MIN_H)

        self._build_ui(data.get("text", ""))

        if self.image_path and os.path.exists(self.image_path):
            self._load_image(self.image_path, persist=False)

    def _build_ui(self, text):
        self.bar = tk.Frame(self.win, bg=self._darker(self.color), height=18, cursor="fleur")
        self.bar.bind("<ButtonPress-1>", self._start_move)
        self.bar.bind("<B1-Motion>", self._do_move)
        self.bar.bind("<Button-3>", self._show_menu)

        self.close_btn = tk.Label(self.bar, text="×", bg=self._darker(self.color), fg="#3a3a3a",
                                   font=("Segoe UI", 10, "bold"), cursor="hand2")
        self.close_btn.pack(side="right", padx=5)
        self.close_btn.bind("<Button-1>", lambda e: self.close())

        self.pin_btn = tk.Label(self.bar, text="•", bg=self._darker(self.color), fg="#3a3a3a",
                                 font=("Segoe UI", 9), cursor="hand2")
        self.pin_btn.pack(side="right", padx=2)
        self.pin_btn.bind("<Button-1>", lambda e: self._toggle_pin())

        self.img_label = tk.Label(self.win, bg=self.color, bd=0)

        self.text_widget = tk.Text(self.win, wrap="word", bd=0, highlightthickness=0,
                                    bg=self.color, fg="#2b2b2b", font=("Segoe UI", 11))
        self.text_widget.insert("1.0", text)
        self.text_widget.bind("<KeyRelease>", lambda e: self._save_debounced())
        self.text_widget.bind("<Button-3>", self._show_menu)

        self.grip = tk.Label(self.win, text="◢", bg=self.color, fg="#8d8d6b", cursor="size_nw_se")
        self.grip.bind("<ButtonPress-1>", self._start_resize)
        self.grip.bind("<B1-Motion>", self._do_resize)
        self.grip.bind("<ButtonRelease-1>", self._end_resize)

        self._relayout_body()

    def _relayout_body(self):
        """Reempacota barra (se não estiver em clique-através) -> imagem
        (se houver) -> texto, sempre nessa ordem, e mostra/esconde a alça
        de redimensionar. No modo 'somente imagem', o texto some e a
        imagem ocupa todo o corpo da nota. Chamado sempre que a barra, a
        imagem, o modo somente-imagem ou o clique-através mudam."""
        self.bar.pack_forget()
        self.img_label.pack_forget()
        self.text_widget.pack_forget()
        self.grip.place_forget()

        if not self.click_through:
            self.bar.pack(fill="x", side="top")

        if self.image_only and self.image_path:
            self.img_label.pack(fill="both", expand=True)
        else:
            if self.image_path:
                self.img_label.pack(fill="x", padx=6, pady=(4, 0))
            self.text_widget.pack(fill="both", expand=True, padx=6, pady=(4, 0))

        if not self.click_through:
            self.grip.place(relx=1.0, rely=1.0, anchor="se")


    def _snap(self, value):
        """Arredonda para o múltiplo mais próximo de GRID_SIZE quando a
        grade de alinhamento (botão 'Grade' no menu) está ativa."""
        if self.app.grid_enabled:
            return round(value / GRID_SIZE) * GRID_SIZE
        return value

    def _start_move(self, event):
        if self.click_through:
            return
        self._move_x, self._move_y = event.x, event.y

    def _do_move(self, event):
        if self.click_through:
            return
        x = self._snap(self.win.winfo_x() + (event.x - self._move_x))
        y = self._snap(self.win.winfo_y() + (event.y - self._move_y))
        self.win.geometry(f"+{x}+{y}")
        self._save_debounced()

    def _start_resize(self, event):
        if self.click_through:
            return
        self._rw, self._rh = self.win.winfo_width(), self.win.winfo_height()
        self._rx, self._ry = event.x_root, event.y_root

    def _do_resize(self, event):
        if self.click_through:
            return
        raw_w = self._rw + (event.x_root - self._rx)
        raw_h = self._rh + (event.y_root - self._ry)
        w = max(MIN_W, self._snap(raw_w))
        h = max(MIN_H, self._snap(raw_h))
        self.win.geometry(f"{w}x{h}")
        if self.image_only and self.image_path:
            self._render_image_debounced()
        self._save_debounced()

    def _end_resize(self, event=None):
        """Ao soltar o botão, garante a imagem final nítida e no tamanho
        exato, sem esperar o timer do debounce."""
        if self._render_job is not None:
            self.app.root.after_cancel(self._render_job)
            self._render_job = None
        if self.image_only and self.image_path and not self.click_through:
            self._render_image_for_current_size()

    def _render_image_debounced(self, delay=RESIZE_RENDER_DELAY_MS):
        """Adia a re-renderização da imagem enquanto o usuário ainda está
        arrastando. O resize com LANCZOS é a parte cara; a janela em si
        acompanha o mouse normalmente porque o geometry() é imediato."""
        if self._render_job is not None:
            self.app.root.after_cancel(self._render_job)
        self._render_job = self.app.root.after(delay, self._run_debounced_render)

    def _run_debounced_render(self):
        self._render_job = None
        if self.image_only and self.image_path:
            self._render_image_for_current_size()

    def _show_menu(self, event):
        menu = tk.Menu(self.win, tearoff=0)
        menu.add_command(label="Cor de fundo...", command=self._pick_color)

        op_menu = tk.Menu(menu, tearoff=0)
        for pct in (100, 90, 75, 50, 30, 15):
            op_menu.add_command(label=f"{pct}%", command=lambda p=pct: self._set_opacity(p / 100))
        menu.add_cascade(label="Opacidade", menu=op_menu)

        menu.add_command(label="Inserir imagem...", command=self._pick_image)
        if self.image_path:
            label_img_only = "Desativar modo somente imagem" if self.image_only else "Ativar modo somente imagem"
            menu.add_command(label=label_img_only, command=self._toggle_image_only)
            menu.add_command(label="Remover imagem", command=self._remove_image)

        menu.add_separator()
        label_pin = "Desativar clique-através" if self.click_through else "Ativar clique-através (nesta nota)"
        menu.add_command(label=label_pin, command=self._toggle_pin)

        menu.add_separator()
        menu.add_command(label="Nova nota", command=self.app.new_note)
        menu.add_command(label="Fechar esta nota", command=self.close)
        menu.tk_popup(event.x_root, event.y_root)

    def _pick_color(self):
        _, hexcolor = colorchooser.askcolor(color=self.color, title="Escolher cor da nota")
        if hexcolor:
            self.color = hexcolor
            self._apply_color()
            self._save_debounced()

    def _apply_color(self):
        darker = self._darker(self.color)
        self.win.configure(bg=self.color)
        self.bar.configure(bg=darker)
        self.close_btn.configure(bg=darker)
        self.pin_btn.configure(bg=darker)
        self.text_widget.configure(bg=self.color)
        self.img_label.configure(bg=self.color)
        self.grip.configure(bg=self.color)

    def _set_opacity(self, value):
        self.opacity = value
        try:
            self.win.attributes("-alpha", value)
        except tk.TclError:
            pass
        self._save_debounced()

    @staticmethod
    def _darker(hexcolor, factor=0.82):
        hexcolor = hexcolor.lstrip("#")
        try:
            r, g, b = (int(hexcolor[i:i + 2], 16) for i in (0, 2, 4))
        except ValueError:
            r, g, b = (255, 245, 157)
        r, g, b = (max(0, int(c * factor)) for c in (r, g, b))
        return f"#{r:02x}{g:02x}{b:02x}"

    def _pick_image(self):
        path = filedialog.askopenfilename(
            title="Escolher imagem",
            filetypes=[("Imagens", "*.png *.jpg *.jpeg"), ("PNG", "*.png"), ("JPEG", "*.jpg *.jpeg")],
        )
        if not path:
            return
        ext = os.path.splitext(path)[1].lower()
        if ext in (".jpg", ".jpeg") and not HAS_PIL:
            messagebox.showwarning(
                "Sem suporte a JPEG",
                "Para usar imagens JPEG, instale a biblioteca Pillow:\n\npip install Pillow\n\n"
                "Sem ela, apenas PNG é suportado.",
            )
            return
        dest = os.path.join(IMG_DIR, f"{uuid.uuid4().hex}{ext}")
        try:
            shutil.copyfile(path, dest)
        except Exception as e:
            log.exception("Falha ao copiar a imagem %s para %s", path, dest)
            messagebox.showerror("Erro ao copiar imagem", str(e))
            return
        if not self._load_image(dest):
            # A cópia não serviu para nada: não deixa o arquivo no disco.
            self._delete_image_file(dest)

    def _load_image(self, path, persist=True):
        """Carrega a imagem na nota. Devolve True se deu certo."""
        old_path = self.image_path
        old_pil = self._pil_full_image
        try:
            self.image_path = path
            if HAS_PIL:
                with Image.open(path) as src:
                    # load() lê tudo para a memória; assim o arquivo fica
                    # livre logo, e não há handle aberto durante a sessão.
                    src.load()
                    self._pil_full_image = src.copy()
            else:
                self._pil_full_image = None
            self._relayout_body()
            self._render_image_for_current_size()
            if persist:
                self._save_debounced()
        except Exception as e:
            log.exception("Falha ao carregar a imagem %s", path)
            # Volta ao estado anterior para a nota não ficar apontando
            # para uma imagem que não abre.
            self.image_path = old_path
            self._pil_full_image = old_pil
            self._relayout_body()
            messagebox.showerror("Erro ao carregar imagem", str(e))
            return False

        # Troca bem-sucedida: a imagem anterior deixou de ser usada. Não é
        # apagada agora (o JSON salvo ainda a referencia até o próximo
        # save_all); a varredura de inicialização cuida disso.
        return True

    @staticmethod
    def _delete_image_file(path):
        """Apaga um arquivo dentro de IMG_DIR (nunca fora dele)."""
        try:
            img_dir = os.path.normcase(os.path.abspath(IMG_DIR))
            target = os.path.normcase(os.path.abspath(path))
            if os.path.dirname(target) != img_dir:
                return
            if os.path.isfile(target):
                os.remove(path)
        except OSError:
            log.warning("Não foi possível apagar a imagem %s", path, exc_info=True)

    def _render_image_for_current_size(self):
        """Desenha a imagem no tamanho certo para o espaço disponível na
        nota. No modo 'somente imagem', ela preenche todo o corpo (esticando
        para acompanhar o redimensionamento); no modo normal, vira uma
        miniatura acima do texto, preservando a proporção."""
        if not self.image_path:
            return
        try:
            self.win.update_idletasks()
            bar_h = self.bar.winfo_height() if self.bar.winfo_ismapped() else 0

            if self.image_only:
                avail_w = max(20, self.win.winfo_width())
                avail_h = max(20, self.win.winfo_height() - bar_h)
            else:
                avail_w = max(60, self.win.winfo_width() - 20)
                avail_h = 140

            if HAS_PIL:
                if self._pil_full_image is None:
                    with Image.open(self.image_path) as src:
                        src.load()
                        self._pil_full_image = src.copy()
                if self.image_only:
                    im = self._pil_full_image.resize((avail_w, avail_h), RESAMPLE)
                else:
                    im = self._pil_full_image.copy()
                    im.thumbnail((avail_w, avail_h), RESAMPLE)
                photo = ImageTk.PhotoImage(im)
            else:
                photo = tk.PhotoImage(file=self.image_path)

            self._photo_ref = photo
            self.img_label.configure(image=photo)
        except Exception as e:
            log.exception("Falha ao exibir a imagem %s", self.image_path)
            messagebox.showerror("Erro ao exibir imagem", str(e))

    def _toggle_image_only(self):
        if not self.image_path:
            return
        if not self.image_only and not HAS_PIL:
            messagebox.showinfo(
                "Recurso limitado sem Pillow",
                "Sem a biblioteca Pillow instalada, a imagem não acompanha o "
                "redimensionamento da nota (fica no tamanho original).\n\n"
                "Para redimensionar a imagem junto com a nota, instale:\n"
                "pip install Pillow",
            )
        self.image_only = not self.image_only
        self._relayout_body()
        if self.image_only:
            self._render_image_for_current_size()
        self._save_debounced()

    def _release_pil_image(self):
        """Fecha o arquivo aberto pelo Pillow. No Windows, um arquivo com
        handle aberto não pode ser apagado, e Image.open é preguiçoso."""
        if self._pil_full_image is not None:
            try:
                self._pil_full_image.close()
            except Exception:
                log.debug("Falha ao fechar a imagem do Pillow", exc_info=True)
            self._pil_full_image = None

    def _remove_image(self):
        self.image_path = None
        self._photo_ref = None
        self._release_pil_image()
        self.image_only = False
        self.img_label.configure(image="")
        self._relayout_body()
        self._save_debounced()

    def _toggle_pin(self):
        self.click_through = not self.click_through
        set_click_through(self.win, self.click_through)
        self._update_interactive_visuals()

    def _update_interactive_visuals(self):
        """Oculta a barra de título e a seta de redimensionamento (canto ◢)
        enquanto o clique-através estiver ativo, já que o mouse passa direto
        pela nota nesse modo e essas alças ficam inúteis; volta a mostrá-las
        quando o clique-através é desligado."""
        self._relayout_body()
        if self.image_only and self.image_path:
            self._render_image_for_current_size()

    def close(self):
        # Cancela timers pendentes: se disparassem depois do destroy(),
        # tentariam mexer em widgets que já não existem.
        for job in (self._render_job, self._save_job):
            if job is not None:
                try:
                    self.app.root.after_cancel(job)
                except tk.TclError:
                    pass
        self._render_job = self._save_job = None
        if self in self.app.notes:
            self.app.notes.remove(self)
        self._release_pil_image()
        self.win.destroy()
        self.app.save_all()

    def _save_debounced(self):
        if self._save_job:
            self.app.root.after_cancel(self._save_job)
        self._save_job = self.app.root.after(600, self.app.save_all)

    def to_dict(self):
        return {
            "color": self.color,
            "opacity": self.opacity,
            "text": self.text_widget.get("1.0", "end-1c"),
            "image": self.image_path,
            "image_only": self.image_only,
            "x": self.win.winfo_x(),
            "y": self.win.winfo_y(),
            "w": self.win.winfo_width(),
            "h": self.win.winfo_height(),
        }


class App:
    def __init__(self):
        self.root = tk.Tk()
        self.root.withdraw()
        self.notes = []
        self._launcher_visible = True
        self.grid_enabled = False
        self.grid_overlay = None
        self._save_error_shown = False
        self._grid_photo = None
        self.hotkeys = None

        self._build_launcher()
        self._load_all()
        self._register_hotkeys()

    def _register_hotkeys(self):
        if not IS_WINDOWS:
            print("Aviso: atalhos globais (Ctrl+Alt+X / Ctrl+Alt+L) exigem Windows. "
                  "Use o botão de fixar em cada nota para o clique-através.")
            log.info("Atalhos globais indisponíveis fora do Windows.")
            return
        self.hotkeys = GlobalHotkeys(self.root)
        self.hotkeys.add(MOD_CONTROL | MOD_ALT, ord("X"), self.toggle_all_click_through)
        self.hotkeys.add(MOD_CONTROL | MOD_ALT, ord("L"), self.toggle_launcher_visibility)
        self.hotkeys.start()

    def _build_launcher(self):
        self.launcher = tk.Toplevel(self.root)
        self.launcher.overrideredirect(True)
        self.launcher.attributes("-topmost", True)
        self.launcher.geometry("250x36+40+40")
        self.launcher.configure(bg="#2f2f2f")
        self.launcher.protocol("WM_DELETE_WINDOW", self.quit)

        bar = tk.Frame(self.launcher, bg="#2f2f2f")
        bar.pack(fill="both", expand=True)
        bar.bind("<ButtonPress-1>", self._start_move_launcher)
        bar.bind("<B1-Motion>", self._do_move_launcher)

        btn_style = dict(bd=0, cursor="hand2", font=("Segoe UI", 9), fg="white")

        tk.Button(bar, text="+Nota", command=self.new_note, bg="#4CAF50",
                  activebackground="#43a047", **btn_style).pack(side="left", fill="y", padx=(4, 2), pady=4)
        tk.Button(bar, text="-Nota", command=self.delete_last_note, bg="#e67e22",
                  activebackground="#d35400", **btn_style).pack(side="left", fill="y", padx=2, pady=4)
        tk.Button(bar, text="Fechar", command=self.quit, bg="#c0392b",
                  activebackground="#a93226", **btn_style).pack(side="left", fill="y", padx=2, pady=4)
        self.grid_btn = tk.Button(bar, text="Grade", command=self.toggle_grid, bg="#555555",
                                   activebackground="#666666", **btn_style)
        self.grid_btn.pack(side="left", fill="y", padx=(2, 4), pady=4)

    def _start_move_launcher(self, event):
        self._lx, self._ly = event.x, event.y

    def _do_move_launcher(self, event):
        x = self.launcher.winfo_x() + (event.x - self._lx)
        y = self.launcher.winfo_y() + (event.y - self._ly)
        self.launcher.geometry(f"+{x}+{y}")

    def toggle_launcher_visibility(self):
        """Esconde ou mostra a barra de controle (mesmo atalho liga/desliga)."""
        if self._launcher_visible:
            self.launcher.withdraw()
        else:
            self.launcher.deiconify()
            self.launcher.attributes("-topmost", True)
        self._launcher_visible = not self._launcher_visible

    def _create_note(self, data=None):
        note = StickyNote(self, data)
        self.notes.append(note)
        return note

    def new_note(self):
        self._create_note(None)
        self.save_all()

    def delete_last_note(self):
        """Exclui a nota criada mais recentemente (botão '-Nota')."""
        if not self.notes:
            return
        self.notes[-1].close()

    def toggle_all_click_through(self):
        turn_on = not any(n.click_through for n in self.notes)
        for n in self.notes:
            n.click_through = turn_on
            set_click_through(n.win, turn_on)
            n._update_interactive_visuals()

    def toggle_grid(self):
        """Liga/desliga a grade visual e o encaixe automático (snap) das
        notas nela, para alinhá-las com mais facilidade ao mover/redimensionar."""
        self.grid_enabled = not self.grid_enabled
        if self.grid_enabled:
            self._show_grid_overlay()
            self.grid_btn.configure(bg="#2980b9", activebackground="#2471a3")
        else:
            self._hide_grid_overlay()
            self.grid_btn.configure(bg="#555555", activebackground="#666666")

    @staticmethod
    def _grid_points(sw, sh):
        """Coordenadas (x, y) de cada ponto da grade, com um ponto 3x3 px
        centrado em cada cruzamento (equivalente ao oval de raio 1)."""
        for gx in range(0, sw, GRID_SIZE):
            for gy in range(0, sh, GRID_SIZE):
                yield gx, gy

    def _build_grid_image(self, sw, sh):
        """Monta o bitmap da grade uma única vez.

        Com Pillow, desenha os pontos direto no bitmap (ImageDraw). Sem
        Pillow, usa PhotoImage.put com faixas de pixels, o que continua
        sendo uma única imagem no Canvas."""
        dot = "#4caf50"
        bg = "#000000"
        if HAS_PIL:
            img = Image.new("RGB", (sw, sh), bg)
            px = img.load()
            for gx, gy in self._grid_points(sw, sh):
                for dx in (-1, 0, 1):
                    for dy in (-1, 0, 1):
                        x, y = gx + dx, gy + dy
                        if 0 <= x < sw and 0 <= y < sh:
                            px[x, y] = (0x4C, 0xAF, 0x50)
            return ImageTk.PhotoImage(img)

        photo = tk.PhotoImage(width=sw, height=sh)
        photo.put(bg, to=(0, 0, sw, sh))
        for gx, gy in self._grid_points(sw, sh):
            photo.put(dot, to=(max(0, gx - 1), max(0, gy - 1),
                               min(sw, gx + 2), min(sh, gy + 2)))
        return photo

    def _ensure_grid_overlay(self):
        """Cria (uma única vez) a janela de tela cheia com os pontos da
        grade. Fica sempre com clique-através, nunca atrapalha o mouse."""
        if self.grid_overlay is not None:
            return
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()

        win = tk.Toplevel(self.root)
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        try:
            win.attributes("-alpha", 0.45)
        except tk.TclError:
            pass
        win.geometry(f"{sw}x{sh}+0+0")
        win.configure(bg="#000000")

        canvas = tk.Canvas(win, width=sw, height=sh, bg="#000000", highlightthickness=0)
        canvas.pack(fill="both", expand=True)

        # Um único item de imagem no Canvas em vez de milhares de ovais.
        # A referência precisa ficar guardada, senão o Tk descarta a imagem.
        self._grid_photo = self._build_grid_image(sw, sh)
        canvas.create_image(0, 0, image=self._grid_photo, anchor="nw")

        set_click_through(win, True)
        win.withdraw()
        self.grid_overlay = win

    def _show_grid_overlay(self):
        self._ensure_grid_overlay()
        self.grid_overlay.deiconify()
        self.grid_overlay.attributes("-topmost", True)
        self.grid_overlay.lower()

    def _hide_grid_overlay(self):
        if self.grid_overlay is not None:
            self.grid_overlay.withdraw()

    def cleanup_unused_images(self):
        """Remove de IMG_DIR as imagens que nenhuma nota usa mais (sobras de
        imagens removidas, trocadas ou de notas fechadas).

        Feita na inicialização, e não no momento em que a imagem é
        desvinculada, de propósito: o save_all é adiado (debounce), então se
        o programa caísse logo após apagar o arquivo, o JSON ainda apontaria
        para uma imagem inexistente. Aqui só apagamos o que o JSON já salvo
        realmente não referencia."""
        in_use = {os.path.normcase(os.path.abspath(n.image_path))
                  for n in self.notes if n.image_path}
        try:
            names = os.listdir(IMG_DIR)
        except OSError:
            log.exception("Não foi possível listar %s para limpeza", IMG_DIR)
            return
        removed = 0
        for name in names:
            full = os.path.join(IMG_DIR, name)
            if not os.path.isfile(full):
                continue
            if os.path.normcase(os.path.abspath(full)) in in_use:
                continue
            try:
                os.remove(full)
                removed += 1
            except OSError:
                log.warning("Não foi possível remover a imagem órfã %s", full, exc_info=True)
        if removed:
            log.info("Limpeza: %d imagem(ns) órfã(s) removida(s).", removed)

    def save_all(self):
        """Grava as notas de forma atômica: escreve num arquivo temporário e
        só então troca o definitivo com os.replace. Se o programa cair ou o
        disco encher no meio da escrita, o notas.json anterior continua
        intacto em vez de ficar truncado/corrompido."""
        data = [n.to_dict() for n in self.notes]
        tmp_path = DATA_FILE + ".tmp"
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp_path, DATA_FILE)
            self._save_error_shown = False
        except Exception as e:
            log.exception("Falha ao salvar as notas em %s", DATA_FILE)
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except OSError:
                log.warning("Não foi possível remover o arquivo temporário %s", tmp_path)
            # Avisa o usuário uma única vez até um salvamento dar certo de novo:
            # o save_all roda a cada pausa de digitação e não dá para abrir um
            # popup toda vez.
            if not self._save_error_shown:
                self._save_error_shown = True
                messagebox.showerror(
                    "Erro ao salvar",
                    f"Não foi possível salvar as notas:\n{e}\n\n"
                    f"Detalhes em: {LOG_FILE}",
                )

    def _load_all(self):
        if os.path.exists(DATA_FILE):
            try:
                with open(DATA_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if data:
                    for d in data:
                        self._create_note(d)
                    self.cleanup_unused_images()
                    return
            except Exception:
                log.exception("Falha ao ler %s", DATA_FILE)
                # Preserva o arquivo problemático para o usuário poder tentar
                # recuperar o conteúdo, em vez de sobrescrevê-lo em silêncio.
                try:
                    backup = f"{DATA_FILE}.corrompido"
                    os.replace(DATA_FILE, backup)
                    log.warning("Arquivo de notas ilegível movido para %s", backup)
                    messagebox.showwarning(
                        "Notas não carregadas",
                        "Não foi possível ler o arquivo de notas.\n"
                        f"Uma cópia foi guardada em:\n{backup}",
                    )
                except OSError:
                    log.exception("Não foi possível preservar o arquivo corrompido")
        self._create_note({
            "text": ("Bem-vindo(a)!\n\n"
                     "- Arraste a barra de cima para mover.\n"
                     "- Arraste o canto ◢ para redimensionar.\n"
                     "- Botão direito: cor, opacidade, imagem, fixar.\n"
                     "- Barra de controle: +Nota, -Nota (apaga a mais\n"
                     "  recente), Fechar (fecha tudo) e Grade (alinhar).\n"
                     "- Ctrl+Alt+X: clique-através em todas as notas\n"
                     "  (a barra de título e o canto de redimensionar\n"
                     "  somem enquanto estiver ativo).\n"
                     "- Ctrl+Alt+L: esconde/mostra a barra de controle."),
        })
        self.save_all()

    def quit(self):
        """Fecha o programa inteiro: salva, e destrói a barra de controle,
        a grade e TODAS as notas de uma vez (elas são filhas da mesma
        janela raiz, então root.destroy() derruba tudo em cascata)."""
        self.save_all()
        if self.hotkeys is not None:
            self.hotkeys.stop()
        self.root.quit()
        self.root.destroy()
        sys.exit(0)

    def run(self):
        try:
            self.root.mainloop()
        finally:
            # Cobre encerramentos que não passam pelo quit() (ex.: Ctrl+C
            # no terminal ou exceção no mainloop). stop() é idempotente.
            if self.hotkeys is not None:
                self.hotkeys.stop()


if __name__ == "__main__":
    if not IS_WINDOWS:
        print("Aviso: este programa foi feito para Windows. O recurso de "
              "'clique-através' depende de APIs do Windows e não funcionará "
              "em outros sistemas (o resto do app continua funcional).")
    App().run()
