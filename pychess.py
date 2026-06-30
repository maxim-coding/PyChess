#!/usr/bin/env python3
"""
PyChess - A complete two-player chess game with timers and color themes.

Requires only the Python standard library (tkinter), no internet/pip needed.

Features:
- Full legal chess rules: castling, en passant, promotion, check/checkmate/stalemate,
  fifty-move/insufficient-material draw detection.
- Per-game timers (minutes + Fischer increment) with flag-fall loss.
- "New Game" dialog so you can start as many games as you like with your own time control.
- Color theme picker (several presets + fully custom colors via color chooser).
- Move highlighting, captured-piece tray, move list, undo, board flip.

Run with:  python3 chess_game.py
"""

import tkinter as tk
from tkinter import ttk, simpledialog, colorchooser, messagebox
import time
import copy

# ---------------------------------------------------------------------------
# Chess engine (pure logic, no GUI dependencies)
# ---------------------------------------------------------------------------

WHITE, BLACK = "w", "b"


def other(color):
    return BLACK if color == WHITE else WHITE


FILES = "abcdefgh"


def sq_name(r, c):
    return f"{FILES[c]}{8 - r}"


class Move:
    __slots__ = ("fr", "fc", "tr", "tc", "promo", "is_castle", "is_ep", "piece", "captured")

    def __init__(self, fr, fc, tr, tc, promo=None, is_castle=None, is_ep=False, piece=None, captured=None):
        self.fr, self.fc, self.tr, self.tc = fr, fc, tr, tc
        self.promo = promo            # 'Q','R','B','N' or None
        self.is_castle = is_castle    # 'K' / 'Q' / None
        self.is_ep = is_ep
        self.piece = piece
        self.captured = captured

    def uci(self):
        s = sq_name(self.fr, self.fc) + sq_name(self.tr, self.tc)
        if self.promo:
            s += self.promo.lower()
        return s


class Board:
    """8x8 board, row 0 = rank 8 (top, black side), row 7 = rank 1 (bottom, white side)."""

    def __init__(self):
        self.grid = [[None] * 8 for _ in range(8)]
        self.turn = WHITE
        self.castling = {"wK": True, "wQ": True, "bK": True, "bQ": True}
        self.ep_target = None  # (r, c) square that can be captured en passant this move
        self.halfmove_clock = 0
        self.history = []  # list of Move
        self.position_counts = {}
        self.setup_start()

    def setup_start(self):
        back = ["R", "N", "B", "Q", "K", "B", "N", "R"]
        for c in range(8):
            self.grid[0][c] = "b" + back[c]
            self.grid[1][c] = "bP"
            self.grid[6][c] = "wP"
            self.grid[7][c] = "w" + back[c]
        self.turn = WHITE
        self.castling = {"wK": True, "wQ": True, "bK": True, "bQ": True}
        self.ep_target = None
        self.halfmove_clock = 0
        self.history = []
        self.position_counts = {}

    def clone(self):
        b = Board.__new__(Board)
        b.grid = [row[:] for row in self.grid]
        b.turn = self.turn
        b.castling = dict(self.castling)
        b.ep_target = self.ep_target
        b.halfmove_clock = self.halfmove_clock
        b.history = []
        b.position_counts = {}
        return b

    def king_pos(self, color):
        target = color + "K"
        for r in range(8):
            for c in range(8):
                if self.grid[r][c] == target:
                    return r, c
        return None

    def in_bounds(self, r, c):
        return 0 <= r < 8 and 0 <= c < 8

    def is_attacked(self, r, c, by_color):
        """Is square (r,c) attacked by any piece of by_color?"""
        # Pawn attacks
        direction = 1 if by_color == WHITE else -1  # pawn of by_color attacks from row+direction
        for dc in (-1, 1):
            rr, cc = r + direction, c + dc
            if self.in_bounds(rr, cc) and self.grid[rr][cc] == by_color + "P":
                return True
        # Knight
        for dr, dc in [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]:
            rr, cc = r + dr, c + dc
            if self.in_bounds(rr, cc) and self.grid[rr][cc] == by_color + "N":
                return True
        # King
        for dr in (-1, 0, 1):
            for dc in (-1, 0, 1):
                if dr == 0 and dc == 0:
                    continue
                rr, cc = r + dr, c + dc
                if self.in_bounds(rr, cc) and self.grid[rr][cc] == by_color + "K":
                    return True
        # Sliding: rook/queen (straight)
        for dr, dc in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
            rr, cc = r + dr, c + dc
            while self.in_bounds(rr, cc):
                p = self.grid[rr][cc]
                if p is not None:
                    if p[0] == by_color and p[1] in ("R", "Q"):
                        return True
                    break
                rr += dr
                cc += dc
        # Sliding: bishop/queen (diagonal)
        for dr, dc in [(-1, -1), (-1, 1), (1, -1), (1, 1)]:
            rr, cc = r + dr, c + dc
            while self.in_bounds(rr, cc):
                p = self.grid[rr][cc]
                if p is not None:
                    if p[0] == by_color and p[1] in ("B", "Q"):
                        return True
                    break
                rr += dr
                cc += dc
        return False

    def in_check(self, color):
        kp = self.king_pos(color)
        if kp is None:
            return False
        return self.is_attacked(kp[0], kp[1], other(color))

    # ---- move generation ----

    def pseudo_moves_for(self, r, c):
        piece = self.grid[r][c]
        if piece is None:
            return []
        color, kind = piece[0], piece[1]
        moves = []

        def add(tr, tc, promo=None, is_castle=None, is_ep=False):
            moves.append(Move(r, c, tr, tc, promo, is_castle, is_ep, piece, self.grid[tr][tc]))

        if kind == "P":
            direction = -1 if color == WHITE else 1
            start_row = 6 if color == WHITE else 1
            promo_row = 0 if color == WHITE else 7
            # forward
            rr = r + direction
            if self.in_bounds(rr, c) and self.grid[rr][c] is None:
                if rr == promo_row:
                    for p in ("Q", "R", "B", "N"):
                        add(rr, c, promo=p)
                else:
                    add(rr, c)
                rr2 = r + 2 * direction
                if r == start_row and self.grid[rr2][c] is None:
                    add(rr2, c)
            # captures
            for dc in (-1, 1):
                rr, cc = r + direction, c + dc
                if self.in_bounds(rr, cc):
                    target = self.grid[rr][cc]
                    if target is not None and target[0] != color:
                        if rr == promo_row:
                            for p in ("Q", "R", "B", "N"):
                                add(rr, cc, promo=p)
                        else:
                            add(rr, cc)
                    elif self.ep_target == (rr, cc):
                        add(rr, cc, is_ep=True)

        elif kind == "N":
            for dr, dc in [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]:
                rr, cc = r + dr, c + dc
                if self.in_bounds(rr, cc):
                    target = self.grid[rr][cc]
                    if target is None or target[0] != color:
                        add(rr, cc)

        elif kind == "B" or kind == "R" or kind == "Q":
            dirs = []
            if kind in ("B", "Q"):
                dirs += [(-1, -1), (-1, 1), (1, -1), (1, 1)]
            if kind in ("R", "Q"):
                dirs += [(-1, 0), (1, 0), (0, -1), (0, 1)]
            for dr, dc in dirs:
                rr, cc = r + dr, c + dc
                while self.in_bounds(rr, cc):
                    target = self.grid[rr][cc]
                    if target is None:
                        add(rr, cc)
                    else:
                        if target[0] != color:
                            add(rr, cc)
                        break
                    rr += dr
                    cc += dc

        elif kind == "K":
            for dr in (-1, 0, 1):
                for dc in (-1, 0, 1):
                    if dr == 0 and dc == 0:
                        continue
                    rr, cc = r + dr, c + dc
                    if self.in_bounds(rr, cc):
                        target = self.grid[rr][cc]
                        if target is None or target[0] != color:
                            add(rr, cc)
            # castling
            row = 7 if color == WHITE else 0
            if r == row and c == 4 and not self.in_check(color):
                # kingside
                if self.castling[color + "K"] and self.grid[row][5] is None and self.grid[row][6] is None:
                    if self.grid[row][7] == color + "R":
                        if not self.is_attacked(row, 5, other(color)) and not self.is_attacked(row, 6, other(color)):
                            add(row, 6, is_castle="K")
                # queenside
                if self.castling[color + "Q"] and self.grid[row][1] is None and self.grid[row][2] is None and self.grid[row][3] is None:
                    if self.grid[row][0] == color + "R":
                        if not self.is_attacked(row, 3, other(color)) and not self.is_attacked(row, 2, other(color)):
                            add(row, 2, is_castle="Q")
        return moves

    def all_pseudo_moves(self, color):
        moves = []
        for r in range(8):
            for c in range(8):
                p = self.grid[r][c]
                if p is not None and p[0] == color:
                    moves.extend(self.pseudo_moves_for(r, c))
        return moves

    def make_move(self, mv: Move, record=True):
        color = mv.piece[0]
        kind = mv.piece[1]

        # update castling rights
        if kind == "K":
            self.castling[color + "K"] = False
            self.castling[color + "Q"] = False
        if mv.fr == 7 and mv.fc == 0 or mv.tr == 7 and mv.tc == 0:
            self.castling["wQ"] = False
        if mv.fr == 7 and mv.fc == 7 or mv.tr == 7 and mv.tc == 7:
            self.castling["wK"] = False
        if mv.fr == 0 and mv.fc == 0 or mv.tr == 0 and mv.tc == 0:
            self.castling["bQ"] = False
        if mv.fr == 0 and mv.fc == 7 or mv.tr == 0 and mv.tc == 7:
            self.castling["bK"] = False

        # en passant capture removal
        if mv.is_ep:
            cap_row = mv.fr
            cap_col = mv.tc
            self.grid[cap_row][cap_col] = None

        # move the piece
        self.grid[mv.fr][mv.fc] = None
        placed = mv.piece
        if mv.promo:
            placed = color + mv.promo
        self.grid[mv.tr][mv.tc] = placed

        # castling rook move
        if mv.is_castle == "K":
            row = mv.fr
            self.grid[row][5] = self.grid[row][7]
            self.grid[row][7] = None
        elif mv.is_castle == "Q":
            row = mv.fr
            self.grid[row][3] = self.grid[row][0]
            self.grid[row][0] = None

        # en passant target for next move
        if kind == "P" and abs(mv.tr - mv.fr) == 2:
            self.ep_target = ((mv.fr + mv.tr) // 2, mv.fc)
        else:
            self.ep_target = None

        # halfmove clock (50-move rule)
        if kind == "P" or mv.captured is not None or mv.is_ep:
            self.halfmove_clock = 0
        else:
            self.halfmove_clock += 1

        self.turn = other(self.turn)
        if record:
            self.history.append(mv)

    def legal_moves(self, color=None):
        color = color or self.turn
        legal = []
        for mv in self.all_pseudo_moves(color):
            trial = self.clone()
            trial.make_move(mv, record=False)
            if not trial.in_check(color):
                legal.append(mv)
        return legal

    def legal_moves_from(self, r, c):
        color = self.grid[r][c][0] if self.grid[r][c] else None
        if color != self.turn:
            return []
        out = []
        for mv in self.pseudo_moves_for(r, c):
            trial = self.clone()
            trial.make_move(mv, record=False)
            if not trial.in_check(color):
                out.append(mv)
        return out

    def game_status(self):
        """Returns one of: 'playing', 'checkmate', 'stalemate', 'draw50', 'insufficient'"""
        moves = self.legal_moves(self.turn)
        if not moves:
            if self.in_check(self.turn):
                return "checkmate"
            return "stalemate"
        if self.halfmove_clock >= 100:
            return "draw50"
        if self.insufficient_material():
            return "insufficient"
        return "playing"

    def insufficient_material(self):
        pieces = []
        for row in self.grid:
            for p in row:
                if p and p[1] != "K":
                    pieces.append(p[1])
        if not pieces:
            return True
        if len(pieces) == 1 and pieces[0] in ("N", "B"):
            return True
        if len(pieces) == 2 and pieces.count("B") == 2:
            return True
        return False


# ---------------------------------------------------------------------------
# Chess AI (minimax with alpha-beta pruning)
# ---------------------------------------------------------------------------

_PIECE_VAL = {"P": 100, "N": 320, "B": 330, "R": 500, "Q": 900, "K": 0}

# Simple piece-square tables (from White's perspective, row 0 = rank 8).
_PST_PAWN = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [50, 50, 50, 50, 50, 50, 50, 50],
    [10, 10, 20, 30, 30, 20, 10, 10],
    [5, 5, 10, 25, 25, 10, 5, 5],
    [0, 0, 0, 20, 20, 0, 0, 0],
    [5, -5, -10, 0, 0, -10, -5, 5],
    [5, 10, 10, -20, -20, 10, 10, 5],
    [0, 0, 0, 0, 0, 0, 0, 0],
]
_PST_KNIGHT = [
    [-50, -40, -30, -30, -30, -30, -40, -50],
    [-40, -20, 0, 0, 0, 0, -20, -40],
    [-30, 0, 10, 15, 15, 10, 0, -30],
    [-30, 5, 15, 20, 20, 15, 5, -30],
    [-30, 0, 15, 20, 20, 15, 0, -30],
    [-30, 5, 10, 15, 15, 10, 5, -30],
    [-40, -20, 0, 5, 5, 0, -20, -40],
    [-50, -40, -30, -30, -30, -30, -40, -50],
]
_PST_BISHOP = [
    [-20, -10, -10, -10, -10, -10, -10, -20],
    [-10, 0, 0, 0, 0, 0, 0, -10],
    [-10, 0, 5, 10, 10, 5, 0, -10],
    [-10, 5, 5, 10, 10, 5, 5, -10],
    [-10, 0, 10, 10, 10, 10, 0, -10],
    [-10, 10, 10, 10, 10, 10, 10, -10],
    [-10, 5, 0, 0, 0, 0, 5, -10],
    [-20, -10, -10, -10, -10, -10, -10, -20],
]
_PST_KING_MID = [
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-30, -40, -40, -50, -50, -40, -40, -30],
    [-20, -30, -30, -40, -40, -30, -30, -20],
    [-10, -20, -20, -20, -20, -20, -20, -10],
    [20, 20, 0, 0, 0, 0, 20, 20],
    [20, 30, 10, 0, 0, 10, 30, 20],
]
_PST = {"P": _PST_PAWN, "N": _PST_KNIGHT, "B": _PST_BISHOP, "K": _PST_KING_MID}


def _pst_value(piece, r, c):
    kind = piece[1]
    table = _PST.get(kind)
    if table is None:
        return 0
    rr = r if piece[0] == WHITE else 7 - r
    return table[rr][c]


def evaluate_board(board):
    """Positive = good for White, negative = good for Black, in centipawns."""
    score = 0
    for r in range(8):
        for c in range(8):
            p = board.grid[r][c]
            if p is None:
                continue
            val = _PIECE_VAL[p[1]] + _pst_value(p, r, c)
            score += val if p[0] == WHITE else -val
    return score


def _ordered_moves(board, color):
    moves = board.legal_moves(color)
    moves.sort(key=lambda m: _PIECE_VAL.get(m.captured[1], 0) if m.captured else 0, reverse=True)
    return moves


def _minimax(board, depth, alpha, beta, maximizing):
    status = board.game_status()
    if status == "checkmate":
        return (-100000 - depth) if maximizing else (100000 + depth)
    if status in ("stalemate", "draw50", "insufficient"):
        return 0
    if depth == 0:
        return evaluate_board(board)

    moves = _ordered_moves(board, board.turn)
    if maximizing:
        best = -float("inf")
        for mv in moves:
            trial = board.clone()
            trial.make_move(mv, record=False)
            val = _minimax(trial, depth - 1, alpha, beta, False)
            best = max(best, val)
            alpha = max(alpha, best)
            if beta <= alpha:
                break
        return best
    else:
        best = float("inf")
        for mv in moves:
            trial = board.clone()
            trial.make_move(mv, record=False)
            val = _minimax(trial, depth - 1, alpha, beta, True)
            best = min(best, val)
            beta = min(beta, best)
            if beta <= alpha:
                break
        return best


# difficulty -> (search depth, randomness in centipawns added as noise)
AI_DIFFICULTIES = {
    "Easy": (1, 120),
    "Medium": (2, 40),
    "Hard": (3, 0),
}


def ai_pick_move(board, difficulty="Medium"):
    """Pick a move for board.turn using minimax. Returns a Move or None."""
    import random
    depth, noise = AI_DIFFICULTIES.get(difficulty, (2, 40))
    color = board.turn
    moves = _ordered_moves(board, color)
    if not moves:
        return None
    maximizing_root = (color == WHITE)
    best_move = None
    best_val = -float("inf") if maximizing_root else float("inf")
    for mv in moves:
        trial = board.clone()
        trial.make_move(mv, record=False)
        val = _minimax(trial, depth - 1, -float("inf"), float("inf"), not maximizing_root)
        if noise:
            val += random.uniform(-noise, noise)
        if maximizing_root and val > best_val:
            best_val, best_move = val, mv
        elif not maximizing_root and val < best_val:
            best_val, best_move = val, mv
    return best_move or moves[0]


# ---------------------------------------------------------------------------
# Color themes
# ---------------------------------------------------------------------------
# Clean, modern palettes (a light "Lichess-style" board is the default).
# Every theme defines the full UI palette plus board colors so switching
# themes restyles the whole window consistently.

THEMES = {
    "Noir": dict(
        bg="#0c0c0d", surface="#161617", surface2="#1f1f21", border="#2c2c2f",
        text="#f1f0ec", text_muted="#9b9a96", accent="#c9a227", accent_text="#0c0c0d",
        board_light="#3c3b39", board_dark="#141414", select="#c9a227", legal="#c9a227", check="#b3413a",
    ),
    "Daylight": dict(
        bg="#f6f7f5", surface="#ffffff", surface2="#eef1ed", border="#e0e3de",
        text="#1f2421", text_muted="#6b7368", accent="#3aa655", accent_text="#ffffff",
        board_light="#eeeed2", board_dark="#7a9b5e", select="#f6f06b", legal="#3aa655", check="#e5534b",
    ),
    "Midnight": dict(
        bg="#14161b", surface="#1b1e25", surface2="#22262e", border="#2c313a",
        text="#eceef2", text_muted="#8b93a3", accent="#5b8def", accent_text="#0d1420",
        board_light="#5b6478", board_dark="#262b35", select="#5b8def", legal="#5b8def", check="#e5534b",
    ),
    "Walnut": dict(
        bg="#f6efe4", surface="#fffaf2", surface2="#efe2cc", border="#ddcaaa",
        text="#352a1f", text_muted="#8a7763", accent="#b5793a", accent_text="#ffffff",
        board_light="#f0d9b5", board_dark="#b5854f", select="#f6e07a", legal="#b5793a", check="#d9534f",
    ),
    "Ocean": dict(
        bg="#eef5fb", surface="#ffffff", surface2="#e1edf7", border="#cfe0ee",
        text="#16313f", text_muted="#5e7c8c", accent="#1f8fd6", accent_text="#ffffff",
        board_light="#e9f1f7", board_dark="#5d8fae", select="#bfe3ff", legal="#1f8fd6", check="#e5534b",
    ),
    "Forest": dict(
        bg="#10160f", surface="#161e15", surface2="#1c261a", border="#283322",
        text="#e9f0e4", text_muted="#8aa17f", accent="#5fbf5f", accent_text="#0b1409",
        board_light="#3c4a35", board_dark="#1f291c", select="#5fbf5f", legal="#5fbf5f", check="#e5534b",
    ),
}

PIECE_UNICODE = {
    "wK": "\u2654", "wQ": "\u2655", "wR": "\u2656", "wB": "\u2657", "wN": "\u2658", "wP": "\u2659",
    "bK": "\u265A", "bQ": "\u265B", "bR": "\u265C", "bB": "\u265D", "bN": "\u265E", "bP": "\u265F",
}

PIECE_VALUE = {"P": 1, "N": 3, "B": 3, "R": 5, "Q": 9, "K": 0}

# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------

SQUARE = 80
BOARD_PX = SQUARE * 8
FONT_FAMILY = "Helvetica"


def _hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def _rgb_to_hex(rgb):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(v))) for v in rgb)


def shade(hexcolor, factor):
    """factor > 1 lightens, < 1 darkens."""
    r, g, b = _hex_to_rgb(hexcolor)
    return _rgb_to_hex((r * factor, g * factor, b * factor))


def mix(hex_a, hex_b, t):
    a, b = _hex_to_rgb(hex_a), _hex_to_rgb(hex_b)
    return _rgb_to_hex(tuple(a[i] + (b[i] - a[i]) * t for i in range(3)))


def is_light(hexcolor):
    r, g, b = _hex_to_rgb(hexcolor)
    return (r * 299 + g * 587 + b * 114) / 1000 > 150


def round_rect(canvas, x1, y1, x2, y2, radius=12, **kwargs):
    r = radius
    points = [
        x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r,
        x2, y2 - r, x2, y2, x2 - r, y2, x1 + r, y2,
        x1, y2, x1, y2 - r, x1, y1 + r, x1, y1,
    ]
    return canvas.create_polygon(points, smooth=True, **kwargs)


class Tooltip:
    """Small hover tooltip for icon-only buttons."""

    def __init__(self, widget, text, theme_getter):
        self.widget = widget
        self.text = text
        self.theme_getter = theme_getter
        self.tip = None
        widget.bind("<Enter>", self._show, add="+")
        widget.bind("<Leave>", self._hide, add="+")

    def _show(self, _event=None):
        if self.tip is not None:
            return
        t = self.theme_getter()
        x = self.widget.winfo_rootx() + self.widget.winfo_width() // 2
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 8
        self.tip = tk.Toplevel(self.widget)
        self.tip.overrideredirect(True)
        self.tip.attributes("-topmost", True)
        lbl = tk.Label(self.tip, text=self.text, font=(FONT_FAMILY, 9), bg=t["text"], fg=t["surface"],
                        padx=8, pady=4)
        lbl.pack()
        self.tip.update_idletasks()
        w = self.tip.winfo_width()
        self.tip.geometry(f"+{x - w // 2}+{y}")

    def _hide(self, _event=None):
        if self.tip is not None:
            self.tip.destroy()
            self.tip = None


class RoundedButton(tk.Canvas):
    """A real button: rounded rectangle, hover/press feedback, optional icon + label.

    variant: 'primary' (solid accent), 'secondary' (outlined), 'ghost' (icon-only, minimal).
    """

    def __init__(self, parent, theme, text="", icon="", command=None, variant="secondary",
                 width=132, height=40, radius=10, font_size=11, tooltip=None):
        bg = parent["bg"] if isinstance(parent["bg"], str) else theme["bg"]
        super().__init__(parent, width=width, height=height, highlightthickness=0, bd=0, bg=bg)
        self.theme = theme
        self.command = command
        self.variant = variant
        self.text = text
        self.icon = icon
        self.width, self.height, self.radius = width, height, radius
        self.font_size = font_size
        self.state = "normal"
        self.enabled = True
        self._draw()
        self.bind("<Enter>", lambda e: self._set_state("hover"))
        self.bind("<Leave>", lambda e: self._set_state("normal"))
        self.bind("<ButtonPress-1>", lambda e: self._set_state("active"))
        self.bind("<ButtonRelease-1>", self._on_release)
        if tooltip:
            Tooltip(self, tooltip, lambda: self.theme)

    def set_enabled(self, enabled):
        self.enabled = enabled
        self._set_state("disabled" if not enabled else "normal")

    def _palette(self):
        t = self.theme
        if not self.enabled:
            return dict(fill=t["surface2"], outline=t["border"], text=t["text_muted"])
        if self.variant == "primary":
            base = {"normal": t["accent"], "hover": shade(t["accent"], 1.1), "active": shade(t["accent"], 0.88)}
            return dict(fill=base[self.state if self.state in base else "normal"], outline="", text=t["accent_text"])
        if self.variant == "ghost":
            base = {"normal": t["surface"], "hover": t["surface2"], "active": t["border"]}
            return dict(fill=base.get(self.state, t["surface"]), outline=t["border"], text=t["text"])
        # secondary
        base = {"normal": t["surface"], "hover": t["surface2"], "active": t["border"]}
        return dict(fill=base.get(self.state, t["surface"]), outline=t["border"], text=t["text"])

    def _set_state(self, state):
        if state in ("hover", "active") and not self.enabled:
            return
        self.state = state if self.enabled else "disabled"
        self._draw()

    def _on_release(self, event):
        inside = 0 <= event.x <= self.width and 0 <= event.y <= self.height
        self._set_state("hover" if inside else "normal")
        if inside and self.enabled and self.command:
            self.command()

    def _draw(self):
        self.delete("all")
        pal = self._palette()
        round_rect(self, 1, 1, self.width - 1, self.height - 1, radius=self.radius,
                   fill=pal["fill"], outline=pal["outline"], width=1.2)
        cx = self.width / 2
        if self.icon and self.text:
            self.create_text(18, self.height / 2, text=self.icon, font=(FONT_FAMILY, self.font_size + 2), fill=pal["text"], anchor="w")
            self.create_text(self.width / 2 + 8, self.height / 2, text=self.text, font=(FONT_FAMILY, self.font_size, "bold"), fill=pal["text"])
        elif self.icon:
            self.create_text(cx, self.height / 2, text=self.icon, font=(FONT_FAMILY, self.font_size + 5), fill=pal["text"])
        else:
            self.create_text(cx, self.height / 2, text=self.text, font=(FONT_FAMILY, self.font_size, "bold"), fill=pal["text"])

    def retheme(self, theme):
        self.theme = theme
        self.configure(bg=self.master["bg"])
        self._draw()


class Chip(tk.Canvas):
    """Small pill-shaped clickable tag, used for theme swatches / time presets."""

    def __init__(self, parent, theme, text, command, width=104, height=30, selected=False):
        bg = parent["bg"]
        super().__init__(parent, width=width, height=height, highlightthickness=0, bd=0, bg=bg)
        self.theme = theme
        self.text = text
        self.command = command
        self.selected = selected
        self.width, self.height = width, height
        self._draw()
        self.bind("<Button-1>", lambda e: command())
        self.bind("<Enter>", lambda e: self._draw(hover=True))
        self.bind("<Leave>", lambda e: self._draw(hover=False))

    def _draw(self, hover=False):
        self.delete("all")
        t = self.theme
        if self.selected:
            fill, outline, fg = t["accent"], "", t["accent_text"]
        elif hover:
            fill, outline, fg = t["surface2"], t["border"], t["text"]
        else:
            fill, outline, fg = t["surface"], t["border"], t["text"]
        round_rect(self, 1, 1, self.width - 1, self.height - 1, radius=self.height / 2,
                   fill=fill, outline=outline, width=1)
        self.create_text(self.width / 2, self.height / 2, text=self.text,
                          font=(FONT_FAMILY, 9, "bold"), fill=fg)


    def set_selected(self, selected):
        self.selected = selected
        self._draw()


class Section(tk.Frame):
    """A clean bordered panel (1px border, flat fill) -- the basic card primitive."""

    def __init__(self, parent, theme, pad=16, **kw):
        super().__init__(parent, bg=theme["border"], **kw)
        self.body = tk.Frame(self, bg=theme["surface"], padx=pad, pady=pad)
        self.body.pack(fill="both", expand=True, padx=1, pady=1)


# ---------------------------------------------------------------------------
# Online play: a tiny relay using jsonblob.com, a free, no-signup JSON store.
# One player "hosts" (creates a blob = the game code), the other "joins" with
# that code. Each side polls for the opponent's moves over plain HTTPS.
# ---------------------------------------------------------------------------

import json
import random
import ssl
import threading
import urllib.request
import urllib.error

JSONBLOB_BASE = "https://jsonblob.com/api/jsonBlob"


def _urlopen(req, timeout=6):
    """Open a request, falling back to an unverified SSL context if the
    server's certificate can't be validated (e.g. an expired cert on a
    free third-party service) so a single broken relay host doesn't hard-fail
    online play."""
    try:
        return urllib.request.urlopen(req, timeout=timeout)
    except urllib.error.URLError as e:
        reason = getattr(e, "reason", e)
        if isinstance(reason, ssl.SSLError) or "CERTIFICATE_VERIFY_FAILED" in str(e):
            ctx = ssl.create_default_context()
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
            return urllib.request.urlopen(req, timeout=timeout, context=ctx)
        raise


def relay_create(initial_obj):
    """Creates a new shared JSON blob and returns its id (the 'game code')."""
    data = json.dumps(initial_obj).encode("utf-8")
    req = urllib.request.Request(JSONBLOB_BASE, data=data, method="POST",
                                  headers={"Content-Type": "application/json",
                                           "Accept": "application/json",
                                           "User-Agent": "PyChess/1.0"})
    with _urlopen(req) as resp:
        location = resp.headers.get("Location") or resp.geturl()
    if not location:
        raise RuntimeError("relay did not return a game id")
    return location.rstrip("/").split("/")[-1]


def relay_set(blob_id, obj):
    url = f"{JSONBLOB_BASE}/{blob_id}"
    data = json.dumps(obj).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="PUT",
                                  headers={"Content-Type": "application/json",
                                           "Accept": "application/json",
                                           "User-Agent": "PyChess/1.0"})
    with _urlopen(req):
        pass


def relay_get(blob_id):
    url = f"{JSONBLOB_BASE}/{blob_id}"
    req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "PyChess/1.0"})
    try:
        with _urlopen(req) as resp:
            raw = resp.read().decode("utf-8")
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise
    if not raw:
        return None
    try:
        return json.loads(raw)
    except ValueError:
        return None


class ChessApp:
    def __init__(self, root):
        self.root = root
        self.root.title("PyChess")
        self.root.minsize(1140, 840)
        self.theme_name = "Noir"
        self.theme = dict(THEMES[self.theme_name])
        self.flipped = False

        self.board = Board()
        self.selected = None
        self.legal_targets = {}
        self.last_move = None
        self.game_over = False

        self.base_time = 5 * 60
        self.increment = 0
        self.clock = {WHITE: self.base_time, BLACK: self.base_time}
        self.clock_running = False
        self.last_tick = None

        self._buttons = []   # all RoundedButton instances, for retheming
        self._sections = []  # all Section instances, for retheming

        # ---- Game mode: "local" (2 players, same device), "ai" (vs computer),
        # ---- "online" (vs a remote opponent over a shared game code/link) ----
        self.mode = "local"
        self.ai_difficulty = "Medium"
        self.ai_color = BLACK         # which side the computer plays
        self.ai_thinking = False

        self.online_bucket = None     # the shared "game code"
        self.online_color = None      # which side *this* device plays online
        self.online_role = None       # "host" or "guest"
        self.online_running = False
        self.online_applied = 0       # number of opponent moves already applied
        self.online_status_var = None

        self._build_ui()
        self._draw_board()
        self._update_captured()
        self._tick()

    # ---------------- UI construction ----------------

    def _build_ui(self):
        t = self.theme
        self.root.configure(bg=t["bg"])

        # ---- Top app bar ----
        self.appbar = tk.Frame(self.root, bg=t["surface"])
        self.appbar.pack(side="top", fill="x")
        bar = tk.Frame(self.appbar, bg=t["surface"], padx=24, pady=16)
        bar.pack(fill="x")
        self.appbar_inner = bar

        brand = tk.Frame(bar, bg=t["surface"])
        brand.pack(side="left")
        self.logo_lbl = tk.Label(brand, text="\u265A", font=(FONT_FAMILY, 20, "bold"), bg=t["surface"], fg=t["accent"])
        self.logo_lbl.pack(side="left")
        self.title_lbl = tk.Label(brand, text="PyChess", font=(FONT_FAMILY, 17, "bold"), bg=t["surface"], fg=t["text"])
        self.title_lbl.pack(side="left", padx=(8, 0))
        self.brand = brand

        actions = tk.Frame(bar, bg=t["surface"])
        actions.pack(side="right")
        self.actions = actions

        self.btn_new = RoundedButton(actions, t, text="New Game", icon="\u25B6", command=lambda: self.toggle_settings_panel("new"),
                                      variant="primary", width=148, height=42)
        self.btn_new.pack(side="left", padx=(0, 8))
        self._buttons.append(self.btn_new)

        self.btn_undo = RoundedButton(actions, t, icon="\u21B6", command=self.undo_move, variant="secondary",
                                       width=42, height=42, tooltip="Undo last move")
        self.btn_undo.pack(side="left", padx=4)
        self._buttons.append(self.btn_undo)

        self.btn_flip = RoundedButton(actions, t, icon="\u21C5", command=self.flip_board, variant="secondary",
                                       width=42, height=42, tooltip="Flip board")
        self.btn_flip.pack(side="left", padx=4)
        self._buttons.append(self.btn_flip)

        self.btn_theme = RoundedButton(actions, t, icon="\u2699", command=lambda: self.toggle_settings_panel("theme"), variant="secondary",
                                        width=42, height=42, tooltip="Themes & colors")
        self.btn_theme.pack(side="left", padx=4)
        self._buttons.append(self.btn_theme)

        self.appbar_divider = tk.Frame(self.root, bg=t["border"], height=1)
        self.appbar_divider.pack(fill="x")

        # ---- Inline settings panel (replaces popup windows) ----
        self.settings_visible = False
        self.settings_focus = "new"
        self.settings_panel = tk.Frame(self.root, bg=t["bg"])

        # ---- Status banner ----
        self.status_wrap = tk.Frame(self.root, bg=t["bg"])
        self.status_wrap.pack(side="top", fill="x")
        self.status_inner = tk.Frame(self.status_wrap, bg=t["surface2"])
        self.status_inner.pack(fill="x", padx=0, pady=0)
        status_pad = tk.Frame(self.status_inner, bg=t["surface2"], padx=24, pady=10)
        status_pad.pack(fill="x")
        self.status_accent = tk.Frame(status_pad, bg=t["accent"], width=4)
        self.status_accent.pack(side="left", fill="y", padx=(0, 12))
        self.status_lbl = tk.Label(status_pad, text="White to move", font=(FONT_FAMILY, 11, "bold"),
                                    bg=t["surface2"], fg=t["text"])
        self.status_lbl.pack(side="left")
        self.status_pad = status_pad

        # ---- Body: board + sidebar ----
        body = tk.Frame(self.root, bg=t["bg"])
        body.pack(side="top", fill="both", expand=True, padx=24, pady=20)
        self.body = body

        content = tk.Frame(body, bg=t["bg"])
        content.pack(expand=True)
        self.content = content

        board_col = tk.Frame(content, bg=t["bg"])
        board_col.pack(side="left", fill="y")
        self.board_col = board_col

        self.board_frame = tk.Frame(board_col, bg=t["border"])
        self.board_frame.pack()
        self.canvas = tk.Canvas(self.board_frame, width=BOARD_PX, height=BOARD_PX, highlightthickness=0, bd=0)
        self.canvas.pack(padx=1, pady=1)
        self.canvas.bind("<Button-1>", self.on_click)

        self.caption_lbl = tk.Label(board_col, text="Click a piece to begin", font=(FONT_FAMILY, 10),
                                     bg=t["bg"], fg=t["text_muted"])
        self.caption_lbl.pack(fill="x", pady=(10, 0))

        # ---- Sidebar ----
        side = tk.Frame(content, bg=t["bg"], width=260)
        side.pack(side="left", fill="y", padx=(24, 0))
        side.pack_propagate(False)
        self.side = side

        self.black_section = Section(side, t, pad=14)
        self.black_section.pack(fill="x", pady=(0, 12))
        self._sections.append(self.black_section)
        self._build_player_row(self.black_section.body, BLACK)

        self.moves_section = Section(side, t, pad=0, height=260)
        self.moves_section.pack(fill="x", pady=(0, 12))
        self.moves_section.pack_propagate(False)
        self._sections.append(self.moves_section)
        mh = tk.Frame(self.moves_section.body, bg=t["surface"], padx=16, pady=12)
        mh.pack(fill="x")
        self.moves_header = mh
        self.moves_header_lbl = tk.Label(mh, text="MOVE LIST", font=(FONT_FAMILY, 9, "bold"),
                                          bg=t["surface"], fg=t["text_muted"])
        self.moves_header_lbl.pack(side="left")
        self.moves_header_div = tk.Frame(self.moves_section.body, bg=t["border"], height=1)
        self.moves_header_div.pack(fill="x")

        ml_wrap = tk.Frame(self.moves_section.body, bg=t["surface"], padx=12, pady=12)
        ml_wrap.pack(fill="both", expand=True)
        self.ml_wrap = ml_wrap
        scrollbar = tk.Scrollbar(ml_wrap)
        scrollbar.pack(side="right", fill="y")
        self.movelist = tk.Listbox(ml_wrap, yscrollcommand=scrollbar.set, font=("Consolas", 11),
                                    bg=t["surface2"], fg=t["text"], bd=0, highlightthickness=0,
                                    selectbackground=t["accent"], selectforeground=t["accent_text"],
                                    activestyle="none")
        self.movelist.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=self.movelist.yview)

        self.white_section = Section(side, t, pad=14)
        self.white_section.pack(fill="x")
        self._sections.append(self.white_section)
        self._build_player_row(self.white_section.body, WHITE)

        self._apply_theme_colors()

    def _build_player_row(self, parent, color):
        t = self.theme
        row = tk.Frame(parent, bg=t["surface"])
        row.pack(fill="x")

        avatar_bg = "#202020" if color == BLACK else "#fafafa"
        avatar_fg = "#fafafa" if color == BLACK else "#202020"
        avatar = tk.Label(row, text=PIECE_UNICODE[color + "K"], font=(FONT_FAMILY, 19), bg=avatar_bg,
                           fg=avatar_fg, width=2, height=1, highlightbackground=t["border"], highlightthickness=1)
        avatar.pack(side="left", padx=(0, 12))

        info = tk.Frame(row, bg=t["surface"])
        info.pack(side="left", fill="x", expand=True)
        name_lbl = tk.Label(info, text="Black" if color == BLACK else "White", font=(FONT_FAMILY, 11, "bold"),
                             bg=t["surface"], fg=t["text"])
        name_lbl.pack(anchor="w")
        captured_lbl = tk.Label(info, text="", font=(FONT_FAMILY, 11), bg=t["surface"], fg=t["text_muted"])
        captured_lbl.pack(anchor="w")

        clock_wrap = tk.Frame(row, bg=t["surface2"], padx=14, pady=6)
        clock_wrap.pack(side="right")
        clock_lbl = tk.Label(clock_wrap, text="05:00", font=("Consolas", 21, "bold"), bg=t["surface2"], fg=t["text"])
        clock_lbl.pack()

        if color == WHITE:
            self.white_row, self.white_name_lbl, self.white_captured_lbl = row, name_lbl, captured_lbl
            self.white_clock_wrap, self.white_clock_lbl, self.white_avatar = clock_wrap, clock_lbl, avatar
        else:
            self.black_row, self.black_name_lbl, self.black_captured_lbl = row, name_lbl, captured_lbl
            self.black_clock_wrap, self.black_clock_lbl, self.black_avatar = clock_wrap, clock_lbl, avatar

    def _apply_theme_colors(self):
        t = self.theme
        self.root.configure(bg=t["bg"])
        self.appbar.configure(bg=t["surface"])
        self.appbar_inner.configure(bg=t["surface"])
        self.brand.configure(bg=t["surface"])
        self.logo_lbl.configure(bg=t["surface"], fg=t["accent"])
        self.title_lbl.configure(bg=t["surface"], fg=t["text"])
        self.actions.configure(bg=t["surface"])
        self.appbar_divider.configure(bg=t["border"])
        self.settings_panel.configure(bg=t["bg"])

        self.status_wrap.configure(bg=t["bg"])
        self.status_inner.configure(bg=t["surface2"])
        self.status_pad.configure(bg=t["surface2"])
        self.status_accent.configure(bg=t["accent"])
        self.status_lbl.configure(bg=t["surface2"], fg=t["text"])

        self.body.configure(bg=t["bg"])
        self.content.configure(bg=t["bg"])
        self.board_col.configure(bg=t["bg"])
        self.board_frame.configure(bg=t["border"])
        self.caption_lbl.configure(bg=t["bg"], fg=t["text_muted"])
        self.side.configure(bg=t["bg"])

        for btn in self._buttons:
            btn.retheme(t)

        for sec in self._sections:
            sec.configure(bg=t["border"])
            sec.body.configure(bg=t["surface"])

        self.moves_header.configure(bg=t["surface"])
        self.moves_header_lbl.configure(bg=t["surface"], fg=t["text_muted"])
        self.moves_header_div.configure(bg=t["border"])
        self.ml_wrap.configure(bg=t["surface"])
        self.movelist.configure(bg=t["surface2"], fg=t["text"], selectbackground=t["accent"],
                                 selectforeground=t["accent_text"])

        for row, name_lbl, cap_lbl, clock_wrap, clock_lbl, avatar in (
            (self.white_row, self.white_name_lbl, self.white_captured_lbl, self.white_clock_wrap, self.white_clock_lbl, self.white_avatar),
            (self.black_row, self.black_name_lbl, self.black_captured_lbl, self.black_clock_wrap, self.black_clock_lbl, self.black_avatar),
        ):
            row.configure(bg=t["surface"])
            row.winfo_children()[1].configure(bg=t["surface"])
            name_lbl.configure(bg=t["surface"], fg=t["text"])
            cap_lbl.configure(bg=t["surface"], fg=t["text_muted"])
            clock_wrap.configure(bg=t["surface2"])
            clock_lbl.configure(bg=t["surface2"], fg=t["text"])
            avatar.configure(highlightbackground=t["border"])

        if self.settings_visible:
            self._populate_settings_panel(self.settings_focus)

    # ---------------- Drawing ----------------

    def board_to_screen(self, r, c):
        if self.flipped:
            r, c = 7 - r, 7 - c
        return c * SQUARE, r * SQUARE

    def screen_to_board(self, x, y):
        c, r = x // SQUARE, y // SQUARE
        if self.flipped:
            r, c = 7 - r, 7 - c
        return int(r), int(c)

    def _draw_board(self):
        t = self.theme
        self.canvas.delete("all")
        self.canvas.configure(bg=t["board_dark"])
        check_sq = None
        if self.board.in_check(self.board.turn):
            check_sq = self.board.king_pos(self.board.turn)

        for r in range(8):
            for c in range(8):
                x, y = self.board_to_screen(r, c)
                color = t["board_light"] if (r + c) % 2 == 0 else t["board_dark"]
                self.canvas.create_rectangle(x, y, x + SQUARE, y + SQUARE, fill=color, outline="")

                if self.last_move and ((r, c) == (self.last_move.fr, self.last_move.fc) or (r, c) == (self.last_move.tr, self.last_move.tc)):
                    overlay = mix(color, t["select"], 0.55)
                    self.canvas.create_rectangle(x, y, x + SQUARE, y + SQUARE, fill=overlay, outline="")

                if self.selected == (r, c):
                    self.canvas.create_rectangle(x, y, x + SQUARE, y + SQUARE, fill=t["select"], outline="", stipple="gray50")

                if check_sq == (r, c):
                    self.canvas.create_oval(x + 3, y + 3, x + SQUARE - 3, y + SQUARE - 3, fill=t["check"], outline="", stipple="gray25")

                piece = self.board.grid[r][c]
                if piece:
                    is_white_piece = piece[0] == "w"
                    fill = "#fbfbfb" if is_white_piece else "#0a0a0a"
                    outline = "#0a0a0a" if is_white_piece else "#fbfbfb"
                    px, py = x + SQUARE / 2, y + SQUARE / 2
                    fsize = int(SQUARE * 0.62)
                    for ox, oy in ((-1.4, -1.4), (1.4, -1.4), (-1.4, 1.4), (1.4, 1.4), (0, -1.6), (0, 1.6), (-1.6, 0), (1.6, 0)):
                        self.canvas.create_text(px + ox, py + oy, text=PIECE_UNICODE[piece],
                                                 font=("DejaVu Sans", fsize), fill=outline)
                    self.canvas.create_text(px, py, text=PIECE_UNICODE[piece],
                                             font=("DejaVu Sans", fsize), fill=fill)

                if (r, c) in self.legal_targets:
                    cx, cy = x + SQUARE / 2, y + SQUARE / 2
                    if self.board.grid[r][c] is not None:
                        self.canvas.create_oval(x + 4, y + 4, x + SQUARE - 4, y + SQUARE - 4, outline=t["legal"], width=4)
                    else:
                        rad = SQUARE * 0.13
                        self.canvas.create_oval(cx - rad, cy - rad, cx + rad, cy + rad, fill=t["legal"], outline="")

        for i in range(8):
            r_label = str(8 - i) if not self.flipped else str(i + 1)
            sq_color = t["board_light"] if i % 2 == 0 else t["board_dark"]
            label_fg = t["board_dark"] if is_light(sq_color) else t["board_light"]
            self.canvas.create_text(6, i * SQUARE + 9, text=r_label, anchor="w",
                                     font=(FONT_FAMILY, 8, "bold"), fill=label_fg)
            f_label = FILES[i] if not self.flipped else FILES[7 - i]
            sq_color2 = t["board_light"] if (i + 7) % 2 == 0 else t["board_dark"]
            label_fg2 = t["board_dark"] if is_light(sq_color2) else t["board_light"]
            self.canvas.create_text(i * SQUARE + SQUARE - 7, BOARD_PX - 9, text=f_label, anchor="e",
                                     font=(FONT_FAMILY, 8, "bold"), fill=label_fg2)

    # ---------------- Interaction ----------------

    def on_click(self, event):
        if self.game_over:
            return
        if self.ai_thinking:
            return
        if self.mode == "ai" and self.board.turn == self.ai_color:
            return
        if self.mode == "online" and self.board.turn != self.online_color:
            return
        r, c = self.screen_to_board(event.x, event.y)
        if not self.board.in_bounds(r, c):
            return

        if self.selected is None:
            piece = self.board.grid[r][c]
            if piece and piece[0] == self.board.turn:
                self.selected = (r, c)
                moves = self.board.legal_moves_from(r, c)
                self.legal_targets = {(m.tr, m.tc): m for m in moves}
        else:
            if (r, c) in self.legal_targets:
                mv = self.legal_targets[(r, c)]
                if mv.promo:
                    choice = self.ask_promotion()
                    matches = [m for m in self.legal_targets.values()
                               if m.fr == mv.fr and m.fc == mv.fc and m.tr == mv.tr and m.tc == mv.tc and m.promo == choice]
                    mv = matches[0] if matches else mv
                self.do_move(mv)
                self.selected = None
                self.legal_targets = {}
            else:
                piece = self.board.grid[r][c]
                if piece and piece[0] == self.board.turn:
                    self.selected = (r, c)
                    moves = self.board.legal_moves_from(r, c)
                    self.legal_targets = {(m.tr, m.tc): m for m in moves}
                else:
                    self.selected = None
                    self.legal_targets = {}
        self._draw_board()

    def ask_promotion(self):
        t = self.theme
        top = self._styled_toplevel("Promote Pawn")
        pad = tk.Frame(top, bg=t["surface"], padx=20, pady=18)
        pad.pack()
        tk.Label(pad, text="Choose a piece", font=(FONT_FAMILY, 12, "bold"), bg=t["surface"],
                 fg=t["text"]).pack(pady=(0, 12))
        row = tk.Frame(pad, bg=t["surface"])
        row.pack()

        result = {}

        def pick(p):
            result["p"] = p
            top.destroy()

        side_for_glyph = self.board.turn
        for p, label in [("Q", "Queen"), ("R", "Rook"), ("B", "Bishop"), ("N", "Knight")]:
            cell = tk.Frame(row, bg=t["surface2"], padx=12, pady=10, cursor="hand2",
                             highlightbackground=t["border"], highlightthickness=1)
            cell.pack(side="left", padx=4)
            glyph = tk.Label(cell, text=PIECE_UNICODE[side_for_glyph + p], font=("DejaVu Sans", 28),
                              bg=t["surface2"], fg=t["text"])
            glyph.pack()
            txt = tk.Label(cell, text=label, font=(FONT_FAMILY, 9), bg=t["surface2"], fg=t["text_muted"])
            txt.pack()
            for w in (cell, glyph, txt):
                w.bind("<Button-1>", lambda e, p=p: pick(p))

        top.wait_window()
        return result.get("p", "Q")

    def do_move(self, mv):
        mover_color = self.board.turn
        self.board.make_move(mv)
        self.last_move = mv
        self._log_move(mv)
        self._update_captured()

        self.clock[mover_color] += self.increment

        if not self.clock_running:
            self.clock_running = True
            self.last_tick = time.time()

        status = self.board.game_status()
        if status != "playing":
            self.end_game(status)

        self._update_status()
        self._update_clock_labels()
        self.caption_lbl.config(text=f"Last move: {mv.uci()}")

        # Online: tell the opponent about this move (only if it was *our* move).
        if self.mode == "online" and mover_color == self.online_color and self.online_bucket:
            self._online_push_move(mv)

        # vs AI: if it's now the computer's turn, let it think and reply.
        if self.mode == "ai" and not self.game_over and self.board.turn == self.ai_color:
            self._trigger_ai_move()

    def _trigger_ai_move(self):
        self.ai_thinking = True
        self.caption_lbl.config(text="Computer is thinking\u2026")
        board_copy = self.board.clone()
        difficulty = self.ai_difficulty

        def worker():
            mv = ai_pick_move(board_copy, difficulty)
            self.root.after(0, lambda: self._apply_ai_move(mv))

        threading.Thread(target=worker, daemon=True).start()

    def _apply_ai_move(self, mv):
        self.ai_thinking = False
        if self.game_over or mv is None or self.mode != "ai":
            return
        self.selected = None
        self.legal_targets = {}
        self.do_move(mv)
        self._draw_board()

    # ---------------- Online play ----------------

    def _online_push_move(self, mv):
        bucket = self.online_bucket

        def worker():
            try:
                relay_set(bucket, {"moves": [m.uci() for m in self.board.history]})
            except Exception:
                pass  # best-effort; the poll loop will resync if needed

        threading.Thread(target=worker, daemon=True).start()

    def start_online_host(self):
        self.caption_lbl.config(text="Creating online game\u2026")
        self.root.update_idletasks()

        def worker():
            try:
                bucket = relay_create({"moves": []})
            except Exception as e:
                self.root.after(0, lambda: self._online_error(str(e)))
                return
            self.root.after(0, lambda: self._online_host_ready(bucket))

        threading.Thread(target=worker, daemon=True).start()

    def _online_host_ready(self, bucket):
        self.mode = "online"
        self.online_bucket = bucket
        self.online_role = "host"
        self.online_color = WHITE
        self.online_applied = 0
        self.start_new_game()
        self._close_settings_panel()
        self._show_game_code_dialog(bucket)
        self._start_online_poll()

    def start_online_join(self, code):
        code = code.strip()
        if not code:
            messagebox.showerror("Missing code", "Paste the game code/link your friend sent you.")
            return
        # Allow pasting either the bare code or a full shareable link.
        if "/" in code:
            code = code.rstrip("/").split("/")[-1]
        self.caption_lbl.config(text="Connecting\u2026")
        self.root.update_idletasks()

        def worker():
            try:
                blob = relay_get(code)
            except Exception as e:
                self.root.after(0, lambda: self._online_error(str(e)))
                return
            moves = blob.get("moves") if blob else None
            if moves is None:
                self.root.after(0, lambda: self._online_error("Game code not found. Check it and try again."))
                return
            self.root.after(0, lambda: self._online_join_ready(code))

        threading.Thread(target=worker, daemon=True).start()

    def _online_join_ready(self, bucket):
        self.mode = "online"
        self.online_bucket = bucket
        self.online_role = "guest"
        self.online_color = BLACK
        self.online_applied = 0
        self.start_new_game()
        self._close_settings_panel()
        self.caption_lbl.config(text="Connected! You are playing Black.")
        self._start_online_poll()

    def _online_error(self, msg):
        self.caption_lbl.config(text="Connection failed")
        messagebox.showerror("Online game", f"Couldn't connect: {msg}\n\n"
                              "Check your internet connection and try again.")

    def _show_game_code_dialog(self, bucket):
        t = self.theme
        top = self._styled_toplevel("Invite a friend")
        pad = tk.Frame(top, bg=t["surface"], padx=24, pady=20)
        pad.pack()
        tk.Label(pad, text="Send this code to your opponent", font=(FONT_FAMILY, 12, "bold"),
                 bg=t["surface"], fg=t["text"]).pack(anchor="w")
        tk.Label(pad, text="They paste it into \u201cJoin online game\u201d to connect from any device.",
                 font=(FONT_FAMILY, 9), bg=t["surface"], fg=t["text_muted"], wraplength=360,
                 justify="left").pack(anchor="w", pady=(2, 14))

        code_var = tk.StringVar(value=bucket)
        entry = tk.Entry(pad, textvariable=code_var, font=("Consolas", 14, "bold"), width=28,
                          bg=t["surface2"], fg=t["text"], insertbackground=t["text"], relief="flat",
                          justify="center", state="readonly", readonlybackground=t["surface2"])
        entry.pack(fill="x", ipady=8)

        def copy_code():
            self.root.clipboard_clear()
            self.root.clipboard_append(bucket)
            copy_btn.config(text="Copied!")
            self.root.after(1200, lambda: copy_btn.config(text="Copy code"))

        copy_btn = Chip(pad, t, "Copy code", copy_code, width=160, height=32)
        copy_btn.pack(pady=(12, 0))
        tk.Label(pad, text="You are playing White. Waiting for your opponent\u2019s first move\u2026",
                 font=(FONT_FAMILY, 9), bg=t["surface"], fg=t["text_muted"]).pack(pady=(14, 0))
        Chip(pad, t, "Done", top.destroy, width=80, height=30).pack(pady=(14, 0))

    def _start_online_poll(self):
        self.online_running = True
        self._online_poll_tick()

    def _stop_online_poll(self):
        self.online_running = False

    def _online_poll_tick(self):
        if not self.online_running or self.mode != "online":
            return
        bucket = self.online_bucket

        def worker():
            try:
                blob = relay_get(bucket)
                moves = blob.get("moves") if blob else None
            except Exception:
                moves = None
            self.root.after(0, lambda: self._online_poll_result(moves))

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(1500, self._online_poll_tick)

    def _online_poll_result(self, moves):
        if not self.online_running or self.mode != "online" or moves is None:
            return
        local_n = len(self.board.history)
        if len(moves) > local_n:
            # Apply each new move (in case more than one arrived since last poll).
            for uci in moves[local_n:]:
                mv = self._find_move_by_uci(uci)
                if mv is None:
                    break  # out of sync; will retry next poll
                self.selected = None
                self.legal_targets = {}
                self.do_move(mv)
            self._draw_board()

    def _find_move_by_uci(self, uci):
        for r in range(8):
            for c in range(8):
                piece = self.board.grid[r][c]
                if not piece or piece[0] != self.board.turn:
                    continue
                for mv in self.board.legal_moves_from(r, c):
                    if mv.uci() == uci:
                        return mv
        return None

    def _update_captured(self):
        present = {"P": 0, "N": 0, "B": 0, "R": 0, "Q": 0}
        counts = {WHITE: dict(present), BLACK: dict(present)}
        for row in self.board.grid:
            for p in row:
                if p and p[1] != "K":
                    counts[p[0]][p[1]] += 1
        start = {"P": 8, "N": 2, "B": 2, "R": 2, "Q": 1}
        captured_by_white, captured_by_black = [], []
        score_diff = 0
        for kind in ("Q", "R", "B", "N", "P"):
            missing_black = start[kind] - counts[BLACK][kind]
            missing_white = start[kind] - counts[WHITE][kind]
            captured_by_white += [PIECE_UNICODE["b" + kind]] * missing_black
            captured_by_black += [PIECE_UNICODE["w" + kind]] * missing_white
            score_diff += missing_black * PIECE_VALUE[kind]
            score_diff -= missing_white * PIECE_VALUE[kind]

        w_text = " ".join(captured_by_white)
        b_text = " ".join(captured_by_black)
        if score_diff > 0:
            w_text += f"  +{score_diff}"
        elif score_diff < 0:
            b_text += f"  +{-score_diff}"
        self.white_captured_lbl.config(text=w_text)
        self.black_captured_lbl.config(text=b_text)

    def _log_move(self, mv):
        n = len(self.board.history)
        text = mv.uci()
        if n % 2 == 1:
            self.movelist.insert("end", f"{(n + 1)//2:>3}.  {text}")
        else:
            last_idx = self.movelist.size() - 1
            if last_idx >= 0:
                cur = self.movelist.get(last_idx)
                self.movelist.delete(last_idx)
                self.movelist.insert("end", f"{cur}    {text}")
            else:
                self.movelist.insert("end", text)
        self.movelist.see("end")

    def undo_move(self):
        if not self.board.history or self.game_over:
            return
        if self.mode != "local":
            messagebox.showinfo("Undo unavailable", "Undo is only available in local 2-player games.")
            return
        moves = self.board.history[:-1]
        self.board = Board()
        for mv in moves:
            self.board.make_move(mv)
        self.last_move = moves[-1] if moves else None
        self.selected = None
        self.legal_targets = {}
        self.movelist.delete(0, "end")
        for i in range(0, len(moves), 2):
            w = moves[i].uci()
            b = moves[i + 1].uci() if i + 1 < len(moves) else ""
            self.movelist.insert("end", f"{i//2 + 1:>3}.  {w}" + (f"    {b}" if b else ""))
        self.game_over = False
        self._update_status()
        self._update_captured()
        self.caption_lbl.config(text="Move undone")
        self._draw_board()

    def flip_board(self):
        self.flipped = not self.flipped
        self._draw_board()

    def _update_status(self):
        if self.game_over:
            return
        status = self.board.game_status()
        turn_name = "White" if self.board.turn == WHITE else "Black"
        if status in ("checkmate", "stalemate", "draw50", "insufficient"):
            self.end_game(status)
        else:
            in_check = self.board.in_check(self.board.turn)
            check_txt = "  \u2022  Check!" if in_check else ""
            self.status_lbl.config(text=f"{turn_name} to move{check_txt}")
            t = self.theme
            bg = mix(t["surface2"], t["check"], 0.25) if in_check else t["surface2"]
            self.status_inner.configure(bg=bg)
            self.status_pad.configure(bg=bg)
            self.status_lbl.configure(bg=bg)

    def end_game(self, status):
        self.game_over = True
        self.clock_running = False
        t = self.theme
        if status == "checkmate":
            winner = "Black" if self.board.turn == WHITE else "White"
            msg = f"Checkmate \u2014 {winner} wins!"
        elif status == "stalemate":
            msg = "Stalemate \u2014 the game is a draw."
        elif status == "draw50":
            msg = "Draw \u2014 fifty-move rule."
        elif status == "insufficient":
            msg = "Draw \u2014 insufficient material."
        elif status == "flag_white":
            msg = "Time's up \u2014 Black wins!"
        elif status == "flag_black":
            msg = "Time's up \u2014 White wins!"
        else:
            msg = status
        self.status_lbl.config(text=msg)
        bg = mix(t["surface2"], t["accent"], 0.3)
        self.status_inner.configure(bg=bg)
        self.status_pad.configure(bg=bg)
        self.status_lbl.configure(bg=bg)
        self.caption_lbl.config(text=msg)
        messagebox.showinfo("Game Over", msg)

    # ---------------- Timer ----------------

    def _tick(self):
        if self.clock_running and not self.game_over:
            now = time.time()
            elapsed = now - self.last_tick
            self.last_tick = now
            self.clock[self.board.turn] -= elapsed
            if self.clock[self.board.turn] <= 0:
                self.clock[self.board.turn] = 0
                self.end_game("flag_white" if self.board.turn == WHITE else "flag_black")
            self._update_clock_labels()
        self.root.after(200, self._tick)

    def _update_clock_labels(self):
        t = self.theme

        def fmt(tt):
            tt = max(0, tt)
            m, s = divmod(int(tt), 60)
            return f"{m:02d}:{s:02d}"

        self.white_clock_lbl.config(text=fmt(self.clock[WHITE]))
        self.black_clock_lbl.config(text=fmt(self.clock[BLACK]))

        low_color = "#e05a5a"
        for color, wrap, lbl in ((WHITE, self.white_clock_wrap, self.white_clock_lbl),
                                  (BLACK, self.black_clock_wrap, self.black_clock_lbl)):
            is_active = self.board.turn == color and self.clock_running and not self.game_over
            low_time = self.clock[color] < 20
            if is_active:
                wrap.configure(bg=t["accent"])
                lbl.configure(bg=t["accent"], fg=low_color if low_time else t["accent_text"])
            else:
                wrap.configure(bg=t["surface2"])
                lbl.configure(bg=t["surface2"], fg=low_color if low_time else t["text"])

    # ---------------- Dialogs ----------------

    def _styled_toplevel(self, title):
        t = self.theme
        top = tk.Toplevel(self.root)
        top.title(title)
        top.configure(bg=t["surface"])
        top.resizable(False, False)
        top.grab_set()
        return top

    def toggle_settings_panel(self, focus="new"):
        if self.settings_visible and self.settings_focus == focus:
            self._close_settings_panel()
        else:
            self.settings_visible = True
            self.settings_focus = focus
            self._populate_settings_panel(focus)
            self.settings_panel.pack(side="top", fill="x", padx=24, pady=(16, 0), before=self.body)

    def _close_settings_panel(self):
        self.settings_visible = False
        self.settings_panel.pack_forget()
        self.root.after_idle(self._clear_settings_panel)

    def _clear_settings_panel(self):
        for w in list(self.settings_panel.winfo_children()):
            w.destroy()

    def _populate_settings_panel(self, focus="new"):
        for w in self.settings_panel.winfo_children():
            w.destroy()
        t = self.theme

        outer = Section(self.settings_panel, t, pad=0)
        outer.pack(fill="x", pady=(16, 0))
        body = outer.body

        title = "New Game" if focus == "new" else "Theme & Colors"
        header = tk.Frame(body, bg=t["surface"], padx=20, pady=14)
        header.pack(fill="x")
        tk.Label(header, text=title, font=(FONT_FAMILY, 13, "bold"),
                 bg=t["surface"], fg=t["text"]).pack(side="left")
        RoundedButton(header, t, icon="\u2715", command=self._close_settings_panel, variant="secondary",
                      width=34, height=34, tooltip="Close").pack(side="right")

        div = tk.Frame(body, bg=t["border"], height=1)
        div.pack(fill="x")

        content = tk.Frame(body, bg=t["surface"], padx=20, pady=18)
        content.pack(fill="x")

        if focus == "new":
            self._build_new_game_section(content, t)
        else:
            self._build_theme_section(content, t)

    def _build_new_game_section(self, left, t):
        mode_var = tk.StringVar(value=self.mode if self.mode in ("local", "ai") else "local")
        diff_var = tk.StringVar(value=self.ai_difficulty)

        tk.Label(left, text="Play against", font=(FONT_FAMILY, 10), bg=t["surface"],
                 fg=t["text_muted"]).grid(row=0, column=0, sticky="w", pady=(0, 8))
        mode_row = tk.Frame(left, bg=t["surface"])
        mode_row.grid(row=1, column=0, columnspan=2, sticky="w", pady=(0, 16))

        body = tk.Frame(left, bg=t["surface"])
        body.grid(row=2, column=0, columnspan=2, sticky="ew")

        def set_mode(m):
            mode_var.set(m)
            render_mode_chips()
            render_body()

        mode_chips = {}

        def render_mode_chips():
            for w in mode_row.winfo_children():
                w.destroy()
            for label, key in [("Local 2-player", "local"), ("vs Computer", "ai"), ("Online", "online")]:
                chip = Chip(mode_row, t, label, lambda k=key: set_mode(k), width=124, height=30,
                            selected=(mode_var.get() == key))
                chip.pack(side="left", padx=(0, 6))
                mode_chips[key] = chip

        # ---- Local / vs-computer shared time control ----
        def build_time_and_start(parent):
            tk.Label(parent, text="Minutes per side", font=(FONT_FAMILY, 10), bg=t["surface"],
                      fg=t["text_muted"]).grid(row=0, column=0, sticky="w", pady=6)
            minutes_var = tk.StringVar(value=str(round(self.base_time / 60, 1)).rstrip("0").rstrip("."))
            tk.Entry(parent, textvariable=minutes_var, width=10, font=(FONT_FAMILY, 11),
                      bg=t["surface2"], fg=t["text"], insertbackground=t["text"],
                      relief="flat").grid(row=0, column=1, padx=(16, 0), pady=6, ipady=5)

            tk.Label(parent, text="Increment (sec)", font=(FONT_FAMILY, 10), bg=t["surface"],
                      fg=t["text_muted"]).grid(row=1, column=0, sticky="w", pady=6)
            inc_var = tk.StringVar(value=str(self.increment))
            tk.Entry(parent, textvariable=inc_var, width=10, font=(FONT_FAMILY, 11),
                      bg=t["surface2"], fg=t["text"], insertbackground=t["text"],
                      relief="flat").grid(row=1, column=1, padx=(16, 0), pady=6, ipady=5)

            tk.Label(parent, text="Quick presets", font=(FONT_FAMILY, 10), bg=t["surface"],
                      fg=t["text_muted"]).grid(row=2, column=0, columnspan=2, sticky="w", pady=(16, 8))
            presets = tk.Frame(parent, bg=t["surface"])
            presets.grid(row=3, column=0, columnspan=2, sticky="w")
            for label, mins, inc in [("1+0", 1, 0), ("3+2", 3, 2), ("5+0", 5, 0), ("10+5", 10, 5), ("30+0", 30, 0)]:
                Chip(presets, t, label, lambda m=mins, i=inc: (minutes_var.set(str(m)), inc_var.set(str(i))),
                     width=58, height=28).pack(side="left", padx=3)
            return minutes_var, inc_var

        def render_body():
            for w in body.winfo_children():
                w.destroy()
            m = mode_var.get()

            if m in ("local", "ai"):
                if m == "ai":
                    tk.Label(body, text="Difficulty", font=(FONT_FAMILY, 10), bg=t["surface"],
                              fg=t["text_muted"]).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 8))
                    diff_row = tk.Frame(body, bg=t["surface"])
                    diff_row.grid(row=1, column=0, columnspan=2, sticky="w", pady=(0, 16))
                    diff_chips = {}

                    def set_diff(d):
                        diff_var.set(d)
                        for key, chip in diff_chips.items():
                            chip.set_selected(key == d)

                    for d in ("Easy", "Medium", "Hard"):
                        chip = Chip(diff_row, t, d, lambda d=d: set_diff(d), width=80, height=30,
                                    selected=(diff_var.get() == d))
                        chip.pack(side="left", padx=(0, 6))
                        diff_chips[d] = chip
                    time_parent = tk.Frame(body, bg=t["surface"])
                    time_parent.grid(row=2, column=0, columnspan=2, sticky="ew")
                else:
                    time_parent = tk.Frame(body, bg=t["surface"])
                    time_parent.grid(row=0, column=0, columnspan=2, sticky="ew")

                minutes_var, inc_var = build_time_and_start(time_parent)

                def start():
                    try:
                        mins = max(0.1, float(minutes_var.get()))
                        inc = max(0, float(inc_var.get()))
                    except ValueError:
                        messagebox.showerror("Invalid input", "Please enter numbers for time control.")
                        return
                    self.base_time = mins * 60
                    self.increment = inc
                    self._stop_online_poll()
                    self.online_bucket = None
                    self.mode = mode_var.get()
                    self.ai_difficulty = diff_var.get()
                    self.start_new_game()
                    self._close_settings_panel()

                RoundedButton(body, t, text="Start Game", icon="\u25B6", command=start, variant="primary",
                              width=150, height=42).grid(row=3, column=0, columnspan=2, pady=(20, 0), sticky="w")

            else:  # online
                tk.Label(body, text="Host a game and share the code, or join one a friend sent you.",
                          font=(FONT_FAMILY, 9), bg=t["surface"], fg=t["text_muted"], wraplength=380,
                          justify="left").grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 14))

                RoundedButton(body, t, text="Host New Online Game", icon="\u2606", command=self.start_online_host,
                              variant="primary", width=230, height=42).grid(row=1, column=0, columnspan=2,
                                                                             sticky="w", pady=(0, 18))

                tk.Label(body, text="Join with a code", font=(FONT_FAMILY, 10), bg=t["surface"],
                          fg=t["text_muted"]).grid(row=2, column=0, columnspan=2, sticky="w", pady=(0, 6))
                join_row = tk.Frame(body, bg=t["surface"])
                join_row.grid(row=3, column=0, columnspan=2, sticky="w")
                code_var = tk.StringVar()
                tk.Entry(join_row, textvariable=code_var, width=22, font=("Consolas", 11),
                          bg=t["surface2"], fg=t["text"], insertbackground=t["text"],
                          relief="flat").pack(side="left", ipady=6)
                RoundedButton(join_row, t, text="Join", command=lambda: self.start_online_join(code_var.get()),
                              variant="secondary", width=72, height=36).pack(side="left", padx=(8, 0))

        render_mode_chips()
        render_body()

    def _build_theme_section(self, right, t):
        def apply_preset(name):
            self.theme_name = name
            self.theme = dict(THEMES[name])
            self._apply_theme_colors()
            self._draw_board()

        col = 0
        for name, th in THEMES.items():
            cell = tk.Frame(right, bg=t["surface2"] if name != self.theme_name else t["accent"],
                             padx=10, pady=10, cursor="hand2")
            cell.grid(row=0, column=col, padx=4, sticky="n")
            swatch = tk.Frame(cell, bg=cell["bg"])
            swatch.pack()
            for key in ("board_light", "board_dark", "accent"):
                tk.Frame(swatch, bg=th[key], width=18, height=18).pack(side="left", padx=1)
            fg = t["accent_text"] if name == self.theme_name else t["text"]
            lbl = tk.Label(cell, text=name, font=(FONT_FAMILY, 9, "bold"), bg=cell["bg"], fg=fg)
            lbl.pack(pady=(6, 0))
            for w in (cell, swatch, lbl):
                w.bind("<Button-1>", lambda e, n=name: apply_preset(n))
            col += 1

        sep = tk.Frame(right, bg=t["border"], height=1)
        sep.grid(row=1, column=0, columnspan=5, sticky="ew", pady=18)

        tk.Label(right, text="Fine-tune Colors", font=(FONT_FAMILY, 11, "bold"),
                  bg=t["surface"], fg=t["text"]).grid(row=2, column=0, columnspan=5, sticky="w")

        def pick_color(key):
            color = colorchooser.askcolor(color=self.theme[key], title=f"Pick {key} color")
            if color and color[1]:
                self.theme[key] = color[1]
                self._apply_theme_colors()
                self._draw_board()

        keys = [("board_light", "Light squares"), ("board_dark", "Dark squares"), ("accent", "Accent color"),
                ("check", "Check indicator"), ("bg", "Window background")]
        for i, (key, label) in enumerate(keys):
            line = tk.Frame(right, bg=t["surface"])
            line.grid(row=3 + i, column=0, columnspan=5, sticky="ew", pady=4)
            tk.Frame(line, bg=self.theme[key], width=22, height=22, highlightbackground=t["border"],
                     highlightthickness=1).pack(side="left")
            tk.Label(line, text=label, font=(FONT_FAMILY, 10), bg=t["surface"],
                      fg=t["text"], width=16, anchor="w").pack(side="left", padx=10)
            Chip(line, t, "Change", lambda k=key: pick_color(k), width=84, height=28).pack(side="left")

    def start_new_game(self):
        self.board = Board()
        self.selected = None
        self.legal_targets = {}
        self.last_move = None
        self.game_over = False
        self.ai_thinking = False
        self.clock = {WHITE: self.base_time, BLACK: self.base_time}
        self.clock_running = False
        self.last_tick = None
        self.movelist.delete(0, "end")
        self.caption_lbl.config(text="New game \u2014 White moves first")
        self._update_status()
        self._update_clock_labels()
        self._update_captured()
        self._draw_board()


def main():
    root = tk.Tk()
    try:
        root.tk.call("tk", "scaling", 1.2)
    except tk.TclError:
        pass
    app = ChessApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
