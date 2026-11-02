import os
import queue
import random
import threading
import time
import tkinter as tk
from tkinter import messagebox, simpledialog

import chess
from PIL import Image, ImageTk

SQUARE_SIZE = 64
PIECE_PATH = os.path.join(os.path.dirname(__file__), "pieces")
THINK_TIME = 2.0  # seconds per bot move; raise for a stronger bot

piece_images = {}
fallen_king_image = {}

# Book keyed by the UCI moves played so far
opening_book = {
    (): ["e2e4", "d2d4", "g1f3", "c2c4"],
    ("e2e4",): ["c7c5", "e7e5"],
    ("d2d4",): ["d7d5", "g8f6"],
    ("g1f3",): ["d7d5", "g8f6"],
    ("c2c4",): ["e7e5", "g8f6"],
}

# --------------------------------------------------------------------------
# Evaluation: material + piece-square tables (precomputed per colour/piece)
# --------------------------------------------------------------------------
VALUES = {chess.PAWN: 100, chess.KNIGHT: 320, chess.BISHOP: 330,
          chess.ROOK: 500, chess.QUEEN: 900, chess.KING: 0}

# Tables are written from White's view, a8 first.
PST = {
    chess.PAWN: [
        0, 0, 0, 0, 0, 0, 0, 0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
        5, 5, 10, 25, 25, 10, 5, 5,
        0, 0, 0, 20, 20, 0, 0, 0,
        5, -5, -10, 0, 0, -10, -5, 5,
        5, 10, 10, -20, -20, 10, 10, 5,
        0, 0, 0, 0, 0, 0, 0, 0],
    chess.KNIGHT: [
        -50, -40, -30, -30, -30, -30, -40, -50,
        -40, -20, 0, 0, 0, 0, -20, -40,
        -30, 0, 10, 15, 15, 10, 0, -30,
        -30, 5, 15, 20, 20, 15, 5, -30,
        -30, 0, 15, 20, 20, 15, 0, -30,
        -30, 5, 10, 15, 15, 10, 5, -30,
        -40, -20, 0, 5, 5, 0, -20, -40,
        -50, -40, -30, -30, -30, -30, -40, -50],
    chess.BISHOP: [
        -20, -10, -10, -10, -10, -10, -10, -20,
        -10, 0, 0, 0, 0, 0, 0, -10,
        -10, 0, 5, 10, 10, 5, 0, -10,
        -10, 5, 5, 10, 10, 5, 5, -10,
        -10, 0, 10, 10, 10, 10, 0, -10,
        -10, 10, 10, 10, 10, 10, 10, -10,
        -10, 5, 0, 0, 0, 0, 5, -10,
        -20, -10, -10, -10, -10, -10, -10, -20],
    chess.ROOK: [
        0, 0, 0, 0, 0, 0, 0, 0,
        5, 10, 10, 10, 10, 10, 10, 5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        0, 0, 0, 5, 5, 0, 0, 0],
    chess.QUEEN: [
        -20, -10, -10, -5, -5, -10, -10, -20,
        -10, 0, 0, 0, 0, 0, 0, -10,
        -10, 0, 5, 5, 5, 5, 0, -10,
        -5, 0, 5, 5, 5, 5, 0, -5,
        0, 0, 5, 5, 5, 5, 0, -5,
        -10, 5, 5, 5, 5, 5, 0, -10,
        -10, 0, 5, 0, 0, 0, 0, -10,
        -20, -10, -10, -5, -5, -10, -10, -20],
    chess.KING: [
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -30, -40, -40, -50, -50, -40, -40, -30,
        -20, -30, -30, -40, -40, -30, -30, -20,
        -10, -20, -20, -20, -20, -20, -20, -10,
        20, 20, 0, 0, 0, 0, 20, 20,
        20, 30, 10, 0, 0, 10, 30, 20],
}

SCORE = {chess.WHITE: {}, chess.BLACK: {}}
for _pt, _table in PST.items():
    SCORE[chess.WHITE][_pt] = [VALUES[_pt] + _table[sq ^ 56] for sq in range(64)]
    SCORE[chess.BLACK][_pt] = [VALUES[_pt] + _table[sq] for sq in range(64)]


def evaluate(board):
    """Score from the side-to-move's point of view."""
    score = 0
    for sq, p in board.piece_map().items():
        v = SCORE[p.color][p.piece_type][sq]
        score += v if p.color == chess.WHITE else -v
    return score if board.turn == chess.WHITE else -score


# --------------------------------------------------------------------------
# Search: negamax + alpha-beta + iterative deepening + transposition table,
# move ordering (TT move, MVV-LVA, killers, history), null-move pruning,
# late-move reductions, check extensions, quiescence search.
# --------------------------------------------------------------------------
INF = 10 ** 9
MATE = 100_000
EXACT, LOWER, UPPER = 0, 1, 2


def to_tt(score, ply):
    if score > MATE - 1000:
        return score + ply
    if score < -MATE + 1000:
        return score - ply
    return score


def from_tt(score, ply):
    if score > MATE - 1000:
        return score - ply
    if score < -MATE + 1000:
        return score + ply
    return score


class Searcher:
    def __init__(self):
        self.tt = {}
        self.nodes = 0
        self.deadline = 0.0
        self.stop = False
        self.killers = [[None, None] for _ in range(128)]
        self.history = {}

    def _order(self, board, moves, tt_move, ply):
        killers = self.killers[ply]

        def key(m):
            if m == tt_move:
                return 1_000_000
            if board.is_capture(m):
                victim = board.piece_type_at(m.to_square) or chess.PAWN  # en passant
                attacker = board.piece_type_at(m.from_square)
                return 100_000 + 10 * victim - attacker
            if m.promotion:
                return 90_000 + m.promotion
            if m in killers:
                return 80_000
            return self.history.get((board.turn, m.from_square, m.to_square), 0)

        return sorted(moves, key=key, reverse=True)

    def quiesce(self, board, alpha, beta):
        self.nodes += 1
        stand = evaluate(board)
        if stand >= beta:
            return beta
        if stand > alpha:
            alpha = stand

        def key(m):
            victim = board.piece_type_at(m.to_square) or chess.PAWN
            return 10 * victim - board.piece_type_at(m.from_square)

        for move in sorted(board.generate_legal_captures(), key=key, reverse=True):
            board.push(move)
            score = -self.quiesce(board, -beta, -alpha)
            board.pop()
            if score >= beta:
                return beta
            if score > alpha:
                alpha = score
        return alpha

    def negamax(self, board, depth, alpha, beta, ply, allow_null=True):
        self.nodes += 1
        if self.nodes & 1023 == 0 and time.time() > self.deadline:
            self.stop = True
        if self.stop:
            return 0

        if ply > 0 and (board.halfmove_clock >= 100
                        or board.is_insufficient_material()
                        or board.is_repetition(2)):
            return 0
        if ply >= 100:
            return evaluate(board)

        in_check = board.is_check()
        if in_check:
            depth += 1  # check extension
        if depth <= 0:
            return self.quiesce(board, alpha, beta)

        orig_alpha = alpha
        key = board._transposition_key()
        tt_move = None
        entry = self.tt.get(key)
        if entry:
            e_depth, e_flag, e_score, tt_move = entry
            if ply > 0 and e_depth >= depth:
                e_score = from_tt(e_score, ply)
                if e_flag == EXACT:
                    return e_score
                if e_flag == LOWER:
                    alpha = max(alpha, e_score)
                else:
                    beta = min(beta, e_score)
                if alpha >= beta:
                    return e_score

        # Null-move pruning
        if (allow_null and not in_check and depth >= 3 and ply > 0
                and board.occupied_co[board.turn] & ~(board.pawns | board.kings)):
            board.push(chess.Move.null())
            score = -self.negamax(board, depth - 3, -beta, -beta + 1, ply + 1, False)
            board.pop()
            if self.stop:
                return 0
            if score >= beta:
                return beta

        moves = self._order(board, list(board.legal_moves), tt_move, ply)
        if not moves:
            return -MATE + ply if in_check else 0

        best = -INF
        best_move = None
        for i, move in enumerate(moves):
            is_cap = board.is_capture(move)
            board.push(move)
            if (i >= 4 and depth >= 3 and not in_check and not is_cap
                    and not move.promotion):
                # Late-move reduction, re-search at full depth if it looks good
                score = -self.negamax(board, depth - 2, -beta, -alpha, ply + 1)
                if score > alpha:
                    score = -self.negamax(board, depth - 1, -beta, -alpha, ply + 1)
            else:
                score = -self.negamax(board, depth - 1, -beta, -alpha, ply + 1)
            board.pop()
            if self.stop:
                return 0

            if score > best:
                best = score
                best_move = move
            if score > alpha:
                alpha = score
            if alpha >= beta:
                if not is_cap:
                    k = self.killers[ply]
                    if move != k[0]:
                        k[1] = k[0]
                        k[0] = move
                    hk = (board.turn, move.from_square, move.to_square)
                    self.history[hk] = self.history.get(hk, 0) + depth * depth
                break

        flag = UPPER if best <= orig_alpha else LOWER if best >= beta else EXACT
        self.tt[key] = (depth, flag, to_tt(best, ply), best_move)
        return best

    def search(self, board, time_limit=THINK_TIME, max_depth=64):
        self.deadline = time.time() + time_limit
        self.stop = False
        self.nodes = 0
        self.killers = [[None, None] for _ in range(128)]
        self.history = {}
        if len(self.tt) > 1_000_000:
            self.tt.clear()

        root_key = board._transposition_key()
        best_move = None
        start = time.time()
        for depth in range(1, max_depth + 1):
            score = self.negamax(board, depth, -INF, INF, 0)
            if self.stop:
                break
            entry = self.tt.get(root_key)
            if entry and entry[3]:
                best_move = entry[3]
            elapsed = max(time.time() - start, 1e-6)
            print(f"[depth {depth}] score={score} best={board.san(best_move)} "
                  f"nodes={self.nodes} ({int(self.nodes / elapsed)} n/s)")
            if abs(score) > MATE - 100:
                break
        return best_move or next(iter(board.legal_moves))


def get_best_move(board, searcher):
    history = tuple(m.uci() for m in board.move_stack)
    if history in opening_book:
        legal = {m.uci(): m for m in board.legal_moves}
        options = [legal[u] for u in opening_book[history] if u in legal]
        if options:
            move = random.choice(options)
            print(f"[Opening Book] Playing {board.san(move)}")
            return move
    return searcher.search(board)


# --------------------------------------------------------------------------
# GUI
# --------------------------------------------------------------------------
def load_piece_images():
    pieces = ['wK', 'wQ', 'wR', 'wB', 'wN', 'wP',
              'bK', 'bQ', 'bR', 'bB', 'bN', 'bP']
    for p in pieces:
        img_path = os.path.join(PIECE_PATH, f"{p}.png")
        img = Image.open(img_path).resize((SQUARE_SIZE, SQUARE_SIZE), Image.LANCZOS)
        piece_images[p] = ImageTk.PhotoImage(img)

    for king_code in ['wK', 'bK']:
        img_path = os.path.join(PIECE_PATH, f"{king_code}.png")
        img = Image.open(img_path).resize((SQUARE_SIZE, SQUARE_SIZE), Image.LANCZOS).rotate(90, expand=True)
        fallen_king_image[king_code] = ImageTk.PhotoImage(img)


def piece_to_code(piece):
    return ('w' if piece.color == chess.WHITE else 'b') + piece.symbol().upper()


class ChessApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Pyfish")
        self.canvas = tk.Canvas(root, width=8 * SQUARE_SIZE, height=8 * SQUARE_SIZE)
        self.canvas.pack()
        self.canvas.bind("<Button-1>", self.on_click)

        self.board = chess.Board()
        self.selected_square = None
        self.move_history = []
        self.player_color = None
        self.searcher = Searcher()
        self.thinking = False
        self.result_q = queue.Queue()
        self.game_over_shown = False

        load_piece_images()
        self.show_color_menu()

    def show_color_menu(self):
        self.canvas.delete("all")
        self.canvas.create_text(256, 100, text="Choose Your Color", font=("Arial", 20, "bold"))
        self.canvas.create_rectangle(120, 180, 240, 260, fill="white")
        self.canvas.create_text(180, 220, text="White", font=("Arial", 16))
        self.canvas.create_rectangle(280, 180, 400, 260, fill="black")
        self.canvas.create_text(340, 220, text="Black", font=("Arial", 16), fill="white")
        self.canvas.bind("<Button-1>", self.color_menu_click)

    def color_menu_click(self, event):
        if 120 <= event.x <= 240 and 180 <= event.y <= 260:
            self.player_color = chess.WHITE
        elif 280 <= event.x <= 400 and 180 <= event.y <= 260:
            self.player_color = chess.BLACK
        else:
            return

        self.canvas.unbind("<Button-1>")
        self.canvas.bind("<Button-1>", self.on_click)
        self.draw_board()

        if self.player_color == chess.BLACK:
            self.root.after(500, self.bot_move)

    def draw_square(self, sq, **kwargs):
        col = chess.square_file(sq)
        row = 7 - chess.square_rank(sq)
        x1, y1 = col * SQUARE_SIZE, row * SQUARE_SIZE
        self.canvas.create_rectangle(x1, y1, x1 + SQUARE_SIZE, y1 + SQUARE_SIZE, **kwargs)

    def draw_board(self):
        self.canvas.delete("all")
        colors = ["#f0d9b5", "#b58863"]

        for row in range(8):
            for col in range(8):
                x1, y1 = col * SQUARE_SIZE, row * SQUARE_SIZE
                self.canvas.create_rectangle(x1, y1, x1 + SQUARE_SIZE, y1 + SQUARE_SIZE,
                                             fill=colors[(row + col) % 2], outline="")

        if self.move_history:
            last = self.move_history[-1]
            for sq in (last.from_square, last.to_square):
                self.draw_square(sq, fill="#fff200", stipple="gray50")

        if self.selected_square is not None:
            self.draw_square(self.selected_square, outline="red", width=3)

        if self.board.is_check():
            king_sq = self.board.king(self.board.turn)
            if king_sq is not None:
                self.draw_square(king_sq, fill="#ffa500", stipple="gray50")

        for square, piece in self.board.piece_map().items():
            col = chess.square_file(square)
            row = 7 - chess.square_rank(square)
            self.canvas.create_image(col * SQUARE_SIZE, row * SQUARE_SIZE, anchor="nw",
                                     image=piece_images[piece_to_code(piece)])

        if self.board.is_game_over():
            self.display_game_over()

    def display_game_over(self):
        result = self.board.result()
        if result in ("1-0", "0-1"):
            loser = chess.WHITE if result == "0-1" else chess.BLACK
            king_sq = self.board.king(loser)
            if king_sq is not None:
                code = 'wK' if loser == chess.WHITE else 'bK'
                col = chess.square_file(king_sq)
                row = 7 - chess.square_rank(king_sq)
                self.canvas.create_image(col * SQUARE_SIZE, row * SQUARE_SIZE, anchor="nw",
                                         image=fallen_king_image[code])
        if not self.game_over_shown:
            self.game_over_shown = True
            winner = "White" if result == "1-0" else "Black" if result == "0-1" else "Draw"
            self.root.after(50, lambda: messagebox.showinfo("Game Over", f"Game Over: {winner}"))

    def on_click(self, event):
        if self.board.is_game_over() or self.thinking:
            return

        col = event.x // SQUARE_SIZE
        row = 7 - (event.y // SQUARE_SIZE)
        if not (0 <= col < 8 and 0 <= row < 8):
            return
        square = chess.square(col, row)

        if self.selected_square is None:
            piece = self.board.piece_at(square)
            if piece and piece.color == self.board.turn == self.player_color:
                self.selected_square = square
        else:
            move = chess.Move(self.selected_square, square)

            # Only ask for a promotion piece if a promotion is actually legal here
            piece = self.board.piece_at(self.selected_square)
            if (piece and piece.piece_type == chess.PAWN
                    and chess.square_rank(square) in (0, 7)
                    and chess.Move(self.selected_square, square, promotion=chess.QUEEN)
                    in self.board.legal_moves):
                move = chess.Move(self.selected_square, square,
                                  promotion=self.ask_promotion_piece())

            if move in self.board.legal_moves:
                self.board.push(move)
                self.move_history.append(move)
                self.selected_square = None
                self.draw_board()
                if not self.board.is_game_over():
                    self.root.after(200, self.bot_move)
                return
            self.selected_square = None
        self.draw_board()

    def ask_promotion_piece(self):
        piece = simpledialog.askstring("Promotion", "Promote to (q, r, b, n):")
        if not piece:
            return chess.QUEEN
        return {'q': chess.QUEEN, 'r': chess.ROOK,
                'b': chess.BISHOP, 'n': chess.KNIGHT}.get(piece.lower(), chess.QUEEN)

    # The search runs in a background thread so the window never freezes.
    def bot_move(self):
        if self.thinking or self.board.is_game_over() or self.board.turn == self.player_color:
            return
        self.thinking = True
        board_copy = self.board.copy()

        def work():
            self.result_q.put(get_best_move(board_copy, self.searcher))

        threading.Thread(target=work, daemon=True).start()
        self.root.after(50, self.poll_bot)

    def poll_bot(self):
        try:
            move = self.result_q.get_nowait()
        except queue.Empty:
            self.root.after(50, self.poll_bot)
            return
        self.thinking = False
        if move in self.board.legal_moves:
            self.board.push(move)
            self.move_history.append(move)
        self.draw_board()


if __name__ == "__main__":
    root = tk.Tk()
    app = ChessApp(root)
    root.mainloop()
