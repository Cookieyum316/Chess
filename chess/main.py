import tkinter as tk
from tkinter import simpledialog, messagebox
import chess
import os
from PIL import Image, ImageTk

SQUARE_SIZE = 64
PIECE_PATH = os.path.join(os.path.dirname(__file__), "pieces")

piece_images = {}
fallen_king_image = {}

opening_book = {
    (): ["e4", "d4", "Nf3", "c4"],
    ("e4",): ["c5"],
}


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


def evaluate_board(board):
    values = {
        chess.PAWN: 100,
        chess.KNIGHT: 320,
        chess.BISHOP: 330,
        chess.ROOK: 500,
        chess.QUEEN: 900,
        chess.KING: 20000
    }

    value = 0
    for ptype in values:
        value += len(board.pieces(ptype, chess.WHITE)) * values[ptype]
        value -= len(board.pieces(ptype, chess.BLACK)) * values[ptype]

    central_squares = [chess.D4, chess.D5, chess.E4, chess.E5]
    for sq in central_squares:
        piece = board.piece_at(sq)
        if piece and piece.piece_type == chess.PAWN:
            value += 20 if piece.color == chess.WHITE else -20

    if board.piece_at(chess.E1) != chess.Piece(chess.KING, chess.WHITE):
        value += 40
    else:
        value -= 30

    if board.piece_at(chess.E8) != chess.Piece(chess.KING, chess.BLACK):
        value -= 40
    else:
        value += 30

    return value


def quiescence(board, alpha, beta, is_maximizing):
    stand_pat = evaluate_board(board)
    if is_maximizing:
        if stand_pat >= beta:
            return beta
        if alpha < stand_pat:
            alpha = stand_pat
    else:
        if stand_pat <= alpha:
            return alpha
        if beta > stand_pat:
            beta = stand_pat

    for move in board.legal_moves:
        if board.is_capture(move):
            board.push(move)
            score = quiescence(board, alpha, beta, not is_maximizing)
            board.pop()
            if is_maximizing:
                if score >= beta:
                    return beta
                if score > alpha:
                    alpha = score
            else:
                if score <= alpha:
                    return alpha
                if score < beta:
                    beta = score
    return alpha if is_maximizing else beta


def minimax(board, depth, alpha, beta, is_maximizing):
    if depth == 0 or board.is_game_over():
        return quiescence(board, alpha, beta, is_maximizing)

    if is_maximizing:
        max_eval = float('-inf')
        for move in board.legal_moves:
            board.push(move)
            eval = minimax(board, depth - 1, alpha, beta, False)
            board.pop()
            max_eval = max(max_eval, eval)
            alpha = max(alpha, eval)
            if beta <= alpha:
                break
        return max_eval
    else:
        min_eval = float('inf')
        for move in board.legal_moves:
            board.push(move)
            eval = minimax(board, depth - 1, alpha, beta, True)
            board.pop()
            min_eval = min(min_eval, eval)
            beta = min(beta, eval)
            if beta <= alpha:
                break
        return min_eval


def get_best_move(board):
    try:
        san_history = tuple(board.san(m) for m in board.move_stack)
        if san_history in opening_book:
            candidates = opening_book[san_history]
            for move in board.legal_moves:
                if board.san(move) in candidates:
                    print(f"[Opening Book] Playing {board.san(move)}")
                    return move
    except Exception as e:
        print(f"Opening book error: {e}")

    print("\n[Bot Calculating Moves] Evaluating legal moves...")
    best_move = None
    best_value = float('inf')
    for move in board.legal_moves:
        board.push(move)
        board_value = minimax(board, 2, float('-inf'), float('inf'), True)
        board.pop()
        print(f"Evaluated move {board.san(move)}: Score = {board_value}")
        if board_value < best_value:
            best_value = board_value
            best_move = move
    print(f"[Bot Decision] Best move: {board.san(best_move)} with score {best_value}\n")
    return best_move


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

    def draw_board(self):
        self.canvas.delete("all")
        colors = ["#f0d9b5", "#b58863"]
        highlight_color = "#fff200"

        for row in range(8):
            for col in range(8):
                x1 = col * SQUARE_SIZE
                y1 = row * SQUARE_SIZE
                x2 = x1 + SQUARE_SIZE
                y2 = y1 + SQUARE_SIZE
                color = colors[(row + col) % 2]
                self.canvas.create_rectangle(x1, y1, x2, y2, fill=color, outline="")

        if self.move_history:
            last_move = self.move_history[-1]
            for sq in [last_move.from_square, last_move.to_square]:
                col = chess.square_file(sq)
                row = 7 - chess.square_rank(sq)
                x1 = col * SQUARE_SIZE
                y1 = row * SQUARE_SIZE
                x2 = x1 + SQUARE_SIZE
                y2 = y1 + SQUARE_SIZE
                self.canvas.create_rectangle(x1, y1, x2, y2, fill=highlight_color, stipple="gray50")

        if self.selected_square is not None:
            col = chess.square_file(self.selected_square)
            row = 7 - chess.square_rank(self.selected_square)
            x1 = col * SQUARE_SIZE
            y1 = row * SQUARE_SIZE
            x2 = x1 + SQUARE_SIZE
            y2 = y1 + SQUARE_SIZE
            self.canvas.create_rectangle(x1, y1, x2, y2, outline="red", width=3)

        if self.board.is_check():
            king_sq = self.board.king(self.board.turn)
            if king_sq is not None:
                col = chess.square_file(king_sq)
                row = 7 - chess.square_rank(king_sq)
                x1 = col * SQUARE_SIZE
                y1 = row * SQUARE_SIZE
                x2 = x1 + SQUARE_SIZE
                y2 = y1 + SQUARE_SIZE
                self.canvas.create_rectangle(x1, y1, x2, y2, fill="#ffa500", stipple="gray50")

        for square in chess.SQUARES:
            piece = self.board.piece_at(square)
            if piece:
                code = piece_to_code(piece)
                col = chess.square_file(square)
                row = 7 - chess.square_rank(square)
                x = col * SQUARE_SIZE
                y = row * SQUARE_SIZE
                self.canvas.create_image(x, y, anchor="nw", image=piece_images[code])

        if self.board.is_game_over():
            self.display_game_over()

    def display_game_over(self):
        result = self.board.result()
        winner = "White" if result == "1-0" else "Black" if result == "0-1" else "Draw"
        messagebox.showinfo("Game Over", f"Game Over: {winner}")
        king_sq = self.board.king(chess.WHITE if result == "0-1" else chess.BLACK)
        if king_sq is not None:
            code = 'wK' if result == "0-1" else 'bK'
            col = chess.square_file(king_sq)
            row = 7 - chess.square_rank(king_sq)
            x = col * SQUARE_SIZE
            y = row * SQUARE_SIZE
            self.canvas.create_image(x, y, anchor="nw", image=fallen_king_image[code])

    def on_click(self, event):
        if self.board.is_game_over():
            return

        col = event.x // SQUARE_SIZE
        row = 7 - (event.y // SQUARE_SIZE)
        square = chess.square(col, row)

        if self.selected_square is None:
            piece = self.board.piece_at(square)
            if piece and piece.color == self.board.turn == self.player_color:
                self.selected_square = square
        else:
            move = chess.Move(self.selected_square, square)

            # Handle pawn promotion
            if chess.square_rank(square) in [0, 7]:
                piece = self.board.piece_at(self.selected_square)
                if piece and piece.piece_type == chess.PAWN:
                    promotion = self.ask_promotion_piece()
                    if promotion:
                        move = chess.Move(self.selected_square, square, promotion=promotion)

            if move in self.board.legal_moves:
                self.board.push(move)
                self.move_history.append(move)
                self.selected_square = None
                self.draw_board()
                if not self.board.is_game_over():
                    self.root.after(200, self.bot_move)
            else:
                self.selected_square = None
        self.draw_board()

    def ask_promotion_piece(self):
        piece = simpledialog.askstring("Promotion", "Promote to (q, r, b, n):")
        if not piece:
            return chess.QUEEN
        piece = piece.lower()
        return {
            'q': chess.QUEEN,
            'r': chess.ROOK,
            'b': chess.BISHOP,
            'n': chess.KNIGHT
        }.get(piece, chess.QUEEN)

    def bot_move(self):
        if self.board.turn != self.player_color and not self.board.is_game_over():
            move = get_best_move(self.board)
            self.board.push(move)
            self.move_history.append(move)
            self.draw_board()


if __name__ == "__main__":
    root = tk.Tk()
    app = ChessApp(root)
    root.mainloop()
