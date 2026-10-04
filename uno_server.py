#!/usr/bin/env python3
"""LAN UNO - run on one computer; everyone on the same Wi-Fi opens the printed URL.

No installs, no cloud: pure Python standard library. Live updates use Server-Sent Events.
Usage:  python3 uno_server.py [port]      (default port 8000)
"""
import json
import os
import random
import secrets
import socket
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

COLORS = ["red", "yellow", "green", "blue"]
DIGITS = [str(n) for n in range(10)]
MAX_PLAYERS = 10
HAND_SIZE = 7


MODES = ("classic", "nomercy")
MERCY_LIMIT = 25
DRAW_VALUES = {"draw2": 2, "wild4": 4, "draw4": 4, "wildrev4": 4, "wild6": 6, "wild10": 10}
NAMES = {"skip": "Skip", "reverse": "Reverse", "draw2": "+2", "wild": "Wild", "wild4": "Wild +4",
         "draw4": "+4", "discard": "Discard All", "skipall": "Skip Everyone",
         "wildrev4": "Wild Reverse +4", "wild6": "Wild +6", "wild10": "Wild +10", "roulette": "Color Roulette"}


def new_deck(mode):
    cards = []

    def add(color, value, times=1):
        for _ in range(times):
            cards.append({"id": len(cards), "color": color, "value": value})

    if mode == "nomercy":  # UNO Show 'Em No Mercy: 168 cards
        for c in COLORS:
            for d in DIGITS:
                add(c, d, 2)
            for v, n in (("draw2", 3), ("skip", 3), ("reverse", 3), ("discard", 3), ("draw4", 2), ("skipall", 2)):
                add(c, v, n)
        for v, n in (("wildrev4", 8), ("wild6", 4), ("wild10", 4), ("roulette", 8)):
            add("wild", v, n)
    else:  # classic: 108 cards
        for c in COLORS:
            add(c, "0")
            for v in DIGITS[1:] + ["skip", "reverse", "draw2"]:
                add(c, v, 2)
        add("wild", "wild", 4)
        add("wild", "wild4", 4)
    random.shuffle(cards)
    return cards


def card_name(card):
    v = NAMES.get(card["value"], card["value"])
    return v if card["color"] == "wild" else "%s %s" % (card["color"].capitalize(), v)


class GameError(Exception):
    pass


class Game:
    def __init__(self):
        self.cond = threading.Condition()
        self.version = 0
        self.players = []
        self.host = None
        self.phase = "lobby"
        self.mode = "classic"
        self.log = []
        self._clear_round()

    # ---------- helpers ----------
    def _clear_round(self):
        self.deck, self.discard = [], []
        self.turn, self.direction = 0, 1
        self.color = None
        self.drawn_id = None
        self.winner = None
        self.pending = 0       # No Mercy: stacked draw total waiting for the current player
        self.pending_min = 0   # No Mercy: lowest draw value that may be stacked
        self.roulette = False  # No Mercy: current player must pick a roulette color

    def _changed(self):
        self.version += 1
        self.cond.notify_all()

    def _say(self, msg):
        self.log = (self.log + [msg])[-8:]

    def _player(self, token):
        return next((p for p in self.players if p["token"] == token), None)

    def _require(self, token):
        p = self._player(token)
        if not p:
            raise GameError("You are not in this game")
        return p

    def _require_turn(self, token):
        p = self._require(token)
        if self.phase != "playing":
            raise GameError("Game is not running")
        if self.players[self.turn] is not p:
            raise GameError("Not your turn")
        return p

    def _alive(self):
        return [p for p in self.players if not p["out"]]

    def _next_index(self, steps=1):
        n, idx = len(self.players), self.turn
        for _ in range(steps):
            idx = (idx + self.direction) % n
            while self.players[idx]["out"]:
                idx = (idx + self.direction) % n
        return idx

    def _advance(self, steps=1):
        self.turn = self._next_index(steps)
        self.drawn_id = None

    def _draw_one(self, player):
        if not self.deck:
            top = self.discard.pop()
            self.deck, self.discard = self.discard, [top]
            random.shuffle(self.deck)
            if not self.deck:
                return None
        card = self.deck.pop()
        player["hand"].append(card)
        if len(player["hand"]) > 1:
            player["uno"] = False
            player["vulnerable"] = False
        return card

    def _draw_cards(self, player, n):
        got = []
        for _ in range(n):
            c = self._draw_one(player)
            if not c:
                break
            got.append(c)
        return got

    def _win(self, p, why=None):
        self.phase = "over"
        self.winner = p["name"]
        p["wins"] += 1
        self._say(why or "%s wins!" % p["name"])

    def _mercy(self, p):
        """No Mercy rule: 25+ cards = eliminated. Returns True if this ended the game."""
        if self.mode != "nomercy" or p["out"] or len(p["hand"]) < MERCY_LIMIT:
            return False
        p["out"] = True
        self.deck[0:0] = p["hand"]
        p["hand"], p["uno"], p["vulnerable"] = [], False, False
        self._say("💀 %s hit %d cards and is out!" % (p["name"], MERCY_LIMIT))
        alive = self._alive()
        if len(alive) == 1:
            self._win(alive[0], "%s is the last one standing and wins!" % alive[0]["name"])
            return True
        return False

    def _playable(self, card):
        if self.roulette:
            return False
        if self.pending:
            return DRAW_VALUES.get(card["value"], 0) >= self.pending_min
        top = self.discard[-1]
        return card["color"] == "wild" or card["color"] == self.color or card["value"] == top["value"]

    def _clear_vulnerable(self, actor):
        for p in self.players:
            if p is not actor:
                p["vulnerable"] = False

    def _fix_uno(self, *players):
        for p in players:
            if len(p["hand"]) != 1:
                p["uno"] = False
            p["vulnerable"] = False

    # ---------- lobby actions ----------
    def _clean_name(self, name, exclude=None):
        name = " ".join(str(name or "").split())[:16]
        if not name:
            raise GameError("Enter a name")
        taken = {p["name"].lower() for p in self.players if p is not exclude}
        base, i = name, 2
        while name.lower() in taken:
            name = "%s %d" % (base, i)
            i += 1
        return name

    def join(self, name):
        name = self._clean_name(name)
        if self.phase == "playing":
            raise GameError("A game is in progress - wait for it to finish")
        if len(self.players) >= MAX_PLAYERS:
            raise GameError("Room is full (%d players)" % MAX_PLAYERS)
        token = secrets.token_urlsafe(9)
        self.players.append({"token": token, "name": name, "hand": [], "uno": False, "vulnerable": False,
                             "out": False, "streams": 0, "wins": 0})
        if not self.host:
            self.host = token
        self._say("%s joined" % name)
        return token

    def rename(self, token, name):
        p = self._require(token)
        if self.phase == "playing":
            raise GameError("Change your name between games")
        old, p["name"] = p["name"], self._clean_name(name, exclude=p)
        if old != p["name"]:
            self._say("%s is now %s" % (old, p["name"]))

    def set_mode(self, token, mode):
        self._require(token)
        if token != self.host:
            raise GameError("Only the host can change the mode")
        if self.phase == "playing":
            raise GameError("Can't change mode mid-game")
        if mode not in MODES:
            raise GameError("Unknown mode")
        self.mode = mode
        self._say("Mode: %s" % ("No Mercy" if mode == "nomercy" else "Classic"))

    def start(self, token):
        self._require(token)
        if token != self.host:
            raise GameError("Only the host can start")
        if self.phase == "playing":
            raise GameError("Already playing")
        if len(self.players) < 2:
            raise GameError("Need at least 2 players")
        self._clear_round()
        self.deck = new_deck(self.mode)
        for p in self.players:
            p["hand"], p["uno"], p["vulnerable"], p["out"] = [], False, False, False
        for _ in range(HAND_SIZE):
            for p in self.players:
                p["hand"].append(self.deck.pop())
        while self.deck[-1]["value"] not in DIGITS:  # start on a number card
            self.deck.insert(0, self.deck.pop())
        first = self.deck.pop()
        self.discard = [first]
        self.color = first["color"]
        self.turn = random.randrange(len(self.players))
        self.phase = "playing"
        self.log = []
        self._say("New %sgame! %s goes first" % ("NO MERCY " if self.mode == "nomercy" else "",
                                                  self.players[self.turn]["name"]))

    # ---------- turn actions ----------
    def play(self, token, card_id, color=None, target=None):
        p = self._require_turn(token)
        card = next((c for c in p["hand"] if c["id"] == card_id), None)
        if not card:
            raise GameError("You don't have that card")
        if self.drawn_id is not None and card_id != self.drawn_id:
            raise GameError("After drawing you can only play the drawn card (or pass)")
        if not self._playable(card):
            if self.roulette:
                raise GameError("Pick a roulette color first")
            if self.pending:
                raise GameError("Stack a +%d or higher, or take %d cards" % (self.pending_min, self.pending))
            raise GameError("That card doesn't match")
        v, nomercy = card["value"], self.mode == "nomercy"
        if card["color"] == "wild" and v != "roulette" and color not in COLORS:
            raise GameError("Pick a color")
        victim = None
        if nomercy and v == "7" and len(p["hand"]) > 1:
            others = [x for x in self._alive() if x is not p]
            victim = others[0] if len(others) == 1 else next((x for x in others if x["name"] == target), None)
            if not victim:
                raise GameError("Pick a player to swap hands with")

        self._clear_vulnerable(p)
        p["hand"].remove(card)
        self.discard.append(card)
        if card["color"] != "wild":
            self.color = card["color"]
        elif v != "roulette":
            self.color = color
        self.drawn_id = None
        msg = "%s played %s" % (p["name"], card_name(card))
        if card["color"] == "wild" and v != "roulette":
            msg += " -> %s" % color
        if nomercy and v == "discard":
            dumped = [c for c in p["hand"] if c["color"] == card["color"]]
            for c in dumped:
                p["hand"].remove(c)
            self.discard[-1:-1] = dumped
            if dumped:
                msg += " and dumped %d more" % len(dumped)
        if not p["hand"]:
            self._say(msg)
            self._win(p)
            return
        if len(p["hand"]) == 1 and not p["uno"]:
            p["vulnerable"] = True

        alive_n = len(self._alive())
        if nomercy:
            if v == "skip":
                msg += ", %s is skipped" % self.players[self._next_index()]["name"]
                self._advance(2)
            elif v == "reverse":
                if alive_n == 2:
                    self._advance(2)
                else:
                    self.direction *= -1
                    self._advance(1)
            elif v == "skipall":
                msg += " - everyone skipped, %s goes again" % p["name"]
                self._advance(0)
            elif v in DRAW_VALUES:
                if v == "wildrev4" and alive_n > 2:
                    self.direction *= -1
                self.pending += DRAW_VALUES[v]
                self.pending_min = DRAW_VALUES[v]
                self._advance(1)
                msg += " - %s must stack or take %d" % (self.players[self.turn]["name"], self.pending)
            elif v == "roulette":
                self.roulette = True
                self._advance(1)
                msg += " - %s spins the roulette" % self.players[self.turn]["name"]
            elif v == "7":
                p["hand"], victim["hand"] = victim["hand"], p["hand"]
                self._fix_uno(p, victim)
                msg += " and swapped hands with %s" % victim["name"]
                self._say(msg)
                if self._mercy(p) or self._mercy(victim):
                    return
                self._advance(1)
                return
            elif v == "0":
                alive = self._alive()
                hands = [x["hand"] for x in alive]
                k = self.direction  # each player passes their hand to the next player in play order
                for i, x in enumerate(alive):
                    x["hand"] = hands[(i - k) % len(alive)]
                self._fix_uno(*alive)
                msg += " - everyone passed their hand %s" % ("left" if k == 1 else "right")
                self._advance(1)
            else:
                self._advance(1)
        else:
            if v == "skip":
                msg += ", %s is skipped" % self.players[self._next_index()]["name"]
                self._advance(2)
            elif v == "reverse":
                if alive_n == 2:
                    self._advance(2)
                else:
                    self.direction *= -1
                    self._advance(1)
            elif v in ("draw2", "wild4"):
                victim = self.players[self._next_index()]
                k = DRAW_VALUES[v]
                self._draw_cards(victim, k)
                msg += ", %s draws %d" % (victim["name"], k)
                self._advance(2)
            else:
                self._advance(1)
        self._say(msg)

    def draw(self, token):
        p = self._require_turn(token)
        if self.roulette:
            raise GameError("Pick a roulette color")
        if self.pending:
            raise GameError("Stack a draw card or take %d" % self.pending)
        if self.drawn_id is not None:
            raise GameError("You already drew - play it or pass")
        self._clear_vulnerable(p)
        if self.mode == "nomercy":  # draw until you get a playable card
            n = 0
            while True:
                c = self._draw_one(p)
                if not c:
                    self._say("%s drew %d and the deck ran out" % (p["name"], n))
                    self._advance(1)
                    return
                n += 1
                if self._mercy(p):
                    return
                if p["out"]:
                    self._advance(1)
                    return
                if self._playable(c):
                    self.drawn_id = c["id"]
                    self._say("%s drew %d card%s" % (p["name"], n, "" if n == 1 else "s"))
                    return
        got = self._draw_cards(p, 1)
        if not got:
            self._say("%s couldn't draw (deck empty) and passed" % p["name"])
            self._advance(1)
        elif self._playable(got[0]):
            self.drawn_id = got[0]["id"]
            self._say("%s drew a card" % p["name"])
        else:
            self._say("%s drew a card and passed" % p["name"])
            self._advance(1)

    def take(self, token):
        p = self._require_turn(token)
        if not self.pending:
            raise GameError("Nothing to take")
        self._clear_vulnerable(p)
        n = self.pending
        self.pending = self.pending_min = 0
        self._draw_cards(p, n)
        self._say("%s took %d cards" % (p["name"], n))
        if self._mercy(p):
            return
        self._advance(1)

    def spin(self, token, color):
        p = self._require_turn(token)
        if not self.roulette:
            raise GameError("No roulette to spin")
        if color not in COLORS:
            raise GameError("Pick a color")
        self._clear_vulnerable(p)
        self.roulette = False
        self.color = color
        n = 0
        while True:
            c = self._draw_one(p)
            if not c:
                break
            n += 1
            if c["color"] == color:
                break
        self._say("%s picked %s and flipped %d card%s" % (p["name"], color, n, "" if n == 1 else "s"))
        if self._mercy(p):
            return
        self._advance(1)

    def pass_turn(self, token):
        p = self._require_turn(token)
        if self.drawn_id is None:
            raise GameError("Draw a card first")
        self._say("%s passed" % p["name"])
        self._advance(1)

    def uno(self, token):
        p = self._require(token)
        if self.phase != "playing" or p["out"]:
            raise GameError("Game is not running")
        if len(p["hand"]) > 2:
            raise GameError("You can only call UNO with 2 or fewer cards")
        if p["uno"]:
            return
        p["uno"], p["vulnerable"] = True, False
        self._say("%s: UNO!" % p["name"])

    def catch(self, token, target):
        p = self._require(token)
        t = next((x for x in self.players if x["name"] == target), None)
        if not t or t is p or self.phase != "playing":
            raise GameError("Can't catch that player")
        if not t["vulnerable"]:
            raise GameError("Too late - nothing to catch")
        t["vulnerable"] = False
        self._draw_cards(t, 2)
        self._say("%s caught %s without UNO! +2 cards" % (p["name"], t["name"]))
        if self._mercy(t):
            return
        if t["out"] and self.players[self.turn] is t:
            self._advance(1)

    def leave(self, token):
        p = self._require(token)
        idx = self.players.index(p)
        self.players.remove(p)
        self._say("%s left" % p["name"])
        if self.host == token:
            self.host = self.players[0]["token"] if self.players else None
        if not self.players:
            self.phase, self.log = "lobby", []
            self._clear_round()
            return
        if self.phase == "playing":
            self.deck[0:0] = p["hand"]
            alive = self._alive()
            if len(alive) < 2:
                if alive:
                    self._win(alive[0], "%s wins (everyone else left)" % alive[0]["name"])
                else:
                    self.phase = "over"
                return
            if idx < self.turn:
                self.turn -= 1
            elif idx == self.turn:
                self.turn = (idx if self.direction == 1 else idx - 1) % len(self.players)
                self.drawn_id = None
                if self.players[self.turn]["out"]:
                    self.turn = self._next_index(1)

    def lobby(self, token):
        self._require(token)
        if token != self.host:
            raise GameError("Only the host can do that")
        self.phase = "lobby"
        self._clear_round()
        for p in self.players:
            p["hand"], p["uno"], p["vulnerable"], p["out"] = [], False, False, False
        self._say("Back to lobby")

    # ---------- view ----------
    def view(self, token):
        me = self._player(token)
        if not me:
            return {"phase": "unknown"}
        playing = self.phase == "playing"
        cur = self.players[self.turn] if playing else None
        my_turn = cur is me
        playable = []
        if my_turn:
            playable = [c["id"] for c in me["hand"] if self._playable(c)
                        and (self.drawn_id is None or c["id"] == self.drawn_id)]
        return {
            "phase": self.phase,
            "mode": self.mode,
            "you": {"name": me["name"], "hand": me["hand"], "isHost": token == self.host, "uno": me["uno"],
                    "out": me["out"]},
            "players": [{"name": p["name"], "count": len(p["hand"]), "turn": p is cur, "uno": p["uno"],
                         "vulnerable": p["vulnerable"], "you": p is me, "online": p["streams"] > 0,
                         "host": p["token"] == self.host, "wins": p["wins"], "out": p["out"]}
                        for p in self.players],
            "top": self.discard[-1] if self.discard else None,
            "color": self.color,
            "direction": self.direction,
            "turnName": cur["name"] if cur else None,
            "myTurn": my_turn,
            "drawnId": self.drawn_id if my_turn else None,
            "playable": playable,
            "pending": self.pending,
            "pendingMin": self.pending_min,
            "roulette": self.roulette,
            "deckCount": len(self.deck),
            "log": self.log,
            "winner": self.winner,
            "mercyLimit": MERCY_LIMIT,
        }


GAME = Game()


class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):
        pass

    def _json(self, code, obj):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        url = urlparse(self.path)
        token = parse_qs(url.query).get("token", [""])[0]
        if url.path == "/":
            body = PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif url.path == "/uno_server.py":  # lets a phone download the server to host it itself
            with open(__file__, "rb") as f:
                body = f.read()
            self.send_response(200)
            self.send_header("Content-Type", "text/x-python")
            self.send_header("Content-Disposition", "attachment; filename=uno_server.py")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif url.path == "/api/state":
            with GAME.cond:
                self._json(200, GAME.view(token))
        elif url.path == "/events":
            self._events(token)
        else:
            self._json(404, {"ok": False, "error": "not found"})

    def _events(self, token):
        self.send_response(200)
        self.send_header("Content-Type", "text/event-stream")
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        with GAME.cond:
            p = GAME._player(token)
            if p:
                p["streams"] += 1
                GAME._changed()
        last = -1
        try:
            while True:
                with GAME.cond:
                    GAME.cond.wait_for(lambda: GAME.version != last, timeout=15)
                    v, data = GAME.version, GAME.view(token)
                if v == last:
                    self.wfile.write(b": ping\n\n")
                else:
                    self.wfile.write(("data: %s\n\n" % json.dumps(data)).encode())
                    if data["phase"] == "unknown":
                        break
                self.wfile.flush()
                last = v
        except (BrokenPipeError, ConnectionResetError, OSError):
            pass
        finally:
            with GAME.cond:
                p = GAME._player(token)
                if p:
                    p["streams"] = max(0, p["streams"] - 1)
                    GAME._changed()

    def do_POST(self):
        action = urlparse(self.path).path.rsplit("/", 1)[-1]
        try:
            n = int(self.headers.get("Content-Length") or 0)
            data = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            return self._json(400, {"ok": False, "error": "bad request"})
        token = data.get("token") or ""
        actions = {
            "join": lambda: GAME.join(data.get("name")),
            "start": lambda: GAME.start(token),
            "play": lambda: GAME.play(token, data.get("card"), data.get("color"), data.get("target")),
            "take": lambda: GAME.take(token),
            "spin": lambda: GAME.spin(token, data.get("color")),
            "rename": lambda: GAME.rename(token, data.get("name")),
            "mode": lambda: GAME.set_mode(token, data.get("mode")),
            "draw": lambda: GAME.draw(token),
            "pass": lambda: GAME.pass_turn(token),
            "uno": lambda: GAME.uno(token),
            "catch": lambda: GAME.catch(token, data.get("target")),
            "leave": lambda: GAME.leave(token),
            "lobby": lambda: GAME.lobby(token),
        }
        if action not in actions:
            return self._json(404, {"ok": False, "error": "unknown action"})
        with GAME.cond:
            try:
                result = actions[action]()
            except GameError as e:
                return self._json(400, {"ok": False, "error": str(e)})
            GAME._changed()
        out = {"ok": True}
        if action == "join":
            out["token"] = result
        self._json(200, out)


def lan_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))  # no packets are sent; just picks the Wi-Fi interface
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


PAGE = r"""<!doctype html>
<html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no">
<title>LAN UNO</title>
<link rel="icon" href="data:,">
<style>
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
body{margin:0;font-family:-apple-system,system-ui,Segoe UI,Roboto,sans-serif;background:radial-gradient(circle at 50% 30%,#1b6b3a,#0b3d20);color:#fff;min-height:100vh}
#app{max-width:900px;margin:0 auto;padding:12px;display:flex;flex-direction:column;min-height:100vh;gap:10px}
h1{margin:8px 0;text-align:center;font-size:34px;letter-spacing:2px}
h1 span{background:#e53935;padding:2px 14px;border-radius:40px;transform:rotate(-8deg);display:inline-block;border:3px solid #fff}
.panel{background:rgba(0,0,0,.25);border-radius:14px;padding:14px}
input{width:100%;padding:12px;font-size:18px;border-radius:10px;border:0;margin:8px 0}
button{font-size:16px;font-weight:700;padding:11px 16px;border-radius:10px;border:0;cursor:pointer;background:#fff;color:#123}
button:disabled{opacity:.4;cursor:default}
button.big{width:100%;font-size:19px;padding:14px}
button.uno{background:#e53935;color:#fff;font-size:20px;animation:pulse 1s infinite}
button.warn{background:#fdd835}
button.ghost{background:transparent;color:#fff;border:1px solid rgba(255,255,255,.4);font-weight:500;font-size:14px;padding:8px 12px}
@keyframes pulse{50%{transform:scale(1.07)}}
.players{display:flex;flex-wrap:wrap;gap:6px;justify-content:center}
.chip{background:rgba(0,0,0,.3);border-radius:20px;padding:6px 12px;font-size:14px;display:flex;align-items:center;gap:6px;border:2px solid transparent}
.chip.turn{border-color:#fdd835;background:rgba(253,216,53,.2)}
.chip.off{opacity:.5}
.chip b{background:#fff;color:#123;border-radius:10px;padding:0 7px}
.chip .tag{background:#e53935;border-radius:6px;padding:0 5px;font-size:11px;font-weight:800}
.chip button{padding:3px 8px;font-size:12px;background:#fdd835}
.table{display:flex;align-items:center;justify-content:center;gap:22px;padding:10px 0}
.card{width:64px;height:96px;border-radius:9px;border:3px solid #fff;position:relative;display:flex;align-items:center;justify-content:center;font-weight:900;box-shadow:0 3px 8px rgba(0,0,0,.45);flex:0 0 auto;user-select:none;transition:transform .12s}
.card .mid{background:#fff;border-radius:50%;width:48px;height:62px;display:flex;align-items:center;justify-content:center;transform:rotate(-25deg);font-size:24px}
.card .corner{position:absolute;top:2px;left:5px;font-size:13px;color:#fff;text-shadow:0 0 2px #000}
.red{background:#e53935}.red .mid{color:#e53935}
.yellow{background:#f9c80e}.yellow .mid{color:#d4a300}
.green{background:#43a047}.green .mid{color:#43a047}
.blue{background:#1e88e5}.blue .mid{color:#1e88e5}
.wild{background:conic-gradient(#e53935 0 25%,#f9c80e 0 50%,#43a047 0 75%,#1e88e5 0)}
.wild .mid{color:#111}
.back{background:#111;cursor:pointer}
.back .mid{background:#e53935;color:#fdd835;font-size:18px;transform:rotate(-25deg)}
.big .card,.card.bigc{width:92px;height:138px}
.card.bigc .mid{width:70px;height:92px;font-size:36px}
.hand{display:flex;flex-wrap:wrap;justify-content:center;gap:6px;padding:8px 0 20px}
.hand .card{cursor:pointer}
.hand .card.playable{transform:translateY(-8px);box-shadow:0 0 0 3px #fdd835,0 6px 14px rgba(0,0,0,.5)}
.hand .card.dim{filter:brightness(.55)}
.colorbox{display:flex;flex-direction:column;align-items:center;gap:6px;font-size:13px}
.dot{width:34px;height:34px;border-radius:50%;border:3px solid #fff}
.status{text-align:center;font-size:20px;font-weight:700;min-height:28px}
.status.mine{color:#fdd835}
.log{text-align:center;font-size:14px;opacity:.85;min-height:40px}
.actions{display:flex;gap:8px;justify-content:center;flex-wrap:wrap}
.footer{display:flex;gap:8px;justify-content:center;margin-top:auto;padding-bottom:6px}
#toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%);background:#111;color:#fff;padding:10px 16px;border-radius:10px;opacity:0;transition:opacity .2s;pointer-events:none;z-index:9;max-width:90%;text-align:center}
#toast.show{opacity:.95}
#picker{position:fixed;inset:0;background:rgba(0,0,0,.6);display:flex;align-items:center;justify-content:center;z-index:8}
#picker.hidden{display:none}
#picker .grid{display:grid;grid-template-columns:1fr 1fr;gap:12px;background:#222;padding:18px;border-radius:16px}
#picker .grid div{width:110px;height:80px;border-radius:12px;border:3px solid #fff;cursor:pointer}
#picker .grid div.ptitle{grid-column:1/3;height:auto;border:0;text-align:center;font-weight:700;cursor:default}
#targets{position:fixed;inset:0;background:rgba(0,0,0,.6);display:flex;align-items:center;justify-content:center;z-index:8}
#targets.hidden{display:none}
.tbox{background:#222;padding:18px;border-radius:16px;min-width:240px;display:flex;flex-direction:column;gap:8px}
.ptitle{font-weight:700;text-align:center;margin-bottom:4px}
.tbox button{width:100%}
.card .mid.small{font-size:16px}
.badge{display:inline-block;background:#111;border-radius:8px;padding:2px 10px;font-size:13px;font-weight:800;letter-spacing:1px}
.badge.nm{background:linear-gradient(90deg,#e53935,#8e24aa)}
.modes{display:flex;gap:8px;margin:10px 0}
.modes button{flex:1;background:rgba(255,255,255,.15);color:#fff;border:2px solid transparent}
.modes button.on{background:#fff;color:#123;border-color:#fdd835}
.rules{font-size:13px;opacity:.85;line-height:1.45;margin:6px 0 10px}
.chip.out{opacity:.45;text-decoration:line-through}
.pending{color:#ff8a80}
.rename{display:flex;gap:6px;margin-bottom:6px}
.rename input{margin:0;padding:8px;font-size:15px}
.rename button{padding:8px 12px;font-size:14px}
ul.lobby{list-style:none;padding:0;margin:8px 0}
ul.lobby li{padding:8px 4px;border-bottom:1px solid rgba(255,255,255,.15);font-size:18px}
.winner{text-align:center;font-size:30px;font-weight:900;margin:20px 0}
.muted{opacity:.75;font-size:14px}
</style></head>
<body>
<div id="app"></div>
<div id="toast"></div>
<div id="picker" class="hidden" onclick="if(event.target.id==='picker'&&pickMode!=='spin')this.classList.add('hidden')">
  <div class="grid"><div class="ptitle" id="ptitle">Pick a color</div>
    <div class="red" onclick="pick('red')"></div><div class="yellow" onclick="pick('yellow')"></div>
    <div class="green" onclick="pick('green')"></div><div class="blue" onclick="pick('blue')"></div>
  </div>
</div>
<div id="targets" class="hidden" onclick="if(event.target.id==='targets')this.classList.add('hidden')">
  <div class="tbox"><div class="ptitle">Swap hands with…</div><div id="tlist"></div></div>
</div>
<script>
let token = localStorage.getItem('uno_token');
let S = null, es = null, pendingWild = null, pendingSeven = null, pickMode = 'wild', wasMyTurn = false;
const $ = s => document.querySelector(s);
const SYM = {skip:'⊘', reverse:'⇄', draw2:'+2', wild:'W', wild4:'+4', draw4:'+4', discard:'ALL',
             skipall:'⊘⊘', wildrev4:'⇄+4', wild6:'+6', wild10:'+10', roulette:'🎲'};
const FULL = {skip:'Skip', reverse:'Reverse', draw2:'Draw 2', wild:'Wild', wild4:'Wild Draw 4', draw4:'Draw 4',
              discard:'Discard All (dump every card of this color)', skipall:'Skip Everyone (you go again)',
              wildrev4:'Wild Reverse Draw 4', wild6:'Wild Draw 6', wild10:'Wild Draw 10',
              roulette:'Color Roulette (next player flips until their color)'};
const RULES = {
  classic: `Match color or number. Skip, Reverse, +2, Wild, Wild +4. Can't play? Draw 1. Call UNO at one card or get caught for +2.`,
  nomercy: `168-card deck. <b>Stack</b> draw cards (+2, +4, +6, +10) — equal or higher — or take the whole pile.
  Can't play? <b>Draw until you can.</b> <b>7</b> = swap hands with anyone, <b>0</b> = everyone passes hands.
  Discard All, Skip Everyone, Color Roulette. <b>25+ cards = you're out!</b>`
};
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));

function toast(m){ const t=$('#toast'); t.textContent=m; t.classList.add('show'); clearTimeout(t._h); t._h=setTimeout(()=>t.classList.remove('show'),2400); }

async function api(action, body={}){
  try{
    const r = await fetch('/api/'+action, {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(Object.assign({token}, body))});
    const j = await r.json();
    if(!j.ok) toast(j.error);
    return j;
  }catch(e){ toast('Connection lost - is the host still running?'); return {ok:false}; }
}

function connect(){
  if(es) es.close();
  es = new EventSource('/events?token='+encodeURIComponent(token));
  es.onmessage = e => {
    S = JSON.parse(e.data);
    if(S.phase === 'unknown'){ localStorage.removeItem('uno_token'); token=null; S=null; es.close(); es=null; }
    render();
  };
}

async function join(){
  const name = $('#name').value.trim();
  if(!name) return toast('Enter your name');
  localStorage.setItem('uno_name', name);
  const j = await api('join', {name});
  if(j.ok){ token=j.token; localStorage.setItem('uno_token', token); connect(); }
}
async function rename(){
  const name = $('#newname').value.trim();
  if(!name) return toast('Enter a name');
  const j = await api('rename', {name});
  if(j.ok) localStorage.setItem('uno_name', name);
}
async function leave(){ if(!confirm('Leave the game?')) return; await api('leave'); localStorage.removeItem('uno_token'); token=null; S=null; if(es){es.close(); es=null;} render(); }

function cardHTML(c, o={}){
  const label = SYM[c.value] || c.value;
  const cls = ['card', c.color];
  if(o.playable) cls.push('playable');
  if(o.dim) cls.push('dim');
  if(o.big) cls.push('bigc');
  const small = label.length > 2 ? ' small' : '';
  return `<div class="${cls.join(' ')}" title="${esc(FULL[c.value]||c.value)}" ${o.click?`onclick="clickCard(${c.id})"`:''}><span class="corner">${label}</span><span class="mid${small}">${label}</span></div>`;
}

function showPicker(mode, title){ pickMode = mode; $('#ptitle').textContent = title; $('#picker').classList.remove('hidden'); }

function clickCard(id){
  if(!S.myTurn) return toast("Wait for your turn");
  if(S.roulette) return showPicker('spin', 'Roulette! Pick a color — you flip until you hit it');
  const c = S.you.hand.find(x => x.id === id);
  if(!S.playable.includes(id)){
    if(S.pending) return toast(`Stack a +${S.pendingMin} or higher, or take ${S.pending}`);
    return toast(S.drawnId!=null ? 'Play the card you drew, or pass' : "That card doesn't match");
  }
  if(c.color === 'wild' && c.value !== 'roulette'){ pendingWild = id; return showPicker('wild', 'Pick a color'); }
  const others = S.players.filter(p => !p.you && !p.out);
  if(S.mode === 'nomercy' && c.value === '7' && S.you.hand.length > 1 && others.length > 1){
    pendingSeven = id;
    $('#tlist').innerHTML = others.map(p => `<button onclick='swapWith(${esc(JSON.stringify(p.name))})'>${esc(p.name)} (${p.count} cards)</button>`).join('');
    $('#targets').classList.remove('hidden');
    return;
  }
  api('play', {card:id});
}
function swapWith(name){ $('#targets').classList.add('hidden'); if(pendingSeven!=null) api('play', {card:pendingSeven, target:name}); pendingSeven=null; }
function pick(color){
  $('#picker').classList.add('hidden');
  if(pickMode === 'spin') api('spin', {color});
  else if(pendingWild!=null) api('play', {card:pendingWild, color});
  pendingWild = null;
}

function modeBadge(){ return S.mode==='nomercy' ? '<span class="badge nm">NO MERCY</span>' : '<span class="badge">CLASSIC</span>'; }

function renderJoin(){
  const saved = esc(localStorage.getItem('uno_name') || '');
  return `<h1><span>UNO</span></h1>
  <div class="panel"><div>Your name</div>
    <input id="name" maxlength="16" value="${saved}" placeholder="e.g. Alex" autocomplete="off" onkeydown="if(event.key==='Enter')join()">
    <button class="big" onclick="join()">Join game</button>
    <p class="muted">Everyone on the same Wi-Fi opens this page on their own device and enters their name. The first person to join is the host and picks the mode.</p></div>`;
}

function renderLobby(){
  const list = S.players.map(p => `<li>${p.host?'👑 ':''}${esc(p.name)}${p.you?' (you)':''}${p.wins?` · 🏆${p.wins}`:''}${p.online?'':' <span class="muted">(offline)</span>'}</li>`).join('');
  const modes = S.you.isHost
    ? `<div class="modes"><button class="${S.mode==='classic'?'on':''}" onclick="api('mode',{mode:'classic'})">Classic UNO</button>
       <button class="${S.mode==='nomercy'?'on':''}" onclick="api('mode',{mode:'nomercy'})">UNO No Mercy</button></div>`
    : `<div style="margin:10px 0">Mode: ${modeBadge()}</div>`;
  const startBtn = S.you.isHost
    ? `<button class="big" ${S.players.length<2?'disabled':''} onclick="api('start')">Start ${S.mode==='nomercy'?'No Mercy':'Classic'} game (${S.players.length} players)</button>`
    : `<p class="muted" style="text-align:center">Waiting for the host to start…</p>`;
  return `<h1><span>UNO</span></h1>
  <div class="panel">${modes}<div class="rules">${RULES[S.mode]}</div>
  <b>Players</b><ul class="lobby">${list}</ul>${startBtn}
  ${S.players.length<2?'<p class="muted" style="text-align:center">Need at least 2 players.</p>':''}</div>
  <div class="panel"><div class="rename"><input id="newname" maxlength="16" placeholder="Change your name" value="${esc(S.you.name)}" onkeydown="if(event.key==='Enter')rename()"><button onclick="rename()">Save</button></div></div>
  <div class="footer"><button class="ghost" onclick="leave()">Leave</button></div>`;
}

function chips(){
  return `<div class="players">${S.players.map(p => `<div class="chip ${p.turn?'turn':''} ${p.online?'':'off'} ${p.out?'out':''}">
    ${p.out?'💀':''}${p.host?'👑':''}${esc(p.name)}${p.you?' (you)':''} <b>${p.count}</b>
    ${p.uno?'<span class="tag">UNO</span>':''}
    ${p.vulnerable && !p.you ? `<button onclick='api("catch",{target:${esc(JSON.stringify(p.name))}})'>Catch!</button>`:''}
  </div>`).join('')}</div>`;
}

function renderGame(){
  const me = S.you;
  const hand = me.hand.slice().sort((a,b)=> (a.color+a.value).localeCompare(b.color+b.value));
  const handHTML = hand.map(c => cardHTML(c, {click:true, playable:S.playable.includes(c.id), dim:S.myTurn && !S.playable.includes(c.id)})).join('');
  const canUno = !me.uno && !me.out && me.hand.length <= 2;
  let status;
  if(me.out) status = `💀 You're out (${S.mercyLimit}+ cards). Watching…`;
  else if(!S.myTurn) status = `${esc(S.turnName)}'s turn` + (S.pending ? ` <span class="pending">(+${S.pending} incoming)</span>` : '');
  else if(S.roulette) status = '🎲 Roulette! Pick a color';
  else if(S.pending) status = `<span class="pending">+${S.pending} on you!</span> Stack a +${S.pendingMin}+ or take it`;
  else if(S.drawnId!=null) status = 'You drew a playable card — play it or pass';
  else status = 'Your turn!';
  const canDraw = S.myTurn && S.drawnId==null && !S.pending && !S.roulette;
  const mercyWarn = S.mode==='nomercy' && !me.out && me.hand.length >= S.mercyLimit-5 ? `<div class="muted" style="text-align:center;color:#ff8a80">⚠ ${me.hand.length}/${S.mercyLimit} cards</div>` : '';
  return `<div style="text-align:center">${modeBadge()}</div>${chips()}
  <div class="table">
    <div class="card back" onclick="${canDraw ? "api('draw')" : ''}" title="Draw"><span class="mid">UNO</span></div>
    ${S.top ? cardHTML(S.top, {big:true}) : ''}
    <div class="colorbox"><div class="dot ${S.color}"></div><div>${S.direction===1?'↻':'↺'}</div><div class="muted">${S.deckCount} left</div></div>
  </div>
  <div class="status ${S.myTurn?'mine':''}">${status}</div>
  <div class="log">${S.log.slice(-3).map(esc).join('<br>')}</div>
  <div class="actions">
    ${canDraw ? `<button onclick="api('draw')">${S.mode==='nomercy'?'Draw until playable':'Draw card'}</button>`:''}
    ${S.myTurn && S.drawnId!=null ? `<button class="warn" onclick="api('pass')">Pass</button>`:''}
    ${S.myTurn && S.pending ? `<button class="warn" onclick="api('take')">Take ${S.pending} cards</button>`:''}
    ${S.myTurn && S.roulette ? `<button class="warn" onclick="showPicker('spin','Roulette! Pick a color — you flip until you hit it')">Spin roulette 🎲</button>`:''}
    ${canUno ? `<button class="uno" onclick="api('uno')">UNO!</button>`:''}
  </div>
  ${mercyWarn}
  <div class="hand">${handHTML}</div>
  <div class="footer">${me.isHost?`<button class="ghost" onclick="if(confirm('End this game for everyone?'))api('lobby')">End game</button>`:''}<button class="ghost" onclick="leave()">Leave</button></div>`;
}

function renderOver(){
  const me = S.you;
  const board = S.players.slice().sort((a,b)=>b.wins-a.wins).map(p=>`<li>${p.out?'💀 ':''}${esc(p.name)} — 🏆 ${p.wins} <span class="muted">(${p.count} cards left)</span></li>`).join('');
  return `<div style="text-align:center">${modeBadge()}</div>${chips()}
  <div class="winner">🎉 ${esc(S.winner)} wins! 🎉</div>
  <div class="panel"><b>Scoreboard</b><ul class="lobby">${board}</ul>
  ${me.isHost ? `<button class="big" ${S.players.length<2?'disabled':''} onclick="api('start')">Play again</button>
    <div style="height:8px"></div><button class="big ghost" onclick="api('lobby')">Back to lobby (change mode)</button>`
    : '<p class="muted" style="text-align:center">Waiting for the host…</p>'}</div>
  <div class="log">${S.log.slice(-3).map(esc).join('<br>')}</div>
  <div class="footer"><button class="ghost" onclick="leave()">Leave</button></div>`;
}

function render(){
  const app = $('#app');
  if(!token || !S){ if(!$('#name')) app.innerHTML = renderJoin(); return; }
  const focused = document.activeElement && document.activeElement.id === 'newname';
  if(focused && S.phase === 'lobby') return;  // don't wipe the rename box while typing
  if(S.myTurn && !wasMyTurn){ navigator.vibrate && navigator.vibrate(150); document.title='▶ Your turn - UNO'; }
  if(!S.myTurn) document.title='LAN UNO';
  if(S.myTurn && S.roulette && !wasMyTurn) showPicker('spin', 'Roulette! Pick a color — you flip until you hit it');
  if(!S.myTurn || !S.roulette){ if(pickMode==='spin') $('#picker').classList.add('hidden'); }
  wasMyTurn = S.myTurn;
  app.innerHTML = S.phase==='lobby' ? renderLobby() : S.phase==='playing' ? renderGame() : renderOver();
}

if(token) connect();
render();
</script>
</body></html>
"""


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get("PORT", 8000))  # PORT is set by cloud hosts
    server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    server.daemon_threads = True
    ip = lan_ip()
    print("\n  LAN UNO is running!")
    print("  On this computer : http://localhost:%d" % port)
    print("  Other devices    : http://%s:%d   (same Wi-Fi)" % (ip, port))
    print("\n  Press Ctrl+C to stop.\n", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nBye!")


if __name__ == "__main__":
    main()
