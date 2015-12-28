# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import os
import re
import subprocess
from core.position import *
from core.suit import *
from core.call import Call

import tempfile


class Gib(object):
    _startwine_path = "/Applications/Wine.app/Contents/MacOS/startwine"
    _gib_path = "/Users/eseidel/Wine Files/drive_c/Program Files/GIB/BRIDGE.EXE"

    def __init__(self):
        self._process = None

    def _start_if_necessary(self):
        if self._process:
            return
        gib_directory = os.path.dirname(self._gib_path)
        gib_command = [self._startwine_path, self._gib_path, "-u"]  # -u for "ui mode"
        self._process = subprocess.Popen(gib_command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, cwd=gib_directory)
        # Ignore the first two lines printed from gib, they're just a version number and empty line.
        self._read_line()
        self._read_line()
        self._read_until_command_prompt()

    def _stop(self):
        self._exit_current_command()
        self._send_command("-q -x")

    def _strip_gib_header(self, gib_output):
        return "\n".join(gib_output.split('\n')[2:])

    def _run_gib(self, args=None, input_text=None):
        gib_directory = os.path.dirname(self._gib_path)
        gib_args = ['-q'] + args
        gib_command = [self._startwine_path, self._gib_path] + gib_args
        gib_output = subprocess.Popen(gib_command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, cwd=gib_directory).communicate(input_text)[0]
        return self._strip_gib_header(gib_output)

    def _write_line(self, text_input):
        self._process.stdin.write(text_input + "\n")

    def _read_line(self):
        buffered_output = ""
        while True:
            read_char = self._process.stdout.read(1)
            if read_char == "\n":
                return buffered_output
            buffered_output += read_char

    def _read_until_command_prompt(self):
        buffered_output = ""
        while True:
            read_char = self._process.stdout.read(1)
            buffered_output += read_char
            prompt = "Enter argument line: "
            if buffered_output.endswith(prompt):
                return buffered_output[:-len(prompt)]
            # if read_char == "\n":
            #     print buffered_output

    def _exit_current_command(self):
        self._write_line('q')

    def _send_command(self, command_text):
        self._write_line(command_text)

    def _double_dummy_command(self, board):
        input_text = "\n".join([position.char + " " + board.deal.hands[position].shdc_dot_string() for position in POSITIONS])
        if board.call_history.is_complete():
            leader = board.call_history.declarer().lho
            trump = board.call_history.last_contract().strain
        else:
            leader = NORTH
            trump = SPADES
        input_text += "\n%s %s\n" % (leader.char, trump.char)
        input_text += "dq"
        return input_text

    def _temp_file_with_contents(self, contents):
        temp = tempfile.NamedTemporaryFile()
        temp.write(contents)
        temp.seek(0)
        return temp

    def solve_double_dummy(self, board):
        self._start_if_necessary()
        # Gib seems confused when passed -d without a file, so we have to use a temp file to do double dummy results.
        with self._temp_file_with_contents(self._double_dummy_command(board)) as command_file:
            self._send_command('-d ' + command_file.name)
            # Double-dummy mode does not put a newline after the result, so we use
            # _read_until_command_prompt instead of _read_line here.
            return int(self._read_until_command_prompt())

    def _next_bid_command(self, hand, history):
        return "\n".join([
            hand.shdc_dot_string(),
            history.dealer.char,
            history.vulnerability.gib_name(),
            history.calls_string(),
        ])

    def find_call_for(self, hand, history):
        # Gib doesn't seem to have a way to let us "bid" for it (without using ! to back-up)
        # when passing it input over stdin, but when we use a file it lets us pass its previous bids just fine.
        with self._temp_file_with_contents(self._next_bid_command(hand, history)) as command_file:
            input_text = "\n"  # Causes gib to actually spit out the answer.
            input_text += "q\n-q -x" # Actually cause gib to quit.
            args = [command_file.name]
            args.append("-%s" % history.position_to_call().char)
            gib_output = self._run_gib(args, input_text)
            bid_name = re.search(r"I bid (\S{1,2})", gib_output).group(1)
            interpretation = re.search(r"^That bid shows: (.*)$", gib_output, re.MULTILINE).group(1)
            return Call(bid_name)

    # FIXME: This doesn't work yet.
    def find_play_for(self, hand, other_hand, call_history, played_cards_string):
        position = playHistory.next_to_play()
        # otherHand is normally the dummy, but can be the declarer's hand when considering what to play for the dummy.
        other_hand_position = playHistory.dummy() if position != play_history.dummy() else play_history.declarer()
        played_cards = played_cards_string.split(" ")
        git_input_lines = [
            hand.shdc_dot_string(),
            history.dealer.char,
            history.vulnerability.gib_name(),
            history.calls_string(),
        ]
        if played_cards:
            gib_input_lines.append(played_cards[0])
            gib_input_lines.append(dummy_hand)
            gib_input_lines.append(played_cards[1:].join(" "))
        next_play_command = "\n".join(git_input_lines)
        print next_play_command

        with self._temp_file_with_contents(next_play_command) as command_file:
            input_text = "\n"  # Causes gib to actually spit out the answer.
            input_text += "q\n-q -x" # Actually cause gib to quit.
            args = [command_file.name]
            args.append("-%s" % history.position_to_call().char)
            gib_output = self._run_gib(args, input_text)
            return gib_output

    # This should work, but doesn't.  The bids it produces are bogus.
    def new_find_call_for(self, hand, history):
        self._start_if_necessary()
        # Gib doesn't seem to understand to bid when we pass it -N,-S,-W or -E at the command prompt
        # so we're using -H (hand record) mode instead for our bid-finding.  Hand-record mode
        # requires all 4 hands, so we just pass the same hand 4 times. (it doesn't seem to care.)
        self._send_command("-H")  # We could pass -z here to always make the "book" bid, but that results in some crazy bids...
        for _ in range(4):
            self._write_line(hand.shdc_dot_string())
        self._write_line(history.dealer.char)
        self._write_line(history.vulnerability.gib_name())
        if history.calls:
            self._write_line(history.calls_string())
        self._write_line("*")  # Ask gib to suggest the next bid.
        self._exit_current_command()
        gib_output = self._read_until_command_prompt()
        bid_name = re.search(r"I hint bid (\S{1,2})", gib_output).group(1)
        return Call(bid_name)
