# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

SAYCBridge is a Python library for automatically bidding bridge hands using Standard American Yellow Card (SAYC) conventions. The master branch uses the Z3 Bidder (z3b) built on Microsoft Research's Z3 theorem prover. The production site (saycbridge.com) runs the legacy Knowledge Based Bidder (KBB) from the `kbb` branch.

**Status:** Not actively maintained. The Z3 bidder has a known memory leak that would need to be fixed for production use.

## Build & Development Commands

### Setup
```bash
# Use virtualenv
python3 -m venv sayc-env
source sayc-env/bin/activate

# Install dependencies (from src/ directory)
cd src && poetry install
```

### Testing
```bash
# Run full test suite
scripts/test-sayc

# Check changes against baseline
scripts/test-sayc -f > src/z3b_actual.txt && diff -U 7 src/z3b_baseline.txt src/z3b_actual.txt

# Accept new baseline (after validating changes are correct)
mv src/z3b_actual.txt src/z3b_baseline.txt

# Test individual hand: scripts/test-hand [EXPECTED_CALL] HAND_STRING [HISTORY_STRING]
scripts/test-hand "2C" "KQ4.AQ8.K9873.K2" "1N P"

# Explain bidder's reasoning for a sequence
scripts/explain "1S X P"

# Performance profiling
scripts/test-sayc -p

# Single-process mode (useful for debugging)
scripts/test-sayc -s
```

### Interactive Development
```bash
# Command-line interactive bidder
scripts/saycbot.py

# Auto-bid all hands (for crash testing)
scripts/saycbot.py -a
```

## Architecture

### Core Data Types (`src/core/`)
- `Call` - A bid (level 1-7 + strain CDHSN) or Pass
- `Hand` - 13 cards organized by suit
- `CallHistory` - Sequence of calls with vulnerability/dealer info
- `Deal` - 4 hands for 4 positions (N/E/S/W)
- `Board` - Global state: Deal + CallHistory + board number

### Z3 Bidder (`src/z3b/`)
The Z3 bidder uses constraint satisfaction to model bridge bidding:

- `bidder.py` - Main bidder class using Z3 solver
- `rules.py` - SAYC bidding conventions (~11K lines of rule definitions)
- `model.py` - Z3 constraint model (suit counts, HCP, honors, etc.)
- `constraints.py` - Complex Z3 constraint objects
- `orderings.py` - Partial ordering for bid priority comparison

**Three-tier priority system:**
1. **Category** - Segregates bid types (e.g., "Unusual 2N" vs natural 2N)
2. **Priority** - Compares possible bids over a given history
3. **Tie-breaking** - Uses actual hand to decide between equal-priority bids

### Hand String Format
Hands use dot-separated suit notation: `Clubs.Diamonds.Hearts.Spades`
Example: `KQ4.AQ8.K9873.K2` = ♣KQ4, ♦AQ8, ♥K9873, ♠K2

Bidding history: space-separated calls like `1S X P 2C`

### Key Files for Development
- `src/z3b/rules.py` - Add new bidding rules here
- `src/z3b_baseline.txt` - Test expectations (~30K lines)
- `src/tests/test_sayc.py` - Test case definitions

## Development Workflow

1. Make changes to bidding rules in `src/z3b/`
2. Run tests and compare against baseline
3. Use `scripts/test-hand` and `scripts/explain` to debug unexpected behavior
4. Once changes are validated, update baseline and commit

## Dependencies

- Python 3.10+
- z3-solver ^4.8.17 (Microsoft Research Z3 theorem prover)
- networkx ^2.8.3
