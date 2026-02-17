# CLAUDE.md

Minimal checkout of the SAYCBridge z3b bidding engine, used as a reference by yarborough.

## Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install z3-solver==4.12.6.0 networkx
```

## Usage

```bash
# Auto-bid a deal (outputs JSON to stdout)
python z3b_cli.py autobid --dealer N --vulnerability None \
  --north "AK.J.T8753.JT432" --east "Q.KT9876.QJ.AK98" \
  --south "JT9876.A5432.6.7" --west "5432.Q.AK942.Q65"

# Interpret a bidding sequence (outputs JSON to stdout)
python z3b_cli.py interpret --calls "1H,P,2H,P" --dealer N --vulnerability None
```

## Architecture

### Core Data Types (`src/core/`)
- `Call` — A bid (level 1-7 + strain CDHSN) or Pass
- `Hand` — 13 cards organized by suit
- `CallHistory` — Sequence of calls with vulnerability/dealer info
- `Deal` — 4 hands for 4 positions (N/E/S/W)

### Z3 Bidder (`src/z3b/`)
Uses constraint satisfaction (Z3 theorem prover) to model bridge bidding:
- `bidder.py` — Main bidder class
- `rules.py` — SAYC bidding conventions (~11K lines)
- `model.py` — Z3 constraint model (suit counts, HCP, honors)
- `constraints.py` — Complex Z3 constraint objects

### Hand String Format
Hands use dot-separated suit notation: `Clubs.Diamonds.Hearts.Spades`
Example: `KQ4.AQ8.K9873.K2` = clubs KQ4, diamonds AQ8, hearts K9873, spades K2
