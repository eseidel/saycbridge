// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

enum Strain { clubs, diamonds, hearts, spades, notrump }

String? getStringForStrain(Strain? strain) {
  return const {
    Strain.clubs: 'C',
    Strain.diamonds: 'D',
    Strain.hearts: 'H',
    Strain.spades: 'S',
    Strain.notrump: 'N',
  }[strain];
}

Strain? getStrainFromString(String name) {
  if (name == 'C') return Strain.clubs;
  if (name == 'D') return Strain.diamonds;
  if (name == 'H') return Strain.hearts;
  if (name == 'S') return Strain.spades;
  if (name == 'N') return Strain.notrump;
  return null;
}

final int _runeC = 'C'.codeUnitAt(0);
final int _runeD = 'D'.codeUnitAt(0);
final int _runeH = 'H'.codeUnitAt(0);
final int _runeS = 'S'.codeUnitAt(0);
final int _runeN = 'N'.codeUnitAt(0);

Strain? getStrainFromRune(int rune) {
  if (rune == _runeC) return Strain.clubs;
  if (rune == _runeD) return Strain.diamonds;
  if (rune == _runeH) return Strain.hearts;
  if (rune == _runeS) return Strain.spades;
  if (rune == _runeN) return Strain.notrump;
  return null;
}

String getSymbolForStrain(Strain? strain) {
  return const {
    Strain.clubs: '\u2663',
    Strain.diamonds: '\u2666',
    Strain.hearts: '\u2665',
    Strain.spades: '\u2660',
    Strain.notrump: 'NT',
  }[strain]!;
}

enum SpecialCall { pass, double, redouble }

String? getStringSpecialCall(SpecialCall? specialCall) {
  return const {
    SpecialCall.pass: 'P',
    SpecialCall.double: 'X',
    SpecialCall.redouble: 'XX',
  }[specialCall];
}

class Call {
  Call(this.level, this.strain) : specialCall = null {
    assert(level != null);
    assert(strain != null);
  }

  const Call.special(this.specialCall)
      : level = null,
        strain = null;

  factory Call.fromName(String callName) {
    if (callName == 'P') return pass;
    if (callName == 'X') return x;
    if (callName == 'XX') return xx;
    return Call(int.parse(callName[0]), getStrainFromString(callName[1]));
  }

  final int? level;
  final Strain? strain;
  final SpecialCall? specialCall;

  bool get isContract => specialCall == null;

  bool get isPass => specialCall == SpecialCall.pass;
  bool get isDouble => specialCall == SpecialCall.double;
  bool get isRedouble => specialCall == SpecialCall.redouble;

  static const Call pass = Call.special(SpecialCall.pass);
  static const Call x = Call.special(SpecialCall.double);
  static const Call xx = Call.special(SpecialCall.redouble);

  @override
  String toString() {
    if (isContract) return '$level${getStringForStrain(strain)}';
    return getStringSpecialCall(specialCall)!;
  }
}

class Position {
  final String name;
  const Position._(this.name);

  static const Position west = Position._("West");
  static const Position north = Position._("North");
  static const Position east = Position._("East");
  static const Position south = Position._("South");

  int get index => values.indexOf(this);

  // Order here has to match the "index" parameters below.
  static const List<Position> values = [west, north, east, south];
}

class CallHistory {
  CallHistory({this.calls = const [], this.dealer = Position.north});

  final List<Call> calls;
  final Position dealer;

  CallHistory extendWithCall(Call call) {
    return CallHistory(
      calls: List<Call>.from(calls)..add(call),
      dealer: dealer,
    );
  }

  bool get isComplete {
    if (calls.length < 4) return false;
    for (int i = calls.length - 3; i < calls.length; ++i) {
      if (!calls[i].isPass) return false;
    }
    return true;
  }

  int? get lastNonPassIndex {
    for (int i = calls.length - 1; i >= 0; --i) {
      if (!calls[i].isPass) return i;
    }
    return null;
  }

  Position getPositionForIndex(int index) {
    return Position.values[(dealer.index + index) % Position.values.length];
  }

  Call? get lastContract {
    for (Call call in calls.reversed) {
      if (call.isContract) return call;
    }
    return null;
  }

  Iterable<Call> get possibleCalls sync* {
    if (isComplete) return;

    yield Call.pass;

    int? lastNonPassIndex = this.lastNonPassIndex;
    if (lastNonPassIndex == calls.length - 1 ||
        lastNonPassIndex == calls.length - 3) {
      Call lastNonPass = calls[lastNonPassIndex!];
      if (lastNonPass.isContract) {
        yield Call.x;
      } else if (lastNonPass.isDouble) {
        yield Call.xx;
      }
    }

    Call? lastContract = this.lastContract;
    for (int level = 1; level < 8; ++level) {
      if (lastContract != null && level < lastContract.level!) continue;
      for (Strain strain in Strain.values) {
        if (lastContract != null &&
            level == lastContract.level &&
            strain.index <= lastContract.strain!.index) continue;
        yield Call(level, strain);
      }
    }
  }
}

String displayRuleName(String ruleName) {
  String displayName =
      ruleName.replaceAllMapped(RegExp(r'([1-9A-Z])'), (Match m) => ' ${m[1]}');
  // A couple exceptions to the spacing rules:
  displayName = displayName.replaceAll('R H O', 'RHO');
  displayName = displayName.replaceAll('L H O', 'LHO');
  displayName = displayName.replaceAll(RegExp(r'\sN$'), 'NT');
  return displayName.trim();
}

class CallInterpretation {
  const CallInterpretation({
    this.ruleName,
    this.knowledge,
    required this.call,
    this.isTentative = false,
  });

  final String? ruleName;
  final String? knowledge;
  final Call call;
  final bool isTentative;

  bool get hasInterpretation => ruleName != null && knowledge != null;
}

class Rank {
  final String name;

  const Rank(this.name);

  String get displayRank => name == 'T' ? '10' : name;

  int get index => '23456789TJQKA'.indexOf(name);

  int get highCardPoints =>
      {
        'A': 4,
        'K': 3,
        'Q': 2,
        'J': 1,
      }[name] ??
      0;
}

class Suit {
  final String name;

  const Suit._(this.name);

  factory Suit.fromChar(String name) {
    int index = 'CDHS'.indexOf(name);
    if (index == -1) throw ArgumentError('Unknown Suit $name');
    return all[index];
  }

  String get codePoint => {
        'C': '\u2663',
        'D': '\u2666',
        'H': '\u2665',
        'S': '\u2660',
      }[name]!;

  static const Suit clubs = Suit._('C');
  static const Suit diamonds = Suit._('D');
  static const Suit hearts = Suit._('H');
  static const Suit spades = Suit._('S');

  static const List<Suit> all = [clubs, diamonds, hearts, spades];
}

class Card {
  final Rank rank;
  final Suit suit;

  const Card(this.rank, this.suit);

  factory Card.fromIdentifier(int identifier) {
    final int suitIndex = identifier ~/ 13;
    final int cardIndex = identifier % 13;
    final String suitChar = 'CDHS'[suitIndex];
    final String rankChar = '23456789TJQKA'[cardIndex];
    return Card(Rank(rankChar), Suit.fromChar(suitChar));
  }

  int get identifier {
    int suitIndex = 'CDHS'.indexOf(suit.name);
    return suitIndex * 13 + rank.index;
  }

  static List<Card> allCards() =>
      List.generate(52, (index) => Card.fromIdentifier(index));
}

class Hand {
  List<Card> cards = [];

  Iterable<Card> matchingSuit(Suit suit) =>
      cards.where((card) => card.suit == suit);
}

class Deal {
  List<Hand> hands;

  Deal(this.hands) {
    _validate(hands);
  }

  Deal.empty() : hands = List.generate(4, (index) => Hand());

  void _validate(List<Hand> hands) {
    List<Card> allCards = hands.expand((hand) => hand.cards).toList();
    if (allCards.length != 52) {
      throw ArgumentError("Incorrect number of cards ${allCards.length}");
    }
    Set<Card> unique = Set.from(allCards);
    if (unique.length != 52) throw ArgumentError("Duplicate cards in deal");
  }

  Hand handFor(Position position) => hands[position.index];

  factory Deal.random() {
    Deal deal = Deal.empty();
    List<Card> shuffledCards = Card.allCards();
    shuffledCards.shuffle();
    int index = 0;
    for (Card card in shuffledCards) {
      deal.hands[index++ % 4].cards.add(card);
    }
    return deal;
  }
}
