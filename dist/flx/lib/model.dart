// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

enum Strain {
  clubs,
  diamonds,
  hearts,
  spades,
  notrump
}

String getStringForStrain(Strain strain) {
  return const {
    Strain.clubs: 'C',
    Strain.diamonds: 'D',
    Strain.hearts: 'H',
    Strain.spades: 'S',
    Strain.notrump: 'N',
  }[strain];
}

Strain getStrainFromString(String name) {
  if (name == 'C')
    return Strain.clubs;
  if (name == 'D')
    return Strain.diamonds;
  if (name == 'H')
    return Strain.hearts;
  if (name == 'S')
    return Strain.spades;
  if (name == 'N')
    return Strain.notrump;
  return null;
}

final int _runeC = 'C'.codeUnitAt(0);
final int _runeD = 'D'.codeUnitAt(0);
final int _runeH = 'H'.codeUnitAt(0);
final int _runeS = 'S'.codeUnitAt(0);

Strain getStrainFromRune(int rune) {
  if (rune == _runeC)
    return Strain.clubs;
  if (rune == _runeD)
    return Strain.diamonds;
  if (rune == _runeH)
    return Strain.hearts;
  if (rune == _runeS)
    return Strain.spades;
  if (rune == 'N')
    return Strain.notrump;
  return null;
}

String getSymbolForStrain(Strain strain) {
  return const {
    Strain.clubs: '\u2663',
    Strain.diamonds: '\u2666',
    Strain.hearts: '\u2665',
    Strain.spades: '\u2660',
    Strain.notrump: 'NT',
  }[strain];
}

enum SpecialCall {
  pass,
  double,
  redouble
}

String getStringSpecialCall(SpecialCall specialCall) {
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

  const Call.special(this.specialCall) : level = null, strain = null;

  factory Call.fromName(String callName) {
    if (callName == 'P')
      return pass;
    if (callName == 'X')
      return x;
    if (callName == 'XX')
      return xx;
    return new Call(int.parse(callName[0]), getStrainFromString(callName[1]));
  }

  final int level;
  final Strain strain;
  final SpecialCall specialCall;

  bool get isContract => specialCall == null;

  bool get isPass => specialCall == SpecialCall.pass;
  bool get isDouble => specialCall == SpecialCall.double;
  bool get isRedouble => specialCall == SpecialCall.redouble;

  static const Call pass = const Call.special(SpecialCall.pass);
  static const Call x = const Call.special(SpecialCall.double);
  static const Call xx = const Call.special(SpecialCall.redouble);

  String toString() {
    if (isContract)
      return '$level${getStringForStrain(strain)}';
    return getStringSpecialCall(specialCall);
  }
}

enum Positions {
  west,
  north,
  east,
  south
}

class CallHistory {
  CallHistory({
    this.calls: const [],
    this.dealer: Positions.north
  });

  final List<Call> calls;
  final Positions dealer;

  CallHistory extendWithCall(Call call) {
    return new CallHistory(
      calls: new List<Call>.from(calls)..add(call),
      dealer: dealer
    );
  }

  bool get isComplete {
    if (calls.length < 4)
      return false;
    for (int i = calls.length - 4; i < calls.length; ++i) {
      if (!calls[i].isPass)
        return false;
    }
    return true;
  }

  int get lastNonPassIndex {
    for (int i = calls.length - 1; i >= 0; --i) {
      if (!calls[i].isPass)
        return i;
    }
    return null;
  }

  Positions getPositionForIndex(int index) {
    return Positions.values[
      (dealer.index + index) % Positions.values.length
    ];
  }

  Call get lastContract {
    for (Call call in calls.reversed) {
      if (call.isContract)
        return call;
    }
    return null;
  }

  Iterable<Call> get possibleCalls sync* {
    if (isComplete)
      return;

    yield Call.pass;

    int lastNonPassIndex = this.lastNonPassIndex;
    if (lastNonPassIndex == calls.length - 1 || lastNonPassIndex == calls.length - 3) {
      Call lastNonPass = calls[lastNonPassIndex];
      if (lastNonPass.isContract)
        yield Call.x;
      else if (lastNonPass.isDouble)
        yield Call.xx;
    }

    Call lastContract = this.lastContract;
    for (int level = 1; level < 8; ++level) {
      if (lastContract != null && level < lastContract.level)
        continue;
      for (Strain strain in Strain.values) {
        if (lastContract != null && level == lastContract.level && level <= lastContract.level)
          continue;
        yield new Call(level, strain);
      }
    }
  }
}

class CallInterpretation {
  const CallInterpretation({
    this.ruleName,
    this.knowledge,
    this.call,
    this.isTentative: false
  });

  final String ruleName;
  final String knowledge;
  final Call call;
  final bool isTentative;

  bool get hasInterpretation => ruleName != null && knowledge != null;
}
