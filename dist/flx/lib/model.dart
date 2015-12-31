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
  const Call(this.level, this.strain) : specialCall = null;
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

  bool get isBid => specialCall == null;

  bool get isPass => specialCall == SpecialCall.pass;
  bool get isDouble => specialCall == SpecialCall.double;
  bool get isRedouble => specialCall == SpecialCall.redouble;

  static const Call pass = const Call.special(SpecialCall.pass);
  static const Call x = const Call.special(SpecialCall.double);
  static const Call xx = const Call.special(SpecialCall.redouble);

  String toString() {
    if (isBid)
      return '$level${getStringForStrain(strain)}';
    return getStringSpecialCall(specialCall);
  }
}
