// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'package:test/test.dart';

import 'package:saycbridge/model.dart';

void main() {
  test('Deal', () {
    Deal deal = Deal.random();
    expect(deal, isNotNull);
    expect(deal.hands.length, 4);
    for (Hand hand in deal.hands) {
      expect(hand.cards.length, 13);
    }
  });
}
