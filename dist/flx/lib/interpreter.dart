// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'dart:async';
import 'dart:convert';

import 'package:flutter/http.dart' as http;

import 'model.dart';

String _getUrl({
  String callString: '',
  String dealer: 'N',
  String vulnerability: 'None'
}) {
  return 'https://sayc.abortz.net/json/interpret2?calls_string=${Uri.encodeQueryComponent(callString)}&dealer=${Uri.encodeQueryComponent(dealer)}&vulnerability=${Uri.encodeQueryComponent(vulnerability)}';
}

class CallInterpretation {
  String get callName => _data['call_name'];
  String get ruleName => _data['rule_name'];
  String get knowledge => _data['knowledge_string'];

  Call get call => new Call.fromName(callName);
  bool get hasInterpretation => ruleName != null && knowledge != null;

  CallInterpretation._(this._data);

  final Map<String, String> _data;
}

Future<List<CallInterpretation>> getInterpretations(CallHistory callHistory) async {
  String url = _getUrl(callString: callHistory.calls.join(','));
  List interpretations = JSON.decode(await http.read(url));

  return interpretations.map((item) {
    return new CallInterpretation._(item);
  }).toList();
}
