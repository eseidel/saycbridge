// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'dart:async';
import 'dart:convert';

import 'package:http/http.dart' as http;

import 'model.dart';

String _getUrl({
  String callString = '',
  String dealer = 'N',
  String vulnerability = 'None',
}) {
  return 'https://sayc.abortz.net/json/interpret2?calls_string=${Uri.encodeQueryComponent(callString)}&dealer=${Uri.encodeQueryComponent(dealer)}&vulnerability=${Uri.encodeQueryComponent(vulnerability)}';
}

final Map<String, Future<List<CallInterpretation>>> _memoryCache = {};

Future<List<CallInterpretation>> getInterpretations(CallHistory callHistory) {
  String url = _getUrl(callString: callHistory.calls.join(','));
  return _memoryCache.putIfAbsent(url, () async {
    try {
      var uri = Uri.parse(url);
      return json.decode(await http.read(uri)).map<CallInterpretation>((item) {
        return CallInterpretation(
          ruleName: item['rule_name'],
          knowledge: item['knowledge_string'],
          call: Call.fromName(item['call_name']),
        );
      }).toList();
    } catch (e) {
      _memoryCache.remove(url);
      rethrow;
    }
  });
}
