// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'dart:async';

import 'package:flutter/material.dart';

import 'interpreter.dart';
import 'model.dart';

class CallMenuItem extends StatelessComponent {
  CallMenuItem({
    Key key,
    this.interpretation,
    this.backgroundColor
  }) : super(key: key);

  final CallInterpretation interpretation;
  final Color backgroundColor;

  bool get _hasInterpretation => interpretation.hasInterpretation;

  Widget _getDescription(BuildContext context) {
    return new Column([
      new Text(interpretation.ruleName, style: const TextStyle(fontWeight: FontWeight.bold)),
      new Text(interpretation.knowledge),
    ], justifyContent: FlexJustifyContent.center, alignItems: FlexAlignItems.start);
  }

  Widget build(BuildContext context) {
    return new ListItem(
      left: new CircleAvatar(
        label: interpretation.call.toString()
      ),
      center: _hasInterpretation ? _getDescription(context) : new Text('Unknown')
    );
  }
}

class CallMenu extends StatefulComponent {
  CallMenu({
    Key key,
    this.callHistory
  }) : super(key: key);

  final List<Call> callHistory;

  _CallMenuState createState() => new _CallMenuState();
}

class _CallMenuState extends State<CallMenu> {
  void initState() {
    super.initState();
    _fetchInterpretations();
  }

  List<CallInterpretation> _interpretations;

  Future _fetchInterpretations() async {
    _interpretations = await getInterpretations(config.callHistory);
    setState(() { });
  }

  Widget build(BuildContext context) {
    if (_interpretations == null) {
      return new Center(
        child: new Text('Loading...')
      );
    }
    return new MaterialList<CallInterpretation>(
      items: _interpretations,
      itemBuilder: (BuildContext context, CallInterpretation item, int index) {
        return new CallMenuItem(
          key: new ObjectKey(item),
          interpretation: item,
          backgroundColor: index % 2 == 0 ? Colors.amber[200] : Colors.green[200]
        );
      }
    );
  }
}

class FlutterDemo extends StatelessComponent {
  Widget build(BuildContext context) {
    return new Scaffold(
      toolBar: new ToolBar(
        center: new Text("SAYC Explorer")
      ),
      body: new Material(
        child: new CallMenu(
          callHistory: []
        )
      )
    );
  }
}

void main() {
  runApp(
    new MaterialApp(
      title: "Flutter Demo",
      routes: {
        '/': (RouteArguments args) => new FlutterDemo()
      }
    )
  );
}
