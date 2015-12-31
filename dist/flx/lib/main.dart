// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'dart:async';

import 'package:flutter/material.dart';

import 'interpreter.dart';
import 'model.dart';

final Container _kPlaceholder = new Container(width: 0.0, height: 0.0);

class FlexTable extends StatelessComponent {
  FlexTable({
    Key key,
    this.columnCount,
    this.children
  }) : super(key: key);

  final int columnCount;
  final List<Widget> children;

  Widget build(BuildContext context) {
    List<Widget> rows = <Widget>[];
    int rowCount = (children.length / columnCount).ceil();
    for (int rowIndex = 0; rowIndex < rowCount; ++rowIndex) {
      List<Widget> cols = <Widget>[];
      for (int colIndex = 0; colIndex < columnCount; ++colIndex) {
        int i = colIndex + rowIndex * columnCount;
        cols.add(new Flexible(
          child: i < children.length ? children[i] : _kPlaceholder
        ));
      }
      rows.add(new Row(cols));
    }
    return new Column(rows);
  }
}

class PositionLabel extends StatelessComponent {
  PositionLabel({
    Key key,
    this.label
  }) : super(key: key);

  final String label;

  Widget build(BuildContext context) {
    return new Center(
      child: new Text(label, style: const TextStyle(
        fontWeight: FontWeight.bold
      ))
    );
  }
}

class CallTable extends StatelessComponent {
  CallTable({
    Key key,
    this.callHistory
  }) : super(key: key);

  final CallHistory callHistory;

  Widget build(BuildContext context) {
    List<Widget> children = <Widget>[
      new PositionLabel(label: 'West'),
      new PositionLabel(label: 'North'),
      new PositionLabel(label: 'East'),
      new PositionLabel(label: 'South')
    ];

    for (int i = 0; i < callHistory.dealer.index; ++i)
      children.add(_kPlaceholder);

    for (Call call in callHistory.calls)
      children.add(new Center(child: new Text(call.toString())));

    children.add(new Center(child: new Text('?')));

    return new Container(
      padding: const EdgeDims.all(16.0),
      decoration: new BoxDecoration(
        backgroundColor: Colors.grey[200]
      ),
      child: new FlexTable(
        columnCount: 4,
        children: children
      )
    );
  }
}

class CallMenuItem extends StatelessComponent {
  CallMenuItem({
    Key key,
    this.interpretation,
    this.onCall
  }) : super(key: key);

  final ValueChanged<Call> onCall;
  final CallInterpretation interpretation;

  bool get _hasInterpretation => interpretation.hasInterpretation;

  Widget _getDescription(BuildContext context) {
    return new Column([
      new Text(interpretation.ruleName, style: const TextStyle(fontWeight: FontWeight.bold)),
      new Text(interpretation.knowledge),
    ], justifyContent: FlexJustifyContent.center, alignItems: FlexAlignItems.start);
  }

  void _handleTap() {
    onCall(interpretation.call);
  }

  static final Text _kUnknownCall = new Text('Unknown',
      style: new TextStyle(color: Colors.black26));

  Widget build(BuildContext context) {
    return new ListItem(
      left: new CircleAvatar(
        label: interpretation.call.toString()
      ),
      center: _hasInterpretation ? _getDescription(context) : _kUnknownCall,
      onTap: _handleTap
    );
  }
}

class CallMenu extends StatefulComponent {
  CallMenu({
    Key key,
    this.callHistory,
    this.onCall
  }) : super(key: key);

  final CallHistory callHistory;
  final ValueChanged<Call> onCall;

  _CallMenuState createState() => new _CallMenuState();
}

class _CallMenuState extends State<CallMenu> {
  void initState() {
    super.initState();
    _fetchInterpretations();
  }

  void didUpdateConfig(CallMenu oldConfig) {
    if (config.callHistory != oldConfig.callHistory) {
      _interpretations = null;
      _fetchInterpretations();
    }
  }

  List<CallInterpretation> _interpretations;
  int _currentFetchNumber = 0;

  Future _fetchInterpretations() async {
    int fetchNumber = ++_currentFetchNumber;
    List<CallInterpretation> interpretations =
        await getInterpretations(config.callHistory);
    if (fetchNumber != _currentFetchNumber)
      return;
    _interpretations = interpretations;
    setState(() { });
  }

  Widget build(BuildContext context) {
    List<Widget> children = <Widget>[];
    List<CallInterpretation> interpretations = _interpretations;

    if (interpretations == null) {
      interpretations = config.callHistory.possibleCalls.map((Call call) {
        return new CallInterpretation(call: call);
      }).toList();
    }

    children.add(new MaterialList<CallInterpretation>(
      key: new ObjectKey(config.callHistory),
      items: interpretations,
      itemBuilder: (BuildContext context, CallInterpretation item, int index) {
        return new CallMenuItem(
          key: new ObjectKey(item),
          interpretation: item,
          onCall: config.onCall
        );
      }
    ));

    if (_interpretations == null)
      children.add(new Center(child: new CircularProgressIndicator()));

    return new Stack(children);
  }
}

class BidExplorer extends StatefulComponent {
  _BidExplorerState createState() => new _BidExplorerState();
}

class _BidExplorerState extends State<BidExplorer> {
  void initState() {
    super.initState();
    _callHistory = new CallHistory();
  }

  final GlobalKey<ScaffoldState> _scaffoldKey = new GlobalKey<ScaffoldState>();
  CallHistory _callHistory;

  void _handleCall(Call call) {
    _setCallHistory(_callHistory.extendWithCall(call));
  }

  void _clearHistory() {
    _setCallHistory(new CallHistory());
    _scaffoldKey.currentState.showSnackBar(new SnackBar(
      content: new Text('Call history cleared.')
    ));
  }

  void _setCallHistory(CallHistory newCallHistory) {
    CallHistory oldCallHistory = _callHistory;
    ModalRoute.of(context).addLocalHistoryEntry(
      new LocalHistoryEntry(
        onRemove: () {
          setState(() {
            _callHistory = oldCallHistory;
          });
        }
      )
    );
    setState(() {
      _callHistory = newCallHistory;
    });
  }

  Widget build(BuildContext context) {
    return new Scaffold(
      key: _scaffoldKey,
      toolBar: new ToolBar(
        center: new Text('Bid Explorer')
      ),
      body: new Material(
        child: new Column([
          new CallTable(
            callHistory: _callHistory
          ),
          new Flexible(
            child: new CallMenu(
              callHistory: _callHistory,
              onCall: _handleCall
            )
          ),
        ])
      ),
      floatingActionButton: new FloatingActionButton(
        onPressed: _clearHistory,
        child: new Icon(
          icon: 'navigation/close'
        )
      )
    );
  }
}

void main() {
  runApp(
    new MaterialApp(
      title: 'Bid Explorer',
      routes: {
        '/': (RouteArguments args) => new BidExplorer()
      }
    )
  );
}
