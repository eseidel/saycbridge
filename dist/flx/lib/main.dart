// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'dart:async';

import 'package:flutter/material.dart';

import 'interpreter.dart';
import 'model.dart';

final Container _kPlaceholder = new Container(width: 0.0, height: 0.0);

class PositionLabel extends StatelessWidget {
  PositionLabel({
    Key key,
    this.label,
  })
      : super(key: key);

  final String label;

  Widget build(BuildContext context) {
    return new Center(
      child: new Text(
        label,
        style: const TextStyle(fontWeight: FontWeight.bold),
      ),
    );
  }
}

Color getColorForStrain(Strain strain) {
  return const {
    Strain.clubs: const Color(0xFF191970),
    Strain.diamonds: const Color(0xFFFF4200),
    Strain.hearts: const Color(0xFFFF0000),
    Strain.spades: Colors.black,
    Strain.notrump: Colors.black,
  }[strain];
}

TextStyle getTextStyleForStrain(Strain strain, TextStyle defaultStyle) {
  return defaultStyle.merge(new TextStyle(color: getColorForStrain(strain)));
}

TextSpan getTextSpanForStrain(Strain strain, TextStyle defaultStyle) {
  return new TextSpan(
    text: getSymbolForStrain(strain),
    style: getTextStyleForStrain(strain, defaultStyle),
  );
}

TextSpan getTextSpanForCall(Call call, TextStyle defaultStyle) {
  if (call.isContract) {
    return new TextSpan(
      style: defaultStyle,
      text: call.level.toString(),
      children: <TextSpan>[
        getTextSpanForStrain(call.strain, defaultStyle),
      ],
    );
  }
  return new TextSpan(style: defaultStyle, text: call.toString());
}

class KnowledgeText extends StatelessWidget {
  KnowledgeText({Key key, this.knowledge}) : super(key: key);

  final String knowledge;

  // FIXME: This is a horrible hack for the explorer page which uses "4rS" and expects the "S" not to be replaced.
  bool _isReplacementPoint(int rune) {
    // ASCII 0-9
    if (rune >= 0x30 && rune <= 0x39) return true;
    // ASCII + and -
    if (rune == 0x2B || rune == 0x2D) return true;
    return false;
  }

  TextSpan _getTextSpan(TextStyle defaultStyle) {
    List<TextSpan> children = <TextSpan>[];
    List<int> buffer = <int>[];

    void flushBuffer() {
      children.add(new TextSpan(text: new String.fromCharCodes(buffer)));
      buffer = <int>[];
    }

    for (int rune in knowledge.runes) {
      Strain strain = getStrainFromRune(rune);
      if (strain != null &&
          buffer.isNotEmpty &&
          _isReplacementPoint(buffer.last)) {
        flushBuffer();
        children.add(getTextSpanForStrain(strain, defaultStyle));
      } else {
        buffer.add(rune);
      }
    }

    flushBuffer();

    return new TextSpan(style: defaultStyle, children: children);
  }

  Widget build(BuildContext context) {
    return new RichText(text: _getTextSpan(DefaultTextStyle.of(context).style));
  }
}

class CallTable extends StatelessWidget {
  CallTable({Key key, this.callHistory}) : super(key: key);

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
      children.add(new Center(child: new CallText(call: call)));

    if (!callHistory.isComplete) children.add(new Center(child: new Text('?')));

    return new Container(
      padding: const EdgeInsets.all(16.0),
      decoration: new BoxDecoration(backgroundColor: Colors.grey[200]),
      child: new GridView.count(
        crossAxisCount: 4,
        childAspectRatio: 3.0,
        children: children,
      ),
    );
  }
}

class CallText extends StatelessWidget {
  CallText({Key key, this.call}) : super(key: key);

  final Call call;

  Widget build(BuildContext context) {
    return new RichText(
      text: getTextSpanForCall(call, DefaultTextStyle.of(context).style),
    );
  }
}

class CallAvatar extends StatelessWidget {
  CallAvatar({Key key, this.call}) : super(key: key);

  final Call call;

  Widget build(BuildContext context) {
    return new Container(
      width: 40.0,
      height: 40.0,
      decoration: new BoxDecoration(
        shape: BoxShape.circle,
        backgroundColor: Colors.grey[200],
      ),
      child: new Center(
        child: new CallText(call: call),
      ),
    );
  }
}

class CallMenuItem extends StatelessWidget {
  CallMenuItem({Key key, this.interpretation, this.onCall}) : super(key: key);

  final ValueChanged<Call> onCall;
  final CallInterpretation interpretation;

  static final Text _kLoading = new Text(
    '...',
    style: new TextStyle(color: Colors.black26),
  );
  static final Text _kUnknown = new Text(
    'Unknown',
    style: new TextStyle(color: Colors.black26),
  );

  Widget get _description {
    if (interpretation.hasInterpretation) {
      return new ListView(
        scrollDirection: Axis.horizontal,
        children: <Widget>[
          new Column(
            mainAxisAlignment: MainAxisAlignment.center,
            crossAxisAlignment: CrossAxisAlignment.start,
            children: <Widget>[
              new Text(
                displayRuleName(interpretation.ruleName),
                style: const TextStyle(fontWeight: FontWeight.bold),
              ),
              new KnowledgeText(knowledge: interpretation.knowledge),
            ],
          )
        ],
      );
    }
    if (interpretation.isTentative) return _kLoading;
    return _kUnknown;
  }

  void _handleTap() {
    onCall(interpretation.call);
  }

  Widget build(BuildContext context) {
    return new ListTile(
      leading: new CallAvatar(call: interpretation.call),
      title: _description,
      onTap: _handleTap,
    );
  }
}

class CallMenu extends StatefulWidget {
  CallMenu({Key key, this.callHistory, this.onCall}) : super(key: key);

  final CallHistory callHistory;
  final ValueChanged<Call> onCall;

  _CallMenuState createState() => new _CallMenuState();
}

class _CallMenuState extends State<CallMenu> {
  void initState() {
    super.initState();
    _updateInterpretations();
  }

  void didUpdateConfig(CallMenu oldConfig) {
    if (config.callHistory != oldConfig.callHistory) _updateInterpretations();
  }

  List<CallInterpretation> _interpretations;
  int _currentFetchNumber = 0;

  void _updateInterpretations() {
    _interpretations = config.callHistory.possibleCalls.map((Call call) {
      return new CallInterpretation(call: call, isTentative: true);
    }).toList(growable: false);
    _fetchInterpretations();
  }

  Future _fetchInterpretations() async {
    int fetchNumber = ++_currentFetchNumber;
    List<CallInterpretation> interpretations =
        await getInterpretations(config.callHistory);
    if (fetchNumber != _currentFetchNumber) return;
    setState(() {
      _interpretations = interpretations;
    });
  }

  Widget build(BuildContext context) {
    List<Widget> children = <Widget>[];

    children.add(
      new ListView(
        key: new ObjectKey(config.callHistory),
        children: _interpretations.map((CallInterpretation interpretation) {
          return new CallMenuItem(
            key: new ObjectKey(interpretation),
            interpretation: interpretation,
            onCall: config.onCall,
          );
        }).toList(),
      ),
    );

    if (_interpretations.isNotEmpty && _interpretations[0].isTentative)
      children.add(new Center(child: new CircularProgressIndicator()));

    return new Stack(children: children);
  }
}

class BidExplorer extends StatefulWidget {
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
    _scaffoldKey.currentState.showSnackBar(
      new SnackBar(
        content: new Text('Call history cleared.'),
        action: new SnackBarAction(
          label: 'UNDO',
          onPressed: () {
            Navigator.pop(context);
          },
        ),
      ),
    );
  }

  void _setCallHistory(CallHistory newCallHistory) {
    CallHistory oldCallHistory = _callHistory;
    ModalRoute.of(context).addLocalHistoryEntry(
      new LocalHistoryEntry(onRemove: () {
        setState(() {
          _callHistory = oldCallHistory;
        });
      }),
    );
    setState(() {
      _callHistory = newCallHistory;
    });
  }

  Widget get _clearButton {
    if (_callHistory.calls.isEmpty) return null;
    return new FloatingActionButton(
      onPressed: _clearHistory,
      child: new Icon(Icons.close),
    );
  }

  Widget build(BuildContext context) {
    return new Scaffold(
      key: _scaffoldKey,
      appBar: new AppBar(
        leading: new IconButton(
          icon: new Icon(Icons.arrow_back),
          onPressed: () {
            Navigator.pop(context);
          },
        ),
        title: new Text('Bid Explorer'),
      ),
      body: new Material(
        child: new Column(
          children: <Widget>[
            new CallTable(callHistory: _callHistory),
            new Flexible(
                child: new CallMenu(
                    callHistory: _callHistory, onCall: _handleCall)),
          ],
        ),
      ),
      floatingActionButton: _clearButton,
    );
  }
}

void main() {
  runApp(new MaterialApp(
    title: 'Bid Explorer',
    routes: {'/': (BuildContext context) => new BidExplorer()},
  ));
}
