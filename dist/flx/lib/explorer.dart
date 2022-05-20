// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'dart:async';

import 'package:flutter/material.dart';

import 'interpreter.dart';
import 'model.dart';

const SizedBox _kPlaceholder = SizedBox(width: 0.0, height: 0.0);

class PositionLabel extends StatelessWidget {
  const PositionLabel({super.key, required this.label});
  final String label;

  @override
  Widget build(BuildContext context) {
    return Center(
      child: Text(
        label,
        style: const TextStyle(fontWeight: FontWeight.bold),
      ),
    );
  }
}

Color getColorForStrain(Strain strain) {
  return const {
    Strain.clubs: Color(0xFF191970),
    Strain.diamonds: Color(0xFFFF4200),
    Strain.hearts: Color(0xFFFF0000),
    Strain.spades: Colors.black,
    Strain.notrump: Colors.black,
  }[strain]!;
}

TextStyle getTextStyleForStrain(Strain strain, TextStyle defaultStyle) {
  return defaultStyle.merge(TextStyle(color: getColorForStrain(strain)));
}

TextSpan getTextSpanForStrain(Strain strain, TextStyle defaultStyle) {
  return TextSpan(
    text: getSymbolForStrain(strain),
    style: getTextStyleForStrain(strain, defaultStyle),
  );
}

TextSpan getTextSpanForCall(Call call, TextStyle defaultStyle) {
  if (call.isContract) {
    return TextSpan(
      style: defaultStyle,
      text: call.level.toString(),
      children: <TextSpan>[
        getTextSpanForStrain(call.strain!, defaultStyle),
      ],
    );
  }
  return TextSpan(style: defaultStyle, text: call.toString());
}

class KnowledgeText extends StatelessWidget {
  const KnowledgeText({super.key, required this.knowledge});

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
      children.add(TextSpan(text: String.fromCharCodes(buffer)));
      buffer = <int>[];
    }

    for (int rune in knowledge.runes) {
      Strain? strain = getStrainFromRune(rune);
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

    return TextSpan(style: defaultStyle, children: children);
  }

  @override
  Widget build(BuildContext context) {
    return RichText(text: _getTextSpan(DefaultTextStyle.of(context).style));
  }
}

class CallTable extends StatelessWidget {
  const CallTable({super.key, required this.callHistory});

  final CallHistory callHistory;

  @override
  Widget build(BuildContext context) {
    List<Widget> children = <Widget>[
      const PositionLabel(label: 'West'),
      const PositionLabel(label: 'North'),
      const PositionLabel(label: 'East'),
      const PositionLabel(label: 'South')
    ];

    for (int i = 0; i < callHistory.dealer.index; ++i) {
      children.add(_kPlaceholder);
    }

    for (Call call in callHistory.calls) {
      children.add(Center(child: CallText(call: call)));
    }
    if (!callHistory.isComplete) children.add(const Center(child: Text('?')));

    return Container(
      padding: const EdgeInsets.all(16.0),
      decoration: BoxDecoration(color: Colors.grey[200]),
      child: GridView.count(
        shrinkWrap: true,
        crossAxisCount: 4,
        childAspectRatio: 3.0,
        children: children,
      ),
    );
  }
}

class CallText extends StatelessWidget {
  const CallText({super.key, required this.call});

  final Call call;

  @override
  Widget build(BuildContext context) {
    return RichText(
      text: getTextSpanForCall(call, DefaultTextStyle.of(context).style),
    );
  }
}

class CallAvatar extends StatelessWidget {
  const CallAvatar({super.key, required this.call});

  final Call call;

  @override
  Widget build(BuildContext context) {
    return Container(
      width: 40.0,
      height: 40.0,
      decoration: BoxDecoration(
        shape: BoxShape.circle,
        color: Colors.grey[200],
      ),
      child: Center(
        child: CallText(call: call),
      ),
    );
  }
}

class CallMenuItem extends StatelessWidget {
  const CallMenuItem(
      {super.key, required this.interpretation, required this.onCall});

  final ValueChanged<Call> onCall;
  final CallInterpretation interpretation;

  static const Text _kLoading = Text(
    '...',
    style: TextStyle(color: Colors.black26),
  );
  static const Text _kUnknown = Text(
    'Unknown',
    style: TextStyle(color: Colors.black26),
  );

  Widget get _description {
    if (interpretation.hasInterpretation) {
      return Column(
        mainAxisAlignment: MainAxisAlignment.center,
        crossAxisAlignment: CrossAxisAlignment.start,
        children: <Widget>[
          Text(
            displayRuleName(interpretation.ruleName!),
            style: const TextStyle(fontWeight: FontWeight.bold),
          ),
          KnowledgeText(knowledge: interpretation.knowledge!),
        ],
      );
    }
    if (interpretation.isTentative) return _kLoading;
    return _kUnknown;
  }

  void _handleTap() {
    onCall(interpretation.call);
  }

  @override
  Widget build(BuildContext context) {
    return ListTile(
      leading: CallAvatar(call: interpretation.call),
      title: _description,
      onTap: _handleTap,
    );
  }
}

class CallMenu extends StatefulWidget {
  const CallMenu({super.key, required this.callHistory, required this.onCall});

  final CallHistory callHistory;
  final ValueChanged<Call> onCall;

  @override
  _CallMenuState createState() => _CallMenuState();
}

class _CallMenuState extends State<CallMenu> {
  @override
  void initState() {
    super.initState();
    _updateInterpretations();
  }

  @override
  void didUpdateWidget(CallMenu oldWidget) {
    if (widget.callHistory != oldWidget.callHistory) _updateInterpretations();
    super.didUpdateWidget(oldWidget);
  }

  late List<CallInterpretation> _interpretations;
  int _currentFetchNumber = 0;

  void _updateInterpretations() {
    _interpretations = widget.callHistory.possibleCalls.map((Call call) {
      return CallInterpretation(call: call, isTentative: true);
    }).toList(growable: false);
    _fetchInterpretations();
  }

  Future _fetchInterpretations() async {
    int fetchNumber = ++_currentFetchNumber;
    List<CallInterpretation> interpretations =
        await getInterpretations(widget.callHistory);
    if (fetchNumber != _currentFetchNumber) return;
    setState(() {
      _interpretations = interpretations;
    });
  }

  @override
  Widget build(BuildContext context) {
    List<Widget> children = <Widget>[];

    children.add(
      ListView(
        key: ObjectKey(widget.callHistory),
        children: _interpretations.map((CallInterpretation interpretation) {
          return CallMenuItem(
            key: ObjectKey(interpretation),
            interpretation: interpretation,
            onCall: widget.onCall,
          );
        }).toList(),
      ),
    );

    if (_interpretations.isNotEmpty && _interpretations[0].isTentative) {
      children.add(const Center(child: CircularProgressIndicator()));
    }

    return Stack(children: children);
  }
}

class BidExplorer extends StatefulWidget {
  const BidExplorer({super.key});

  @override
  _BidExplorerState createState() => _BidExplorerState();
}

class _BidExplorerState extends State<BidExplorer> {
  @override
  void initState() {
    super.initState();
    _callHistory = CallHistory();
  }

  final GlobalKey<ScaffoldState> _scaffoldKey = GlobalKey<ScaffoldState>();
  late CallHistory _callHistory;

  void _handleCall(Call call) {
    _setCallHistory(_callHistory.extendWithCall(call));
  }

  void _clearHistory() {
    _setCallHistory(CallHistory());
    ScaffoldMessenger.of(context).showSnackBar(
      SnackBar(
        content: const Text('Call history cleared.'),
        action: SnackBarAction(
          label: 'UNDO',
          onPressed: () {
            Navigator.pop(context);
          },
        ),
      ),
    );
  }

  void _setCallHistory(CallHistory callHistory) {
    CallHistory oldCallHistory = _callHistory;
    ModalRoute.of(context)!.addLocalHistoryEntry(
      LocalHistoryEntry(onRemove: () {
        setState(() {
          _callHistory = oldCallHistory;
        });
      }),
    );
    setState(() {
      _callHistory = callHistory;
    });
  }

  Widget? get _clearButton {
    if (_callHistory.calls.isEmpty) return null;
    return FloatingActionButton(
      onPressed: _clearHistory,
      child: const Icon(Icons.close),
    );
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      key: _scaffoldKey,
      appBar: AppBar(
        title: const Text('Bid Explorer'),
      ),
      body: Material(
        child: Column(
          children: <Widget>[
            CallTable(callHistory: _callHistory),
            Flexible(
                child:
                    CallMenu(callHistory: _callHistory, onCall: _handleCall)),
          ],
        ),
      ),
      floatingActionButton: _clearButton,
    );
  }
}
