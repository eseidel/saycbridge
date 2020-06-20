// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'package:flutter/material.dart';
import 'package:saycbridge/play.dart';
import 'package:saycbridge/explorer.dart';

class MainMenu extends StatelessWidget {
  Widget build(BuildContext context) {
    return Scaffold(
      body: Center(
        child: Row(
          children: [
            RaisedButton(
                child: Text("Explorer"),
                onPressed: () => Navigator.pushNamed(context, '/explore')),
            RaisedButton(
                child: Text("Play"),
                onPressed: () => Navigator.pushNamed(context, '/play')),
          ],
        ),
      ),
    );
  }
}

void main() {
  runApp(new MaterialApp(
    title: 'SAYC Bridge',
    routes: {
      '/': (BuildContext context) => MainMenu(),
      '/play': (BuildContext context) => PlayHome(),
      '/explore': (BuildContext context) => BidExplorer(),
    },
  ));
}
