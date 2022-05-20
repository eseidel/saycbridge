// Copyright 2016 The SAYCBridge Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

import 'package:flutter/material.dart';
import 'package:saycbridge/play.dart';
import 'package:saycbridge/explorer.dart';

class MainMenu extends StatelessWidget {
  const MainMenu({super.key});

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      body: Center(
        child: Row(
          children: [
            ElevatedButton(
                child: const Text("Explorer"),
                onPressed: () => Navigator.pushNamed(context, '/explore')),
            ElevatedButton(
                child: const Text("Play"),
                onPressed: () => Navigator.pushNamed(context, '/play')),
          ],
        ),
      ),
    );
  }
}

void main() {
  runApp(MaterialApp(
    title: 'SAYC Bridge',
    routes: {
      '/': (BuildContext context) => const MainMenu(),
      '/play': (BuildContext context) => const PlayHome(),
      '/explore': (BuildContext context) => const BidExplorer(),
    },
  ));
}
