#!/bin/sh
# Copyright (c) 2016 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.
apt-get update
apt-get install git build-essentials python-pip python-dev
git clone https://github.com/eseidel/saycbridge.git
cd saycbridge
git submodule update --init
make deps -j$(nproc)
