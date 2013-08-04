# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.


# It's nice to have the scripts outside of src, but the
# cost is that we need to teach all the scripts to be able
# to find src, hence this module.

import os.path
import sys

scripts_dir = os.path.dirname(__file__)
root_dir = os.path.dirname(scripts_dir)
src_dir = os.path.join(root_dir, 'src')
sys.path.append(src_dir)
