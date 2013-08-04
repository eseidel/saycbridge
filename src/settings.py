# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import os.path
PROJECT_DIR = os.path.dirname(__file__) # this is not Django setting.

TEMPLATE_DIRS = (
    os.path.join(PROJECT_DIR, "templates"),
)
