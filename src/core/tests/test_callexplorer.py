# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import unittest
from core.callexplorer import *


class CallExplorerTest(unittest.TestCase):
    def _assert_histories(self, glob_string, histories):
        explorer = CallExplorer()
        self.assertEqual(sorted([history.calls_string(
        ) for history in explorer.history_glob(glob_string)]), sorted(histories))

    def test_history_glob(self):
        self._assert_histories("", [])
        self._assert_histories(" ", [])
        self._assert_histories("P", ["P"])
        self._assert_histories(" P ", ["P"])
        self._assert_histories("P  1C", ["P 1C"])
        self._assert_histories("* 1C", ["P 1C"])
        self._assert_histories("1C * 1H", ["1C 1D 1H", "1C X 1H", "1C P 1H"])
        self._assert_histories("* 1C * 1D", ["P 1C X 1D", "P 1C P 1D"])
        # Only non-pass options should be considered.
        self._assert_histories("P P P * 1D", ["P P P 1C 1D"])


if __name__ == '__main__':
    unittest.main()
