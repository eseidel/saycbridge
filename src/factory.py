# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

import gib
import z3b.bidder


# FIXME: This probably should be a shared instance instead of
# having global state on the class (for easier unit testing).
class BidderFactory(object):
    default_bidder_class = z3b.bidder.Bidder

    @classmethod
    def default_bidder(cls):
        return cls.default_bidder_class()

    @classmethod
    def configure_from_args(cls, args):
        bidders_by_flag = {
            '-g' : gib.Gib,
            '-z' : z3b.bidder.Bidder,
        }
        for flag in args:
            if flag in bidders_by_flag:
                BidderFactory.default_bidder_class = bidders_by_flag[flag]
                return [arg for arg in args if arg != flag]
        return args
