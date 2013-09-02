#!/bin/sh
# Copyright (c) 2013 The SAYCBridge Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

while :
do
    git clean -f -d # Remove any left-over files.
    git fetch origin # Avoid updating the working copy to a stale revision.

    # Forcibly create a new production branch (to make sure we're really clean).
    git checkout origin/production -f
    git branch -D production
    git checkout origin/production -b production

    make serve-prod
done
