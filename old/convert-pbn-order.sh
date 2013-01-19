#!/bin/sh
sed -i '' -e 's/\([2-9AKQJTakqjt]\{0,13\}\)[.]\([2-9AKQJTakqjt]\{0,13\}\)[.]\([2-9AKQJTakqjt]\{0,13\}\)[.]\([2-9AKQJTakqjt]\{0,13\}\)/\4.\3.\2.\1/g' `find . -type f | grep -v .git`
