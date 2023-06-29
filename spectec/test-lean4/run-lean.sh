#!/usr/bin/env bash

lean "$1" 2>&1 | sed -e 's,/[^ ]*/toolchains,.../toolchains`,g' | sed -e 's,SpecTec.lean:[0-9]\+:[0-9]\+,SpecTec.lean,' | sed -e 's,\?m\.[0-9]\+,?m,g'
