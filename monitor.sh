#!/bin/bash
exec multitail                                  \
    -l "cd ~/fpco; git-monitor -v"              \
    -l "cd ~/fpco/gitlib; git-monitor -v"       \
    -l "cd ~/fpco/gitlib-fpco; git-monitor -v"
