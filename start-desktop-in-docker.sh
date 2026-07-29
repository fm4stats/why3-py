#!/bin/bash

set -e

mkdir -p /home/guest/.config/tigervnc
chown -R guest:guest /home/guest/.config/tigervnc

su - guest -c "vncserver :1 \
    -geometry 1280x800 \
    -depth 24 \
    -SecurityTypes None"

exec websockify \
    --web=/usr/share/novnc/ \
    0.0.0.0:6080 \
    localhost:5901
