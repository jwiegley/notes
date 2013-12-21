#!/bin/bash

vlc=/Applications/Misc/VLC.app/Contents/MacOS/VLC

case $1 in
    server)                     # argument is the file to play
        $vlc $2 --sout "#standard{access=udp,mux=ts,dst=239.255.1.1}" ;;
    mclient)
        $vlc udp://@239.255.1.1 --control netsync --netsync-master ;;
    client)                     # argument is the server's IP address
        $vlc udp://@239.255.1.1 --control netsync --netsync-master-ip $2 ;;
esac
