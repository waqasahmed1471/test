#!/bin/sh
sudo ./build/helloworld -l 0-2 -n 1 -- -u 1 -L 6 -D 4 -m 225.53.6.13 &
sleep 1
cd /home/waqas/Downloads/dpdk-stable-18.02.2
sudo ./build/app/dpdk-pdump -- --pdump 'port=0,queue=0,tx-dev=/tmp/tx1.pcap,rx-dev=/tmp/rx1.pcap'
