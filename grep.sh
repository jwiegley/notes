#!/bin/bash

for i in $(seq 1 100); do
    echo hello | grep -q hello
done
