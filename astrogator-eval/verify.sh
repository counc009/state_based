#!/usr/bin/bash
set -e

./verifier.py
mv results.csv results-verifier-2026-07-02.csv

clear
./verifier.py -u
mv results.csv results-users-2026-07-02.csv

clear
./verifier.py -p
mv results.csv results-packages-2026-07-02.csv

clear
./verifier.py -f
mv results.csv results-files-2026-07-02.csv

clear
./verifier.py -r
mv results.csv results-reboot-2026-07-02.csv

clear
./verifier.py -w
mv results.csv results-writes-2026-07-02.csv

clear
./verifier.py -F
mv results.csv results-strict-files-2026-07-02.csv
