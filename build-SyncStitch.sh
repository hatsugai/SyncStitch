#!/bin/sh
git clone https://github.com/hatsugai/ocaml-csp.git
(cd ocaml-csp/src; make)
git clone https://github.com/hatsugai/Guedra.git
(cd Guedra/src; make)
git clone https://github.com/hatsugai/Guedra-draw.git
(cd Guedra-draw/src; make)
git clone https://github.com/hatsugai/SyncStitch.git
(cd SyncStitch/src; make)
