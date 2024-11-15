#!/usr/bin/env bash
cat ex.hoa | autfilt --dot | dot -Tpng -o ex.png
# cat ex.hoa | owl nbadet --no-use-sim-internal --no-sep-sccs --no-use-powersets --no-use-smart-succ --no-sep-rej --compute-lang-inclusions=NULL_SIM | tee det.hoa
cat ex.hoa | owl nbadet --no-use-sim-internal --no-sep-sccs --no-use-powersets --no-use-smart-succ --no-sep-rej --compute-lang-inclusions=NULL_SIM  --state-labels | tee det.hoa
# cat ex.hoa | owl nbadet --no-use-sim-internal --no-sep-sccs --no-use-powersets --no-use-smart-succ --no-sep-rej --state-acceptance --state-labels | tee det.hoa
cat det.hoa | autfilt --dot | dot -Tpng -o det.png
