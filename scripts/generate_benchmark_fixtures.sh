#!/usr/bin/env bash
#
# Generates the deterministic parity automata (DPAs) used by the benchmarks.
#
# This needs Spot (https://spot.lre.epita.fr, tested with 2.14.5): genltl, ltl2tgba, randaut,
# genaut and autfilt must be in the PATH. The result is committed to the repository; the
# script is NOT run as part of a benchmark. See benches/fixtures/README.md.
#
# Usage: scripts/generate_benchmark_fixtures.sh [OUTPUT_DIR]   (default: benches/fixtures)
#
# Every fixture is deterministic, complete, colored (each edge has exactly one priority),
# uses `parity min even`, has a single initial state and no unreachable states.

set -euo pipefail

OUT=${1:-benches/fixtures}

MAX_STATES=200            # fixtures should stay small, callgrind is slow
MAX_APS=6                 # the HOA reader supports at most 6 atomic propositions
PATTERNS_PER_COLLECTION=4 # how many automata we take from each collection of LTL patterns

# Spot can blow up on some formulas, so every translation gets a time and memory limit.
ulimit -v 1000000                     # 1 GB of address space per process
translate() { timeout 10 ltl2tgba "$@"; }

# Turns whatever comes in on stdin into a deterministic, complete, colored min-even parity
# automaton without unreachable states. Extra arguments are passed on to autfilt.
# `--hoaf=t` forces priorities on edges: by default Spot puts them on states when it can.
# `--split-edges` makes every edge label a conjunction that mentions all atomic propositions,
# the HOA reader of this crate does not accept labels with disjunctions.
to_dpa() {
  autfilt --hoaf=t --split-edges --deterministic --complete --colored-parity='min even' \
          --remove-unreachable-states "$@"
}

rm -rf "$OUT"
mkdir -p "$OUT"/{ltl,random,hard}

# ---------------------------------------------------------------------------------------------
# 1. LTL formulas
# ---------------------------------------------------------------------------------------------

# Parametrised families of formulas from `genltl`: "name  genltl-option  smallest  largest".
# `--gh-r=3` is the third formula of the family `--gh-r`. See `genltl --help` for the formulas.
ltl_families=(
  "gh-r         --gh-r                  1 3"
  "gh-q         --gh-q                  1 3"
  "gf-equiv     --gf-equiv              1 3"
  "gf-implies   --gf-implies            1 3"
  "sejk-j       --sejk-j                1 3"
  "sejk-k       --sejk-k                1 3"
  "ms-phi-r     --ms-phi-r              1 3"
  "ms-phi-s     --ms-phi-s              1 3"
  "ms-phi-h     --ms-phi-h              1 3"
  "go-theta     --go-theta              1 3"
  "and-gf       --and-gf                1 3"
  "and-fg       --and-fg                1 3"
  "or-gf        --or-gf                 1 3"
  "fxg-or       --fxg-or                1 3"
  "u-left       --u-left                1 3"
  "r-right      --r-right               1 3"
  "tv-uu        --tv-uu                 1 3"
  "rv-counter   --rv-counter            1 3"
  "pps-arbiter  --pps-arbiter-standard  2 3"
)

for family in "${ltl_families[@]}"; do
  read -r name option smallest largest <<<"$family"
  for n in $(seq "$smallest" "$largest"); do
    genltl "$option=$n" \
      | translate --deterministic --generic \
      | to_dpa --name="$name-$n" \
      | autfilt --hoaf=t --ap="..$MAX_APS" --states="2..$MAX_STATES" --output="$OUT/ltl/$name-$n.hoa" \
      || true   # a formula whose automaton is too large is simply skipped
  done
done

# Collections of formulas from the literature. Most of them give tiny automata, so we only
# keep the first few that have at least 5 states and 3 priorities. `%l` in the output name
# is replaced by autfilt with the number of the automaton.
pattern_collections=(
  dac-patterns eh-patterns p-patterns sb-patterns hkrss-patterns lily-patterns sejk-patterns
)

for collection in "${pattern_collections[@]}"; do
  genltl "--$collection" \
    | translate --deterministic --generic \
    | to_dpa \
    | autfilt --hoaf=t --ap="..$MAX_APS" --states="5..$MAX_STATES" --acc-sets=3..8 --max-count="$PATTERNS_PER_COLLECTION" \
              --name="$collection-%l" --output="$OUT/ltl/$collection-%l.hoa" \
    || true
done

# ---------------------------------------------------------------------------------------------
# 2. Random automata
# ---------------------------------------------------------------------------------------------
# The seeds below are only used to create the files that are committed. Benchmarks read the
# files, so they never depend on a random number generator.

# "states  atomic-propositions  priorities  edge-density  first-seed  last-seed"
random_automata=(
  "16   1  3  0.20  1 2"
  "64   1  4  0.10  1 2"
  "64   2  4  0.10  1 2"
  "128  2  4  0.03  1 3"
  "128  2  6  0.02  1 2"
  "256  2  8  0.05  1 2"
)

for config in "${random_automata[@]}"; do
  read -r states aps priorities density first_seed last_seed <<<"$config"
  for seed in $(seq "$first_seed" "$last_seed"); do
    name="n$states-a$aps-p$priorities-s$seed"
    randaut --deterministic --colored --states="$states" --density="$density" \
            --acceptance="parity min even $priorities" --seed="$seed" "$aps" \
      | autfilt --hoaf=t --invert-match --is-empty --states="$((states / 2))".. --unique \
      | to_dpa --name="random-$name" --output="$OUT/random/$name.hoa" \
      || true
  done
done

# ---------------------------------------------------------------------------------------------
# 3. Hard cases from genaut
# ---------------------------------------------------------------------------------------------
# These are automata for which determinization (or the conversion to parity acceptance)
# is expensive: many states and many priorities.

hard_cases=(
  "m-nba   --m-nba"    # nondeterministic Büchi, determinization needs n! states
  "l-nba   --l-nba"    # nondeterministic Büchi, complement needs n! states
  "ks-nca  --ks-nca"   # nondeterministic co-Büchi, determinization needs 2^n/(2n+1) states
  "l-dsa   --l-dsa"    # deterministic Streett, no small Rabin automaton exists
)

for case in "${hard_cases[@]}"; do
  read -r name option <<<"$case"
  for n in 2 3; do
    genaut "$option=$n" | to_dpa --name="$name-$n" --output="$OUT/hard/$name-$n.hoa"
  done
done

# The HOA parser (hoars) does not know some of the (purely informative) properties that Spot
# writes, so they are removed from the files.
find "$OUT" -name '*.hoa' -exec sed -i -E 's/ (stutter-sensitive|terminal|very-weak|weak|inherently-weak)\b//g' {} +

echo "wrote $(find "$OUT" -name '*.hoa' | wc -l) fixtures to $OUT"
