#!/usr/bin/env bash
set -euo pipefail

: "${TLA_TOOLS_JAR:?Set TLA_TOOLS_JAR to the absolute path of tla2tools.jar}"

run_pass() {
  local cfg="$1"
  local module="$2"
  echo "PASS expected: ${cfg}"
  java -cp "$TLA_TOOLS_JAR" tlc2.TLC -workers auto -config "$cfg" "$module"
}

run_pass DataPath.cfg SkyLogDataPath.tla
run_pass DataPathLiveness.cfg SkyLogDataPath.tla
run_pass HomeUnchanged.cfg SkyLogHomeUnchanged.tla
run_pass HomeChanged.cfg SkyLogHomeChanged.tla
