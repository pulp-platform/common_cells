#!/usr/bin/env bash
# Copyright 2026 ETH Zurich and University of Bologna.
#
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

command -v verible-verilog-lint

find src -type f \( -name '*.sv' -o -name '*.svh' -o -name '*.v' \) -print0 \
  | xargs -0 verible-verilog-lint \
      --waiver_files lint/common_cells.style.waiver \
      --rules=-interface-name-style \
      --lint_fatal
