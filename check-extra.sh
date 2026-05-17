#!/usr/bin/env bash
# Verify hand-written Dafny proofs not covered by `lsc check`.
set -e
cd "$(dirname "$0")"

dafny verify --standard-libraries src/domain.proofs.dfy
