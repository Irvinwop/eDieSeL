# Register AND64 immediate probes

Owned Linux x86-64 C/assembly fixtures check 25 instruction windows on four
input states each, covering all 16 GPR destinations and selected positive and
negative signed-byte masks. A bit-membership and low-byte population oracle
checks the full result, all GPR frames and every defined effective flag. AF is
undefined and observed as a witness. Five deliberately wrong width, sign,
destination, flag and operation windows must disagree with that oracle.

Run `bash scripts/verify-and64-immediate.sh`. It authenticates the extracted
linked bytes, rejects an altered extraction, checks every window against
`cases.json`, then generates and kernel-checks 25 four-observation Lean shards
through the production decoder and executor. The fresh output directory holds
the exact decimal observations, sources, hashes, commands and exit status.
`--native-only` skips Lean replay and says so in `scope.txt`.

Inputs are installed/requested GPRs, measured effective flags and measured post
GPRs/flags. RIP denotes the linked continuation label; the empty operand-read
list is a model property. These finite observations establish no compiler,
physical CPU/OS refinement, corpus certification or timing result. The positive
fixtures include RSP as data and do not replace or grant a program's stack loan.
