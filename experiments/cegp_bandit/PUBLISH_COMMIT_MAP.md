# GitHub publication commit map

GitHub rejected the first push because the original cluster commits used a
private email address. For publication, only author/committer email metadata
was rewritten to the account's GitHub noreply address. File trees, commit
messages, authorship name, and timestamps are unchanged.

Raw result directory names and the `result_commit` column in exported CSV files
retain the original cluster experiment IDs so that they still match the paths
used by the LSF runs.

| Original cluster commit | GitHub commit | Subject |
| --- | --- | --- |
| `c455b912c284` | `fceb64262aa7` | experiments: add CEGP liveness benchmark harness |
| `511331ae4b7a` | `87dbe8336af8` | ic3: expose lightweight epoch propagation statistics |
| `554c28502443` | `2ed009a8ef57` | cegp: add online UCB refinement controller |
| `f127f560e04b` | `e30d0aaee0ba` | experiments: compare CEGP strategies and oracle gap |
| `1e7cf6932e6c` | `59cb5c628869` | ic3ia: recover from stalled interpolation with transition predicates |
| `9d008ec8cf1f` | `5bf3ca0dd00e` | cegp: add bounded pre-refinement warmup |
| `820e28ae334f` | `0c3e2643091f` | experiments: add interpolator ablations |
| `3db26dc72d35` | `1f5c5f763c35` | experiments: add pseudo-init ablations |
| `56128f8d9f3d` | `a44d3cfc5024` | experiments: treat Pono UNSAT exit code as solved |
| `e119ec3299e4` | `6f62e8f1b96f` | ic3ia: adapt fallback strength with online UCB |
| `479f0a2b5656` | `399f86aa0075` | experiments: isolate pseudo-init contribution |
| `80f549363357` | `1c13aba9e372` | ic3ia: credit fallback actions over complete epochs |
| `a149d4972732` | `3fea767f0873` | experiments: record liveness benchmark results |
| `4aabfdcd2e3d` | `ccfe1a0e6e8d` | experiments: support full 310-case array track |
| `29de180e1f45` | `6d7f08fad430` | experiments: shard large LSF benchmark arrays |
| `e9c4870430df` | `2187705f63d1` | experiments: orchestrate sharded full-track runs |
| `2b58e933cbe0` | `78d37be6025a` | experiments: allow pipelined range orchestration |
| `952a958313b0` | `7556dcacbdbc` | experiments: record full 310-case array results |
| `59f7af2739ff` | `4a08e4401c5a` | experiments: publish raw results and MAB trigger tables |
