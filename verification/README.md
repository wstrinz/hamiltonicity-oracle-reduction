# Fresh rc3 verification

All 103 source modules compiled on 4.35.0-rc3; combined and four individual installed Comparator runs exited0 and reached successful default-kernel replay. Positive/negative fixture controls and four local metadata controls passed. `axioms.json` records the actual exported Solution axiom closure. Challenge deliberately contains one definition and four theorem placeholders; Solution has no proof holes or custom axioms.

The source is byte-identical to the older checked development; only the toolchain pin changed. These summaries are whitelist-derived records of a fresh run, not reused 4.34.1 acceptance evidence or signed attestations. Raw logs, exact process identities and full exports are retained privately; their hashes are recorded here. No machine-private paths or unrelated campaign records are included. Standalone export hashes identify separate reproduction exports, not a capture of Comparator's internal streams.

The original WSL version preflight was denied before Lean ran. A later explicitly approved retry through the supported execution context succeeded; no WSL security setting, sandbox rule, binary location, tool source, global default or permission was changed. Existing rc3 tools were used without installation or fetching.

Installed verification is complete. Hosted Palomar/NanoDa verification, editorial review and public release remain separate. License and maintainer decisions were made after this proof run; see `LICENSE-PACKAGING-CHECK.json`. Older `policy-snapshot.json`, `PACKAGING-CHECK.json` and base manifests retain their historical pre-license values and are not current metadata.

Independent agent review confirmed all 103 source files unchanged and all five selected exported types equal across 4.34.1 and rc3, retaining bound-variable display names. Supplemental inspection of 2,362 shared fixed rc3 declaration records also found agreement after resolving export-local IDs and ignoring bound-variable display names only. It did not alter Comparator rules or replace kernel replay. This is not human peer review or novelty clearance.
