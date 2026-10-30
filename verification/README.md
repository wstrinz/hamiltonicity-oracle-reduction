# Fresh rc3 verification

All 103 source modules compiled on 4.35.0-rc3; combined and four individual installed Comparator runs exited0 and reached successful default-kernel replay. Positive/negative fixture controls and four local metadata controls passed. `axioms.json` records the actual exported Solution axiom closure. Challenge deliberately contains one definition and four theorem placeholders; Solution has no proof holes or custom axioms.

The source is byte-identical to the older checked development; only the toolchain pin changed. These summaries are whitelist-derived records of a fresh run, not reused 4.34.1 acceptance evidence or signed attestations. Raw logs, exact process identities and full exports are retained privately; their hashes are recorded here. No machine-private paths or unrelated campaign records are included. Standalone export hashes identify separate reproduction exports, not a capture of Comparator's internal streams.

The original WSL version preflight was denied before Lean ran. A later explicitly approved retry through the supported execution context succeeded; no WSL security setting, sandbox rule, binary location, tool source, global default or permission was changed. Existing rc3 tools were used without installation or fetching.

Installed verification is complete. Hosted Palomar/NanoDa verification, editorial review and public release remain separate. License and maintainer decisions were made after this proof run; see `LICENSE-PACKAGING-CHECK.json`. Older `policy-snapshot.json`, `PACKAGING-CHECK.json` and base manifests retain their historical pre-license values and are not current metadata.

Independent agent review confirmed all 103 source files unchanged and all five selected exported types equal across 4.34.1 and rc3, retaining bound-variable display names. Supplemental inspection of 2,362 shared fixed rc3 declaration records also found agreement after resolving export-local IDs and ignoring bound-variable display names only. It did not alter Comparator rules or replace kernel replay. This is not human peer review or novelty clearance.

## Standalone installed NanoDa replay after publication

NanoDa 0.4.17, bundled with the installed Lean 4.35.0-rc3 toolchain, checked the retained Solution export on 30 October 2026. Exit 0; output reports 5,087 declarations with no typechecker errors and one pretty-printer diagnostic, "Unable to print axioms". This was not a fresh hosted workflow or a claim of editorial acceptance. The input export is the standalone reproduction export described in `exports.json`, not Comparator's captured internal stream. Its proof sources match the published package; publication edits affect documentation only.

Binary SHA-256: `8241c5e6baa29490aa118d382f97961b208ae730fdb96545c2abed74c9ece5a8`. Export SHA-256: `cd005f31629040badf74cafefeeec4726b2550184fa50298c2660d91cf64602b`. Only propext, Classical.choice and Quot.sound were permitted, with unpermitted axioms a hard error and permit-all disabled; Nat and String extensions were enabled. One-core, 16 GiB and host-free-memory guards completed without a stop, and checker/launcher identities exited. Licensee was unavailable in the installed Ruby environment; no package was installed and the official license gate is not claimed complete.
