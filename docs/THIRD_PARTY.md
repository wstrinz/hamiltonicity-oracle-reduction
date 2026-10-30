# Third-party attribution and bounded rights audit

The candidate includes 103 project Lean files, not Lean/Std, Mathlib, Comparator, exporter or sandbox implementations. It includes no external paper PDFs, private transcripts, upstream source archives, binaries, object files or complete declaration exports. Scans of copied Lean sources found no existing third-party copyright/license header to strip and no machine-private path. This is a bounded inventory/attribution audit, not proof that every expression is original or that all rights are settled.

| Component | Role here | Upstream license / treatment |
|---|---|---|
| Lean 4.35.0-rc3, including core/Std | Required toolchain and imported library; not vendored | Apache-2.0; [pinned license](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/LICENSE) |
| leanprover/comparator | External verifier; not vendored | Apache-2.0; [pinned license](https://github.com/leanprover/comparator/blob/fd5d5bcf14177b187f66d4502071268d877887c3/LICENSE) |
| leanprover/lean4export | External exporter; not vendored | Apache-2.0; [pinned license](https://github.com/leanprover/lean4export/blob/66f1fb4bc256072069767fce52d39480e4524869/LICENSE) |
| Zouuup/landrun | External sandbox; not vendored | MIT; [pinned license](https://github.com/Zouuup/landrun/blob/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4/LICENSE) |
| Cygan et al.; Applebaum | Mathematical citations | Bibliographic attribution; no paper text or source redistributed |

The dependency licenses do not themselves select a license for this project's original work. Apache-2.0 distinguishes separable interface use from derivative works; if dependency code or binaries are later distributed, retain the applicable license and notices and review modifications. No incompatibility is inferred merely from importing core/Std. The approved MIT grant covers this project's original proof/code and associated documentation; it does not relicense dependencies, cited papers, upstream license texts or any third-party contribution. Existing notices and citation records are retained.

The proof/statement correspondence was independently agent-reviewed. Bibliographic novelty and ownership were not established by that review. Source rights and any unrecorded human contributions remain for author confirmation. `AI_ASSISTANCE.md` records the substantial automated contribution without designating AI systems as human authors.
