# Licensing and publication layout

Will Strinz approved MIT for the original proofs/code and associated documentation, CC BY 4.0 for the separate manuscript, and his role as responsible maintainer on 29 October 2026. These are the applied local choices. They do not authorize a public push or submission.

## Included snapshot

`LICENSE` is the single conventional root license file; `formalization.yaml` declares `project.license: MIT`. MIT covers original `HamParity/*.lean`, `HamParity.lean`, scripts, build configuration, metadata, README, documentation and original verification summaries. Dependencies, cited works and third-party material retain their own rights and notices; nothing here purports to relicense them. Implementations of the external tools/libraries and paper texts are not vendored. See `docs/THIRD_PARTY.md`.

The focused manuscript is distributed separately under CC BY 4.0. Its source/PDF must not be added to this single-license submission snapshot without revisiting packaging. The proof snapshot includes its own statement, proof map, attribution and AI disclosure, so it does not depend on the external note to describe the formal claim.

## Palomar boundary

The [official policy, sections 2.5 and 6.1](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#25-repository-licence) requires one root license and a matching SPDX identifier. Selecting a Lean subdirectory does not relocate that license or exclude the rest of the commit. The [verifier](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/verify_submission.py#L1526-L1548) checks the checkout root, not the selected project root. The detector inspects the chosen root license; that is not approval of any undocumented mixed-license arrangement.

Recommended publication: use `hamiltonicity-oracle-reduction` for this proof-only root, and distribute the CC BY manuscript separately with cross-links once real destinations exist. A second repository is not an express policy requirement. A proof-only commit/branch in a broader repository is a plausible alternative because intake pins a complete commit, but its acceptability is an inference, not a documented subtree filter. Do not submit a mixed tree while assuming `project_path` hides its manuscript.

## Identity and remaining gate

`project.responsible_maintainers: ["Will Strinz"]` meets the documented name-list shape. Email, telephone, postal address, affiliation, GitHub login and ORCID are not required in that field. The already-approved ORCID remains in citation/author documentation; no additional personal contact details are added. Submission authority and GitHub push access are separate checks. No self-approval evidence is needed when Will submits as responsible author/maintainer; an agent must truthfully use approval from a responsible author/maintainer. Optional free-text evidence can become public and is omitted here.

Remaining: authorize and create the public repository/fixed commit; run the full official workflow (including NanoDa) and editorial process; then explicitly approve registration. Installed Comparator/default-kernel results alone are not hosted acceptance. No public destination or commit identifier is invented.

Official license texts: [MIT](https://opensource.org/license/mit) and [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/legalcode.en). Current requirements were inspected 29 October 2026; recheck at submission.
