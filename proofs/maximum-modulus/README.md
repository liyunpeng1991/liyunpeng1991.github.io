# Maximum-modulus points: paper v2 and Lean proof

This directory is the source distribution intended for `proofs/maximum-modulus/` in the author's website repository.

The [revised paper source](lean/docs/continuation_expansion.tex), titled *A cofinal bound for maximum-modulus points of entire functions*, proves that every nonzero entire function that is not a monomial has a fixed finite maximum-point bound at arbitrarily large radii. This rules out divergence of the number of exact maximum-modulus points along all large radii. The stronger locally finite exceptional-radius theorem and sharpness examples from the earlier manuscript are outside this verified claim.

The reproducible [Lean project](lean/README.md) has exact pinned dependencies and an explicit theorem with actual function values, all quantifiers, and finiteness. [Verification evidence](lean/verification/README.md) preserves actual historical commands, complete target axiom reports, kernel replay logs, and the independent statement comparison.

`maximum_modulus_points.tex` is the unchanged earlier manuscript preserved for the provenance check in `lean/scripts/source_integrity.py`; its original SHA-256 is `bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1`. It is an archival input, not the revised paper. Keep it immediately above the `lean/` directory if running the full verification script.

`STAGE-MANIFEST.json` records every staged file's role, size, and SHA-256. `SHA256SUMS` also authenticates that manifest. The 53 production Lean source/config/script files are copied byte for byte from the verified source; staging does not rerun Lean checks and does not assert that a new public Git commit has already been verified. The historical audit snapshot is identified in the evidence; any subsequent public-commit check must be recorded separately.

Generated `.lake/` and `.tools/` products are excluded. The two large raw NDJSON proof exports are omitted; their recorded hashes and generating commands remain in the evidence and they can be regenerated. Nothing in this staging record constitutes maintainer acceptance or an award decision.
