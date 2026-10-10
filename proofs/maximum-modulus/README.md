# Maximum-modulus points: published paper v2 and Lean proof

The paper and proof source are published in the [author's website repository](https://github.com/liyunpeng1991/liyunpeng1991.github.io) on branch `main`, under [`proofs/maximum-modulus/`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/main/proofs/maximum-modulus). The exact immutable source publication A is [`c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus); the Lean project is [`proofs/maximum-modulus/lean/`](https://github.com/liyunpeng1991/liyunpeng1991.github.io/tree/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/proofs/maximum-modulus/lean).

The revised paper, *A cofinal bound for maximum-modulus points of entire functions*, is available as [PDF v2](https://liyunpeng1991.github.io/papers/maximum-modulus-points-v2.pdf) and [source pinned to publication A](https://github.com/liyunpeng1991/liyunpeng1991.github.io/blob/c063e5f83dfa71c97871eabc8b70cf8a8c1e0bc9/papers/maximum-modulus-points-v2.tex). It proves that every nonzero entire function which is not a monomial has a fixed finite bound on its exact maximum-modulus points at arbitrarily large radii. This rules out divergence along all large radii. The earlier stronger locally finite exceptional-radius theorem and sharpness examples are outside the verified claim.

The [Lean project](lean/README.md) has exact pinned dependencies, an explicit theorem using actual function values and all quantifiers, and explicit finiteness. Its 53 production source/config/script files are unchanged from the historical verified proof and are published in A.

Verification records are separated by their inputs:

- [Fresh verification of the exact published source A](lean/verification/public-commit-report.md): **passed**. The fresh clean build, 43 source checks, 42 project-module kernel replays, eight target checks, and exported-proof comparison with all five bundled additional kernels plus Lean default exited 0. The 126 audited production declarations and all eight targets report only the three standard foundations. Complete curated executed records are included.
- [Historical verification](lean/verification/prize-report.md): the actual successful prepublication checks concerned temporary audit snapshot `8b731b51dcb0ed3d7e8c6463b6266c35d8099c85`. Their results are not represented as fresh checks of A or a later evidence publication.
- This later evidence update B adds documentation and executed records. It does not replace the exact proof-input revision A or imply verification of its own documentation from the source-A checks.

`maximum_modulus_points.tex` is the unchanged earlier manuscript preserved solely for the provenance check in `lean/scripts/source_integrity.py`; its SHA-256 is `bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1`. It is an archival input, not the revised paper. Keep it immediately above `lean/` when running the full verification script.

`STAGE-MANIFEST.json`, `SHA256SUMS`, and `PUBLIC-CONTENT-REVIEW.json` are unchanged historical records of the frozen prepublication staging directory. They include that directory's former READMEs and do not cover later README overrides or new public-commit evidence. The new `PUBLICATION-MANIFEST.json`, `PUBLICATION-SHA256SUMS`, and `PUBLICATION-CONTENT-REVIEW.json` describe the B update payload separately.

Generated toolchains/caches, `.git/`, `.lake/`, `.tools/`, and large raw NDJSON exports are excluded. Export hashes and generating commands remain in the evidence. Verification and publication do not imply maintainer acceptance or an award decision.
