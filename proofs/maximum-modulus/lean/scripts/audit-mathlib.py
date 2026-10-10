#!/usr/bin/env python3
"""Run the source audit against the project's pinned local mathlib checkout."""

from pathlib import Path
import shlex
import subprocess

project = Path(__file__).resolve().parents[1]
mathlib = project / ".lake" / "packages" / "mathlib"
commands = [
    ["git", "rev-parse", "HEAD"],
    ["cat", "lean-toolchain"],
    ["rg", "--files", "Mathlib/Analysis/Complex", "Mathlib/Analysis/Meromorphic"],
    ["rg", "-n", "-i", r"rouch[eé]?|argument[ _-]?principle|residue[ _-]?theorem|\bvalence\b|\bpuiseux\b|analytic[ _-]?curve|holomorphic.*normali[sz]|normali[sz].*holomorphic|generic[ _-]?degree|proper.*holomorphic|holomorphic.*proper", "Mathlib"],
    ["rg", "-n", "circleIntegral.*logDeriv|logDeriv.*circleIntegral|integral.*divisor|divisor.*integral|sum.*residue|residue.*sum", "Mathlib/Analysis"],
    ["rg", "-n", "-i", r"\bnewton\b|newtonIdent|newton_ident|power.?sums|powersum", "Mathlib"],
    ["rg", "-n", "^(private )?(protected )?(theorem|lemma|def|structure)|^namespace", "Mathlib/Analysis/Complex/JensenFormula.lean", "Mathlib/Analysis/Complex/CanonicalDecomposition.lean", "Mathlib/Analysis/Complex/RiemannMapping.lean", "Mathlib/Analysis/Meromorphic/LogDeriv.lean"],
    ["rg", "-n", "Differentiable\\.analyticAt|DifferentiableOn\\.analyticAt|circleIntegral_eq_zero|circleIntegral_sub_inv_smul", "Mathlib/Analysis/Complex/CauchyIntegral.lean"],
    ["rg", "-n", "analyticAt_clog|cpow_nat_inv_pow|hasStrictDerivAt_cpow_const|analyticAt_localInverse|map_nhds_eq", "Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean", "Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean", "Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean", "Mathlib/Analysis/Calculus/InverseFunctionTheorem/Analytic.lean", "Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean"],
    ["rg", "-n", "analyticOrderAt_eq_natCast|analyticOrderAt_ne_top|analyticOrderAt_deriv_add_one|analyticOrderAt_comp|preimage_zero_mem_codiscreteWithin", "Mathlib/Analysis/Analytic/Order.lean"],
    ["rg", "-n", "logDeriv_mul|logDeriv_comp|logDeriv_pow|logDeriv_eqOn_iff|theorem logDeriv|lemma logDeriv", "Mathlib/Analysis/Calculus/LogDeriv.lean", "Mathlib/Analysis/Meromorphic/Basic.lean"],
    ["rg", "-n", "card_nthRoots|mem_nthRoots|nthRootsFinset_toSet|ncard_rootSet_le", "Mathlib/Algebra/Polynomial/Roots.lean"],
    ["rg", "-n", "norm_le_interp_of_mem_verticalClosedStrip'|slope_le_deriv|deriv_le_slope|monotoneOn_rightDeriv|locallyLipschitz|ae_differentiableAt", "Mathlib/Analysis/Complex/Hadamard.lean", "Mathlib/Analysis/Convex/Deriv.lean", "Mathlib/Analysis/Convex/Continuous.lean", "Mathlib/Analysis/Calculus/Monotone.lean", "Mathlib/Analysis/Calculus/Rademacher.lean"],
    ["rg", "-n", "isCompact_preimage|isClosed_range|isProperMap_fst_of_compactSpace|IsProperMap.restrict|countable_of_isDiscrete|finite_sdiff_of_mem_codiscreteWithin", "Mathlib/Topology/Maps/Proper/Basic.lean", "Mathlib/Topology/Compactness/Lindelof.lean", "Mathlib/Topology/DiscreteSubset.lean"],
    ["rg", "-n", "analytic sets in the context|nothing to do with analytic sets|Weierstrass preparation|exists_isWeierstrassFactorization", "Mathlib/MeasureTheory/Constructions/Polish/Basic.lean", "Mathlib/Geometry/Manifold/Complex.lean", "Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean"],
]

log = project / "logs" / "mathlib-audit.log"
log.parent.mkdir(parents=True, exist_ok=True)
with log.open("w") as output:
    output.write(f"Working directory: {mathlib}\n\n")
    for command in commands:
        output.write("$ " + shlex.join(command) + "\n")
        result = subprocess.run(command, cwd=mathlib, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
        output.write(result.stdout)
        output.write(f"[exit {result.returncode}]\n\n")
        if result.returncode not in (0, 1):
            raise RuntimeError(f"Unexpected audit command failure: {command}")
print(log)
