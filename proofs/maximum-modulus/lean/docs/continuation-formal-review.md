# Review of the reduced continuation argument

This review checks the mathematical scope of `BranchContinuation.lean`,
`ProductNonconstant.lean`, and `HighCountInterior.lean` against the manuscript's
continuation/degree argument. It does not claim completion of the final theorem
or replace the project's executed build and kernel-verification records. The
manuscript was read and left unchanged.

## Finding

No mathematical error or hidden weakening was found in these three modules.
The reduced route replaces the manuscript's global irreducible-component degree
and normalization argument by the closure of the actual regular high-count
locus. Its required hypotheses are actual local analytic families, physical
fiber counts, and captures. Openness or complete-branch selection is proved
from these inputs; it is not smuggled into the actual finite-value construction.

The remaining global application must cover all three spherical-value cases:
ordinary finite values different from `m`, the omitted finite value `m`, and
infinity. The finite interior module alone does not establish the latter two.

## Actual objects and hypotheses

`FiniteLogDerivativeImage m g` uses nonempty actual ordered inverse-pair fibers
of `sphereLogDerivative m g` and its reflected counterpart. `IsSingleValueGraph`
means that the **whole actual image**, not merely one chosen branch, is locally
an analytic graph over the common value. `RegularLogDerivativeHighCount` uses
explicitly finite actual fibers, their `Set.ncard`, and a strict inequality
`L < ncard`. Thus infinite sets cannot qualify through a zero-valued `ncard`.
Its regularity condition also explicitly restricts the locus to finite values.

The analytic hypotheses used throughout are `Entire g`, `g 0 ≠ 0`,
`¬IsMonomial f`, and the pointwise identity `f z = z^m * g z`. These are the
actual factorization data already constructed for the original nonzero,
non-monomial entire function. There is no extra reciprocal-exclusion axiom,
chart-existence axiom, or assumed global degree.

## Finite interior values

`finiteTargetBranchCover_exists` constructs the finite family from the actual
proper correspondence and local inverse-root charts. Its index type remembers
central physical pairs and roots of unity. Different indices are allowed to
represent the same physical pair. The exposed `fiber_eq` is equality with a
physical image set, including parameter zero; no index cardinal is substituted
for physical cardinality.

In `HighCountInterior.lean`, a common smaller radius stabilizes physical
collision kernels and actual branch fiber counts. The selected index set is
`J = {j | L < d j}`. Every selected punctured branch consists of actual regular
high-count targets. Conversely, a high-count target in the local neighborhood
lies on a selected full branch.

The converse's central case is checked separately. At a regular central target,
all product germs lie in the single total-image graph. Equality of physical
pairs at a punctured parameter gives a germ equality and hence central
physical equality. `central_fiber_count_le_of_total_graph` therefore bounds
central physical cardinality by the punctured physical cardinality. This
prevents an isolated high-count central fiber from appearing. A singular
central target is excluded from the regular locus but may still occur in its
closure, as it should.

`high_count_local_closure_branches` then applies the proved selected-branch
closure theorem. `finite_regular_high_count_closure_contains_analytic_branch`
supplies a whole centered branch at every closure point with `s ≠ 0` and
`p ≠ m`. `regular_high_count_closure_finite_local_projection_isOpen` transfers
the proved local open projection to the actual spherical closure using the
finite-value open embedding. These restrictions are explicit, not a purported
proof at the omitted value or infinity.

## Constant-product exclusion

`logarithmic_pair_product_germ_nonconstant` assumes an actual analytic first
physical coordinate, a continuous second coordinate, positive `N`, actual
common values `p₀+t^N`, and a nonzero central physical product. It derives
first-coordinate nonconstancy from those actual values. An eventually constant
first coordinate would make `p₀+t^N` constant as a germ, which is impossible.

Finite central spherical values imply both factor values are nonzero, so the
proved local reciprocal-germ exclusion applies. A constant product would force
`w = s/z` on a genuine open set of first-coordinate values and contradict that
exclusion. The result applies at `p₀=m` as well: it only requires the central
value to be finite. It does **not** by itself address a pole-centered branch;
that case needs its own argument at a nearby finite-valued parameter.

## Continuation through the omitted value

`closure_continues_through_finite_imageBranches` is a general theorem with
explicit inputs: finitely many analytic raw branches, stabilized rotated
comparisons, an open neighborhood inside the value cylinder, entire raw disks
contained in that neighborhood, capture of `A` there, omission of the central
value by `A`, and actual interior subbranches of `closure A`.

The proof first captures `closure A` by the finite raw-image union using
relative closedness in the value cylinder. At a noncentral point, stabilized
comparisons capture the whole nearby union inside one branch graph. An
interior analytic subbranch in the closure has a nonconstant power value
coordinate. Open mapping makes closure membership open on that graph.
Closedness and preconnectedness of the punctured disk then select the entire
punctured branch, and closedness adds its center. The final closure equality
uses that `A` omits the central value, so no unsupported isolated center is
introduced.

The actual omitted-value input is supplied by
`omittedHighCountBranchCover_exists`: the small-coordinate bound leaves a
bounded surviving physical pair; compact annulus capture produces finite
inverse-root families. Families with a different central product are
**discarded** using `finite_germ_central_value_capture`. This is necessary:
retaining all annulus product centers would not justify placing every whole
branch disk inside one neighborhood of the chosen target. The construction
filters to `S_i(0)=s₀`, then uniformly shrinks disks, so its `branchW` input is
supported by actual continuity. Only capture of high-count targets is required;
there is no claim that every escaping physical pair is enumerated at `p=m`.

## Infinity and scope of the final application

The definition of the regular high-count locus omits infinity. Infinity can
still lie in its closure. The separate infinity chart uses the actual spherical
coordinate `p = 1/t`, with `p=∞` at `t=0`. Its punctured actual total-image graphs
transfer to ordinary finite-value graphs by analytic inversion. Selection of
branches by constant actual physical counts then supplies the local closure
and projection argument at infinity; a central high-count comparison is not
needed because infinity itself is absent from the regular locus.

`InfinityTargetBranchCover.product_germ_nonconstant` handles verticality there
by moving to a nearby nonzero reciprocal parameter, where both physical factor
values are nonzero, and applying local reciprocity exclusion. This fills the
pole-centered case not covered by the finite-value product-germ theorem.

For global assembly, nonzero product at every closure point must come from the
proved small-product exclusion. Then the three local projection results must
be combined with closed projection along the compact sphere. The original
all-radii conclusion still requires that final assembly and its executed
verification; the general continuation theorem alone is not that conclusion.

## Executed checks relevant to this review

`HighCountInterior.lean` compiled without warnings and its module build passed
in `logs/high-count-interior-04.*` and `logs/high-count-interior-build-01.*`.
Five targeted axiom checks are recorded in
`logs/high-count-interior-axioms-01.*`; they report only `propext`,
`Classical.choice`, and `Quot.sound`. The corresponding check source is
`verification/HighCountInteriorAxioms.lean`.
