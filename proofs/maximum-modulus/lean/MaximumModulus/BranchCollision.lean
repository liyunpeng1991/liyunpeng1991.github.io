module

public import MaximumModulus.LocalValence
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Order.Filter.Finite

@[expose] public section

/-!
# Persistent collisions in a local image branch

An image parameterization `(S(t), p₀ + t^E)` can collide only through multiplication
by an `E`th root of unity. Near the origin, each of these finitely many possible
collisions either persists as an equality of analytic germs or never occurs away
from the origin. The theorems below prove this dichotomy uniformly, and identify
the exact noncentral fibers with the persistent root symmetries.
-/

open Filter
open scoped Topology

namespace MaximumModulus

noncomputable section

/-- Roots of unity whose multiplication preserves the germ of `S` at zero. -/
def PersistentSymmetries (S : ℂ → ℂ) (E : ℕ) : Set ℂ :=
  {ω | ω ^ E = 1 ∧ ∀ᶠ t in 𝓝 (0 : ℂ), S (ω * t) = S t}

/-- The special image parameterization arising from the local inverse-pair construction. -/
def ImageBranch (S : ℂ → ℂ) (E : ℕ) (p₀ : ℂ) (t : ℂ) : ℂ × ℂ :=
  (S t, p₀ + t ^ E)

theorem persistentSymmetries_finite {S : ℂ → ℂ} {E : ℕ} (hE : 0 < E) :
    (PersistentSymmetries S E).Finite := by
  exact (power_fiber_finite_ncard_le E hE 1).1.subset fun _ hω => hω.1

theorem persistentSymmetries_ncard_le {S : ℂ → ℂ} {E : ℕ} (hE : 0 < E) :
    (PersistentSymmetries S E).ncard ≤ E := by
  exact (Set.ncard_le_ncard (fun _ hω => hω.1)
    (power_fiber_finite_ncard_le E hE 1).1).trans
    (power_fiber_finite_ncard_le E hE 1).2

theorem one_mem_persistentSymmetries (S : ℂ → ℂ) (E : ℕ) :
    (1 : ℂ) ∈ PersistentSymmetries S E := by
  exact ⟨one_pow E, Eventually.of_forall fun _ => by simp⟩

theorem persistentSymmetries_mul {S : ℂ → ℂ} {E : ℕ} {ω ξ : ℂ}
    (hω : ω ∈ PersistentSymmetries S E) (hξ : ξ ∈ PersistentSymmetries S E) :
    ω * ξ ∈ PersistentSymmetries S E := by
  refine ⟨by rw [mul_pow, hω.1, hξ.1, one_mul], ?_⟩
  have htend : Tendsto (fun t : ℂ => ξ * t) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using (continuous_const_mul ξ).tendsto (0 : ℂ)
  filter_upwards [htend.eventually hω.2, hξ.2] with t h₁ h₂
  simpa only [mul_assoc] using h₁.trans h₂

theorem persistentSymmetries_ne_zero {S : ℂ → ℂ} {E : ℕ} (hE : 0 < E) {ω : ℂ}
    (hω : ω ∈ PersistentSymmetries S E) : ω ≠ 0 := by
  intro hzero
  have hp := hω.1
  simp [hzero, hE.ne'] at hp

theorem persistentSymmetries_inv {S : ℂ → ℂ} {E : ℕ} (hE : 0 < E) {ω : ℂ}
    (hω : ω ∈ PersistentSymmetries S E) : ω⁻¹ ∈ PersistentSymmetries S E := by
  have hne := persistentSymmetries_ne_zero hE hω
  refine ⟨by rw [inv_pow, hω.1, inv_one], ?_⟩
  have htend : Tendsto (fun t : ℂ => ω⁻¹ * t) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using (continuous_const_mul ω⁻¹).tendsto (0 : ℂ)
  filter_upwards [htend.eventually hω.2] with t ht
  simpa only [← mul_assoc, mul_inv_cancel₀ hne, one_mul] using ht.symm

/-- The comparison version of isolated zeros, needed when combining finitely many image
branches. The two analytic functions need not be equal. -/
theorem analytic_multiplier_comparison {S T : ℂ → ℂ}
    (hS : AnalyticAt ℂ S 0) (hT : AnalyticAt ℂ T 0) (ω : ℂ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      S (ω * t) = T t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u := by
  have hmul : AnalyticAt ℂ (fun t : ℂ => ω * t) 0 :=
    analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ (fun t => S (ω * t)) 0 :=
    hS.fun_comp_of_eq hmul (by simp)
  rcases hcomp.eventually_eq_or_eventually_ne hT with h | h
  · filter_upwards [h.filter_mono nhdsWithin_le_nhds] with t ht
    exact ⟨fun _ => h, fun _ => ht⟩
  · have hn : ¬∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u := by
      intro heq
      have hc := (heq.filter_mono nhdsWithin_le_nhds).and h
      exact hc.exists.elim fun _ hu => hu.2 hu.1
    filter_upwards [h] with t ht
    exact ⟨fun heq => False.elim (ht heq), fun heq => False.elim (hn heq)⟩

/-- Isolated zeros give the persistent/nonpersistent collision dichotomy for one multiplier. -/
theorem analytic_multiplier_collision {S : ℂ → ℂ} (hS : AnalyticAt ℂ S 0)
    (ω : ℂ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      S (ω * t) = S t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = S u := by
  exact analytic_multiplier_comparison hS hS ω

/-- The finitely many root-of-unity collision tests stabilize simultaneously. -/
theorem imageBranch_collisions_eventually {S : ℂ → ℂ} (hS : AnalyticAt ℂ S 0)
    {E : ℕ} (hE : 0 < E) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = S t ↔ ω ∈ PersistentSymmetries S E) := by
  have hfin := (power_fiber_finite_ncard_le E hE 1).1
  apply hfin.eventually_all.mpr
  intro ω hω
  change ω ^ E = 1 at hω
  filter_upwards [analytic_multiplier_collision hS ω] with t ht
  simpa only [PersistentSymmetries, Set.mem_ofPred_eq, hω, true_and] using ht

/-- A metric version of simultaneous stabilization, with an explicit positive radius. -/
theorem imageBranch_collisions_radius {S : ℂ → ℂ} (hS : AnalyticAt ℂ S 0)
    {E : ℕ} (hE : 0 < E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      ∀ ω : ℂ, ω ^ E = 1 →
        (S (ω * t) = S t ↔ ω ∈ PersistentSymmetries S E) := by
  have hevent := eventually_nhdsWithin_iff.mp (imageBranch_collisions_eventually hS hE)
  obtain ⟨ε, hε, ht⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, hε, fun t hnorm hne => ?_⟩
  exact ht (by simpa only [dist_zero_right] using hnorm) hne

/-- Once collisions have stabilized, the whole fiber is the persistent symmetry orbit. -/
theorem imageBranch_fiber_eq_orbit {S : ℂ → ℂ} {E : ℕ} {p₀ t : ℂ}
    (ht : t ≠ 0)
    (hcollision : ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = S t ↔ ω ∈ PersistentSymmetries S E)) :
    {u : ℂ | ImageBranch S E p₀ u = ImageBranch S E p₀ t} =
      (fun ω : ℂ => ω * t) '' PersistentSymmetries S E := by
  ext u
  constructor
  · intro hu
    have hfirst : S u = S t := congrArg Prod.fst hu
    have hpow : u ^ E = t ^ E := add_left_cancel (congrArg Prod.snd hu)
    have hω : (u / t) ^ E = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ ht)]
    refine ⟨u / t, (hcollision _ hω).mp ?_, div_mul_cancel₀ _ ht⟩
    simpa only [div_mul_cancel₀ _ ht] using hfirst
  · rintro ⟨ω, hω, rfl⟩
    apply Prod.ext
    · exact (hcollision ω hω.1).mpr hω
    · simp only [ImageBranch, mul_pow, hω.1, one_mul]

/-- Near zero, every noncentral image fiber is finite and has exactly the number of
persistent root symmetries. This is an actual set of parameter values, not a degree axiom. -/
theorem imageBranch_fibers_radius {S : ℂ → ℂ} (hS : AnalyticAt ℂ S 0)
    {E : ℕ} (hE : 0 < E) (p₀ : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      {u : ℂ | ImageBranch S E p₀ u = ImageBranch S E p₀ t}.Finite ∧
      {u : ℂ | ImageBranch S E p₀ u = ImageBranch S E p₀ t}.ncard =
        (PersistentSymmetries S E).ncard := by
  obtain ⟨ε, hε, hcoll⟩ := imageBranch_collisions_radius hS hE
  refine ⟨ε, hε, fun t hnorm ht => ?_⟩
  rw [imageBranch_fiber_eq_orbit ht (hcoll t hnorm ht)]
  exact ⟨(persistentSymmetries_finite hE).image _,
    Set.ncard_image_of_injective _ (mul_left_injective₀ ht)⟩

/-- Uniform collision stabilization between two analytic branches with the same exponent. -/
theorem imageBranch_comparisons_radius {S T : ℂ → ℂ}
    (hS : AnalyticAt ℂ S 0) (hT : AnalyticAt ℂ T 0) {E : ℕ} (hE : 0 < E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      ∀ ω : ℂ, ω ^ E = 1 →
        (S (ω * t) = T t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u) := by
  have hfin := (power_fiber_finite_ncard_le E hE 1).1
  have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ ω : ℂ, ω ^ E = 1 →
      (S (ω * t) = T t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u) :=
    hfin.eventually_all.mpr fun ω _ => analytic_multiplier_comparison hS hT ω
  obtain ⟨ε, hε, ht⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hevent)
  exact ⟨ε, hε, fun t hnorm hne =>
    ht (by simpa only [dist_zero_right] using hnorm) hne⟩

/-- Distinct branch germs have no noncentral intersection after shrinking. This result uses
the actual images, and rules out all first-branch parameters, not just nearby ones. -/
theorem imageBranch_distinct_germs_disjoint {S T : ℂ → ℂ}
    (hS : AnalyticAt ℂ S 0) (hT : AnalyticAt ℂ T 0) {E : ℕ} (hE : 0 < E)
    (hdistinct : ∀ ω : ℂ, ω ^ E = 1 →
      ¬∀ᶠ u in 𝓝 (0 : ℂ), S (ω * u) = T u) (p₀ : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      ∀ u : ℂ, ImageBranch S E p₀ u ≠ ImageBranch T E p₀ t := by
  obtain ⟨ε, hε, hcompare⟩ := imageBranch_comparisons_radius hS hT hE
  refine ⟨ε, hε, fun t hnorm ht u hu => ?_⟩
  have hfirst : S u = T t := congrArg Prod.fst hu
  have hpow : u ^ E = t ^ E := add_left_cancel (congrArg Prod.snd hu)
  have hω : (u / t) ^ E = 1 := by rw [div_pow, hpow, div_self (pow_ne_zero _ ht)]
  apply hdistinct (u / t) hω
  apply (hcompare t hnorm ht _ hω).mp
  simpa only [div_mul_cancel₀ _ ht] using hfirst

/-- An equality after a root rotation gives equality of the local image germs. -/
theorem imageBranch_eq_images_of_rotated_germ {S T : ℂ → ℂ} {E : ℕ}
    (hE : 0 < E) {ω : ℂ} (hω : ω ^ E = 1)
    (heq : ∀ᶠ t in 𝓝 (0 : ℂ), S (ω * t) = T t) (p₀ : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ImageBranch S E p₀ '' {u : ℂ | ‖u‖ < δ} =
        ImageBranch T E p₀ '' {t : ℂ | ‖t‖ < δ} := by
  have hnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hE.ne'
  have hne : ω ≠ 0 := by intro h; simp [h] at hnorm
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨ε, hε, fun δ _ hδε => ?_⟩
  have himage : ∀ t : ℂ, ‖t‖ < δ →
      ImageBranch S E p₀ (ω * t) = ImageBranch T E p₀ t := by
    intro t ht
    apply Prod.ext
    · exact hlocal (by simpa only [dist_zero_right] using ht.trans_le hδε)
    · simp only [ImageBranch, mul_pow, hω, one_mul]
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    change ‖u‖ < δ at hu
    have hnorminv : ‖ω⁻¹ * u‖ = ‖u‖ := by simp only [norm_mul, norm_inv, hnorm, inv_one, one_mul]
    have ht : ‖ω⁻¹ * u‖ < δ := by simpa only [hnorminv] using hu
    refine ⟨ω⁻¹ * u, ht, ?_⟩
    simpa only [← mul_assoc, mul_inv_cancel₀ hne, one_mul] using (himage _ ht).symm
  · rintro ⟨t, ht, rfl⟩
    change ‖t‖ < δ at ht
    refine ⟨ω * t, ?_, himage t ht⟩
    change ‖ω * t‖ < δ
    simpa only [norm_mul, hnorm, one_mul] using ht

/-- Uniform comparison of all pairs in a finite analytic family, including every root
rotation. This is the finite comparison input for inverse-root families with a common
power parameter; no quotient or normalization is assumed. -/
theorem finite_imageBranch_comparisons_radius {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} (hS : ∀ i, AnalyticAt ℂ (S i) 0) {N : ℕ} (hN : 0 < N) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      ∀ i j : ι, ∀ ω : ℂ, ω ^ N = 1 →
        (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u) := by
  have hroots := (power_fiber_finite_ncard_le N hN 1).1
  have hevent : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ i j : ι, ∀ ω : ℂ, ω ^ N = 1 →
      (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact hroots.eventually_all.mpr fun ω _ =>
      analytic_multiplier_comparison (hS i) (hS j) ω
  obtain ⟨ε, hε, ht⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hevent)
  exact ⟨ε, hε, fun t hnorm hne =>
    ht (by simpa only [dist_zero_right] using hnorm) hne⟩

/-- The collision class of each member of a finite analytic family is an actual finite
set of indices, and is constant throughout a sufficiently small punctured disk. -/
theorem finite_imageBranch_classes_radius {ι : Type*} [Finite ι]
    {S : ι → ℂ → ℂ} (hS : ∀ i, AnalyticAt ℂ (S i) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 → ∀ j : ι,
      {i : ι | S i t = S j t} =
        {i : ι | ∀ᶠ u in 𝓝 (0 : ℂ), S i u = S j u} := by
  obtain ⟨ε, hε, ht⟩ := finite_imageBranch_comparisons_radius hS (N := 1) (by decide)
  refine ⟨ε, hε, fun t hnorm hne j => ?_⟩
  ext i
  simpa only [Set.mem_ofPred_eq, one_mul] using ht t hnorm hne i j 1 (one_pow 1)

end

end MaximumModulus
