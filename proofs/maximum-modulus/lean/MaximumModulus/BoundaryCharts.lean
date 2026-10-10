module

public import MaximumModulus.GlobalCharts
public import MaximumModulus.HighCountCapture
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# Constructed inverse-root charts at the omitted common value

The chart centers in this file are ordinary physical coordinates, not elements of
`SphereCorrespondenceSource`, whose common value is required to avoid the omitted value.
The high-count capture comes from the actual compact annulus survivor theorem.
-/

open Set Filter Metric
open scoped Topology ComplexConjugate OnePoint

namespace MaximumModulus

noncomputable section

/-- A genuine finite-value power coordinate, without excluding its central value. -/
structure SphereValueCoordinateChart (A : ℂ → OnePoint ℂ) (p₀ a : ℂ) where
  k : ℕ
  pos : 0 < k
  e : OpenPartialHomeomorph ℂ ℂ
  mem : a ∈ e.source
  center : e a = 0
  inverseCenter : e.symm 0 = a
  analytic : AnalyticAt ℂ e.symm 0
  value : ∀ z : ℂ, z ∈ e.source → A z = ((p₀ + (e z) ^ k : ℂ) : OnePoint ℂ)

theorem sphereValueCoordinateChart_exists {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) {p₀ a : ℂ}
    (ha : sphereLogDerivative m g a = (p₀ : OnePoint ℂ)) :
    Nonempty (SphereValueCoordinateChart (sphereLogDerivative m g) p₀ a) := by
  have hregular := (sphereLogDerivative_eq_coe m g a p₀).mp ha
  obtain ⟨k, hk, e, hmem, hcenter, hinverse, hanalytic, hvalue⟩ :=
    sphereLogDerivative_regular_inverse_chart hg hg0 hnm hfactor hregular.1
  exact ⟨⟨k, hk, e, hmem, hcenter, hinverse, hanalytic,
    fun z hz => by simpa only [hregular.2] using hvalue z hz⟩⟩

/-- The two coordinate charts of a physical pair at any finite common value. -/
structure SphereValuePairChart (A B : ℂ → OnePoint ℂ) (p₀ : ℂ) (ab : ℂ × ℂ) where
  first : SphereValueCoordinateChart A p₀ ab.1
  second : SphereValueCoordinateChart B p₀ ab.2

def SphereValuePairChart.rootPair {A B : ℂ → OnePoint ℂ} {p₀ : ℂ} {ab : ℂ × ℂ}
    (C : SphereValuePairChart A B p₀ ab) (lA lB : ℕ) (η : ℂ × ℂ) (t : ℂ) : ℂ × ℂ :=
  (C.first.e.symm (η.1 * t ^ lA), C.second.e.symm (η.2 * t ^ lB))

def SphereValuePairChart.rootProduct {A B : ℂ → OnePoint ℂ} {p₀ : ℂ} {ab : ℂ × ℂ}
    (C : SphereValuePairChart A B p₀ ab) (lA lB : ℕ) (η : ℂ × ℂ) (t : ℂ) : ℂ :=
  (C.rootPair lA lB η t).1 * (C.rootPair lA lB η t).2

theorem SphereValuePairChart.analytic_rootProduct {A B : ℂ → OnePoint ℂ}
    {p₀ : ℂ} {ab : ℂ × ℂ} (C : SphereValuePairChart A B p₀ ab)
    {lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB) (η : ℂ × ℂ) :
    AnalyticAt ℂ (C.rootProduct lA lB η) 0 :=
  (analytic_inverseRoot_branch C.first.analytic hA η.1).mul
    (analytic_inverseRoot_branch C.second.analytic hB η.2)

theorem SphereValuePairChart.rootPair_zero {A B : ℂ → OnePoint ℂ}
    {p₀ : ℂ} {ab : ℂ × ℂ} (C : SphereValuePairChart A B p₀ ab)
    {lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB) (η : ℂ × ℂ) :
    C.rootPair lA lB η 0 = ab := by
  simp [SphereValuePairChart.rootPair, zero_pow hA.ne', zero_pow hB.ne',
    C.first.inverseCenter, C.second.inverseCenter]

/-- A captured actual pair is one of the finite common-power inverse roots. -/
theorem SphereValuePairChart.capture_rootPair {A B : ℂ → OnePoint ℂ}
    {p₀ : ℂ} {ab : ℂ × ℂ} (C : SphereValuePairChart A B p₀ ab)
    {N lA lB : ℕ} (hN_A : N = C.first.k * lA) (hN_B : N = C.second.k * lB)
    {t : ℂ} (ht : t ≠ 0) {zw : ℂ × ℂ}
    (hz : zw.1 ∈ C.first.e.source) (hw : zw.2 ∈ C.second.e.source)
    (hAvalue : A zw.1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ))
    (hBvalue : B zw.2 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ)) :
    ∃ η ∈ RootPairIndices C.first.k C.second.k, C.rootPair lA lB η t = zw := by
  have hA : (C.first.e zw.1) ^ C.first.k = t ^ N :=
    add_left_cancel (OnePoint.coe_injective ((C.first.value _ hz).symm.trans hAvalue))
  have hB : (C.second.e zw.2) ^ C.second.k = t ^ N :=
    add_left_cancel (OnePoint.coe_injective ((C.second.value _ hw).symm.trans hBvalue))
  let ω : ℂ := C.first.e zw.1 / t ^ lA
  let ξ : ℂ := C.second.e zw.2 / t ^ lB
  have hω : ω ^ C.first.k = 1 := by
    dsimp [ω]
    rw [div_pow, hA, ← pow_mul, Nat.mul_comm lA C.first.k, ← hN_A,
      div_self (pow_ne_zero _ ht)]
  have hξ : ξ ^ C.second.k = 1 := by
    dsimp [ξ]
    rw [div_pow, hB, ← pow_mul, Nat.mul_comm lB C.second.k, ← hN_B,
      div_self (pow_ne_zero _ ht)]
  refine ⟨(ω, ξ), ⟨hω, hξ⟩, ?_⟩
  apply Prod.ext
  · simp only [SphereValuePairChart.rootPair, ω, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
    exact C.first.e.left_inv hz
  · simp only [SphereValuePairChart.rootPair, ξ, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
    exact C.second.e.left_inv hw

theorem SphereValuePairChart.rootPair_eventually_values {A B : ℂ → OnePoint ℂ}
    {p₀ : ℂ} {ab : ℂ × ℂ} (C : SphereValuePairChart A B p₀ ab)
    {N lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB)
    (hN_A : N = C.first.k * lA) (hN_B : N = C.second.k * lB)
    {η : ℂ × ℂ} (hη : η ∈ RootPairIndices C.first.k C.second.k) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      A (C.rootPair lA lB η t).1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      B (C.rootPair lA lB η t).2 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) := by
  have hzeroA : (0 : ℂ) ∈ C.first.e.target :=
    C.first.center ▸ C.first.e.map_source C.first.mem
  have hzeroB : (0 : ℂ) ∈ C.second.e.target :=
    C.second.center ▸ C.second.e.map_source C.second.mem
  have htoA : Tendsto (fun t : ℂ => η.1 * t ^ lA) (𝓝 0) (𝓝 0) := by
    convert! (continuous_const.mul (continuous_id.pow lA)).continuousAt.tendsto using 1 <;>
      first | simp [hA.ne'] | infer_instance
  have htoB : Tendsto (fun t : ℂ => η.2 * t ^ lB) (𝓝 0) (𝓝 0) := by
    convert! (continuous_const.mul (continuous_id.pow lB)).continuousAt.tendsto using 1 <;>
      first | simp [hB.ne'] | infer_instance
  filter_upwards [htoA.eventually (C.first.e.open_target.mem_nhds hzeroA),
    htoB.eventually (C.second.e.open_target.mem_nhds hzeroB)] with t htA htB
  constructor
  · change A (C.first.e.symm (η.1 * t ^ lA)) = _
    rw [C.first.value _ (C.first.e.map_target htA), C.first.e.right_inv htA, mul_pow,
      hη.1, one_mul, ← pow_mul, Nat.mul_comm lA C.first.k, ← hN_A]
  · change B (C.second.e.symm (η.2 * t ^ lB)) = _
    rw [C.second.value _ (C.second.e.map_target htB), C.second.e.right_inv htB, mul_pow,
      hη.2, one_mul, ← pow_mul, Nat.mul_comm lB C.second.k, ← hN_B]

abbrev OmittedAnnulusRoots (m : ℕ) (g : ℂ → ℂ) (ε T : ℝ) :=
  {z : ℂ // z ∈ CoordinateAnnulus ε T ∧
    sphereLogDerivative m g z = ((m : ℂ) : OnePoint ℂ)}

abbrev OmittedAnnulusPairCenters (m : ℕ) (g : ℂ → ℂ) (ε T : ℝ) :=
  OmittedAnnulusRoots m g ε T × OmittedAnnulusRoots m (reflection g) ε T

def omittedPairCenter {m : ℕ} {g : ℂ → ℂ} {ε T : ℝ}
    (i : OmittedAnnulusPairCenters m g ε T) : ℂ × ℂ := (i.1.val, i.2.val)

/-- The actual high-count locus near the omitted value is captured by a constructed
finite common-power family of genuine coordinate inverse roots. This is containment,
not an assertion that these charts enumerate every escaping physical pair. -/
theorem logDerivative_high_count_omitted_root_family {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S : ℝ,
      Finite (OmittedAnnulusPairCenters m g ε (S / ε)) ∧
      ∃ C : ∀ i : OmittedAnnulusPairCenters m g ε (S / ε),
          SphereValuePairChart (sphereLogDerivative m g)
            (sphereLogDerivative m (reflection g)) (m : ℂ) (omittedPairCenter i),
        ∃ N : ℕ, ∃ lA lB : OmittedAnnulusPairCenters m g ε (S / ε) → ℕ,
          0 < N ∧
          (∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).first.k * lA i ∧
            N = (C i).second.k * lB i) ∧
          (∀ i η, AnalyticAt ℂ ((C i).rootProduct (lA i) (lB i) η) 0) ∧
          ∃ W : Set (OnePoint ℂ), IsOpen W ∧ ((m : ℂ) : OnePoint ℂ) ∈ W ∧
            ∀ y ∈ LogDerivativeHighCount m g
              (2 * analyticOrderNatAt
                (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0),
              ‖y.1‖ ≤ S → y.2 ∈ W → ∀ t : ℂ, t ≠ 0 →
                y.2 = (((m : ℂ) + t ^ N : ℂ) : OnePoint ℂ) →
                ∃ i : OmittedAnnulusPairCenters m g ε (S / ε),
                  ∃ η ∈ RootPairIndices (C i).first.k (C i).second.k,
                    (C i).rootProduct (lA i) (lB i) η t = y.1 := by
  classical
  obtain ⟨ε, hε, hcapture⟩ :=
    logDerivative_high_count_omitted_value_capture hg hg0 hnm hfactor
  refine ⟨ε, hε, fun S => ?_⟩
  obtain ⟨hFA, hFB⟩ := finite_omitted_roots_in_coordinate_annulus hg hg0 hnm hfactor
    ε (S / ε)
  have : Finite (OmittedAnnulusRoots m g ε (S / ε)) := hFA.to_subtype
  have : Finite (OmittedAnnulusRoots m (reflection g) ε (S / ε)) := hFB.to_subtype
  let CA : ∀ a : OmittedAnnulusRoots m g ε (S / ε),
      SphereValueCoordinateChart (sphereLogDerivative m g) (m : ℂ) a.val :=
    fun a => Classical.choice
      (sphereValueCoordinateChart_exists hg hg0 hnm hfactor a.property.2)
  have hgR := entire_reflection hg
  have hgR0 : reflection g 0 ≠ 0 := by simpa [reflection] using hg0
  have hnmR : ¬IsMonomial (reflection f) :=
    fun h => hnm (isMonomial_of_reflection_isMonomial h)
  let CB : ∀ b : OmittedAnnulusRoots m (reflection g) ε (S / ε),
      SphereValueCoordinateChart (sphereLogDerivative m (reflection g)) (m : ℂ) b.val :=
    fun b => Classical.choice
      (sphereValueCoordinateChart_exists hgR hgR0 hnmR (reflection_factor hfactor) b.property.2)
  let C : ∀ i : OmittedAnnulusPairCenters m g ε (S / ε),
      SphereValuePairChart (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) (m : ℂ) (omittedPairCenter i) :=
    fun i => ⟨CA i.1, CB i.2⟩
  obtain ⟨N, hN, hdiv⟩ := finite_orders_common_power (fun i => (C i).first.k)
    (fun i => (C i).second.k) (fun i => (C i).first.pos) (fun i => (C i).second.pos)
  choose lA lB hposA hposB hN_A hN_B using hdiv
  refine ⟨inferInstance, C, N, lA, lB, hN,
    fun i => ⟨hposA i, hposB i, hN_A i, hN_B i⟩,
    fun i η => (C i).analytic_rootProduct (hposA i) (hposB i) η, ?_⟩
  let U : Set ℂ := ⋃ a, (CA a).e.source
  let V : Set ℂ := ⋃ b, (CB b).e.source
  have hU : IsOpen U := isOpen_iUnion fun a => (CA a).e.open_source
  have hV : IsOpen V := isOpen_iUnion fun b => (CB b).e.open_source
  obtain ⟨W, hW, hcW, hcaptureW⟩ := hcapture S U V hU hV
    (fun a ha => mem_iUnion.mpr ⟨⟨a, ha⟩, (CA ⟨a, ha⟩).mem⟩)
    (fun b hb => mem_iUnion.mpr ⟨⟨b, hb⟩, (CB ⟨b, hb⟩).mem⟩)
  refine ⟨W, hW, hcW, ?_⟩
  intro y hy hS hp t ht htvalue
  obtain ⟨zw, hzw, hz, hw⟩ := hcaptureW y hy hS hp
  obtain ⟨a, ha⟩ := mem_iUnion.mp hz
  obtain ⟨b, hb⟩ := mem_iUnion.mp hw
  let i : OmittedAnnulusPairCenters m g ε (S / ε) := (a, b)
  obtain ⟨η, hη, hpair⟩ := (C i).capture_rootPair (hN_A i) (hN_B i) ht ha hb
    (hzw.2.1.trans htvalue) (hzw.2.2.trans htvalue)
  refine ⟨i, η, hη, ?_⟩
  change ((C i).rootPair (lA i) (lB i) η t).1 *
    ((C i).rootPair (lA i) (lB i) η t).2 = y.1
  rw [hpair]
  exact hzw.1

/-- Flattened finite indices retain the central coordinate pair and its roots of unity. -/
def SphereValueRootIndex {ι : Type*} {A B : ℂ → OnePoint ℂ} {p₀ : ℂ}
    {ab : ι → ℂ × ℂ} (C : ∀ i : ι, SphereValuePairChart A B p₀ (ab i)) :=
  Σ i : ι, RootPairIndices (C i).first.k (C i).second.k

instance {ι : Type*} [Finite ι] {A B : ℂ → OnePoint ℂ} {p₀ : ℂ}
    {ab : ι → ℂ × ℂ} (C : ∀ i : ι, SphereValuePairChart A B p₀ (ab i)) :
    Finite (SphereValueRootIndex C) := by
  let : ∀ i : ι, Finite (RootPairIndices (C i).first.k (C i).second.k) :=
    fun i => (rootPairIndices_finite (C i).first.pos (C i).second.pos).to_subtype
  unfold SphereValueRootIndex
  infer_instance

def sphereValueRootPair {ι : Type*} {A B : ℂ → OnePoint ℂ} {p₀ : ℂ}
    {ab : ι → ℂ × ℂ} (C : ∀ i : ι, SphereValuePairChart A B p₀ (ab i))
    (lA lB : ι → ℕ) (j : SphereValueRootIndex C) : ℂ → ℂ × ℂ :=
  (C j.1).rootPair (lA j.1) (lB j.1) j.2.val

theorem sphereValueRootPair_analytic {ι : Type*} {A B : ℂ → OnePoint ℂ} {p₀ : ℂ}
    {ab : ι → ℂ × ℂ} (C : ∀ i : ι, SphereValuePairChart A B p₀ (ab i))
    (lA lB : ι → ℕ) (hA : ∀ i, 0 < lA i) (hB : ∀ i, 0 < lB i)
    (j : SphereValueRootIndex C) :
    AnalyticAt ℂ (fun t => (sphereValueRootPair C lA lB j t).1) 0 ∧
      AnalyticAt ℂ (fun t => (sphereValueRootPair C lA lB j t).2) 0 :=
  ⟨analytic_inverseRoot_branch (C j.1).first.analytic (hA j.1) j.2.val.1,
    analytic_inverseRoot_branch (C j.1).second.analytic (hB j.1) j.2.val.2⟩

theorem sphereValueRootFamily_values_radius {ι : Type*} [Finite ι]
    {A B : ℂ → OnePoint ℂ} {p₀ : ℂ} {ab : ι → ℂ × ℂ}
    (C : ∀ i : ι, SphereValuePairChart A B p₀ (ab i))
    {N : ℕ} (lA lB : ι → ℕ)
    (horders : ∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).first.k * lA i ∧
      N = (C i).second.k * lB i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℂ, ‖t‖ < ρ → ∀ j : SphereValueRootIndex C,
      A (sphereValueRootPair C lA lB j t).1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      B (sphereValueRootPair C lA lB j t).2 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j : SphereValueRootIndex C,
      A (sphereValueRootPair C lA lB j t).1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      B (sphereValueRootPair C lA lB j t).2 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (C j.1).rootPair_eventually_values (horders j.1).1 (horders j.1).2.1
      (horders j.1).2.2.1 (horders j.1).2.2.2 j.2.property
  obtain ⟨ρ, hρ, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ρ, hρ, fun t ht => hlocal (by simpa only [dist_zero_right] using ht)⟩

/-- A finite family of actual analytic physical pairs contains every bounded high-count
target sufficiently close to the omitted value. Any desired positive raw disk radius
is obtained by shrinking the value neighborhood to its Nth-power cylinder. -/
theorem logDerivative_high_count_omitted_finite_image_cover {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ S : ℝ,
      ∃ ι : Type, Finite ι ∧ ∃ N : ℕ, 0 < N ∧ ∃ P : ι → ℂ → ℂ × ℂ,
        (∀ j, AnalyticAt ℂ (fun t => (P j t).1) 0 ∧
          AnalyticAt ℂ (fun t => (P j t).2) 0) ∧
        (∀ j, (P j 0).1 ∈ CoordinateAnnulus ε (S / ε) ∧
          (P j 0).2 ∈ CoordinateAnnulus ε (S / ε) ∧
          sphereLogDerivative m g (P j 0).1 = ((m : ℂ) : OnePoint ℂ) ∧
          sphereLogDerivative m (reflection g) (P j 0).2 = ((m : ℂ) : OnePoint ℂ)) ∧
        (∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℂ, ‖t‖ < ρ → ∀ j,
          sphereLogDerivative m g (P j t).1 = (((m : ℂ) + t ^ N : ℂ) : OnePoint ℂ) ∧
          sphereLogDerivative m (reflection g) (P j t).2 =
            (((m : ℂ) + t ^ N : ℂ) : OnePoint ℂ)) ∧
        ∃ W : Set (OnePoint ℂ), IsOpen W ∧ ((m : ℂ) : OnePoint ℂ) ∈ W ∧
          ∀ (s p : ℂ), (s, (p : OnePoint ℂ)) ∈ LogDerivativeHighCount m g
            (2 * analyticOrderNatAt
              (fun z => normalizedLogDerivative m g z - (m : ℂ)) 0) →
            ‖s‖ ≤ S → (p : OnePoint ℂ) ∈ W → ∀ δ : ℝ, 0 < δ →
              ‖p - (m : ℂ)‖ < δ ^ N →
              (s, p) ∈ ⋃ j, (fun t : ℂ => ((P j t).1 * (P j t).2, (m : ℂ) + t ^ N)) ''
                (ball (0 : ℂ) δ \ {0}) := by
  classical
  obtain ⟨ε, hε, hfamily⟩ := logDerivative_high_count_omitted_root_family hg hg0 hnm hfactor
  refine ⟨ε, hε, fun S => ?_⟩
  obtain ⟨hfinite, C, N, lA, lB, hN, horders, _, W, hW, hcW, hcapture⟩ := hfamily S
  have : Finite (OmittedAnnulusPairCenters m g ε (S / ε)) := hfinite
  let ι := SphereValueRootIndex C
  let P : ι → ℂ → ℂ × ℂ := sphereValueRootPair C lA lB
  refine ⟨ι, inferInstance, N, hN, P,
    sphereValueRootPair_analytic C lA lB (fun i => (horders i).1)
      (fun i => (horders i).2.1), ?_, ?_, W, hW, hcW, ?_⟩
  · intro j
    have hjzero : P j 0 = omittedPairCenter j.1 :=
      (C j.1).rootPair_zero (horders j.1).1 (horders j.1).2.1 j.2.val
    rw [hjzero]
    exact ⟨j.1.1.property.1, j.1.2.property.1, j.1.1.property.2, j.1.2.property.2⟩
  · exact sphereValueRootFamily_values_radius C lA lB horders
  · intro s p hy hS hp δ hδ hsmall
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (p - (m : ℂ)) hN
    have htne : t ≠ 0 := by
      intro htzero
      have hpm : p = (m : ℂ) := sub_eq_zero.mp (by simpa [htzero, zero_pow hN.ne'] using ht.symm)
      exact hy.2.1 (by simp [hpm])
    have htnorm : ‖t‖ < δ := by
      apply lt_of_pow_lt_pow_left₀ N hδ.le
      rw [← norm_pow, ht]
      exact hsmall
    have hvalue : (p : OnePoint ℂ) = (((m : ℂ) + t ^ N : ℂ) : OnePoint ℂ) := by
      congr 1
      rw [ht]
      ring
    obtain ⟨i, η, hη, hproduct⟩ := hcapture (s, (p : OnePoint ℂ)) hy hS hp t htne hvalue
    let j : ι := ⟨i, ⟨η, hη⟩⟩
    apply mem_iUnion.mpr
    refine ⟨j, t, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using htnorm
    · simpa only [mem_singleton_iff] using htne
    · apply Prod.ext
      · exact hproduct
      · change (m : ℂ) + t ^ N = p
        rw [ht]
        ring

end

end MaximumModulus
