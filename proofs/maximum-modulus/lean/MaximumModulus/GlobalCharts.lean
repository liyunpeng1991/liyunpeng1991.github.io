module

public import MaximumModulus.PoleChart
public import MaximumModulus.InversePairFamily
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-!
# Finite chart capture for the actual spherical correspondence

Properness captures every nearby physical pair in the union of the charts of a finite
central fiber. The charts at finite common values are constructed from the genuine
logarithmic derivative germs. No local-chart cover is an assumption of the construction.
-/

open Set Filter
open scoped Topology ComplexConjugate

namespace MaximumModulus

noncomputable section

/-- A proper map captures all nearby preimages in any open neighborhood of its central
fiber. This uses the closed-map consequence of properness. -/
theorem proper_map_neighborhood_capture {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {F : X → Y} (hF : IsProperMap F) {y : Y} {U : Set X}
    (hU : IsOpen U) (hfiber : ∀ x : X, F x = y → x ∈ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∀ x : X, F x ∈ V → x ∈ U := by
  let V := (F '' Uᶜ)ᶜ
  have hV : IsOpen V := (hF.isClosedMap Uᶜ hU.isClosed_compl).isOpen_compl
  have hy : y ∈ V := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hfiber x hxy)
  refine ⟨V, hV, hy, fun x hx => ?_⟩
  by_contra hxu
  exact hx ⟨x, hxu, rfl⟩

theorem reflection_factor {f g : ℂ → ℂ} {m : ℕ}
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) :
    ∀ z : ℂ, reflection f z = z ^ m * reflection g z := by
  intro z
  simp [reflection, hfactor]

theorem isMonomial_of_reflection_isMonomial {f : ℂ → ℂ}
    (hf : IsMonomial (reflection f)) : IsMonomial f := by
  obtain ⟨c, m, hc, hmon⟩ := hf
  refine ⟨conj c, m, ?_, fun z => ?_⟩
  · simpa using hc
  · simpa [reflection] using congrArg conj (hmon (conj z))

abbrev SphereCentralFiber (m : ℕ) (g : ℂ → ℂ) (y : SphereCorrespondenceTarget m) :=
  {x : SphereCorrespondenceSource m g // sphereCorrespondenceMap m g x = y}

/-- Constructed regular coordinate charts for one actual central physical pair. -/
structure RegularSpherePairChart (m : ℕ) (g : ℂ → ℂ) (p₀ : ℂ)
    (x : SphereCorrespondenceSource m g) where
  kA : ℕ
  kB : ℕ
  posA : 0 < kA
  posB : 0 < kB
  eA : OpenPartialHomeomorph ℂ ℂ
  eB : OpenPartialHomeomorph ℂ ℂ
  memA : x.val.1 ∈ eA.source
  memB : x.val.2 ∈ eB.source
  centerA : eA x.val.1 = 0
  centerB : eB x.val.2 = 0
  inverseCenterA : eA.symm 0 = x.val.1
  inverseCenterB : eB.symm 0 = x.val.2
  analyticA : AnalyticAt ℂ eA.symm 0
  analyticB : AnalyticAt ℂ eB.symm 0
  valueA : ∀ z : ℂ, z ∈ eA.source →
    sphereLogDerivative m g z = ((p₀ + (eA z) ^ kA : ℂ) : OnePoint ℂ)
  valueB : ∀ z : ℂ, z ∈ eB.source →
    sphereLogDerivative m (reflection g) z = ((p₀ + (eB z) ^ kB : ℂ) : OnePoint ℂ)

def RegularSpherePairChart.source {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x) :
    Set (SphereCorrespondenceSource m g) :=
  {x' | x'.val.1 ∈ C.eA.source ∧ x'.val.2 ∈ C.eB.source}

theorem RegularSpherePairChart.open_source {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x) :
    IsOpen C.source := by
  change IsOpen (Subtype.val ⁻¹' (C.eA.source ×ˢ C.eB.source))
  exact (C.eA.open_source.prod C.eB.open_source).preimage continuous_subtype_val

theorem RegularSpherePairChart.mem_source {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x) :
    x ∈ C.source := ⟨C.memA, C.memB⟩

theorem regularSpherePairChart_exists {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) (p₀ : ℂ)
    (x : SphereCorrespondenceSource m g)
    (hx : sphereLogDerivative m g x.val.1 = (p₀ : OnePoint ℂ)) :
    Nonempty (RegularSpherePairChart m g p₀ x) := by
  have hA := (sphereLogDerivative_eq_coe m g x.val.1 p₀).mp hx
  have hB := (sphereLogDerivative_eq_coe m (reflection g) x.val.2 p₀).mp
    (x.property.1.symm.trans hx)
  have hgR := entire_reflection hg
  have hgR0 : reflection g 0 ≠ 0 := by simpa [reflection] using hg0
  have hnmR : ¬IsMonomial (reflection f) := fun h => hnm (isMonomial_of_reflection_isMonomial h)
  obtain ⟨kA, hkA, eA, ha, hzeroA, hcenterA, hψA, hpowerA⟩ :=
    sphereLogDerivative_regular_inverse_chart hg hg0 hnm hfactor hA.1
  obtain ⟨kB, hkB, eB, hb, hzeroB, hcenterB, hψB, hpowerB⟩ :=
    sphereLogDerivative_regular_inverse_chart hgR hgR0 hnmR (reflection_factor hfactor) hB.1
  refine ⟨⟨kA, kB, hkA, hkB, eA, eB, ha, hb, hzeroA, hzeroB, hcenterA, hcenterB,
    hψA, hψB, ?_, ?_⟩⟩
  · intro z hz
    simpa only [hA.2] using hpowerA z hz
  · intro z hz
    simpa only [hB.2] using hpowerB z hz

/-- A finite family of positive orders has a positive common multiple, obtained by a
finite product. No least-common-multiple construction is needed. -/
theorem finite_orders_common_power {ι : Type*} [Finite ι] (kA kB : ι → ℕ)
    (hA : ∀ i, 0 < kA i) (hB : ∀ i, 0 < kB i) :
    ∃ N : ℕ, 0 < N ∧ ∀ i : ι,
      ∃ lA lB : ℕ, 0 < lA ∧ 0 < lB ∧ N = kA i * lA ∧ N = kB i * lB := by
  classical
  let _ := Fintype.ofFinite ι
  let N : ℕ := ∏ i : ι, kA i * kB i
  have hN : 0 < N := Finset.prod_pos fun i _ => Nat.mul_pos (hA i) (hB i)
  refine ⟨N, hN, fun i => ?_⟩
  have hi : kA i * kB i ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨lA, hlA⟩ := (dvd_mul_right (kA i) (kB i)).trans hi
  obtain ⟨lB, hlB⟩ := (dvd_mul_left (kB i) (kA i)).trans hi
  have hposA : 0 < lA := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hN.ne' (by rw [hlA, hzero, mul_zero])
  have hposB : 0 < lB := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hN.ne' (by rw [hlB, hzero, mul_zero])
  exact ⟨lA, lB, hposA, hposB, hlA, hlB⟩

def RegularSpherePairChart.rootPair {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    (lA lB : ℕ) (η : ℂ × ℂ) (t : ℂ) : ℂ × ℂ :=
  (C.eA.symm (η.1 * t ^ lA), C.eB.symm (η.2 * t ^ lB))

def RegularSpherePairChart.rootProduct {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    (lA lB : ℕ) (η : ℂ × ℂ) (t : ℂ) : ℂ :=
  (C.rootPair lA lB η t).1 * (C.rootPair lA lB η t).2

theorem RegularSpherePairChart.analytic_rootProduct {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB) (η : ℂ × ℂ) :
    AnalyticAt ℂ (C.rootProduct lA lB η) 0 :=
  (analytic_inverseRoot_branch C.analyticA hA η.1).mul
    (analytic_inverseRoot_branch C.analyticB hB η.2)

/-- Every actual pair captured in a chart product has one of its explicit inverse-root
parameters. This algebraic capture holds for every nonzero common parameter. -/
theorem RegularSpherePairChart.capture_rootPair {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {N lA lB : ℕ} (hN_A : N = C.kA * lA) (hN_B : N = C.kB * lB)
    {t : ℂ} (ht : t ≠ 0) {x' : SphereCorrespondenceSource m g} (hx' : x' ∈ C.source)
    (hvalue : sphereLogDerivative m g x'.val.1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ)) :
    ∃ η ∈ RootPairIndices C.kA C.kB, C.rootPair lA lB η t = x'.val := by
  have hA : (C.eA x'.val.1) ^ C.kA = t ^ N :=
    add_left_cancel (OnePoint.coe_injective ((C.valueA _ hx'.1).symm.trans hvalue))
  have hB : (C.eB x'.val.2) ^ C.kB = t ^ N :=
    add_left_cancel (OnePoint.coe_injective
      ((C.valueB _ hx'.2).symm.trans (x'.property.1.symm.trans hvalue)))
  let ω : ℂ := C.eA x'.val.1 / t ^ lA
  let ξ : ℂ := C.eB x'.val.2 / t ^ lB
  have hω : ω ^ C.kA = 1 := by
    dsimp [ω]
    rw [div_pow, hA, ← pow_mul, Nat.mul_comm lA C.kA, ← hN_A, div_self (pow_ne_zero _ ht)]
  have hξ : ξ ^ C.kB = 1 := by
    dsimp [ξ]
    rw [div_pow, hB, ← pow_mul, Nat.mul_comm lB C.kB, ← hN_B, div_self (pow_ne_zero _ ht)]
  refine ⟨(ω, ξ), ⟨hω, hξ⟩, ?_⟩
  apply Prod.ext
  · simp only [RegularSpherePairChart.rootPair, ω, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
    exact C.eA.left_inv hx'.1
  · simp only [RegularSpherePairChart.rootPair, ξ, div_mul_cancel₀ _ (pow_ne_zero _ ht)]
    exact C.eB.left_inv hx'.2

/-- At every finite central target, a finite family of constructed regular chart products
captures every nearby actual preimage of the proper spherical correspondence. -/
theorem sphereCorrespondence_regular_chart_capture {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) (y : SphereCorrespondenceTarget m)
    (p₀ : ℂ) (hp₀ : y.val.2 = (p₀ : OnePoint ℂ)) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val,
        ∃ V : Set (SphereCorrespondenceTarget m), IsOpen V ∧ y ∈ V ∧
          ∀ x : SphereCorrespondenceSource m g, sphereCorrespondenceMap m g x ∈ V →
            ∃ i : SphereCentralFiber m g y, x ∈ (C i).source := by
  classical
  have hfinite : {x : SphereCorrespondenceSource m g | sphereCorrespondenceMap m g x = y}.Finite := by
    simpa only [Set.preimage_singleton] using sphereCorrespondenceMap_finite_fiber hg hg0 m y
  refine ⟨hfinite.to_subtype, ?_⟩
  have hchart : ∀ i : SphereCentralFiber m g y, Nonempty (RegularSpherePairChart m g p₀ i.val) := by
    intro i
    apply regularSpherePairChart_exists hg hg0 hnm hfactor
    have hvalue := congrArg (fun q : SphereCorrespondenceTarget m => q.val.2) i.property
    exact hvalue.trans hp₀
  let C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val :=
    fun i => Classical.choice (hchart i)
  let U : Set (SphereCorrespondenceSource m g) := ⋃ i, (C i).source
  have hU : IsOpen U := isOpen_iUnion fun i => (C i).open_source
  have hcover : ∀ x : SphereCorrespondenceSource m g, sphereCorrespondenceMap m g x = y → x ∈ U := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (C ⟨x, hx⟩).mem_source⟩
  obtain ⟨V, hV, hy, hcapture⟩ := proper_map_neighborhood_capture
    (isProperMap_sphereCorrespondenceMap hg hg0 m) hU hcover
  exact ⟨C, V, hV, hy, fun x hx => mem_iUnion.mp (hcapture x hx)⟩

/-- Properness and the constructed charts produce a genuine common-exponent finite root
cover of every nearby actual physical fiber. The exponent is constructed from the finite
family of local orders. -/
theorem sphereCorrespondence_regular_root_capture {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) (y : SphereCorrespondenceTarget m)
    (p₀ : ℂ) (hp₀ : y.val.2 = (p₀ : OnePoint ℂ)) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val,
        ∃ N : ℕ, ∃ lA lB : SphereCentralFiber m g y → ℕ,
          0 < N ∧
          (∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).kA * lA i ∧ N = (C i).kB * lB i) ∧
          (∀ i η, AnalyticAt ℂ ((C i).rootProduct (lA i) (lB i) η) 0) ∧
          ∃ V : Set (SphereCorrespondenceTarget m), IsOpen V ∧ y ∈ V ∧
            ∀ t : ℂ, t ≠ 0 → ∀ x : SphereCorrespondenceSource m g,
              sphereCorrespondenceMap m g x ∈ V →
              sphereLogDerivative m g x.val.1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) →
                ∃ i : SphereCentralFiber m g y,
                  ∃ η ∈ RootPairIndices (C i).kA (C i).kB,
                    (C i).rootPair (lA i) (lB i) η t = x.val := by
  obtain ⟨hfinite, C, V, hV, hy, hcapture⟩ :=
    sphereCorrespondence_regular_chart_capture hg hg0 hnm hfactor y p₀ hp₀
  have : Finite (SphereCentralFiber m g y) := hfinite
  obtain ⟨N, hN, hdiv⟩ := finite_orders_common_power (fun i => (C i).kA)
    (fun i => (C i).kB) (fun i => (C i).posA) (fun i => (C i).posB)
  choose lA lB hposA hposB hN_A hN_B using hdiv
  refine ⟨hfinite, C, N, lA, lB, hN, fun i => ⟨hposA i, hposB i, hN_A i, hN_B i⟩,
    fun i η => (C i).analytic_rootProduct (hposA i) (hposB i) η, V, hV, hy, ?_⟩
  intro t ht x hx hvalue
  obtain ⟨i, hi⟩ := hcapture x hx
  exact ⟨i, (C i).capture_rootPair (hN_A i) (hN_B i) ht hi hvalue⟩

/-- Every inverse-root parameter of a constructed chart gives genuine common spherical
values on a neighborhood of zero. This is the forward direction of the physical cover. -/
theorem RegularSpherePairChart.rootPair_eventually_values {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {N lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB)
    (hN_A : N = C.kA * lA) (hN_B : N = C.kB * lB)
    {η : ℂ × ℂ} (hη : η ∈ RootPairIndices C.kA C.kB) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      η.1 * t ^ lA ∈ C.eA.target ∧ η.2 * t ^ lB ∈ C.eB.target ∧
      sphereLogDerivative m g (C.rootPair lA lB η t).1 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      sphereLogDerivative m (reflection g) (C.rootPair lA lB η t).2 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) := by
  have hzeroA : (0 : ℂ) ∈ C.eA.target := C.centerA ▸ C.eA.map_source C.memA
  have hzeroB : (0 : ℂ) ∈ C.eB.target := C.centerB ▸ C.eB.map_source C.memB
  have htoA : Tendsto (fun t : ℂ => η.1 * t ^ lA) (𝓝 0) (𝓝 0) := by
    convert! (continuous_const.mul (continuous_id.pow lA)).continuousAt.tendsto using 1 <;> first | simp [hA.ne'] | infer_instance
  have htoB : Tendsto (fun t : ℂ => η.2 * t ^ lB) (𝓝 0) (𝓝 0) := by
    convert! (continuous_const.mul (continuous_id.pow lB)).continuousAt.tendsto using 1 <;> first | simp [hB.ne'] | infer_instance
  filter_upwards [htoA.eventually (C.eA.open_target.mem_nhds hzeroA),
    htoB.eventually (C.eB.open_target.mem_nhds hzeroB)] with t htA htB
  refine ⟨htA, htB, ?_, ?_⟩
  · change sphereLogDerivative m g (C.eA.symm (η.1 * t ^ lA)) = _
    rw [C.valueA _ (C.eA.map_target htA), C.eA.right_inv htA, mul_pow, hη.1,
      one_mul, ← pow_mul, Nat.mul_comm lA C.kA, ← hN_A]
  · change sphereLogDerivative m (reflection g) (C.eB.symm (η.2 * t ^ lB)) = _
    rw [C.valueB _ (C.eB.map_target htB), C.eB.right_inv htB, mul_pow, hη.2,
      one_mul, ← pow_mul, Nat.mul_comm lB C.kB, ← hN_B]

/-- Distinct root indices in one chart give distinct physical pairs at every nonzero
parameter where both coordinates lie in the inverse-chart targets. -/
theorem RegularSpherePairChart.rootPair_injective {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    (lA lB : ℕ) {t : ℂ} (ht : t ≠ 0)
    (htarget : ∀ η ∈ RootPairIndices C.kA C.kB,
      η.1 * t ^ lA ∈ C.eA.target ∧ η.2 * t ^ lB ∈ C.eB.target) :
    Set.InjOn (fun η => C.rootPair lA lB η t) (RootPairIndices C.kA C.kB) := by
  intro η hη ξ hξ heq
  apply Prod.ext
  · exact mul_right_cancel₀ (pow_ne_zero _ ht)
      (C.eA.symm.injOn (htarget η hη).1 (htarget ξ hξ).1 (congrArg Prod.fst heq))
  · exact mul_right_cancel₀ (pow_ne_zero _ ht)
      (C.eB.symm.injOn (htarget η hη).2 (htarget ξ hξ).2 (congrArg Prod.snd heq))

/-- A single positive radius works for forward physical validity and injectivity of every
root index of a constructed chart. -/
theorem RegularSpherePairChart.rootPair_values_radius {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {N lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB)
    (hN_A : N = C.kA * lA) (hN_B : N = C.kB * lB) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      (∀ η ∈ RootPairIndices C.kA C.kB,
        η.1 * t ^ lA ∈ C.eA.target ∧ η.2 * t ^ lB ∈ C.eB.target ∧
        sphereLogDerivative m g (C.rootPair lA lB η t).1 =
          ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
        sphereLogDerivative m (reflection g) (C.rootPair lA lB η t).2 =
          ((p₀ + t ^ N : ℂ) : OnePoint ℂ)) ∧
      (t ≠ 0 → Set.InjOn (fun η => C.rootPair lA lB η t) (RootPairIndices C.kA C.kB)) := by
  have hevent := (rootPairIndices_finite C.posA C.posB).eventually_all.mpr
    fun η hη => C.rootPair_eventually_values hA hB hN_A hN_B hη
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, hε, fun t ht => ?_⟩
  have hvalid := hlocal (by simpa only [dist_zero_right] using ht)
  exact ⟨hvalid, fun hne => C.rootPair_injective lA lB hne
    (fun η hη => ⟨(hvalid η hη).1, (hvalid η hη).2.1⟩)⟩

/-- Root-branch centers are the original physical central pair. -/
theorem RegularSpherePairChart.rootPair_zero {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {lA lB : ℕ} (hA : 0 < lA) (hB : 0 < lB) (η : ℂ × ℂ) :
    C.rootPair lA lB η 0 = x.val := by
  simp [RegularSpherePairChart.rootPair, zero_pow hA.ne', zero_pow hB.ne',
    C.inverseCenterA, C.inverseCenterB]

/-- Every forward root branch remains in the actual correspondence source near its
center: its common value avoids the omitted value and its physical product stays nonzero. -/
theorem RegularSpherePairChart.rootPair_eventually_source {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {x : SphereCorrespondenceSource m g} (C : RegularSpherePairChart m g p₀ x)
    {N lA lB : ℕ} (hN : 0 < N) (hA : 0 < lA) (hB : 0 < lB)
    (hN_A : N = C.kA * lA) (hN_B : N = C.kB * lB)
    (hp₀ : p₀ ≠ (m : ℂ)) {η : ℂ × ℂ} (hη : η ∈ RootPairIndices C.kA C.kB) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      sphereLogDerivative m g (C.rootPair lA lB η t).1 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      sphereLogDerivative m (reflection g) (C.rootPair lA lB η t).2 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      C.rootProduct lA lB η t ≠ 0 ∧ p₀ + t ^ N ≠ (m : ℂ) := by
  have hprodzero : C.rootProduct lA lB η 0 ≠ 0 := by
    change (C.rootPair lA lB η 0).1 * (C.rootPair lA lB η 0).2 ≠ 0
    rw [C.rootPair_zero hA hB η]
    exact x.property.2.1
  have hproduct := (C.analytic_rootProduct hA hB η).continuousAt.eventually_ne hprodzero
  have hvalue : ContinuousAt (fun t : ℂ => p₀ + t ^ N) 0 := by
    exact continuous_const.continuousAt.add (continuous_id.pow N).continuousAt
  have hvaluene : p₀ + (0 : ℂ) ^ N ≠ (m : ℂ) := by simpa [zero_pow hN.ne'] using hp₀
  filter_upwards [C.rootPair_eventually_values hA hB hN_A hN_B hη,
    hproduct, hvalue.eventually_ne hvaluene] with t hvalues hprod hp
  exact ⟨hvalues.2.2.1, hvalues.2.2.2, hprod, hp⟩

/-- The actual finite index type of the common-power family. Indices remember both the
central physical pair and the two roots of unity. -/
def RegularSphereRootIndex {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val) :=
  Σ i : SphereCentralFiber m g y, RootPairIndices (C i).kA (C i).kB

instance {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ} {y : SphereCorrespondenceTarget m}
    [Finite (SphereCentralFiber m g y)]
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val) :
    Finite (RegularSphereRootIndex C) := by
  let : ∀ i : SphereCentralFiber m g y, Finite (RootPairIndices (C i).kA (C i).kB) :=
    fun i => (rootPairIndices_finite (C i).posA (C i).posB).to_subtype
  unfold RegularSphereRootIndex
  infer_instance

def regularSphereRootPair {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val)
    (lA lB : SphereCentralFiber m g y → ℕ) (j : RegularSphereRootIndex C) : ℂ → ℂ × ℂ :=
  (C j.1).rootPair (lA j.1) (lB j.1) j.2.val

def regularSphereRootProduct {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val)
    (lA lB : SphereCentralFiber m g y → ℕ) (j : RegularSphereRootIndex C) : ℂ → ℂ :=
  (C j.1).rootProduct (lA j.1) (lB j.1) j.2.val

/-- The finite common-power family has a uniform positive disk on which every index
provides a genuine physical pair of the original spherical correspondence. -/
theorem regularSphereRootFamily_values_radius {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m} [Finite (SphereCentralFiber m g y)]
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val)
    {N : ℕ} (hN : 0 < N) (lA lB : SphereCentralFiber m g y → ℕ)
    (horders : ∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).kA * lA i ∧ N = (C i).kB * lB i)
    (hp₀ : p₀ ≠ (m : ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ j : RegularSphereRootIndex C,
      sphereLogDerivative m g (regularSphereRootPair C lA lB j t).1 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      sphereLogDerivative m (reflection g) (regularSphereRootPair C lA lB j t).2 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      regularSphereRootProduct C lA lB j t ≠ 0 ∧ p₀ + t ^ N ≠ (m : ℂ) := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j : RegularSphereRootIndex C,
      sphereLogDerivative m g (regularSphereRootPair C lA lB j t).1 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      sphereLogDerivative m (reflection g) (regularSphereRootPair C lA lB j t).2 =
        ((p₀ + t ^ N : ℂ) : OnePoint ℂ) ∧
      regularSphereRootProduct C lA lB j t ≠ 0 ∧ p₀ + t ^ N ≠ (m : ℂ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (C j.1).rootPair_eventually_source hN (horders j.1).1 (horders j.1).2.1
      (horders j.1).2.2.1 (horders j.1).2.2.2 hp₀ j.2.property
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ε, hε, fun t ht => hlocal (by simpa only [dist_zero_right] using ht)⟩

/-- Both coordinates of each physical root branch are analytic at zero. -/
theorem regularSphereRootPair_analytic {m : ℕ} {g : ℂ → ℂ} {p₀ : ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val)
    (lA lB : SphereCentralFiber m g y → ℕ)
    (hA : ∀ i, 0 < lA i) (hB : ∀ i, 0 < lB i) (j : RegularSphereRootIndex C) :
    AnalyticAt ℂ (fun t => (regularSphereRootPair C lA lB j t).1) 0 ∧
      AnalyticAt ℂ (fun t => (regularSphereRootPair C lA lB j t).2) 0 :=
  ⟨analytic_inverseRoot_branch (C j.1).analyticA (hA j.1) j.2.val.1,
    analytic_inverseRoot_branch (C j.1).analyticB (hB j.1) j.2.val.2⟩

/-- Every nearby actual physical fiber is exactly the image of the finite family filtered
by its actual product values. Both cover directions use constructed analytic charts;
repeated indices are permitted and do not alter the physical image set. -/
theorem sphereCorrespondence_regular_finite_family {f g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (hnm : ¬IsMonomial f)
    (hfactor : ∀ z : ℂ, f z = z ^ m * g z) (y : SphereCorrespondenceTarget m)
    (p₀ : ℂ) (hp₀ : y.val.2 = (p₀ : OnePoint ℂ)) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, RegularSpherePairChart m g p₀ i.val,
        ∃ N : ℕ, ∃ lA lB : SphereCentralFiber m g y → ℕ,
          0 < N ∧
          (∀ i, 0 < lA i ∧ 0 < lB i ∧ N = (C i).kA * lA i ∧ N = (C i).kB * lB i) ∧
          (∀ j : RegularSphereRootIndex C,
            AnalyticAt ℂ (regularSphereRootProduct C lA lB j) 0) ∧
          ∃ V : Set (SphereCorrespondenceTarget m), IsOpen V ∧ y ∈ V ∧
            ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
              ∀ y' : SphereCorrespondenceTarget m, y'.val.2 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) →
                y' ∈ V →
                InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
                  y'.val.1 y'.val.2 =
                    (fun j => regularSphereRootPair C lA lB j t) ''
                      {j : RegularSphereRootIndex C |
                        regularSphereRootProduct C lA lB j t = y'.val.1} := by
  obtain ⟨hfinite, C, N, lA, lB, hN, horders, hanalytic, V, hV, hy, hcapture⟩ :=
    sphereCorrespondence_regular_root_capture hg hg0 hnm hfactor y p₀ hp₀
  have : Finite (SphereCentralFiber m g y) := hfinite
  have hp : p₀ ≠ (m : ℂ) := by
    intro heq
    exact y.property.2 (by simpa only [heq] using hp₀)
  obtain ⟨ε, hε, hforward⟩ := regularSphereRootFamily_values_radius C hN lA lB horders hp
  refine ⟨hfinite, C, N, lA, lB, hN, horders, fun j => hanalytic j.1 j.2.val,
    V, hV, hy, ε, hε, ?_⟩
  intro t ht hne y' hvalue hy'
  ext zw
  constructor
  · intro hzw
    let x : SphereCorrespondenceSource m g := ⟨zw,
      hzw.2.1.trans hzw.2.2.symm,
      fun hz => y'.property.1 (hzw.1.symm.trans hz),
      fun hz => y'.property.2 (hzw.2.1.symm.trans hz)⟩
    have hxmap : sphereCorrespondenceMap m g x = y' := by
      apply Subtype.ext
      exact Prod.ext hzw.1 hzw.2.1
    have hxvalue : sphereLogDerivative m g x.val.1 = ((p₀ + t ^ N : ℂ) : OnePoint ℂ) :=
      hzw.2.1.trans hvalue
    obtain ⟨i, η, hη, hpair⟩ := hcapture t hne x (hxmap ▸ hy') hxvalue
    let j : RegularSphereRootIndex C := ⟨i, ⟨η, hη⟩⟩
    have hjpair : regularSphereRootPair C lA lB j t = zw := hpair
    refine ⟨j, ?_, hjpair⟩
    change (regularSphereRootPair C lA lB j t).1 *
      (regularSphereRootPair C lA lB j t).2 = y'.val.1
    rw [hjpair]
    exact hzw.1
  · rintro ⟨j, hj, rfl⟩
    have hf := hforward t ht j
    exact ⟨hj, hf.1.trans hvalue.symm, hf.2.1.trans hvalue.symm⟩

end

end MaximumModulus
