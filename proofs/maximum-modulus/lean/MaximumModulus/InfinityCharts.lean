module

public import MaximumModulus.GlobalCharts
public import MaximumModulus.FiniteImageGraphs
public import MaximumModulus.HighCountLocus
public import MaximumModulus.PairNonvertical

@[expose] public section

/-!
# Actual finite physical families at the common value infinity

The logarithmic poles are simple. Their inverse coordinates therefore have exponent
one, and every central physical pair supplies a single analytic parameter branch.
-/

open Set Filter Metric
open scoped Topology ComplexConjugate

namespace MaximumModulus

noncomputable section

def infinityValue (t : ℂ) : OnePoint ℂ :=
  if t = 0 then OnePoint.infty else ((t⁻¹ : ℂ) : OnePoint ℂ)

theorem infinityValue_injective : Function.Injective infinityValue := by
  intro t u h
  by_cases ht : t = 0
  · subst t
    by_cases hu : u = 0
    · exact hu.symm
    · simp [infinityValue, hu] at h
  · by_cases hu : u = 0
    · subst u
      simp [infinityValue, ht] at h
    · exact inv_injective (OnePoint.coe_injective (by simpa [infinityValue, ht, hu] using h))

/-- Inversion extends continuously through zero after assigning its spherical value
infinity. This is proved from the inverse map's cobounded limit. -/
theorem continuous_infinityValue : Continuous infinityValue := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    rw [ContinuousAt, show infinityValue (0 : ℂ) = OnePoint.infty by simp [infinityValue],
      ← nhdsNE_sup_pure]
    apply Tendsto.sup
    · have hinv : Tendsto (fun t : ℂ => t⁻¹) (𝓝[≠] 0) (coclosedCompact ℂ) := by
        simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
          (tendsto_inv₀_nhdsNE_zero : Tendsto (fun t : ℂ => t⁻¹) (𝓝[≠] 0) (Bornology.cobounded ℂ))
      apply (OnePoint.tendsto_coe_infty.comp hinv).congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [mem_compl_iff, mem_singleton_iff] at hz
      simp [infinityValue, hz]
    · simpa only [show infinityValue (0 : ℂ) = OnePoint.infty by simp [infinityValue]] using
        tendsto_pure_nhds infinityValue (0 : ℂ)
  · have hc : ContinuousAt (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ)) t :=
      OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ ht)
    apply hc.congr
    filter_upwards [eventually_ne_nhds ht] with z hz
    simp [infinityValue, hz]

def infinityCoordinate (p : OnePoint ℂ) : ℂ := p.elim 0 fun z => z⁻¹

@[simp] theorem infinityCoordinate_infty : infinityCoordinate OnePoint.infty = 0 := rfl

@[simp] theorem infinityCoordinate_coe (z : ℂ) : infinityCoordinate (z : OnePoint ℂ) = z⁻¹ := rfl

@[simp] theorem infinityCoordinate_value (t : ℂ) : infinityCoordinate (infinityValue t) = t := by
  by_cases ht : t = 0 <;> simp [infinityValue, ht]

theorem infinityValue_coordinate {p : OnePoint ℂ} (hp : p ≠ ((0 : ℂ) : OnePoint ℂ)) :
    infinityValue (infinityCoordinate p) = p := by
  cases p using OnePoint.rec with
  | infty => simp [infinityValue]
  | coe z =>
    have hz : z ≠ 0 := by simpa using hp
    simp [infinityValue, hz]

theorem infinityValue_ne_zero (t : ℂ) : infinityValue t ≠ ((0 : ℂ) : OnePoint ℂ) := by
  by_cases ht : t = 0 <;> simp [infinityValue, ht]

theorem continuousAt_infinityCoordinate {p : OnePoint ℂ}
    (hp : p ≠ ((0 : ℂ) : OnePoint ℂ)) : ContinuousAt infinityCoordinate p := by
  cases p using OnePoint.rec with
  | infty =>
    apply OnePoint.continuousAt_infty'.mpr
    simpa only [Function.comp_def, infinityCoordinate_coe, infinityCoordinate_infty,
      coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  | coe z =>
    have hz : z ≠ 0 := by simpa using hp
    apply OnePoint.continuousAt_coe.mpr
    simpa only [Function.comp_def, infinityCoordinate_coe] using continuousAt_inv₀ hz

/-- The genuine reciprocal spherical chart has full complex source and omits only
the finite value zero. It is an open embedding, including at the infinity center. -/
def infinityValueChart : OpenPartialHomeomorph ℂ (OnePoint ℂ) where
  toFun := infinityValue
  invFun := infinityCoordinate
  source := univ
  target := {p | p ≠ ((0 : ℂ) : OnePoint ℂ)}
  map_source' := fun t _ => infinityValue_ne_zero t
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun t _ => infinityCoordinate_value t
  right_inv' := fun _ hp => infinityValue_coordinate hp
  open_source := isOpen_univ
  open_target := isOpen_ne
  continuousOn_toFun := continuous_infinityValue.continuousOn
  continuousOn_invFun := fun _ hp => (continuousAt_infinityCoordinate hp).continuousWithinAt

theorem isOpenEmbedding_infinityValue : Topology.IsOpenEmbedding infinityValue :=
  infinityValueChart.isOpenEmbedding rfl

theorem range_infinityValue : range infinityValue = {p | p ≠ ((0 : ℂ) : OnePoint ℂ)} := by
  ext p
  exact ⟨fun ⟨t, ht⟩ => ht ▸ infinityValue_ne_zero t,
    fun hp => ⟨infinityCoordinate p, infinityValue_coordinate hp⟩⟩

def infinityValueEmbedding : ℂ × ℂ → ℂ × OnePoint ℂ :=
  fun y => (y.1, infinityValue y.2)

theorem infinityValueEmbedding_isOpenEmbedding : Topology.IsOpenEmbedding infinityValueEmbedding :=
  Topology.IsOpenEmbedding.id.prodMap isOpenEmbedding_infinityValue

theorem infinityValueEmbedding_continuous : Continuous infinityValueEmbedding :=
  infinityValueEmbedding_isOpenEmbedding.continuous

theorem infinityValueEmbedding_preimage_closure (A : Set (ℂ × OnePoint ℂ)) :
    infinityValueEmbedding ⁻¹' closure A = closure (infinityValueEmbedding ⁻¹' A) :=
  infinityValueEmbedding_isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    infinityValueEmbedding_continuous A

theorem infinityValueEmbedding_open_local_projection {H : Set (ℂ × OnePoint ℂ)}
    {W : Set (ℂ × ℂ)} (hW : IsOpen W)
    (hproj : IsOpen (Prod.fst '' ((infinityValueEmbedding ⁻¹' H) ∩ W))) :
    IsOpen (infinityValueEmbedding '' W) ∧
      IsOpen (Prod.fst '' (H ∩ (infinityValueEmbedding '' W))) := by
  refine ⟨infinityValueEmbedding_isOpenEmbedding.isOpenMap W hW, ?_⟩
  have heq : Prod.fst '' (H ∩ (infinityValueEmbedding '' W)) =
      Prod.fst '' ((infinityValueEmbedding ⁻¹' H) ∩ W) := by
    ext s
    constructor
    · rintro ⟨y, ⟨hy, x, hx, rfl⟩, rfl⟩
      exact ⟨x, ⟨hy, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hxH, hxW⟩, rfl⟩
      exact ⟨infinityValueEmbedding x, ⟨hxH, x, hxW, rfl⟩, rfl⟩
  rw [heq]
  exact hproj

/-- Open proper-capture neighborhoods pull back through the genuine reciprocal
spherical chart to open neighborhoods of the parameter zero. -/
theorem infinityTarget_capture_neighborhood {m : ℕ} {y : SphereCorrespondenceTarget m}
    (hy_infty : y.val.2 = OnePoint.infty)
    {V : Set (SphereCorrespondenceTarget m)} (hV : IsOpen V) (hy : y ∈ V) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (y.val.1, (0 : ℂ)) ∈ W ∧
      ∀ z ∈ W, ∃ hz : z.1 ≠ 0 ∧ infinityValue z.2 ≠ ((m : ℂ) : OnePoint ℂ),
        (⟨(z.1, infinityValue z.2), hz⟩ : SphereCorrespondenceTarget m) ∈ V := by
  have hdomain : IsOpen {z : ℂ × OnePoint ℂ |
      z.1 ≠ 0 ∧ z.2 ≠ ((m : ℂ) : OnePoint ℂ)} :=
    (isClosed_singleton.isOpen_compl.preimage continuous_fst).inter
      (isClosed_singleton.isOpen_compl.preimage continuous_snd)
  let W := infinityValueEmbedding ⁻¹' (Subtype.val '' V)
  have hW : IsOpen W := (hdomain.isOpenMap_subtype_val V hV).preimage infinityValueEmbedding_continuous
  refine ⟨W, hW, ?_, ?_⟩
  · exact ⟨y, hy, Prod.ext rfl (by simpa [infinityValueEmbedding, infinityValue] using hy_infty)⟩
  · intro z hz
    obtain ⟨q, hq, heq⟩ := hz
    have heq' : q.val = (z.1, infinityValue z.2) := heq
    have hprop : z.1 ≠ 0 ∧ infinityValue z.2 ≠ ((m : ℂ) : OnePoint ℂ) := by
      change (z.1, infinityValue z.2).1 ≠ 0 ∧
        (z.1, infinityValue z.2).2 ≠ ((m : ℂ) : OnePoint ℂ)
      rw [← heq']
      exact q.property
    refine ⟨hprop, ?_⟩
    have hsub : (⟨(z.1, infinityValue z.2), hprop⟩ : SphereCorrespondenceTarget m) = q :=
      Subtype.ext heq'.symm
    rw [hsub]
    exact hq

structure InfinitySpherePairChart (m : ℕ) (g : ℂ → ℂ)
    (x : SphereCorrespondenceSource m g) where
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
  valueA : ∀ z : ℂ, z ∈ eA.source → sphereLogDerivative m g z = infinityValue (eA z)
  valueB : ∀ z : ℂ, z ∈ eB.source →
    sphereLogDerivative m (reflection g) z = infinityValue (eB z)

def InfinitySpherePairChart.source {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    Set (SphereCorrespondenceSource m g) :=
  {x' | x'.val.1 ∈ C.eA.source ∧ x'.val.2 ∈ C.eB.source}

theorem InfinitySpherePairChart.open_source {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    IsOpen C.source := by
  change IsOpen (Subtype.val ⁻¹' (C.eA.source ×ˢ C.eB.source))
  exact (C.eA.open_source.prod C.eB.open_source).preimage continuous_subtype_val

theorem InfinitySpherePairChart.mem_source {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    x ∈ C.source := ⟨C.memA, C.memB⟩

theorem infinitySpherePairChart_exists {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (x : SphereCorrespondenceSource m g)
    (hx : sphereLogDerivative m g x.val.1 = OnePoint.infty) :
    Nonempty (InfinitySpherePairChart m g x) := by
  have hga : g x.val.1 = 0 := (sphereLogDerivative_eq_infty m g x.val.1).mp hx
  have hgb : reflection g x.val.2 = 0 :=
    (sphereLogDerivative_eq_infty m (reflection g) x.val.2).mp (x.property.1.symm.trans hx)
  have hxa : x.val.1 ≠ 0 := left_ne_zero_of_mul x.property.2.1
  have hxb : x.val.2 ≠ 0 := right_ne_zero_of_mul x.property.2.1
  have hgR := entire_reflection hg
  have hgR0 : reflection g 0 ≠ 0 := by simpa [reflection] using hg0
  obtain ⟨eA, ha, hzeroA, hcenterA, hψA, hvalueA⟩ :=
    sphereLogDerivative_pole_inverse_chart hg hg0 m hxa hga
  obtain ⟨eB, hb, hzeroB, hcenterB, hψB, hvalueB⟩ :=
    sphereLogDerivative_pole_inverse_chart hgR hgR0 m hxb hgb
  exact ⟨⟨eA, eB, ha, hb, hzeroA, hzeroB, hcenterA, hcenterB, hψA, hψB,
    hvalueA, hvalueB⟩⟩

def InfinitySpherePairChart.pair {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x)
    (t : ℂ) : ℂ × ℂ := (C.eA.symm t, C.eB.symm t)

def InfinitySpherePairChart.product {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x)
    (t : ℂ) : ℂ := (C.pair t).1 * (C.pair t).2

theorem InfinitySpherePairChart.pair_zero {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    C.pair 0 = x.val := Prod.ext C.inverseCenterA C.inverseCenterB

theorem InfinitySpherePairChart.analytic_product {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    AnalyticAt ℂ C.product 0 := C.analyticA.mul C.analyticB

theorem InfinitySpherePairChart.capture_pair {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x)
    {t : ℂ} {x' : SphereCorrespondenceSource m g} (hx' : x' ∈ C.source)
    (hvalue : sphereLogDerivative m g x'.val.1 = infinityValue t) :
    C.pair t = x'.val := by
  have hA : C.eA x'.val.1 = t := infinityValue_injective ((C.valueA _ hx'.1).symm.trans hvalue)
  have hB : C.eB x'.val.2 = t := infinityValue_injective
    ((C.valueB _ hx'.2).symm.trans (x'.property.1.symm.trans hvalue))
  apply Prod.ext
  · change C.eA.symm t = x'.val.1
    rw [← hA]
    exact C.eA.left_inv hx'.1
  · change C.eB.symm t = x'.val.2
    rw [← hB]
    exact C.eB.left_inv hx'.2

theorem sphereCorrespondence_infinity_chart_capture {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (y : SphereCorrespondenceTarget m)
    (hy_infty : y.val.2 = OnePoint.infty) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val,
        ∃ V : Set (SphereCorrespondenceTarget m), IsOpen V ∧ y ∈ V ∧
          ∀ x : SphereCorrespondenceSource m g, sphereCorrespondenceMap m g x ∈ V →
            ∃ i : SphereCentralFiber m g y, x ∈ (C i).source := by
  classical
  have hfinite : {x : SphereCorrespondenceSource m g | sphereCorrespondenceMap m g x = y}.Finite := by
    simpa only [Set.preimage_singleton] using sphereCorrespondenceMap_finite_fiber hg hg0 m y
  refine ⟨hfinite.to_subtype, ?_⟩
  have hchart : ∀ i : SphereCentralFiber m g y, Nonempty (InfinitySpherePairChart m g i.val) := by
    intro i
    apply infinitySpherePairChart_exists hg hg0
    have hvalue := congrArg (fun q : SphereCorrespondenceTarget m => q.val.2) i.property
    exact hvalue.trans hy_infty
  let C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val :=
    fun i => Classical.choice (hchart i)
  let U : Set (SphereCorrespondenceSource m g) := ⋃ i, (C i).source
  have hU : IsOpen U := isOpen_iUnion fun i => (C i).open_source
  have hcover : ∀ x : SphereCorrespondenceSource m g, sphereCorrespondenceMap m g x = y → x ∈ U := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (C ⟨x, hx⟩).mem_source⟩
  obtain ⟨V, hV, hy, hcapture⟩ := proper_map_neighborhood_capture
    (isProperMap_sphereCorrespondenceMap hg hg0 m) hU hcover
  exact ⟨C, V, hV, hy, fun x hx => mem_iUnion.mp (hcapture x hx)⟩

theorem InfinitySpherePairChart.pair_eventually_values {m : ℕ} {g : ℂ → ℂ}
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      sphereLogDerivative m g (C.pair t).1 = infinityValue t ∧
      sphereLogDerivative m (reflection g) (C.pair t).2 = infinityValue t := by
  have hzeroA : (0 : ℂ) ∈ C.eA.target := C.centerA ▸ C.eA.map_source C.memA
  have hzeroB : (0 : ℂ) ∈ C.eB.target := C.centerB ▸ C.eB.map_source C.memB
  filter_upwards [C.eA.open_target.mem_nhds hzeroA,
    C.eB.open_target.mem_nhds hzeroB] with t htA htB
  refine ⟨?_, ?_⟩
  · change sphereLogDerivative m g (C.eA.symm t) = _
    rw [C.valueA _ (C.eA.map_target htA), C.eA.right_inv htA]
  · change sphereLogDerivative m (reflection g) (C.eB.symm t) = _
    rw [C.valueB _ (C.eB.map_target htB), C.eB.right_inv htB]

theorem InfinitySpherePairChart.pair_eventually_source {m : ℕ} {g : ℂ → ℂ}
    (hg : Entire g) (hg0 : g 0 ≠ 0)
    {x : SphereCorrespondenceSource m g} (C : InfinitySpherePairChart m g x) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      sphereLogDerivative m g (C.pair t).1 = infinityValue t ∧
      sphereLogDerivative m (reflection g) (C.pair t).2 = infinityValue t ∧
      C.product t ≠ 0 ∧ infinityValue t ≠ ((m : ℂ) : OnePoint ℂ) := by
  have hprodzero : C.product 0 ≠ 0 := by
    change (C.pair 0).1 * (C.pair 0).2 ≠ 0
    rw [C.pair_zero]
    exact x.property.2.1
  have hproduct := C.analytic_product.continuousAt.eventually_ne hprodzero
  have hvalue : ContinuousAt (fun t : ℂ => sphereLogDerivative m g (C.pair t).1) 0 :=
    (continuous_sphereLogDerivative hg hg0 m).continuousAt.comp C.analyticA.continuousAt
  have hvaluene : sphereLogDerivative m g (C.pair 0).1 ≠ ((m : ℂ) : OnePoint ℂ) := by
    rw [C.pair_zero]
    exact x.property.2.2
  filter_upwards [C.pair_eventually_values, hproduct,
    hvalue.eventually_ne hvaluene] with t hvalues hprod hne
  exact ⟨hvalues.1, hvalues.2, hprod, hvalues.1 ▸ hne⟩

def infinitySpherePair {m : ℕ} {g : ℂ → ℂ} {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val)
    (i : SphereCentralFiber m g y) : ℂ → ℂ × ℂ := (C i).pair

def infinitySphereProduct {m : ℕ} {g : ℂ → ℂ} {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val)
    (i : SphereCentralFiber m g y) : ℂ → ℂ := (C i).product

theorem infinitySpherePair_analytic {m : ℕ} {g : ℂ → ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val)
    (i : SphereCentralFiber m g y) :
    AnalyticAt ℂ (fun t => (infinitySpherePair C i t).1) 0 ∧
      AnalyticAt ℂ (fun t => (infinitySpherePair C i t).2) 0 :=
  ⟨(C i).analyticA, (C i).analyticB⟩

theorem infinitySphereFamily_values_radius {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) {y : SphereCorrespondenceTarget m}
    [Finite (SphereCentralFiber m g y)]
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ i : SphereCentralFiber m g y,
      sphereLogDerivative m g (infinitySpherePair C i t).1 = infinityValue t ∧
      sphereLogDerivative m (reflection g) (infinitySpherePair C i t).2 = infinityValue t ∧
      infinitySphereProduct C i t ≠ 0 ∧ infinityValue t ≠ ((m : ℂ) : OnePoint ℂ) := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i : SphereCentralFiber m g y,
      sphereLogDerivative m g (infinitySpherePair C i t).1 = infinityValue t ∧
      sphereLogDerivative m (reflection g) (infinitySpherePair C i t).2 = infinityValue t ∧
      infinitySphereProduct C i t ≠ 0 ∧ infinityValue t ≠ ((m : ℂ) : OnePoint ℂ) :=
    Filter.eventually_all.mpr fun i => (C i).pair_eventually_source hg hg0
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ε, hε, fun t ht => hlocal (by simpa only [dist_zero_right] using ht)⟩

/-- Around an actual central fiber over infinity, every nearby physical fiber is exactly
the finite family filtered by its product values. The parameter zero includes infinity
itself, rather than discarding it as an exceptional common value. -/
theorem sphereCorrespondence_infinity_finite_family {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (y : SphereCorrespondenceTarget m)
    (hy_infty : y.val.2 = OnePoint.infty) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val,
        (∀ i : SphereCentralFiber m g y, AnalyticAt ℂ (infinitySphereProduct C i) 0) ∧
        ∃ V : Set (SphereCorrespondenceTarget m), IsOpen V ∧ y ∈ V ∧
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
            ∀ y' : SphereCorrespondenceTarget m, y'.val.2 = infinityValue t → y' ∈ V →
              InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
                y'.val.1 y'.val.2 =
                  (fun i => infinitySpherePair C i t) ''
                    {i : SphereCentralFiber m g y | infinitySphereProduct C i t = y'.val.1} := by
  obtain ⟨hfinite, C, V, hV, hy, hcapture⟩ :=
    sphereCorrespondence_infinity_chart_capture hg hg0 y hy_infty
  have : Finite (SphereCentralFiber m g y) := hfinite
  obtain ⟨ε, hε, hforward⟩ := infinitySphereFamily_values_radius hg hg0 C
  refine ⟨hfinite, C, fun i => (C i).analytic_product, V, hV, hy, ε, hε, ?_⟩
  intro t ht y' hvalue hy'
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
    obtain ⟨i, hi⟩ := hcapture x (hxmap ▸ hy')
    have hpair : infinitySpherePair C i t = zw :=
      (C i).capture_pair hi (hzw.2.1.trans hvalue)
    refine ⟨i, ?_, hpair⟩
    change (infinitySpherePair C i t).1 * (infinitySpherePair C i t).2 = y'.val.1
    rw [hpair]
    exact hzw.1
  · rintro ⟨i, hi, rfl⟩
    have hf := hforward t ht i
    exact ⟨hi, hf.1.trans hvalue.symm, hf.2.1.trans hvalue.symm⟩

/-- Distinct central physical pairs remain distinct uniformly near the common pole
parameter. Consequently family indices count physical points without multiplicity. -/
theorem infinitySphereFamily_injective_radius {m : ℕ} {g : ℂ → ℂ}
    {y : SphereCorrespondenceTarget m} [Finite (SphereCentralFiber m g y)]
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
      Function.Injective (fun i : SphereCentralFiber m g y => infinitySpherePair C i t) := by
  have hcenter : Function.Injective (fun i : SphereCentralFiber m g y => infinitySpherePair C i 0) := by
    intro i j heq
    apply Subtype.ext
    apply Subtype.ext
    exact ((C i).pair_zero.symm.trans heq).trans (C j).pair_zero
  have hcont : ∀ i : SphereCentralFiber m g y, ContinuousAt (infinitySpherePair C i) 0 :=
    fun i => (C i).analyticA.continuousAt.prodMk (C i).analyticB.continuousAt
  have hopen : IsOpen {p : (ℂ × ℂ) × (ℂ × ℂ) | p.1 ≠ p.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j : SphereCentralFiber m g y,
      i ≠ j → infinitySpherePair C i t ≠ infinitySpherePair C j t := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    · have hne : infinitySpherePair C i 0 ≠ infinitySpherePair C j 0 := fun h => hij (hcenter h)
      filter_upwards [((hcont i).prodMk (hcont j)).eventually (hopen.mem_nhds hne)] with t ht
      exact fun _ => ht
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, hε, fun t ht i j hij => ?_⟩
  by_contra hne
  exact hlocal (by simpa only [dist_zero_right] using ht) i j hne hij

/-- Exact physical cardinality near infinity. Finiteness is explicit; the cardinality is
the number of indices with the required product, not an infinite-set `ncard` value. -/
theorem sphereCorrespondence_infinity_finite_ncard {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (y : SphereCorrespondenceTarget m)
    (hy_infty : y.val.2 = OnePoint.infty) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val,
        (∀ i : SphereCentralFiber m g y, AnalyticAt ℂ (infinitySphereProduct C i) 0) ∧
        ∃ V : Set (SphereCorrespondenceTarget m), IsOpen V ∧ y ∈ V ∧
          ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε →
            ∀ y' : SphereCorrespondenceTarget m, y'.val.2 = infinityValue t → y' ∈ V →
              (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
                y'.val.1 y'.val.2).Finite ∧
              (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
                y'.val.1 y'.val.2).ncard =
                  {i : SphereCentralFiber m g y | infinitySphereProduct C i t = y'.val.1}.ncard := by
  obtain ⟨hfinite, C, hanalytic, V, hV, hy, ε₁, hε₁, hfamily⟩ :=
    sphereCorrespondence_infinity_finite_family hg hg0 y hy_infty
  have : Finite (SphereCentralFiber m g y) := hfinite
  obtain ⟨ε₂, hε₂, hinj⟩ := infinitySphereFamily_injective_radius C
  refine ⟨hfinite, C, hanalytic, V, hV, hy, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro t ht y' hvalue hy'
  rw [hfamily t (lt_of_lt_of_le ht (min_le_left _ _)) y' hvalue hy']
  exact ⟨(Set.toFinite _).image _,
    Set.ncard_image_of_injective _ (hinj t (lt_of_lt_of_le ht (min_le_right _ _)))⟩

theorem infinitySphereProduct_zero {m : ℕ} {g : ℂ → ℂ}
    {y : SphereCorrespondenceTarget m}
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val)
    (i : SphereCentralFiber m g y) : infinitySphereProduct C i 0 = y.val.1 := by
  change ((C i).pair 0).1 * ((C i).pair 0).2 = y.val.1
  rw [(C i).pair_zero]
  exact congrArg (fun q : SphereCorrespondenceTarget m => q.val.1) i.property

/-- Every physical branch remains in an arbitrary captured target neighborhood after
uniform shrinking. This supplies actual complete fibers along the branch images. -/
theorem infinitySphereFamily_target_radius {m : ℕ} {g : ℂ → ℂ}
    {y : SphereCorrespondenceTarget m} [Finite (SphereCentralFiber m g y)]
    (C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val)
    {W : Set (ℂ × ℂ)} (hW : IsOpen W) (hy : (y.val.1, (0 : ℂ)) ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → ∀ i : SphereCentralFiber m g y,
      (infinitySphereProduct C i t, t) ∈ W := by
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i : SphereCentralFiber m g y,
      (infinitySphereProduct C i t, t) ∈ W := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun t : ℂ => (infinitySphereProduct C i t, t)) 0 :=
      (C i).analytic_product.continuousAt.prodMk continuousAt_id
    have hcenter : (infinitySphereProduct C i 0, (0 : ℂ)) = (y.val.1, (0 : ℂ)) :=
      Prod.ext (infinitySphereProduct_zero C i) rfl
    have hy' : (infinitySphereProduct C i 0, (0 : ℂ)) ∈ W := by
      rw [hcenter]
      exact hy
    exact hc.eventually (hW.mem_nhds hy')
  obtain ⟨ε, hε, hlocal⟩ := Metric.eventually_nhds_iff.mp hevent
  exact ⟨ε, hε, fun t ht => hlocal (by simpa only [dist_zero_right] using ht)⟩

/-- The physical count on each actual pole image branch is constant on a punctured
parameter disk. It equals the number of central indices with the same product germ.
Neither branch regularity nor an abstract generic-degree assumption is used. -/
theorem sphereCorrespondence_infinity_branch_counts {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) (y : SphereCorrespondenceTarget m)
    (hy_infty : y.val.2 = OnePoint.infty) :
    Finite (SphereCentralFiber m g y) ∧
      ∃ C : ∀ i : SphereCentralFiber m g y, InfinitySpherePairChart m g i.val,
        (∀ i : SphereCentralFiber m g y, AnalyticAt ℂ (infinitySphereProduct C i) 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 → ∀ i : SphereCentralFiber m g y,
          (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
            (infinitySphereProduct C i t) (infinityValue t)).Finite ∧
          (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
            (infinitySphereProduct C i t) (infinityValue t)).ncard =
              {j : SphereCentralFiber m g y |
                ∀ᶠ u in 𝓝 (0 : ℂ), infinitySphereProduct C j u = infinitySphereProduct C i u}.ncard := by
  obtain ⟨hfinite, C, hanalytic, V, hV, hy, ε₁, hε₁, hcount⟩ :=
    sphereCorrespondence_infinity_finite_ncard hg hg0 y hy_infty
  have : Finite (SphereCentralFiber m g y) := hfinite
  obtain ⟨W, hW, hyW, hWV⟩ := infinityTarget_capture_neighborhood hy_infty hV hy
  obtain ⟨ε₂, hε₂, hbranchW⟩ := infinitySphereFamily_target_radius C hW hyW
  obtain ⟨ε₃, hε₃, hclasses⟩ := finite_imageBranch_classes_radius hanalytic
  refine ⟨hfinite, C, hanalytic, min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), ?_⟩
  intro t ht hne i
  have ht₁ := ht.trans_le (min_le_left ε₁ (min ε₂ ε₃))
  have ht₂ := ht.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_left ε₂ ε₃))
  have ht₃ := ht.trans_le ((min_le_right ε₁ (min ε₂ ε₃)).trans (min_le_right ε₂ ε₃))
  obtain ⟨hprop, hmem⟩ := hWV _ (hbranchW t ht₂ i)
  let y' : SphereCorrespondenceTarget m := ⟨(infinitySphereProduct C i t, infinityValue t), hprop⟩
  have hc := hcount t ht₁ y' rfl hmem
  have hclass := hclasses t ht₃ hne i
  exact ⟨hc.1, hc.2.trans (congrArg Set.ncard hclass)⟩

def ReciprocalLogDerivativeImage (m : ℕ) (g : ℂ → ℂ) : Set (ℂ × ℂ) :=
  {z | (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
    z.1 (infinityValue z.2)).Nonempty}

/-- Constructed full-image cover in the genuine reciprocal target coordinate. -/
structure InfinityTargetBranchCover (m : ℕ) (g : ℂ → ℂ) (s₀ : ℂ) where
  Index : Type
  finite_index : Finite Index
  δ : ℝ
  posδ : 0 < δ
  P : Index → ℂ → ℂ × ℂ
  S : Index → ℂ → ℂ
  product : ∀ j t, (P j t).1 * (P j t).2 = S j t
  analyticA : ∀ j, AnalyticAt ℂ (fun t => (P j t).1) 0
  analyticB : ∀ j, AnalyticAt ℂ (fun t => (P j t).2) 0
  analyticS : ∀ j, AnalyticOnNhd ℂ (S j) (closedBall 0 δ)
  center : ∀ j, S j 0 = s₀
  forward : ∀ t : ℂ, ‖t‖ < δ → ∀ j,
    sphereLogDerivative m g (P j t).1 = infinityValue t ∧
    sphereLogDerivative m (reflection g) (P j t).2 = infinityValue t
  W : Set (ℂ × ℂ)
  openW : IsOpen W
  centerW : (s₀, (0 : ℂ)) ∈ W
  domainW : ∀ z ∈ W, z.1 ≠ 0 ∧ infinityValue z.2 ≠ ((m : ℂ) : OnePoint ℂ)
  Wcylinder : W ⊆ BranchValueCylinder 1 0 δ
  branchW : ∀ j t, ‖t‖ < δ → ImageBranch (S j) 1 0 t ∈ W
  imageCover : ∀ z ∈ W,
    z ∈ ReciprocalLogDerivativeImage m g ↔
      z ∈ ⋃ j, ImageBranch (S j) 1 0 '' ball 0 δ
  fiber_eq : ∀ t : ℂ, ‖t‖ < δ → ∀ j,
    InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
      (S j t) (infinityValue t) = (fun k => P k t) '' {k | S k t = S j t}
  comparisons : ∀ t : ℂ, ‖t‖ < δ → t ≠ 0 → ∀ i j, ∀ ω : ℂ, ω ^ 1 = 1 →
    (S i (ω * t) = S j t ↔ ∀ᶠ u in 𝓝 (0 : ℂ), S i (ω * u) = S j u)

attribute [instance] InfinityTargetBranchCover.finite_index

theorem infinityTargetBranchCover_exists {g : ℂ → ℂ} {m : ℕ}
    (hg : Entire g) (hg0 : g 0 ≠ 0) {s₀ : ℂ} (hs₀ : s₀ ≠ 0) :
    Nonempty (InfinityTargetBranchCover m g s₀) := by
  classical
  let y : SphereCorrespondenceTarget m := ⟨(s₀, OnePoint.infty), hs₀, OnePoint.infty_ne_coe _⟩
  obtain ⟨hfinite, C, hS, V, hV, hy, ε₁, hε₁, hfamily⟩ :=
    sphereCorrespondence_infinity_finite_family hg hg0 y rfl
  let : Finite (SphereCentralFiber m g y) := hfinite
  let ι := SphereCentralFiber m g y
  let P := infinitySpherePair C
  let S := infinitySphereProduct C
  obtain ⟨W₀, hW₀, hyW₀, hWcapture⟩ := infinityTarget_capture_neighborhood (m := m)
    (y := y) rfl hV hy
  obtain ⟨ε₂, hε₂, hbranch⟩ := infinitySphereFamily_target_radius C hW₀ hyW₀
  have hnearAnalytic : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ j : ι, AnalyticAt ℂ (S j) t :=
    Filter.eventually_all.mpr fun j => (hS j).eventually_analyticAt
  obtain ⟨ε₃, hε₃, hlocalAnalytic⟩ := Metric.eventually_nhds_iff.mp hnearAnalytic
  obtain ⟨ε₄, hε₄, hcmp⟩ := finite_imageBranch_comparisons_radius hS (N := 1) (by decide)
  let δ := min ε₁ (min ε₂ (min (ε₃ / 2) ε₄))
  have hδ : 0 < δ := lt_min hε₁ (lt_min hε₂ (lt_min (half_pos hε₃) hε₄))
  have hδ₁ : δ ≤ ε₁ := min_le_left _ _
  have hδ₂ : δ ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ < ε₃ := lt_of_le_of_lt
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (half_lt_self hε₃)
  have hδ₄ : δ ≤ ε₄ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let W := W₀ ∩ BranchValueCylinder 1 0 δ
  have hW : IsOpen W := hW₀.inter (isOpen_branchValueCylinder 1 0 δ)
  have hyW : (s₀, (0 : ℂ)) ∈ W := ⟨hyW₀, by simpa [BranchValueCylinder] using hδ⟩
  have hbranchW : ∀ j : ι, ∀ t : ℂ, ‖t‖ < δ → ImageBranch (S j) 1 0 t ∈ W := by
    intro j t ht
    refine ⟨?_, ?_⟩
    · simpa [ImageBranch] using hbranch t (ht.trans_le hδ₂) j
    · simpa [ImageBranch, BranchValueCylinder] using ht
  have hfamilyW : ∀ z ∈ W,
      InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
        z.1 (infinityValue z.2) = (fun j : ι => P j z.2) '' {j | S j z.2 = z.1} := by
    intro z hz
    obtain ⟨hprop, hmem⟩ := hWcapture z hz.1
    let y' : SphereCorrespondenceTarget m := ⟨(z.1, infinityValue z.2), hprop⟩
    have ht : ‖z.2‖ < δ := by simpa [BranchValueCylinder] using hz.2
    exact hfamily z.2 (ht.trans_le hδ₁) y' rfl hmem
  have hforward : ∀ t : ℂ, ‖t‖ < δ → ∀ j : ι,
      sphereLogDerivative m g (P j t).1 = infinityValue t ∧
      sphereLogDerivative m (reflection g) (P j t).2 = infinityValue t := by
    intro t ht j
    have hfam := hfamilyW (ImageBranch (S j) 1 0 t) (hbranchW j t ht)
    simp only [ImageBranch, pow_one, zero_add] at hfam
    have hmem : P j t ∈ InversePairs (sphereLogDerivative m g)
        (sphereLogDerivative m (reflection g)) (S j t) (infinityValue t) := by
      rw [hfam]
      exact ⟨j, rfl, rfl⟩
    exact ⟨hmem.2.1, hmem.2.2⟩
  have hcover : ∀ z ∈ W, z ∈ ReciprocalLogDerivativeImage m g ↔
      z ∈ ⋃ j : ι, ImageBranch (S j) 1 0 '' ball 0 δ := by
    intro z hz
    have ht : ‖z.2‖ < δ := by simpa [BranchValueCylinder] using hz.2
    constructor
    · rintro ⟨zw, hzw⟩
      rw [hfamilyW z hz] at hzw
      obtain ⟨j, hj, _⟩ := hzw
      apply mem_iUnion.mpr
      refine ⟨j, z.2, by simpa [mem_ball_iff_norm] using ht, ?_⟩
      exact Prod.ext hj (by simp [ImageBranch])
    · rintro himage
      obtain ⟨j, t, ht, heq⟩ := mem_iUnion.mp himage
      have ht' : ‖t‖ < δ := by simpa [mem_ball_iff_norm] using ht
      rw [← heq]
      have hf := hforward t ht' j
      simp only [ImageBranch, pow_one, zero_add]
      change (InversePairs (sphereLogDerivative m g) (sphereLogDerivative m (reflection g))
        (S j t) (infinityValue t)).Nonempty
      exact ⟨P j t, rfl, hf.1, hf.2⟩
  refine ⟨⟨ι, inferInstance, δ, hδ, P, S, fun _ _ => rfl, ?_, ?_, ?_,
    infinitySphereProduct_zero C, hforward, W, hW, hyW,
    fun z hz => (hWcapture z hz.1).1, fun _ hz => hz.2, hbranchW, hcover, ?_,
    fun t ht => hcmp t (ht.trans_le hδ₄)⟩⟩
  · exact fun j => (C j).analyticA
  · exact fun j => (C j).analyticB
  · intro j t ht
    have hnorm : ‖t‖ ≤ δ := by simpa [mem_closedBall, dist_zero_right] using ht
    exact hlocalAnalytic (by simpa [dist_zero_right] using hnorm.trans_lt hδ₃) j
  · intro t ht j
    simpa [ImageBranch] using hfamilyW (ImageBranch (S j) 1 0 t) (hbranchW j t ht)

end

end MaximumModulus
