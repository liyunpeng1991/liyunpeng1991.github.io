module

public import MaximumModulus.InverseRootChart
public import MaximumModulus.SmallFibers
public import MaximumModulus.BranchCollision

@[expose] public section

/-!
# Complete finite families of local physical inverse pairs

Two inverse-root charts can be expressed over the common power parameter of exponent
`kA * kB`. The indices are actual roots of unity. The family enumerates every physical
pair in the two chart sources and is injective on its indices for nonzero parameters.
Its product coordinate is analytic, so finite analytic collision comparisons apply to it.
-/

open Filter
open scoped Topology

namespace MaximumModulus

noncomputable section

def LocalCommonValuePairs (A B : ℂ → ℂ) (U V : Set ℂ) (p : ℂ) : Set (ℂ × ℂ) :=
  {zw | zw.1 ∈ U ∧ zw.2 ∈ V ∧ A zw.1 = p ∧ B zw.2 = p}

def LocalInversePairs (A B : ℂ → ℂ) (U V : Set ℂ) (s p : ℂ) : Set (ℂ × ℂ) :=
  InversePairs A B s p ∩ (U ×ˢ V)

def RootPairIndices (kA kB : ℕ) : Set (ℂ × ℂ) :=
  {ω : ℂ | ω ^ kA = 1} ×ˢ {ξ : ℂ | ξ ^ kB = 1}

def InverseRootPair (eA eB : OpenPartialHomeomorph ℂ ℂ) (kA kB : ℕ)
    (η : ℂ × ℂ) (t : ℂ) : ℂ × ℂ :=
  (eA.symm (η.1 * t ^ kB), eB.symm (η.2 * t ^ kA))

def InverseRootProduct (eA eB : OpenPartialHomeomorph ℂ ℂ) (kA kB : ℕ)
    (η : ℂ × ℂ) (t : ℂ) : ℂ :=
  (InverseRootPair eA eB kA kB η t).1 * (InverseRootPair eA eB kA kB η t).2

theorem rootPairIndices_finite {kA kB : ℕ} (hkA : 0 < kA) (hkB : 0 < kB) :
    (RootPairIndices kA kB).Finite :=
  (power_fiber_finite_ncard_le kA hkA 1).1.prod
    (power_fiber_finite_ncard_le kB hkB 1).1

theorem localCommonValuePairs_eq_prod (A B : ℂ → ℂ) (U V : Set ℂ) (p : ℂ) :
    LocalCommonValuePairs A B U V p =
      {z : ℂ | z ∈ U ∧ A z = p} ×ˢ {w : ℂ | w ∈ V ∧ B w = p} := by
  ext zw
  simp only [LocalCommonValuePairs, Set.mem_ofPred_eq, Set.mem_prod]
  simp only [and_assoc, and_left_comm, and_comm]

theorem analytic_inverseRoot_product {eA eB : OpenPartialHomeomorph ℂ ℂ}
    (hA : AnalyticAt ℂ eA.symm 0) (hB : AnalyticAt ℂ eB.symm 0)
    {kA kB : ℕ} (hkA : 0 < kA) (hkB : 0 < kB) (η : ℂ × ℂ) :
    AnalyticAt ℂ (InverseRootProduct eA eB kA kB η) 0 :=
  (analytic_inverseRoot_branch hA hkB η.1).mul
    (analytic_inverseRoot_branch hB hkA η.2)

/-- The product and common value of every member of an enumerated pair family give an
actual inverse pair in the original correspondence. -/
theorem inverseRootPair_mem_inversePairs {A B : ℂ → ℂ}
    {eA eB : OpenPartialHomeomorph ℂ ℂ} {kA kB : ℕ} {p t : ℂ}
    (hcapture : LocalCommonValuePairs A B eA.source eB.source p =
      (fun η => InverseRootPair eA eB kA kB η t) '' RootPairIndices kA kB)
    {η : ℂ × ℂ} (hη : η ∈ RootPairIndices kA kB) :
    InverseRootPair eA eB kA kB η t ∈
      InversePairs A B (InverseRootProduct eA eB kA kB η t) p := by
  have hp : InverseRootPair eA eB kA kB η t ∈
      LocalCommonValuePairs A B eA.source eB.source p := by
    rw [hcapture]
    exact ⟨η, hη, rfl⟩
  exact ⟨rfl, hp.2.2.1, hp.2.2.2⟩

/-- Fixing the product coordinate filters the complete family by its actual analytic
product values. -/
theorem localInversePairs_eq_filtered_family {A B : ℂ → ℂ}
    {eA eB : OpenPartialHomeomorph ℂ ℂ} {kA kB : ℕ} {p t : ℂ}
    (hcapture : LocalCommonValuePairs A B eA.source eB.source p =
      (fun η => InverseRootPair eA eB kA kB η t) '' RootPairIndices kA kB) (s : ℂ) :
    LocalInversePairs A B eA.source eB.source s p =
      (fun η => InverseRootPair eA eB kA kB η t) ''
        {η : ℂ × ℂ | η ∈ RootPairIndices kA kB ∧ InverseRootProduct eA eB kA kB η t = s} := by
  ext zw
  constructor
  · intro hzw
    have hlocal : zw ∈ LocalCommonValuePairs A B eA.source eB.source p :=
      ⟨hzw.2.1, hzw.2.2, hzw.1.2.1, hzw.1.2.2⟩
    rw [hcapture] at hlocal
    obtain ⟨η, hη, hpair⟩ := hlocal
    change InverseRootPair eA eB kA kB η t = zw at hpair
    refine ⟨η, ⟨hη, ?_⟩, hpair⟩
    change (InverseRootPair eA eB kA kB η t).1 *
      (InverseRootPair eA eB kA kB η t).2 = s
    rw [hpair]
    exact hzw.1.1
  · rintro ⟨η, ⟨hη, hprod⟩, rfl⟩
    have hlocal : InverseRootPair eA eB kA kB η t ∈
        LocalCommonValuePairs A B eA.source eB.source p := by
      rw [hcapture]
      exact ⟨η, hη, rfl⟩
    exact ⟨⟨hprod, hlocal.2.2.1, hlocal.2.2.2⟩, hlocal.1, hlocal.2.1⟩

/-- Actual local fibers are finite, and their cardinalities equal the corresponding
finite index classes whenever the complete pair family is injective. -/
theorem localInversePairs_finite_ncard {A B : ℂ → ℂ}
    {eA eB : OpenPartialHomeomorph ℂ ℂ} {kA kB : ℕ} {p t : ℂ}
    (hindices : (RootPairIndices kA kB).Finite)
    (hcapture : LocalCommonValuePairs A B eA.source eB.source p =
      (fun η => InverseRootPair eA eB kA kB η t) '' RootPairIndices kA kB)
    (hinj : Set.InjOn (fun η => InverseRootPair eA eB kA kB η t) (RootPairIndices kA kB))
    (s : ℂ) :
    (LocalInversePairs A B eA.source eB.source s p).Finite ∧
      (LocalInversePairs A B eA.source eB.source s p).ncard =
        {η : ℂ × ℂ | η ∈ RootPairIndices kA kB ∧
          InverseRootProduct eA eB kA kB η t = s}.ncard := by
  have hsub : {η : ℂ × ℂ | η ∈ RootPairIndices kA kB ∧
      InverseRootProduct eA eB kA kB η t = s} ⊆ RootPairIndices kA kB := fun _ hη => hη.1
  rw [localInversePairs_eq_filtered_family hcapture s]
  exact ⟨(hindices.subset hsub).image _, (hinj.mono hsub).ncard_image⟩

/-- Product collision classes of the finite family stabilize near zero. -/
theorem inverseRoot_product_classes_radius {eA eB : OpenPartialHomeomorph ℂ ℂ}
    (hA : AnalyticAt ℂ eA.symm 0) (hB : AnalyticAt ℂ eB.symm 0)
    {kA kB : ℕ} (hkA : 0 < kA) (hkB : 0 < kB) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
      ∀ η ∈ RootPairIndices kA kB,
        {ξ : ℂ × ℂ | ξ ∈ RootPairIndices kA kB ∧
          InverseRootProduct eA eB kA kB ξ t = InverseRootProduct eA eB kA kB η t} =
        {ξ : ℂ × ℂ | ξ ∈ RootPairIndices kA kB ∧
          ∀ᶠ u in 𝓝 (0 : ℂ),
            InverseRootProduct eA eB kA kB ξ u = InverseRootProduct eA eB kA kB η u} := by
  have : Finite (RootPairIndices kA kB) := (rootPairIndices_finite hkA hkB).to_subtype
  obtain ⟨ε, hε, hclasses⟩ := finite_imageBranch_classes_radius
    (S := fun ξ : RootPairIndices kA kB => InverseRootProduct eA eB kA kB ξ.val)
    (fun ξ => analytic_inverseRoot_product hA hB hkA hkB ξ.val)
  refine ⟨ε, hε, fun t ht hne η hη => ?_⟩
  have heq := hclasses t ht hne ⟨η, hη⟩
  ext ξ
  by_cases hξ : ξ ∈ RootPairIndices kA kB
  · simpa only [Set.mem_ofPred_eq, hξ, true_and] using
      Set.ext_iff.mp heq (⟨ξ, hξ⟩ : RootPairIndices kA kB)
  · simp only [Set.mem_ofPred_eq, hξ, false_and]

/-- Two analytic germs with the same value admit a finite analytic family that exactly
enumerates all local physical inverse pairs over their common power parameter. -/
theorem analytic_inverseRoot_pair_family {A B : ℂ → ℂ} {a b : ℂ}
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B b) (hcommon : A a = B b)
    (hAfin : analyticOrderAt (fun z => A z - A a) a ≠ ⊤)
    (hBfin : analyticOrderAt (fun z => B z - B b) b ≠ ⊤) :
    ∃ kA kB : ℕ, 0 < kA ∧ 0 < kB ∧
      kA = analyticOrderNatAt (fun z => A z - A a) a ∧
      kB = analyticOrderNatAt (fun z => B z - B b) b ∧
      ∃ eA eB : OpenPartialHomeomorph ℂ ℂ,
        a ∈ eA.source ∧ b ∈ eB.source ∧ eA.symm 0 = a ∧ eB.symm 0 = b ∧
        (RootPairIndices kA kB).Finite ∧
        (∀ η : ℂ × ℂ, AnalyticAt ℂ (InverseRootProduct eA eB kA kB η) 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
          LocalCommonValuePairs A B eA.source eB.source (A a + t ^ (kA * kB)) =
            (fun η => InverseRootPair eA eB kA kB η t) '' RootPairIndices kA kB ∧
          Set.InjOn (fun η => InverseRootPair eA eB kA kB η t) (RootPairIndices kA kB) := by
  obtain ⟨kA, hkA, horderA, eA, ha, hzeroA, hcenterA, hψA, hfamA⟩ :=
    analytic_inverseRoot_family hA hAfin
  obtain ⟨kB, hkB, horderB, eB, hb, hzeroB, hcenterB, hψB, hfamB⟩ :=
    analytic_inverseRoot_family hB hBfin
  obtain ⟨_, εA, hεA, hlocalA⟩ := hfamA kB hkB
  obtain ⟨_, εB, hεB, hlocalB⟩ := hfamB kA hkA
  refine ⟨kA, kB, hkA, hkB, horderA, horderB, eA, eB, ha, hb, hcenterA, hcenterB,
    rootPairIndices_finite hkA hkB, fun η => analytic_inverseRoot_product hψA hψB hkA hkB η,
    min εA εB, lt_min hεA hεB, fun t ht hne => ?_⟩
  obtain ⟨heqA, hinjA⟩ := hlocalA t (ht.trans_le (min_le_left _ _)) hne
  obtain ⟨heqB, hinjB⟩ := hlocalB t (ht.trans_le (min_le_right _ _)) hne
  rw [← hcommon, Nat.mul_comm kB kA] at heqB
  constructor
  · rw [localCommonValuePairs_eq_prod, heqA, heqB, Set.prod_image_image_eq]
    rfl
  · intro η hη η' hη' heq
    exact Prod.ext
      (hinjA hη.1 hη'.1 (congrArg Prod.fst heq))
      (hinjB hη.2 hη'.2 (congrArg Prod.snd heq))

/-- Every selected branch has a constant actual local inverse-pair count on a sufficiently
small punctured parameter disk. This count is proved equal to a finite germ collision class;
no abstract generic-degree theorem is assumed. -/
theorem analytic_inverseRoot_local_fiber_count {A B : ℂ → ℂ} {a b : ℂ}
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B b) (hcommon : A a = B b)
    (hAfin : analyticOrderAt (fun z => A z - A a) a ≠ ⊤)
    (hBfin : analyticOrderAt (fun z => B z - B b) b ≠ ⊤) :
    ∃ kA kB : ℕ, 0 < kA ∧ 0 < kB ∧
      ∃ eA eB : OpenPartialHomeomorph ℂ ℂ,
        a ∈ eA.source ∧ b ∈ eB.source ∧ eA.symm 0 = a ∧ eB.symm 0 = b ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℂ, ‖t‖ < ε → t ≠ 0 →
          ∀ η ∈ RootPairIndices kA kB,
            (LocalInversePairs A B eA.source eB.source
              (InverseRootProduct eA eB kA kB η t) (A a + t ^ (kA * kB))).Finite ∧
            (LocalInversePairs A B eA.source eB.source
              (InverseRootProduct eA eB kA kB η t) (A a + t ^ (kA * kB))).ncard =
              {ξ : ℂ × ℂ | ξ ∈ RootPairIndices kA kB ∧
                ∀ᶠ u in 𝓝 (0 : ℂ), InverseRootProduct eA eB kA kB ξ u =
                  InverseRootProduct eA eB kA kB η u}.ncard := by
  obtain ⟨kA, kB, hkA, hkB, _, _, eA, eB, ha, hb, hcenterA, hcenterB,
    hindices, hproduct, εP, hεP, hpair⟩ :=
    analytic_inverseRoot_pair_family hA hB hcommon hAfin hBfin
  have : Finite (RootPairIndices kA kB) := hindices.to_subtype
  obtain ⟨εC, hεC, hclasses⟩ := finite_imageBranch_classes_radius
    (S := fun ξ : RootPairIndices kA kB => InverseRootProduct eA eB kA kB ξ.val)
    (fun ξ => hproduct ξ.val)
  refine ⟨kA, kB, hkA, hkB, eA, eB, ha, hb, hcenterA, hcenterB,
    min εP εC, lt_min hεP hεC, fun t ht hne η hη => ?_⟩
  obtain ⟨hcapture, hinj⟩ := hpair t (ht.trans_le (min_le_left _ _)) hne
  obtain ⟨hfinite, hcard⟩ := localInversePairs_finite_ncard hindices hcapture hinj
    (InverseRootProduct eA eB kA kB η t)
  refine ⟨hfinite, hcard.trans ?_⟩
  apply congrArg Set.ncard
  have heq := hclasses t (ht.trans_le (min_le_right _ _)) hne ⟨η, hη⟩
  ext ξ
  by_cases hξ : ξ ∈ RootPairIndices kA kB
  · simpa only [Set.mem_ofPred_eq, hξ, true_and] using
      Set.ext_iff.mp heq (⟨ξ, hξ⟩ : RootPairIndices kA kB)
  · simp only [Set.mem_ofPred_eq, hξ, false_and]

end

end MaximumModulus
