module

public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Topology.Compactness.CompactSystem
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Kolmogorov extension theorem (arbitrary index type)

Let `ι` be an **arbitrary** index type and `X : ι → Type*` a family of measurable spaces.
For a projective family `P J` of finite measures on `Π j : J, X j` (`J : Finset ι`), whose
members are inner regular with respect to closed compact measurable sets, the projective
family content on measurable cylinders is continuous at `∅` along decreasing sequences
(`projectiveFamilyContent_tendsto_zero_of_innerRegular`), hence σ-subadditive; the
Carathéodory extension `projectiveLimitOfInnerRegular` is a projective limit of `P` on the
product σ-algebra of `Π i, X i`.

For Polish Borel coordinate spaces the inner-regularity hypothesis holds automatically
(`innerRegularClosedCompact_of_polish`); this gives the classical theorem
`isProjectiveLimit_kolmogorovExtension` with `kolmogorovExtension P hP`, which is a probability
measure when every `P J` is (and unique, by `IsProjectiveLimit.unique`).

The topological core is `isCompactSystem_closedCompactCylinders`: cylinders with closed
compact bases form a compact system in `Π i, X i` for arbitrary topological coordinate spaces
(no Hausdorff assumption).

Measure: the product σ-algebra `MeasurableSpace.pi`.  No countability of `ι` is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {ι : Type*} {X : ι → Type*}

section CompactSystem

variable [∀ i, TopologicalSpace (X i)]

/-- **Cylinders with closed compact bases form a compact system.**  For an arbitrary index
type and arbitrary topological coordinate spaces: if countably many closed compact
cylinders have all finite intersections nonempty, their total intersection is nonempty. -/
theorem isCompactSystem_closedCompactCylinders :
    IsCompactSystem (closedCompactCylinders X) := by
  classical
  refine IsCompactSystem.of_nonempty_iInter fun C hC hne => ?_
  let s : ℕ → Finset ι := fun n => closedCompactCylinders.finset (hC n)
  let K : ∀ n, Set (Π j : s n, X j) := fun n => closedCompactCylinders.set (hC n)
  have hCeq : ∀ n, C n = cylinder (s n) (K n) := fun n =>
    closedCompactCylinders.eq_cylinder (hC n)
  have hKc : ∀ n, IsCompact (K n) := fun n => closedCompactCylinders.isCompact (hC n)
  let w : ℕ → Π i, X i := fun n => (hne n).some
  have hw : ∀ n, w n ∈ C n := fun n => dissipate_subset le_rfl (hne n).some_mem
  have hmemK : ∀ {n : ℕ} {y : Π i, X i}, y ∈ C n → (s n).restrict y ∈ K n := by
    intro n y hy
    rw [hCeq n] at hy
    exact hy
  let L : ∀ i, Set (X i) := fun i =>
    if h : ∃ n, i ∈ s n then
      (fun y : Π j : s (Nat.find h), X j => y ⟨i, Nat.find_spec h⟩) '' K (Nat.find h)
    else {w 0 i}
  have hLc : ∀ i, IsCompact (L i) := by
    intro i
    by_cases h : ∃ n, i ∈ s n
    · simp only [L, dite_eq_left h]
      exact (hKc _).image (continuous_apply _)
    · simp only [L, dite_eq_right h]
      exact isCompact_singleton
  have hmemL : ∀ (i : ι) (h : ∃ n, i ∈ s n) {y : Π i, X i}, y ∈ C (Nat.find h) →
      y i ∈ L i := by
    intro i h y hy
    simp only [L, dite_eq_left h]
    exact ⟨_, hmemK hy, rfl⟩
  have hbox : IsCompact (Set.pi univ L) := isCompact_univ_pi hLc
  have hclosed : ∀ n, IsClosed (C n) := by
    intro n
    rw [hCeq n]
    exact (closedCompactCylinders.isClosed (hC n)).cylinder (s n)
  have key := hbox.inter_iInter_nonempty C hclosed ?_
  · obtain ⟨x, -, hx⟩ := key
    exact ⟨x, hx⟩
  intro u
  let N : ℕ := u.sup id
  obtain ⟨y, hy⟩ := hne N
  have hyC : ∀ k ≤ N, y ∈ C k := fun k hk => dissipate_subset hk hy
  let z : Π i, X i := fun i =>
    if h : ∃ n, i ∈ s n then (if Nat.find h ≤ N then y i else w (Nat.find h) i) else w 0 i
  refine ⟨z, ?_, ?_⟩
  · intro i _
    by_cases h : ∃ n, i ∈ s n
    · by_cases hN : Nat.find h ≤ N
      · have : z i = y i := by simp only [z, dite_eq_left h, ite_eq_left hN]
        rw [this]
        exact hmemL i h (hyC _ hN)
      · have : z i = w (Nat.find h) i := by simp only [z, dite_eq_left h, ite_eq_right hN]
        rw [this]
        exact hmemL i h (hw _)
    · have : z i = w 0 i := by simp only [z, dite_eq_right h]
      rw [this]
      simp only [L, dite_eq_right h, mem_singleton_iff]
  · refine mem_iInter₂.2 fun k hk => ?_
    have hkN : k ≤ N := Finset.le_sup (f := id) hk
    have hrestr : (s k).restrict z = (s k).restrict y := by
      funext j
      have h : ∃ n, (j : ι) ∈ s n := ⟨k, j.2⟩
      have hle : Nat.find h ≤ N := (Nat.find_min' h j.2).trans hkN
      simp only [Finset.restrict, z, dite_eq_left h, ite_eq_left hle]
    rw [hCeq k]
    change (s k).restrict z ∈ K k
    rw [hrestr]
    exact hmemK (hyC k hkN)

end CompactSystem

section Content

variable [∀ i, MeasurableSpace (X i)]

/-- Inner regularity of every finite-dimensional measure of a family with respect to closed,
compact, measurable sets (the hypothesis of the Kolmogorov extension theorem). -/
def InnerRegularClosedCompact [∀ i, TopologicalSpace (X i)]
    (P : ∀ J : Finset ι, Measure (Π j : J, X j)) : Prop :=
  ∀ (J : Finset ι) (S : Set (Π j : J, X j)), MeasurableSet S → ∀ ε : ℝ≥0∞, ε ≠ 0 →
    ∃ K ⊆ S, IsCompact K ∧ IsClosed K ∧ MeasurableSet K ∧ P J (S \ K) < ε

/-- **Continuity at `∅` of the projective family content** (the analytic core of the Kolmogorov
extension theorem): for a projective family of finite measures that is inner regular for
closed compact sets, the content of a decreasing sequence of measurable cylinders with empty
intersection tends to `0`.  Arbitrary index type. -/
theorem projectiveFamilyContent_tendsto_zero_of_innerRegular [∀ i, TopologicalSpace (X i)]
    {P : ∀ J : Finset ι, Measure (Π j : J, X j)} (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsFiniteMeasure (P J)] (hreg : InnerRegularClosedCompact P)
    {A : ℕ → Set (Π i, X i)} (hA : ∀ n, A n ∈ measurableCylinders X) (hanti : Antitone A)
    (hempty : ⋂ n, A n = ∅) :
    Tendsto (fun n => projectiveFamilyContent hP (A n)) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  let s : ℕ → Finset ι := fun n => measurableCylinders.finset (hA n)
  let S : ∀ n, Set (Π j : s n, X j) := fun n => measurableCylinders.set (hA n)
  have hS : ∀ n, MeasurableSet (S n) := fun n => measurableCylinders.measurableSet (hA n)
  have hAeq : ∀ n, A n = cylinder (s n) (S n) := fun n => measurableCylinders.eq_cylinder (hA n)
  have hK : ∀ n, ∃ K ⊆ S n, IsCompact K ∧ IsClosed K ∧ MeasurableSet K ∧
      P (s n) (S n \ K) < δ n := fun n =>
    hreg (s n) (S n) (hS n) (δ n) (by exact_mod_cast (hδpos n).ne')
  choose K hKS hKc hKcl hKm hKloss using hK
  let C : ℕ → Set (Π i, X i) := fun n => cylinder (s n) (K n)
  have hCcc : ∀ n, C n ∈ closedCompactCylinders X := fun n =>
    cylinder_mem_closedCompactCylinders _ _ (hKcl n) (hKc n)
  have hCA : ∀ n, C n ⊆ A n := by
    intro n x hx
    rw [hAeq n]
    exact hKS n hx
  have hCempty : ⋂ n, C n = ∅ :=
    subset_empty_iff.1 ((iInter_mono hCA).trans hempty.le)
  obtain ⟨N, hN⟩ := isCompactSystem_closedCompactCylinders C hCcc hCempty
  refine ⟨N, fun n hn => ?_⟩
  have hDmem : ∀ k, A k \ C k ∈ measurableCylinders X := fun k =>
    sdiff_mem_measurableCylinders (hA k)
      (cylinder_mem_measurableCylinders _ _ (hKm k))
  have hsub : A n ⊆ ⋃ k ≤ N, (A k \ C k) := by
    intro x hx
    have hxN : x ∉ dissipate C N := by rw [hN]; exact notMem_empty x
    simp only [dissipate_def, mem_iInter, not_forall] at hxN
    obtain ⟨k, hk, hxk⟩ := hxN
    exact mem_iUnion₂.2 ⟨k, hk, hanti (hk.trans hn) hx, hxk⟩
  have hUmem : (⋃ k ≤ N, (A k \ C k)) ∈ measurableCylinders X :=
    isSetRing_measurableCylinders.iUnion_le_mem hDmem N
  calc projectiveFamilyContent hP (A n)
      ≤ projectiveFamilyContent hP (⋃ k ≤ N, (A k \ C k)) :=
        projectiveFamilyContent_mono hP (hA n) hUmem hsub
    _ ≤ ∑ k ∈ Finset.range (N + 1), projectiveFamilyContent hP (A k \ C k) :=
        projectiveFamilyContent_iUnion_le hP hDmem N
    _ = ∑ k ∈ Finset.range (N + 1), P (s k) (S k \ K k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hAeq k, sdiff_cylinder_same]
        exact projectiveFamilyContent_cylinder hP ((hS k).diff (hKm k))
    _ ≤ ∑ k ∈ Finset.range (N + 1), (δ k : ℝ≥0∞) :=
        Finset.sum_le_sum fun k _ => (hKloss k).le
    _ ≤ ∑' k, (δ k : ℝ≥0∞) := ENNReal.sum_le_tsum _
    _ ≤ ε := hδsum.le

/-- The projective family content of an inner regular projective family of finite measures is
σ-subadditive on measurable cylinders. -/
theorem isSigmaSubadditive_projectiveFamilyContent_of_innerRegular
    [∀ i, TopologicalSpace (X i)]
    {P : ∀ J : Finset ι, Measure (Π j : J, X j)} (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsFiniteMeasure (P J)] (hreg : InnerRegularClosedCompact P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders ?_
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent hP) (fun _ _ => projectiveFamilyContent_ne_top hP)
    (fun _ hA hanti hempty =>
      projectiveFamilyContent_tendsto_zero_of_innerRegular hP hreg hA hanti hempty)

/-- The Carathéodory extension of an inner regular projective family of finite measures to the
product σ-algebra on `Π i, X i`. -/
def projectiveLimitOfInnerRegular [∀ i, TopologicalSpace (X i)]
    (P : ∀ J : Finset ι, Measure (Π j : J, X j)) (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsFiniteMeasure (P J)] (hreg : InnerRegularClosedCompact P) :
    Measure (Π i, X i) :=
  (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    (isSigmaSubadditive_projectiveFamilyContent_of_innerRegular hP hreg)

/-- **Kolmogorov extension (inner regular form, arbitrary index type).**  The Carathéodory
extension is a projective limit of `P`: every finite-dimensional marginal is `P J`. -/
theorem isProjectiveLimit_projectiveLimitOfInnerRegular [∀ i, TopologicalSpace (X i)]
    (P : ∀ J : Finset ι, Measure (Π j : J, X j)) (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsFiniteMeasure (P J)] (hreg : InnerRegularClosedCompact P) :
    IsProjectiveLimit (projectiveLimitOfInnerRegular P hP hreg) P := by
  intro J
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply (Finset.measurable_restrict J) hS]
  change projectiveLimitOfInnerRegular P hP hreg (cylinder J S) = P J S
  rw [projectiveLimitOfInnerRegular, AddContent.measure_eq _ isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.symm _ (cylinder_mem_measurableCylinders J S hS)]
  exact projectiveFamilyContent_cylinder hP hS

end Content

section Polish

variable [∀ i, MeasurableSpace (X i)] [∀ i, TopologicalSpace (X i)] [∀ i, PolishSpace (X i)]
  [∀ i, BorelSpace (X i)]

/-- For Polish Borel coordinate spaces, every family of finite measures on the
finite-dimensional products is inner regular for closed compact sets. -/
theorem innerRegularClosedCompact_of_polish
    (P : ∀ J : Finset ι, Measure (Π j : J, X j)) [∀ J, IsFiniteMeasure (P J)] :
    InnerRegularClosedCompact P := by
  intro J S hS ε hε
  obtain ⟨K, hKS, hKc, hKcl, hK⟩ :=
    hS.exists_isCompact_isClosed_sdiff_lt (μ := P J) (measure_ne_top _ _) hε
  exact ⟨K, hKS, hKc, hKcl, hKcl.measurableSet, hK⟩

/-- **The Kolmogorov extension** of a projective family of finite measures with Polish Borel
coordinate spaces, on the product σ-algebra of `Π i, X i` (arbitrary index type). -/
def kolmogorovExtension (P : ∀ J : Finset ι, Measure (Π j : J, X j))
    (hP : IsProjectiveMeasureFamily P) [∀ J, IsFiniteMeasure (P J)] : Measure (Π i, X i) :=
  projectiveLimitOfInnerRegular P hP (innerRegularClosedCompact_of_polish P)

/-- **Kolmogorov extension theorem.**  Arbitrary index type `ι`, Polish Borel coordinate spaces,
projective family of finite measures: `kolmogorovExtension P hP` has every finite-dimensional
marginal equal to `P J`. -/
theorem isProjectiveLimit_kolmogorovExtension (P : ∀ J : Finset ι, Measure (Π j : J, X j))
    (hP : IsProjectiveMeasureFamily P) [∀ J, IsFiniteMeasure (P J)] :
    IsProjectiveLimit (kolmogorovExtension P hP) P :=
  isProjectiveLimit_projectiveLimitOfInnerRegular P hP _

/-- The Kolmogorov extension of a projective family of probability measures is a probability
measure. -/
theorem isProbabilityMeasure_kolmogorovExtension
    (P : ∀ J : Finset ι, Measure (Π j : J, X j)) (hP : IsProjectiveMeasureFamily P)
    [∀ J, IsProbabilityMeasure (P J)] :
    IsProbabilityMeasure (kolmogorovExtension P hP) :=
  (isProjectiveLimit_kolmogorovExtension P hP).isProbabilityMeasure

/-- Existence form of the Kolmogorov extension theorem for probability families. -/
theorem exists_isProjectiveLimit_of_polish (P : ∀ J : Finset ι, Measure (Π j : J, X j))
    (hP : IsProjectiveMeasureFamily P) [∀ J, IsProbabilityMeasure (P J)] :
    ∃ μ : Measure (Π i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P :=
  ⟨kolmogorovExtension P hP, isProbabilityMeasure_kolmogorovExtension P hP,
    isProjectiveLimit_kolmogorovExtension P hP⟩

/-- Finite-dimensional marginal identity for the Kolmogorov extension on one cylinder. -/
theorem kolmogorovExtension_cylinder (P : ∀ J : Finset ι, Measure (Π j : J, X j))
    (hP : IsProjectiveMeasureFamily P) [∀ J, IsFiniteMeasure (P J)] (J : Finset ι)
    {S : Set (Π j : J, X j)} (hS : MeasurableSet S) :
    kolmogorovExtension P hP (cylinder J S) = P J S :=
  (isProjectiveLimit_kolmogorovExtension P hP).measure_cylinder J hS

end Polish

end BlockBand.Diffusion
