module

public import BlockBand.Counting.OpenIntervalEvaluation
public import Mathlib.Algebra.Order.ToIntervalMod
public import BlockBand.Critical.DecoratedSine.Quantile

/-!
# Measurable enumeration of the points of a locally finite point measure on `ℝ`

The points of a locally finite point measure `ξ` on `ℝ` are enumerated window by window: in each
unit window `[n, n + 1)`, `windowAtom ξ n j` is the `j`-th point from the left, for
`j < windowCount ξ n`. Then `ξ` is the sum of the Dirac masses at these points
(`measure_eq_sum_groundAtom`), and the counts and points depend measurably on `ξ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.DecoratedSine

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

/-!
## Interval masses are measurable
-/

theorem measurable_measure_Icc (a b : ℝ) :
    Measurable fun ξ : VaguePointMeasure ℝ => ξ.measure (Icc a b) := by
  set s : ℕ → Set ℝ := fun k => Ioo (a - 1 / ((k : ℝ) + 1)) (b + 1 / ((k : ℝ) + 1))
  have hanti : Antitone s := by
    intro k l hkl
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hkl
      linarith
    have := one_div_le_one_div_of_le hk hkl'
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  have he : (⋂ k, s k) = Icc a b := by
    ext x
    simp only [s, mem_iInter, mem_Ioo, mem_Icc]
    refine ⟨fun hx => ⟨?_, ?_⟩, fun hx k => ?_⟩
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      linarith [(hx k).1]
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      linarith [(hx k).2]
    · have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      constructor <;> linarith [hx.1, hx.2]
  have hfun : (fun ξ : VaguePointMeasure ℝ => ξ.measure (Icc a b)) =
      fun ξ => ⨅ k, ξ.measure (s k) := by
    funext ξ
    rw [← he]
    refine hanti.measure_iInter (fun k => measurableSet_Ioo.nullMeasurableSet) ⟨0, ?_⟩
    exact (lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self)
      (ξ.finite_on_compact _ isCompact_Icc)).ne
  rw [hfun]
  exact Measurable.iInf fun k => BlockBand.Counting.measurable_vague_Ioo_mass _ _

theorem measurable_measure_Ico (a b : ℝ) :
    Measurable fun ξ : VaguePointMeasure ℝ => ξ.measure (Ico a b) := by
  set s : ℕ → Set ℝ := fun k => Icc a (b - 1 / ((k : ℝ) + 1))
  have hmono : Monotone s := by
    intro k l hkl
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hkl' : (k : ℝ) + 1 ≤ (l : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hkl
      linarith
    have := one_div_le_one_div_of_le hk hkl'
    exact Icc_subset_Icc le_rfl (by linarith)
  have he : (⋃ k, s k) = Ico a b := by
    ext x
    simp only [s, mem_iUnion, mem_Icc, mem_Ico]
    refine ⟨fun ⟨k, hk⟩ => ⟨hk.1, ?_⟩, fun hx => ?_⟩
    · have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith [hk.2]
    · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hx.2)
      exact ⟨k, hx.1, by linarith⟩
  have hfun : (fun ξ : VaguePointMeasure ℝ => ξ.measure (Ico a b)) =
      fun ξ => ⨆ k, ξ.measure (s k) := by
    funext ξ
    rw [← he]
    exact hmono.measure_iUnion
  rw [hfun]
  exact Measurable.iSup fun k => measurable_measure_Icc _ _

/-!
## Unit windows
-/

/-- The unit window `[n, n + 1)`. -/
def window (n : ℤ) : Set ℝ :=
  Ico (n : ℝ) (n + 1)

theorem measurableSet_window (n : ℤ) : MeasurableSet (window n) :=
  measurableSet_Ico

theorem iUnion_window : (⋃ n : ℤ, window n) = univ :=
  iUnion_Ico_intCast ℝ

theorem pairwise_disjoint_window : Pairwise (Disjoint on window) :=
  pairwise_disjoint_Ico_intCast ℝ

theorem measure_window_lt_top (ξ : VaguePointMeasure ℝ) (n : ℤ) :
    ξ.measure (window n) < ∞ :=
  lt_of_le_of_lt (measure_mono Ico_subset_Icc_self) (ξ.finite_on_compact _ isCompact_Icc)

/-- The restriction of `ξ` to the window `[n, n + 1)`. -/
def windowMeasure (ξ : VaguePointMeasure ℝ) (n : ℤ) : Measure ℝ :=
  ξ.measure.restrict (window n)

instance (ξ : VaguePointMeasure ℝ) (n : ℤ) : IsFiniteMeasure (windowMeasure ξ n) :=
  ⟨by
    rw [windowMeasure, Measure.restrict_apply_univ]
    exact measure_window_lt_top ξ n⟩

/-- Number of points of `ξ` in the window `[n, n + 1)`. -/
def windowCount (ξ : VaguePointMeasure ℝ) (n : ℤ) : ℕ :=
  ⌊(ξ.measure (window n)).toReal⌋₊

theorem measure_window_eq (ξ : VaguePointMeasure ℝ) (n : ℤ) :
    ξ.measure (window n) = windowCount ξ n := by
  rcases ξ.integer_valued _ (measurableSet_window n) with h | ⟨k, hk⟩
  · exact absurd h (measure_window_lt_top ξ n).ne
  · rw [windowCount, hk, ENNReal.toReal_natCast, Nat.floor_natCast]

theorem windowMeasure_univ (ξ : VaguePointMeasure ℝ) (n : ℤ) :
    windowMeasure ξ n univ = windowCount ξ n := by
  rw [windowMeasure, Measure.restrict_apply_univ, measure_window_eq]

theorem hasNatCDF_windowMeasure (ξ : VaguePointMeasure ℝ) (n : ℤ) :
    HasNatCDF (windowMeasure ξ n) := by
  intro t
  rw [windowMeasure, Measure.restrict_apply measurableSet_Iic]
  rcases ξ.integer_valued _ (measurableSet_Iic.inter (measurableSet_window n)) with h | ⟨k, hk⟩
  · refine absurd h (ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right)
      (measure_window_lt_top ξ n)))
  · exact ⟨k, hk⟩

/-- The `j`-th point of `ξ` in the window `[n, n + 1)` (from the left), and the left endpoint
`n` when there are at most `j` points. -/
def windowAtom (ξ : VaguePointMeasure ℝ) (n : ℤ) (j : ℕ) : ℝ :=
  if j < windowCount ξ n then atomQuantile (windowMeasure ξ n) j else n

theorem windowMeasure_eq_sum_dirac (ξ : VaguePointMeasure ℝ) (n : ℤ) :
    windowMeasure ξ n =
      ∑ j ∈ Finset.range (windowCount ξ n), Measure.dirac (windowAtom ξ n j) := by
  rw [eq_sum_dirac_atomQuantile (windowMeasure_univ ξ n) (hasNatCDF_windowMeasure ξ n)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [windowAtom, ite_eq_left (Finset.mem_range.mp hj)]

theorem windowAtom_mem (ξ : VaguePointMeasure ℝ) (n : ℤ) {j : ℕ}
    (hj : j < windowCount ξ n) : windowAtom ξ n j ∈ window n := by
  by_contra hmem
  have h0 : windowMeasure ξ n (window n)ᶜ = 0 := by
    rw [windowMeasure, Measure.restrict_apply (measurableSet_window n).compl, compl_inter_self,
      measure_empty]
  rw [windowMeasure_eq_sum_dirac, Measure.coe_finsetSum, Finset.sum_apply,
    Finset.sum_eq_zero_iff] at h0
  have := h0 j (Finset.mem_range.mpr hj)
  rw [Measure.dirac_apply' _ (measurableSet_window n).compl,
    indicator_of_mem (mem_compl hmem)] at this
  exact one_ne_zero this

/-!
## The ground measure as a countable sum of Dirac masses
-/

/-- The Dirac mass at the `j`-th point of window `n`, or `0` when that point does not exist. -/
def groundAtom (ξ : VaguePointMeasure ℝ) (p : ℤ × ℕ) : Measure ℝ :=
  if p.2 < windowCount ξ p.1 then Measure.dirac (windowAtom ξ p.1 p.2) else 0

theorem finset_sum_dirac_eq_sum (N : ℕ) (x : ℕ → ℝ) :
    ∑ j ∈ Finset.range N, Measure.dirac (x j) =
      Measure.sum fun j : ℕ => if j < N then Measure.dirac (x j) else 0 := by
  ext s hs
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.sum_apply _ hs,
    tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [ite_eq_left (Finset.mem_range.mp hj)]
  · intro j hj
    rw [ite_eq_right (fun h => hj (Finset.mem_range.mpr h)), Measure.coe_zero, Pi.zero_apply]

/-- **Every locally finite point measure on `ℝ` is the sum of the Dirac masses at its window
points** `windowAtom ξ n j`, `j < windowCount ξ n`, `n ∈ ℤ`. -/
theorem measure_eq_sum_groundAtom (ξ : VaguePointMeasure ℝ) :
    ξ.measure = Measure.sum (groundAtom ξ) := by
  have h1 : ξ.measure = Measure.sum fun n : ℤ => windowMeasure ξ n := by
    rw [← Measure.restrict_univ (μ := ξ.measure), ← iUnion_window,
      Measure.restrict_iUnion pairwise_disjoint_window measurableSet_window]
    rfl
  rw [h1]
  simp_rw [windowMeasure_eq_sum_dirac, finset_sum_dirac_eq_sum]
  rw [Measure.sum_sum]
  rfl

/-!
## Measurability of the window points
-/

theorem measurable_windowMeasure_Iic (n : ℤ) (t : ℝ) :
    Measurable fun ξ : VaguePointMeasure ℝ => windowMeasure ξ n (Iic t) := by
  simp only [windowMeasure, Measure.restrict_apply measurableSet_Iic, window]
  by_cases ht : t < (n : ℝ) + 1
  · have he : Iic t ∩ Ico (n : ℝ) (n + 1) = Icc (n : ℝ) t := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ico, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, lt_of_le_of_lt h2 ht⟩
    rw [he]
    exact measurable_measure_Icc _ _
  · have he : Iic t ∩ Ico (n : ℝ) (n + 1) = Ico (n : ℝ) (n + 1) := by
      refine inter_eq_right.mpr fun x hx => ?_
      exact le_trans hx.2.le (not_lt.mp ht)
    rw [he]
    exact measurable_measure_Ico _ _

theorem measurableSet_lt_windowCount (n : ℤ) (j : ℕ) :
    MeasurableSet {ξ : VaguePointMeasure ℝ | j < windowCount ξ n} := by
  have he : {ξ : VaguePointMeasure ℝ | j < windowCount ξ n} =
      {ξ | (j : ℝ≥0∞) < ξ.measure (window n)} := by
    ext ξ
    simp only [mem_ofPred_eq, measure_window_eq]
    exact_mod_cast Iff.rfl
  rw [he]
  exact measurableSet_lt measurable_const (measurable_measure_Ico _ _)

theorem measurable_windowAtom (n : ℤ) (j : ℕ) :
    Measurable fun ξ : VaguePointMeasure ℝ => windowAtom ξ n j := by
  refine measurable_of_Iic fun s => ?_
  have he : (fun ξ : VaguePointMeasure ℝ => windowAtom ξ n j) ⁻¹' Iic s =
      ({ξ | j < windowCount ξ n} ∩ {ξ | (j : ℝ≥0∞) + 1 ≤ windowMeasure ξ n (Iic s)}) ∪
        ({ξ | j < windowCount ξ n}ᶜ ∩ {_ξ | (n : ℝ) ≤ s}) := by
    ext ξ
    simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
      windowAtom]
    by_cases hj : j < windowCount ξ n
    · rw [ite_eq_left hj, atomQuantile_le_iff (windowMeasure_univ ξ n) (hasNatCDF_windowMeasure ξ n) hj]
      tauto
    · rw [ite_eq_right hj]
      tauto
  rw [he]
  exact ((measurableSet_lt_windowCount n j).inter
    (measurableSet_le measurable_const (measurable_windowMeasure_Iic n s))).union
    ((measurableSet_lt_windowCount n j).compl.inter (MeasurableSet.const _))

end BlockBand.Critical.DecoratedSine
