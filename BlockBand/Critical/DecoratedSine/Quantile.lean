module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Interval

/-!
# Finite counting measures on `ℝ` are sums of Dirac masses at their quantiles

For a finite measure `μ` on `ℝ` whose distribution function `t ↦ μ(-∞, t]` is `ℕ`-valued, the
quantiles `atomQuantile μ j` (the least `t` with `μ(-∞, t] ≥ j + 1`) enumerate its atoms from the
left, and `μ = Σ_{j < μ(ℝ)} δ_{atomQuantile μ j}` (`eq_sum_dirac_atomQuantile`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.DecoratedSine

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-- The `j`-th atom from the left (`j = 0, 1, …`) of a finite counting measure `μ` on `ℝ`:
the least `t` with `μ(-∞, t] ≥ j + 1`. -/
def atomQuantile (μ : Measure ℝ) (j : ℕ) : ℝ :=
  sInf {t : ℝ | (j : ℝ≥0∞) + 1 ≤ μ (Iic t)}

/-- The distribution function `t ↦ μ(-∞, t]` takes values in `ℕ`. -/
def HasNatCDF (μ : Measure ℝ) : Prop :=
  ∀ t : ℝ, ∃ k : ℕ, μ (Iic t) = k

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
theorem exists_le_measure_Iic {N : ℕ} (hN : μ univ = N) (hint : HasNatCDF μ) {j : ℕ}
    (hj : j < N) : ∃ t : ℝ, (j : ℝ≥0∞) + 1 ≤ μ (Iic t) := by
  have h := tendsto_measure_Iic_atTop μ
  rw [hN] at h
  have hlt : (j : ℝ≥0∞) < N := by exact_mod_cast hj
  obtain ⟨t, ht⟩ := (h.eventually (lt_mem_nhds hlt)).exists
  obtain ⟨k, hk⟩ := hint t
  refine ⟨t, ?_⟩
  rw [hk] at ht ⊢
  have hjk : j < k := by exact_mod_cast ht
  exact_mod_cast (show j + 1 ≤ k by omega)

theorem bddBelow_quantileSet (j : ℕ) :
    BddBelow {t : ℝ | (j : ℝ≥0∞) + 1 ≤ μ (Iic t)} := by
  have hanti : Antitone fun k : ℕ => Iic (-(k : ℝ)) := by
    intro a b hab
    exact Iic_subset_Iic.mpr (by simpa using (Nat.cast_le.mpr hab : (a : ℝ) ≤ b))
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun k : ℕ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have he : (⋂ k : ℕ, Iic (-(k : ℝ))) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨k, hk⟩ := exists_nat_gt (-x)
    exact ⟨k, by linarith⟩
  rw [he, measure_empty] at h
  obtain ⟨k, hk⟩ := (h.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from one_pos))).exists
  refine ⟨-(k : ℝ), fun t ht => ?_⟩
  by_contra hlt'
  have hlt : t < -(k : ℝ) := not_le.mp hlt'
  have hmono : μ (Iic t) ≤ μ (Iic (-(k : ℝ))) := measure_mono (Iic_subset_Iic.mpr hlt.le)
  have h1 : (1 : ℝ≥0∞) ≤ (j : ℝ≥0∞) + 1 := le_add_self
  have : (1 : ℝ≥0∞) < 1 := lt_of_le_of_lt (h1.trans (ht.trans hmono)) hk
  exact lt_irrefl _ this

/-- Right continuity of the distribution function, in the form used for the quantile. -/
theorem le_measure_Iic_sInf {j : ℕ} (hne : ∃ t : ℝ, (j : ℝ≥0∞) + 1 ≤ μ (Iic t)) :
    (j : ℝ≥0∞) + 1 ≤ μ (Iic (atomQuantile μ j)) := by
  set S := {t : ℝ | (j : ℝ≥0∞) + 1 ≤ μ (Iic t)}
  set q := atomQuantile μ j
  have hS : S.Nonempty := hne
  have hbdd : BddBelow S := bddBelow_quantileSet j
  have hanti : Antitone fun k : ℕ => Iic (q + 1 / ((k : ℝ) + 1)) := by
    intro a b hab
    refine Iic_subset_Iic.mpr ?_
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).mpr hab
      linarith
    have := one_div_le_one_div_of_le ha hab'
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ)
    (fun k : ℕ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have he : (⋂ k : ℕ, Iic (q + 1 / ((k : ℝ) + 1))) = Iic q := by
    ext x
    simp only [mem_iInter, mem_Iic]
    refine ⟨fun hx => ?_, fun hx k => ?_⟩
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      exact lt_of_le_of_lt (hx k) (by linarith)
    · have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [he] at h
  refine ge_of_tendsto h (Eventually.of_forall fun k => ?_)
  have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hS (show sInf S < q + 1 / ((k : ℝ) + 1) by
    change q < _
    linarith)
  exact htS.trans (measure_mono (Iic_subset_Iic.mpr htlt.le))

/-- Characterisation of the quantile: for `j < μ(ℝ)`, `q_j ≤ t ↔ μ(-∞, t] ≥ j + 1`. -/
theorem atomQuantile_le_iff {N : ℕ} (hN : μ univ = N) (hint : HasNatCDF μ) {j : ℕ}
    (hj : j < N) (t : ℝ) :
    atomQuantile μ j ≤ t ↔ (j : ℝ≥0∞) + 1 ≤ μ (Iic t) := by
  constructor
  · intro h
    exact (le_measure_Iic_sInf (exists_le_measure_Iic hN hint hj)).trans
      (measure_mono (Iic_subset_Iic.mpr h))
  · intro h
    exact csInf_le (bddBelow_quantileSet j) h

/-- **A finite measure on `ℝ` with an `ℕ`-valued distribution function is the sum of the Dirac
masses at its quantiles.** -/
theorem eq_sum_dirac_atomQuantile {N : ℕ} (hN : μ univ = N) (hint : HasNatCDF μ) :
    μ = ∑ j ∈ Finset.range N, Measure.dirac (atomQuantile μ j) := by
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.dirac_apply' _ measurableSet_Iic, indicator_apply, mem_Iic, Pi.one_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  obtain ⟨k, hk⟩ := hint t
  have hkN : k ≤ N := by
    have := measure_mono (μ := μ) (subset_univ (Iic t))
    rw [hk, hN] at this
    exact_mod_cast this
  have hfil : (Finset.range N).filter (fun j => atomQuantile μ j ≤ t) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hq⟩
      rw [atomQuantile_le_iff hN hint hj, hk] at hq
      have : j + 1 ≤ k := by exact_mod_cast hq
      omega
    · intro hj
      refine ⟨by omega, ?_⟩
      rw [atomQuantile_le_iff hN hint (by omega), hk]
      exact_mod_cast (show j + 1 ≤ k by omega)
  rw [hfil, Finset.card_range, hk]

end BlockBand.Critical.DecoratedSine
