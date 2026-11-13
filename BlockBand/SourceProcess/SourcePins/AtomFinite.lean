module

public import BlockBand.SourceProcess.SourcePins.AtomSet
public import BlockBand.Transmission.LawDuality.PowerBridge

/-!
# Finite trace measures lie in `atomSet` (`EntranceAtomic`, finite `W`)

* `padEig`: the eigenvalues of `T` in decreasing order (`eigenvalues₀`, Mathlib), padded by `0`.
* `traceMeasure_mem_atomSet`: if `Tr T^p ≤ R` (`fracTrace`), then `traceMeasure T ∈ atomSet p R`.
* `lintegral_psiP_traceMeasure`: `∫⁻ ψ_p d(traceMeasure T) = Tr T^p`, where
  `ψ_p(y) = y^{p-1} 1_{y>0}`; this makes `Tr T^p` a measurable function of the trace measure.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal BoundedContinuousFunction ComplexOrder

/-- `ψ_p(y) = y^{p-1}` on `(0,1]`, `0` at `0`. -/
def psiP (p : ℝ) (y : unitInterval) : ℝ≥0∞ :=
  if 0 < (y : ℝ) then ENNReal.ofReal ((y : ℝ) ^ (p - 1)) else 0

theorem measurable_psiP (p : ℝ) : Measurable (psiP p) :=
  Measurable.ite measurableSet_ppos (measurable_subtype_coe.pow_const (p - 1)).ennreal_ofReal
    measurable_const

theorem sum_range_eq_of_vanish {g : ℕ → ℝ} {M N : ℕ} (hN : ∀ i, N ≤ i → g i = 0)
    (hM : ∀ i, M ≤ i → g i = 0) :
    ∑ i ∈ Finset.range M, g i = ∑ i ∈ Finset.range N, g i := by
  rcases le_total M N with h | h
  · rw [← Finset.sum_range_add_sum_Ico g h, Finset.sum_eq_zero fun i hi => hM i
      (Finset.mem_Ico.1 hi).1, add_zero]
  · rw [← Finset.sum_range_add_sum_Ico g h, Finset.sum_eq_zero fun i hi => hN i
      (Finset.mem_Ico.1 hi).1, add_zero]

variable {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}

/-- The decreasing eigenvalues of `T`, padded by `0`. -/
def padEig (hT : T.IsHermitian) (i : ℕ) : ℝ :=
  if h : i < Fintype.card n then hT.eigenvalues₀ ⟨i, h⟩ else 0

theorem sum_eig_eq (hT : T.IsHermitian) (g : ℝ → ℝ) :
    ∑ i, g (hT.eigenvalues i) = ∑ i ∈ Finset.range (Fintype.card n), g (padEig hT i) := by
  have e1 : ∑ i, g (hT.eigenvalues i) = ∑ j, g (hT.eigenvalues₀ j) :=
    Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun j => g (hT.eigenvalues₀ j))
  rw [e1, ← Fin.sum_univ_eq_sum_range (fun i => g (padEig hT i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [padEig, j.2]

theorem padEig_mem (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) (i : ℕ) :
    0 ≤ padEig h0.1 i ∧ padEig h0.1 i ≤ 1 := by
  unfold padEig
  split_ifs with h
  · have := Transmission.LawDuality.eigenvalues_mem h0 h1
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨i, h⟩)
    simpa [Matrix.IsHermitian.eigenvalues] using this
  · exact ⟨le_rfl, zero_le_one⟩

theorem antitone_padEig (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) :
    Antitone (padEig h0.1) := by
  intro i j hij
  by_cases hj : j < Fintype.card n
  · have hi : i < Fintype.card n := lt_of_le_of_lt hij hj
    simp only [padEig, hi, hj, dite_true]
    exact h0.1.eigenvalues₀_antitone (Fin.mk_le_mk.2 hij)
  · simp only [padEig, hj, dite_false]
    exact (padEig_mem h0 h1 i).1

theorem padEig_eq_zero (hT : T.IsHermitian) {i : ℕ} (hi : Fintype.card n ≤ i) :
    padEig hT i = 0 := by
  simp [padEig, not_lt.2 hi]

theorem fracTrace_eq_sum (hT : T.IsHermitian) (p : ℝ) :
    fracTrace p T = ∑ i, (max (hT.eigenvalues i) 0) ^ p := by
  rw [fracTrace, hT.roots_charpoly_eq_eigenvalues, Multiset.map_map, Finset.sum_eq_multiset_sum]
  simp [Function.comp_def]

theorem fracTrace_eq_sum_pad (h0 : T.PosSemidef) (p : ℝ) :
    fracTrace p T = ∑ i ∈ Finset.range (Fintype.card n), padEig h0.1 i ^ p := by
  rw [fracTrace_eq_sum h0.1, ← sum_eig_eq h0.1 (fun x => x ^ p)]
  exact Finset.sum_congr rfl fun i _ => by rw [max_eq_left (h0.eigenvalues_nonneg i)]

theorem pBound_padEig {p R : ℝ} (hp : 0 < p) (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef)
    (hR : fracTrace p T ≤ R) : PBound p R (padEig h0.1) := by
  refine ⟨antitone_padEig h0 h1, padEig_mem h0 h1, fun m => ?_⟩
  have hz : ∀ i, Fintype.card n ≤ i → padEig h0.1 i ^ p = 0 := fun i hi => by
    rw [padEig_eq_zero h0.1 hi, Real.zero_rpow hp.ne']
  calc ∑ i ∈ Finset.range m, padEig h0.1 i ^ p
      ≤ ∑ i ∈ Finset.range (m + Fintype.card n), padEig h0.1 i ^ p :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_add_right _ _))
          fun i _ _ => Real.rpow_nonneg (padEig_mem h0 h1 i).1 p
    _ = fracTrace p T := by
        rw [fracTrace_eq_sum_pad h0, sum_range_eq_of_vanish hz
          fun i hi => hz i ((Nat.le_add_left _ _).trans hi)]
    _ ≤ R := hR

/-- **Finite trace measures lie in `atomSet`.** -/
theorem traceMeasure_mem_atomSet {p R : ℝ} (hp : 0 < p) (h0 : T.PosSemidef)
    (h1 : (1 - T).PosSemidef) (hR : fracTrace p T ≤ R) : traceMeasure T ∈ atomSet p R := by
  have hB := pBound_padEig hp h0 h1 hR
  refine ⟨padEig h0.1, hB, fun x hx f hf => ?_⟩
  rw [Transmission.LawDuality.integral_traceMeasure h0.1 f.continuous]
  have e : ∀ i, (Real.toNNReal (h0.1.eigenvalues i) : ℝ) * f (toUnit (h0.1.eigenvalues i)) =
      (fun y => y * f (toUnit y)) (h0.1.eigenvalues i) := fun i => by
    simp only [Real.coe_toNNReal _ (h0.eigenvalues_nonneg i)]
  rw [Finset.sum_congr rfl fun i _ => e i, sum_eig_eq h0.1 (fun y => y * f (toUnit y))]
  refine sum_range_eq_of_vanish (fun i hi => ?_) fun i hi => ?_
  · have hle := le_of_cutIdx_le hp hx hB hi
    rw [hf _ (by rw [coe_toUnit_of_mem (padEig_mem h0 h1 i).1 (padEig_mem h0 h1 i).2]; exact hle),
      mul_zero]
  · rw [padEig_eq_zero h0.1 hi, zero_mul]

theorem mul_psiP_toUnit {p y : ℝ} (hp : 0 < p) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    (Real.toNNReal y : ℝ≥0∞) * psiP p (toUnit y) = ENNReal.ofReal (y ^ p) := by
  rcases h0.eq_or_lt with rfl | hy
  · simp [Real.zero_rpow hp.ne']
  · rw [psiP, coe_toUnit_of_mem h0 h1, ite_eq_left hy, ← ENNReal.ofReal.eq_def,
      ← ENNReal.ofReal_mul h0, Real.rpow_sub_one hy.ne', mul_div_cancel₀ _ hy.ne']

/-- **`Tr T^p` from the trace measure.** -/
theorem lintegral_psiP_traceMeasure {p : ℝ} (hp : 0 < p) (h0 : T.PosSemidef)
    (h1 : (1 - T).PosSemidef) :
    ∫⁻ y, psiP p y ∂(traceMeasure T : Measure unitInterval) = ENNReal.ofReal (fracTrace p T) := by
  rw [Transmission.LawDuality.traceMeasure_eq_sum h0.1, FiniteMeasure.toMeasure_sum,
    lintegral_finsetSum_measure, fracTrace_eq_sum h0.1,
    ENNReal.ofReal_sum_of_nonneg fun i _ => Real.rpow_nonneg (le_max_right _ _) p]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := Transmission.LawDuality.eigenvalues_mem h0 h1 i
  rw [FiniteMeasure.toMeasure_smul, lintegral_smul_measure, max_eq_left hm.1]
  simp only [unitDirac, FiniteMeasure.toMeasure_mk]
  rw [lintegral_dirac, ENNReal.smul_def, smul_eq_mul, mul_psiP_toUnit hp hm.1 hm.2]

end BlockBand.SourceProcess.SourcePins
