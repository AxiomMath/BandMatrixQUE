module

public import BlockBand.Native.PSSS.BlockBand.Analysis.HermitianPoissonTrace
public import BlockBand.Native.PSSS.BlockBand.Analysis.PoissonLayerCake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Deterministic radial count identity for the PSSS Minami reduction

This module proves the exact finite-dimensional radial layer-cake identity used
in Proposition 3.1 (`formula`) of Peled–Schenker–Shamis–Sodin.  It is a
pointwise deterministic equality, prior to every random expectation or
factorial weight: the regulated trace of a Hermitian matrix is the radial
integral of its multiplicity count in the symmetric open interval.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal Topology Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem lintegral_poissonRadialWeight_Ioi_abs
    {η x : ℝ} (hη : 0 < η) :
    (∫⁻ r : ℝ in Ioi |x|, ENNReal.ofReal (poissonRadialWeight η r)) =
      ENNReal.ofReal (η / (x ^ 2 + η ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_poissonRadialWeight_Ioi hη (abs_nonneg x))]
  · rw [integral_poissonRadialWeight_Ioi_abs hη]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := (abs_nonneg x).trans_lt hr
    unfold poissonRadialWeight
    positivity

private theorem lintegral_radial_indicator
    {η x : ℝ} (hη : 0 < η) :
    (∫⁻ r : ℝ in Ioi 0,
      (Ioi |x|).indicator
        (fun r => ENNReal.ofReal (poissonRadialWeight η r)) r) =
      ENNReal.ofReal (η / (x ^ 2 + η ^ 2)) := by
  rw [setLIntegral_indicator measurableSet_Ioi]
  have hinter : Ioi |x| ∩ Ioi 0 = Ioi |x| := by
    ext r
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, (abs_nonneg x).trans_lt h⟩
  rw [hinter]
  exact lintegral_poissonRadialWeight_Ioi_abs hη

private theorem eigenCount_Ioo_eq_sum_indicators
    (A : HermitianMatrix ι) (r : ℝ) :
    (eigenCount A (Ioo (-r) r) : ℝ≥0∞) =
      ∑ i : Fin (Fintype.card ι),
        (Ioi |orderedEigenvalue A i|).indicator (fun _ => (1 : ℝ≥0∞)) r := by
  classical
  rw [eigenCount_def]
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [Finset.sum_filter, Set.mem_Ioo,
    Set.indicator_apply, Set.mem_Ioi, abs_lt]

/-- **Deterministic radial selected-count identity.**  For every finite
Hermitian matrix, the negative imaginary trace of its resolvent at `iη` is
exactly the `ℝ≥0∞` radial integral of the multiplicity count in `(-ξ,ξ)`
against the PSSS density `2ηξ/(ξ²+η²)²`.  The equality is pointwise and hence
may be multiplied by a nonnegative compression factorial weight before any
parameter integration. -/
theorem negImTrace_eq_lintegral_eigenCount_Ioo
    (A : HermitianMatrix ι) {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal
      (-(((((A : Matrix ι ι ℂ) +
        Complex.I • (η • (1 : Matrix ι ι ℂ)))⁻¹).trace).im)) =
      ∫⁻ r : ℝ in Ioi 0,
        (eigenCount A (Ioo (-r) r) : ℝ≥0∞) *
          ENNReal.ofReal (poissonRadialWeight η r) := by
  have htrace :
      -(((((A : Matrix ι ι ℂ) +
        Complex.I • (η • (1 : Matrix ι ι ℂ)))⁻¹).trace).im) =
        ∑ i : Fin (Fintype.card ι),
          η / ((orderedEigenvalue A i) ^ 2 + η ^ 2) := by
    simpa using
      (neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
        A 0 hη)
  rw [htrace]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · simp_rw [eigenCount_Ioo_eq_sum_indicators A]
    have hfun :
        (fun r : ℝ =>
          (∑ i : Fin (Fintype.card ι),
            (Ioi |orderedEigenvalue A i|).indicator
              (fun _ => (1 : ℝ≥0∞)) r) *
            ENNReal.ofReal (poissonRadialWeight η r)) =
        (fun r : ℝ =>
          ∑ i : Fin (Fintype.card ι),
            (Ioi |orderedEigenvalue A i|).indicator
              (fun r => ENNReal.ofReal (poissonRadialWeight η r)) r) := by
      funext r
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hri : |orderedEigenvalue A i| < r
      · have hmem : r ∈ Ioi |orderedEigenvalue A i| := hri
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul]
      · have hmem : r ∉ Ioi |orderedEigenvalue A i| := hri
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
          zero_mul]
    rw [hfun, MeasureTheory.lintegral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [← lintegral_radial_indicator (x := orderedEigenvalue A i) hη]
    · intro i hi
      apply Measurable.indicator
      · unfold poissonRadialWeight
        fun_prop
      · exact measurableSet_Ioi
  · intro i hi
    positivity

end PSSSNative.BlockBand
