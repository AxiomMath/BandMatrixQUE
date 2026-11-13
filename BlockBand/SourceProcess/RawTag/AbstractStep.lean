module

public import BlockBand.SourceProcess.RawTag.FreshStep
public import BlockBand.SourceProcess.FullSource.DeltaReduction

/-!
# One conditional step of the raw-moment recursion on an abstract product

`abstract_step`: on a product `P × F` of a past and a fresh probability space, the `4m`-th moment
of one step `x + a*D c` is at most `(1 + K/W_r)` times the `4m`-th power of the mean step
`x + a*(E D)c` plus `K W_r^{2m-1}` times the `L^{4m}` bound on the centred fluctuation
`a*(D - E D)c`. `lintegral_pow_le_of_eLpNorm` converts an `L^{4m}` bound into a lower-integral
bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal

theorem bilinear_sub_mid {n : Type*} [Fintype n] (u : n → ℂ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (A - B) v = bilinear u A v - bilinear u B v := by
  simp [bilinear, sub_mulVec, dotProduct_sub]

/-- `∫⁻ ‖d‖ₑ^{4m} ≤ s^{4m}` from an `L^{4m}` bound `s`. -/
theorem lintegral_pow_le_of_eLpNorm {F : Type*} [MeasurableSpace F] {μ : Measure F}
    {d : F → ℂ} (hd : AEStronglyMeasurable d μ) {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : eLpNorm d (ENNReal.ofReal (4 * m)) μ ≤ ENNReal.ofReal s) :
    ∫⁻ f, ENNReal.ofReal ((‖d f‖ ^ 2) ^ (2 * m)) ∂μ ≤ ENNReal.ofReal (s ^ (4 * m)) := by
  have h4 : (0 : ℝ) < 4 * m := by have : (1 : ℝ) ≤ m := by exact_mod_cast hm
                                  linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h4) ENNReal.ofReal_ne_top hd,
    ENNReal.toReal_ofReal h4.le] at hs
  have hs' := ENNReal.rpow_le_rpow hs h4.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel h4.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hs0 h4.le] at hs'
  have e : ∀ f, ENNReal.ofReal ((‖d f‖ ^ 2) ^ (2 * m)) = ‖d f‖ₑ ^ (4 * (m : ℝ)) := by
    intro f
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) h4.le, ← pow_mul,
      show 2 * (2 * m) = 4 * m by ring, ← Real.rpow_natCast]
    push_cast; rfl
  simp_rw [e]
  refine hs'.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast]; push_cast; rfl

/-- **The abstract conditional step.** -/
theorem abstract_step {P F : Type*} [MeasurableSpace P] [MeasurableSpace F] (μP : Measure P)
    [SFinite μP] (μF : Measure F) [IsProbabilityMeasure μF] {W : ℕ}
    (x : P → ℂ) (a c : P → Fin W → ℂ) (D : P → F → Matrix (Fin W) (Fin W) ℂ) {m : ℕ}
    (hm : 1 ≤ m) {Wr : ℝ} (hW : 1 ≤ Wr)
    (hΦ : AEMeasurable (fun z : P × F => ENNReal.ofReal
      ((‖x z.1 + bilinear (a z.1) (D z.1 z.2) (c z.1)‖ ^ 2) ^ (2 * m))) (μP.prod μF))
    (hI : ∀ᵐ p ∂μP, ∀ i j, Integrable (fun f => D p f i j) μF)
    (s : P → ℝ) (hs0 : ∀ p, 0 ≤ s p)
    (hs : ∀ᵐ p ∂μP, eLpNorm (fun f => bilinear (a p) (D p f - matrixExpect μF (D p)) (c p))
      (ENNReal.ofReal (4 * m)) μF ≤ ENNReal.ofReal (s p)) :
    ∫⁻ z, ENNReal.ofReal ((‖x z.1 + bilinear (a z.1) (D z.1 z.2) (c z.1)‖ ^ 2) ^ (2 * m))
        ∂(μP.prod μF) ≤
      ∫⁻ p, (ENNReal.ofReal ((1 + stepK (2 * m) / Wr) *
          (‖x p + bilinear (a p) (matrixExpect μF (D p)) (c p)‖ ^ 2) ^ (2 * m)) +
        ENNReal.ofReal (stepK (2 * m) * Wr ^ (2 * m - 1)) * ENNReal.ofReal (s p ^ (4 * m)))
          ∂μP := by
  rw [lintegral_prod _ hΦ]
  refine lintegral_mono_ae ?_
  filter_upwards [hI, hs] with p hIp hsp
  set M := matrixExpect μF (D p)
  set u := x p + bilinear (a p) M (c p)
  set d : F → ℂ := fun f => bilinear (a p) (D p f - M) (c p)
  have hdecomp : ∀ f, x p + bilinear (a p) (D p f) (c p) = u + d f := by
    intro f; simp only [u, d, bilinear_sub_mid]; ring
  have hDM : ∀ i j, Integrable (fun f => (D p f - M) i j) μF := fun i j =>
    (hIp i j).sub (integrable_const _)
  have hdi : Integrable d μF := integrable_bilinear (fun f => D p f - M) hDM (a p) (c p)
  have hd0 : ∫ f, d f ∂μF = 0 := by
    have e : ∀ f, d f = bilinear (a p) (D p f) (c p) - bilinear (a p) M (c p) := fun f =>
      bilinear_sub_mid _ _ _ _
    simp_rw [e]
    rw [integral_sub (integrable_bilinear (D p) hIp (a p) (c p)) (integrable_const _),
      integral_bilinear (D p) hIp, integral_const, probReal_univ, one_smul, sub_self]
  simp_rw [hdecomp]
  refine (lintegral_fresh_step u hdi hd0 hm hW).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_right ?_ _
  exact lintegral_pow_le_of_eLpNorm hdi.aestronglyMeasurable hm (hs0 p) hsp

end BlockBand.SourceProcess.RawTag
