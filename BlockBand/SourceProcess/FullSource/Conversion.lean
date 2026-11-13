module

public import BlockBand.SourceProcess.FullSource.TagBound

/-!
# From lintegral moments of the tag mass to the contract's `L^p` norms; the exit event

* `norm_tag_eq`: `‖W⁻¹ Tr Y_{j;k}‖ = t_j` (the trace is real and `≥ 0`);
* `eLpNorm_tag_le`: `‖W⁻¹Tr Y_{j;k}‖_p ≤ X^{1/n}` from `E t_j^n ≤ X`, `1 ≤ p ≤ n`;
* `stopEv_compl_subset`: `G_jᶜ ⊆ {∃ r ≤ TW, δ_r > d}` for `j ≤ TW` (the SUPX event).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem norm_tag_eq (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) :
    ‖(W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace‖ = tagMass b E W j k ω := by
  rw [tagResponse_eq_factor, trace_factor_eq_re, tagMass_eq_past, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) (trace_factor_re_nonneg _))]

/-- **From a lintegral moment to the `L^p` norm of the tag.** -/
theorem eLpNorm_tag_le (b E : ℝ) (j k : ℕ) {p : ℝ} {n : ℕ} (hp : 1 ≤ p) (hpn : p ≤ n)
    {X : ℝ} (hX : 0 ≤ X)
    (h : ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ n) ∂growthPathLaw W b ≤ ENNReal.ofReal X) :
    eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal (X ^ (1 / (n : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by linarith
  refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpn)).trans ?_
  have hmeas : AEStronglyMeasurable (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace)
      (growthPathLaw W b) := by
    have : (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) = fun ω =>
        (W : ℂ)⁻¹ * ((pastS b E W j k (pastCoords W j ω))ᴴ *
          pastS b E W j k (pastCoords W j ω)).trace := by
      funext ω; rw [tagResponse_eq_factor]
    rw [this]
    have hS := (measurable_pastS (W := W) b E j k).comp (measurable_pastCoords W j)
    have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
    refine (measurable_const.mul ?_).aestronglyMeasurable
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.measurable_sum _ fun i _ => hT.eval_matrix
  have hn0' : ENNReal.ofReal n ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hn0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn0' ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hn0.le, ← ENNReal.ofReal_rpow_of_nonneg hX (by positivity)]
  refine ENNReal.rpow_le_rpow (le_of_eq_of_le (lintegral_congr fun ω => ?_) h) (by positivity)
  rw [← ofReal_norm, norm_tag_eq, ENNReal.ofReal_rpow_of_nonneg (tagMass_nonneg b E j k ω)
    hn0.le, Real.rpow_natCast]

/-- The complement of the stopping event lies in the SUPX exit event. -/
theorem stopEv_compl_subset (b E : ℝ) (k : ℕ) (d T : ℝ) {j : ℕ} (hj : (j : ℝ) ≤ T * W) :
    (stopEv b E W k d j)ᶜ ⊆ {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
      d < jetDistance0 b E (pathX b E W r ω)} := by
  intro ω hω
  simp only [stopEv, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨i, hi1, hij, hd⟩ := hω
  refine ⟨i, by omega, ?_, hd⟩
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

end BlockBand.SourceProcess.FullSource
