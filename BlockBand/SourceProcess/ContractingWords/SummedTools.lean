module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Probability tools for the summed step

* `condExp_mul_left_complex`: pull-out of an `m`-measurable complex factor;
* `eLpNorm_mul_le_two`: `‖fg‖₁ ≤ ‖f‖₂‖g‖₂` (Cauchy–Schwarz);
* `eLpNorm_two_le_of_bound`, `integrable_of_bound`: a function dominated by `c·M^n` is
  integrable and `‖f‖₂ ≤ c (E M^{2n})^{1/2}`;
* `eLpNorm_cube_le`: `‖M^n|g|³‖₁ ≤ ‖M^n‖₂ ‖g‖₆³`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem condExp_mul_left_complex {m : MeasurableSpace Ω} {f g : Ω → ℂ}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun ω => f ω * g ω) μ)
    (hg : Integrable g μ) : μ[fun ω => f ω * g ω | m] =ᵐ[μ] fun ω => f ω * μ[g | m] ω :=
  condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf hfg hg

theorem holderTriple_two_two_one : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := by
  rw [ENNReal.holderTriple_iff, ENNReal.inv_two_add_inv_two, inv_one]

/-- Cauchy–Schwarz: `‖fg‖₁ ≤ ‖f‖₂‖g‖₂`. -/
theorem eLpNorm_mul_le_two {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => f ω * g ω) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have := holderTriple_two_two_one
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf hg
  exact h

theorem eLpNorm_two_pow (M : Ω → ℝ) (hM : ∀ ω, 0 ≤ M ω) (hMm : AEStronglyMeasurable M μ)
    (n : ℕ) :
    eLpNorm (fun ω => M ω ^ n) 2 μ =
      (∫⁻ ω, ENNReal.ofReal (M ω) ^ (2 * n) ∂μ) ^ (1 / 2 : ℝ) := by
  have hm : AEStronglyMeasurable (fun ω => M ω ^ n) μ := hMm.pow n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm]
  congr 1
  · refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (pow_nonneg (hM ω) n), ENNReal.ofReal_pow (hM ω),
      ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num [mul_comm]

/-- `|f| ≤ cM^n` a.e. gives `‖f‖₂ ≤ c (E M^{2n})^{1/2}`. -/
theorem eLpNorm_two_le_of_bound {f : Ω → ℂ} {M : Ω → ℝ} {c : ℝ} {n : ℕ}
    (hf : AEStronglyMeasurable f μ) (hM : ∀ ω, 0 ≤ M ω) (hMm : AEStronglyMeasurable M μ)
    (hc : 0 ≤ c) (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c * M ω ^ n) :
    eLpNorm f 2 μ ≤
      ENNReal.ofReal c * (∫⁻ ω, ENNReal.ofReal (M ω) ^ (2 * n) ∂μ) ^ (1 / 2 : ℝ) := by
  have h1 : eLpNorm f 2 μ ≤ eLpNorm (c • fun ω => M ω ^ n) 2 μ := by
    refine eLpNorm_mono_ae hf ?_
    filter_upwards [h] with ω hω
    rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (by have := hM ω; positivity)]
    exact hω
  refine h1.trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc, eLpNorm_two_pow M hM hMm]

/-- `|f| ≤ cM^n` a.e. with `E M^n < ∞` gives integrability. -/
theorem integrable_of_bound {f : Ω → ℂ} {M : Ω → ℝ} {c : ℝ} {n : ℕ}
    (hf : AEStronglyMeasurable f μ) (hM : ∀ ω, 0 ≤ M ω)
    (h : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ c * M ω ^ n)
    (hfin : ∫⁻ ω, ENNReal.ofReal (M ω) ^ n ∂μ ≠ ⊤) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  have h1 : ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ∫⁻ ω, ENNReal.ofReal c * ENNReal.ofReal (M ω) ^ n ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [h] with ω hω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (hM ω), ← ENNReal.ofReal_mul' (by
      have := hM ω; positivity)]
    exact ENNReal.ofReal_le_ofReal hω
  refine lt_of_le_of_lt h1 ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hfin)

/-- `‖M^n|g|³‖₁ ≤ ‖M^n‖₂‖g‖₆³`. -/
theorem eLpNorm_cube_le {g : Ω → ℂ} {M : Ω → ℝ} (n : ℕ) (hg : AEStronglyMeasurable g μ)
    (hMm : AEStronglyMeasurable M μ) :
    eLpNorm (fun ω => M ω ^ n * ‖g ω‖ ^ 3) 1 μ ≤
      eLpNorm (fun ω => M ω ^ n) 2 μ * eLpNorm g 6 μ ^ (3 : ℝ) := by
  have := holderTriple_two_two_one
  have hG : AEStronglyMeasurable (fun ω => ‖g ω‖ ^ (3 : ℝ)) μ :=
    (hg.aemeasurable.norm.pow_const (3 : ℝ)).aestronglyMeasurable
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (hMm.pow n) hG
  have e : (M ^ n • fun ω => ‖g ω‖ ^ (3 : ℝ)) = fun ω => M ω ^ n * ‖g ω‖ ^ 3 := by
    funext ω
    simp only [Pi.smul_apply', Pi.pow_apply, smul_eq_mul]
    norm_cast
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  rw [eLpNorm_norm_rpow g hg (by norm_num : (0 : ℝ) < 3)]
  congr 3
  rw [show ENNReal.ofReal 3 = 3 by norm_num]
  norm_num

/-- Linearity and pull-out for a finite sum `Σ_i c_i f_i` with `m`-measurable `c_i`. -/
theorem condExp_sum_mul {m : MeasurableSpace Ω} {ι : Type*} (s : Finset ι) (c f : ι → Ω → ℂ)
    (hc : ∀ i ∈ s, StronglyMeasurable[m] (c i))
    (hcf : ∀ i ∈ s, Integrable (fun ω => c i ω * f i ω) μ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    μ[fun ω => ∑ i ∈ s, c i ω * f i ω | m] =ᵐ[μ] fun ω => ∑ i ∈ s, c i ω * μ[f i | m] ω := by
  have e : (fun ω => ∑ i ∈ s, c i ω * f i ω) = ∑ i ∈ s, fun ω => c i ω * f i ω := by
    funext ω; simp [Finset.sum_apply]
  rw [e]
  refine (condExp_finsetSum hcf m).trans ?_
  have h : ∀ i ∈ s, μ[fun ω => c i ω * f i ω | m] =ᵐ[μ] fun ω => c i ω * μ[f i | m] ω :=
    fun i hi => condExp_mul_left_complex (hc i hi) (hcf i hi) (hf i hi)
  filter_upwards [(eventually_all_finset s).mpr h] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => hω i hi

/-- `‖Σ_i c_ie_i‖₁ ≤ Σ_i ‖c_i‖₂‖e_i‖₂`. -/
theorem eLpNorm_sum_mul_le {ι : Type*} (s : Finset ι) (c e : ι → Ω → ℂ)
    (hc : ∀ i ∈ s, AEStronglyMeasurable (c i) μ) (he : ∀ i ∈ s, AEStronglyMeasurable (e i) μ) :
    eLpNorm (fun ω => ∑ i ∈ s, c i ω * e i ω) 1 μ ≤
      ∑ i ∈ s, eLpNorm (c i) 2 μ * eLpNorm (e i) 2 μ := by
  have e1 : (fun ω => ∑ i ∈ s, c i ω * e i ω) = ∑ i ∈ s, fun ω => c i ω * e i ω := by
    funext ω; simp [Finset.sum_apply]
  rw [e1]
  exact (eLpNorm_sum_le le_rfl).trans
    (Finset.sum_le_sum fun i hi => eLpNorm_mul_le_two (hc i hi) (he i hi))

end BlockBand.SourceProcess.ContractingWords
