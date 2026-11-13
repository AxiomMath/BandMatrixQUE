module

public import BlockBand.SourceProcess.FullSource.SqBirth
public import BlockBand.SourceProcess.FullSource.TagBulk

/-!
# The tag-square moment, at one width and uniformly on a bulk interval

* `sq_moment_bound`: at one width,
  `E h_{k+1+m} ≤ (1+α/W)^m((1+Kd)B₁ + mDτ) + (B₂(C_N⁸)^m P)^{1/2}`, given the birth moments
  `B₁, B₂` of `h_{k+1}`, `E t_{k+1+i}² ≤ τ` (`i < m`) and `μ(G_{k+1+m}ᶜ) ≤ P`;
* `eLpNorm_two_tag`: `E t_j² ≤ C²` from `‖W⁻¹Tr Y_{j;k}‖₂ ≤ C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The tag-square moment at one width.** -/
theorem sq_moment_bound {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k : ℕ} (hW : 1 ≤ W)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lsq Ca ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lsq Ca * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (hd0 : 0 ≤ d)
    (m : ℕ) {B₁ B₂ τ P : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hτ0 : 0 ≤ τ) (hP0 : 0 ≤ P)
    (hb1 : ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ 1) ∂growthPathLaw W b ≤
      ENNReal.ofReal B₁)
    (hb2 : ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ 2) ∂growthPathLaw W b ≤
      ENNReal.ofReal B₂)
    (hτ : ∀ i, i < m →
      ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1 + i) k ω ^ 2) ∂growthPathLaw W b ≤
        ENNReal.ofReal τ)
    (hP : growthPathLaw W b (stopEv b E W k d (k + 1 + m))ᶜ ≤ ENNReal.ofReal P) :
    ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1 + m) k ω) ∂growthPathLaw W b ≤
      ENNReal.ofReal ((1 + alphaSq K Cm Ca Cf CN / W) ^ m *
          ((1 + K * d) * B₁ + m * (dsq K Cm C₂ ρ * τ)) +
        (B₂ * (CN ^ (2 * (2 * 2))) ^ m * P) ^ (1 / 2 : ℝ)) := by
  set μ := growthPathLaw W b
  set α := alphaSq K Cm Ca Cf CN
  set D := dsq K Cm C₂ ρ
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hα : 0 ≤ α := alphaSq_nonneg hK hCm hCa hCN
  have hD : 0 ≤ D := by simp only [D, dsq]; positivity
  have hKd : 0 ≤ 1 + K * d := add_nonneg zero_le_one (mul_nonneg hK hd0)
  have h1α : 0 ≤ 1 + α / W := add_nonneg zero_le_one (div_nonneg hα hW0.le)
  have hrem := sq_stop_removal (W := W) b E (k := k) hK d (k + 1 + m)
  have hiter := stopped_sq_iter hb0 hb hE1 hE2 (k := k) hW hL hCa hC₂ hCN hCf hCm hK
    hρ0 hρ1 hKL hd1 hρLd hdd₀ m hτ
  have hbirth : ∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (sqWeight b E W k K (k + 1)) ω ∂μ ≤
      ENNReal.ofReal ((1 + K * d) * B₁) := by
    calc ∫⁻ ω, (stopEv b E W k d (k + 1)).indicator (sqWeight b E W k K (k + 1)) ω ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (1 + K * d) *
            ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ 1) ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases h : ω ∈ stopEv b E W k d (k + 1)
          · rw [Set.indicator_of_mem h, sqWeight, ← ENNReal.ofReal_mul hKd, pow_one]
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
              (tagSq_nonneg b E _ k ω))
            have := h (k + 1) le_rfl le_rfl
            nlinarith
          · rw [Set.indicator_of_notMem h]; exact zero_le
      _ = ENNReal.ofReal (1 + K * d) * ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1) k ω ^ 1) ∂μ :=
          lintegral_const_mul _ ((measurable_tagSq b E _ k).pow_const 1).ennreal_ofReal
      _ ≤ ENNReal.ofReal (1 + K * d) * ENNReal.ofReal B₁ := mul_le_mul_of_nonneg_left hb1 zero_le
      _ = ENNReal.ofReal ((1 + K * d) * B₁) := (ENNReal.ofReal_mul hKd).symm
  have hcrude := crude_sq_iter hb0 hb hE1 hE2 (k := k) hW hCN hL.N m
  have h2 : ∫⁻ ω, ENNReal.ofReal (tagSq b E W (k + 1 + m) k ω ^ 2) ∂μ ≤
      ENNReal.ofReal (B₂ * (CN ^ (2 * (2 * 2))) ^ m) := by
    refine hcrude.trans ((mul_le_mul_of_nonneg_left hb2 zero_le).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_mul hB₂, ENNReal.ofReal_pow (pow_nonneg hCN _), mul_comm]
  refine hrem.trans ?_
  have hX0 : 0 ≤ (1 + K * d) * B₁ + m * (D * τ) := by positivity
  rw [ENNReal.ofReal_add (mul_nonneg (pow_nonneg h1α m) hX0)
    (Real.rpow_nonneg (mul_nonneg (mul_nonneg hB₂ (pow_nonneg (pow_nonneg hCN _) m)) hP0) _)]
  refine add_le_add (hiter.trans ?_) ?_
  · rw [ENNReal.ofReal_mul (pow_nonneg h1α m), ENNReal.ofReal_pow h1α]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [ENNReal.ofReal_add (mul_nonneg hKd hB₁) (by positivity)]
    refine add_le_add hbirth (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_mul hD]
  · have hP' : μ (stopEv b E W k d (k + 1 + m))ᶜ ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal P ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hP (by norm_num)
    have h2' := ENNReal.rpow_le_rpow h2 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    refine (mul_le_mul h2' hP' zero_le zero_le).trans (le_of_eq ?_)
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.ofReal_mul (mul_nonneg hB₂ (pow_nonneg (pow_nonneg hCN _) m)),
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (mul_nonneg hB₂ (pow_nonneg (pow_nonneg hCN _) m))
        hP0) (by norm_num)]

/-- `E t_j² ≤ C²` from `‖W⁻¹Tr Y_{j;k}‖₂ ≤ C`. -/
theorem eLpNorm_two_tag (b E : ℝ) (j k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal 2)
      (growthPathLaw W b) ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ 2) ∂growthPathLaw W b ≤ ENNReal.ofReal (C ^ 2) := by
  have hm := measurable_tagMass (W := W) b E j k
  have he : eLpNorm (tagMass b E W j k) (ENNReal.ofReal 2) (growthPathLaw W b) ≤
      ENNReal.ofReal C :=
    (eLpNorm_mono hm.aestronglyMeasurable fun ω => le_of_eq (by
      rw [norm_tag_eq, Real.norm_eq_abs, abs_of_nonneg (tagMass_nonneg b E j k ω)])).trans h
  obtain ⟨hi, hb⟩ := integral_abs_pow_le (ν := growthPathLaw W b) (f := tagMass b E W j k)
    (n := 2) (by norm_num) hC ⟨hm.aestronglyMeasurable, by exact_mod_cast he⟩
  have e : (fun ω => |tagMass b E W j k ω| ^ 2) = fun ω => tagMass b E W j k ω ^ 2 := by
    funext ω; exact sq_abs _
  rw [e] at hi hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hb

end BlockBand.SourceProcess.FullSource
