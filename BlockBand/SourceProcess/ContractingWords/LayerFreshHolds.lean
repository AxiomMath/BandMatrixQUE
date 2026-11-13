module

public import BlockBand.SourceProcess.ContractingWords.SepAll
public import BlockBand.SourceProcess.FullSource.NearPassive
public import BlockBand.SourceProcess.FullSourceCovariance.Assembly
public import BlockBand.Transmission.SourceMixing.MatchedScalars

/-!
# Auxiliary bounds for the one-layer word step

Moment bounds for `G = 1 + ‖N‖ + ‖D‖`, a bound on the gap factor and the arithmetic of the mean and
centered one-layer bounds, used in `layerFreshBound_of`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

/-- `‖(1 + ‖N‖ + ‖D‖)^k‖_r ≤ (1 + 2C)^k` from `‖‖N‖‖_{kr}, ‖‖D‖‖_{kr} ≤ C`. -/
theorem eLpNorm_G_pow_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {f g : Ω → ℝ} (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y) {k : ℕ} (hk : 1 ≤ k) {r C : ℝ} (hr : 1 ≤ r)
    (hC : 0 ≤ C) (hfC : eLpNorm f (ENNReal.ofReal (k * r)) ν ≤ ENNReal.ofReal C)
    (hgC : eLpNorm g (ENNReal.ofReal (k * r)) ν ≤ ENNReal.ofReal C) :
    eLpNorm (fun y => (1 + f y + g y) ^ k) (ENNReal.ofReal r) ν ≤
      ENNReal.ofReal ((1 + 2 * C) ^ k) := by
  have hG : AEStronglyMeasurable (fun y => 1 + f y + g y) ν :=
    (aestronglyMeasurable_const.add hf).add hg
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have e : (fun y => (1 + f y + g y) ^ k) = fun y => ‖1 + f y + g y‖ ^ (k : ℝ) := by
    funext y; rw [Real.norm_of_nonneg (by linarith [hf0 y, hg0 y]), Real.rpow_natCast]
  rw [e, eLpNorm_norm_rpow _ hG hk0]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r * ENNReal.ofReal k := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.one_le_ofReal.mpr (by nlinarith [(by exact_mod_cast hk : (1 : ℝ) ≤ k)])
  have hmul : ENNReal.ofReal r * ENNReal.ofReal k = ENNReal.ofReal (k * r) := by
    rw [← ENNReal.ofReal_mul (by linarith), mul_comm]
  have h1 : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (k * r)) ν ≤ ENNReal.ofReal 1 := by
    refine (eLpNorm_le_of_ae_bound aestronglyMeasurable_const (C := 1)
      (Eventually.of_forall fun _ => by simp)).trans ?_
    simp
  have hsum : eLpNorm (fun y => 1 + f y + g y) (ENNReal.ofReal (k * r)) ν ≤
      ENNReal.ofReal (1 + 2 * C) := by
    have e2 : (fun y => 1 + f y + g y) = ((fun _ : Ω => (1 : ℝ)) + f) + g := by
      funext y; simp
    rw [e2]
    have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (k * r) := by rw [← hmul]; exact hp1
    refine (eLpNorm_add_le hq).trans ((add_le_add ((eLpNorm_add_le hq).trans
      (add_le_add h1 hfC)) hgC).trans ?_)
    rw [← ENNReal.ofReal_add (by norm_num) hC, ← ENNReal.ofReal_add (by positivity) hC]
    exact le_of_eq (by congr 1; ring)
  rw [hmul]
  calc eLpNorm (fun y => 1 + f y + g y) (ENNReal.ofReal (k * r)) ν ^ (k : ℝ) ≤
        ENNReal.ofReal (1 + 2 * C) ^ (k : ℝ) := ENNReal.rpow_le_rpow hsum hk0.le
    _ = _ := by rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hk0.le, Real.rpow_natCast]

theorem norm_gapFactor_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {s : ℂ} (hs : IsStationaryJet b E s) (σ : Separator) : ‖gapFactor b E s σ‖ ≤ 1 := by
  have hθ := (BlockBand.Transmission.SourceMixing.norm_thetaStar_le hb0 hb h1 h2 hs).1
  rw [gapFactor, norm_mul, norm_pow, norm_pow, Complex.norm_conj]
  have ha := pow_le_one₀ (n := σ.unconj) (norm_nonneg _) hθ
  have hb' := pow_le_one₀ (n := σ.conj) (norm_nonneg _) hθ
  have hb0' : 0 ≤ ‖thetaStar b E s‖ ^ σ.conj := by positivity
  nlinarith

theorem sqrt_bounds {W : ℝ} (hW1 : 1 ≤ W) :
    0 < Real.sqrt W ∧ 1 / Real.sqrt W ≤ 1 ∧ W⁻¹ ≤ 1 / Real.sqrt W ∧
      (1 / Real.sqrt W) ^ 2 = W⁻¹ := by
  have hW0 : 0 < W := by linarith
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  refine ⟨hsW, by rw [div_le_one hsW]; exact Real.one_le_sqrt.mpr hW1, ?_, ?_⟩
  · rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hsW (by rw [Real.sqrt_le_left hW0.le]; nlinarith)
  · rw [div_pow, Real.sq_sqrt hW0.le, one_pow, one_div]

/-- The arithmetic of the mean bound. -/
theorem arith_mean {Γ Kd Cf Ce μ e Ci W δ0 δ1 g m : ℝ} (dn : ℕ) (hΓ : 0 ≤ Γ) (hKd : 0 ≤ Kd)
    (hCf : 0 ≤ Cf) (hCe : 0 ≤ Ce) (hCi : 0 ≤ Ci) (hW1 : 1 ≤ W) (hδ0 : 0 ≤ δ0)
    (hδ1 : 0 ≤ δ1) (hg : 0 ≤ g) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hmδ : m ≤ δ0) (he0 : 0 ≤ e)
    (he1 : e ≤ Ce * (δ0 + δ1 + g / W + W⁻¹ ^ 2)) (he2 : e ≤ μ + 1) :
    Γ * (Kd * ((dn : ℝ) * (Cf * (1 / Real.sqrt W + m))) ^ 2 *
        (1 + ((dn : ℝ) * (Cf * (1 / Real.sqrt W + m))) ^ dn) + dn * e * (1 + 1 + e) ^ dn) +
      Ci / W ≤
    (Γ * (Kd * ((dn : ℝ) ^ 2 * (2 * Cf ^ 2)) * (1 + (2 * dn * Cf) ^ dn) +
        dn * Ce * (3 + μ) ^ dn) + Ci) * (δ0 + δ1 + g / W + W⁻¹) := by
  obtain ⟨hsW, hsW1, hWsW, hsq⟩ := sqrt_bounds hW1
  have hW0 : 0 < W := by linarith
  set E1 := δ0 + δ1 + g / W + W⁻¹
  have hgW : 0 ≤ g / W := div_nonneg hg hW0.le
  have hWi : 0 ≤ W⁻¹ := inv_nonneg.mpr hW0.le
  have hE1 : 0 ≤ E1 := by positivity
  have hD := (Nat.cast_nonneg dn : (0 : ℝ) ≤ dn)
  set β := Cf * (1 / Real.sqrt W + m)
  have hβ0 : 0 ≤ β := mul_nonneg hCf (add_nonneg (by positivity) hm0)
  have hβ : (dn : ℝ) * β ≤ 2 * dn * Cf := by
    have : 1 / Real.sqrt W + m ≤ 2 := by linarith
    calc (dn : ℝ) * β = dn * Cf * (1 / Real.sqrt W + m) := by ring
      _ ≤ dn * Cf * 2 := mul_le_mul_of_nonneg_left this (mul_nonneg hD hCf)
      _ = 2 * dn * Cf := by ring
  have hpow : 1 + ((dn : ℝ) * β) ^ dn ≤ 1 + (2 * dn * Cf) ^ dn :=
    add_le_add_right (pow_le_pow_left₀ (mul_nonneg hD hβ0) hβ dn) 1
  have hβ2 : ((dn : ℝ) * β) ^ 2 ≤ dn ^ 2 * (2 * Cf ^ 2) * E1 := by
    have hm2 : m ^ 2 ≤ δ0 := by nlinarith
    have h1 : (1 / Real.sqrt W + m) ^ 2 ≤ 2 * (W⁻¹ + δ0) := by
      rw [← hsq]; nlinarith [sq_nonneg (1 / Real.sqrt W - m)]
    have h2 : W⁻¹ + δ0 ≤ E1 := by simp only [E1]; linarith
    calc ((dn : ℝ) * β) ^ 2 = dn ^ 2 * Cf ^ 2 * (1 / Real.sqrt W + m) ^ 2 := by ring
      _ ≤ dn ^ 2 * Cf ^ 2 * (2 * (W⁻¹ + δ0)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ dn ^ 2 * Cf ^ 2 * (2 * E1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have herr : W⁻¹ ^ 2 ≤ W⁻¹ := by
    rw [sq]; exact mul_le_of_le_one_left hWi (inv_le_one_of_one_le₀ hW1)
  have he3 : e ≤ Ce * E1 := he1.trans (mul_le_mul_of_nonneg_left (by simp only [E1]; linarith) hCe)
  have he4 : (1 + 1 + e) ^ dn ≤ (3 + μ) ^ dn := pow_le_pow_left₀ (by positivity) (by linarith) dn
  have hA1 : Kd * ((dn : ℝ) * β) ^ 2 * (1 + ((dn : ℝ) * β) ^ dn) ≤
      Kd * (dn ^ 2 * (2 * Cf ^ 2) * E1) * (1 + (2 * dn * Cf) ^ dn) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hβ2 hKd) hpow (by positivity) (by positivity)
  have hA2 : (dn : ℝ) * e * (1 + 1 + e) ^ dn ≤ dn * (Ce * E1) * (3 + μ) ^ dn :=
    mul_le_mul (mul_le_mul_of_nonneg_left he3 hD) he4 (by positivity) (by positivity)
  have hA3 : Ci / W ≤ Ci * E1 := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left (by simp only [E1]; linarith) hCi
  calc Γ * (Kd * ((dn : ℝ) * β) ^ 2 * (1 + ((dn : ℝ) * β) ^ dn) + dn * e * (1 + 1 + e) ^ dn) +
        Ci / W ≤ Γ * (Kd * (dn ^ 2 * (2 * Cf ^ 2) * E1) * (1 + (2 * dn * Cf) ^ dn) +
          dn * (Ce * E1) * (3 + μ) ^ dn) + Ci * E1 :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) hΓ) hA3
    _ = _ := by ring

/-- The arithmetic of the centered bound. -/
theorem arith_fluct {Γ Kd Cf Ci W δ0 m : ℝ} (dn : ℕ) (hΓ : 0 ≤ Γ) (hKd : 0 ≤ Kd)
    (hCf : 0 ≤ Cf) (hCi : 0 ≤ Ci) (hW1 : 1 ≤ W) (hδ0 : 0 ≤ δ0) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hmδ : m ≤ δ0) :
    2 * (Γ * (Kd * ((dn : ℝ) * (Cf * (1 / Real.sqrt W + m))) *
        (1 + ((dn : ℝ) * (Cf * (1 / Real.sqrt W + m))) ^ dn))) + 2 * (Ci / W) ≤
      (2 * (Γ * Kd * (dn * Cf) * (1 + (2 * dn * Cf) ^ dn)) + 2 * Ci) * (1 / Real.sqrt W + δ0) := by
  obtain ⟨hsW, hsW1, hWsW, -⟩ := sqrt_bounds hW1
  have hW0 : 0 < W := by linarith
  have hD := (Nat.cast_nonneg dn : (0 : ℝ) ≤ dn)
  set β := Cf * (1 / Real.sqrt W + m)
  have hβ0 : 0 ≤ β := mul_nonneg hCf (add_nonneg (by positivity) hm0)
  have hE2 : 0 ≤ 1 / Real.sqrt W + δ0 := by positivity
  have hβ : (dn : ℝ) * β ≤ 2 * dn * Cf := by
    have : 1 / Real.sqrt W + m ≤ 2 := by linarith
    calc (dn : ℝ) * β = dn * Cf * (1 / Real.sqrt W + m) := by ring
      _ ≤ dn * Cf * 2 := mul_le_mul_of_nonneg_left this (mul_nonneg hD hCf)
      _ = 2 * dn * Cf := by ring
  have hpow : 1 + ((dn : ℝ) * β) ^ dn ≤ 1 + (2 * dn * Cf) ^ dn :=
    add_le_add_right (pow_le_pow_left₀ (mul_nonneg hD hβ0) hβ dn) 1
  have hB1 : (dn : ℝ) * β ≤ dn * Cf * (1 / Real.sqrt W + δ0) := by
    calc (dn : ℝ) * β = dn * Cf * (1 / Real.sqrt W + m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hD hCf)
  have hB3 : Ci / W ≤ Ci * (1 / Real.sqrt W + δ0) := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left (by linarith) hCi
  have hA : Kd * ((dn : ℝ) * β) * (1 + ((dn : ℝ) * β) ^ dn) ≤
      Kd * (dn * Cf * (1 / Real.sqrt W + δ0)) * (1 + (2 * dn * Cf) ^ dn) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hB1 hKd) hpow (by positivity) (by positivity)
  calc 2 * (Γ * (Kd * ((dn : ℝ) * β) * (1 + ((dn : ℝ) * β) ^ dn))) + 2 * (Ci / W) ≤
        2 * (Γ * (Kd * (dn * Cf * (1 / Real.sqrt W + δ0)) * (1 + (2 * dn * Cf) ^ dn))) +
          2 * (Ci * (1 / Real.sqrt W + δ0)) :=
        add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hΓ) (by norm_num))
          (mul_le_mul_of_nonneg_left hB3 (by norm_num))
    _ = _ := by ring

end BlockBand.SourceProcess.ContractingWords
