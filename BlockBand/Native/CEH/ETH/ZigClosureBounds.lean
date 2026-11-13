module

public import BlockBand.Native.CEH.ETH.ZigClosureConst

/-!
# CEH ETH: the pathwise bounds of the path core along the flow

The fields of the pathwise hypotheses `zpc_Hyp` for the processes of `zcl_Data.proc`, each with the
lemma that gives it:

* `cfX_le`, `cfY_le`: `zgl_norm_coeff_le_twoHeight`;
* `driftX`, `driftY`: `normalizedTrace_flowDrift2_mul` (`B = 1`) and `zgl_drift_X_eq`,
  `zgl_drift_Y_eq`, then the triangle inequality and `‖W_i^{(b)}‖ = ‖W_i‖`;
* `driftZ`: `fz_driftC_eq_cehDrift`, `zgl_fz_cehDrift_eq` (coefficient, cross terms and the four
  `a`-terms), `zgl_norm_index_terms_le` (both indices);
* `cross_le`: `zcl_norm_cross_le` (`4x²`);
* `MA_le`: from a Lemma 5.6 bound `‖⟨M^A_σ⟩‖ ≤ C √chainP` (hypothesis `hMA`, discharged by
  `zgl_lemma56_window_uniform`) and `sqrt_chain_le` at `σ = s`;
* `QX₁_le`, `QX₂_le`, `QY₁_le`, `QY₂_le`, `V₁_le`, `V₂_le`: the resolvent-chain bounds
  `bw_norm_normalizedTrace_…`, rewritten with the heights and the per-constellation identities;
* the brackets `brkXre/im_le` (`bf_avgRe2/avgIm2_bracket_X_le`), `brkYre/im_le`
  (`bf_avgRe2/avgIm2_bracket_Y_le`), `brkZ_le` (`bf_avg_bracket_Z_le_sq`) and their
  nonnegativity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {Ω : Type} {N : ℕ}

/-!
## Generic drift identities
-/

/-- The `X` drift minus `⟨M^I⟩ X` (`B = 1`, `zgl_drift_X_eq`). -/
theorem zcl_driftX_eq (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ μA μI : ℂ) :
    (normalizedTrace (flowDrift2 R₁ R₂ A m₁ m₂) - μA * μI) -
        μI * (normalizedTrace (R₁ * A * R₂) - μA) =
      μA * (normalizedTrace (R₁ * R₂) - μI) +
        (normalizedTrace (R₁ * A * R₂) - μA) * (normalizedTrace (R₁ * R₂) - μI) +
        (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * A * R₂) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * A * R₂ * R₂) := by
  have h1 := normalizedTrace_flowDrift2_mul R₁ R₂ A 1 m₁ m₂
  rw [Matrix.mul_one] at h1
  have h2 := zgl_drift_X_eq R₁ R₂ A m₁ m₂ μA μI
  linear_combination h1 + h2

/-- The `Y` drift minus `2⟨M^I⟩ Y` (`A = B = 1`, `zgl_drift_Y_eq`). -/
theorem zcl_driftY_eq (R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ μI : ℂ) :
    (normalizedTrace (flowDrift2 R₁ R₂ 1 m₁ m₂) - μI * μI) -
        2 * μI * (normalizedTrace (R₁ * R₂) - μI) =
      (normalizedTrace (R₁ * R₂) - μI) ^ 2 +
        (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * R₂) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * R₂ * R₂) := by
  have h1 := normalizedTrace_flowDrift2_mul R₁ R₂ 1 1 m₁ m₂
  rw [Matrix.mul_one] at h1
  have h2 := zgl_drift_Y_eq R₁ R₂ m₁ m₂ μI
  linear_combination h1 + h2

/-- The bracket path function of `ZigTail` with `K = N⁻¹` is the `Re` form of the flow Itô formula. -/
theorem zcl_brkX_true (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) (ω : Ω) (t : ℝ) :
    ztl_brkX F G z₁ m₁ z₂ m₂ s (ztl_evK true (ztl_avgK N)) A ω t =
      1 / (N : ℝ) * ∑ x, (normalizedTrace (pathR F G z₁ m₁ s ω t * hermBasis x *
        pathR F G z₁ m₁ s ω t * A * pathR F G z₂ m₂ s ω t * 1) +
      normalizedTrace (pathR F G z₁ m₁ s ω t * A * pathR F G z₂ m₂ s ω t * hermBasis x *
        pathR F G z₂ m₂ s ω t * 1)).re ^ 2 := by
  unfold ztl_brkX
  simp only [ztl_reTr_evK_avgK_true, Matrix.mul_one, Phase1.normalizedTrace_add]

/-- The bracket path function of `ZigTail` with `K = -iN⁻¹` is the `Im` form of the flow Itô formula. -/
theorem zcl_brkX_false (F : Matrix (Fin N) (Fin N) ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ≥0) (A : Matrix (Fin N) (Fin N) ℂ) (ω : Ω) (t : ℝ) :
    ztl_brkX F G z₁ m₁ z₂ m₂ s (ztl_evK false (ztl_avgK N)) A ω t =
      1 / (N : ℝ) * ∑ x, (normalizedTrace (pathR F G z₁ m₁ s ω t * hermBasis x *
        pathR F G z₁ m₁ s ω t * A * pathR F G z₂ m₂ s ω t * 1) +
      normalizedTrace (pathR F G z₁ m₁ s ω t * A * pathR F G z₂ m₂ s ω t * hermBasis x *
        pathR F G z₂ m₂ s ω t * 1)).im ^ 2 := by
  unfold ztl_brkX
  simp only [ztl_reTr_evK_avgK_false, Matrix.mul_one, Phase1.normalizedTrace_add]

namespace zcl_Data

variable {d : zcl_Data Ω N} (hd : d.Valid) (ω : Ω)
include hd

/-!
## Linear coefficients
-/

theorem cfX_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    ‖(d.proc ω).cfX k r‖ ≤ (d.geom.c₁ / d.geom.e₁ r + d.geom.c₂ / d.geom.e₂ r) / 2 := by
  intro r hr
  have h := zgl_norm_coeff_le_twoHeight hd.mde₁ hd.mde₂ hd.z₁_pos.ne' hd.z₂_pos.ne' d.s.2
    (zcl_ch k.1) (zcl_ch k.2) r hr
  rw [abs_of_pos hd.z₁_pos, abs_of_pos hd.z₂_pos,
    abs_of_pos (show 0 < (NTrace d.M₁).im from hd.m₁_pos),
    abs_of_pos (show 0 < (NTrace d.M₂).im from hd.m₂_pos)] at h
  exact h

theorem cfY_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    ‖(d.proc ω).cfY k r‖ ≤ (d.geom.c₁ / d.geom.e₁ r + d.geom.c₂ / d.geom.e₂ r) / 2 :=
  cfX_le hd ω k

/-!
## Drifts
-/

theorem driftX (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    ‖(d.proc ω).DX k r - (d.proc ω).cfX k r * (d.proc ω).X k r‖ ≤
      ‖(d.proc ω).MA k r‖ * ‖(d.proc ω).Y ((d.proc ω).yX k) r‖ +
        ‖(d.proc ω).X k r‖ * ‖(d.proc ω).Y ((d.proc ω).yX k) r‖ +
        ‖(d.proc ω).W₁ r‖ * ‖(d.proc ω).QX₁ k r‖ + ‖(d.proc ω).W₂ r‖ * ‖(d.proc ω).QX₂ k r‖ := by
  intro r _
  rw [← hd.norm_W₁ k.1 ω r, ← hd.norm_W₂ k.2 ω r]
  change ‖(normalizedTrace (flowDrift2 (d.R₁ k.1 ω r) (d.R₂ k.2 ω r) d.A (ztl_cz k.1 d.m₁)
      (ztl_cz k.2 d.m₂)) - d.μA k r * d.μI k r) - d.μI k r *
      (normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r) - d.μA k r)‖ ≤ _
  rw [zcl_driftX_eq]
  refine norm_add₄_le.trans (le_of_eq ?_)
  simp only [norm_mul]
  rfl

theorem driftY (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    ‖(d.proc ω).DY k r - 2 * (d.proc ω).cfY k r * (d.proc ω).Y k r‖ ≤
      ‖(d.proc ω).Y k r‖ ^ 2 + ‖(d.proc ω).W₁ r‖ * ‖(d.proc ω).QY₁ k r‖ +
        ‖(d.proc ω).W₂ r‖ * ‖(d.proc ω).QY₂ k r‖ := by
  intro r _
  rw [← hd.norm_W₁ k.1 ω r, ← hd.norm_W₂ k.2 ω r]
  change ‖(normalizedTrace (flowDrift2 (d.R₁ k.1 ω r) (d.R₂ k.2 ω r) 1 (ztl_cz k.1 d.m₁)
      (ztl_cz k.2 d.m₂)) - d.μI k r * d.μI k r) - 2 * d.μI k r *
      (normalizedTrace (d.R₁ k.1 ω r * d.R₂ k.2 ω r) - d.μI k r)‖ ≤ _
  rw [zcl_driftY_eq]
  refine (norm_add₃_le).trans (le_of_eq ?_)
  simp only [norm_mul, norm_pow]
  rfl

theorem V₁_norm (r : ℝ) (hr : r ∈ Icc 0 d.geom.s) :
    ‖(d.proc ω).V₁ r‖ = |(d.proc ω).Z r| / d.geom.e₁ r := by
  change ‖((|d.Zp ω r| / d.geom.e₁ r : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (hd.geom_valid.e₁_pos hr.2).le)]
  rfl

theorem V₂_norm (r : ℝ) (hr : r ∈ Icc 0 d.geom.s) :
    ‖(d.proc ω).V₂ r‖ = |(d.proc ω).Z r| / d.geom.e₂ r := by
  change ‖((|d.Zp ω r| / d.geom.e₂ r : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (hd.geom_valid.e₂_pos hr.2).le)]
  rfl

theorem V₁_le : ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).V₁ r‖ ≤ |(d.proc ω).Z r| / d.geom.e₁ r :=
  fun r hr => (V₁_norm hd ω r hr).le

theorem V₂_le : ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).V₂ r‖ ≤ |(d.proc ω).Z r| / d.geom.e₂ r :=
  fun r hr => (V₂_norm hd ω r hr).le

theorem driftZ : ∀ r ∈ Icc 0 d.geom.s, |(d.proc ω).DZ r| ≤
    (‖(d.proc ω).W₁ r‖ / d.geom.e₁ r + ‖(d.proc ω).W₂ r‖ / d.geom.e₂ r) * |(d.proc ω).Z r| +
      2 * ‖(d.proc ω).W₁ r‖ * ‖(d.proc ω).V₁ r‖ + 2 * ‖(d.proc ω).W₂ r‖ * ‖(d.proc ω).V₂ r‖ +
      ‖(d.proc ω).cross r‖ := by
  intro r hr
  have he₁ := hd.geom_valid.e₁_pos hr.2
  have he₂ := hd.geom_valid.e₂_pos hr.2
  rw [V₁_norm hd ω r hr, V₂_norm hd ω r hr]
  set R₁ := Phase1.resolvent (d.H ω r) (d.w₁ true r) with hR₁
  set R₂ := Phase1.resolvent (d.H ω r) (d.w₂ true r) with hR₂
  have hD : (d.proc ω).DZ r = (fz_cehDrift R₁ R₂ d.A d.m₁ d.m₂ (d.w₁ true r)
      (d.w₂ true r)).re := by
    change (fz_driftC R₁ R₂ d.A d.m₁ d.m₂).re = _
    rw [fz_driftC_eq_cehDrift (hd.H_herm ω r) (hd.w₁_ne true hr) (hd.w₂_ne true hr)]
  have hW₁ : (d.proc ω).W₁ r = normalizedTrace R₁ - d.m₁ := rfl
  have hW₂ : (d.proc ω).W₂ r = normalizedTrace R₂ - d.m₂ := rfl
  have hX : (d.proc ω).cross r = zgl_cross R₁ R₂ d.A := rfl
  have hc : ‖normalizedTrace (bwImChain d.A R₁ R₂)‖ = |(d.proc ω).Z r| :=
    hd.norm_chain true true ω hr
  have hc' : ‖fz_chain R₁ R₂ d.A‖ = |(d.proc ω).Z r| := hc
  rw [hD, zgl_fz_cehDrift_eq, hW₁, hW₂, hX]
  have hidx := zgl_norm_index_terms_le (hd.H_herm ω r) (hd.w₁_ne true hr) (hd.w₂_ne true hr)
    d.A (normalizedTrace R₁ - d.m₁) (normalizedTrace R₂ - d.m₂)
  rw [hd.abs_w₁ true hr, hd.abs_w₂ true hr, hc] at hidx
  have hcoef : ‖((((normalizedTrace R₁ - d.m₁).im / (d.w₁ true r).im +
      (normalizedTrace R₂ - d.m₂).im / (d.w₂ true r).im : ℝ)) : ℂ)‖ ≤
      ‖normalizedTrace R₁ - d.m₁‖ / d.geom.e₁ r + ‖normalizedTrace R₂ - d.m₂‖ / d.geom.e₂ r := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, hd.abs_w₁ true hr]
      exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) he₁.le
    · rw [abs_div, hd.abs_w₂ true hr]
      exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) he₂.le
  set c := ((((normalizedTrace R₁ - d.m₁).im / (d.w₁ true r).im +
      (normalizedTrace R₂ - d.m₂).im / (d.w₂ true r).im : ℝ)) : ℂ)
  set I := (normalizedTrace R₁ - d.m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * d.A *
          External.CEH.imaginaryPart R₂ * d.Aᴴ * R₁) +
        (normalizedTrace R₂ - d.m₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * d.Aᴴ *
          External.CEH.imaginaryPart R₁ * d.A * R₂) +
        conj (normalizedTrace R₁ - d.m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ *
          d.A * External.CEH.imaginaryPart R₂ * d.Aᴴ * R₁ᴴ) +
        conj (normalizedTrace R₂ - d.m₂) * normalizedTrace (External.CEH.imaginaryPart R₂ *
          d.Aᴴ * External.CEH.imaginaryPart R₁ * d.A * R₂ᴴ) with hI
  have hZ0 := abs_nonneg ((d.proc ω).Z r)
  have hcc : ‖c * fz_chain R₁ R₂ d.A‖ ≤ (‖normalizedTrace R₁ - d.m₁‖ / d.geom.e₁ r +
      ‖normalizedTrace R₂ - d.m₂‖ / d.geom.e₂ r) * |(d.proc ω).Z r| := by
    rw [norm_mul, hc']
    exact mul_le_mul_of_nonneg_right hcoef hZ0
  calc |(c * fz_chain R₁ R₂ d.A + zgl_cross R₁ R₂ d.A + I).re|
      ≤ ‖c * fz_chain R₁ R₂ d.A + zgl_cross R₁ R₂ d.A + I‖ := Complex.abs_re_le_norm _
    _ ≤ ‖c * fz_chain R₁ R₂ d.A‖ + ‖zgl_cross R₁ R₂ d.A‖ + ‖I‖ := norm_add₃_le
    _ ≤ _ := by
        have e : 2 * (‖normalizedTrace R₁ - d.m₁‖ / d.geom.e₁ r +
            ‖normalizedTrace R₂ - d.m₂‖ / d.geom.e₂ r) * |(d.proc ω).Z r| =
            2 * ‖normalizedTrace R₁ - d.m₁‖ * (|(d.proc ω).Z r| / d.geom.e₁ r) +
              2 * ‖normalizedTrace R₂ - d.m₂‖ * (|(d.proc ω).Z r| / d.geom.e₂ r) := by ring
        linarith

/-!
## Cross terms and the deterministic approximation
-/

theorem cross_le : ∀ r ∈ Icc 0 d.geom.s, ∀ x : ℝ,
    (∀ k, ‖(d.proc ω).X k r‖ + ‖(d.proc ω).MA k r‖ ≤ x) → ‖(d.proc ω).cross r‖ ≤ 4 * x ^ 2 := by
  intro r _ x hx
  have hk : ∀ k : Bool × Bool,
      ‖normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r)‖ ≤ x := by
    intro k
    refine le_trans ?_ (hx k)
    have := norm_add_le ((d.proc ω).X k r) ((d.proc ω).MA k r)
    have e : (d.proc ω).X k r + (d.proc ω).MA k r =
        normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r) := by
      change normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r) - d.μA k r + d.μA k r = _
      ring
    rw [e] at this
    exact this
  have h₁₁ := hk (true, true)
  have h₁₂ := hk (true, false)
  have h₂₁ := hk (false, true)
  have h₂₂ := hk (false, false)
  dsimp only at h₁₁ h₁₂ h₂₁ h₂₂
  rw [hd.R₂_cz false ω r] at h₁₂ h₂₂
  rw [hd.R₁_cz false ω r] at h₂₁ h₂₂
  simp only [Bool.false_eq_true, ↓reduceIte] at h₁₂ h₂₁ h₂₂
  exact zcl_norm_cross_le _ _ _ h₁₁ h₁₂ h₂₁ h₂₂

/-- **`MA_le`** from the Lemma 5.6 form `‖⟨M^A_σ⟩‖ ≤ C √chainP` (`C = p.Cm`). -/
theorem MA_le {p : zpc_Par} (hCm : 0 ≤ p.Cm)
    (hMA : ∀ k : Bool × Bool, ∀ r ∈ Icc 0 (d.s : ℝ), ‖d.μA k r‖ ≤
      p.Cm * Real.sqrt (NTrace (matrixImaginaryPart d.M₁ * d.A * matrixImaginaryPart d.M₂ *
        d.Aᴴ)).re) :
    ∀ k, ∀ r ∈ Icc 0 d.geom.s,
      ‖(d.proc ω).MA k r‖ ≤ p.Cm * Real.pi * Real.sqrt (d.geom.ρ₁ * d.geom.ρ₂) * d.geom.S := by
  intro k r hr
  refine (hMA k r hr).trans ?_
  have h := sqrt_chain_le d.M₁ d.M₂ d.A (show 0 < (NTrace d.M₁).im from hd.m₁_pos)
    (show 0 < (NTrace d.M₂).im from hd.m₂_pos) d.s.2
  calc p.Cm * Real.sqrt (NTrace (matrixImaginaryPart d.M₁ * d.A * matrixImaginaryPart d.M₂ *
        d.Aᴴ)).re ≤ p.Cm * (Real.pi * Real.sqrt (cehDensityOf d.M₁ * cehDensityOf d.M₂) *
          sTwoAt d.s d.M₁ d.M₂ d.A) := mul_le_mul_of_nonneg_left h hCm
    _ = _ := by
        change _ = p.Cm * Real.pi * Real.sqrt (cehDensityOf d.M₁ * cehDensityOf d.M₂) *
          sTwoAt d.s d.M₁ d.M₂ d.A
        ring

/-!
## Chains with a squared resolvent
-/

theorem QX₁_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).QX₁ k r‖ ≤
    (d.geom.e₁ r)⁻¹ * Real.sqrt (d.geom.e₂ r)⁻¹ * Real.sqrt ((d.proc ω).imR₁ r) *
      Real.sqrt |(d.proc ω).Z r| := by
  intro r hr
  have h : ‖normalizedTrace (d.R₁ k.1 ω r * d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r)‖ ≤
      |(d.w₁ k.1 r).im|⁻¹ * Real.sqrt |(d.w₂ k.2 r).im|⁻¹ *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ k.1 ω r))‖ *
        Real.sqrt ‖normalizedTrace (bwImChain d.A (d.R₁ k.1 ω r) (d.R₂ k.2 ω r))‖ :=
    bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le (hd.H_herm ω r) (hd.w₁_ne k.1 hr)
      (hd.w₂_ne k.2 hr) d.A
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.norm_imR₁ k.1 ω r, hd.norm_chain k.1 k.2 ω hr]
    at h
  exact h

theorem QX₂_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).QX₂ k r‖ ≤
    (d.geom.e₂ r)⁻¹ * Real.sqrt (d.geom.e₁ r)⁻¹ * Real.sqrt ((d.proc ω).imR₂ r) *
      Real.sqrt |(d.proc ω).Z r| := by
  intro r hr
  have h : ‖normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r * d.R₂ k.2 ω r)‖ ≤
      |(d.w₂ k.2 r).im|⁻¹ * Real.sqrt |(d.w₁ k.1 r).im|⁻¹ *
        Real.sqrt ‖normalizedTrace (External.CEH.imaginaryPart (d.R₂ k.2 ω r))‖ *
        Real.sqrt ‖normalizedTrace (bwImChain d.A (d.R₁ k.1 ω r) (d.R₂ k.2 ω r))‖ :=
    bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le (hd.H_herm ω r) (hd.w₁_ne k.1 hr)
      (hd.w₂_ne k.2 hr) d.A
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.norm_imR₂ k.2 ω r, hd.norm_chain k.1 k.2 ω hr]
    at h
  exact h

theorem QY₁_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).QY₁ k r‖ ≤
    (d.proc ω).imR₁ r / (d.geom.e₁ r * d.geom.e₂ r) := by
  intro r hr
  have h : ‖normalizedTrace (d.R₁ k.1 ω r * d.R₁ k.1 ω r * d.R₂ k.2 ω r)‖ ≤
      ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ k.1 ω r))‖ /
        (|(d.w₁ k.1 r).im| * |(d.w₂ k.2 r).im|) :=
    bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le_div (hd.H_herm ω r)
      (hd.w₁_ne k.1 hr) (hd.w₂_ne k.2 hr)
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.norm_imR₁ k.1 ω r] at h
  exact h

theorem QY₂_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).QY₂ k r‖ ≤
    (d.proc ω).imR₂ r / (d.geom.e₁ r * d.geom.e₂ r) := by
  intro r hr
  have h : ‖normalizedTrace (d.R₁ k.1 ω r * d.R₂ k.2 ω r * d.R₂ k.2 ω r)‖ ≤
      ‖normalizedTrace (External.CEH.imaginaryPart (d.R₂ k.2 ω r))‖ /
        (|(d.w₁ k.1 r).im| * |(d.w₂ k.2 r).im|) :=
    bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le_div (hd.H_herm ω r)
      (hd.w₁_ne k.1 hr) (hd.w₂_ne k.2 hr)
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.norm_imR₂ k.2 ω r] at h
  exact h

/-!
## Brackets
-/

omit hd in
theorem brkXre_nonneg (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    0 ≤ (d.proc ω).brkXre k r := by
  intro r _
  change 0 ≤ ztl_brkX _ _ _ _ _ _ _ _ _ _ _
  unfold ztl_brkX
  positivity

omit hd in
theorem brkXim_nonneg (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    0 ≤ (d.proc ω).brkXim k r := by
  intro r _
  change 0 ≤ ztl_brkX _ _ _ _ _ _ _ _ _ _ _
  unfold ztl_brkX
  positivity

omit hd in
theorem brkYre_nonneg (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    0 ≤ (d.proc ω).brkYre k r := by
  intro r _
  change 0 ≤ ztl_brkX _ _ _ _ _ _ _ _ _ _ _
  unfold ztl_brkX
  positivity

omit hd in
theorem brkYim_nonneg (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s,
    0 ≤ (d.proc ω).brkYim k r := by
  intro r _
  change 0 ≤ ztl_brkX _ _ _ _ _ _ _ _ _ _ _
  unfold ztl_brkX
  positivity

omit hd in
theorem brkZ_nonneg : ∀ r ∈ Icc 0 d.geom.s, 0 ≤ (d.proc ω).brkZ r := by
  intro r _
  change 0 ≤ ztl_brkZ _ _ _ _ _ _ _ _ _ _
  unfold ztl_brkZ
  positivity

theorem brkXre_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).brkXre k r ≤
    2 / d.geom.N ^ 2 * ((d.geom.e₁ r)⁻¹ ^ 3 * (d.geom.e₂ r)⁻¹ +
      (d.geom.e₁ r)⁻¹ * (d.geom.e₂ r)⁻¹ ^ 3) * |(d.proc ω).Z r| := by
  intro r hr
  have h : 1 / (N : ℝ) * ∑ x, (normalizedTrace (d.R₁ k.1 ω r * hermBasis x * d.R₁ k.1 ω r *
      d.A * d.R₂ k.2 ω r * 1) + normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r *
      hermBasis x * d.R₂ k.2 ω r * 1)).re ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|(d.w₁ k.1 r).im|⁻¹ ^ 3 * |(d.w₂ k.2 r).im|⁻¹ +
        |(d.w₁ k.1 r).im|⁻¹ * |(d.w₂ k.2 r).im|⁻¹ ^ 3) *
        ‖normalizedTrace (bwImChain d.A (d.R₁ k.1 ω r) (d.R₂ k.2 ω r))‖ :=
    bf_avgRe2_bracket_X_le (hd.H_herm ω r) (hd.w₁_ne k.1 hr) (hd.w₂_ne k.2 hr) d.A
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.norm_chain k.1 k.2 ω hr] at h
  refine le_of_eq_of_le ?_ h
  exact zcl_brkX_true _ _ _ _ _ _ _ _ _ _

theorem brkXim_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).brkXim k r ≤
    2 / d.geom.N ^ 2 * ((d.geom.e₁ r)⁻¹ ^ 3 * (d.geom.e₂ r)⁻¹ +
      (d.geom.e₁ r)⁻¹ * (d.geom.e₂ r)⁻¹ ^ 3) * |(d.proc ω).Z r| := by
  intro r hr
  have h : 1 / (N : ℝ) * ∑ x, (normalizedTrace (d.R₁ k.1 ω r * hermBasis x * d.R₁ k.1 ω r *
      d.A * d.R₂ k.2 ω r * 1) + normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r *
      hermBasis x * d.R₂ k.2 ω r * 1)).im ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|(d.w₁ k.1 r).im|⁻¹ ^ 3 * |(d.w₂ k.2 r).im|⁻¹ +
        |(d.w₁ k.1 r).im|⁻¹ * |(d.w₂ k.2 r).im|⁻¹ ^ 3) *
        ‖normalizedTrace (bwImChain d.A (d.R₁ k.1 ω r) (d.R₂ k.2 ω r))‖ :=
    bf_avgIm2_bracket_X_le (hd.H_herm ω r) (hd.w₁_ne k.1 hr) (hd.w₂_ne k.2 hr) d.A
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.norm_chain k.1 k.2 ω hr] at h
  refine le_of_eq_of_le ?_ h
  exact zcl_brkX_false _ _ _ _ _ _ _ _ _ _

theorem brkYre_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).brkYre k r ≤
    2 / d.geom.N ^ 2 * ((d.geom.e₁ r)⁻¹ ^ 3 * (d.geom.e₂ r)⁻¹ +
      (d.geom.e₁ r)⁻¹ * (d.geom.e₂ r)⁻¹ ^ 3) * (d.proc ω).TI r := by
  intro r hr
  have h : 1 / (N : ℝ) * ∑ x, (normalizedTrace (d.R₁ k.1 ω r * hermBasis x * d.R₁ k.1 ω r *
      1 * d.R₂ k.2 ω r * 1) + normalizedTrace (d.R₁ k.1 ω r * 1 * d.R₂ k.2 ω r *
      hermBasis x * d.R₂ k.2 ω r * 1)).re ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|(d.w₁ k.1 r).im|⁻¹ ^ 3 * |(d.w₂ k.2 r).im|⁻¹ +
        |(d.w₁ k.1 r).im|⁻¹ * |(d.w₂ k.2 r).im|⁻¹ ^ 3) *
        ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ k.1 ω r) *
          External.CEH.imaginaryPart (d.R₂ k.2 ω r))‖ :=
    bf_avgRe2_bracket_Y_le (hd.H_herm ω r) (hd.w₁_ne k.1 hr) (hd.w₂_ne k.2 hr)
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.TI_eq k.1 k.2 ω r] at h
  refine le_of_eq_of_le ?_ h
  exact zcl_brkX_true _ _ _ _ _ _ _ _ _ _

theorem brkYim_le (k : Bool × Bool) : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).brkYim k r ≤
    2 / d.geom.N ^ 2 * ((d.geom.e₁ r)⁻¹ ^ 3 * (d.geom.e₂ r)⁻¹ +
      (d.geom.e₁ r)⁻¹ * (d.geom.e₂ r)⁻¹ ^ 3) * (d.proc ω).TI r := by
  intro r hr
  have h : 1 / (N : ℝ) * ∑ x, (normalizedTrace (d.R₁ k.1 ω r * hermBasis x * d.R₁ k.1 ω r *
      1 * d.R₂ k.2 ω r * 1) + normalizedTrace (d.R₁ k.1 ω r * 1 * d.R₂ k.2 ω r *
      hermBasis x * d.R₂ k.2 ω r * 1)).im ^ 2 ≤
      2 / (N : ℝ) ^ 2 * (|(d.w₁ k.1 r).im|⁻¹ ^ 3 * |(d.w₂ k.2 r).im|⁻¹ +
        |(d.w₁ k.1 r).im|⁻¹ * |(d.w₂ k.2 r).im|⁻¹ ^ 3) *
        ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ k.1 ω r) *
          External.CEH.imaginaryPart (d.R₂ k.2 ω r))‖ :=
    bf_avgIm2_bracket_Y_le (hd.H_herm ω r) (hd.w₁_ne k.1 hr) (hd.w₂_ne k.2 hr)
  rw [hd.abs_w₁ k.1 hr, hd.abs_w₂ k.2 hr, hd.TI_eq k.1 k.2 ω r] at h
  refine le_of_eq_of_le ?_ h
  exact zcl_brkX_false _ _ _ _ _ _ _ _ _ _

theorem brkZ_le : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).brkZ r ≤
    2 / d.geom.N * ((d.geom.e₁ r)⁻¹ ^ 2 + (d.geom.e₂ r)⁻¹ ^ 2) * (d.proc ω).Z r ^ 2 := by
  intro r hr
  have h : 1 / (N : ℝ) * ∑ x,
      (bfZDiff d.A (d.R₁ true ω r) (d.R₂ true ω r) (hermBasis x)).re ^ 2 ≤
      2 / (N : ℝ) * (|(d.w₁ true r).im|⁻¹ ^ 2 + |(d.w₂ true r).im|⁻¹ ^ 2) *
        (normalizedTrace (bwImChain d.A (d.R₁ true ω r) (d.R₂ true ω r))).re ^ 2 :=
    bf_avg_bracket_Z_le_sq (hd.H_herm ω r) (hd.w₁_ne true hr) (hd.w₂_ne true hr) d.A
  rw [hd.abs_w₁ true hr, hd.abs_w₂ true hr] at h
  exact h

end zcl_Data

end BlockBand.Native.CEH.ETH
