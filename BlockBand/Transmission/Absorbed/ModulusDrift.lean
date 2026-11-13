module

public import BlockBand.Transmission.Absorbed.ModulusFour

/-!
# The absorbed modulus: the crude one-layer drift

**`modulusDrift_layer_bulk hGA hLp`**: `b ∈ (0,1/2)`, `κ > 0`, `k` first; then `K ≥ 0, W₀`; for
`W ≥ W₀`, `E ∈ bulkInterval κ` and every passive `X`,
`|E Re Tr T(X₊)^{k+1} - Re Tr T(X)^{k+1}| ≤ K·Y'³/W`, `Y' = (g+1)(Wδ₀+1)`.

Route (`br_expand` about `D = sand T 1`, first order only): `Δ = x + b + R` with
* `x = (k+1) Re brLin(U - Ū)`, `E x = 0` (`integral_brLin_centered`);
* `|b| ≤ (k+1)νg` (`norm_brLin_le`), `ν ≤ C_ν Y'/W` (`br_nu_le`);
* `|R| ≤ c(2h + 2ν²g)` (`br_rem_le`), `h = ‖sand T(U - Ū)‖²_HS`; `2h ≤ t + h²/t` with
  `t = C²(g+1)²/W` and `E h² ≤ (C g/√W)⁴ ≤ t²` (`hs_moment4_bulk`), so `E|R| ≤ c(2t + 2ν²g)`.
No mixing factor and no `δ₁` enter: the majorant is `Y'`, as in `modulusFour_layer_bulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Generator
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- The real bookkeeping of the crude drift. -/
theorem drift_rhs_le {Kk ck C Cν ν g Y Wr : ℝ} (hKk : 0 ≤ Kk) (hck : 0 ≤ ck) (hCν : 0 ≤ Cν)
    (hWr : 1 ≤ Wr) (hY1 : 1 ≤ Y) (hg : 0 ≤ g) (hgY : g + 1 ≤ Y) (hν0 : 0 ≤ ν)
    (hν : ν ≤ Cν * Y / Wr) :
    Kk * (ν * g) + ck * (2 * (C ^ 2 * (g + 1) ^ 2 / Wr) + 2 * (ν ^ 2 * g)) ≤
      (Kk * Cν + 2 * ck * C ^ 2 + 2 * ck * Cν ^ 2) * (Y ^ 3 / Wr) := by
  have hW0 : 0 < Wr := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hgY' : g ≤ Y := by linarith
  have hY2 : Y ^ 2 ≤ Y ^ 3 := by nlinarith
  have hνW : ν * Wr ≤ Cν * Y := by rwa [le_div_iff₀ hW0] at hν
  have hνY : ν ≤ Cν * Y := by nlinarith
  -- `νg ≤ CνY³/W`
  have a1 : ν * g ≤ Cν * (Y ^ 3 / Wr) := by
    rw [mul_div_assoc', le_div_iff₀ hW0]
    have : ν * g * Wr ≤ Cν * Y * Y := by
      calc ν * g * Wr = ν * Wr * g := by ring
        _ ≤ Cν * Y * Y := mul_le_mul hνW hgY' hg (by positivity)
    nlinarith
  -- `(g+1)² ≤ Y³`
  have a2 : (g + 1) ^ 2 ≤ Y ^ 3 := (pow_le_pow_left₀ (by linarith) hgY 2).trans hY2
  -- `ν²g ≤ Cν²Y³/W`
  have a3 : ν ^ 2 * g ≤ Cν ^ 2 * (Y ^ 3 / Wr) := by
    rw [mul_div_assoc', le_div_iff₀ hW0]
    have h1 : ν ^ 2 * Wr ≤ Cν ^ 2 * Y ^ 2 := by
      have : (ν * Wr) * ν ≤ (Cν * Y) * (Cν * Y) := mul_le_mul hνW hνY hν0 (by positivity)
      nlinarith
    calc ν ^ 2 * g * Wr = ν ^ 2 * Wr * g := by ring
      _ ≤ Cν ^ 2 * Y ^ 2 * Y := mul_le_mul h1 hgY' hg (by positivity)
      _ = Cν ^ 2 * Y ^ 3 := by ring
  have a2' : C ^ 2 * (g + 1) ^ 2 / Wr ≤ C ^ 2 * (Y ^ 3 / Wr) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right a2 hW0.le) (sq_nonneg _)
  have b1 := mul_le_mul_of_nonneg_left a1 hKk
  have b2 : ck * (2 * (C ^ 2 * (g + 1) ^ 2 / Wr) + 2 * (ν ^ 2 * g)) ≤
      ck * (2 * (C ^ 2 * (Y ^ 3 / Wr)) + 2 * (Cν ^ 2 * (Y ^ 3 / Wr))) :=
    mul_le_mul_of_nonneg_left (by linarith) hck
  nlinarith

/-- **The crude one-layer drift with the majorant `Y' = (g+1)(Wδ₀+1)`**, bulk-uniform. -/
theorem modulusDrift_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        |∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ∂freshLaw W b| ≤
          K * ((((passiveTransmission b E X).trace.re + 1) * (W * jetDistance0 b E X + 1)) ^ 3 /
            W) := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨C4, W4, hC4, hm4⟩ := hs_moment4_bulk hA hb0 hb hκ
  obtain ⟨Wi, hUi⟩ := ml_integrable_U_bulk hA hb0 hb hκ
  obtain ⟨Cu, Wu, hCu, hUB⟩ := ubarMean_bulk hA hb0 hb hκ
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set cq := (4 * ηL)⁻¹
  have hcq : 0 ≤ cq := by positivity
  set CD := sigmaPlus b / (2 * ηL ^ 2)
  have hCD : 0 ≤ CD := by
    have : 0 ≤ sigmaPlus b := by
      simp only [sigmaPlus, kPlus]; have : 0 ≤ (1 - b) ^ 2 := sq_nonneg _
      have e : 1 - 2 * b + b ^ 2 = (1 - b) ^ 2 := by ring
      rw [e]; positivity
    positivity
  set Kk : ℝ := ((k + 1 : ℕ) : ℝ)
  set ck : ℝ := Kk * (3 * 2) ^ (2 * (k + 1))
  set Cν := Cu * (2 + cq) + CD
  have hCν : 0 ≤ Cν := by positivity
  set C := C4 + 1
  refine ⟨Kk * Cν + 2 * ck * C ^ 2 + 2 * ck * Cν ^ 2, max (max W4 Wi) (max Wu 1),
    by positivity, fun W hW E hE X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW4, hWi⟩, hWu, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hs2 : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWpos.le
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  have hT : (passiveTransmission b E X).PosSemidef :=
    passiveTransmission_posSemidef (by linarith) h1 h2 hX
  have ht1 : ∀ i, ts_lam hT i ≤ 1 :=
    ts_lam_le_one hT (one_sub_passiveTransmission_posSemidef b E X)
  set g := (passiveTransmission b E X).trace.re
  set δ := jetDistance0 b E X
  set q := passiveMass b E X
  have hg : 0 ≤ g := (mm_trace_posSemidef hT).1
  have hq0 : 0 ≤ q := passiveMass_nonneg b E hX
  have hqg : q ≤ cq * g := mass_le_bulk (by linarith) hκ hE hX
  have ha : 0 ≤ (W : ℝ) * δ := mul_nonneg hWpos.le (norm_nonneg _)
  set Y := (g + 1) * (W * δ + 1)
  have hY1 : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hg1Y : g + 1 ≤ Y := le_mul_of_one_le_right (by linarith) (by linarith)
  have hgY : g ≤ Y := by linarith
  have haY : (W : ℝ) * δ ≤ Y := by
    have : W * δ + 1 ≤ Y := le_mul_of_one_le_left (by linarith) (by linarith)
    linarith
  obtain ⟨hD0, hDC⟩ := transportD0_le_bulk hb0 (by linarith) hκ hE
  set U := freshU b E X
  set μ := freshLaw W b
  have hUm : Measurable U := measurable_freshU b E X
  have hUi' := hUi W hWi E hE X hX
  have hS := ae_norm_sand_freshU_le hb0 hb hW1 h1 h2 hX hT
  set ν := Cu * (δ + (W : ℝ)⁻¹ ^ 2 + q / W) + transportD0 b E * g / (2 * W)
  set Ub := matrixExpect μ U
  have hν : ‖Ub - 1‖ ≤ ν :=
    (norm_ubar_sub_one_le hb0 hb h1 h2 hD0 hX _).trans (by linarith [(hUB W hWu E hE X hX).1])
  have hν0 : 0 ≤ ν := add_nonneg (mul_nonneg hCu (add_nonneg (add_nonneg (norm_nonneg _)
    (by positivity)) (div_nonneg hq0 hWpos.le))) (div_nonneg (mul_nonneg hD0 hg) (by positivity))
  have hνY : ν ≤ Cν * Y / W := by
    have := br_nu_le hCu hWr hs2 haY hqg hcq hg hgY hY1 hD0 hDC
    rwa [hs2] at this
  obtain ⟨hh0, hH40⟩ := hm4 W hW4 E hE X hX hT
  -- the decomposition
  set h : LayerSample W .oneBlockOnePort → ℝ := fun ω => frobSq (sand hT (U ω - Ub))
  have hh : Integrable (fun ω => h ω ^ 2) μ := hh0
  have hH4 : ∫ ω, h ω ^ 2 ∂μ ≤ (C4 / Real.sqrt W * g) ^ 4 := hH40
  set x : LayerSample W .oneBlockOnePort → ℝ := fun ω => Kk * (brLin hT (k + 1) (U ω - Ub)).re
  set bb : ℝ := Kk * (brLin hT (k + 1) (Ub - 1)).re
  set t : ℝ := C ^ 2 * (g + 1) ^ 2 / W
  have ht0 : 0 < t := by positivity
  have hDm : Measurable fun ω => brInc hT (k + 1) (U ω) :=
    (continuous_brInc hT (k + 1)).measurable.comp hUm
  have iD : Integrable (fun ω => brInc hT (k + 1) (U ω)) μ := by
    refine Integrable.of_bound hDm.aestronglyMeasurable (2 * W) ?_
    filter_upwards [hS] with ω hω
    rw [Real.norm_eq_abs]; exact abs_brInc_le hT ht1 (k + 1) hω
  have ix : Integrable x μ :=
    (integrable_cre (integrable_brLin_centered hT U hUi' _)).const_mul _
  have ex : ∫ ω, x ω ∂μ = 0 := by
    simp only [x]
    rw [integral_const_mul, integral_cre (integrable_brLin_centered hT U hUi' _),
      integral_brLin_centered hT U hUi', Complex.zero_re, mul_zero]
  set F : LayerSample W .oneBlockOnePort → ℝ :=
    fun ω => ck * (t + h ω ^ 2 / t + 2 * (ν ^ 2 * g))
  have iF : Integrable F μ :=
    (((integrable_const t).add (hh.div_const t)).add (integrable_const _)).const_mul _
  have hpt : ∀ᵐ ω ∂μ, ‖brInc hT (k + 1) (U ω) - x ω - bb‖ ≤ F ω := by
    filter_upwards [hS] with ω hω
    rw [Real.norm_eq_abs]
    have hR := br_rem_le hT ht1 hω hν k
    have hh0 : 0 ≤ h ω := by
      simp only [h, frobSq]; positivity
    have hy : 2 * h ω ≤ t + h ω ^ 2 / t := by
      rw [← sub_nonneg]
      have : t + h ω ^ 2 / t - 2 * h ω = (h ω - t) ^ 2 / t := by field_simp; ring
      rw [this]; positivity
    have hck : 0 ≤ ck := by positivity
    refine hR.trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hck
  have iR : Integrable (fun ω => brInc hT (k + 1) (U ω) - x ω - bb) μ :=
    (iD.sub ix).sub (integrable_const _)
  have eI : ∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
      ((passiveTransmission b E X) ^ (k + 1)).trace.re) ∂μ =
      ∫ ω, brInc hT (k + 1) (U ω) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_trace_pow_fresh hb0 hb hW1 h1 h2 hX hT (k + 1)] with ω e1
    rw [e1, show ((passiveTransmission b E X) ^ (k + 1)).trace = ((sand hT 1) ^ (k + 1)).trace by
      rw [← trace_pow_sand hT 1 (k + 1), Matrix.mul_one]]
    rfl
  have eD : ∫ ω, brInc hT (k + 1) (U ω) ∂μ =
      ∫ ω, x ω ∂μ + bb + ∫ ω, (brInc hT (k + 1) (U ω) - x ω - bb) ∂μ := by
    have a1 := integral_sub (iD.sub ix) (integrable_const bb)
    have a2 := integral_sub iD ix
    simp only [Pi.sub_apply] at a1 a2
    rw [integral_const, probReal_univ, one_smul] at a1
    linarith
  have hRint : |∫ ω, (brInc hT (k + 1) (U ω) - x ω - bb) ∂μ| ≤ ∫ ω, F ω ∂μ := by
    rw [← Real.norm_eq_abs]; exact norm_integral_le_of_norm_le iF hpt
  have eF : ∫ ω, F ω ∂μ = ck * (t + (∫ ω, h ω ^ 2 ∂μ) / t + 2 * (ν ^ 2 * g)) := by
    have a1 := integral_add ((integrable_const t).add (hh.div_const t))
      (integrable_const (2 * (ν ^ 2 * g)))
    have a2 := integral_add (integrable_const t) (hh.div_const t)
    simp only [Pi.add_apply] at a1 a2
    simp only [F]
    rw [integral_const_mul, a1, a2, integral_const, integral_const, integral_div, probReal_univ,
      one_smul, one_smul]
  have hHt : (∫ ω, h ω ^ 2 ∂μ) / t ≤ t := by
    rw [div_le_iff₀ ht0]
    refine hH4.trans ?_
    have e : t * t = (C / Real.sqrt W * (g + 1)) ^ 4 := by
      rw [mul_pow, div_pow, show Real.sqrt W ^ 4 = (W : ℝ) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs2]]
      simp only [t]; field_simp
    rw [e]
    refine pow_le_pow_left₀ (by positivity) ?_ 4
    exact mul_le_mul (div_le_div_of_nonneg_right (by linarith) hs0.le) (by linarith) hg
      (by positivity)
  have hbb : |bb| ≤ Kk * (ν * g) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (Nat.cast_nonneg _)
    exact (norm_brLin_le hT ht1 (by omega) _).trans (mul_le_mul_of_nonneg_right hν hg)
  rw [eI, eD, ex, zero_add]
  have hck : 0 ≤ ck := by positivity
  calc |bb + ∫ ω, (brInc hT (k + 1) (U ω) - x ω - bb) ∂μ|
      ≤ |bb| + |∫ ω, (brInc hT (k + 1) (U ω) - x ω - bb) ∂μ| := abs_add_le _ _
    _ ≤ Kk * (ν * g) + ck * (t + t + 2 * (ν ^ 2 * g)) := by
        rw [eF] at hRint
        have := mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add_left hHt t)
          (2 * (ν ^ 2 * g))) hck
        linarith
    _ = Kk * (ν * g) + ck * (2 * (C ^ 2 * (g + 1) ^ 2 / W) + 2 * (ν ^ 2 * g)) := by ring
    _ ≤ _ := drift_rhs_le (Nat.cast_nonneg _) hck hCν hWr hY1 hg hg1Y hν0 hνY

end BlockBand.Transmission.Absorbed
