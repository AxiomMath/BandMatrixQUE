module

public import BlockBand.Transmission.Generator.BrFourLayer
public import BlockBand.Transmission.Absorbed.OneTime

/-!
# The absorbed modulus: one-layer fourth moment with a mixing-free majorant

**`modulusFour_layer_bulk hGA hLp`**: `Generator.fourth_layer_bulk` with the majorant
`brY` replaced by `Y' = (g+1)(Wδ₀+1)` (`g = Re Tr T(X)`, `δ₀ = jetDistance0`): `b ∈ (0,1/2)`,
`κ > 0`, `k` first; then `K ≥ 0, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ` and every passive `X`,
`E(Re Tr T(X₊)^{k+1} - Re Tr T(X)^{k+1})⁴ ≤ K·Y'¹²/W²`. The proof is that of
`Generator.fourth_layer_bulk`, except for the majorant: `br4_rhs_le` and `br_nu_le` use only
`1 ≤ Y`, `g ≤ Y` and `Wδ₀ ≤ Y`, so the mixing factor and `Wδ₁` of `brY` are not needed. The
moments of `Y'` along the absorbed path come from `absorbedConductance_bulk` and
`absorbedDeltaUniform_holds` (no absorbed mixing input).
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

/-- **The one-layer fourth moment with the majorant `Y' = (g+1)(Wδ₀+1)`**, bulk-uniform. -/
theorem modulusFour_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ∂freshLaw W b ≤
          K * ((((passiveTransmission b E X).trace.re + 1) * (W * jetDistance0 b E X + 1)) ^ 12 /
            (W : ℝ) ^ 2) := by
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨C8, W8, hC8, hm8⟩ := hs_moment8_bulk hA hb0 hb hκ
  obtain ⟨C4, W4, hC4, hm4⟩ := brLin_moment4_bulk hA hb0 hb hκ
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
  refine ⟨27 * (Kk ^ 4 * C4 ^ 4 + Kk ^ 4 * Cν ^ 4 + 128 * ck ^ 4 * (C8 ^ 8 + Cν ^ 8)),
    max (max W8 W4) (max Wu 1), by positivity, fun W hW E hE X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW8, hW4⟩, hWu, hW1⟩ := hW
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
  have hgY : g ≤ Y := by
    have : g + 1 ≤ Y := le_mul_of_one_le_right (by linarith) (by linarith)
    linarith
  have haY : (W : ℝ) * δ ≤ Y := by
    have : W * δ + 1 ≤ Y := le_mul_of_one_le_left (by linarith) (by linarith)
    linarith
  obtain ⟨hD0, hDC⟩ := transportD0_le_bulk hb0 (by linarith) hκ hE
  set U := freshU b E X
  set μ := freshLaw W b
  have hS := ae_norm_sand_freshU_le hb0 hb hW1 h1 h2 hX hT
  set ν := Cu * (δ + (W : ℝ)⁻¹ ^ 2 + q / W) + transportD0 b E * g / (2 * W)
  have hν : ‖matrixExpect μ U - 1‖ ≤ ν :=
    (norm_ubar_sub_one_le hb0 hb h1 h2 hD0 hX _).trans (by linarith [(hUB W hWu E hE X hX).1])
  have hν0 : 0 ≤ ν := add_nonneg (mul_nonneg hCu (add_nonneg (add_nonneg (norm_nonneg _)
    (by positivity)) (div_nonneg hq0 hWpos.le))) (div_nonneg (mul_nonneg hD0 hg) (by positivity))
  have hνY : ν ≤ Cν * Y / W := by
    have := br_nu_le hCu hWr hs2 haY hqg hcq hg hgY hY1 hD0 hDC
    rwa [hs2] at this
  obtain ⟨hh, hH8⟩ := hm8 W hW8 E hE X hX hT
  obtain ⟨hl, hL4⟩ := hm4 W hW4 E hE X hX hT k
  obtain ⟨-, hF⟩ := br_four hT ht1 U (measurable_freshU b E X) hS hν k hh hH8 hl hL4
  have eI : ∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
      ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ∂μ =
      ∫ ω, brInc hT (k + 1) (U ω) ^ 4 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_trace_pow_fresh hb0 hb hW1 h1 h2 hX hT (k + 1)] with ω e1
    rw [e1, show ((passiveTransmission b E X) ^ (k + 1)).trace = ((sand hT 1) ^ (k + 1)).trace by
      rw [← trace_pow_sand hT 1 (k + 1), Matrix.mul_one]]
    rfl
  rw [eI]
  exact hF.trans (br4_rhs_le (by positivity) hWr hs2 hY1 hg hgY hν0 hνY hCν)

end BlockBand.Transmission.Absorbed
