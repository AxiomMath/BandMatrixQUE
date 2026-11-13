module

public import BlockBand.Transmission.Generator.BrFourBulk

/-!
# One-layer fourth moment of the increment, bulk-uniform: the theorem

**`fourth_layer_bulk hGA hLp`**: `b ∈ (0,1/2)`, `κ > 0`, `k` first; then `K ≥ 0, W₀`; for
`W ≥ W₀`, `E ∈ bulkInterval κ`, every `s : ℂ` and every passive `X`:
`E(Re Tr T(X₊)^{k+1} - Re Tr T^{k+1})⁴ ≤ K·brY¹²/W²` (`brY` as in `BrBulk`). From `br_four`,
`brLin_moment4_bulk`, `hs_moment8_bulk`, `ubarMean_bulk` (a) and `br4_rhs_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PathScalar
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

theorem br_mono' {Y s : ℝ} (hY : 1 ≤ Y) (hs : 1 ≤ s) {j m p q : ℕ} (hj : j ≤ m) (hp : q ≤ p) :
    Y ^ j / s ^ p ≤ Y ^ m / s ^ q := by
  have hs0 : 0 < s := by linarith
  calc Y ^ j / s ^ p ≤ Y ^ m / s ^ p :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ hY hj) (by positivity)
    _ ≤ Y ^ m / s ^ q :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hs hp)

/-- **Bookkeeping of the fourth moment.** -/
theorem br4_rhs_le {K c Wr s g Y ν C4 C8 Cν : ℝ} (hK : 0 ≤ K) (hWr : 1 ≤ Wr)
    (hs2 : s ^ 2 = Wr) (hY : 1 ≤ Y) (hg0 : 0 ≤ g) (hgY : g ≤ Y) (hν0 : 0 ≤ ν)
    (hν : ν ≤ Cν * Y / Wr) (hCν : 0 ≤ Cν) :
    27 * (K ^ 4 * (C4 / s * g) ^ 4 + (K * (ν * g)) ^ 4 +
        128 * c ^ 4 * ((C8 / s * g) ^ 8 + (ν ^ 2 * g) ^ 4)) ≤
      27 * (K ^ 4 * C4 ^ 4 + K ^ 4 * Cν ^ 4 + 128 * c ^ 4 * (C8 ^ 8 + Cν ^ 8)) *
        (Y ^ 12 / Wr ^ 2) := by
  have hW0 : 0 < Wr := by linarith
  set X := Y ^ 12 / Wr ^ 2
  have s4 : s ^ 4 = Wr ^ 2 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]
  have s8 : s ^ 8 = Wr ^ 4 := by rw [show s ^ 8 = (s ^ 2) ^ 4 by ring, hs2]
  have a1 : (C4 / s * g) ^ 4 ≤ C4 ^ 4 * X := by
    calc (C4 / s * g) ^ 4 = C4 ^ 4 * (g ^ 4 / Wr ^ 2) := by
          rw [div_mul_eq_mul_div, div_pow, mul_pow, s4]; ring
      _ ≤ C4 ^ 4 * (Y ^ 4 / Wr ^ 2) := by gcongr
      _ ≤ C4 ^ 4 * X := by gcongr; exact br_mono' hY hWr (by norm_num) le_rfl
  have hνg : ν * g ≤ Cν * (Y ^ 2 / Wr) := by
    calc ν * g ≤ Cν * Y / Wr * Y := mul_le_mul hν hgY hg0 (by positivity)
      _ = _ := by ring
  have a2 : (K * (ν * g)) ^ 4 ≤ K ^ 4 * Cν ^ 4 * X := by
    calc (K * (ν * g)) ^ 4 ≤ (K * (Cν * (Y ^ 2 / Wr))) ^ 4 := by gcongr
      _ = K ^ 4 * Cν ^ 4 * (Y ^ 8 / Wr ^ 4) := by field_simp
      _ ≤ _ := by gcongr; exact br_mono' hY hWr (by norm_num) (by norm_num)
  have a3 : (C8 / s * g) ^ 8 ≤ C8 ^ 8 * X := by
    calc (C8 / s * g) ^ 8 = C8 ^ 8 * (g ^ 8 / Wr ^ 4) := by
          rw [div_mul_eq_mul_div, div_pow, mul_pow, s8]; ring
      _ ≤ C8 ^ 8 * (Y ^ 8 / Wr ^ 4) := by gcongr
      _ ≤ C8 ^ 8 * X := by gcongr; exact br_mono' hY hWr (by norm_num) (by norm_num)
  have hν2g : ν ^ 2 * g ≤ Cν ^ 2 * (Y ^ 3 / Wr ^ 2) := by
    calc ν ^ 2 * g ≤ (Cν * Y / Wr) ^ 2 * Y :=
          mul_le_mul (pow_le_pow_left₀ hν0 hν 2) hgY hg0 (by positivity)
      _ = _ := by field_simp
  have a4 : (ν ^ 2 * g) ^ 4 ≤ Cν ^ 8 * X := by
    calc (ν ^ 2 * g) ^ 4 ≤ (Cν ^ 2 * (Y ^ 3 / Wr ^ 2)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hν2g 4
      _ = Cν ^ 8 * (Y ^ 12 / Wr ^ 8) := by field_simp
      _ ≤ _ := by gcongr; exact br_mono' hY hWr le_rfl (by norm_num)
  have c4 : 0 ≤ 128 * c ^ 4 := by positivity
  have b1 := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ K ^ 4)
  have b2 := mul_le_mul_of_nonneg_left (add_le_add a3 a4) c4
  have e : 27 * (K ^ 4 * C4 ^ 4 + K ^ 4 * Cν ^ 4 + 128 * c ^ 4 * (C8 ^ 8 + Cν ^ 8)) * X =
      27 * (K ^ 4 * (C4 ^ 4 * X) + K ^ 4 * Cν ^ 4 * X + 128 * c ^ 4 * (C8 ^ 8 * X + Cν ^ 8 * X)) := by
    ring
  rw [e]
  linarith

/-- **The one-layer fourth moment, bulk-uniform.** -/
theorem fourth_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ∂freshLaw W b ≤
          K * (brY b E s X ^ 12 / (W : ℝ) ^ 2) := by
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
    max (max W8 W4) (max Wu 1), by positivity, fun W hW E hE s X hX => ?_⟩
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
  have ht : 0 ≤ Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      hsSandwich (passiveQ b E X) (passiveF b E X)) :=
    mul_nonneg hs0.le (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hd : 0 ≤ (W : ℝ) * jetDistance1 b E s X := mul_nonneg hWpos.le (norm_nonneg _)
  obtain ⟨hY1, hgY, haY, -, -, -⟩ := brY_ge hg ha ht hd
  set Y := brY b E s X
  have hYe : Y = (g + 1) * (W * δ + 1) * (Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      hsSandwich (passiveQ b E X) (passiveF b E X)) + 1) * (W * jetDistance1 b E s X + 1) := rfl
  rw [← hYe] at hY1 hgY haY
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

end BlockBand.Transmission.Generator
