module

public import BlockBand.Transmission.Absorbed.ShiftMixW
public import BlockBand.Transmission.Absorbed.ShiftLayer
public import BlockBand.Transmission.LawForced.RatioP
public import BlockBand.Transmission.Generator.LayerBulk

/-!
# The majorant `ratioP` at the shifted input

**`ratioP_absorb_le`**: `ratioP(X − iε) ≤ cP·((g+1)²·(Wδ₀+1)·M₃·M₄)` at `X`, with
`M₃ = √W(‖Tr Qf‖ + hs(Q,f)) + 1`, `M₄ = Wδ₁ + 1` and `cP` depending on `b, κ_I, K` only
(`modY_absorb_le`, `mix_absorb_le`, `jetDistance1_absorb_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LawFinite
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawForced
open BlockBand.Transmission.PathScalar BlockBand.Transmission.Generator
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}
/-- `M₃ = √W(‖Tr Qf‖ + hs(Q, f)) + 1`. -/
def mixM3 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
    hsSandwich (passiveQ b E X) (passiveF b E X)) + 1

/-- The constant of `ratioP_absorb_le` (`L = η_L⁻¹`). -/
def cP (L K : ℝ) : ℝ :=
  ((1 + K * L) ^ 2 + 4 * K * L + 1) * (1 + K * L ^ 2) * (1 + cMix L K * (L / 4 + 1)) *
    (1 + 2 * K * L ^ 3)

theorem cMix_nonneg {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) : 0 ≤ cMix L K := by
  unfold cMix; positivity

theorem absorb_s_le_one {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI) {K : ℝ}
    (hK : 0 ≤ K) {E : ℝ} (hE : E ∈ bulkInterval κI) (hW1 : 1 ≤ W)
    (hWK : K * (etaLow b κI)⁻¹ ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (_hY : (passiveY X).PosSemidef) {ε : ℝ} (_hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2) :
    ε / etaZ b E ≤ 1 := by
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hηL := etaLow_pos hb1 hκI
  have hηle := etaLow_le hb1 hκI hE
  have hL0 : 0 ≤ (etaLow b κI)⁻¹ := by positivity
  have hιL : (etaZ b E)⁻¹ ≤ (etaLow b κI)⁻¹ := inv_anti₀ hηL hηle
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have a : ε / etaZ b E ≤ K / (W : ℝ) ^ 2 * (etaLow b κI)⁻¹ := by
    rw [div_eq_mul_inv]; exact mul_le_mul hεK hιL (by positivity) (by positivity)
  have b' : K / (W : ℝ) ^ 2 * (etaLow b κI)⁻¹ ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith
  linarith

theorem absorb_modY_factor {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI) {K : ℝ}
    (hK : 0 ≤ K) {E : ℝ} (hE : E ∈ bulkInterval κI) (hW1 : 1 ≤ W)
    (_hWK : K * (etaLow b κI)⁻¹ ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2) :
    modY b E (absorbedInput X ε) ≤ ((1 + K * (etaLow b κI)⁻¹) ^ 2 + 4 * K * (etaLow b κI)⁻¹ + 1) *
      (1 + K * (etaLow b κI)⁻¹ ^ 2) * modY b E X := by
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hηL := etaLow_pos hb1 hκI
  have hηle := etaLow_le hb1 hκI hE
  have hL0 : 0 ≤ (etaLow b κI)⁻¹ := by positivity
  have hιL : (etaZ b E)⁻¹ ≤ (etaLow b κI)⁻¹ := inv_anti₀ hηL hηle
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hg0 := (mm_trace_posSemidef (passiveTransmission_posSemidef hb1 h1 h2 hY)).1
  set L := (etaLow b κI)⁻¹
  have hY1 := modY_absorb_le hb0 hb h1 h2 hK hε hεK hW1 hY
  have hKη : K / etaZ b E ≤ K * L := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hιL hK
  have hKη2 : K / etaZ b E ^ 2 ≤ K * L ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hιL 2) hK
  have hcY : ((1 + K / etaZ b E) ^ 2 + 4 * K / etaZ b E + 1) * (1 + K / etaZ b E ^ 2) ≤
      ((1 + K * L) ^ 2 + 4 * K * L + 1) * (1 + K * L ^ 2) := by
    have a0 : 0 ≤ K / etaZ b E := by positivity
    have a1 : (1 + K / etaZ b E) ^ 2 ≤ (1 + K * L) ^ 2 := pow_le_pow_left₀ (by positivity)
      (by linarith) 2
    have a2 : 4 * K / etaZ b E ≤ 4 * K * L := by
      rw [mul_div_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left hKη (by norm_num)
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hmY0 : 0 ≤ modY b E X := by
    unfold modY; have := mul_nonneg hW0.le (norm_nonneg ((W : ℂ)⁻¹ *
      (passiveResolvent b E X).trace - matchedA E))
    unfold jetDistance0; positivity
  have hYf := hY1.trans (mul_le_mul_of_nonneg_right hcY hmY0)
  exact hYf

theorem absorb_M3_factor {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI) {K : ℝ}
    (hK : 0 ≤ K) {E : ℝ} (hE : E ∈ bulkInterval κI) (hW1 : 1 ≤ W)
    (hWK : K * (etaLow b κI)⁻¹ ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2) :
    mixM3 b E (absorbedInput X ε) ≤ (1 + cMix (etaLow b κI)⁻¹ K * ((etaLow b κI)⁻¹ / 4 + 1)) *
      mixM3 b E X * ((passiveTransmission b E X).trace.re + 1) := by
  have hs1 := absorb_s_le_one hb0 hb hκI hK hE hW1 hWK hY hε hεK
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hηL := etaLow_pos hb1 hκI
  have hηle := etaLow_le hb1 hκI hE
  have hL0 : 0 ≤ (etaLow b κI)⁻¹ := by positivity
  have hιL : (etaZ b E)⁻¹ ≤ (etaLow b κI)⁻¹ := inv_anti₀ hηL hηle
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set L := (etaLow b κI)⁻¹
  have hg0 := (mm_trace_posSemidef (passiveTransmission_posSemidef hb1 h1 h2 hY)).1
  set g := (passiveTransmission b E X).trace.re
  have hq := mass_le_bulk hb1 hκI hE hY
  have hq0 := passiveMass_nonneg b E hY
  have hm := mix_absorb_le hb0 hb h1 h2 hY hε
  have hsm := sqrtW_mixErr_le hη hιL hK hW1 hε hεK hs1 hq0
  have hqg : passiveMass b E X + 1 ≤ (L / 4 + 1) * (g + 1) := by
    have : (4 * etaLow b κI)⁻¹ = L / 4 := by rw [mul_inv]; ring
    rw [this] at hq; nlinarith
  have hM1 : 1 ≤ mixM3 b E X := by
    unfold mixM3
    have := mul_nonneg (Real.sqrt_nonneg (W : ℝ)) (add_nonneg (norm_nonneg
      (passiveQ b E X * passiveF b E X).trace) (Real.sqrt_nonneg
        ((passiveQ b E X) * passiveF b E X * passiveQ b E X * (passiveF b E X)ᴴ).trace.re))
    unfold hsSandwich; linarith
  have hc := cMix_nonneg hL0 hK
  have t : mixM3 b E (absorbedInput X ε) ≤ mixM3 b E X + cMix L K * ((L / 4 + 1) * (g + 1)) := by
    unfold mixM3
    have := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg (W : ℝ))
    have := mul_le_mul_of_nonneg_left hqg hc
    linarith
  have : mixM3 b E X + cMix L K * ((L / 4 + 1) * (g + 1)) ≤
      (1 + cMix L K * (L / 4 + 1)) * mixM3 b E X * (g + 1) := by
    have e : (1 + cMix L K * (L / 4 + 1)) * mixM3 b E X * (g + 1) =
        mixM3 b E X * (g + 1) + cMix L K * (L / 4 + 1) * (mixM3 b E X * (g + 1)) := by ring
    rw [e]
    have k1 : mixM3 b E X ≤ mixM3 b E X * (g + 1) := le_mul_of_one_le_right (by linarith)
      (by linarith)
    have k2 : g + 1 ≤ mixM3 b E X * (g + 1) := le_mul_of_one_le_left (by linarith) hM1
    have := mul_le_mul_of_nonneg_left k2 (by positivity : (0 : ℝ) ≤ cMix L K * (L / 4 + 1))
    linarith
  linarith

theorem absorb_M4_factor {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI) {K : ℝ}
    (hK : 0 ≤ K) {E : ℝ} (hE : E ∈ bulkInterval κI) (hW1 : 1 ≤ W)
    (_hWK : K * (etaLow b κI)⁻¹ ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2) (s : ℂ) :
    (W : ℝ) * jetDistance1 b E s (absorbedInput X ε) + 1 ≤
      (1 + 2 * K * (etaLow b κI)⁻¹ ^ 3) * ((W : ℝ) * jetDistance1 b E s X + 1) := by
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hηL := etaLow_pos hb1 hκI
  have hηle := etaLow_le hb1 hκI hE
  have hL0 : 0 ≤ (etaLow b κI)⁻¹ := by positivity
  have hιL : (etaZ b E)⁻¹ ≤ (etaLow b κI)⁻¹ := inv_anti₀ hηL hηle
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set L := (etaLow b κI)⁻¹
  have hj := jetDistance1_absorb_le hb0 hb h1 h2 hY hε s
  have hj0 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have k : (W : ℝ) * (2 * ε / etaZ b E ^ 3) ≤ 2 * K * L ^ 3 := by
    have hεW : (W : ℝ) * ε ≤ K := by
      have := mul_le_mul_of_nonneg_left hεK hW0.le
      have e : (W : ℝ) * (K / (W : ℝ) ^ 2) = K / W := by field_simp
      rw [e] at this
      exact this.trans (div_le_self hK hWr)
    have e : (W : ℝ) * (2 * ε / etaZ b E ^ 3) = 2 * ((W : ℝ) * ε) * (etaZ b E)⁻¹ ^ 3 := by
      field_simp
    rw [e]
    have := pow_le_pow_left₀ (by positivity) hιL 3
    have := mul_le_mul (mul_le_mul_of_nonneg_left hεW (by norm_num : (0 : ℝ) ≤ 2)) this
      (by positivity) (by positivity)
    linarith
  have := mul_le_mul_of_nonneg_left hj hW0.le
  have k2 : 2 * K * L ^ 3 ≤ 2 * K * L ^ 3 * ((W : ℝ) * jetDistance1 b E s X + 1) :=
    le_mul_of_one_le_right (by positivity) (by nlinarith)
  nlinarith

/-- **The majorant `ratioP` at the shifted input.** -/
theorem ratioP_absorb_le {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI) {K : ℝ}
    (hK : 0 ≤ K) {E : ℝ} (hE : E ∈ bulkInterval κI) (hW1 : 1 ≤ W)
    (hWK : K * (etaLow b κI)⁻¹ ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2) (s : ℂ) :
    ratioP b E s (absorbedInput X ε) ≤ cP (etaLow b κI)⁻¹ K *
      (((passiveTransmission b E X).trace.re + 1) ^ 2 * (W * jetDistance0 b E X + 1) *
        mixM3 b E X * (W * jetDistance1 b E s X + 1)) := by
  have hYf := absorb_modY_factor hb0 hb hκI hK hE hW1 hWK hY hε hεK
  have hM3 := absorb_M3_factor hb0 hb hκI hK hE hW1 hWK hY hε hεK
  have hM4 := absorb_M4_factor hb0 hb hκI hK hE hW1 hWK hY hε hεK s
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hηL := etaLow_pos hb1 hκI
  have hηle := etaLow_le hb1 hκI hE
  have hL0 : 0 ≤ (etaLow b κI)⁻¹ := by positivity
  have hιL : (etaZ b E)⁻¹ ≤ (etaLow b κI)⁻¹ := inv_anti₀ hηL hηle
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hY' := passiveY_absorbedInput hY hε
  have hg0 := (mm_trace_posSemidef (passiveTransmission_posSemidef hb1 h1 h2 hY)).1
  -- assemble
  have e : ratioP b E s (absorbedInput X ε) = modY b E (absorbedInput X ε) *
      mixM3 b E (absorbedInput X ε) * ((W : ℝ) * jetDistance1 b E s (absorbedInput X ε) + 1) := rfl
  rw [e]
  have hmY'0 : 0 ≤ modY b E (absorbedInput X ε) := by
    unfold modY
    have := (mm_trace_posSemidef (passiveTransmission_posSemidef hb1 h1 h2 hY')).1
    have := mul_nonneg hW0.le (norm_nonneg ((W : ℂ)⁻¹ *
      (passiveResolvent b E (absorbedInput X ε)).trace - matchedA E))
    unfold jetDistance0; positivity
  have hM3'0 : 0 ≤ mixM3 b E (absorbedInput X ε) := by
    unfold mixM3 hsSandwich; positivity
  have hJ'0 : 0 ≤ (W : ℝ) * jetDistance1 b E s (absorbedInput X ε) + 1 := by
    have := mul_nonneg hW0.le (norm_nonneg (deriv (fun w : ℂ => (W : ℂ)⁻¹ *
      ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - absorbedInput X ε)⁻¹).trace) (boundaryZ b E) - s))
    unfold jetDistance1; linarith
  have hmY0 : 0 ≤ modY b E X := by
    unfold modY
    have := mul_nonneg hW0.le (norm_nonneg ((W : ℂ)⁻¹ *
      (passiveResolvent b E X).trace - matchedA E))
    unfold jetDistance0; positivity
  have hM30 : 0 ≤ mixM3 b E X := by unfold mixM3 hsSandwich; positivity
  have hc := cMix_nonneg hL0 hK
  have hcY : 0 ≤ ((1 + K * (etaLow b κI)⁻¹) ^ 2 + 4 * K * (etaLow b κI)⁻¹ + 1) *
      (1 + K * (etaLow b κI)⁻¹ ^ 2) := by positivity
  have s1 := mul_le_mul hYf hM3 hM3'0 (mul_nonneg hcY hmY0)
  have s2 := mul_le_mul s1 hM4 hJ'0 (mul_nonneg (mul_nonneg hcY hmY0)
    (mul_nonneg (mul_nonneg (by positivity) hM30) (by linarith)))
  refine s2.trans (le_of_eq ?_)
  unfold cP modY
  ring

end BlockBand.Transmission.Absorbed
