module

public import BlockBand.Transmission.Absorbed.ShiftTrace
public import BlockBand.Transmission.Absorbed.ModulusDrift

/-!
# The absorbed modulus: one fresh layer at the shifted input

The absorbed step is `X ↦ freshSchur E (X - iε) y`, `0 ≤ ε ≤ K_ε/W²`. At fixed `b, E` and every
passive `X`, with the majorant `Y'(X) = (g+1)(Wδ₀+1)` (`modY`) taken at the *unshifted* `X`:
* `modY_absorb_le`: `Y'(X - iε) ≤ c_Y Y'(X)` (`passiveMass_absorb_le`,
  `jetDistance0_absorb_le`);
* **`shiftFour_layer`**: `E(Re Tr T(freshSchur(X - iε))^{k+1} - Re Tr T(X)^{k+1})⁴ ≤ K·Y'¹²/W²`;
* **`shiftDrift_layer`**: `|E(Re Tr T(freshSchur(X - iε))^{k+1} - Re Tr T(X)^{k+1})| ≤ K·Y'³/W`.

Proof: the increment is the passive one-layer increment at `X - iε` (`modulusFour_layer_bulk`,
`modulusDrift_layer_bulk`) plus the deterministic shift `d` (`abs_powerTrace_shift_le_div`,
`|d| ≤ c(g+1)/W`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LawFinite
open BlockBand.Transmission.Generator
open scoped ComplexOrder

variable {W : ℕ}

/-- The mixing-free majorant `Y'(X) = (g+1)(Wδ₀+1)`. -/
def modY (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ((passiveTransmission b E X).trace.re + 1) * (W * jetDistance0 b E X + 1)

theorem measurable_modY (b E : ℝ) : Measurable (modY (W := W) b E) := by
  have h1 := measurable_trace_pow_transmission (W := W) b E 1
  simp only [pow_one] at h1
  exact (h1.add_const 1).mul (((PathScalar.measurable_jetDistance0 b E).const_mul _).add_const 1)

theorem add_pow_four_le (a d : ℝ) : (a + d) ^ 4 ≤ 8 * (a ^ 4 + d ^ 4) := by
  have h : (a + d) ^ 2 ≤ 2 * (a ^ 2 + d ^ 2) := by nlinarith [sq_nonneg (a - d)]
  have h' : (a ^ 2 + d ^ 2) ^ 2 ≤ 2 * (a ^ 4 + d ^ 4) := by nlinarith [sq_nonneg (a ^ 2 - d ^ 2)]
  calc (a + d) ^ 4 = ((a + d) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (a ^ 2 + d ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h 2
    _ = 4 * (a ^ 2 + d ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * (a ^ 4 + d ^ 4)) := by linarith
    _ = _ := by ring

/-- The shift part: `|d| ≤ c(g+1)/W` gives `d⁴ ≤ c⁴Y¹²/W²` and `|d| ≤ cY³/W`. -/
theorem shift_pow_le {d c g Y Wr : ℝ} (hc : 0 ≤ c) (hWr : 1 ≤ Wr) (hg : 0 ≤ g) (hgY : g + 1 ≤ Y)
    (hd : |d| ≤ c * (g + 1) / Wr) :
    d ^ 4 ≤ c ^ 4 * (Y ^ 12 / Wr ^ 2) ∧ |d| ≤ c * (Y ^ 3 / Wr) := by
  have hW0 : 0 < Wr := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hY3 : g + 1 ≤ Y ^ 3 := hgY.trans (le_self_pow₀ hY1 (by norm_num))
  have h3 : |d| ≤ c * (Y ^ 3 / Wr) := by
    rw [mul_div_assoc'] ; exact hd.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hY3 hc) hW0.le)
  refine ⟨?_, h3⟩
  have h4 : d ^ 4 ≤ (c * (Y ^ 3 / Wr)) ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg d) h3 4
    rwa [show |d| ^ 4 = d ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
      at this
  have e : (c * (Y ^ 3 / Wr)) ^ 4 = c ^ 4 * (Y ^ 12 / Wr ^ 4) := by ring
  have hW4 : Wr ^ 2 ≤ Wr ^ 4 := pow_le_pow_right₀ hWr (by norm_num)
  have h5 : Y ^ 12 / Wr ^ 4 ≤ Y ^ 12 / Wr ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hW4
  calc d ^ 4 ≤ _ := h4
    _ = _ := e
    _ ≤ _ := mul_le_mul_of_nonneg_left h5 (by positivity)

/-- The passive one-layer increment `Re Tr T(X₊)^k - Re Tr T(X)^k` at input `X`. -/
def freshIncAt (b E : ℝ) (k : ℕ) (X : Matrix (Fin W) (Fin W) ℂ)
    (y : LayerSample W .oneBlockOnePort) : ℝ :=
  ((passiveTransmission b E (freshSchur E X y)) ^ k).trace.re -
    ((passiveTransmission b E X) ^ k).trace.re

theorem four_combine {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} {d A B : ℝ} (iF : Integrable (fun y => F y ^ 4) μ) (hF : ∫ y, F y ^ 4 ∂μ ≤ A)
    (hd : d ^ 4 ≤ B) : ∫ y, (F y + d) ^ 4 ∂μ ≤ 8 * (A + B) := by
  have i8 : Integrable (fun y => 8 * (F y ^ 4 + d ^ 4)) μ := (iF.add (integrable_const _)).const_mul 8
  refine (integral_mono_of_nonneg (ae_of_all _ fun y => by positivity) i8
    (ae_of_all _ fun y => add_pow_four_le (F y) d)).trans ?_
  rw [integral_const_mul, integral_add iF (integrable_const _), integral_const, probReal_univ,
    one_smul]
  linarith

theorem drift_combine {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : Ω → ℝ} {d A B : ℝ} (iF : Integrable F μ) (hF : |∫ y, F y ∂μ| ≤ A) (hd : |d| ≤ B) :
    |∫ y, (F y + d) ∂μ| ≤ A + B := by
  rw [integral_add iF (integrable_const _), integral_const, probReal_univ, one_smul]
  exact (abs_add_le _ _).trans (add_le_add hF hd)

section Fixed

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
include hb0 hb h1 h2

theorem modY_ge {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    1 ≤ modY b E X ∧ (passiveTransmission b E X).trace.re + 1 ≤ modY b E X := by
  have hg : 0 ≤ (passiveTransmission b E X).trace.re :=
    (SourceMixing.mm_trace_posSemidef (passiveTransmission_posSemidef (by linarith) h1 h2 hX)).1
  have ha : 0 ≤ (W : ℝ) * jetDistance0 b E X := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have : (passiveTransmission b E X).trace.re + 1 ≤ modY b E X :=
    le_mul_of_one_le_right (by linarith) (by linarith)
  exact ⟨by linarith, this⟩

/-- **`Y'(X - iε) ≤ c_Y Y'(X)`** for `0 ≤ ε ≤ K/W²`, `W ≥ 1`. -/
theorem modY_absorb_le {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) (hεK : ε ≤ K / (W : ℝ) ^ 2)
    (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    modY b E (absorbedInput X ε) ≤
      ((1 + K / etaZ b E) ^ 2 + 4 * K / etaZ b E + 1) * (1 + K / etaZ b E ^ 2) * modY b E X := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hεW : ε * W ≤ K := by
    have : ε * (W : ℝ) ^ 2 ≤ K := by rwa [le_div_iff₀ (by positivity)] at hεK
    nlinarith
  have hε1 : ε ≤ K := by nlinarith
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  have eg : ∀ Z : Matrix (Fin W) (Fin W) ℂ,
      (passiveTransmission b E Z).trace.re = 4 * etaZ b E * passiveMass b E Z := fun Z => by
    rw [passiveTransmission, trace_smul, passiveMass, smul_eq_mul, Complex.re_ofReal_mul]
  set g := (passiveTransmission b E X).trace.re
  have hg : 0 ≤ g := (SourceMixing.mm_trace_posSemidef
    (passiveTransmission_posSemidef (by linarith) h1 h2 hX)).1
  -- the conductance factor
  have hq := passiveMass_absorb_le hb0 hb h1 h2 hX hε
  have hs : ε / etaZ b E ≤ K / etaZ b E := div_le_div_of_nonneg_right hε1 hη.le
  have hg' : (passiveTransmission b E (absorbedInput X ε)).trace.re ≤
      (1 + K / etaZ b E) ^ 2 * g + 4 * K / etaZ b E := by
    rw [eg, show g = 4 * etaZ b E * passiveMass b E X from eg X]
    have a1 : (1 + ε / etaZ b E) ^ 2 ≤ (1 + K / etaZ b E) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have a2 : 4 * etaZ b E * (ε * W / etaZ b E ^ 2) ≤ 4 * K / etaZ b E := by
      rw [show 4 * etaZ b E * (ε * W / etaZ b E ^ 2) = 4 * (ε * W) / etaZ b E by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hη.le
    have hq0 : 0 ≤ passiveMass b E X := passiveMass_nonneg b E hX
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 4 * etaZ b E)
    have a3 : 4 * etaZ b E * ((1 + ε / etaZ b E) ^ 2 * passiveMass b E X) ≤
        (1 + K / etaZ b E) ^ 2 * (4 * etaZ b E * passiveMass b E X) := by
      rw [show 4 * etaZ b E * ((1 + ε / etaZ b E) ^ 2 * passiveMass b E X) =
        (1 + ε / etaZ b E) ^ 2 * (4 * etaZ b E * passiveMass b E X) by ring]
      exact mul_le_mul_of_nonneg_right a1 (by positivity)
    nlinarith
  have hG : (passiveTransmission b E (absorbedInput X ε)).trace.re + 1 ≤
      ((1 + K / etaZ b E) ^ 2 + 4 * K / etaZ b E + 1) * (g + 1) := by
    have : 0 ≤ 4 * K / etaZ b E := by positivity
    nlinarith [sq_nonneg (1 + K / etaZ b E)]
  -- the jet factor
  have hd := PathScalar.jetDistance0_absorb_le hb0 hb h1 h2 hX hε
  have hD : (W : ℝ) * jetDistance0 b E (absorbedInput X ε) + 1 ≤
      (1 + K / etaZ b E ^ 2) * (W * jetDistance0 b E X + 1) := by
    have e : absorbedInput X ε = X - (((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ) :=
      rfl
    rw [e]
    have a1 : (W : ℝ) * (ε / etaZ b E ^ 2) ≤ K / etaZ b E ^ 2 := by
      rw [mul_div_assoc', mul_comm]; exact div_le_div_of_nonneg_right hεW (by positivity)
    have a0 : 0 ≤ (W : ℝ) * jetDistance0 b E X := mul_nonneg hW0.le (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left hd hW0.le
    have : 0 ≤ K / etaZ b E ^ 2 := by positivity
    nlinarith
  have hD0 : 0 ≤ (W : ℝ) * jetDistance0 b E (absorbedInput X ε) + 1 := by
    have := mul_nonneg hW0.le (norm_nonneg ((W : ℂ)⁻¹ *
      (passiveResolvent b E (absorbedInput X ε)).trace - matchedA E))
    rw [jetDistance0]; linarith
  have hG0 : 0 ≤ (passiveTransmission b E (absorbedInput X ε)).trace.re + 1 := by
    have := (SourceMixing.mm_trace_posSemidef
      (passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX')).1
    linarith
  calc modY b E (absorbedInput X ε)
      ≤ (((1 + K / etaZ b E) ^ 2 + 4 * K / etaZ b E + 1) * (g + 1)) * ((1 + K / etaZ b E ^ 2) *
          (W * jetDistance0 b E X + 1)) := mul_le_mul hG hD hD0 (by positivity)
    _ = _ := by simp only [modY, g]; ring

/-- The fresh increment at the shifted input is measurable and a.s. bounded by `W`. -/
theorem fresh_inc_facts {ε : ℝ} (hε : 0 ≤ ε) (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) (k : ℕ) :
    Measurable (freshIncAt b E (k + 1) (absorbedInput X ε)) ∧
    ∀ᵐ y ∂freshLaw W b, |freshIncAt b E (k + 1) (absorbedInput X ε) y| ≤ W := by
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  refine ⟨((measurable_trace_pow_transmission b E (k + 1)).comp
    ((SourceMixing.measurable_freshSchur_prod E).comp
      (measurable_const.prodMk measurable_id))).sub_const _, ?_⟩
  filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
  have hY := PathScalar.passiveY_freshSchur E hX' y hy.1
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hY (by omega : 1 ≤ k + 1)
  obtain ⟨c0, c1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hX' (by omega : 1 ≤ k + 1)
  rw [freshIncAt, abs_le]; constructor <;> linarith

/-- The scalar facts at one passive input: `Y'(X') ≤ c_Y Y'(X)` and the shift bound. -/
theorem shift_scalars {Kε : ℝ} (hKε : 0 ≤ Kε) (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hεK : ε ≤ Kε / (W : ℝ) ^ 2) (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) :
    0 ≤ modY b E (absorbedInput X ε) ∧
    modY b E (absorbedInput X ε) ≤
      ((1 + Kε / etaZ b E) ^ 2 + 4 * Kε / etaZ b E + 1) * (1 + Kε / etaZ b E ^ 2) * modY b E X ∧
    1 ≤ modY b E X ∧
    (((passiveTransmission b E (absorbedInput X ε)) ^ (k + 1)).trace.re -
        ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ≤
      (((k + 1 : ℕ) : ℝ) * ((Kε / etaZ b E) * (2 + Kε / etaZ b E) + 4 * Kε / etaZ b E)) ^ 4 *
        (modY b E X ^ 12 / (W : ℝ) ^ 2) ∧
    |((passiveTransmission b E (absorbedInput X ε)) ^ (k + 1)).trace.re -
        ((passiveTransmission b E X) ^ (k + 1)).trace.re| ≤
      ((k + 1 : ℕ) : ℝ) * ((Kε / etaZ b E) * (2 + Kε / etaZ b E) + 4 * Kε / etaZ b E) *
        (modY b E X ^ 3 / W) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  obtain ⟨hY1, hgY⟩ := modY_ge hb0 hb h1 h2 hX
  have hg : 0 ≤ (passiveTransmission b E X).trace.re :=
    (SourceMixing.mm_trace_posSemidef (passiveTransmission_posSemidef (b := b) (by linarith)
      h1 h2 hX)).1
  have hd := abs_powerTrace_shift_le_div hb0 hb h1 h2 hX hKε hε hεK hW1 (k + 1)
  have hcK : 0 ≤ ((k + 1 : ℕ) : ℝ) * ((Kε / etaZ b E) * (2 + Kε / etaZ b E) + 4 * Kε / etaZ b E) :=
    by positivity
  obtain ⟨hd4, hd3⟩ := shift_pow_le hcK hWr hg hgY hd
  exact ⟨by linarith [(modY_ge hb0 hb h1 h2 hX').1], modY_absorb_le hb0 hb h1 h2 hKε hε hεK hW1 hX,
    hY1, hd4, hd3⟩

/-- **The fourth moment of one absorbed step at a passive input.** -/
theorem shiftFour_layer (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {Kε : ℝ}
    (hKε : 0 ≤ Kε) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        ∫ y, (((passiveTransmission b E (freshSchur E (absorbedInput X ε) y)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ^ 4 ∂freshLaw W b ≤
          K * (modY b E X ^ 12 / (W : ℝ) ^ 2) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨K4, W4, hK4, h4⟩ := modulusFour_layer_bulk hGA hLp hb0 hb hκ k
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨cY, hcY, hcYd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((1 + Kε / etaZ b E) ^ 2 + 4 * Kε / etaZ b E + 1) *
      (1 + Kε / etaZ b E ^ 2) := ⟨_, by positivity, rfl⟩
  obtain ⟨cK, hcK, hcKd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((k + 1 : ℕ) : ℝ) * ((Kε / etaZ b E) *
      (2 + Kε / etaZ b E) + 4 * Kε / etaZ b E) := ⟨_, by positivity, rfl⟩
  refine ⟨8 * (K4 * cY ^ 12 + cK ^ 4), max W4 1, by positivity, fun W hW X hX ε hε hεK => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  obtain ⟨hFm, hFb⟩ := fresh_inc_facts hb0 hb h1 h2 hε hW1 hX k
  obtain ⟨hYa0, hYa, -, hd4, -⟩ := shift_scalars hb0 hb h1 h2 hKε k hε hεK hW1 hX
  rw [← hcYd] at hYa
  rw [← hcKd] at hd4
  have iF : Integrable (fun y => freshIncAt b E (k + 1) (absorbedInput X ε) y ^ 4)
      (freshLaw W b) := by
    refine Integrable.of_bound (hFm.pow_const 4).aestronglyMeasurable ((W : ℝ) ^ 4) ?_
    filter_upwards [hFb] with y hy
    rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hy 4
  have hF4 : ∫ y, freshIncAt b E (k + 1) (absorbedInput X ε) y ^ 4 ∂freshLaw W b ≤
      K4 * (modY b E (absorbedInput X ε) ^ 12 / (W : ℝ) ^ 2) :=
    h4 W (le_of_max_le_left hW) E (PassiveLayer.mem_bulkInterval_min E) _ hX'
  have hY12 : modY b E (absorbedInput X ε) ^ 12 ≤ cY ^ 12 * modY b E X ^ 12 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hYa0 hYa 12
  have a1 : K4 * (modY b E (absorbedInput X ε) ^ 12 / (W : ℝ) ^ 2) ≤
      K4 * cY ^ 12 * (modY b E X ^ 12 / (W : ℝ) ^ 2) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hK4
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hY12 (by positivity)
  have key := four_combine iF (hF4.trans a1) hd4
  refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun y => ?_))) (key.trans_eq (by ring))
  simp only [freshIncAt]; ring

/-- **The conditional mean of one absorbed step at a passive input.** -/
theorem shiftDrift_layer (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {Kε : ℝ}
    (hKε : 0 ≤ Kε) (k : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        |∫ y, (((passiveTransmission b E (freshSchur E (absorbedInput X ε) y)) ^ (k + 1)).trace.re -
            ((passiveTransmission b E X) ^ (k + 1)).trace.re) ∂freshLaw W b| ≤
          K * (modY b E X ^ 3 / W) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨Kd, Wd, hKd, hdr⟩ := modulusDrift_layer_bulk hGA hLp hb0 hb hκ k
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨cY, hcY, hcYd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((1 + Kε / etaZ b E) ^ 2 + 4 * Kε / etaZ b E + 1) *
      (1 + Kε / etaZ b E ^ 2) := ⟨_, by positivity, rfl⟩
  obtain ⟨cK, hcK, hcKd⟩ : ∃ c : ℝ, 0 ≤ c ∧ c = ((k + 1 : ℕ) : ℝ) * ((Kε / etaZ b E) *
      (2 + Kε / etaZ b E) + 4 * Kε / etaZ b E) := ⟨_, by positivity, rfl⟩
  refine ⟨Kd * cY ^ 3 + cK, max Wd 1, by positivity, fun W hW X hX ε hε hεK => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hX' := LawFinite.passiveY_absorbedInput hX hε
  obtain ⟨hFm, hFb⟩ := fresh_inc_facts hb0 hb h1 h2 hε hW1 hX k
  obtain ⟨hYa0, hYa, -, -, hd3⟩ := shift_scalars hb0 hb h1 h2 hKε k hε hεK hW1 hX
  rw [← hcYd] at hYa
  rw [← hcKd] at hd3
  have iF : Integrable (freshIncAt b E (k + 1) (absorbedInput X ε)) (freshLaw W b) :=
    Integrable.of_bound hFm.aestronglyMeasurable (W : ℝ) (hFb.mono fun y h => by
      rwa [Real.norm_eq_abs])
  have hF : |∫ y, freshIncAt b E (k + 1) (absorbedInput X ε) y ∂freshLaw W b| ≤
      Kd * (modY b E (absorbedInput X ε) ^ 3 / W) :=
    hdr W (le_of_max_le_left hW) E (PassiveLayer.mem_bulkInterval_min E) _ hX'
  have hY3 : modY b E (absorbedInput X ε) ^ 3 ≤ cY ^ 3 * modY b E X ^ 3 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hYa0 hYa 3
  have a1 : Kd * (modY b E (absorbedInput X ε) ^ 3 / W) ≤ Kd * cY ^ 3 * (modY b E X ^ 3 / W) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hKd
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hY3 hW0.le
  have key := drift_combine iF (hF.trans a1) hd3
  refine le_trans (le_of_eq (congrArg abs (integral_congr_ae (ae_of_all _ fun y => ?_))))
    (key.trans_eq (by ring))
  simp only [freshIncAt]; ring

end Fixed

end BlockBand.Transmission.Absorbed
