module

public import BlockBand.Transmission.FractionalBulk.LayerStep

/-!
# The one-layer step as a single smooth bound

**`stepBound_bulk hGA hLp hP`**: constants `c > 0`, `A ≥ 0`, `B ≥ 0`, `d, γ > 0` and `W₀`, chosen
from `b, κ, p` only, such that for `W ≥ W₀`, `E ∈ bulkInterval κ`, a stationary jet `s` and every
passive `X`,
`E stepFrac ≤ P - (c/W)P² + A Wδ₀² + A/W + A g²/W + B W((δ₀/d)² + (δ₁/d)² + (g/(γW))²)`.

Instead of restricting to a small fixed jet and `g/W` domain, the bound uses the smooth majorant
`B W((δ₀/d)² + (δ₁/d)² + (g/(γW))²)`, which is `≥ BW` off the domain. The `δ₀P` term is
absorbed by Young's inequality, `Cδ₀P ≤ (c/4W)P² + (C²W/c)δ₀²` (instead of a scalar-error
weight `1 + K_pδ_{0,+}`), and `Σ_{t ≤ 1/2} t^p ≥ P - 2g` gives the `g²/W` forcing.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Pure real bookkeeping.** -/
theorem step_alg {P low g δ₀ δ₁ I C₀ C c d γ Wr : ℝ} (hW : 1 ≤ Wr) (hP0 : 0 ≤ P) (hPW : P ≤ Wr)
    (hl0 : 0 ≤ low) (hlP : low ≤ P) (hlg : P - 2 * g ≤ low) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hc : 0 < c) (hd : 0 < d) (hγ : 0 < γ)
    (ha : I ≤ (1 + C₀) * P)
    (hb : δ₀ ≤ d → δ₁ ≤ d → g ≤ γ * Wr → I ≤ (1 + C * (δ₀ + Wr⁻¹ ^ 2)) * P - c / Wr * low ^ 2) :
    I ≤ P - c / (4 * Wr) * P ^ 2 + C ^ 2 * Wr / c * δ₀ ^ 2 + C / Wr + 4 * c / Wr * g ^ 2 +
      (C₀ + c) * Wr * ((δ₀ / d) ^ 2 + (δ₁ / d) ^ 2 + (g / (γ * Wr)) ^ 2) := by
  have hW0 : 0 < Wr := by linarith
  have hS0 : 0 ≤ (δ₀ / d) ^ 2 + (δ₁ / d) ^ 2 + (g / (γ * Wr)) ^ 2 := by positivity
  have hP2 : c / (4 * Wr) * P ^ 2 ≤ c * Wr / 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hPW hPW hP0 hW0.le]
  have hfr : 0 ≤ C ^ 2 * Wr / c * δ₀ ^ 2 + C / Wr + 4 * c / Wr * g ^ 2 := by positivity
  by_cases hD : δ₀ ≤ d ∧ δ₁ ≤ d ∧ g ≤ γ * Wr
  · obtain ⟨h0, h1, h2⟩ := hD
    have hI := hb h0 h1 h2
    -- `low² ≥ P²/2 - 4g²`
    have hlow2 : P ^ 2 / 2 - 4 * g ^ 2 ≤ low ^ 2 := by
      by_cases hPg : P - 2 * g ≤ 0
      · nlinarith [sq_nonneg low]
      · push Not at hPg
        have := mul_le_mul hlg hlg hPg.le hl0
        nlinarith [sq_nonneg (P - 4 * g)]
    -- `C W⁻² P ≤ C/W`
    have hWP : C * Wr⁻¹ ^ 2 * P ≤ C / Wr := by
      rw [div_eq_mul_inv]
      have : Wr⁻¹ ^ 2 * P ≤ Wr⁻¹ := by
        rw [sq, mul_assoc]
        have : Wr⁻¹ * P ≤ 1 := by rw [inv_mul_le_iff₀ hW0]; linarith
        nlinarith [inv_nonneg.mpr hW0.le]
      nlinarith
    -- Young
    have hY : C * δ₀ * P ≤ c / (4 * Wr) * P ^ 2 + C ^ 2 * Wr / c * δ₀ ^ 2 := by
      have key : 0 ≤ (c * P - 2 * C * Wr * δ₀) ^ 2 := sq_nonneg _
      have e : c / (4 * Wr) * P ^ 2 + C ^ 2 * Wr / c * δ₀ ^ 2 - C * δ₀ * P =
          (c * P - 2 * C * Wr * δ₀) ^ 2 / (4 * Wr * c) := by
        field_simp; ring
      have : 0 ≤ (c * P - 2 * C * Wr * δ₀) ^ 2 / (4 * Wr * c) := by positivity
      linarith
    have hlowc : c / Wr * (P ^ 2 / 2 - 4 * g ^ 2) ≤ c / Wr * low ^ 2 :=
      mul_le_mul_of_nonneg_left hlow2 (by positivity)
    have e1 : (1 + C * (δ₀ + Wr⁻¹ ^ 2)) * P = P + C * δ₀ * P + C * Wr⁻¹ ^ 2 * P := by ring
    have e2 : c / Wr * (P ^ 2 / 2 - 4 * g ^ 2) =
        2 * (c / (4 * Wr) * P ^ 2) - 4 * c / Wr * g ^ 2 := by field_simp; ring
    have hB0 : 0 ≤ (C₀ + c) * Wr * ((δ₀ / d) ^ 2 + (δ₁ / d) ^ 2 + (g / (γ * Wr)) ^ 2) := by
      positivity
    nlinarith
  · -- off the domain: one square is at least one
    have hS1 : 1 ≤ (δ₀ / d) ^ 2 + (δ₁ / d) ^ 2 + (g / (γ * Wr)) ^ 2 := by
      have hq : ∀ x y : ℝ, 0 < y → y < x → 1 ≤ (x / y) ^ 2 := fun x y hy hxy => by
        have : 1 < x / y := (one_lt_div hy).mpr hxy
        nlinarith
      simp only [not_and_or, not_le] at hD
      have a0 := sq_nonneg (δ₀ / d)
      have a1 := sq_nonneg (δ₁ / d)
      have a2 := sq_nonneg (g / (γ * Wr))
      rcases hD with h | h | h
      · have := hq _ _ hd h; linarith
      · have := hq _ _ hd h; linarith
      · have := hq _ _ (by positivity) h; linarith
    have hB : (C₀ + c) * Wr ≤ (C₀ + c) * Wr * ((δ₀ / d) ^ 2 + (δ₁ / d) ^ 2 + (g / (γ * Wr)) ^ 2) :=
      le_mul_of_one_le_right (by positivity) hS1
    have : C₀ * P ≤ C₀ * Wr := mul_le_mul_of_nonneg_left hPW hC₀
    have e : (1 + C₀) * P = P + C₀ * P := by ring
    have e' : (C₀ + c) * Wr = C₀ * Wr + c * Wr := by ring
    have := mul_pos hc hW0
    linarith

/-- **The one-layer step as one bound.** -/
theorem stepBound_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (c A B d γ : ℝ) (W₀ : ℕ), 0 < c ∧ 0 ≤ A ∧ 0 ≤ B ∧ 0 < d ∧ 0 < γ ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ∫ y, stepFrac p b E X y ∂freshLaw W b ≤
          fracTrace p (passiveTransmission b E X) -
            c / W * fracTrace p (passiveTransmission b E X) ^ 2 +
          A * W * jetDistance0 b E X ^ 2 + A / W +
          A / W * conductanceOf (passiveTransmission b E X) ^ 2 +
          B * W * ((jetDistance0 b E X / d) ^ 2 + (jetDistance1 b E s X / d) ^ 2 +
            (conductanceOf (passiveTransmission b E X) / (γ * W)) ^ 2) := by
  obtain ⟨C₀, C, c, d, γ, W₁, hC₀, hC, hc, hd, hγ, hL⟩ := layerStep_bulk hGA hLp hP hp0 hp1 hb0 hb hκ
  refine ⟨c / 4, C ^ 2 / c + C + 4 * c, C₀ + c, d, γ, max W₁ 1, by positivity, by positivity,
    by positivity, hd, hγ, fun W hW E hE s hs X hX => ?_⟩
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hT := passiveTransmission_posSemidef (by linarith : b < 1) h1 h2 hX
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  obtain ⟨ha, hb'⟩ := hL W (le_trans (le_max_left _ _) hW) E hE s hs X hX
  have hP0 := fracTrace_nonneg' p (passiveTransmission b E X)
  have hPW : fracTrace p (passiveTransmission b E X) ≤ W := by
    have := fracTrace_le_card hT hT1 hp0; rwa [Fintype.card_fin] at this
  have hl0 := lowFrac_nonneg p hT
  have hlP : lowFrac p (passiveTransmission b E X) ≤ fracTrace p (passiveTransmission b E X) := by
    rw [lowFrac_eq_sum hT, fracTrace_eq_sum_ts hT]
    exact Finset.sum_le_sum fun i _ => by
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (ts_lam_nonneg hT i) _
  have hlg := lowFrac_ge hp0 hT hT1
  have hg0 : 0 ≤ conductanceOf (passiveTransmission b E X) := by
    rw [conductanceOf, ← ts_sum_lam hT]; exact Finset.sum_nonneg fun i _ => ts_lam_nonneg hT i
  have h := step_alg (δ₀ := jetDistance0 b E X) (δ₁ := jetDistance1 b E s X) hWr hP0 hPW hl0 hlP
    hlg hC₀ hC hc hd hγ ha hb'
  have e1 : c / 4 / (W : ℝ) = c / (4 * W) := by ring
  rw [e1]
  have e2 : (C ^ 2 / c + C + 4 * c) * W * jetDistance0 b E X ^ 2 + (C ^ 2 / c + C + 4 * c) / W +
      (C ^ 2 / c + C + 4 * c) / W * conductanceOf (passiveTransmission b E X) ^ 2 ≥
      C ^ 2 * W / c * jetDistance0 b E X ^ 2 + C / W +
        4 * c / W * conductanceOf (passiveTransmission b E X) ^ 2 := by
    have hWp : (0 : ℝ) < W := by linarith
    have hδ : 0 ≤ jetDistance0 b E X ^ 2 := sq_nonneg _
    have hg2 : 0 ≤ conductanceOf (passiveTransmission b E X) ^ 2 := sq_nonneg _
    have a1 : C ^ 2 * W / c * jetDistance0 b E X ^ 2 ≤
        (C ^ 2 / c + C + 4 * c) * W * jetDistance0 b E X ^ 2 := by
      rw [show C ^ 2 * W / c = C ^ 2 / c * W by ring]
      gcongr
      have : 0 ≤ C + 4 * c := by positivity
      linarith
    have a2 : C / W ≤ (C ^ 2 / c + C + 4 * c) / W := by
      gcongr; have : 0 ≤ C ^ 2 / c := by positivity
      linarith
    have a3 : 4 * c / W * conductanceOf (passiveTransmission b E X) ^ 2 ≤
        (C ^ 2 / c + C + 4 * c) / W * conductanceOf (passiveTransmission b E X) ^ 2 := by
      gcongr; have : 0 ≤ C ^ 2 / c := by positivity
      linarith
    linarith
  linarith

end BlockBand.Transmission.FractionalBulk
