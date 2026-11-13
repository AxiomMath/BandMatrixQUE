module

public import BlockBand.Transmission.PassiveCovariance.TauP

/-!
# Matched values of `x_p = [p=0] + σ₁(τ^p)` at a stationary jet

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X` with
`δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on `b, E, s`
only, uniformly in `W ≥ W₀`, `X`, `p`.

* `xP_close` (pure algebra; `theta_close` with a general right side `i₀ + bv²i₁`): from
  `x(1 - k_v m) ≈ i₀ + bv²i₁`, `m ≈ -s`, `v ≈ a`, `|1 + k₋s| > b` get `x ≈ (i₀ + ba²i₁)/(1+k₋s)`.
* **`xP_matched`**: `|x_p - A_p| ≤ C·epsOf` (`A_p = leadA p`), `|x_p| ≤ C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `x - x_*` from `x(1 - k_v m) ≈ i₀ + bv²i₁`. -/
theorem xP_close {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {x v m2 s i₀ i₁ : ℂ} {e K B Cx D : ℝ}
    (he : 0 ≤ e) (hK : 0 ≤ K) (hv : ‖v‖ ≤ B) (hx : ‖x‖ ≤ Cx) (hsD : ‖s‖ ≤ D)
    (ha : ‖matchedA E‖ = 1) (hden : b < ‖1 + kMinus b E * s‖) (hi : ‖i₁‖ ≤ 1)
    (hm2 : ‖m2 + s‖ ≤ K * e) (hva : ‖v - matchedA E‖ ≤ K * e)
    (h3 : ‖x * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2) * m2) -
      (i₀ + (b : ℂ) * v ^ 2 * i₁)‖ ≤ K * e) :
    ‖x - (i₀ + (b : ℂ) * matchedA E ^ 2 * i₁) / (1 + kMinus b E * s)‖ ≤
      (Cx * ((1 + b ^ 2 * B ^ 2) * K + b ^ 2 * ((B + 1) * K) * D) + K +
        b * ((B + 1) * K)) / b * e := by
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hB : 0 ≤ B := (norm_nonneg _).trans hv
  have hCx : 0 ≤ Cx := (norm_nonneg _).trans hx
  have hne : 1 + kMinus b E * s ≠ 0 := fun h => by rw [h, norm_zero] at hden; linarith
  have hv2 : ‖v ^ 2 - matchedA E ^ 2‖ ≤ (B + 1) * K * e := by
    rw [show v ^ 2 - matchedA E ^ 2 = (v + matchedA E) * (v - matchedA E) by ring, norm_mul]
    calc ‖v + matchedA E‖ * ‖v - matchedA E‖ ≤ (B + 1) * (K * e) :=
          mul_le_mul ((norm_add_le _ _).trans (by rw [ha]; linarith)) hva (norm_nonneg _)
            (by linarith)
      _ = _ := by ring
  have hkv : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2‖ ≤ 1 + b ^ 2 * B ^ 2 := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    · rw [norm_mul, norm_pow, norm_pow, nb]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (by positivity)
  set xs := (i₀ + (b : ℂ) * matchedA E ^ 2 * i₁) / (1 + kMinus b E * s)
  have hxs : xs * (1 + kMinus b E * s) = i₀ + (b : ℂ) * matchedA E ^ 2 * i₁ := div_mul_cancel₀ _ hne
  have e' : (1 + kMinus b E * s) * (x - xs) =
      x * ((((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2) * (m2 + s) -
        (b : ℂ) ^ 2 * (v ^ 2 - matchedA E ^ 2) * s) +
      (x * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * v ^ 2) * m2) - (i₀ + (b : ℂ) * v ^ 2 * i₁)) +
      (b : ℂ) * (v ^ 2 - matchedA E ^ 2) * i₁ := by
    unfold kMinus at hxs ⊢
    linear_combination (-1 : ℂ) * hxs
  have hn : b * ‖x - xs‖ ≤ Cx * ((1 + b ^ 2 * B ^ 2) * (K * e) + b ^ 2 * ((B + 1) * K * e) * D) +
      K * e + b * ((B + 1) * K * e) := by
    have hle : b * ‖x - xs‖ ≤ ‖1 + kMinus b E * s‖ * ‖x - xs‖ :=
      mul_le_mul_of_nonneg_right hden.le (norm_nonneg _)
    refine hle.trans ?_
    rw [← norm_mul, e']
    refine (norm_add₃_le).trans (add_le_add_three ?_ h3 ?_)
    · rw [norm_mul]
      refine mul_le_mul hx ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _) hCx
      · rw [norm_mul]; exact mul_le_mul hkv hm2 (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_mul, norm_pow, nb]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hv2 (by positivity)) hsD (norm_nonneg _)
          (by positivity)
    · rw [norm_mul, norm_mul, nb]
      calc b * ‖v ^ 2 - matchedA E ^ 2‖ * ‖i₁‖ ≤ b * ((B + 1) * K * e) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hv2 hb0.le) hi (norm_nonneg _) (by positivity)
        _ = _ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
  nlinarith

theorem leadA_eq (b E : ℝ) (s : ℂ) (p : Fin 2) :
    (ind 0 p + (b : ℂ) * matchedA E ^ 2 * ind 1 p) / (1 + kMinus b E * s) = leadA b E s p := by
  fin_cases p <;> simp [ind, leadA, leadDen]

/-- **Matched values `x_p ≈ A_p`.** -/
theorem xP_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖xP b E X p‖ ≤ C ∧ ‖xP b E X p - leadA b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨C₂, W₂, hC₂, hsys⟩ := tauP_system hA hb0 hb h1 h2
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  set K := Cb + C₂
  set Kx := (C₂ * ((1 + b ^ 2 * Cb ^ 2) * K + b ^ 2 * ((Cb + 1) * K) * dStar b) + K +
    b * ((Cb + 1) * K)) / b
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  have hKx : 0 ≤ Kx := by positivity
  refine ⟨d₀, C₂ + Kx, max Wb W₂, hd₀, by positivity, fun W hW X hX hd p => ?_⟩
  obtain ⟨-, hv, -, -, -, hva, -, -, hm2, -⟩ := hmb W (le_trans (le_max_left _ _) hW) X hX hd
  obtain ⟨hx, h3⟩ := hsys W (le_trans (le_max_right _ _) hW) X hX p
  obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have hCbK : Cb ≤ K := by simp only [K]; linarith
  have hC₂K : C₂ ≤ K := by simp only [K]; linarith
  have h3' : ‖xP b E X p * (1 - SourceMixing.kvOf b E X * SourceMixing.m2Of b E X) -
      (ind 0 p + (b : ℂ) * SourceMixing.vOf b E X ^ 2 * ind 1 p)‖ ≤ K * e := by
    refine hKe C₂ hC₂K _ (h3.trans ?_)
    rw [← SourceMixing.div_sq_eq]; exact mul_le_mul_of_nonneg_left (by linarith) hC₂
  unfold SourceMixing.kvOf at h3'
  have hc := xP_close (E := E) hb0 hb he (by positivity) hv hx hs.2 (norm_matchedA E h1 h2) hden
    (norm_ind_le 1 p) (hKe Cb hCbK _ hm2) (hKe Cb hCbK _ hva) h3'
  rw [leadA_eq] at hc
  exact ⟨hx.trans (by linarith), hc.trans (mul_le_mul_of_nonneg_right (by linarith) he)⟩

end BlockBand.Transmission.PassiveCovariance
