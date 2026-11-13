module

public import BlockBand.Transmission.PassiveCovariance.TqSys
public import BlockBand.Transmission.PassiveCovariance.M5Near

/-!
# Matched values of the `t^q` traces, and the `r_p` weights `B_p`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X` with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only (any `s`
in `epsOf`), uniformly in `W ≥ W₀`, `X`, `q, r`.

* `yq_close` (algebra): from `y(1 - k_hA) ≈ i₀ + bhi₁`, `A ≈ d_*`, `h ≈ 1` get `y ≈ (i₀ + bi₁)/b`
  (the determinant `1 - k_*d_* = b`).
* `tStar q r`: `t^q₀ ↦ y^*_q d_*`, `t^q₁ ↦ [q=1] + by^*_q d_*`, `y^*_q = ([q=0] + b[q=1])/b`.
* **`tP_matched`**: `|t^q_r - tStar q r| ≤ C·epsOf`.
* `rB p = [p=0] + σ₁(r_p)` with `r_{pq} = t^q_p` (cyclicity); `tStar_zero_eq` (`t⁰_p ↦ leadR1 p`)
  and `rB_star_eq` (`rB ↦ leadB p`, `B_p = (1/b, 1)`).
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

/-- `y - y^*` from `y(1 - k_hA) ≈ i₀ + bhi₁`. -/
theorem yq_close {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {y h A i₀ i₁ : ℂ} {e K Cy B : ℝ}
    (he : 0 ≤ e) (hK : 0 ≤ K) (hy : ‖y‖ ≤ Cy) (hhB : ‖h‖ ≤ B) (hi : ‖i₁‖ ≤ 1)
    (hh : ‖h - 1‖ ≤ K * e) (hA : ‖A - dStar b‖ ≤ K * e)
    (h3 : ‖y * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A) - (i₀ + (b : ℂ) * h * i₁)‖ ≤
      K * e) :
    ‖y - (i₀ + (b : ℂ) * i₁) / b‖ ≤ (Cy * ((1 + b ^ 2 * B) * K + b ^ 2 * K * dStar b) + K + b * K) /
      b * e := by
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hCy : 0 ≤ Cy := (norm_nonneg _).trans hy
  have hB : 0 ≤ B := (norm_nonneg _).trans hhB
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  have hd := dStar_mul_one_sub hb0 hb
  have nD : ‖(dStar b : ℂ)‖ = dStar b := by rw [Complex.norm_real, Real.norm_of_nonneg hD]
  have hk : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h‖ ≤ 1 + b ^ 2 * B := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    · rw [norm_mul, norm_pow, nb]; exact mul_le_mul_of_nonneg_left hhB (by positivity)
  have e' : (b : ℂ) * (y - (i₀ + (b : ℂ) * i₁) / b) =
      y * ((((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * (A - dStar b) +
        (b : ℂ) ^ 2 * (h - 1) * dStar b) +
      (y * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * h) * A) - (i₀ + (b : ℂ) * h * i₁)) +
      (b : ℂ) * (h - 1) * i₁ := by
    rw [mul_sub, mul_div_cancel₀ _ hb']
    push_cast
    linear_combination (y * (1 - (b : ℂ))) * hd
  have hn : b * ‖y - (i₀ + (b : ℂ) * i₁) / b‖ ≤
      Cy * ((1 + b ^ 2 * B) * (K * e) + b ^ 2 * (K * e) * dStar b) + K * e + b * (K * e) := by
    have hbn : b * ‖y - (i₀ + (b : ℂ) * i₁) / b‖ = ‖(b : ℂ) * (y - (i₀ + (b : ℂ) * i₁) / b)‖ := by
      rw [norm_mul, nb]
    rw [hbn, e']
    refine (norm_add₃_le).trans (add_le_add_three ?_ h3 ?_)
    · rw [norm_mul]
      refine mul_le_mul hy ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _) hCy
      · rw [norm_mul]; exact mul_le_mul hk hA (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_mul, norm_pow, nb, nD]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) hD
    · rw [norm_mul, norm_mul, nb]
      calc b * ‖h - 1‖ * ‖i₁‖ ≤ b * (K * e) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hh hb0.le) hi (norm_nonneg _) (by positivity)
        _ = _ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
  nlinarith

/-- `y^*_q = ([q=0] + b[q=1])/b`. -/
def yStar (b : ℝ) (q : Fin 2) : ℂ := (ind 0 q + (b : ℂ) * ind 1 q) / b

/-- Leading values of `t^q_r`. -/
def tStar (b : ℝ) (q r : Fin 2) : ℂ :=
  if r = 0 then yStar b q * dStar b else ind 1 q + (b : ℂ) * (yStar b q * dStar b)

/-- `[p = 0] + σ₁(r_p)`, `r_{pq} = t^q_p`. -/
def rB (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2) : ℂ :=
  ind 0 p + sig1 b (tP b E X 0 p) (tP b E X 1 p)

theorem tStar_zero_eq {b : ℝ} (hb0 : 0 < b) (p : Fin 2) : tStar b 0 p = leadR1 b p := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  fin_cases p <;> simp [tStar, yStar, ind, leadR1] <;> field_simp

theorem rB_star_eq {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (p : Fin 2) :
    ind 0 p + sig1 b (tStar b 0 p) (tStar b 1 p) = leadB b p := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hd := dStar_mul_one_sub hb0 hb
  fin_cases p <;> simp [tStar, yStar, ind, leadB, sig1] <;> field_simp <;>
    linear_combination (1 - (b : ℂ)) * hd

/-- **Matched values of `t^q_r`.** -/
theorem tP_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ q r : Fin 2,
        ‖tP b E X q r‖ ≤ C ∧ ‖tP b E X q r - tStar b q r‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨C₂, W₂, hC₂, hsys⟩ := tP_system hA hb0 hb h1 h2
  obtain ⟨C₃, W₃, hC₃, hbl⟩ := tP_blocks hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  set K := Cb + C₂
  set Ky := (C₂ * ((1 + b ^ 2 * (Cb * Cb)) * K + b ^ 2 * K * dStar b) + K + b * K) / b
  set BA := Cb * Cb
  set Ys := (1 + b) / b
  set K0 := K + Ky * BA + Ys * K
  set K1 := K + K * (1 + b * C₃) + b * K0
  have hKy : 0 ≤ Ky := by positivity
  refine ⟨d₀, C₃ + K0 + K1, max (max Wb W₂) W₃, hd₀, by positivity,
    fun W hW X hX hd q r => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hW₂⟩, hW₃⟩ := hW
  obtain ⟨hM, hv, -, -, -, -, hh, hAd, -, -⟩ := hmb W hWb X hX hd
  obtain ⟨hy, d1, d2, h3⟩ := hsys W hW₂ X hX q
  obtain ⟨ht, -, -, -, -⟩ := hbl W hW₃ X hX q
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hWe : ∀ C' : ℝ, 0 ≤ C' → C' / (W : ℝ) ^ 2 ≤ C' * e := fun C' hC' =>
    div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hC'
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have hCbK : Cb ≤ K := by simp only [K]; linarith
  have hC₂K : C₂ ≤ K := by simp only [K]; linarith
  have hhB : ‖SourceMixing.hOf b E X‖ ≤ Cb * Cb := by
    unfold SourceMixing.hOf
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCb
  have hAb : ‖SourceMixing.aOf b E X‖ ≤ BA := (PassiveCovariance.norm_normTrace_le _).trans
    ((Matrix.l2_opNorm_mul _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hCb))
  have h3' := hKe C₂ hC₂K _ (h3.trans (hWe C₂ hC₂))
  unfold SourceMixing.khOf at h3'
  have hyc := yq_close hb0 hb he (by positivity) hy hhB (norm_ind_le 1 q) (hKe Cb hCbK _ hh)
    (hKe Cb hCbK _ hAd) h3'
  have hys : ‖yStar b q‖ ≤ Ys := by
    have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    unfold yStar
    rw [norm_div, nb, div_le_div_iff_of_pos_right hb0]
    refine (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 q) ?_)
    rw [norm_mul, nb]; nlinarith [norm_ind_le 1 q]
  change ‖yP b E X q - yStar b q‖ ≤ Ky * e at hyc
  have nD : ‖(dStar b : ℂ)‖ = dStar b := by rw [Complex.norm_real, Real.norm_of_nonneg hD]
  have t0 : ‖tP b E X q 0 - yStar b q * dStar b‖ ≤ K0 * e := by
    have e' : tP b E X q 0 - yStar b q * dStar b = (tP b E X q 0 - yP b E X q * SourceMixing.aOf b E X) +
        (yP b E X q - yStar b q) * SourceMixing.aOf b E X +
        yStar b q * (SourceMixing.aOf b E X - dStar b) := by ring
    rw [e']
    refine (norm_add₃_le).trans (le_trans (add_le_add_three (hKe C₂ hC₂K _ (d1.trans (hWe C₂ hC₂)))
      ((norm_mul_le _ _).trans (mul_le_mul hyc hAb (norm_nonneg _) (by positivity)))
      ((norm_mul_le _ _).trans (mul_le_mul hys (hKe Cb hCbK _ hAd) (norm_nonneg _)
        (by positivity)))) (le_of_eq (by simp only [K0]; ring)))
  have t1 : ‖tP b E X q 1 - (ind 1 q + (b : ℂ) * (yStar b q * dStar b))‖ ≤ K1 * e := by
    have e' : tP b E X q 1 - (ind 1 q + (b : ℂ) * (yStar b q * dStar b)) =
        (tP b E X q 1 - SourceMixing.hOf b E X * (ind 1 q + (b : ℂ) * tP b E X q 0)) +
        (SourceMixing.hOf b E X - 1) * (ind 1 q + (b : ℂ) * tP b E X q 0) +
        (b : ℂ) * (tP b E X q 0 - yStar b q * dStar b) := by ring
    rw [e']
    have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have hi : ‖ind 1 q + (b : ℂ) * tP b E X q 0‖ ≤ 1 + b * C₃ :=
      (norm_add_le _ _).trans (add_le_add (norm_ind_le 1 q) (by
        rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (ht 0) hb0.le))
    refine (norm_add₃_le).trans (le_trans (add_le_add_three (hKe C₂ hC₂K _ (d2.trans (hWe C₂ hC₂)))
      ((norm_mul_le _ _).trans (mul_le_mul (hKe Cb hCbK _ hh) hi (norm_nonneg _) (by positivity)))
      (show ‖(b : ℂ) * (tP b E X q 0 - yStar b q * dStar b)‖ ≤ b * (K0 * e) by
        rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left t0 hb0.le))
      (le_of_eq (by simp only [K1]; ring)))
  have hK0 : 0 ≤ K0 := by positivity
  have hK1 : 0 ≤ K1 := by positivity
  have hC3' : 0 ≤ C₃ := hC₃
  refine ⟨(ht r).trans (by linarith), ?_⟩
  fin_cases r
  · exact t0.trans (mul_le_mul_of_nonneg_right (by linarith) he)
  · exact t1.trans (mul_le_mul_of_nonneg_right (by linarith) he)

end BlockBand.Transmission.PassiveCovariance
