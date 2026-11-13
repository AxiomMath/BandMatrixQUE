module

public import BlockBand.Transmission.PassiveCovarianceBulk.TqSys
public import BlockBand.Transmission.PassiveCovarianceBulk.MatchedBasic
public import BlockBand.Transmission.PassiveCovariance.TauPMatched
public import BlockBand.Transmission.PassiveCovariance.TqMatched
public import BlockBand.Transmission.PassiveCovariance.CStar

/-!
# Bulk-uniform matched values of `x_p`, `t^q`, `C_q`

At a stationary jet, `x_p`, `t^q_r` and `⟨MMᴴMMᴴ⟩` are close to their matched values,
with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds bulk_eta_le_one bulk_norm_z)
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Matched values `x_p ≈ A_p`.**
Bulk-uniform copy of `xP_matched` (constants uniform on `bulkInterval κ`). -/
theorem xP_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖xP b E X p‖ ≤ C ∧ ‖xP b E X p - leadA b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, hsys⟩ := tauP_system_bulk hA hb0 hb hκ
  set K := Cb + C₂
  set Kx := (C₂ * ((1 + b ^ 2 * Cb ^ 2) * K + b ^ 2 * ((Cb + 1) * K) * dStar b) + K +
    b * ((Cb + 1) * K)) / b
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  have hKx : 0 ≤ Kx := by positivity
  refine ⟨d₀, C₂ + Kx, max Wb W₂, hd₀, by positivity, fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  obtain ⟨-, hv, -, -, -, hva, -, -, hm2, -⟩ := hmb W (le_trans (le_max_left _ _) hW) E hEκ s X hX hd
  obtain ⟨hx, h3⟩ := hsys W (le_trans (le_max_right _ _) hW) E hEκ X hX p
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

/-- **Matched values of `t^q_r`.**
Bulk-uniform copy of `tP_matched` (constants uniform on `bulkInterval κ`). -/
theorem tP_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ q r : Fin 2,
        ‖tP b E X q r‖ ≤ C ∧ ‖tP b E X q r - tStar b q r‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, hsys⟩ := tP_system_bulk hA hb0 hb hκ
  obtain ⟨C₃, W₃, hC₃, hbl⟩ := tP_blocks_bulk hA hb0 hb hκ
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
    fun W hW E hEκ s X hX hd q r => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hW₂⟩, hW₃⟩ := hW
  obtain ⟨hM, hv, -, -, -, -, hh, hAd, -, -⟩ := hmb W hWb E hEκ s X hX hd
  obtain ⟨hy, d1, d2, h3⟩ := hsys W hW₂ E hEκ X hX q
  obtain ⟨ht, -, -, -, -⟩ := hbl W hW₃ E hEκ X hX q
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

/-- **`⟨MMᴴMMᴴ⟩ ↦ C_*`.**
Bulk-uniform copy of `cq_matched` (constants uniform on `bulkInterval κ`). -/
theorem cq_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖(W : ℂ)⁻¹ * (SourceMixing.mOf b E X * ((SourceMixing.mOf b E X)ᴴ *
          (SourceMixing.mOf b E X * (SourceMixing.mOf b E X)ᴴ))).trace - jetC b E s‖ ≤
          C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  set Λ := Cb + (etaLow b κ)⁻¹
  have hΛ0 : 0 ≤ Λ := by positivity
  have hCL := constCL_nonneg hb hκ
  refine ⟨d₀, 4 * Λ ^ 3 * Cb + (constCL b κ + 2 / etaLow b κ ^ 3), max Wb 1, hd₀,
    by positivity, fun W hW E hEκ s X hX hd => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηi := inv_etaZ_le_bulk hb hκ hEκ
  obtain ⟨hM, -, hR, -, hMR, -⟩ := hmb W (le_trans (le_max_left _ _) hW) E hEκ s X hX hd
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hC := normTrace_RRsRRs_sub_le hb0 hb h1 h2 hX.posSemidef (by omega) s
  obtain ⟨e0, -, -, e01, he⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
  set e := SourceMixing.epsOf b E s X
  have he0 : 0 ≤ e := by have := sq_nonneg ((W : ℝ)⁻¹); linarith
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  have hM' : ‖M‖ ≤ Λ := hM.trans (by simp only [Λ]; linarith [inv_nonneg.mpr hηL.le])
  have hR' : ‖R‖ ≤ Λ := hR.trans (by simp only [Λ]; linarith)
  have hMh : ‖Mᴴ‖ ≤ Λ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM'
  have hRh : ‖Rᴴ‖ ≤ Λ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hR'
  have hMRh : ‖Mᴴ - Rᴴ‖ ≤ Cb * e := by rw [SourceMixing.norm_conjTranspose_sub]; exact hMR
  have h4 := norm_mul4_sub_le M Mᴴ M Mᴴ R Rᴴ R Rᴴ hMh hM' hMh hR' hRh hR' hMR hMRh hMR hMRh
  have eM : M * (Mᴴ * (M * Mᴴ)) = M * Mᴴ * M * Mᴴ := by simp only [Matrix.mul_assoc]
  have eR : R * Rᴴ * (R * Rᴴ) = R * Rᴴ * R * Rᴴ := by simp only [Matrix.mul_assoc]
  rw [eR] at hC
  have hd : ‖(W : ℂ)⁻¹ * (M * Mᴴ * M * Mᴴ).trace - (W : ℂ)⁻¹ * (R * Rᴴ * R * Rᴴ).trace‖ ≤
      4 * Λ ^ 3 * (Cb * e) := by
    rw [← mul_sub, ← trace_sub]; exact (norm_normTrace_le _).trans h4
  have hC0 : 0 ≤ constC b E + 2 / etaZ b E ^ 3 := by
    have := constB_nonneg (b := b) (E := E) hb0 hb h1 h2
    have : 0 ≤ constC b E := by unfold constC; positivity
    positivity
  rw [eM]
  calc _ ≤ ‖(W : ℂ)⁻¹ * (M * Mᴴ * M * Mᴴ).trace - (W : ℂ)⁻¹ * (R * Rᴴ * R * Rᴴ).trace‖ +
        ‖(W : ℂ)⁻¹ * (R * Rᴴ * R * Rᴴ).trace - jetC b E s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4 * Λ ^ 3 * (Cb * e) + (constCL b κ + 2 / etaLow b κ ^ 3) * e := by
        refine add_le_add hd (hC.trans ((mul_le_mul_of_nonneg_left he hC0).trans
          (mul_le_mul_of_nonneg_right ?_ he0)))
        have h3 := inv_etaZ_pow_le_bulk hb hκ hEκ 3
        have hc := constC_le_bulk hb hκ hEκ
        rw [div_eq_mul_one_div 2 (etaZ b E ^ 3), div_eq_mul_one_div 2 (etaLow b κ ^ 3)]
        linarith
    _ = _ := by ring

end BlockBand.Transmission.CovarianceBulk
