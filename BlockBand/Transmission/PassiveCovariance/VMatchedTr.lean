module

public import BlockBand.Transmission.PassiveCovariance.ZSysTrace

/-!
# Matched values of the two `v_p` traces

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X` with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on
`b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p`.

* **`vP0_matched`**: `|v^p₀ - leadV1 p| ≤ C·epsOf` (`leadV1 = B_pB_* - sσv_p`; from `vP_traces`,
  `s₁ ≈ 1`, `rB_p ≈ B_p`, `B ≈ B_*`, `S_p ≈ σv_p`, `⟨M²⟩ ≈ -s`).
* `v1Star p = a·d_*·t¹_*(p) + b·a·leadV1 p·a` (`t¹_*(p) = tStar 1 p = [p=1] + b·leadR1 p`);
  **`vP1_matched`**: `|v^p₁ - v1Star p| ≤ C·epsOf`.
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

/-- Leading value of `v^p₁ = ⟨(𝒢Π𝒢ᴴP_p𝒢)₁₁⟩` (port block). -/
def v1Star (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  matchedA E * (dStar b : ℂ) * tStar b 1 p * 1 + (b : ℂ) * matchedA E * leadV1 b E s p * matchedA E

theorem norm_m2Of_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C : ℝ}
    (hM : ‖SourceMixing.mOf b E X‖ ≤ C) : ‖SourceMixing.m2Of b E X‖ ≤ C * C :=
  (norm_normTrace_le _).trans ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hM hM (norm_nonneg _) ((norm_nonneg _).trans hM)))

theorem norm_bOf_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C : ℝ}
    (hM : ‖SourceMixing.mOf b E X‖ ≤ C) : ‖SourceMixing.bOf b E X‖ ≤ C * (C * C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hM
  exact (norm_normTrace_le _).trans ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM
    ((Matrix.l2_opNorm_mul _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hC))
    (norm_nonneg _) hC))

/-- `rB_p ≈ B_p` with `|rB_p| ≤ 1 + C_t`. -/
theorem rB_close {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {X : Matrix (Fin W) (Fin W) ℂ}
    {Ct e : ℝ} (p : Fin 2) (ht : ∀ q r : Fin 2, ‖tP b E X q r‖ ≤ Ct ∧ ‖tP b E X q r - tStar b q r‖ ≤ Ct * e) :
    ‖rB b E X p‖ ≤ 1 + Ct ∧ ‖rB b E X p - leadB b p‖ ≤ Ct * e := by
  refine ⟨(norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht 0 p).1 (ht 1 p).1)), ?_⟩
  rw [← rB_star_eq hb0 hb p]
  have e' : rB b E X p - (ind 0 p + sig1 b (tStar b 0 p) (tStar b 1 p)) =
      sig1 b (tP b E X 0 p - tStar b 0 p) (tP b E X 1 p - tStar b 1 p) := by
    simp only [rB, sig1]; ring
  rw [e']; exact norm_sig1_le hb0 hb (ht 0 p).2 (ht 1 p).2

/-- **`v^p₀ ↦ leadV1 p`.** -/
theorem vP0_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖vP b E X p 0 - leadV1 b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₃, Cv, Wv, hd₃, hCv, hsv⟩ := svP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨Ctr, Wtr, hCtr, htr⟩ := vP_traces hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨nB, hnBd⟩ : ∃ x : ℝ, x = ‖leadB b 0‖ + ‖leadB b 1‖ := ⟨_, rfl⟩
  obtain ⟨nS, hnSd⟩ : ∃ x : ℝ, x = ‖leadSv b E s 0‖ + ‖leadSv b E s 1‖ := ⟨_, rfl⟩
  have h0B : 0 ≤ nB := by rw [hnBd]; positivity
  have h0S : 0 ≤ nS := by rw [hnSd]; positivity
  have h0j := norm_nonneg (jetB b E s)
  have hb3 : 0 ≤ Cb * (Cb * Cb) := by positivity
  have hb2 : 0 ≤ Cb * Cb := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + Ct + Cb * (Cb * Cb) + nB + ‖jetB b E s‖ + Cb * Cb + nS +
    dStar b := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cv + Ctr := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ d₃), Ctr + 8 * Λ ^ 3 * K, max (max Wb Ws) (max (max Wt Wv) Wtr),
    lt_min (lt_min hd₀ hd₁) (lt_min hd₂ hd₃), by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, ⟨hWt, hWv⟩, hWtr⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3⟩ := hd
  obtain ⟨hM, -, -, -, -, -, -, -, hm2, hBj⟩ := hmb W hWb X hX hd0
  obtain ⟨-, -, hs1, -, -⟩ := hms W hWs X hX hd1
  obtain ⟨hrn, hrl⟩ := rB_close hb0 hb p (htm W hWt X hX hd2)
  obtain ⟨-, hSl⟩ := hsv W hWv X hX hd3 p
  obtain ⟨d0, -⟩ := htr W hWtr X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have kb : Cb ≤ K := by rw [hKd]; linarith
  have ks : Cs ≤ K := by rw [hKd]; linarith
  have kt : Ct ≤ K := by rw [hKd]; linarith
  have kv : Cv ≤ K := by rw [hKd]; linarith
  have hlB : ‖leadB b p‖ ≤ nB := by rw [hnBd]; exact norm_le_sum_two _ p
  have hlS : ‖leadSv b E s p‖ ≤ nS := by rw [hnSd]; exact norm_le_sum_two _ p
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l2 : 1 + Ct ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l3 : Cb * (Cb * Cb) ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l4 : nB ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l5 : ‖jetB b E s‖ ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l6 : Cb * Cb ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l7 : nS ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l8 : dStar b ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have h1n : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hP := norm_prod4_pair_sub_le (x₁ := SourceMixing.sOne b E X) (x₂ := rB b E X p)
    (x₃ := SourceMixing.bOf b E X) (x₄ := 1) (y₁ := 1) (y₂ := leadB b p) (y₃ := jetB b E s) (y₄ := 1)
    (x₅ := svP b E X p) (x₆ := SourceMixing.m2Of b E X) (x₇ := 1) (x₈ := 1) (y₅ := leadSv b E s p)
    (y₆ := -s) (y₇ := 1) (y₈ := 1) hΛ (hrn.trans l2) ((norm_bOf_le hM).trans l3) h1n h1n
    (hlB.trans l4) l5 ((norm_m2Of_le hM).trans l6) h1n h1n (hlS.trans l7)
    (by rw [norm_neg]; exact hs.2.trans l8) h1n (hKe Cs ks _ hs1) (hKe Ct kt _ hrl)
    (hKe Cb kb _ hBj) hz (hKe Cv kv _ hSl) (by rw [sub_neg_eq_add]; exact hKe Cb kb _ hm2) hz hz
  have eq : vP b E X p 0 - leadV1 b E s p =
      (vP b E X p 0 - (SourceMixing.sOne b E X * rB b E X p * SourceMixing.bOf b E X +
        svP b E X p * SourceMixing.m2Of b E X)) +
      ((SourceMixing.sOne b E X * rB b E X p * SourceMixing.bOf b E X * 1 +
        svP b E X p * SourceMixing.m2Of b E X * 1 * 1) -
        (1 * leadB b p * jetB b E s * 1 + leadSv b E s p * -s * 1 * 1)) := by
    simp only [leadV1]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add (d0.trans (div_sq_le_epsOf (b := b) (E := E) s
    hX.posSemidef hCtr)) hP).trans (le_of_eq ?_))
  ring

/-- **`v^p₁ ↦ v1Star p`.** -/
theorem vP1_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖vP b E X p 1 - v1Star b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₃, C0, W0, hd₃, hC0, hv0⟩ := vP0_matched hA hb0 hb h1 h2 s hs
  obtain ⟨Ctr, Wtr, hCtr, htr⟩ := vP_traces hA hb0 hb h1 h2
  obtain ⟨Cvb, Wvb, hCvb, hVb⟩ := vP_blocks hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨nT, hnTd⟩ : ∃ x : ℝ, x = ‖tStar b 1 0‖ + ‖tStar b 1 1‖ := ⟨_, rfl⟩
  obtain ⟨nV, hnVd⟩ : ∃ x : ℝ, x = ‖leadV1 b E s 0‖ + ‖leadV1 b E s 1‖ := ⟨_, rfl⟩
  have h0T : 0 ≤ nT := by rw [hnTd]; positivity
  have h0V : 0 ≤ nV := by rw [hnVd]; positivity
  have h0bt : 0 ≤ b * Ct := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + (1 + b * Ct) + Ct + dStar b + nT + Cb + Cvb + nV := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Ct + C0 + Ctr := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min d₀ (min d₂ d₃), Ctr + 8 * Λ ^ 3 * K, max (max Wb Wt) (max W0 (max Wtr Wvb)),
    lt_min hd₀ (lt_min hd₂ hd₃), by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWt⟩, hW0, hWtr, hWvb⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨hd0, hd2, hd3⟩ := hd
  obtain ⟨-, hv, -, -, -, hva, -⟩ := hmb W hWb X hX hd0
  have ht := htm W hWt X hX hd2
  have h0 := hv0 W hW0 X hX hd3 p
  obtain ⟨-, d1⟩ := htr W hWtr X hX p
  obtain ⟨hvb, -⟩ := hVb W hWvb X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have kb : Cb ≤ K := by rw [hKd]; linarith
  have kt : Ct ≤ K := by rw [hKd]; linarith
  have k0 : C0 ≤ K := by rw [hKd]; linarith
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have ha := norm_matchedA E h1 h2
  have hb1 : b ≤ 1 := by linarith
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l2 : 1 + b * Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l3 : Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l4 : dStar b ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l5 : nT ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l6 : Cb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l7 : Cvb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l8 : nV ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have h1n : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have hbn : ‖(b : ℂ)‖ ≤ Λ := by rw [nb]; linarith
  have han : ‖matchedA E‖ ≤ Λ := by rw [ha]; exact l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hzb : ‖(b : ℂ) - b‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hc : ‖1 + (b : ℂ) * SourceMixing.tTwo b E X 0‖ ≤ 1 + b * Ct :=
    (norm_add_le _ _).trans (add_le_add (le_of_eq norm_one) (by
      rw [norm_mul, nb, tTwo_eq]; exact mul_le_mul_of_nonneg_left (ht 1 0).1 hb0.le))
  have hcd : ‖(1 + (b : ℂ) * SourceMixing.tTwo b E X 0) - (dStar b : ℂ)‖ ≤ K * e := by
    rw [← one_add_tStar hb0 hb, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, nb, tTwo_eq]
    calc b * ‖tP b E X 1 0 - tStar b 1 0‖ ≤ 1 * (Ct * e) :=
          mul_le_mul hb1 (ht 1 0).2 (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKe Ct kt _ le_rfl
  have hdn : ‖(dStar b : ℂ)‖ ≤ Λ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hD]; exact l4
  have hP := norm_prod4_pair_sub_le (x₁ := SourceMixing.vOf b E X)
    (x₂ := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0) (x₃ := tP b E X 1 p) (x₄ := 1)
    (y₁ := matchedA E) (y₂ := (dStar b : ℂ)) (y₃ := tStar b 1 p) (y₄ := 1) (x₅ := (b : ℂ))
    (x₆ := SourceMixing.vOf b E X) (x₇ := vP b E X p 0) (x₈ := SourceMixing.vOf b E X)
    (y₅ := (b : ℂ)) (y₆ := matchedA E) (y₇ := leadV1 b E s p) (y₈ := matchedA E) hΛ
    (hc.trans l2) ((ht 1 p).1.trans l3) h1n han hdn
    ((by rw [hnTd]; exact norm_le_sum_two _ p : ‖tStar b 1 p‖ ≤ nT).trans l5)
    (hv.trans l6) ((hvb 0).trans l7) (hv.trans l6) hbn han
    ((by rw [hnVd]; exact norm_le_sum_two _ p : ‖leadV1 b E s p‖ ≤ nV).trans l8)
    (hKe Cb kb _ hva) hcd (hKe Ct kt _ (ht 1 p).2) hz hzb (hKe Cb kb _ hva) (hKe C0 k0 _ h0)
    (hKe Cb kb _ hva)
  have eq : vP b E X p 1 - v1Star b E s p =
      (vP b E X p 1 - SourceMixing.vOf b E X * ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
        tP b E X 1 p + (b : ℂ) * vP b E X p 0 * SourceMixing.vOf b E X)) +
      ((SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p * 1 +
        (b : ℂ) * SourceMixing.vOf b E X * vP b E X p 0 * SourceMixing.vOf b E X) -
        (matchedA E * (dStar b : ℂ) * tStar b 1 p * 1 +
          (b : ℂ) * matchedA E * leadV1 b E s p * matchedA E)) := by
    simp only [v1Star]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add (d1.trans (div_sq_le_epsOf (b := b) (E := E) s
    hX.posSemidef hCtr)) hP).trans (le_of_eq ?_))
  ring

end BlockBand.Transmission.PassiveCovariance
