module

public import BlockBand.Transmission.PassiveCovariance.ZMatched

/-!
# Matched values of `σz_p`, conclusion

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X` with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on
`b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p`.

* `zP_rhs_close`: the right side `R = k_hI_z + bv(1+bt₁)conj v^p₁ + b(bv)v^p₀t₂` of the `z_p` system
  is `R_* + O(ε)` (`zI_close`, `vP0_matched`, `vP1_matched`, `matchedBasic`, `tP_matched`).
* **`zP_matched`**: `|σz_p| ≤ C`, `|σz_p - leadSz p| ≤ C·epsOf` (`zP_div`, `leadSz_eq`).
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

/-- The right side of the `z_p` system approaches `R_*`. -/
theorem zP_rhs_close (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖(SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
            (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
              conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
              svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            ((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              conj (vP b E X p 1) +
            (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 *
              SourceMixing.tTwo b E X 1)) - zRStar b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₃, C0, W0, hd₃, hC0, hv0⟩ := vP0_matched hA hb0 hb h1 h2 s hs
  obtain ⟨d₄, C1, W1, hd₄, hC1, hv1⟩ := vP1_matched hA hb0 hb h1 h2 s hs
  obtain ⟨d₅, CI, WI, hd₅, hCI, hIc⟩ := zI_close hA hb0 hb h1 h2 s hs
  obtain ⟨Cvb, Wvb, hCvb, hVb⟩ := vP_blocks hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨nV, hnVd⟩ : ∃ x : ℝ, x = ‖leadV1 b E s 0‖ + ‖leadV1 b E s 1‖ := ⟨_, rfl⟩
  have h0V : 0 ≤ nV := by rw [hnVd]; positivity
  have h0bt : 0 ≤ b * Ct := by positivity
  obtain ⟨nW, hnWd⟩ : ∃ x : ℝ, x = ‖conj (v1Star b E s 0)‖ + ‖conj (v1Star b E s 1)‖ := ⟨_, rfl⟩
  have h0W : 0 ≤ nW := by rw [hnWd]; positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + (1 + b * Ct) + Ct + dStar b + Cb + Cvb + nV + nW := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Ct + C0 + C1 := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₂) (min d₃ (min d₄ d₅)), b ^ 2 * Cb * CI + 2 * CI + 8 * Λ ^ 3 * K,
    max (max Wb Wt) (max W0 (max W1 (max WI Wvb))),
    lt_min (lt_min hd₀ hd₂) (lt_min hd₃ (lt_min hd₄ hd₅)), by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWt⟩, hW0, hW1, hWI, hWvb⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd2⟩, hd3, hd4, hd5⟩ := hd
  obtain ⟨-, hv, -, -, -, hva, hh1, -⟩ := hmb W hWb X hX hd0
  have ht := htm W hWt X hX hd2
  have h0 := hv0 W hW0 X hX hd3 p
  have h1' := hv1 W hW1 X hX hd4 p
  obtain ⟨hIn, hIl⟩ := hIc W hWI X hX hd5 p
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
  have k1 : C1 ≤ K := by rw [hKd]; linarith
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have ha := norm_matchedA E h1 h2
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  -- the first term
  have hkh : ‖SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2)‖ ≤ b ^ 2 * Cb * e := by
    have e' : SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) =
        (b : ℂ) ^ 2 * (SourceMixing.hOf b E X - 1) := by unfold SourceMixing.khOf; ring
    rw [e', norm_mul, norm_pow, nb, mul_assoc]
    exact mul_le_mul_of_nonneg_left hh1 (by positivity)
  have hkP : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_pow, nb]
    linarith only [hb2, hb0]
  set I := SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
    conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
    svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X
  have tI : ‖SourceMixing.khOf b E X * I - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p‖ ≤
      (b ^ 2 * Cb * CI + 2 * CI) * e := by
    have eq : SourceMixing.khOf b E X * I - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p =
        (SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2)) * I +
          (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * (I - zIStar b E s p) := by ring
    rw [eq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have t1 := mul_le_mul hkh hIn (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul hkP hIl (norm_nonneg _) zero_le_two
    calc _ ≤ b ^ 2 * Cb * e * CI + 2 * (CI * e) := add_le_add t1 t2
      _ = _ := by ring
  -- the second term
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l2 : 1 + b * Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l3 : Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l4 : dStar b ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l6 : Cb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l7 : Cvb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l8 : nV ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l9 : nW ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have hbn : ‖(b : ℂ)‖ ≤ Λ := by rw [nb]; linarith
  have han : ‖matchedA E‖ ≤ Λ := by rw [ha]; exact l1
  have hdn : ‖(dStar b : ℂ)‖ ≤ Λ := by rw [Complex.norm_real, Real.norm_of_nonneg hD]; exact l4
  have hzb : ‖(b : ℂ) - b‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hc : ‖1 + (b : ℂ) * SourceMixing.tTwo b E X 0‖ ≤ 1 + b * Ct :=
    (norm_add_le _ _).trans (add_le_add (le_of_eq norm_one) (by
      rw [norm_mul, nb, tTwo_eq]; exact mul_le_mul_of_nonneg_left (ht 1 0).1 hb0.le))
  have hcd : ‖(1 + (b : ℂ) * SourceMixing.tTwo b E X 0) - (dStar b : ℂ)‖ ≤ K * e := by
    rw [← one_add_tStar hb0 hb, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, nb, tTwo_eq]
    calc b * ‖tP b E X 1 0 - tStar b 1 0‖ ≤ 1 * (Ct * e) :=
          mul_le_mul hb1 (ht 1 0).2 (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKe Ct kt _ le_rfl
  have hbv : ‖(b : ℂ) * SourceMixing.vOf b E X‖ ≤ Λ := by
    rw [norm_mul, nb]; exact (mul_le_of_le_one_left (norm_nonneg _) hb1).trans (hv.trans l6)
  have hba : ‖(b : ℂ) * matchedA E‖ ≤ Λ := by rw [norm_mul, nb, ha, mul_one]; linarith
  have hbva : ‖(b : ℂ) * SourceMixing.vOf b E X - (b : ℂ) * matchedA E‖ ≤ K * e := by
    rw [← mul_sub, norm_mul, nb]
    exact (mul_le_of_le_one_left (norm_nonneg _) hb1).trans (hKe Cb kb _ hva)
  have ht2 : ‖SourceMixing.tTwo b E X 1‖ ≤ Λ := by rw [tTwo_eq]; exact (ht 1 1).1.trans l3
  have ht2d : ‖SourceMixing.tTwo b E X 1 - (dStar b : ℂ)‖ ≤ K * e := by
    rw [tTwo_eq, ← tStar_one_one hb0 hb]; exact hKe Ct kt _ (ht 1 1).2
  have hP := norm_prod4_pair_sub_le (x₁ := (b : ℂ)) (x₂ := SourceMixing.vOf b E X)
    (x₃ := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0) (x₄ := conj (vP b E X p 1))
    (y₁ := (b : ℂ)) (y₂ := matchedA E) (y₃ := (dStar b : ℂ)) (y₄ := conj (v1Star b E s p))
    (x₅ := (b : ℂ)) (x₆ := (b : ℂ) * SourceMixing.vOf b E X) (x₇ := vP b E X p 0)
    (x₈ := SourceMixing.tTwo b E X 1) (y₅ := (b : ℂ)) (y₆ := (b : ℂ) * matchedA E)
    (y₇ := leadV1 b E s p) (y₈ := (dStar b : ℂ)) hΛ (hv.trans l6) (hc.trans l2)
    (by rw [Complex.norm_conj]; exact (hvb 1).trans l7) hbn han hdn hbv ((hvb 0).trans l7) ht2
    hbn hba ((by rw [hnVd]; exact norm_le_sum_two _ p : ‖leadV1 b E s p‖ ≤ nV).trans l8)
    hzb (hKe Cb kb _ hva) hcd (by rw [norm_conj_sub]; exact hKe C1 k1 _ h1') hzb hbva
    (hKe C0 k0 _ h0) ht2d
  have eq : (SourceMixing.khOf b E X * I +
      ((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
        conj (vP b E X p 1) +
      (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1)) -
      zRStar b E s p = (SourceMixing.khOf b E X * I -
        (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p) +
      (((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
        conj (vP b E X p 1) +
      (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1) -
        ((b : ℂ) * matchedA E * (dStar b : ℂ) * conj (v1Star b E s p) +
          (b : ℂ) * ((b : ℂ) * matchedA E) * leadV1 b E s p * (dStar b : ℂ))) := by
    simp only [zRStar]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add tI hP).trans (le_of_eq ?_))
  ring

/-- **Matched values of `σz_p`.** -/
theorem zP_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧ ‖szP b E X p - leadSz b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, C₀, W₀, hd₀, hC₀, hdiv⟩ := zP_div hA hb0 hb h1 h2 s
  obtain ⟨d₁, C₁, W₁, hd₁, hC₁, hrhs⟩ := zP_rhs_close hA hb0 hb h1 h2 s hs
  refine ⟨min d₀ d₁, C₀ + C₁ / b, max W₀ W₁, lt_min hd₀ hd₁, by positivity,
    fun W hW X hX hd p => ?_⟩
  obtain ⟨hS, hq⟩ := hdiv W (le_trans (le_max_left _ _) hW) X hX (hd.trans (min_le_left _ _)) p
  have hr := hrhs W (le_trans (le_max_right _ _) hW) X hX (hd.trans (min_le_right _ _)) p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  refine ⟨hS.trans (le_add_of_nonneg_right (by positivity)), ?_⟩
  rw [leadSz_eq hb0 h1 h2]
  set Ra := SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
    (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
    (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
      conj (vP b E X p 1) +
    (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1
  rw [← add_assoc] at hr
  have hq2 : ‖Ra / b - zRStar b E s p / b‖ ≤ C₁ / b * e := by
    rw [← sub_div, norm_div, nb]
    calc ‖Ra - zRStar b E s p‖ / b ≤ (C₁ * e) / b := div_le_div_of_nonneg_right hr hb0.le
      _ = C₁ / b * e := by ring
  calc ‖szP b E X p - zRStar b E s p / b‖ ≤ ‖szP b E X p - Ra / b‖ + ‖Ra / b - zRStar b E s p / b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C₀ * e + C₁ / b * e := add_le_add hq hq2
    _ = (C₀ + C₁ / b) * e := by ring

end BlockBand.Transmission.PassiveCovariance
