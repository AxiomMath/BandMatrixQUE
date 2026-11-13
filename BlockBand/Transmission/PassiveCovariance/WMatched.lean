module

public import BlockBand.Transmission.PassiveCovariance.WSysTrace

/-!
# Matched values of `σ_p = σ₁(w^p)`: `σ_p ↦ σw_p = leadSw p`

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X` with
`δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on `b, E, s`
only, uniformly in `W ≥ W₀`, `X`, `p`.

* `tStar_one_one` (`t₂ ↦ d_*`), `leadU1_eq` (`u_p = -sA_p`), `leadSw_eq` (`σw_p = R_*/b` with the
  matched right side `R_* = k_*A_pB_* + ba([p=1] + bu_p)d_*`, `k_* = c + b² = bσ₊`).
* `tauP_zero_matched`: `|τ^p₀ - u_p| ≤ C·epsOf` (`τ^p₀ ≈ x_p⟨M²⟩`, `x_p ≈ A_p`, `⟨M²⟩ ≈ -s`).
* **`swP_matched`**: `|σ_p| ≤ C`, `|σ_p - leadSw p| ≤ C·epsOf`. From `wP_system` (determinant
  `1 - k_hA → 1 - k_*d_* = b`, divided as in `yq_close`), `matchedBasic` (`h ≈ 1`, `A ≈ d_*`,
  `v ≈ a`, `B ≈ B_*`), `matchedScalars` (`s₁ ≈ 1`), `xP_matched`, `tP_matched` (`t₂ ≈ d_*`).
  For `p = 1` this is `ρ₁ ≈ c₀(1 - θ_*)`; the general-`p` value is checked against `leadSw`
  of `LeadAlgebra`.
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

theorem norm_le_sum_two (f : Fin 2 → ℂ) (p : Fin 2) : ‖f p‖ ≤ ‖f 0‖ + ‖f 1‖ := by
  fin_cases p
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

theorem tStar_one_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) : tStar b 1 1 = dStar b := by
  rw [← one_add_tStar hb0 hb]; simp [tStar, ind]

theorem leadU1_eq (b E : ℝ) (s : ℂ) (p : Fin 2) : leadU1 b E s p = leadA b E s p * (-s) := by
  fin_cases p <;> (simp [leadU1, leadA]; try ring)

theorem leadSw_eq {b : ℝ} (hb0 : 0 < b) (E : ℝ) (s : ℂ) (p : Fin 2) :
    leadSw b E s p = ((((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * leadA b E s p * 1 * jetB b E s +
      (b : ℂ) * matchedA E * (ind 1 p + (b : ℂ) * leadU1 b E s p) * dStar b) / b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hind : ind 1 p = leadInd p := by fin_cases p <;> simp [ind, leadInd]
  rw [hind]
  simp only [leadSw, sigmaPlus, kPlus]
  push_cast
  field_simp

/-- `τ^p₀ ↦ u_p = -sA_p`. -/
theorem tauP_zero_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖tauP b E X p 0 - leadU1 b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₃, Cx, Wx, hd₃, hCx, hxm⟩ := xP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨Cw, Ww, hCw, hsys⟩ := wP_system hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  refine ⟨min d₀ d₃, Cw + Cx * Cb + Cx * dStar b, max (max Wb Wx) Ww, lt_min hd₀ hd₃,
    by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWx⟩, hWw⟩ := hW
  obtain ⟨-, -, -, -, -, -, -, -, hm2, -⟩ := hmb W hWb X hX (hd.trans (min_le_left _ _))
  obtain ⟨hx, hxA⟩ := hxm W hWx X hX (hd.trans (min_le_right _ _)) p
  obtain ⟨-, hτ, -⟩ := hsys W hWw X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have eq : tauP b E X p 0 - leadU1 b E s p = (tauP b E X p 0 - xP b E X p * SourceMixing.m2Of b E X) +
      xP b E X p * (SourceMixing.m2Of b E X + s) - (xP b E X p - leadA b E s p) * s := by
    rw [leadU1_eq]; ring
  rw [eq]
  have a1 := hτ.trans (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCw)
  have a2 : ‖xP b E X p * (SourceMixing.m2Of b E X + s)‖ ≤ Cx * (Cb * e) := by
    rw [norm_mul]; exact mul_le_mul hx hm2 (norm_nonneg _) hCx
  have a3 : ‖(xP b E X p - leadA b E s p) * s‖ ≤ Cx * e * dStar b := by
    rw [norm_mul]; exact mul_le_mul hxA hs.2 (norm_nonneg _) (by positivity)
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add a1 a2)) a3).trans
    (le_of_eq (by ring)))

/-- Two products of four approximate factors. -/
theorem norm_prod4_pair_sub_le {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ x₅ x₆ x₇ x₈ y₅ y₆ y₇ y₈ : ℂ} {Λ ε : ℝ}
    (hΛ : 0 ≤ Λ) (hx₂ : ‖x₂‖ ≤ Λ) (hx₃ : ‖x₃‖ ≤ Λ) (hx₄ : ‖x₄‖ ≤ Λ) (hy₁ : ‖y₁‖ ≤ Λ)
    (hy₂ : ‖y₂‖ ≤ Λ) (hy₃ : ‖y₃‖ ≤ Λ) (hx₆ : ‖x₆‖ ≤ Λ) (hx₇ : ‖x₇‖ ≤ Λ) (hx₈ : ‖x₈‖ ≤ Λ)
    (hy₅ : ‖y₅‖ ≤ Λ) (hy₆ : ‖y₆‖ ≤ Λ) (hy₇ : ‖y₇‖ ≤ Λ)
    (h₁ : ‖x₁ - y₁‖ ≤ ε) (h₂ : ‖x₂ - y₂‖ ≤ ε) (h₃ : ‖x₃ - y₃‖ ≤ ε) (h₄ : ‖x₄ - y₄‖ ≤ ε)
    (h₅ : ‖x₅ - y₅‖ ≤ ε) (h₆ : ‖x₆ - y₆‖ ≤ ε) (h₇ : ‖x₇ - y₇‖ ≤ ε) (h₈ : ‖x₈ - y₈‖ ≤ ε) :
    ‖(x₁ * x₂ * x₃ * x₄ + x₅ * x₆ * x₇ * x₈) - (y₁ * y₂ * y₃ * y₄ + y₅ * y₆ * y₇ * y₈)‖ ≤
      8 * Λ ^ 3 * ε := by
  rw [add_sub_add_comm]
  refine (norm_add_le _ _).trans ((add_le_add
    (norm_prod4_sub_le hΛ hx₂ hx₃ hx₄ hy₁ hy₂ hy₃ h₁ h₂ h₃ h₄)
    (norm_prod4_sub_le hΛ hx₆ hx₇ hx₈ hy₅ hy₆ hy₇ h₅ h₆ h₇ h₈)).trans (le_of_eq (by ring)))

/-- `σ_p ≈ R/b`, `R = k_h(x_ps₁B) + bv([p=1] + bτ^p₀)t₂` (determinant `1 - k_hA ≈ b`). -/
theorem swP_div (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖swP b E X p‖ ≤ C ∧
        ‖swP b E X p - (SourceMixing.khOf b E X * (xP b E X p * SourceMixing.sOne b E X *
            SourceMixing.bOf b E X) + (b : ℂ) * SourceMixing.vOf b E X *
              (ind 1 p + (b : ℂ) * tauP b E X p 0) * SourceMixing.tTwo b E X 1) / b‖ ≤
          C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨Cw, Ww, hCw, hsys⟩ := wP_system hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  set K := Cb + Cw
  have hK : 0 ≤ K := by positivity
  set Kx := (Cw * ((1 + b ^ 2 * (Cb * Cb)) * K + b ^ 2 * K * dStar b) + K + b * K) / b
  have hKx : 0 ≤ Kx := by positivity
  refine ⟨d₀, Cw + Kx, max Wb Ww, hd₀, by positivity, fun W hW X hX hd p => ?_⟩
  obtain ⟨-, hv, -, -, -, -, hh1, hAd, -, -⟩ := hmb W (le_trans (le_max_left _ _) hW) X hX hd
  obtain ⟨hS, -, h3⟩ := hsys W (le_trans (le_max_right _ _) hW) X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have hhB : ‖SourceMixing.hOf b E X‖ ≤ Cb * Cb := by
    unfold SourceMixing.hOf; rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hv hv (norm_nonneg _) hCb
  set Ra := SourceMixing.khOf b E X * (xP b E X p * SourceMixing.sOne b E X *
    SourceMixing.bOf b E X) + (b : ℂ) * SourceMixing.vOf b E X *
      (ind 1 p + (b : ℂ) * tauP b E X p 0) * SourceMixing.tTwo b E X 1
  have h3' : ‖swP b E X p * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * SourceMixing.hOf b E X) *
      SourceMixing.aOf b E X) - (Ra + (b : ℂ) * SourceMixing.hOf b E X * 0)‖ ≤ K * e := by
    rw [mul_zero, add_zero]
    exact hKe Cw (by simp only [K]; linarith) _
      (h3.trans (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCw))
  have hc := yq_close hb0 hb he hK hS hhB (by simp) (hKe Cb (by simp only [K]; linarith) _ hh1)
    (hKe Cb (by simp only [K]; linarith) _ hAd) h3'
  rw [mul_zero, add_zero] at hc
  exact ⟨hS.trans (le_add_of_nonneg_right hKx),
    hc.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCw) he)⟩

/-- The right side `R` of the `w_p` system approaches its matched value `R_*`. -/
theorem swP_rhs_close (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖(SourceMixing.khOf b E X * xP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X +
            (b : ℂ) * SourceMixing.vOf b E X * (ind 1 p + (b : ℂ) * tauP b E X p 0) *
              SourceMixing.tTwo b E X 1) -
          ((((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * leadA b E s p * 1 * jetB b E s +
            (b : ℂ) * matchedA E * (ind 1 p + (b : ℂ) * leadU1 b E s p) * dStar b)‖ ≤
          C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₃, Cx, Wx, hd₃, hCx, hxm⟩ := xP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨d₄, Cu, Wu, hd₄, hCu, hum⟩ := tauP_zero_matched hA hb0 hb h1 h2 s hs
  obtain ⟨Cτ, Wτ, hCτ, hTb⟩ := tauP_blocks hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨Cb3, hCb3⟩ : ∃ x : ℝ, x = Cb * (Cb * Cb) := ⟨_, rfl⟩
  obtain ⟨nA, hnAd⟩ : ∃ x : ℝ, x = ‖leadA b E s 0‖ + ‖leadA b E s 1‖ := ⟨_, rfl⟩
  obtain ⟨nU, hnUd⟩ : ∃ x : ℝ, x = ‖leadU1 b E s 0‖ + ‖leadU1 b E s 1‖ := ⟨_, rfl⟩
  have h0b3 : 0 ≤ Cb3 := by rw [hCb3]; positivity
  have h0A : 0 ≤ nA := by rw [hnAd]; positivity
  have h0U : 0 ≤ nU := by rw [hnUd]; positivity
  have h0j := norm_nonneg (jetB b E s)
  have h0τ : 0 ≤ b * Cτ := by positivity
  have h0u : 0 ≤ b * nU := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 2 + Cx + Cs + Cb3 + nA + ‖jetB b E s‖ + Cb + (1 + b * Cτ) + Ct +
    (1 + b * nU) + dStar b := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cx + Cu := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ (min d₃ d₄)), 8 * Λ ^ 3 * K,
    max (max (max Wb Ws) (max Wt Wx)) (max Wu Wτ),
    lt_min (lt_min hd₀ hd₁) (lt_min hd₂ (lt_min hd₃ hd₄)), by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWb, hWs⟩, hWt, hWx⟩, hWu, hWτ⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3, hd4⟩ := hd
  obtain ⟨hM, hv, -, -, -, hva, hh1, -, -, hBj⟩ := hmb W hWb X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs X hX hd1
  have ht := htm W hWt X hX hd2
  obtain ⟨hx, hxA⟩ := hxm W hWx X hX hd3 p
  have hu := hum W hWu X hX hd4 p
  obtain ⟨hτb, -, -, -, -⟩ := hTb W hWτ X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have ha := norm_matchedA E h1 h2
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have kb : Cb ≤ K := by rw [hKd]; linarith
  have ks : Cs ≤ K := by rw [hKd]; linarith
  have kt : Ct ≤ K := by rw [hKd]; linarith
  have kx : Cx ≤ K := by rw [hKd]; linarith
  have ku : Cu ≤ K := by rw [hKd]; linarith
  have hkh : ‖SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2)‖ ≤ K * e := by
    have e' : SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) =
        (b : ℂ) ^ 2 * (SourceMixing.hOf b E X - 1) := by unfold SourceMixing.khOf; ring
    rw [e', norm_mul, norm_pow, nb]
    calc b ^ 2 * ‖SourceMixing.hOf b E X - 1‖ ≤ 1 * (Cb * e) :=
          mul_le_mul hb2 hh1 (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKe Cb kb _ le_rfl
  have hkP : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_pow, nb]
    linarith only [hb2, hb0]
  have hB' : ‖SourceMixing.bOf b E X‖ ≤ Cb3 := by
    rw [hCb3]
    exact (PassiveCovariance.norm_normTrace_le _).trans ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hM ((Matrix.l2_opNorm_mul _ _).trans (by
        rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hCb))
        (norm_nonneg _) hCb))
  have hcn : ‖ind 1 p + (b : ℂ) * tauP b E X p 0‖ ≤ 1 + b * Cτ :=
    (norm_add_le _ _).trans (add_le_add (norm_ind_le 1 p) (by
      rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (hτb 0) hb0.le))
  have hcSn : ‖ind 1 p + (b : ℂ) * leadU1 b E s p‖ ≤ 1 + b * nU :=
    (norm_add_le _ _).trans (add_le_add (norm_ind_le 1 p) (by
      rw [norm_mul, nb, hnUd]; exact mul_le_mul_of_nonneg_left (norm_le_sum_two _ p) hb0.le))
  have hcc : ‖(ind 1 p + (b : ℂ) * tauP b E X p 0) - (ind 1 p + (b : ℂ) * leadU1 b E s p)‖ ≤
      K * e := by
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, nb]
    calc b * ‖tauP b E X p 0 - leadU1 b E s p‖ ≤ 1 * (Cu * e) :=
          mul_le_mul hb1 hu (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKe Cu ku _ le_rfl
  have ht2 : ‖SourceMixing.tTwo b E X 1‖ ≤ Ct := by rw [tTwo_eq]; exact (ht 1 1).1
  have ht2d : ‖SourceMixing.tTwo b E X 1 - (dStar b : ℂ)‖ ≤ K * e := by
    rw [tTwo_eq, ← tStar_one_one hb0 hb]; exact hKe Ct kt _ (ht 1 1).2
  have hlA : ‖leadA b E s p‖ ≤ nA := by rw [hnAd]; exact norm_le_sum_two _ p
  have l1 : 2 ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l2 : Cx ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l3 : Cs ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l4 : Cb3 ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l5 : nA ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l6 : Cb ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l7 : 1 + b * Cτ ≤ Λ := by
    linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l8 : Ct ≤ Λ := by linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  have l9 : 1 + b * nU ≤ Λ := by
    linarith only [hΛd, hCx, hCs, h0b3, h0A, h0j, hCb, h0τ, hCt, h0u, hD]
  rw [mul_assoc (8 * Λ ^ 3)]
  exact norm_prod4_pair_sub_le hΛ (hx.trans l2) (hs1n.trans l3) (hB'.trans l4) (hkP.trans l1)
    (hlA.trans l5) (by rw [norm_one]; linarith) (hv.trans l6) (hcn.trans l7) (ht2.trans l8)
    (by rw [nb]; linarith) (by rw [ha]; linarith) (hcSn.trans l9) hkh (hKe Cx kx _ hxA)
    (hKe Cs ks _ hs1) (hKe Cb kb _ hBj) (by rw [sub_self, norm_zero]; positivity)
    (hKe Cb kb _ hva) hcc ht2d

/-- **Matched values of `σ_p`.** -/
theorem swP_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖swP b E X p‖ ≤ C ∧ ‖swP b E X p - leadSw b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, C₀, W₀, hd₀, hC₀, hdiv⟩ := swP_div hA hb0 hb h1 h2 s
  obtain ⟨d₁, C₁, W₁, hd₁, hC₁, hrhs⟩ := swP_rhs_close hA hb0 hb h1 h2 s hs
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
  rw [leadSw_eq hb0]
  set Ra := SourceMixing.khOf b E X * (xP b E X p * SourceMixing.sOne b E X *
    SourceMixing.bOf b E X) + (b : ℂ) * SourceMixing.vOf b E X *
      (ind 1 p + (b : ℂ) * tauP b E X p 0) * SourceMixing.tTwo b E X 1
  set Rs := (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * leadA b E s p * 1 * jetB b E s +
    (b : ℂ) * matchedA E * (ind 1 p + (b : ℂ) * leadU1 b E s p) * dStar b
  have eR : Ra = SourceMixing.khOf b E X * xP b E X p * SourceMixing.sOne b E X *
      SourceMixing.bOf b E X + (b : ℂ) * SourceMixing.vOf b E X *
        (ind 1 p + (b : ℂ) * tauP b E X p 0) * SourceMixing.tTwo b E X 1 := by
    simp only [Ra]; ring
  rw [← eR] at hr
  have hq2 : ‖Ra / b - Rs / b‖ ≤ C₁ / b * e := by
    rw [← sub_div, norm_div, nb]
    calc ‖Ra - Rs‖ / b ≤ (C₁ * e) / b := div_le_div_of_nonneg_right hr hb0.le
      _ = C₁ / b * e := by ring
  calc ‖swP b E X p - Rs / b‖ ≤ ‖swP b E X p - Ra / b‖ + ‖Ra / b - Rs / b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C₀ * e + C₁ / b * e := add_le_add hq hq2
    _ = (C₀ + C₁ / b) * e := by ring

end BlockBand.Transmission.PassiveCovariance
