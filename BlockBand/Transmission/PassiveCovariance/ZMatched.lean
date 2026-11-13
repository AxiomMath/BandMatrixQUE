module

public import BlockBand.Transmission.PassiveCovariance.VMatchedTr

/-!
# Matched values of `σz_p = σ₁(z^p)`: `σz_p ↦ leadSz p`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X` with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on
`b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p`.

* `leadSz_eq`: `leadSz p = R_*/b`, `R_* = k_*I_* + b·a·d_*·conj(v1Star p) + b(ba)·leadV1 p·d_*`,
  `I_* = B_pC_* + conj σv_p·conj B_* + σv_pB_*` (uses `a·ā = 1`; this checks `leadSz` of
  `LeadAlgebra` against the Lean system).
* `zP_div` (`σz_p ≈ R/b`, determinant `1 - k_hA ≈ b`), `zI_close` (`I_z ≈ I_*`).

The sibling module proves `zP_rhs_close` (`R ≈ R_*`) and `zP_matched`: `|σz_p| ≤ C`,
`|σz_p - leadSz p| ≤ C·epsOf`.
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

/-- `I_* = B_pC_* + conj σv_p·conj B_* + σv_pB_*` (as three products of four factors). -/
def zIStar (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  1 * 1 * leadB b p * jetC b E s + 1 * conj (leadSv b E s p) * conj (jetB b E s) * 1 +
    leadSv b E s p * 1 * jetB b E s * 1

/-- `R_*`, the matched right side of the `z_p` system. -/
def zRStar (b E : ℝ) (s : ℂ) (p : Fin 2) : ℂ :=
  (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p +
    ((b : ℂ) * matchedA E * (dStar b : ℂ) * conj (v1Star b E s p) +
      (b : ℂ) * ((b : ℂ) * matchedA E) * leadV1 b E s p * (dStar b : ℂ))

theorem leadSz_eq {b : ℝ} (hb0 : 0 < b) {E : ℝ} (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (p : Fin 2) :
    leadSz b E s p = zRStar b E s p / b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have ha0 : matchedA E ≠ 0 := matchedA_ne_zero E h1 h2
  have ha2 : matchedA E * conj (matchedA E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_matchedA E h1 h2]; norm_num
  have hca : conj (matchedA E) = (matchedA E)⁻¹ := eq_inv_of_mul_eq_one_right ha2
  have htS : conj (tStar b 1 p) = tStar b 1 p := by
    rw [tStar_one_eq hb0 p]; fin_cases p <;> simp [leadInd, leadR1]
  have hind : leadInd p + (b : ℂ) * leadR1 b p = tStar b 1 p := (tStar_one_eq hb0 p).symm
  have hσ : ((sigmaPlus b : ℝ) : ℂ) = (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) / b := by
    simp only [sigmaPlus, kPlus]; push_cast; ring
  rw [eq_div_iff hb']
  simp only [leadSz, zRStar, zIStar, v1Star, hind, hσ, map_add, map_mul, map_one,
    Complex.conj_ofReal, htS, hca]
  field_simp
  ring

theorem norm_cqOf_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C : ℝ}
    (hM : ‖SourceMixing.mOf b E X‖ ≤ C) : ‖cqOf b E X‖ ≤ C * (C * (C * C)) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hM
  have hMh : ‖(SourceMixing.mOf b E X)ᴴ‖ ≤ C := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
  exact (norm_normTrace_le _).trans ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM
    ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hMh ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hM hMh (norm_nonneg _) hC)) (norm_nonneg _) hC)) (norm_nonneg _) hC))

theorem norm_conj_sub (x y : ℂ) : ‖conj x - conj y‖ = ‖x - y‖ := by
  rw [← map_sub, Complex.norm_conj]

/-- `σz_p ≈ R/b`. -/
theorem zP_div (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧
        ‖szP b E X p - (SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
            (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
              conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
              svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              conj (vP b E X p 1) +
            (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 *
              SourceMixing.tTwo b E X 1) / b‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨Cw, Ww, hCw, hsys⟩ := zP_system hA hb0 hb h1 h2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  set K := Cb + Cw
  have hK : 0 ≤ K := by positivity
  set Kx := (Cw * ((1 + b ^ 2 * (Cb * Cb)) * K + b ^ 2 * K * dStar b) + K + b * K) / b
  have hKx : 0 ≤ Kx := by positivity
  refine ⟨d₀, Cw + Kx, max Wb Ww, hd₀, by positivity, fun W hW X hX hd p => ?_⟩
  obtain ⟨-, hv, -, -, -, -, hh1, hAd, -, -⟩ := hmb W (le_trans (le_max_left _ _) hW) X hX hd
  obtain ⟨hS, h3⟩ := hsys W (le_trans (le_max_right _ _) hW) X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have hhB : ‖SourceMixing.hOf b E X‖ ≤ Cb * Cb := by
    unfold SourceMixing.hOf; rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hv hv (norm_nonneg _) hCb
  set Ra := SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
    (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
    (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
      conj (vP b E X p 1) +
    (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1
  have h3' : ‖szP b E X p * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * SourceMixing.hOf b E X) *
      SourceMixing.aOf b E X) - (Ra + (b : ℂ) * SourceMixing.hOf b E X * 0)‖ ≤ K * e := by
    rw [mul_zero, add_zero]
    exact hKe Cw (by simp only [K]; linarith) _
      (h3.trans (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCw))
  have hc := yq_close hb0 hb he hK hS hhB (by simp) (hKe Cb (by simp only [K]; linarith) _ hh1)
    (hKe Cb (by simp only [K]; linarith) _ hAd) h3'
  rw [mul_zero, add_zero] at hc
  exact ⟨hS.trans (le_add_of_nonneg_right hKx),
    hc.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCw) he)⟩

/-- `I_z ≈ I_*` (and `|I_z| ≤ C`). -/
theorem zI_close (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
            conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
            svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X‖ ≤ C ∧
        ‖(SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
            conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
            svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) - zIStar b E s p‖ ≤
          C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₃, Cv, Wv, hd₃, hCv, hsv⟩ := svP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨d₄, Cq, Wq, hd₄, hCq, hcq⟩ := cq_matched hA hb0 hb h1 h2 s
  obtain ⟨nB, hnBd⟩ : ∃ x : ℝ, x = ‖leadB b 0‖ + ‖leadB b 1‖ := ⟨_, rfl⟩
  obtain ⟨nS, hnSd⟩ : ∃ x : ℝ, x = ‖leadSv b E s 0‖ + ‖leadSv b E s 1‖ := ⟨_, rfl⟩
  have h0B : 0 ≤ nB := by rw [hnBd]; positivity
  have h0S : 0 ≤ nS := by rw [hnSd]; positivity
  have h0j := norm_nonneg (jetB b E s)
  have h0c := norm_nonneg (jetC b E s)
  have hb3 : 0 ≤ Cb * (Cb * Cb) := by positivity
  have hb4 : 0 ≤ Cb * (Cb * (Cb * Cb)) := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + Cs + Ct + Cv + Cb * (Cb * Cb) + Cb * (Cb * (Cb * Cb)) + nB +
    nS + ‖jetB b E s‖ + ‖jetC b E s‖ := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cv + Cq := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ (min d₃ d₄)),
    Cs * (Cs * (1 + Ct) * (Cb * (Cb * (Cb * Cb))) + Cv * (Cb * (Cb * Cb))) +
      Cv * Cs * (Cb * (Cb * Cb)) + 12 * Λ ^ 3 * K,
    max (max Wb Ws) (max Wt (max Wv Wq)), lt_min (lt_min hd₀ hd₁) (lt_min hd₂ (lt_min hd₃ hd₄)),
    by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, hWt, hWv, hWq⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3, hd4⟩ := hd
  obtain ⟨hM, -, -, -, -, -, -, -, -, hBj⟩ := hmb W hWb X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs X hX hd1
  obtain ⟨hrn, hrl⟩ := rB_close hb0 hb p (htm W hWt X hX hd2)
  obtain ⟨hSn, hSl⟩ := hsv W hWv X hX hd3 p
  have hCql := hcq W hWq X hX hd4
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
  have kq : Cq ≤ K := by rw [hKd]; linarith
  have hB := norm_bOf_le hM
  have hcqn := norm_cqOf_le (b := b) (E := E) (X := X) hM
  have hlB : ‖leadB b p‖ ≤ nB := by rw [hnBd]; exact norm_le_sum_two _ p
  have hlS : ‖leadSv b E s p‖ ≤ nS := by rw [hnSd]; exact norm_le_sum_two _ p
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l2 : Cs ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l3 : 1 + Ct ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l4 : Cv ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l5 : Cb * (Cb * Cb) ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l6 : Cb * (Cb * (Cb * Cb)) ≤ Λ := by
    linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l7 : nB ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l8 : nS ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l9 : ‖jetB b E s‖ ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have h1n : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hS1 := hKe Cs ks _ hs1
  have hP := norm_prod4_pair_sub_le (x₁ := SourceMixing.sOne b E X) (x₂ := SourceMixing.sOne b E X)
    (x₃ := rB b E X p) (x₄ := cqOf b E X) (y₁ := 1) (y₂ := 1) (y₃ := leadB b p) (y₄ := jetC b E s)
    (x₅ := SourceMixing.sOne b E X) (x₆ := conj (svP b E X p)) (x₇ := conj (SourceMixing.bOf b E X))
    (x₈ := 1) (y₅ := 1) (y₆ := conj (leadSv b E s p)) (y₇ := conj (jetB b E s)) (y₈ := 1) hΛ
    (hs1n.trans l2) (hrn.trans l3) (hcqn.trans l6) h1n h1n (hlB.trans l7)
    (by rw [Complex.norm_conj]; exact hSn.trans l4) (by rw [Complex.norm_conj]; exact hB.trans l5) h1n
    h1n (by rw [Complex.norm_conj]; exact hlS.trans l8) (by rw [Complex.norm_conj]; exact l9)
    hS1 hS1 (hKe Ct kt _ hrl) (hKe Cq kq _ hCql) hS1
    (by rw [norm_conj_sub]; exact hKe Cv kv _ hSl) (by rw [norm_conj_sub]; exact hKe Cb kb _ hBj) hz
  have hQ := norm_prod4_sub_le (x₁ := svP b E X p) (x₂ := SourceMixing.sOne b E X)
    (x₃ := SourceMixing.bOf b E X) (x₄ := 1) (y₁ := leadSv b E s p) (y₂ := 1) (y₃ := jetB b E s)
    (y₄ := 1) hΛ (hs1n.trans l2) (hB.trans l5) h1n (hlS.trans l8) h1n l9 (hKe Cv kv _ hSl) hS1
    (hKe Cb kb _ hBj) hz
  have hb' : ‖conj (svP b E X p) * conj (SourceMixing.bOf b E X)‖ ≤ Cv * (Cb * (Cb * Cb)) := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_conj]; exact mul_le_mul hSn hB (norm_nonneg _) hCv
  have h12 : 0 ≤ 12 * Λ ^ 3 * K := by positivity
  have hI : ‖SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X‖ ≤
      Cs * (Cs * (1 + Ct) * (Cb * (Cb * (Cb * Cb))) + Cv * (Cb * (Cb * Cb))) +
        Cv * Cs * (Cb * (Cb * Cb)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      refine mul_le_mul hs1n ((norm_add_le _ _).trans (add_le_add ?_ hb')) (by positivity) hCs
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hs1n hrn (norm_nonneg _) hCs) hcqn (norm_nonneg _) (by positivity)
    · rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hSn hs1n (norm_nonneg _) hCv) hB (norm_nonneg _) (by positivity)
  refine ⟨hI.trans (le_add_of_nonneg_right h12), ?_⟩
  have eq : (SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) - zIStar b E s p =
      ((SourceMixing.sOne b E X * SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
        SourceMixing.sOne b E X * conj (svP b E X p) * conj (SourceMixing.bOf b E X) * 1) -
        (1 * 1 * leadB b p * jetC b E s + 1 * conj (leadSv b E s p) * conj (jetB b E s) * 1)) +
      (svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X * 1 -
        leadSv b E s p * 1 * jetB b E s * 1) := by
    simp only [zIStar]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add hP hQ).trans ?_)
  have : 0 ≤ Cs * (Cs * (1 + Ct) * (Cb * (Cb * (Cb * Cb))) + Cv * (Cb * (Cb * Cb))) +
      Cv * Cs * (Cb * (Cb * Cb)) := by positivity
  rw [show 8 * Λ ^ 3 * (K * e) + 4 * Λ ^ 3 * (K * e) = 12 * Λ ^ 3 * K * e by ring]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left this) he

end BlockBand.Transmission.PassiveCovariance
