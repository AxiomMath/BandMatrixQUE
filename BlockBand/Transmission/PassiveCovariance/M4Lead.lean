module

public import BlockBand.Transmission.PassiveCovariance.M4Block

/-!
# The leading value of `m4_p`: `KM·Q₂ ≈ leadM4 p`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X` with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on
`b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p`. Operator norm.

* `smul4_close`, `norm_smul4_le` (algebra: `c•A` with `c`, `A` products of four approximate factors).
* **`m4_lead`**: with `Q₂ = s₁Mᴴ(rB_ps₁M·KMᴴ + conj S_p·KMᴴ) + S_ps₁M·KMᴴ + σz_p·KMᴴ`,
  `‖KM·Q₂ - (B_pR*R + conj σv_p R* + σv_pR + σz*_p)‖ ≤ C·epsOf` (`KM ≈ 1`, `M ≈ R`, `s₁ ≈ 1`,
  `rB_p ≈ B_p`, `S_p ≈ σv_p`, `σz_p ≈ leadSz p`).
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

theorem norm_mul4_le {A₁ A₂ A₃ A₄ : Matrix (Fin W) (Fin W) ℂ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h₁ : ‖A₁‖ ≤ Λ) (h₂ : ‖A₂‖ ≤ Λ) (h₃ : ‖A₃‖ ≤ Λ) (h₄ : ‖A₄‖ ≤ Λ) :
    ‖A₁ * A₂ * A₃ * A₄‖ ≤ Λ ^ 4 := by
  refine (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul h₁ h₂ (norm_nonneg _) hΛ)) h₃
      (norm_nonneg _) (by positivity))) h₄ (norm_nonneg _) (by positivity)).trans (le_of_eq ?_))
  ring

theorem norm_prod4_le {x₁ x₂ x₃ x₄ : ℂ} {Λ : ℝ} (hΛ : 0 ≤ Λ) (h₁ : ‖x₁‖ ≤ Λ) (h₂ : ‖x₂‖ ≤ Λ)
    (h₃ : ‖x₃‖ ≤ Λ) (h₄ : ‖x₄‖ ≤ Λ) : ‖x₁ * x₂ * x₃ * x₄‖ ≤ Λ ^ 4 := by
  simp only [norm_mul]
  have := norm_nonneg x₁; have := norm_nonneg x₂; have := norm_nonneg x₃
  calc ‖x₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ ≤ Λ * Λ * Λ * Λ := by gcongr
    _ = Λ ^ 4 := by ring

/-- `c • A` with `c` and `A` products of four approximate factors. -/
theorem smul4_close {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℂ} {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Matrix (Fin W) (Fin W) ℂ}
    {Λ ε : ℝ} (hΛ : 0 ≤ Λ)
    (hx₂ : ‖x₂‖ ≤ Λ) (hx₃ : ‖x₃‖ ≤ Λ) (hx₄ : ‖x₄‖ ≤ Λ)
    (hy₁ : ‖y₁‖ ≤ Λ) (hy₂ : ‖y₂‖ ≤ Λ) (hy₃ : ‖y₃‖ ≤ Λ) (hy₄ : ‖y₄‖ ≤ Λ)
    (hA₁ : ‖A₁‖ ≤ Λ) (hA₂ : ‖A₂‖ ≤ Λ) (hA₃ : ‖A₃‖ ≤ Λ) (hA₄ : ‖A₄‖ ≤ Λ)
    (hB₁ : ‖B₁‖ ≤ Λ) (hB₂ : ‖B₂‖ ≤ Λ) (hB₃ : ‖B₃‖ ≤ Λ)
    (e₁ : ‖x₁ - y₁‖ ≤ ε) (e₂ : ‖x₂ - y₂‖ ≤ ε) (e₃ : ‖x₃ - y₃‖ ≤ ε) (e₄ : ‖x₄ - y₄‖ ≤ ε)
    (f₁ : ‖A₁ - B₁‖ ≤ ε) (f₂ : ‖A₂ - B₂‖ ≤ ε) (f₃ : ‖A₃ - B₃‖ ≤ ε) (f₄ : ‖A₄ - B₄‖ ≤ ε) :
    ‖(x₁ * x₂ * x₃ * x₄) • (A₁ * A₂ * A₃ * A₄) - (y₁ * y₂ * y₃ * y₄) • (B₁ * B₂ * B₃ * B₄)‖ ≤
      8 * Λ ^ 7 * ε := by
  have hc := norm_prod4_sub_le hΛ hx₂ hx₃ hx₄ hy₁ hy₂ hy₃ e₁ e₂ e₃ e₄
  have hA := norm_mul4_sub_le _ _ _ _ _ _ _ _ hA₂ hA₃ hA₄ hB₁ hB₂ hB₃ f₁ f₂ f₃ f₄
  have nA := norm_mul4_le hΛ hA₁ hA₂ hA₃ hA₄
  have ny := norm_prod4_le hΛ hy₁ hy₂ hy₃ hy₄
  have e : (x₁ * x₂ * x₃ * x₄) • (A₁ * A₂ * A₃ * A₄) - (y₁ * y₂ * y₃ * y₄) • (B₁ * B₂ * B₃ * B₄) =
      (x₁ * x₂ * x₃ * x₄ - y₁ * y₂ * y₃ * y₄) • (A₁ * A₂ * A₃ * A₄) +
        (y₁ * y₂ * y₃ * y₄) • (A₁ * A₂ * A₃ * A₄ - B₁ * B₂ * B₃ * B₄) := by
    rw [sub_smul, smul_sub]; abel
  rw [e]
  have hε : 0 ≤ ε := (norm_nonneg _).trans e₁
  refine (norm_add_le _ _).trans ((add_le_add ((norm_smul_le _ _).trans
    (mul_le_mul hc nA (norm_nonneg _) (by positivity))) ((norm_smul_le _ _).trans
    (mul_le_mul ny hA (norm_nonneg _) (by positivity)))).trans (le_of_eq ?_))
  ring

theorem norm_smul4_le {x₁ x₂ x₃ x₄ : ℂ} {A₁ A₂ A₃ A₄ : Matrix (Fin W) (Fin W) ℂ} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hx₁ : ‖x₁‖ ≤ Λ) (hx₂ : ‖x₂‖ ≤ Λ) (hx₃ : ‖x₃‖ ≤ Λ) (hx₄ : ‖x₄‖ ≤ Λ)
    (hA₁ : ‖A₁‖ ≤ Λ) (hA₂ : ‖A₂‖ ≤ Λ) (hA₃ : ‖A₃‖ ≤ Λ) (hA₄ : ‖A₄‖ ≤ Λ) :
    ‖(x₁ * x₂ * x₃ * x₄) • (A₁ * A₂ * A₃ * A₄)‖ ≤ Λ ^ 8 :=
  (norm_smul_le _ _).trans ((mul_le_mul (norm_prod4_le hΛ hx₁ hx₂ hx₃ hx₄)
    (norm_mul4_le hΛ hA₁ hA₂ hA₃ hA₄) (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring)))

/-- **The leading value of `m4_p`.** -/
theorem m4_lead (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖SourceMixing.kmOf b E X * (SourceMixing.sOne b E X • ((SourceMixing.mOf b E X)ᴴ *
            (rB b E X p • (SourceMixing.sOne b E X • (SourceMixing.mOf b E X *
              (SourceMixing.kmOf b E X)ᴴ)) + conj (svP b E X p) • (SourceMixing.kmOf b E X)ᴴ)) +
            svP b E X p • (SourceMixing.sOne b E X • (SourceMixing.mOf b E X *
              (SourceMixing.kmOf b E X)ᴴ)) + szP b E X p • (SourceMixing.kmOf b E X)ᴴ) -
          leadM4 b E s X p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₃, Cv, Wv, hd₃, hCv, hsv⟩ := svP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨d₄, Cz, Wz, hd₄, hCz, hsz⟩ := zP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨CK, WK, hCK, hKk⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨nB, hnBd⟩ : ∃ x : ℝ, x = ‖leadB b 0‖ + ‖leadB b 1‖ := ⟨_, rfl⟩
  obtain ⟨nS, hnSd⟩ : ∃ x : ℝ, x = ‖leadSv b E s 0‖ + ‖leadSv b E s 1‖ := ⟨_, rfl⟩
  obtain ⟨nZ, hnZd⟩ : ∃ x : ℝ, x = ‖leadSz b E s 0‖ + ‖leadSz b E s 1‖ := ⟨_, rfl⟩
  have h0B : 0 ≤ nB := by rw [hnBd]; positivity
  have h0S : 0 ≤ nS := by rw [hnSd]; positivity
  have h0Z : 0 ≤ nZ := by rw [hnZd]; positivity
  have h0η : 0 ≤ (etaZ b E)⁻¹ := (inv_pos.mpr hη).le
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + Cs + Ct + Cv + Cz + Cb + CK + (etaZ b E)⁻¹ + nB + nS + nZ :=
    ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cv + Cz := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ (min d₃ d₄)), Cb * (4 * Λ ^ 8) + 4 * (8 * Λ ^ 7 * K),
    max (max Wb Ws) (max Wt (max Wv (max Wz WK))),
    lt_min (lt_min hd₀ hd₁) (lt_min hd₂ (lt_min hd₃ hd₄)), by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, hWt, hWv, hWz, hWK⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3, hd4⟩ := hd
  obtain ⟨hM, -, hR, hKM1, hMR, -⟩ := hmb W hWb X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs X hX hd1
  obtain ⟨hrn, hrl⟩ := rB_close hb0 hb p (htm W hWt X hX hd2)
  obtain ⟨hSn, hSl⟩ := hsv W hWv X hX hd3 p
  obtain ⟨hZn, hZl⟩ := hsz W hWz X hX hd4 p
  obtain ⟨-, -, hKD, -⟩ := hKk W hWK X hX
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
  have kz : Cz ≤ K := by rw [hKd]; linarith
  have l1 : (1 : ℝ) ≤ Λ := by
    linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l2 : Cs ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l3 : 1 + Ct ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l4 : Cv ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l5 : Cz ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l6 : Cb ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l7 : CK ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l8 : (etaZ b E)⁻¹ ≤ Λ := by
    linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l9 : nB ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l10 : nS ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  have l11 : nZ ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z]
  set KM := SourceMixing.kmOf b E X
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set σ := szP b E X p
  set r := rB b E X p
  have h1c : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have h1m : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ Λ := norm_one_matrix_le.trans l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hzm : ‖(1 : Matrix (Fin W) (Fin W) ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hMn : ‖M‖ ≤ Λ := hM.trans l6
  have hMh : ‖Mᴴ‖ ≤ Λ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hMn
  have hRn : ‖R‖ ≤ Λ := hR.trans l8
  have hRh : ‖Rᴴ‖ ≤ Λ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hRn
  have hKh : ‖KMᴴ‖ ≤ Λ := by
    rw [Matrix.l2_opNorm_conjTranspose]; exact ((norm_blkAt_le _ 0 0).trans hKD).trans l7
  have dMR : ‖M - R‖ ≤ K * e := hKe Cb kb _ hMR
  have dMRh : ‖Mᴴ - Rᴴ‖ ≤ K * e := by rw [SourceMixing.norm_conjTranspose_sub]; exact dMR
  have dK : ‖KMᴴ - 1‖ ≤ K * e := by
    rw [← conjTranspose_one, SourceMixing.norm_conjTranspose_sub]; exact hKe Cb kb _ hKM1
  have ds : ‖s₁ - 1‖ ≤ K * e := hKe Cs ks _ hs1
  have hQ2 : s₁ • (Mᴴ * (r • (s₁ • (M * KMᴴ)) + conj S • KMᴴ)) + S • (s₁ • (M * KMᴴ)) + σ • KMᴴ =
      (s₁ * r * s₁ * 1) • (Mᴴ * M * KMᴴ * 1) + (s₁ * conj S * 1 * 1) • (Mᴴ * KMᴴ * 1 * 1) +
        (S * s₁ * 1 * 1) • (M * KMᴴ * 1 * 1) + (σ * 1 * 1 * 1) • (KMᴴ * 1 * 1 * 1) := by
    simp only [mul_one, Matrix.mul_add, Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
    module
  have hL : leadM4 b E s X p = (1 * leadB b p * 1 * 1) • (Rᴴ * R * 1 * 1) +
      (1 * conj (leadSv b E s p) * 1 * 1) • (Rᴴ * 1 * 1 * 1) +
      (leadSv b E s p * 1 * 1 * 1) • (R * 1 * 1 * 1) + (leadSz b E s p * 1 * 1 * 1) • (1 * 1 * 1 * 1) := by
    simp only [leadM4, mul_one, one_mul]; rfl
  have hlB : ‖leadB b p‖ ≤ Λ := (by rw [hnBd]; exact norm_le_sum_two _ p : ‖leadB b p‖ ≤ nB).trans l9
  have hlS : ‖leadSv b E s p‖ ≤ Λ :=
    (by rw [hnSd]; exact norm_le_sum_two _ p : ‖leadSv b E s p‖ ≤ nS).trans l10
  have hlZ : ‖leadSz b E s p‖ ≤ Λ :=
    (by rw [hnZd]; exact norm_le_sum_two _ p : ‖leadSz b E s p‖ ≤ nZ).trans l11
  have hcS : ‖conj S‖ ≤ Λ := by rw [Complex.norm_conj]; exact hSn.trans l4
  have hclS : ‖conj (leadSv b E s p)‖ ≤ Λ := by rw [Complex.norm_conj]; exact hlS
  have t1 := smul4_close hΛ (hrn.trans l3) (hs1n.trans l2) h1c h1c hlB h1c h1c
    hMh hMn hKh h1m hRh hRn h1m ds (hKe Ct kt _ hrl) ds hz dMRh dMR dK hzm
  have t2 := smul4_close hΛ hcS h1c h1c h1c hclS h1c h1c hMh hKh h1m h1m hRh h1m h1m
    ds (by rw [norm_conj_sub]; exact hKe Cv kv _ hSl) hz hz dMRh dK hzm hzm
  have t3 := smul4_close hΛ (hs1n.trans l2) h1c h1c hlS h1c h1c h1c hMn hKh h1m h1m
    hRn h1m h1m (hKe Cv kv _ hSl) ds hz hz dMR dK hzm hzm
  have t4 := smul4_close hΛ h1c h1c h1c hlZ h1c h1c h1c hKh h1m h1m h1m h1m h1m h1m
    (hKe Cz kz _ hZl) hz hz hz dK hzm hzm hzm
  have nQ : ‖(s₁ * r * s₁ * 1) • (Mᴴ * M * KMᴴ * 1) + (s₁ * conj S * 1 * 1) • (Mᴴ * KMᴴ * 1 * 1) +
      (S * s₁ * 1 * 1) • (M * KMᴴ * 1 * 1) + (σ * 1 * 1 * 1) • (KMᴴ * 1 * 1 * 1)‖ ≤ 4 * Λ ^ 8 := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
      (norm_smul4_le hΛ (hs1n.trans l2) (hrn.trans l3) (hs1n.trans l2) h1c hMh hMn hKh h1m)
      (norm_smul4_le hΛ (hs1n.trans l2) hcS h1c h1c hMh hKh h1m h1m)))
      (norm_smul4_le hΛ (hSn.trans l4) (hs1n.trans l2) h1c h1c hMn hKh h1m h1m)))
      (norm_smul4_le hΛ (hZn.trans l5) h1c h1c h1c hKh h1m h1m h1m)).trans (le_of_eq (by ring))
  rw [hQ2, hL]
  set Q := (s₁ * r * s₁ * 1) • (Mᴴ * M * KMᴴ * 1) + (s₁ * conj S * 1 * 1) • (Mᴴ * KMᴴ * 1 * 1) +
      (S * s₁ * 1 * 1) • (M * KMᴴ * 1 * 1) + (σ * 1 * 1 * 1) • (KMᴴ * 1 * 1 * 1)
  have eq : KM * Q - ((1 * leadB b p * 1 * 1) • (Rᴴ * R * 1 * 1) +
      (1 * conj (leadSv b E s p) * 1 * 1) • (Rᴴ * 1 * 1 * 1) +
      (leadSv b E s p * 1 * 1 * 1) • (R * 1 * 1 * 1) + (leadSz b E s p * 1 * 1 * 1) • (1 * 1 * 1 * 1)) =
      (KM - 1) * Q + (((s₁ * r * s₁ * 1) • (Mᴴ * M * KMᴴ * 1) -
        (1 * leadB b p * 1 * 1) • (Rᴴ * R * 1 * 1)) +
      ((s₁ * conj S * 1 * 1) • (Mᴴ * KMᴴ * 1 * 1) - (1 * conj (leadSv b E s p) * 1 * 1) • (Rᴴ * 1 * 1 * 1)) +
      ((S * s₁ * 1 * 1) • (M * KMᴴ * 1 * 1) - (leadSv b E s p * 1 * 1 * 1) • (R * 1 * 1 * 1)) +
      ((σ * 1 * 1 * 1) • (KMᴴ * 1 * 1 * 1) - (leadSz b E s p * 1 * 1 * 1) • (1 * 1 * 1 * 1))) := by
    simp only [Q, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [eq]
  have tK : ‖(KM - 1) * Q‖ ≤ Cb * (4 * Λ ^ 8) * e :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKM1 nQ (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  refine (norm_add_le _ _).trans ((add_le_add tK ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4))).trans
    (le_of_eq ?_))
  ring

end BlockBand.Transmission.PassiveCovariance
