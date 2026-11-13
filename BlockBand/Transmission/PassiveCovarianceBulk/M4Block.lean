module

public import BlockBand.Transmission.PassiveCovarianceBulk.M2Near
public import BlockBand.Transmission.PassiveCovarianceBulk.ZMatched
public import BlockBand.Transmission.PassiveCovariance.M4Lead

/-!
# Bulk-uniform `m4_p` block and leading value

The block form and the leading value of the mean `m4_p`, with constants and `W₀` uniform in
`E ∈ bulkInterval κ`.
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

/-- **The block form of `m4_p`.**
Bulk-uniform copy of `m4_block` (constants uniform on `bulkInterval κ`). -/
theorem m4_block_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
              (portProj * (kHat b E X * gRes b E X ω)ᴴ))))))) 0 0 -
          SourceMixing.kmOf b E X * (SourceMixing.sOne b E X • blkAt (matrixExpect
              (layerLaw W b .oneBlockOnePort) (fun ω => (gRes b E X ω)ᴴ * (bProj p *
                (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 +
            svP b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))) 0 0 +
            szP b E X p • (blkAt (kHat b E X *
              matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := weightedBlock_bulk hA hb0 hb hκ 3 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  refine ⟨C, max W₁ WD, hC, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  have hT := hw W (le_trans (le_max_left _ _) hW) E hEκ X hX 3 le_rfl ![2, 0, 3] (dZ p) (norm_dZ_le p)
  rw [Fin.sum_univ_three] at hT
  set μ := layerLaw W b .oneBlockOnePort
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2, 0, 3] (dZ p)) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) := funext fun ω => by rw [wordVal_M4]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0, 3] (dZ p)) =
      fun ω => portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (kHat b E X * gRes b E X ω)ᴴ)))) := funext fun ω => by rw [wordVal_M4]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 3] (dZ p) 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_M40]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 3] (dZ p) 1) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordAlpha_M41]
  have e5 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 3] (dZ p) 2) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) := funext fun ω => by rw [wordAlpha_M42]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 3] (dZ p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (kHat b E X * gRes b E X ω)ᴴ))) := funext fun ω => by rw [wordGamma_M40]
  have e7 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 3] (dZ p) 1) =
      fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_M41]
  have e8 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 3] (dZ p) 2) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_M42]
  have e9 : matrixExpect μ (fun ω => kHat b E X * gRes b E X ω) =
      kHat b E X * matrixExpect μ (gRes b E X) := (SourceMixing.mul_matrixExpect' _ _ hG).symm
  obtain ⟨p0, -⟩ := blkAt_expect_portProj (μ := μ) (fun ω => (gRes b E X ω)ᴴ * (bProj p *
    (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))
  rw [e1, e2, e3, e4, e5, e6, e7, e8, p0, zero_add, blkAt_expect_conjT, e9] at hT
  exact hT

/-- **The leading value of `m4_p`.**
Bulk-uniform copy of `m4_lead` (constants uniform on `bulkInterval κ`). -/
theorem m4_lead_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖SourceMixing.kmOf b E X * (SourceMixing.sOne b E X • ((SourceMixing.mOf b E X)ᴴ *
            (rB b E X p • (SourceMixing.sOne b E X • (SourceMixing.mOf b E X *
              (SourceMixing.kmOf b E X)ᴴ)) + conj (svP b E X p) • (SourceMixing.kmOf b E X)ᴴ)) +
            svP b E X p • (SourceMixing.sOne b E X • (SourceMixing.mOf b E X *
              (SourceMixing.kmOf b E X)ᴴ)) + szP b E X p • (SourceMixing.kmOf b E X)ᴴ) -
          leadM4 b E s X p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₃, Cv, Wv, hd₃, hCv, hsv⟩ := svP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₄, Cz, Wz, hd₄, hCz, hsz⟩ := zP_matched_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hKk⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨nB, hnBd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  obtain ⟨nS, hnSd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  obtain ⟨nZ, hnZd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  have h0B : 0 ≤ nB := by rw [hnBd]; exact jetL_nonneg' b κ
  have h0S : 0 ≤ nS := by rw [hnSd]; exact jetL_nonneg' b κ
  have h0Z : 0 ≤ nZ := by rw [hnZd]; exact jetL_nonneg' b κ
  have h0η : 0 ≤ (etaLow b κ)⁻¹ := (inv_pos.mpr (etaLow_pos (by linarith) hκ)).le
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + Cs + Ct + Cv + Cz + Cb + CK + (etaLow b κ)⁻¹ + nB + nS + nZ :=
    ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cv + Cz := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ (min d₃ d₄)), Cb * (4 * Λ ^ 8) + 4 * (8 * Λ ^ 7 * K),
    max (max Wb Ws) (max Wt (max Wv (max Wz WK))),
    lt_min (lt_min hd₀ hd₁) (lt_min hd₂ (lt_min hd₃ hd₄)), by positivity,
      fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hLp := lead_le_jetL hb0 hb hκ hEκ hs p
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηi := inv_etaZ_le_bulk hb hκ hEκ
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, hWt, hWv, hWz, hWK⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3, hd4⟩ := hd
  obtain ⟨hM, -, hR, hKM1, hMR, -⟩ := hmb W hWb E hEκ s X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs E hEκ s hs X hX hd1
  obtain ⟨hrn, hrl⟩ := rB_close hb0 hb p (htm W hWt E hEκ s X hX hd2)
  obtain ⟨hSn, hSl⟩ := hsv W hWv E hEκ s hs X hX hd3 p
  obtain ⟨hZn, hZl⟩ := hsz W hWz E hEκ s hs X hX hd4 p
  obtain ⟨-, -, hKD, -⟩ := hKk W hWK E hEκ X hX
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
    linarith only [hΛd, hCs, hCt, hCv, hCz, hCb, hCK, h0η, h0B, h0S, h0Z, hηi]
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
  have hlB : ‖leadB b p‖ ≤ Λ := (by rw [hnBd]; exact hLp.2.2.2.1 : ‖leadB b p‖ ≤ nB).trans l9
  have hlS : ‖leadSv b E s p‖ ≤ Λ :=
    (by rw [hnSd]; exact hLp.2.2.2.2.2.2.1 : ‖leadSv b E s p‖ ≤ nS).trans l10
  have hlZ : ‖leadSz b E s p‖ ≤ Λ :=
    (by rw [hnZd]; exact hLp.2.2.2.2.2.2.2.2.2 : ‖leadSz b E s p‖ ≤ nZ).trans l11
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

end BlockBand.Transmission.CovarianceBulk
