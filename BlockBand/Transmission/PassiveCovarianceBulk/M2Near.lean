module

public import BlockBand.Transmission.PassiveCovarianceBulk.M6Near
public import BlockBand.Transmission.PassiveCovarianceBulk.WMatched
public import BlockBand.Transmission.PassiveCovariance.M2Near

/-!
# Bulk-uniform `m2_p`

The mean `m2_p = E[K̂𝒢P_p𝒢Π(K̂𝒢)ᴴ]₁₁ ↦ A_pR + σw_p`, with constants and `W₀` uniform in
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

/-- The block form of `m2_p`.
Bulk-uniform copy of `m2_block` (constants uniform on `bulkInterval κ`). -/
theorem m2_block_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
          SourceMixing.kmOf b E X * (xP b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))) 0 0 +
            swP b E X p • (blkAt (kHat b E X *
              matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := weightedBlock_bulk hA hb0 hb hκ 2 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  refine ⟨C, max W₁ WD, hC, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  have hT := hw W (le_trans (le_max_left _ _) hW) E hEκ X hX 2 le_rfl ![0, 3] (dM2 p) (norm_dM2_le p)
  rw [Fin.sum_univ_two] at hT
  set μ := layerLaw W b .oneBlockOnePort
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_M2]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_M2]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 0) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordAlpha_M20]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 1) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_M21]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 0) =
      fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_M20]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 1) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_M21]
  have e7 : matrixExpect μ (fun ω => kHat b E X * gRes b E X ω) =
      kHat b E X * matrixExpect μ (gRes b E X) := (SourceMixing.mul_matrixExpect' _ _ hG).symm
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_conjT, e7] at hT
  change ‖_ - SourceMixing.kmOf b E X * (ind 0 p • _ +
    (sig1 b (tauP b E X p 0) (tauP b E X p 1) • _ + swP b E X p • _))‖ ≤ _ at hT
  rw [← add_assoc, ← add_smul] at hT
  exact hT

/-- **`m2_p ↦ A_pR + σw_p`**: the index `(0, p)` of `MeanNearBulk alpFam leadAlp`.
Bulk-uniform copy of `alpNear_zero` (constants uniform on `bulkInterval κ`). -/
theorem alpNear_zero_bulk (hA : PassiveLayer.PassiveBoundsStatement) (p : Fin 2) :
    MeanNearBulk (ι := Unit) (fun _ => alpFam (0, p)) (fun _ => leadAlp (0, p)) := by
  intro b hb0 hb κ hκ
  obtain ⟨Cw, Ww, hCw, hwb⟩ := m2_block_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cb, Wb, hd₁, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₂, Cs, Ws, hd₂, hCs, hms⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨d₃, Cx, Wx, hd₃, hCx, hxm⟩ := xP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₄, CS, WS, hd₄, hCS, hsw⟩ := swP_matched_bulk hA hb0 hb hκ
  obtain ⟨Cm, Wm, hCm, hmix⟩ := mixedBlock_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨Cv, Wv, hCv, hwm⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  set ηi := (etaLow b κ)⁻¹
  have hη : 0 ≤ ηi := (inv_pos.mpr (etaLow_pos (by linarith) hκ)).le
  set c2 := Cx * Cm + CS * Cm
  set c3 := Cx * (Cs * (Cb * CK)) + CS * CK
  set C := Cw + CK * c2 + Cb * c3 + (Cx * Cs * (Cb * Cb) + Cx * Cs * Cb + Cx * Cb + Cx * ηi +
    CS * Cb + CS)
  refine ⟨min (min d₁ d₂) (min d₃ d₄), C,
    max (max (max Ww Wb) (max Ws Wx)) (max (max WS Wm) (max WK (max Wv 1))),
    lt_min (lt_min hd₁ hd₂) (lt_min hd₃ hd₄), by positivity,
      fun W hW E hEκ s hs X hX hδ _ u v => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWb⟩, hWs, hWx⟩, ⟨hWS, hWm⟩, hWK, hWv, hW1⟩ := hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  have hd := h0.trans hδ
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd1, hd2⟩, hd3, hd4⟩ := hd
  obtain ⟨hM, -, hR, hKM1, hMR, -⟩ := hmb W hWb E hEκ s X hX hd1
  replace hR := hR.trans (inv_etaZ_le_bulk hb hκ hEκ)
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs E hEκ s hs X hX hd2
  obtain ⟨hx, hxA⟩ := hxm W hWx E hEκ s hs X hX hd3 p
  obtain ⟨hS, hSl⟩ := hsw W hWS E hEκ s hs X hX hd4 p
  obtain ⟨hN, hKg⟩ := hmix W hWm E hEκ X hX
  obtain ⟨-, -, hKD, -⟩ := hK W hWK E hEκ X hX
  have hT := hwb W hWw E hEκ X hX p
  set μ := layerLaw W b .oneBlockOnePort
  set e := SourceMixing.epsOf b E s X
  have he0 : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hent : ∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj p * (gRes b E X ω *
      (portProj * (kHat b E X * gRes b E X ω)ᴴ))) : LayerMat W) α β) μ := fun α β => by
    have h := (hwm W hWv E hEκ X hX.posSemidef 3 le_rfl ![0, 0, 3] (dM24 p) (norm_dM24_le p)).1 α β
    have e' : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 3] (dM24 p) α β) =
        fun ω => (gRes b E X ω * (bProj p * (gRes b E X ω *
          (portProj * (kHat b E X * gRes b E X ω)ᴴ))) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GM2]
    rw [e'] at h; exact h
  have hint : ∀ i j, Integrable (fun ω => alpFam (0, p) b E W X ω i j) μ := fun i j => by
    simp only [alpFam_zero, Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hent k j).const_mul _
  show ‖(∫ ω, star (physVec u) ⬝ᵥ (alpFam (0, p) b E W X ω *ᵥ physVec v) ∂μ) -
    bilinear u (leadM2 b E s X p) v‖ ≤ _
  rw [integral_form _ hint]
  have ef : alpFam (0, p) b E W X = fun ω => kHat b E X * (gRes b E X ω * (bProj p *
      (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ)))) := funext (alpFam_zero p b E X)
  rw [ef, ← SourceMixing.mul_matrixExpect' _ _ hent]
  refine norm_bilinear_sub_le u v _ _ ?_
  set Y := blkAt (kHat b E X * matrixExpect μ (fun ω => gRes b E X ω * (bProj p *
    (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0
  set KM := SourceMixing.kmOf b E X
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  set N0 := blkAt (matrixExpect μ (fun ω => gRes b E X ω *
    (portProj * (kHat b E X * gRes b E X ω)ᴴ))) 0 0
  set Kg := blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0
  set s₁ := SourceMixing.sOne b E X
  set x := xP b E X p
  set S := swP b E X p
  have hKMn : ‖KM‖ ≤ CK := (norm_blkAt_le _ 0 0).trans hKD
  have hKMh : ‖KMᴴ‖ ≤ CK := by rw [Matrix.l2_opNorm_conjTranspose]; exact hKMn
  have hKM1h : ‖(KM - 1)ᴴ‖ ≤ Cb * e := by rw [Matrix.l2_opNorm_conjTranspose]; exact hKM1
  have hW2 : ∀ c : ℝ, 0 ≤ c → c / (W : ℝ) ^ 2 ≤ c * e := fun c hc =>
    div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hc
  set Q := x • N0 + S • Kgᴴ
  set Q1 := x • (s₁ • (M * KMᴴ)) + S • KMᴴ
  have eq : Y - leadM2 b E s X p = (Y - KM * Q) + KM * (Q - Q1) + (KM - 1) * Q1 +
      ((x * s₁) • (M * (KM - 1)ᴴ) + (x * (s₁ - 1)) • M + x • (M - R) + (x - leadA b E s p) • R +
        S • (KM - 1)ᴴ + (S - leadSw b E s p) • 1) := by
    simp only [leadM2, Q1, Matrix.sub_mul, Matrix.one_mul, conjTranspose_sub,
      conjTranspose_one, smul_sub, sub_smul, mul_sub, mul_one, smul_smul]
    abel
  have eQ : Q - Q1 = x • (N0 - s₁ • (M * KMᴴ)) + S • (Kgᴴ - KMᴴ) := by
    simp only [Q, Q1, smul_sub]; abel
  rw [eq]
  have t1 : ‖Y - KM * Q‖ ≤ Cw * e := hT.trans (hW2 Cw hCw)
  have hQ : ‖Q - Q1‖ ≤ c2 * e := by
    rw [eQ]
    have a1 : ‖x • (N0 - s₁ • (M * KMᴴ))‖ ≤ Cx * (Cm / (W : ℝ) ^ 2) :=
      (norm_smul_le _ _).trans (mul_le_mul hx hN (norm_nonneg _) hCx)
    have a2 : ‖S • (Kgᴴ - KMᴴ)‖ ≤ CS * (Cm / (W : ℝ) ^ 2) := by
      refine (norm_smul_le _ _).trans (mul_le_mul hS ?_ (norm_nonneg _) hCS)
      rw [SourceMixing.norm_conjTranspose_sub]; exact hKg
    refine (norm_add_le _ _).trans ((add_le_add a1 a2).trans ?_)
    rw [show Cx * (Cm / (W : ℝ) ^ 2) + CS * (Cm / (W : ℝ) ^ 2) = c2 / (W : ℝ) ^ 2 by
      simp only [c2]; ring]
    exact hW2 c2 (by positivity)
  have t2 : ‖KM * (Q - Q1)‖ ≤ CK * c2 * e :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKMn hQ (norm_nonneg _) hCK).trans
      (le_of_eq (by ring)))
  have hQ1 : ‖Q1‖ ≤ c3 :=
    (norm_add_le _ _).trans (add_le_add ((norm_smul_le _ _).trans (mul_le_mul hx
      ((norm_smul_le _ _).trans (mul_le_mul hs1n ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul hM hKMh (norm_nonneg _) hCb)) (by positivity) hCs))
      (by positivity) hCx)) ((norm_smul_le _ _).trans (mul_le_mul hS hKMh (norm_nonneg _) hCS)))
  have t3 : ‖(KM - 1) * Q1‖ ≤ Cb * c3 * e :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKM1 hQ1 (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  have hxs : ‖x * s₁‖ ≤ Cx * Cs := by rw [norm_mul]; exact mul_le_mul hx hs1n (norm_nonneg _) hCx
  have u1 : ‖(x * s₁) • (M * (KM - 1)ᴴ)‖ ≤ Cx * Cs * (Cb * Cb) * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hxs ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hM hKM1h (norm_nonneg _) hCb)) (by positivity) (by positivity)).trans
      (le_of_eq (by ring)))
  have hxs1 : ‖x * (s₁ - 1)‖ ≤ Cx * (Cs * e) := by
    rw [norm_mul]; exact mul_le_mul hx hs1 (norm_nonneg _) hCx
  have u2 : ‖(x * (s₁ - 1)) • M‖ ≤ Cx * Cs * Cb * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hxs1 hM (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  have u3 : ‖x • (M - R)‖ ≤ Cx * Cb * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hx hMR (norm_nonneg _) hCx).trans (le_of_eq (by ring)))
  have u4 : ‖(x - leadA b E s p) • R‖ ≤ Cx * ηi * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hxA hR (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  have u5 : ‖S • (KM - 1)ᴴ‖ ≤ CS * Cb * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hS hKM1h (norm_nonneg _) hCS).trans (le_of_eq (by ring)))
  have u6 : ‖(S - leadSw b E s p) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ CS * e :=
    (norm_smul_one_le _).trans hSl
  have hu : ‖(x * s₁) • (M * (KM - 1)ᴴ) + (x * (s₁ - 1)) • M + x • (M - R) +
      (x - leadA b E s p) • R + S • (KM - 1)ᴴ + (S - leadSw b E s p) • 1‖ ≤
      (Cx * Cs * (Cb * Cb) + Cx * Cs * Cb + Cx * Cb + Cx * ηi + CS * Cb + CS) * e := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add u1 u2)) u3)) u4)) u5)) u6).trans (le_of_eq (by ring))
  have hsum : ‖(Y - KM * Q) + KM * (Q - Q1) + (KM - 1) * Q1 +
      ((x * s₁) • (M * (KM - 1)ᴴ) + (x * (s₁ - 1)) • M + x • (M - R) + (x - leadA b E s p) • R +
        S • (KM - 1)ᴴ + (S - leadSw b E s p) • 1)‖ ≤ C * e := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add t1 t2)) t3)) hu).trans (le_of_eq ?_)
    simp only [C]; ring
  exact hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))

end BlockBand.Transmission.CovarianceBulk
