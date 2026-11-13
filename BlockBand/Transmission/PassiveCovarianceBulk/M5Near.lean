module

public import BlockBand.Transmission.PassiveCovarianceBulk.Props
public import BlockBand.Transmission.PassiveCovarianceBulk.Matched1
public import BlockBand.Transmission.PassiveCovarianceBulk.JetBounds
public import BlockBand.Transmission.PassiveCovariance.M5Near

/-!
# Bulk-uniform `m5_p`

The mean `m5_p = E[K̂𝒢P_p𝒢]₁₁ ↦ A_pR`, with constants and `W₀` uniform in `E ∈ bulkInterval κ`.
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

/-- The block form of `m5_p`.
Bulk-uniform copy of `m5_block` (constants uniform on `bulkInterval κ`). -/
theorem m5_block_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))) 0 0 -
          SourceMixing.kmOf b E X * (xP b E X p •
            blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := weightedBlock_bulk hA hb0 hb hκ 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  refine ⟨C, max W₁ WD, hC, fun W hW E hEκ X hX p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W (le_trans (le_max_right _ _) hW) E hEκ X hX
  have hT := hw W (le_trans (le_max_left _ _) hW) E hEκ X hX 1 le_rfl ![0] (dP p) (norm_dP_le p)
  rw [Fin.sum_univ_one] at hT
  set μ := layerLaw W b .oneBlockOnePort
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) := funext fun ω => by rw [wordVal_PpG]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0] (dP p)) =
      fun ω => bProj p * gRes b E X ω := funext fun ω => by rw [wordVal_PpG]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordAlpha_PpG]
  have e4 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 1 ![0] (dP p) 0) =
      fun ω => gRes b E X ω := funext fun ω => by rw [wordGamma_PpG]
  have e5 : matrixExpect μ (fun ω => bProj p * gRes b E X ω) =
      bProj p * matrixExpect μ (gRes b E X) := (SourceMixing.mul_matrixExpect' _ _ hG).symm
  rw [e1, e2, e3, e4, e5, blkAt_bProj_mul] at hT
  change ‖_ - SourceMixing.kmOf b E X * ((ind 0 p) • _ +
    sig1 b (tauP b E X p 0) (tauP b E X p 1) • _)‖ ≤ _ at hT
  rw [← add_smul] at hT
  exact hT

/-- **`m5_p ↦ A_pR`**: the index `(0, p)` of `MeanNearBulk alpFamI leadAlpI`.
Bulk-uniform copy of `alpINear_zero` (constants uniform on `bulkInterval κ`). -/
theorem alpINear_zero_bulk (hA : PassiveLayer.PassiveBoundsStatement) (p : Fin 2) :
    MeanNearBulk (ι := Unit) (fun _ => alpFamI (0, p)) (fun _ => leadAlpI (0, p)) := by
  intro b hb0 hb κ hκ
  obtain ⟨Cw, Ww, hCw, hwb⟩ := m5_block_bulk hA hb0 hb hκ
  obtain ⟨d₀, Cx, Wx, hd₀, hCx, hxm⟩ := xP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cb, Wb, hd₁, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨Ct, Wt, hCt, htb⟩ := tauP_blocks_bulk hA hb0 hb hκ
  set ηi := (etaLow b κ)⁻¹
  have hη : 0 ≤ ηi := (inv_pos.mpr (etaLow_pos (by linarith) hκ)).le
  set C := Cw + CK * Cx * CD + Cb * (Cx * Cb) + Cx * Cb + Cx * ηi
  refine ⟨min d₀ d₁, C, max (max (max Ww Wx) (max Wb WD)) (max (max WK Wt) 1), lt_min hd₀ hd₁,
    by positivity, fun W hW E hEκ s hs X hX hδ _ u v => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWx⟩, hWb, hWD⟩, ⟨hWK, hWt⟩, hW1⟩ := hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  have hd0 := h0.trans (hδ.trans (min_le_left _ _))
  have hd1 := h0.trans (hδ.trans (min_le_right _ _))
  obtain ⟨hx, hxA⟩ := hxm W hWx E hEκ s hs X hX hd0 p
  obtain ⟨hM, -, hR, hKM1, hMR, -⟩ := hmb W hWb E hEκ s X hX hd1
  obtain ⟨-, -, -, -, -, -, hE0, -, -, -, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨-, -, hKD, -⟩ := hK W hWK E hEκ X hX
  obtain ⟨-, -, hent, -, -⟩ := htb W hWt E hEκ X hX p
  have hT := hwb W hWw E hEκ X hX p
  set μ := layerLaw W b .oneBlockOnePort
  set e := SourceMixing.epsOf b E s X
  have he0 : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hint : ∀ i j, Integrable (fun ω => alpFamI (0, p) b E W X ω i j) μ := fun i j => by
    simp only [alpFamI_zero, Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hent k j).const_mul _
  show ‖(∫ ω, star (physVec u) ⬝ᵥ (alpFamI (0, p) b E W X ω *ᵥ physVec v) ∂μ) -
    bilinear u (leadM5 b E s X p) v‖ ≤ _
  rw [integral_form _ hint]
  have ef : alpFamI (0, p) b E W X = fun ω =>
      kHat b E X * (gRes b E X ω * (bProj p * gRes b E X ω)) := funext (alpFamI_zero p b E X)
  rw [ef, ← SourceMixing.mul_matrixExpect' _ _ hent]
  refine norm_bilinear_sub_le u v _ _ ?_
  set Y := blkAt (kHat b E X * matrixExpect μ
    (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))) 0 0
  set KM := SourceMixing.kmOf b E X
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set x := xP b E X p
  have hKMn : ‖KM‖ ≤ CK := (norm_blkAt_le _ 0 0).trans hKD
  have eq : Y - leadM5 b E s X p = (Y - KM * (x • G0)) + KM * (x • (G0 - M)) +
      (KM - 1) * (x • M) + x • (M - R) + (x - leadA b E s p) • R := by
    simp only [leadM5, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, smul_sub,
      sub_smul]
    abel
  rw [eq]
  have t1 : ‖Y - KM * (x • G0)‖ ≤ Cw * e := hT.trans (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCw)
  have t2 : ‖KM * (x • (G0 - M))‖ ≤ CK * Cx * CD * e := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    refine (mul_le_mul hKMn ((norm_smul_le _ _).trans (mul_le_mul hx (hE0.trans
      (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCD)) (norm_nonneg _) hCx)) (by positivity) hCK).trans ?_
    exact le_of_eq (by ring)
  have t3 : ‖(KM - 1) * (x • M)‖ ≤ Cb * (Cx * Cb) * e := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    refine (mul_le_mul hKM1 ((norm_smul_le _ _).trans (mul_le_mul hx hM (norm_nonneg _) hCx))
      (by positivity) (by positivity)).trans ?_
    exact le_of_eq (by ring)
  have t4 : ‖x • (M - R)‖ ≤ Cx * Cb * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hx hMR (norm_nonneg _) hCx).trans (le_of_eq (by ring)))
  have t5 : ‖(x - leadA b E s p) • R‖ ≤ Cx * ηi * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hxA (hR.trans (inv_etaZ_le_bulk hb hκ hEκ))
      (norm_nonneg _) (by positivity)).trans (le_of_eq (by ring)))
  have hsum : ‖(Y - KM * (x • G0)) + KM * (x • (G0 - M)) + (KM - 1) * (x • M) + x • (M - R) +
      (x - leadA b E s p) • R‖ ≤ C * e := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5).trans ?_
    exact le_of_eq (by simp only [C]; ring)
  exact hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))

end BlockBand.Transmission.CovarianceBulk
