module

public import BlockBand.Transmission.PassiveCovariance.TauPMatched

/-!
# The mean `m5_p = E[K̂𝒢P_p𝒢]₁₁ ↦ A_pR` (index `(0, p)` of `alpFamI`)

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X` with `δ = δ₀ + δ₁ + q/W ≤ d`, stationary jet `s`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`;
constants depend on `b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p` and the vectors. Operator
norm.

* `alpFamI_zero`: `alpFamI (0, p) = K̂𝒢P_p𝒢` pointwise.
* `m5_block`: `‖(K̂E[𝒢P_p𝒢])₀₀ - KM·x_p·(E𝒢)₀₀‖ ≤ C/W²` (`weightedBlock`; `x_p = [p=0] + σ₁(τ^p)`).
* **`alpINear_zero hA p`**: `MeanNear` for the single word `alpFamI (0, p)` with leading value
  `leadM5 p = A_pR`: `(K̂E[𝒢P_p𝒢])₀₀ = KM·x_p·(E𝒢)₀₀ + O(W⁻²)` and `KM = 1 + O(ε)`, `E𝒢₀₀ = M + O(W⁻²)`,
  `M = R + O(ε)`, `x_p = A_p + O(ε)` (`xP_matched`), `ε = epsOf ≤ δ + W⁻¹`.
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

theorem alpFamI_zero (p : Fin 2) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    alpFamI (0, p) b E W X ω = kHat b E X * (gRes b E X ω * (bProj p * gRes b E X ω)) := by
  simp [alpFamI, wordAlpha, wLeft, gSide, wordVal_zero, Matrix.mul_assoc]

theorem div_sq_le_epsOf {b E : ℝ} (s : ℂ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {C : ℝ} (hC : 0 ≤ C) :
    C / (W : ℝ) ^ 2 ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hY
  rw [← SourceMixing.div_sq_eq]; exact mul_le_mul_of_nonneg_left (by linarith) hC

/-- The block form of `m5_p`. -/
theorem m5_block (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * (bProj p * gRes b E X ω))) 0 0 -
          SourceMixing.kmOf b E X * (xP b E X p •
            blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := weightedBlock hA hb0 hb h1 h2 1 1
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  refine ⟨C, max W₁ WD, hC, fun W hW X hX p => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W (le_trans (le_max_right _ _) hW) X hX
  have hT := hw W (le_trans (le_max_left _ _) hW) X hX 1 le_rfl ![0] (dP p) (norm_dP_le p)
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

/-- **`m5_p ↦ A_pR`**: the index `(0, p)` of `MeanNear alpFamI leadAlpI`. -/
theorem alpINear_zero (hA : PassiveLayer.PassiveBoundsStatement) (p : Fin 2) :
    MeanNear (ι := Unit) (fun _ => alpFamI (0, p)) (fun _ => leadAlpI (0, p)) := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨Cw, Ww, hCw, hwb⟩ := m5_block hA hb0 hb h1 h2
  obtain ⟨d₀, Cx, Wx, hd₀, hCx, hxm⟩ := xP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨d₁, Cb, Wb, hd₁, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨CK, WK, hCK, hK⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, htb⟩ := tauP_blocks hA hb0 hb h1 h2
  set ηi := (etaZ b E)⁻¹
  have hη : 0 ≤ ηi := (inv_pos.mpr (etaZ_pos b E (by linarith) h1 h2)).le
  set C := Cw + CK * Cx * CD + Cb * (Cx * Cb) + Cx * Cb + Cx * ηi
  refine ⟨min d₀ d₁, C, max (max (max Ww Wx) (max Wb WD)) (max (max WK Wt) 1), lt_min hd₀ hd₁,
    by positivity, fun W hW X hX hδ _ u v => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWx⟩, hWb, hWD⟩, ⟨hWK, hWt⟩, hW1⟩ := hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  have hd0 := h0.trans (hδ.trans (min_le_left _ _))
  have hd1 := h0.trans (hδ.trans (min_le_right _ _))
  obtain ⟨hx, hxA⟩ := hxm W hWx X hX hd0 p
  obtain ⟨hM, -, hR, hKM1, hMR, -⟩ := hmb W hWb X hX hd1
  obtain ⟨-, -, -, -, -, -, hE0, -, -, -, -⟩ := hD W hWD X hX
  obtain ⟨-, -, hKD, -⟩ := hK W hWK X hX
  obtain ⟨-, -, hent, -, -⟩ := htb W hWt X hX p
  have hT := hwb W hWw X hX p
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
    (norm_smul_le _ _).trans ((mul_le_mul hxA hR (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  have hsum : ‖(Y - KM * (x • G0)) + KM * (x • (G0 - M)) + (KM - 1) * (x • M) + x • (M - R) +
      (x - leadA b E s p) • R‖ ≤ C * e := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5).trans ?_
    exact le_of_eq (by simp only [C]; ring)
  exact hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))

end BlockBand.Transmission.PassiveCovariance
