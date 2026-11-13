module

public import BlockBand.Transmission.PassiveCovarianceBulk.AlpBlocks
public import BlockBand.Transmission.PassiveCovarianceBulk.Matched1

/-!
# The weighted two-resolvent block `E[K̂𝒢P_p(K̂𝒢)ᴴ]₀₀ = y_p·KM(KM)ᴴ + O(W⁻²)`

Law `freshLaw W b`, strictly passive `X`, operator norm; constants uniform in `W ≥ W₀`,
`E ∈ bulkInterval κ`, `X`, `p`.

This is `LengthUniform.freshU_mean_bulk` (the case `p = 1`, `P₂`) for both block projectors
`P_p = bProj p`, with the coefficient `y_p = [p = 0] + σ₁(t^p)` of `PassiveCovariance.TqSys`
(`t^p_r = E⟨(𝒢P_p𝒢ᴴ)_rr⟩`). It is the `(0,0)` block of PCB's `weightedBlock_bulk` with the
one-letter word `P_p(K̂𝒢)ᴴ`.

* `wordVal_PpKGs`, `wordAlpha_PpKGs`, `wordGamma_PpKGs`, `wordVal_KGPpKGs`: the word algebra;
* **`projBlock_mean_bulk hA`**: entries of `K̂𝒢P_p(K̂𝒢)ᴴ` integrable, `‖KM‖, |y_p| ≤ C` and
  `‖E[K̂𝒢P_p(K̂𝒢)ᴴ]₀₀ - y_p·KM(KM)ᴴ‖ ≤ C/W²`;
* **`yP_matched_bulk hA`**: `|y_p - y*_p| ≤ C·epsOf` near the jet (`y*₀ = 1/b`, `y*₁ = 1`), from
  PCB's `tP_matched_bulk` and the identity `y*_p = [p = 0] + σ₁(t*^p)` (`yStar_eq_sig1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem wordVal_PpKGs (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![3] (dP p) = bProj p * (Kh * G)ᴴ := by
  rw [wordVal_succ, wordVal_zero]; simp [dP, wLetter]

theorem wordAlpha_PpKGs (Kh G : LayerMat W) (p : Fin 2) (j : Fin 1) :
    wordAlpha Kh G 1 ![3] (dP p) j = bProj p * Gᴴ := by
  rw [Subsingleton.elim j 0]; simp [wordAlpha, dP, wLeft]

theorem wordGamma_PpKGs (Kh G : LayerMat W) (p : Fin 2) (j : Fin 1) :
    wordGamma Kh G 1 ![3] (dP p) j = (Kh * G)ᴴ := by
  rw [Subsingleton.elim j 0]; simp [wordGamma, dP, wRight, wordVal]

theorem wordVal_KGPpKGs (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![1, 3] (dP3 p) = Kh * (G * (bProj p * (Kh * G)ᴴ)) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dP3, wLetter, Matrix.mul_assoc]

theorem wordVal_Gs1' (Kh G : LayerMat W) : wordVal Kh G ![0] ![1, 1] = G := by
  rw [wordVal_succ, wordVal_zero]; simp [wLetter]

theorem matrixExpect_smul' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (c : ℂ)
    (F : Ω → Matrix (Fin W) (Fin W) ℂ) :
    matrixExpect μ (fun ω => c • F ω) = c • matrixExpect μ F := by
  ext i j
  simp only [matrixExpect, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact integral_const_mul c _

/-- **The weighted two-resolvent block** for both projectors `P_p`. -/
theorem projBlock_mean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ α β, Integrable (fun ω => (kHat b E X * (gRes b E X ω *
          (bProj p * (kHat b E X * gRes b E X ω)ᴴ)) : LayerMat W) α β) (freshLaw W b)) ∧
        ‖SourceMixing.kmOf b E X‖ ≤ C ∧ ‖yP b E X p‖ ≤ C ∧
        ‖blkAt (matrixExpect (freshLaw W b) (fun ω => kHat b E X * (gRes b E X ω *
            (bProj p * (kHat b E X * gRes b E X ω)ᴴ)))) 0 0 -
          yP b E X p • (SourceMixing.kmOf b E X * (SourceMixing.kmOf b E X)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hT⟩ := CovarianceBulk.weightedBlock_bulk hA hb0 hb hκ 1 1
  obtain ⟨CK, WK, hCK, hK⟩ := LengthUniform.norm_kHat_dressedInv_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := LengthUniform.wordMean_bound_bulk hA hb0 hb hκ 2 1
  obtain ⟨Cy, Wy, hCy, hsys⟩ := CovarianceBulk.tP_system_bulk hA hb0 hb hκ
  refine ⟨max (max CK Cy) (C₁ + Cy * CK * CK), max (max W₁ WK) (max Ww Wy), by positivity,
    fun W hW E hE X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWK⟩, hWw, hWy⟩ := hW
  set μ := freshLaw W b
  set Kh := kHat b E X
  obtain ⟨-, -, hKD, hKE⟩ := hK W hWK E hE X hX
  have hKM : ‖SourceMixing.kmOf b E X‖ ≤ CK := (norm_blkAt_le _ _ _).trans hKD
  have hy : ‖yP b E X p‖ ≤ Cy := (hsys W hWy E hE X hX p).1
  have hiK : ∀ α β, Integrable (fun ω => (Kh * (gRes b E X ω *
      (bProj p * (Kh * gRes b E X ω)ᴴ)) : LayerMat W) α β) μ := fun α β => by
    have h := (hw W hWw E hE X hX.posSemidef 2 le_rfl ![1, 3] (dP3 p) (norm_dP3_le p)).1 α β
    have e : (fun ω => wordVal Kh (gRes b E X ω) ![1, 3] (dP3 p) α β) =
        fun ω => (Kh * (gRes b E X ω * (bProj p * (Kh * gRes b E X ω)ᴴ)) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_KGPpKGs]
    rw [e] at h; exact h
  have hiN : ∀ α β, Integrable (fun ω => (gRes b E X ω *
      (bProj p * (Kh * gRes b E X ω)ᴴ) : LayerMat W) α β) μ := fun α β => by
    have h := (hw W hWw E hE X hX.posSemidef 2 le_rfl ![0, 3] (dP3 p) (norm_dP3_le p)).1 α β
    have e : (fun ω => wordVal Kh (gRes b E X ω) ![0, 3] (dP3 p) α β) =
        fun ω => (gRes b E X ω * (bProj p * (Kh * gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dP3, wLetter]
    rw [e] at h; exact h
  have hiG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) μ := fun α β => by
    have h := (hw W hWw E hE X hX.posSemidef 1 (by norm_num) ![0] ![1, 1]
      SourceMixing.norm_ins1_le).1 α β
    have e : (fun ω => wordVal Kh (gRes b E X ω) ![0] ![1, 1] α β) = fun ω => gRes b E X ω α β :=
      funext fun ω => by rw [wordVal_Gs1']
    rw [e] at h; exact h
  refine ⟨hiK, hKM.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hy.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  have h := hT W hW₁ E hE X hX 1 le_rfl ![3] (dP p) (norm_dP_le p)
  rw [Fin.sum_univ_one] at h
  have e1 : (fun ω => gRes b E X ω * wordVal Kh (gRes b E X ω) ![3] (dP p)) =
      fun ω => gRes b E X ω * (bProj p * (Kh * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordVal_PpKGs]
  have e2 : (fun ω => wordVal Kh (gRes b E X ω) ![3] (dP p)) =
      fun ω => bProj p * (Kh * gRes b E X ω)ᴴ := funext fun ω => by rw [wordVal_PpKGs]
  have e3 : (fun ω => gRes b E X ω * wordAlpha Kh (gRes b E X ω) 1 ![3] (dP p) 0) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_PpKGs]
  have e4 : (fun ω => wordGamma Kh (gRes b E X ω) 1 ![3] (dP p) 0) =
      fun ω => (Kh * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_PpKGs]
  rw [e1, e2, e3, e4] at h
  -- the left side
  have hL : Kh * matrixExpect μ (fun ω => gRes b E X ω * (bProj p * (Kh * gRes b E X ω)ᴴ)) =
      matrixExpect μ (fun ω => Kh * (gRes b E X ω * (bProj p * (Kh * gRes b E X ω)ᴴ))) :=
    SourceMixing.mul_matrixExpect' _ _ hiN
  -- the right side
  have hGs : blkAt (matrixExpect μ (fun ω => (Kh * gRes b E X ω)ᴴ)) 0 0 =
      (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ := by
    rw [SourceMixing.matrixExpect_conjTranspose, blkAt_conjTranspose,
      SourceMixing.mul_matrixExpect' _ _ hiG]
  set Γ := blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0
  have hPs : blkAt (matrixExpect μ (fun ω => bProj p * (Kh * gRes b E X ω)ᴴ)) 0 0 =
      ind 0 p • Γᴴ := by
    rw [SourceMixing.blkAt_matrixExpect]
    have e : (fun ω => blkAt (bProj p * (Kh * gRes b E X ω)ᴴ) 0 0) =
        fun ω => ind 0 p • blkAt ((Kh * gRes b E X ω)ᴴ) 0 0 :=
      funext fun ω => by rw [blkAt_bProj_mul]; rfl
    rw [e, matrixExpect_smul', ← SourceMixing.blkAt_matrixExpect, hGs]
  have hR : blkAt (matrixExpect μ (fun ω => bProj p * (Kh * gRes b E X ω)ᴴ)) 0 0 +
      sig1 b (trMean b (fun ω => gRes b E X ω * (bProj p * (gRes b E X ω)ᴴ)) 0)
        (trMean b (fun ω => gRes b E X ω * (bProj p * (gRes b E X ω)ᴴ)) 1) •
        blkAt (matrixExpect μ (fun ω => (Kh * gRes b E X ω)ᴴ)) 0 0 = yP b E X p • Γᴴ := by
    rw [hPs, hGs, ← add_smul]; rfl
  rw [hL, hR] at h
  have hdiff : ‖Γ - SourceMixing.kmOf b E X‖ ≤ CK / (W : ℝ) ^ 2 := by
    rw [SourceMixing.kmOf, ← blkAt_sub]; exact (norm_blkAt_le _ _ _).trans hKE
  set B := blkAt (matrixExpect μ (fun ω => Kh * (gRes b E X ω *
    (bProj p * (Kh * gRes b E X ω)ᴴ)))) 0 0
  set KM := SourceMixing.kmOf b E X
  have e : B - yP b E X p • (KM * KMᴴ) =
      (B - KM * (yP b E X p • Γᴴ)) + yP b E X p • (KM * (Γ - KM)ᴴ) := by
    rw [Matrix.mul_smul, conjTranspose_sub, Matrix.mul_sub, smul_sub]; abel
  rw [e]
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  calc _ ≤ C₁ / (W : ℝ) ^ 2 + ‖yP b E X p‖ * (‖KM‖ * (CK / (W : ℝ) ^ 2)) := by
        refine (norm_add_le _ _).trans (add_le_add h ?_)
        refine (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [Matrix.l2_opNorm_conjTranspose]; exact hdiff
    _ ≤ C₁ / (W : ℝ) ^ 2 + Cy * (CK * (CK / (W : ℝ) ^ 2)) := by gcongr
    _ = (C₁ + Cy * CK * CK) / (W : ℝ) ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hW2

/-- `y*_p = [p = 0] + σ₁(t*^p)` (the leading values solve the `t^p` system). -/
theorem yStar_eq_sig1 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (p : Fin 2) :
    yStar b p = ind 0 p + sig1 b (tStar b p 0) (tStar b p 1) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have h1 : (1 : ℂ) - b ≠ 0 := by
    have : (1 : ℝ) - b ≠ 0 := by linarith
    exact_mod_cast this
  fin_cases p <;> simp [yStar, tStar, ind, sig1, dStar] <;> field_simp <;> ring

/-- **Matched values of `y_p`**: `|y_p - y*_p| ≤ C·epsOf` near the jet. -/
theorem yP_matched_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
      ∀ p : Fin 2, ‖yP b E X p - yStar b p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, C, W₀, hd₀, hC, ht⟩ := CovarianceBulk.tP_matched_bulk hA hb0 hb hκ
  refine ⟨d₀, (1 - 2 * b) * C + b * C, W₀, hd₀, by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity, fun W hW E hE s X hX hd p => ?_⟩
  have h0 := (ht W hW E hE s X hX hd p 0).2
  have h1 := (ht W hW E hE s X hX hd p 1).2
  rw [yStar_eq_sig1 hb0 hb, yP]
  have e : ind 0 p + sig1 b (tP b E X p 0) (tP b E X p 1) -
      (ind 0 p + sig1 b (tStar b p 0) (tStar b p 1)) =
      ((1 - 2 * b : ℝ) : ℂ) * (tP b E X p 0 - tStar b p 0) +
        (b : ℂ) * (tP b E X p 1 - tStar b p 1) := by
    simp only [sig1]; ring
  rw [e]
  have hc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hb2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hc, hb2]
  have : 0 ≤ 1 - 2 * b := by linarith
  calc _ ≤ (1 - 2 * b) * (C * SourceMixing.epsOf b E s X) +
        b * (C * SourceMixing.epsOf b E s X) := by gcongr
    _ = _ := by ring

end BlockBand.SourceProcess.FullSourceCovariance
