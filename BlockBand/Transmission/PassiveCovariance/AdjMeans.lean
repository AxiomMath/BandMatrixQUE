module

public import BlockBand.Transmission.PassiveCovariance.AdjBlock

/-!
# Two `𝒢ᴴ`-first means: `E[𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ]` and `E[𝒢ᴴP_p𝒢Π𝒢ᴴ]`

A step of the passive covariance lemma. **Hypothesis:** `PassiveBoundsStatement`. Law
`layerLaw W b .oneBlockOnePort`, strictly passive `X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`;
constants depend on `b, E` only, uniformly in `W ≥ W₀`, `X`, `p`.

* `bProj_conjTranspose`, `blkTr_conjTranspose`, **`trMean_rv`**: `r'_{p,q} = E⟨(𝒢ᴴP_p𝒢Π𝒢ᴴ)_qq⟩ =
  conj v^p_q` exactly (the word is the adjoint of `𝒢Π𝒢ᴴP_p𝒢`), hence `σ₁(r'_p) = conj S_p`.
* **`gsN_block`**: `(E[𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ])₀₀ = Mᴴ(rB_pN₀₀ + conj S_p·((K̂E𝒢)₀₀)ᴴ) + O(W⁻²)`
  (`N = E[𝒢Π(K̂𝒢)ᴴ]`; the `γ₀` term of `m4_p`).
* **`gsT_block`**: `(E[𝒢ᴴP_p𝒢Π𝒢ᴴ])₀₀ = Mᴴ(rB_pT₀₀ + conj S_p·(E𝒢)₀₀ᴴ) + O(W⁻²)` (`T = E[𝒢Π𝒢ᴴ]`;
  the `γ₀` term of the `z_p` system), with the entrywise integrability of `𝒢ᴴP_p𝒢Π𝒢ᴴ`.
Both are `adjBlock` at `![0,3] ![P_p,Π,1]` and `![0,2] ![P_p,Π,1]`.
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

theorem bProj_conjTranspose (p : Fin 2) : (bProj p : LayerMat W)ᴴ = bProj p := by
  ext α β
  simp only [bProj, conjTranspose_apply, diagonal_apply, bInd]
  by_cases h : α = β
  · subst h; split_ifs <;> simp
  · simp [h, Ne.symm h]

theorem portProj_conjTranspose : (portProj : LayerMat W)ᴴ = portProj := by
  rw [← bProj_one, bProj_conjTranspose]

theorem sig1_conj (b : ℝ) (x y : ℂ) : sig1 b (conj x) (conj y) = conj (sig1 b x y) := by
  simp only [sig1, map_add, map_mul, Complex.conj_ofReal]

/-- `r'_{p,q} = conj v^p_q`. -/
theorem trMean_rv (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p q : Fin 2) :
    trMean b (fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))
      q = conj (vP b E X p q) := by
  have e : ∀ ω, SourceMixing.blkTr ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
      (portProj * (gRes b E X ω)ᴴ)))) q = conj (SourceMixing.blkTr (gRes b E X ω *
        (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)))) q) := fun ω => by
    rw [← blkTr_conjTranspose]
    congr 1
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, bProj_conjTranspose, portProj_conjTranspose]
    simp only [Matrix.mul_assoc]
  show ∫ ω, SourceMixing.blkTr ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
    (portProj * (gRes b E X ω)ᴴ)))) q ∂layerLaw W b .oneBlockOnePort = _
  simp only [e]
  exact integral_conj

theorem trMean_rP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p q : Fin 2) :
    trMean b (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) q = tP b E X q p := by
  have e : ∀ ω, SourceMixing.blkTr ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) q =
      SourceMixing.blkTr (gRes b E X ω * (bProj q * (gRes b E X ω)ᴴ)) p := fun ω =>
    blkTr_cyc _ p q
  show ∫ ω, SourceMixing.blkTr ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) q
    ∂layerLaw W b .oneBlockOnePort = _
  simp only [e]; rfl

theorem integrable_entries_of_eq {μ : Measure (LayerSample W .oneBlockOnePort)}
    {F G : LayerSample W .oneBlockOnePort → LayerMat W} (h : ∀ ω, F ω = G ω)
    (hF : ∀ α β, Integrable (fun ω => F ω α β) μ) : ∀ α β, Integrable (fun ω => G ω α β) μ :=
  fun α β => by
    have e : (fun ω => F ω α β) = fun ω => G ω α β := funext fun ω => by rw [h ω]
    rw [← e]; exact hF α β

theorem wordVal_GsM2 (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![2, 0, 3] (dM24 p) = Gᴴ * (bProj p * (G * (portProj * (Kh * G)ᴴ))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]; simp [dM24, wLetter, Matrix.mul_assoc]

theorem wordVal_GsW (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![2, 0, 2] (dW4 p) = Gᴴ * (bProj p * (G * (portProj * Gᴴ))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]; simp [dW4, wLetter, Matrix.mul_assoc]

theorem wordVal_GPKs (Kh G : LayerMat W) :
    wordVal Kh G ![0, 3] ![1, portProj, 1] = G * (portProj * (Kh * G)ᴴ) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [wLetter]

theorem wordVal_GPGs (Kh G : LayerMat W) :
    wordVal Kh G ![0, 2] ![1, portProj, 1] = G * (portProj * Gᴴ) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [wLetter]

theorem wordVal_Ks (Kh G : LayerMat W) : wordVal Kh G ![3] ![1, 1] = (Kh * G)ᴴ := by
  rw [wordVal_succ, wordVal_zero]; simp [wLetter]

theorem norm_ins3_le (j : Fin 3) : ‖(![1, portProj, 1] : Fin 3 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem norm_ins2_le (j : Fin 2) : ‖(![1, 1] : Fin 2 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j <;> exact norm_one_matrix_le

/-- **The `γ₀` mean of `m4_p`.** -/
theorem gsN_block (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => (gRes b E X ω)ᴴ *
            (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0 -
          (SourceMixing.mOf b E X)ᴴ * (rB b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))) 0 0 +
            conj (svP b E X p) • (blkAt (kHat b E X *
              matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := adjBlock hA hb0 hb h1 h2 2 1
  obtain ⟨Cm, Wm, hCm, hm⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 3 1
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  refine ⟨C, max W₁ (max Wm WD), hC, fun W hW X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hW₁, hWm, hWD⟩ := hW
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W hWD X hX
  set μ := layerLaw W b .oneBlockOnePort
  have I1 := (hm W hWm X hX.posSemidef 2 (by norm_num) ![0, 3] (dM2 p) (norm_dM2_le p)).1
  have I2 : ∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ *
      wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_GsM2, wordVal_M2])
      (hm W hWm X hX.posSemidef 3 le_rfl ![2, 0, 3] (dM24 p) (norm_dM24_le p)).1
  have I3 : ∀ j α β, Integrable (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p)
      j α β) μ := fun j => by
    fin_cases j
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_GPKs]; exact (wordGamma_M20 _ _ p).symm)
        (hm W hWm X hX.posSemidef 2 (by norm_num) ![0, 3] ![1, portProj, 1] norm_ins3_le).1
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_Ks]; exact (wordGamma_M21 _ _ p).symm)
        (hm W hWm X hX.posSemidef 1 (by norm_num) ![3] ![1, 1] norm_ins2_le).1
  have hT := hw W hW₁ X hX 2 le_rfl ![0, 3] (dM2 p) (norm_dM2_le p) I1 I2 I3
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (kHat b E X * gRes b E X ω)ᴴ))) := funext fun ω => by rw [wordVal_M2]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] (dM2 p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_M2]
  have e3 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) := funext fun ω => by rw [wordAlpha_M20]
  have e4 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 1) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_M21]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 0) =
      fun ω => gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_M20]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 3] (dM2 p) 1) =
      fun ω => (kHat b E X * gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_M21]
  have e7 : matrixExpect μ (fun ω => kHat b E X * gRes b E X ω) =
      kHat b E X * matrixExpect μ (gRes b E X) := (SourceMixing.mul_matrixExpect' _ _ hG).symm
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_conjT, e7, trMean_rP, trMean_rP,
    trMean_rv, trMean_rv, sig1_conj] at hT
  rw [← add_assoc, ← add_smul] at hT
  exact hT

/-- **The `γ₀` mean of the `z_p` system.** -/
theorem gsT_block (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
          (portProj * (gRes b E X ω)ᴴ))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => (gRes b E X ω)ᴴ *
            (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 0 0 -
          (SourceMixing.mOf b E X)ᴴ * (rB b E X p • blkAt (tMean b E X) 0 0 +
            conj (svP b E X p) •
              (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := adjBlock hA hb0 hb h1 h2 2 1
  obtain ⟨Cm, Wm, hCm, hm⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 3 1
  refine ⟨C, max W₁ Wm, hC, fun W hW X hX p => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hWm : Wm ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have I1 := (hm W hWm X hX.posSemidef 2 (by norm_num) ![0, 2] (dW p) (norm_dW_le p)).1
  have I2' : ∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
      (portProj * (gRes b E X ω)ᴴ))) : LayerMat W) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_GsW])
      (hm W hWm X hX.posSemidef 3 le_rfl ![2, 0, 2] (dW4 p) (norm_dW4_le p)).1
  have I2 : ∀ α β, Integrable (fun ω => ((gRes b E X ω)ᴴ *
      wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_W]) I2'
  have I3 : ∀ j α β, Integrable (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p)
      j α β) μ := fun j => by
    fin_cases j
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_GPGs]; exact (wordGamma_W0 _ _ p).symm)
        (hm W hWm X hX.posSemidef 2 (by norm_num) ![0, 2] ![1, portProj, 1] norm_ins3_le).1
    · exact integrable_entries_of_eq (fun ω => by rw [wordVal_Gs1]; exact (wordGamma_W1 _ _ p).symm)
        (hm W hWm X hX.posSemidef 1 (by norm_num) ![2] ![1, 1] norm_ins2_le).1
  refine ⟨I2', ?_⟩
  have hT := hw W hW₁ X hX 2 le_rfl ![0, 2] (dW p) (norm_dW_le p) I1 I2 I3
  rw [Fin.sum_univ_two] at hT
  have e1 : (fun ω => (gRes b E X ω)ᴴ * wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_W]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_W]
  have e3 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) := funext fun ω => by rw [wordAlpha_W0]
  have e4 : (fun ω => (gRes b E X ω)ᴴ * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_W1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordGamma_W0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_W1]
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_conjT, trMean_rP, trMean_rP,
    trMean_rv, trMean_rv, sig1_conj] at hT
  rw [← add_assoc, ← add_smul] at hT
  exact hT

end BlockBand.Transmission.PassiveCovariance
