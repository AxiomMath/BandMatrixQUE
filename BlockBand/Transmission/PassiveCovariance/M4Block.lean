module

public import BlockBand.Transmission.PassiveCovariance.ZMatched2

/-!
# The block form of `m4_p = E[K̂𝒢Π𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ]₁₁`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`,
`X`, `p`.

Word `w = Π𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ` (`![2,0,3]`, insertions `dZ p`): `α₀ = Π𝒢ᴴ` (`s₁`),
`γ₀ = 𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ` (`X' = E[γ₀]`, `gsN_block`), `α₁ = Π𝒢ᴴP_p𝒢` (`S_p`), `γ₁ = 𝒢Π(K̂𝒢)ᴴ` (`N`),
`α₂ = Π𝒢ᴴP_p𝒢Π𝒢ᴴ` (`σz_p`), `γ₂ = (K̂𝒢)ᴴ`.
* `alpFam_one`: `alpFam (1, p) = K̂𝒢Π𝒢ᴴP_p𝒢Π(K̂𝒢)ᴴ` pointwise.
* **`m4_block`**: `‖(K̂E[𝒢w])₀₀ - KM(s₁X'₀₀ + S_pN₀₀ + σz_p((K̂E𝒢)₀₀)ᴴ)‖ ≤ C/W²` (`weightedBlock`).
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

theorem wordVal_M4 (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![2, 0, 3] (dZ p) =
      portProj * (Gᴴ * (bProj p * (G * (portProj * (Kh * G)ᴴ)))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]; simp [dZ, wLetter, Matrix.mul_assoc]

theorem wordVal_GM4 (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![0, 2, 0, 3] (dZ5 p) =
      G * (portProj * (Gᴴ * (bProj p * (G * (portProj * (Kh * G)ᴴ))))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]
  simp [dZ5, wLetter, Matrix.mul_assoc]

theorem wordAlpha_M40 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 3 ![2, 0, 3] (dZ p) 0 = portProj * Gᴴ := by
  simp [wordAlpha, dZ, wLeft]

theorem wordAlpha_M41 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 3 ![2, 0, 3] (dZ p) 1 = portProj * (Gᴴ * (bProj p * G)) := by
  simp [wordAlpha, dZ, wLeft, wLetter, Matrix.mul_assoc]

theorem wordAlpha_M42 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 3 ![2, 0, 3] (dZ p) 2 = portProj * (Gᴴ * (bProj p * (G * (portProj * Gᴴ)))) := by
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl]
  simp only [wordAlpha, Fin.cons_succ, Fin.cons_one]
  simp [dZ, wLeft, wLetter, Matrix.mul_assoc]

theorem wordGamma_M40 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 3 ![2, 0, 3] (dZ p) 0 = Gᴴ * (bProj p * (G * (portProj * (Kh * G)ᴴ))) := by
  simp [wordGamma, dZ, wRight, wordVal, wLetter, Matrix.mul_assoc]

theorem wordGamma_M41 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 3 ![2, 0, 3] (dZ p) 1 = G * (portProj * (Kh * G)ᴴ) := by
  simp [wordGamma, dZ, wRight, wordVal, wLetter]

theorem wordGamma_M42 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 3 ![2, 0, 3] (dZ p) 2 = (Kh * G)ᴴ := by
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl]
  simp only [wordGamma, Fin.cons_succ, Fin.cons_one]
  simp [dZ, wRight, wordVal]

theorem alpFam_one (p : Fin 2) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    alpFam (1, p) b E W X ω = kHat b E X * (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
      (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ)))))) := by
  simp [alpFam, wordAlpha, wLeft, wLetter, gSide, wordVal_succ, wordVal_zero, Matrix.mul_assoc]

/-- **The block form of `m4_p`.** -/
theorem m4_block (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
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
  obtain ⟨C, W₁, hC, hw⟩ := weightedBlock hA hb0 hb h1 h2 3 1
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  refine ⟨C, max W₁ WD, hC, fun W hW X hX p => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, hG, -, -⟩ := hD W (le_trans (le_max_right _ _) hW) X hX
  have hT := hw W (le_trans (le_max_left _ _) hW) X hX 3 le_rfl ![2, 0, 3] (dZ p) (norm_dZ_le p)
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

end BlockBand.Transmission.PassiveCovariance
