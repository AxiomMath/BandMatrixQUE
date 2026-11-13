module

public import BlockBand.Transmission.PassiveCovariance.CStar

/-!
# The `z_p` trace system: `E[𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ]`, blocks

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`,
`X`, `p`.

Word `w = Π𝒢ᴴP_p𝒢Π𝒢ᴴ` (`![2,0,2]`, insertions `dZ p = ![Π, P_p, Π, 1]`): `α₀ = Π𝒢ᴴ` (`s₁`),
`γ₀ = 𝒢ᴴP_p𝒢Π𝒢ᴴ` (`X'' = E[γ₀]`, `gsT_block`), `α₁ = Π𝒢ᴴP_p𝒢` (`S_p = σ₁(v^p)`), `γ₁ = 𝒢Π𝒢ᴴ` (`T`),
`α₂ = w` (the unknown `z^p_r = E⟨(𝒢w)_rr⟩`, `zP`; `σz = σ₁(z^p)`, `szP`), `γ₂ = 𝒢ᴴ`.
* **`zP_blocks`**: `(E[𝒢w])₀₀ = M(s₁X''₀₀ + S_pT₀₀ + σz(E𝒢)₀₀ᴴ) + O(W⁻²)`,
  `(E[𝒢w])₁₁ = v((1 + bt₁)X''₁₁ + bv^p₀T₁₁ + bz^p₀(E𝒢)₁₁ᴴ) + O(W⁻²)` (`unweightedBlock`).
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

/-- Insertions of `Π𝒢ᴴP_p𝒢Π𝒢ᴴ`. -/
def dZ (p : Fin 2) : Fin 4 → LayerMat W := ![portProj, bProj p, portProj, 1]

/-- Insertions of `𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ`. -/
def dZ5 (p : Fin 2) : Fin 5 → LayerMat W := ![1, portProj, bProj p, portProj, 1]

theorem norm_dZ_le (p : Fin 2) (j : Fin 4) : ‖(dZ p j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_portProj_le
  · exact norm_bProj_le p
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem norm_dZ5_le (p : Fin 2) (j : Fin 5) : ‖(dZ5 p j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_portProj_le
  · exact norm_bProj_le p
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem wordVal_Z (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![2, 0, 2] (dZ p) = portProj * (Gᴴ * (bProj p * (G * (portProj * Gᴴ)))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]; simp [dZ, wLetter, Matrix.mul_assoc]

theorem wordVal_GZ (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![0, 2, 0, 2] (dZ5 p) =
      G * (portProj * (Gᴴ * (bProj p * (G * (portProj * Gᴴ))))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]
  simp [dZ5, wLetter, Matrix.mul_assoc]

theorem wordAlpha_Z0 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 3 ![2, 0, 2] (dZ p) 0 = portProj * Gᴴ := by
  simp [wordAlpha, dZ, wLeft]

theorem wordAlpha_Z1 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 3 ![2, 0, 2] (dZ p) 1 = portProj * (Gᴴ * (bProj p * G)) := by
  simp [wordAlpha, dZ, wLeft, wLetter, Matrix.mul_assoc]

theorem wordAlpha_Z2 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 3 ![2, 0, 2] (dZ p) 2 = portProj * (Gᴴ * (bProj p * (G * (portProj * Gᴴ)))) := by
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl]
  simp only [wordAlpha, Fin.cons_succ, Fin.cons_one]
  simp [dZ, wLeft, wLetter, Matrix.mul_assoc]

theorem wordGamma_Z0 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 3 ![2, 0, 2] (dZ p) 0 = Gᴴ * (bProj p * (G * (portProj * Gᴴ))) := by
  simp [wordGamma, dZ, wRight, wordVal, wLetter, Matrix.mul_assoc]

theorem wordGamma_Z1 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 3 ![2, 0, 2] (dZ p) 1 = G * (portProj * Gᴴ) := by
  simp [wordGamma, dZ, wRight, wordVal, wLetter]

theorem wordGamma_Z2 (Kh G : LayerMat W) (p : Fin 2) : wordGamma Kh G 3 ![2, 0, 2] (dZ p) 2 = Gᴴ := by
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl]
  simp only [wordGamma, Fin.cons_succ, Fin.cons_one]
  simp [dZ, wRight, wordVal]

/-- `z^p_r = E⟨(𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ)_rr⟩`. -/
def zP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p r : Fin 2) : ℂ :=
  trMean b (fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
    (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))))) r

/-- `σz_p = σ₁(z^p)`. -/
def szP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2) : ℂ :=
  sig1 b (zP b E X p 0) (zP b E X p 1)

/-- `X'' = E[𝒢ᴴP_p𝒢Π𝒢ᴴ]`. -/
abbrev gsTMean (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2) : LayerMat W :=
  matrixExpect (layerLaw W b .oneBlockOnePort)
    (fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))

/-- **Blocks of `E[𝒢Π𝒢ᴴP_p𝒢Π𝒢ᴴ]`.** -/
theorem zP_blocks (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖zP b E X p r‖ ≤ C) ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
          (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) : LayerMat W) α β)
          (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p *
              (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))))) 0 0 -
          SourceMixing.mOf b E X * (SourceMixing.sOne b E X • blkAt (gsTMean b E X p) 0 0 +
            svP b E X p • blkAt (tMean b E X) 0 0 +
            szP b E X p • (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p *
              (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))))) 1 1 -
          SourceMixing.vOf b E X • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) •
              blkAt (gsTMean b E X p) 1 1 +
            ((b : ℂ) * vP b E X p 0) • blkAt (tMean b E X) 1 1 +
            ((b : ℂ) * zP b E X p 0) •
              (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock hA hb0 hb h1 h2 3 1
  obtain ⟨Cw, Ww, hCw, hw⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 4 1
  refine ⟨Cu + Cw, max Wu Ww, by positivity, fun W hW X hX p => ?_⟩
  have hWu : Wu ≤ W := le_trans (le_max_left _ _) hW
  have hWw : Ww ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw X hX.posSemidef 4 le_rfl ![0, 2, 0, 2] (dZ5 p) (norm_dZ5_le p)
  have hle : Cw ≤ Cu + Cw := by linarith
  refine ⟨fun r => ?_, integrable_entries_of_eq (fun ω => by rw [wordVal_GZ]) hwt.1, ?_⟩
  · have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2, 0, 2]
        (dZ5 p)) r) = fun ω => SourceMixing.blkTr (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
          (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))))) r :=
      funext fun ω => by rw [wordVal_GZ]
    rw [e] at h; exact h.trans hle
  have hT := hU W hWu X hX 3 le_rfl ![2, 0, 2] (dZ p) (norm_dZ_le p)
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2, 0, 2] (dZ p)) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) := funext fun ω => by rw [wordVal_Z]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0, 2] (dZ p)) =
      fun ω => portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))) := funext fun ω => by rw [wordVal_Z]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_Z0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 1) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordAlpha_Z1]
  have e5 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 2) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p *
        (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) := funext fun ω => by rw [wordAlpha_Z2]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordGamma_Z0]
  have e7 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 1) =
      fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ) := funext fun ω => by rw [wordGamma_Z1]
  have e8 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 3 ![2, 0, 2] (dZ p) 2) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_Z2]
  obtain ⟨p0, p1⟩ := blkAt_expect_portProj (μ := μ) (fun ω => (gRes b E X ω)ᴴ * (bProj p *
    (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))
  rw [e1, e2, e3, e4, e5, e6, e7, e8, p0, p1, zero_add, blkAt_expect_conjT,
    blkAt_expect_conjT] at hT
  obtain ⟨hT0, hT1⟩ := hT
  have hup : Cu / (W : ℝ) ^ 2 ≤ (Cu + Cw) / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨hT0.trans hup, ?_⟩
  change ‖_ - SourceMixing.vOf b E X • (blkAt (gsTMean b E X p) 1 1 +
    (((b : ℂ) * SourceMixing.tTwo b E X 0) • blkAt (gsTMean b E X p) 1 1 +
      ((b : ℂ) * vP b E X p 0) • _ + ((b : ℂ) * zP b E X p 0) • _))‖ ≤ _ at hT1
  have eS : ∀ (c : ℂ) (Y Z₁ Z₂ : Matrix (Fin W) (Fin W) ℂ), Y + (c • Y + Z₁ + Z₂) =
      (1 + c) • Y + Z₁ + Z₂ := fun c Y Z₁ Z₂ => by rw [add_smul, one_smul]; abel
  rw [eS] at hT1
  exact hT1.trans hup

end BlockBand.Transmission.PassiveCovariance
