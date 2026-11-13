module

public import BlockBand.Transmission.PassiveCovariance.GsFirst

/-!
# The `v_p` trace system: `E[𝒢Π𝒢ᴴP_p𝒢]`

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`,
`X`, `p`.

Word `w = Π𝒢ᴴP_p𝒢` (`![2, 0]`, insertions `dV p = ![Π, P_p, 1]`): `α₀ = Π𝒢ᴴ` (the `t` traces,
`σ₁ = s₁`), `γ₀ = 𝒢ᴴP_p𝒢` (the `𝒢ᴴ`-first mean `X = E[𝒢ᴴP_p𝒢]`), `α₁ = Π𝒢ᴴP_p𝒢` (the unknown
`v^p_r = E⟨(𝒢Π𝒢ᴴP_p𝒢)_rr⟩`, `vP`), `γ₁ = 𝒢`. With `S_p = σ₁(v^p)` (`svP`):
* `vP_blocks`: `(E[𝒢w])₀₀ = M(s₁X₀₀ + S_p(E𝒢)₀₀) + O(W⁻²)`,
  `(E[𝒢w])₁₁ = v((1 + bt₁)X₁₁ + bv^p₀(E𝒢)₁₁) + O(W⁻²)`;
* `vP_system` (proved in the sibling module): `S_p(1 - k_v⟨M²⟩) = k_vs₁rB_p⟨M²Mᴴ⟩ + bv(1 + bt₁)r_{p1} + O(W⁻²)`, `r_{p1} = t¹_p`.
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

/-- Insertions of `Π𝒢ᴴP_p𝒢`. -/
def dV (p : Fin 2) : Fin 3 → LayerMat W := ![portProj, bProj p, 1]

/-- Insertions of `𝒢Π𝒢ᴴP_p𝒢`. -/
def dV4 (p : Fin 2) : Fin 4 → LayerMat W := ![1, portProj, bProj p, 1]

theorem norm_dV_le (p : Fin 2) (j : Fin 3) : ‖(dV p j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_portProj_le
  · exact norm_bProj_le p
  · exact norm_one_matrix_le

theorem norm_dV4_le (p : Fin 2) (j : Fin 4) : ‖(dV4 p j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_portProj_le
  · exact norm_bProj_le p
  · exact norm_one_matrix_le

theorem wordVal_V (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![2, 0] (dV p) = portProj * (Gᴴ * (bProj p * G)) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dV, wLetter, Matrix.mul_assoc]

theorem wordVal_GV (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![0, 2, 0] (dV4 p) = G * (portProj * (Gᴴ * (bProj p * G))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]; simp [dV4, wLetter, Matrix.mul_assoc]

theorem wordAlpha_V0 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 2 ![2, 0] (dV p) 0 = portProj * Gᴴ := by
  simp [wordAlpha, dV, wLeft]

theorem wordAlpha_V1 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 2 ![2, 0] (dV p) 1 = portProj * (Gᴴ * (bProj p * G)) := by
  simp [wordAlpha, dV, wLeft, wLetter, Matrix.mul_assoc]

theorem wordGamma_V0 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 2 ![2, 0] (dV p) 0 = Gᴴ * (bProj p * G) := by
  simp [wordGamma, dV, wRight, wordVal, wLetter]

theorem wordGamma_V1 (Kh G : LayerMat W) (p : Fin 2) : wordGamma Kh G 2 ![2, 0] (dV p) 1 = G := by
  simp [wordGamma, dV, wRight, wordVal]

/-- `v^p_r = E⟨(𝒢Π𝒢ᴴP_p𝒢)_rr⟩`. -/
def vP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p r : Fin 2) : ℂ :=
  trMean b (fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)))) r

/-- `S_p = σ₁(v^p)`. -/
def svP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2) : ℂ :=
  sig1 b (vP b E X p 0) (vP b E X p 1)

/-- The `𝒢ᴴ`-first mean `X = E[𝒢ᴴP_p𝒢]`. -/
abbrev gsMean (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2) : LayerMat W :=
  matrixExpect (layerLaw W b .oneBlockOnePort)
    (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))

theorem blkAt_expect_portProj {μ : Measure (LayerSample W .oneBlockOnePort)}
    (F : LayerSample W .oneBlockOnePort → LayerMat W) :
    blkAt (matrixExpect μ (fun ω => portProj * F ω)) 0 0 = 0 ∧
      blkAt (matrixExpect μ (fun ω => portProj * F ω)) 1 1 = blkAt (matrixExpect μ F) 1 1 := by
  constructor
  · have e : (fun ω => blkAt (portProj * F ω) 0 0) = fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) :=
      funext fun ω => SourceMixing.blkAt_portProj_mul_zero _ 0
    rw [SourceMixing.blkAt_matrixExpect, e]; ext x y; simp [matrixExpect]
  · have e : (fun ω => blkAt (portProj * F ω) 1 1) = fun ω => blkAt (F ω) 1 1 :=
      funext fun ω => SourceMixing.blkAt_portProj_mul_one _
    rw [SourceMixing.blkAt_matrixExpect, e]; rfl

/-- **Blocks of `E[𝒢Π𝒢ᴴP_p𝒢]`.** -/
theorem vP_blocks (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖vP b E X p r‖ ≤ C) ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
          (bProj p * gRes b E X ω))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 0 0 -
          SourceMixing.mOf b E X * (SourceMixing.sOne b E X • blkAt (gsMean b E X p) 0 0 +
            svP b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 1 1 -
          SourceMixing.vOf b E X • ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) •
              blkAt (gsMean b E X p) 1 1 +
            ((b : ℂ) * vP b E X p 0) •
              blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock hA hb0 hb h1 h2 2 1
  obtain ⟨Cw, Ww, hCw, hw⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 3 1
  refine ⟨Cu + Cw, max Wu Ww, by positivity, fun W hW X hX p => ?_⟩
  have hWu : Wu ≤ W := le_trans (le_max_left _ _) hW
  have hWw : Ww ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw X hX.posSemidef 3 le_rfl ![0, 2, 0] (dV4 p) (norm_dV4_le p)
  have hle : Cw ≤ Cu + Cw := by linarith
  refine ⟨fun r => ?_, fun α β => ?_, ?_⟩
  · have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2, 0]
        (dV4 p)) r) = fun ω => SourceMixing.blkTr (gRes b E X ω * (portProj *
          ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)))) r := funext fun ω => by rw [wordVal_GV]
    rw [e] at h; exact h.trans hle
  · have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2, 0] (dV4 p) α β) =
        fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :
          LayerMat W) α β := funext fun ω => by rw [wordVal_GV]
    rw [e] at h; exact h
  have hT := hU W hWu X hX 2 le_rfl ![2, 0] (dV p) (norm_dV_le p)
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dV p)) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordVal_V]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dV p)) =
      fun ω => portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) :=
    funext fun ω => by rw [wordVal_V]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_V0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 1) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordAlpha_V1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordGamma_V0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 1) =
      fun ω => gRes b E X ω := funext fun ω => by rw [wordGamma_V1]
  obtain ⟨p0, p1⟩ := blkAt_expect_portProj (μ := μ)
    (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))
  rw [e1, e2, e3, e4, e5, e6, p0, p1, zero_add] at hT
  obtain ⟨hT0, hT1⟩ := hT
  have hup : Cu / (W : ℝ) ^ 2 ≤ (Cu + Cw) / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine ⟨hT0.trans hup, ?_⟩
  change ‖_ - SourceMixing.vOf b E X • (blkAt (gsMean b E X p) 1 1 +
    (((b : ℂ) * SourceMixing.tTwo b E X 0) • blkAt (gsMean b E X p) 1 1 +
      ((b : ℂ) * vP b E X p 0) • _))‖ ≤ _ at hT1
  have eS : ∀ (c : ℂ) (Y : Matrix (Fin W) (Fin W) ℂ), Y + c • Y = (1 + c) • Y := fun c Y => by
    rw [add_smul, one_smul]
  rw [← add_assoc, eS] at hT1
  exact hT1.trans hup

end BlockBand.Transmission.PassiveCovariance
