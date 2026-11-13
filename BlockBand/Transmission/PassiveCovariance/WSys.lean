module

public import BlockBand.Transmission.PassiveCovariance.M6Near

/-!
# The `w_p` trace system: `E[𝒢P_p𝒢Π𝒢ᴴ]`

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X`, fixed
`b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`, `X`, `p`.

Word `w = P_p𝒢Π𝒢ᴴ` (`![0, 2]`, insertions `dW p = ![P_p, Π, 1]`): `α₀ = P_p𝒢` (the `τ^p` traces,
`[p=0] + σ₁ = x_p`), `γ₀ = 𝒢Π𝒢ᴴ` (`T`), `α₁ = P_p𝒢Π𝒢ᴴ` (the unknown
`w^p_r = E⟨(𝒢P_p𝒢Π𝒢ᴴ)_rr⟩`, `wP`), `γ₁ = 𝒢ᴴ`. With `σ_p = σ₁(w^p)` (`swP`):
* `wP_blocks`: `(E[𝒢w])₀₀ = M(x_pT₀₀ + σ_p(E𝒢)₀₀ᴴ) + O(W⁻²)`,
  `(E[𝒢w])₁₁ = v(([p=1] + bτ^p₀)T₁₁ + bw^p₀(E𝒢)₁₁ᴴ) + O(W⁻²)`;
* `wP_system` (proved in the sibling module): `σ_p(1 - k_hA) = k_hx_ps₁B + bv([p=1] + bτ^p₀)t₂ + O(W⁻²)` (`p = 1`:
  `scalarRho`, determinant `1 - k_hA → b`).
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

/-- Insertions of `P_p𝒢Π𝒢ᴴ`. -/
def dW (p : Fin 2) : Fin 3 → LayerMat W := ![bProj p, portProj, 1]

/-- Insertions of `𝒢P_p𝒢Π𝒢ᴴ`. -/
def dW4 (p : Fin 2) : Fin 4 → LayerMat W := ![1, bProj p, portProj, 1]

theorem norm_dW_le (p : Fin 2) (j : Fin 3) : ‖(dW p j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_bProj_le p
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem norm_dW4_le (p : Fin 2) (j : Fin 4) : ‖(dW4 p j : LayerMat W)‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_bProj_le p
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem wordVal_W (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![0, 2] (dW p) = bProj p * (G * (portProj * Gᴴ)) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [dW, wLetter, Matrix.mul_assoc]

theorem wordVal_GW (Kh G : LayerMat W) (p : Fin 2) :
    wordVal Kh G ![0, 0, 2] (dW4 p) = G * (bProj p * (G * (portProj * Gᴴ))) := by
  rw [wordVal_succ, wordVal_succ, wordVal_succ, wordVal_zero]; simp [dW4, wLetter, Matrix.mul_assoc]

theorem wordAlpha_W0 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 2 ![0, 2] (dW p) 0 = bProj p * G := by
  simp [wordAlpha, dW, wLeft]

theorem wordAlpha_W1 (Kh G : LayerMat W) (p : Fin 2) :
    wordAlpha Kh G 2 ![0, 2] (dW p) 1 = bProj p * (G * (portProj * Gᴴ)) := by
  simp [wordAlpha, dW, wLeft, wLetter, Matrix.mul_assoc]

theorem wordGamma_W0 (Kh G : LayerMat W) (p : Fin 2) :
    wordGamma Kh G 2 ![0, 2] (dW p) 0 = G * (portProj * Gᴴ) := by
  simp [wordGamma, dW, wRight, wordVal, wLetter]

theorem wordGamma_W1 (Kh G : LayerMat W) (p : Fin 2) : wordGamma Kh G 2 ![0, 2] (dW p) 1 = Gᴴ := by
  simp [wordGamma, dW, wRight, wordVal]

/-- `w^p_r = E⟨(𝒢P_p𝒢Π𝒢ᴴ)_rr⟩`. -/
def wP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p r : Fin 2) : ℂ :=
  trMean b (fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))) r

/-- `σ_p = σ₁(w^p)`. -/
def swP (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2) : ℂ :=
  sig1 b (wP b E X p 0) (wP b E X p 1)

/-- `T = E[𝒢Π𝒢ᴴ]`. -/
abbrev tMean (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : LayerMat W :=
  matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))

/-- `(E[P_pF])_rs = [r=p](EF)_rs` (no integrability needed). -/
theorem blkAt_expect_bProj {μ : Measure (LayerSample W .oneBlockOnePort)}
    (F : LayerSample W .oneBlockOnePort → LayerMat W) (p r s : Fin 2) :
    blkAt (matrixExpect μ (fun ω => bProj p * F ω)) r s = ind r p • blkAt (matrixExpect μ F) r s := by
  have e : (fun ω => blkAt (bProj p * F ω) r s) = fun ω => ind r p • blkAt (F ω) r s :=
    funext fun ω => blkAt_bProj_mul p r s (F ω)
  change matrixExpect μ (fun ω => blkAt (bProj p * F ω) r s) =
    ind r p • matrixExpect μ (fun ω => blkAt (F ω) r s)
  rw [e]
  ext x y
  simp [matrixExpect, integral_const_mul]

theorem blkAt_expect_conjT {μ : Measure (LayerSample W .oneBlockOnePort)}
    (F : LayerSample W .oneBlockOnePort → LayerMat W) (r : Fin 2) :
    blkAt (matrixExpect μ (fun ω => (F ω)ᴴ)) r r = (blkAt (matrixExpect μ F) r r)ᴴ := by
  rw [SourceMixing.matrixExpect_conjTranspose, blkAt_conjTranspose]

/-- **Blocks of `E[𝒢P_p𝒢Π𝒢ᴴ]`.** -/
theorem wP_blocks (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        (∀ r, ‖wP b E X p r‖ ≤ C) ∧
        (∀ α β, Integrable (fun ω => (gRes b E X ω * (bProj p * (gRes b E X ω *
          (portProj * (gRes b E X ω)ᴴ))) : LayerMat W) α β) (layerLaw W b .oneBlockOnePort)) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 0 0 -
          SourceMixing.mOf b E X * (xP b E X p • blkAt (tMean b E X) 0 0 +
            swP b E X p • (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))))) 1 1 -
          SourceMixing.vOf b E X • ((ind 1 p + (b : ℂ) * tauP b E X p 0) • blkAt (tMean b E X) 1 1 +
            ((b : ℂ) * wP b E X p 0) •
              (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1)ᴴ)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨Cu, Wu, hCu, hU⟩ := unweightedBlock hA hb0 hb h1 h2 2 1
  obtain ⟨Cw, Ww, hCw, hw⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 3 1
  refine ⟨Cu + Cw, max Wu Ww, by positivity, fun W hW X hX p => ?_⟩
  have hWu : Wu ≤ W := le_trans (le_max_left _ _) hW
  have hWw : Ww ≤ W := le_trans (le_max_right _ _) hW
  set μ := layerLaw W b .oneBlockOnePort
  have hwt := hw W hWw X hX.posSemidef 3 le_rfl ![0, 0, 2] (dW4 p) (norm_dW4_le p)
  have hle : Cw ≤ Cu + Cw := by linarith
  refine ⟨fun r => ?_, fun α β => ?_, ?_⟩
  · have h := hwt.2.2.2.2 r
    have e : (fun ω => SourceMixing.blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2]
        (dW4 p)) r) = fun ω => SourceMixing.blkTr (gRes b E X ω * (bProj p *
          (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)))) r := funext fun ω => by rw [wordVal_GW]
    rw [e] at h; exact h.trans hle
  · have h := hwt.1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 2] (dW4 p) α β) =
        fun ω => (gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :
          LayerMat W) α β := funext fun ω => by rw [wordVal_GW]
    rw [e] at h; exact h
  have hT := hU W hWu X hX 2 le_rfl ![0, 2] (dW p) (norm_dW_le p)
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hT
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordVal_W]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 2] (dW p)) =
      fun ω => bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ)) :=
    funext fun ω => by rw [wordVal_W]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => gRes b E X ω * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordAlpha_W0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => gRes b E X ω * (bProj p * (gRes b E X ω * (portProj * (gRes b E X ω)ᴴ))) :=
    funext fun ω => by rw [wordAlpha_W1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 0) =
      fun ω => gRes b E X ω * (portProj * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordGamma_W0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![0, 2] (dW p) 1) =
      fun ω => (gRes b E X ω)ᴴ := funext fun ω => by rw [wordGamma_W1]
  rw [e1, e2, e3, e4, e5, e6, blkAt_expect_bProj, blkAt_expect_bProj, blkAt_expect_conjT,
    blkAt_expect_conjT] at hT
  obtain ⟨hT0, hT1⟩ := hT
  have hup : Cu / (W : ℝ) ^ 2 ≤ (Cu + Cw) / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  constructor
  · change ‖_ - SourceMixing.mOf b E X * (ind 0 p • blkAt (tMean b E X) 0 0 +
      (sig1 b (tauP b E X p 0) (tauP b E X p 1) • blkAt (tMean b E X) 0 0 +
        swP b E X p • _))‖ ≤ _ at hT0
    rw [← add_assoc, ← add_smul] at hT0
    exact hT0.trans hup
  · change ‖_ - SourceMixing.vOf b E X • (ind 1 p • blkAt (tMean b E X) 1 1 +
      (((b : ℂ) * tauP b E X p 0) • blkAt (tMean b E X) 1 1 +
        ((b : ℂ) * wP b E X p 0) • _))‖ ≤ _ at hT1
    rw [← add_assoc, ← add_smul] at hT1
    exact hT1.trans hup

end BlockBand.Transmission.PassiveCovariance
