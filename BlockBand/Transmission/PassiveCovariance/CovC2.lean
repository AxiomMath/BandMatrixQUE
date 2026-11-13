module

public import BlockBand.Transmission.PassiveCovariance.CovC1

/-!
# `E[FQ⁰]` is a pure source term (`cov_C2`)

The second step of the level-0 expansion of the passive covariance. **Hypotheses:**
`PassiveBoundsStatement` and `GaussianPoincare`. Law `layerLaw W b .oneBlockOnePort`,
`z = z_∂(E)`, strictly passive `X`; fixed `b, E`; then `C, W₀`; uniform in `X` and the vectors
with `‖x̌‖‖v₄‖ ≤ 1`.

With the notation of `CovC1` and `x̌' = (K̂M̄)ᴴa'`, `Q̃ = conj Q = c'*K̂𝒢Π(K̂𝒢)ᴴc`
(`conj_Q`), `conj F = a'*K̂𝒢x̌` (`conj_F`): `E[FQ⁰] = conj E[(a'*K̂𝒢x̌)Q̃⁰]`, and the expansion of
the latter (`N = I`: no letters, no trace term; the mean term vanishes since `EQ̃⁰ = 0`) is the
crossed source `X₂` alone:

* **`cov_C2`**: `|E[FQ⁰] - conj X₂| ≤ (C/W²)‖x̌'‖‖v₃‖`,
  `X₂ = Σ_k Σ_{p,p'} s_{pp'} E[x̌'*P_pγ̃'_kc]·E[c'*α̃'_kP_{p'}𝒢x̌]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem wordVal_U (Kh G : LayerMat W) :
    wordVal Kh G ![1, 3] ![1, portProj, 1] = Kh * G * (portProj * (Kh * G)ᴴ) := by
  simp [wordVal_succ, wordVal_zero, wLetter, Matrix.mul_assoc]

theorem wordVal_U_conjT (Kh G : LayerMat W) :
    (wordVal Kh G ![1, 3] ![1, portProj, 1])ᴴ = wordVal Kh G ![1, 3] ![1, portProj, 1] := by
  rw [wordVal_U, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, portProj_conjT,
    Matrix.mul_assoc]

theorem conj_Q (Kh G : LayerMat W) (x y : LayerSite W .oneBlockOnePort → ℂ) :
    conj (wordForm Kh x y ![1, 3] ![1, portProj, 1] G) = wordForm Kh y x ![1, 3] ![1, portProj, 1] G := by
  rw [wordForm, conj_form, wordVal_U_conjT, wordForm]

theorem wordGamma_N (Kh G : LayerMat W) :
    wordGamma Kh G 1 ![3] ![portProj, 1] 0 = (Kh * G)ᴴ := by
  simp [wordGamma, wRight, wordVal_zero]

theorem conj_F (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (x y : LayerSite W .oneBlockOnePort → ℂ) :
    conj (star x ⬝ᵥ (wordGamma (kHat b E X) (gRes b E X ω) 1 ![3] ![portProj, 1] 0 *ᵥ y)) =
      star y ⬝ᵥ ((kHat b E X * gSide b E X false ω *
        wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ x) := by
  rw [conj_form, wordGamma_N, conjTranspose_conjTranspose, wordVal_zero]
  simp [gSide]

/-- **(C2).** -/
theorem cov_C2 (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        vecNorm ((kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₁) * vecNorm v₄ ≤ 1 →
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let xc := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₁
        let xc' := (Kh * mbarSide b E X false)ᴴ *ᵥ physVec v₂
        let Q := fun ω => wordForm Kh (physVec v₃) (physVec v₄) ![1, 3] ![1, portProj, 1]
          (gRes b E X ω)
        let F := fun ω => star xc ⬝ᵥ (wordGamma Kh (gRes b E X ω) 1 ![3] ![portProj, 1] 0 *ᵥ
          physVec v₂)
        let X₂ := ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
          ((∫ ω, star xc' ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k) *ᵥ
              physVec v₃) ∂μ) *
            ∫ ω, star (physVec v₄) ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) 2 ![1, 3] ![1, portProj, 1] k *
              bProj p' * (gSide b E X false ω * wordVal Kh (gRes b E X ω) ![] ![1])) *ᵥ xc) ∂μ)
        ‖∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ - conj X₂‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm xc' * vecNorm v₃) := by
  obtain ⟨C, W₁, hC, hs⟩ := sdQ_expand hP hA hb0 hb h1 h2 2 1 false
  obtain ⟨W₂, hm⟩ := memLp_wordForm_unif hA hb0 hb h1 h2 2 1
  refine ⟨C, max W₁ W₂, hC, fun W hW X hX v₁ v₂ v₃ v₄ hn => ?_⟩
  intro μ Kh xc xc' Q F X₂
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW2 : W₂ ≤ W := le_trans (le_max_right _ _) hW
  have hD1 : ∀ j, ‖(![1] : Fin 1 → LayerMat W) j‖ ≤ 1 := fun j => by
    fin_cases j; exact norm_one_matrix_le
  have h := hs W hW1 X hX 0 (by norm_num) ![] ![1] hD1 2 le_rfl ![1, 3] ![1, portProj, 1]
    norm_uIns_le Kh (physVec v₂) xc (physVec v₄) (physVec v₃)
    (by rw [vecNorm_physVec]; exact hn)
  simp only at h
  set Qt := fun ω => wordForm Kh (physVec v₄) (physVec v₃) ![1, 3] ![1, portProj, 1] (gRes b E X ω)
  have hQt : Integrable Qt μ :=
    (hm W hW2 X hX.posSemidef 2 le_rfl _ _ norm_uIns_le _ _).integrable one_le_two
  have eL : ∫ ω, F ω * (Q ω - ∫ ω', Q ω' ∂μ) ∂μ =
      conj (∫ ω, star (physVec v₂) ⬝ᵥ ((kHat b E X * gSide b E X false ω *
        wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ xc) * (Qt ω - ∫ ω', Qt ω' ∂μ) ∂μ) := by
    rw [← integral_conj]
    have e : ∀ ω, conj (star (physVec v₂) ⬝ᵥ ((kHat b E X * gSide b E X false ω *
        wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ xc) * (Qt ω - ∫ ω', Qt ω' ∂μ)) =
        F ω * (Q ω - ∫ ω', Q ω' ∂μ) := fun ω => by
      have q1 : ∀ ω, conj (Qt ω) = Q ω := fun ω => conj_Q _ _ _ _
      rw [map_mul, map_sub, ← integral_conj, ← conj_F, Complex.conj_conj]
      simp only [q1]
      rfl
    simp only [e]
  have eM : ∫ ω, star (physVec v₂) ⬝ᵥ ((kHat b E X * mbarSide b E X false *
      wordVal (kHat b E X) (gRes b E X ω) ![] ![1]) *ᵥ xc) * (Qt ω - ∫ ω', Qt ω' ∂μ) ∂μ = 0 := by
    have e : ∀ ω, wordVal (kHat b E X) (gRes b E X ω) ![] ![1] = 1 := fun ω => by
      simp [wordVal_zero]
    simp only [e]
    rw [integral_const_mul, integral_sub hQt (integrable_const _), integral_const, probReal_univ,
      one_smul, sub_self, mul_zero]
  have eJ : ∑ j : Fin 0, ∑ q : Fin 2, (∫ ω, SourceMixing.blkTr (gSide b E X false ω *
        wordAlpha (kHat b E X) (gRes b E X ω) 0 ![] ![1] j) q ∂μ) *
      ∫ ω, star xc' ⬝ᵥ ((dRow b q * wordGamma (kHat b E X) (gRes b E X ω) 0 ![] ![1] j) *ᵥ
        xc) * (Qt ω - ∫ ω', Qt ω' ∂μ) ∂μ = 0 := Fin.sum_univ_zero _
  rw [eM, eJ, sub_zero, sub_zero, vecNorm_physVec] at h
  rw [eL, ← map_sub, Complex.norm_conj]
  exact h

end BlockBand.Transmission.PassiveCovariance
