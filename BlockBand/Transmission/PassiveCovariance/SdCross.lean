module

public import BlockBand.Transmission.PassiveCovariance.SdLetter

/-!
# The crossed term of `sd_expand` against `Q⁰`

Hypotheses `PassiveBoundsStatement` and `GaussianPoincare` (through `wordForm_covariance`). Law
`layerLaw W b .oneBlockOnePort`, `z = z_∂(E)`, strictly passive `X`; `b, E, L_w, K_d` and the side
`adj` are fixed, then `C, W₀`; uniform in `X`, the words and the vectors.

The third error term of the first-letter expansion.

For `Q = u*w₂(𝒢)v` the last term of `sd_expand` with `Ψ = Q - EQ`, `DΨ = DQ`, is
`Σ_{α,γ} σ(α,γ) E[x̄_α(𝔊Nc)_γ DQ(E_{γα})] = -Σ_k Σ_{p,p'} s_{pp'} E[F1_{kp}F2_{kp'}]`
(`crossed_pt`), with the dressed forms `F1_{kp} = x*P_pγ'_kv`, `F2_{kp'} = u*α'_kP_{p'}𝔊Nc`.

* **`crossTerm_Q`**: `|Σσ E[x̄(𝔊Nc)DQ] + Σ_k Σ_{p,p'} s_{pp'}E[F1]E[F2]| ≤ (C/W²)‖x‖‖v‖‖u‖‖c‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `E[FG] - EF·EG = E[(F - EF)(G - EG)]`, with integrability of `FG`. -/
theorem integral_mul_sub_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F G : Ω → ℂ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hc : Integrable (fun ω => (F ω - ∫ ω', F ω' ∂μ) * (G ω - ∫ ω', G ω' ∂μ)) μ) :
    Integrable (fun ω => F ω * G ω) μ ∧
      ∫ ω, F ω * G ω ∂μ - (∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ =
        ∫ ω, (F ω - ∫ ω', F ω' ∂μ) * (G ω - ∫ ω', G ω' ∂μ) ∂μ := by
  set a := ∫ ω', F ω' ∂μ
  set c := ∫ ω', G ω' ∂μ
  have e : (fun ω => F ω * G ω) = fun ω => ((F ω - a) * (G ω - c) + (a * G ω + c * F ω)) - a * c := by
    funext ω; ring
  have i1 : Integrable (fun ω => a * G ω + c * F ω) μ := (hG.const_mul a).add (hF.const_mul c)
  have i2 : Integrable (fun ω => (F ω - a) * (G ω - c) + (a * G ω + c * F ω)) μ := hc.add i1
  refine ⟨by rw [e]; exact i2.sub (integrable_const _), ?_⟩
  rw [e, integral_sub i2 (integrable_const _), integral_add hc i1, integral_add (hG.const_mul a)
    (hF.const_mul c), integral_const_mul, integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- Integrability of dressed forms, uniformly over passive inputs. -/
theorem integrable_wordForm_unif (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) →
      ∀ a c : LayerSite W .oneBlockOnePort → ℂ,
        Integrable (fun ω => wordForm (kHat b E X) a c wd D (gRes b E X ω))
          (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₀, hP⟩ := memLp_poly hA hb0 hb h1 h2 (Lw + 1)
  refine ⟨W₀, fun W hW X hX ℓ hℓ wd D hD a c => ?_⟩
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  exact (hP W hW X hX _ (measurable_wordForm _ a c wd D
    (measurable_layerRes E (boundaryZ b E) X)).aestronglyMeasurable _ (Lw + 1) le_rfl
    fun ω => (wordForm_poly_bounds b E X hKd hℓ wd D hD a c ω).1).integrable one_le_two

/-- **The crossed term against `Q⁰`.** -/
theorem crossTerm_Q (hP : GaussianPoincare) (hA : PassiveBoundsStatement) {b E : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) (adj : Bool) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4)
      (D : Fin (ℓ + 1) → LayerMat W), (∀ j, ‖D j‖ ≤ Kd) → ∀ ℓ₂ : ℕ, ℓ₂ ≤ Lw →
      ∀ (wd₂ : Fin ℓ₂ → Fin 4) (D₂ : Fin (ℓ₂ + 1) → LayerMat W), (∀ j, ‖D₂ j‖ ≤ Kd) →
      ∀ x c u v : LayerSite W .oneBlockOnePort → ℂ,
        let μ := layerLaw W b .oneBlockOnePort
        let Kh := kHat b E X
        let M := fun ω => gSide b E X adj ω * wordVal Kh (gRes b E X ω) wd D
        let F1 := fun (k : Fin ℓ₂) (p : Fin 2) ω =>
          star x ⬝ᵥ ((bProj p * wordGamma Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k) *ᵥ v)
        let F2 := fun (k : Fin ℓ₂) (p' : Fin 2) ω =>
          star u ⬝ᵥ ((wordAlpha Kh (gRes b E X ω) ℓ₂ wd₂ D₂ k * bProj p' * M ω) *ᵥ c)
        ‖(∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (x α) * (M ω *ᵥ c) γ *
            wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ) +
          ∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' *
            ((∫ ω, F1 k p ω ∂μ) * ∫ ω, F2 k p' ω ∂μ)‖ ≤
          C / (W : ℝ) ^ 2 * (vecNorm x * vecNorm v * (vecNorm u * vecNorm c)) := by
  set Kd' := max Kd 1 ^ 2
  obtain ⟨Cv, Wv, hCv, hcov⟩ := wordForm_covariance hP hA hb0 hb h1 h2 (2 * Lw + 1) Kd'
  obtain ⟨Wi, hint⟩ := integrable_wordForm_unif hA hb0 hb h1 h2 (2 * Lw + 1) Kd'
  obtain ⟨Wp, hpoly⟩ := memLp_poly hA hb0 hb h1 h2 (2 * Lw + 3)
  refine ⟨Lw * 4 * Cv, max Wv (max Wi Wp), by positivity,
    fun W hW X hX ℓ hℓ wd D hD ℓ₂ hℓ₂ wd₂ D₂ hD₂ x c u v => ?_⟩
  intro μ Kh M F1 F2
  have hWv : Wv ≤ W := le_trans (le_max_left _ _) hW
  have hWi : Wi ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWp : Wp ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hD 0)
  have hK1 : 1 ≤ max Kd 1 := le_max_right _ _
  have hKK : max Kd 1 ≤ Kd' := by nlinarith
  have hD' : ∀ i, ‖D i‖ ≤ max Kd 1 := fun i => (hD i).trans (le_max_left _ _)
  have hD₂' : ∀ i, ‖D₂ i‖ ≤ max Kd 1 := fun i => (hD₂ i).trans (le_max_left _ _)
  -- the words of `F1`, `F2`
  have hw : ∀ k p p', Integrable (F1 k p) μ ∧ Integrable (F2 k p') μ ∧
      Integrable (fun ω => (F1 k p ω - ∫ ω', F1 k p ω' ∂μ) * (F2 k p' ω - ∫ ω', F2 k p' ω' ∂μ)) μ ∧
      ‖∫ ω, (F1 k p ω - ∫ ω', F1 k p ω' ∂μ) * (F2 k p' ω - ∫ ω', F2 k p' ω' ∂μ) ∂μ‖ ≤
        Cv / W * (vecNorm x * vecNorm v * (vecNorm u * vecNorm c)) := by
    intro k p p'
    obtain ⟨ℓA, wdA, DA, hlA, hFA, hGA⟩ := wordAlpha_word Kh ℓ₂ wd₂ D₂ k
    obtain ⟨ℓG, wdG, DG, hlG, hFG, hGG⟩ := wordGamma_word Kh ℓ₂ wd₂ D₂ k
    have hDA := hFA.norm_le hK1 hD₂'
    have hDG := hFG.norm_le hK1 hD₂'
    have hDS := norm_cons_one_le hK1 hD'
    have hcat := norm_catD_le hK1 (bProj p') (norm_bProj_le p') (Fin.cons 1 D) hDS ℓA DA hDA
    have hpre : ∀ i, ‖preD (bProj p) DG i‖ ≤ Kd' := fun i =>
      (norm_preD_le (norm_bProj_le p) hDG i).trans hKK
    have e1 : F1 k p = fun ω => wordForm Kh x v wdG (preD (bProj p) DG) (gRes b E X ω) := by
      funext ω; simp only [F1]; rw [hGG, wordForm, wordVal_preD]
    have e2 : F2 k p' = fun ω => wordForm Kh u c (catWd (Fin.cons (sideLetter adj) wd) ℓA wdA)
        (catD (bProj p') (Fin.cons 1 D) ℓA DA) (gRes b E X ω) := by
      funext ω
      simp only [F2, M]
      rw [hGA, wordForm, wordVal_cat, gSide_letter, letter_mul_wordVal]
    rw [e1, e2]
    obtain ⟨hi, hb'⟩ := hcov W hWv X hX ℓG (by omega) wdG _ hpre (ℓ + 1 + ℓA) (by omega) _ _ hcat
      x v u c
    exact ⟨hint W hWi X hX.posSemidef ℓG (by omega) wdG _ hpre x v,
      hint W hWi X hX.posSemidef _ (by omega) _ _ hcat u c, hi, hb'⟩
  -- integrability of the site terms
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have cS := continuous_gSideOf (W := W) adj
  have cN := continuous_wordVal Kh wd D
  have pM : PolyBM (fun ω => 1 + btFun b E X ω) M (1 + (Lw + 1)) :=
    (polyBM_gSide b E X adj).mul (polyBM_wordVal b E X hKd hℓ wd D hD)
  have hfi : ∀ α γ, Integrable (fun ω => star (x α) * (M ω *ᵥ c) γ *
      wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) μ := by
    intro α γ
    have pD : PolyB (fun ω => 1 + btFun b E X ω)
        (fun ω => wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) (Lw + 1) :=
      ⟨Lw * max Kd 1 ^ (Lw + 1) * ‖(Matrix.single γ α 1 : LayerMat W)‖ * (vecNorm u * vecNorm v),
        by have := vecNorm_nonneg u; have := vecNorm_nonneg v; positivity,
        fun ω => (wordForm_poly_bounds b E X hKd hℓ₂ wd₂ D₂ hD₂ u v ω).2 _⟩
    obtain ⟨Cf, -, hCf⟩ := ((PolyB.const (star (x α))).mul (PolyB.vecEntry pM c γ)).mul pD
    have hm : Measurable fun ω => star (x α) * (M ω *ᵥ c) γ *
        wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) :=
      (measurable_const.mul (((continuous_apply γ).comp ((cS.matrix_mul cN).matrix_mulVec
        continuous_const)).measurable.comp hGm)).mul
        (measurable_wordFormDeriv Kh u v wd₂ D₂ hGm _)
    exact (hpoly W hWp X hX.posSemidef _ hm.aestronglyMeasurable Cf _ (by omega) hCf).integrable
      one_le_two
  -- the pointwise block form
  have hpt : ∀ ω, ∑ α, ∑ γ, siteVar W b α γ * (star (x α) * (M ω *ᵥ c) γ *
      wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) =
      -∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' * (F1 k p ω * F2 k p' ω) := fun ω => by
    simp only [wordFormDeriv_apply]
    exact crossed_pt b x u v c (M ω) _ _
  have hsum : (∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (x α) * (M ω *ᵥ c) γ *
      wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ) =
      -∑ k, ∑ p : Fin 2, ∑ p' : Fin 2, bVar W b p p' * ∫ ω, F1 k p ω * F2 k p' ω ∂μ := by
    have hl : (∑ α, ∑ γ, siteVar W b α γ * ∫ ω, star (x α) * (M ω *ᵥ c) γ *
        wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1) ∂μ) =
        ∫ ω, ∑ α, ∑ γ, siteVar W b α γ * (star (x α) * (M ω *ᵥ c) γ *
          wordFormDeriv Kh u v wd₂ D₂ (gRes b E X ω) (Matrix.single γ α 1)) ∂μ := by
      rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun γ _ => (hfi α γ).const_mul _]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [integral_finsetSum _ fun γ _ => (hfi α γ).const_mul _]
      exact Finset.sum_congr rfl fun γ _ => (integral_const_mul _ _).symm
    have hFF : ∀ k p p', Integrable (fun ω => F1 k p ω * F2 k p' ω) μ := fun k p p' =>
      (integral_mul_sub_mul (hw k p p').1 (hw k p p').2.1 (hw k p p').2.2.1).1
    rw [hl]
    simp only [hpt]
    rw [integral_neg, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun p _ =>
      integrable_finsetSum _ fun p' _ => (hFF k p p').const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun p' _ => (hFF k p p').const_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun p' _ => (hFF k p p').const_mul _]
    exact Finset.sum_congr rfl fun p' _ => integral_const_mul _ _
  rw [hsum, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set P := vecNorm x * vecNorm v * (vecNorm u * vecNorm c)
  have hP0 : 0 ≤ P := by
    have := vecNorm_nonneg x; have := vecNorm_nonneg v; have := vecNorm_nonneg u
    have := vecNorm_nonneg c; positivity
  have hterm : ∀ k p p', ‖bVar W b p p' * ((∫ ω, F1 k p ω ∂μ) * ∫ ω, F2 k p' ω ∂μ) -
      bVar W b p p' * ∫ ω, F1 k p ω * F2 k p' ω ∂μ‖ ≤ Cv / (W : ℝ) ^ 2 * P := by
    intro k p p'
    rw [norm_sub_rev, ← mul_sub, norm_mul, (integral_mul_sub_mul (hw k p p').1 (hw k p p').2.1
      (hw k p p').2.2.1).2]
    calc _ ≤ 1 / W * (Cv / W * P) := mul_le_mul (norm_bVar_le b hb0.le hb p p') (hw k p p').2.2.2
          (norm_nonneg _) (by positivity)
      _ = Cv / (W : ℝ) ^ 2 * P := by
          rcases eq_or_lt_of_le hW0 with h0 | h0
          · rw [← h0]; simp
          · field_simp
  calc _ ≤ ∑ _k : Fin ℓ₂, 4 * (Cv / (W : ℝ) ^ 2 * P) := by
        refine Finset.sum_le_sum fun k _ => ?_
        try simp only [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        calc _ ≤ ∑ _p : Fin 2, 2 * (Cv / (W : ℝ) ^ 2 * P) := by
              refine Finset.sum_le_sum fun p _ => ?_
              refine (norm_sum_le _ _).trans ?_
              calc _ ≤ ∑ _p' : Fin 2, Cv / (W : ℝ) ^ 2 * P :=
                    Finset.sum_le_sum fun p' _ => hterm k p p'
                _ = _ := by simp
          _ = _ := by simp; ring
    _ = ℓ₂ * (4 * (Cv / (W : ℝ) ^ 2 * P)) := by simp
    _ ≤ Lw * (4 * (Cv / (W : ℝ) ^ 2 * P)) := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.PassiveCovariance
