module

public import BlockBand.Transmission.PassiveCovariance.MainTerm

/-!
# Measurability of the fresh transport and the crude covariance bound

* `measurable_freshU`: `ω ↦ U(ω) = L(ω)L(ω)*` is measurable on `LayerSample W .oneBlockOnePort`
  for every deterministic `X` (Lean's totalized inverse is measurable: `M⁻¹ = det(M)⁻¹ adj M`).
* `enorm_bilinearCovariance_le`: Cauchy–Schwarz,
  `|E[(v₁*U⁰v₂)(v₃*U⁰v₄)]| ≤ ‖v₁*U⁰v₂‖₂ ‖v₃*U⁰v₄‖₂` (no integrability hypothesis: a
  non-integrable integrand has Bochner integral `0`).
* `PassiveFluctuationL2`: the `L²` bound `‖u*U⁰v‖₂ ≤ C W^{-1/2}‖u‖‖v‖` uniformly in passive `X`
  (the `p = 2` case of the fluctuation bound of the passive bounds lemma, i.e. of
  `PassiveSourceMixingContract.oneStepFluctuation`, first conjunct;
  `passiveFluctuationL2_of_mixing`).
* `crudeCovariance_of_fluctuation`: it gives `|Cov| ≤ C₁W⁻¹∏‖v_j‖` uniformly in passive `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

/-!
## Measurability
-/

theorem measurable_matrix_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable (fun M : Matrix n n ℂ => M⁻¹) := by
  have h : (fun M : Matrix n n ℂ => M⁻¹) = fun M => Ring.inverse M.det • M.adjugate := by
    funext M; exact Matrix.inv_def M
  rw [h]
  simp only [Ring.inverse_eq_inv']
  exact ((continuous_id.matrix_det).measurable.inv).smul (continuous_id.matrix_adjugate).measurable

variable {W : ℕ}

theorem measurable_layerA (a : Fin 1) (x y : Fin W) :
    Measurable (fun ω : LayerSample W .oneBlockOnePort => ω.1 a x y) :=
  ((measurable_pi_apply a).comp measurable_fst).eval_matrix

theorem measurable_layerB (a p : Fin 1) (x y : Fin W) :
    Measurable (fun ω : LayerSample W .oneBlockOnePort => ω.2 a p x y) :=
  ((measurable_pi_apply p).comp ((measurable_pi_apply a).comp measurable_snd)).eval_matrix

theorem measurable_layerMatrix (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun ω : LayerSample W .oneBlockOnePort => layerMatrix .oneBlockOnePort E z
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [layerMatrix, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix,
      Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply]
  · split_ifs
    · exact ((measurable_layerA _ _ _).sub_const _).sub_const _
    · exact (measurable_const.sub_const _).sub_const _
  · split_ifs
    · exact measurable_layerB _ _ _ _
    · exact measurable_const
  · split_ifs
    · exact continuous_star.measurable.comp (measurable_layerB _ _ _ _)
    · exact measurable_const
  · exact measurable_const

theorem measurable_freshLayer (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshLayer b E X) :=
  measurable_matrix_inv.comp (measurable_layerMatrix E (boundaryZ b E) X)

theorem measurable_freshL (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshL b E X) := by
  have hG : Measurable fun ω => Matrix.of fun x y =>
      freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y)) :=
    Measurable.of_eval_matrix _ fun x y => (measurable_freshLayer b E X).eval_matrix
  exact (continuous_const.matrix_mul continuous_id).measurable.comp hG

theorem measurable_freshU (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (freshU b E X) :=
  (continuous_id.matrix_mul continuous_id.matrix_conjTranspose).measurable.comp
    (measurable_freshL b E X)

theorem measurable_bilinear_centered (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (C : Matrix (Fin W) (Fin W) ℂ) (u v : Fin W → ℂ) :
    Measurable fun ω => bilinear u (freshU b E X ω - C) v := by
  have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u (M - C) v := by
    unfold bilinear; fun_prop
  exact hc.measurable.comp (measurable_freshU b E X)

/-!
## Cauchy–Schwarz for the bilinear covariance
-/

theorem enorm_bilinearCovariance_le {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (μ : Measure Ω) (U : Ω → Matrix n n ℂ) (v₁ v₂ v₃ v₄ : n → ℂ)
    (hF : AEMeasurable (fun ω => bilinear v₁ (U ω - matrixExpect μ U) v₂) μ)
    (hG : AEMeasurable (fun ω => bilinear v₃ (U ω - matrixExpect μ U) v₄) μ) :
    ‖bilinearCovariance μ U v₁ v₂ v₃ v₄‖ₑ ≤
      eLpNorm (fun ω => bilinear v₁ (U ω - matrixExpect μ U) v₂) 2 μ *
        eLpNorm (fun ω => bilinear v₃ (U ω - matrixExpect μ U) v₄) 2 μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp only [enorm_mul]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF.enorm hG.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hG.aestronglyMeasurable]
  simpa using h

/-- **The `L²` fluctuation bound** for the centered bilinear entries of `U = LL*`, uniformly in
passive `X` (the case `p = 2` of the fluctuation bound of the passive bounds lemma). -/
def PassiveFluctuationL2 : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) 2 (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

/-- `PassiveFluctuationL2` is the `p = 2` case of `oneStepFluctuation` (first conjunct). -/
theorem passiveFluctuationL2_of_mixing (h : PassiveSourceMixingContract) :
    PassiveFluctuationL2 := by
  intro b hb0 hb E h1 h2
  obtain ⟨C, W₀, hC⟩ := h.oneStepFluctuation b hb0 hb E h1 h2 2 one_le_two
  refine ⟨C, W₀, fun W hW X hX u v => ?_⟩
  have := (hC W hW X hX u v).1
  rwa [ENNReal.ofReal_ofNat] at this

/-- **Crude covariance bound**: from `PassiveFluctuationL2`,
`|E[(v₁*U⁰v₂)(v₃*U⁰v₄)]| ≤ C₁W⁻¹∏‖v_j‖` uniformly in passive `X`. -/
theorem crudeCovariance_of_fluctuation (h : PassiveFluctuationL2) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∃ (C₁ : ℝ) (W₀ : ℕ), 0 ≤ C₁ ∧ ∀ W : ℕ, W₀ ≤ W →
        ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
          ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄‖ ≤
            C₁ / W * fourNorm v₁ v₂ v₃ v₄ := by
  intro b hb0 hb E h1 h2
  obtain ⟨C, W₀, hC⟩ := h b hb0 hb E h1 h2
  refine ⟨|C| ^ 2, W₀, sq_nonneg _, fun W hW X hX v₁ v₂ v₃ v₄ => ?_⟩
  set μ := freshLaw W b
  have hle : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
      matrixExpect μ (freshU b E X)) v) 2 μ ≤
      ENNReal.ofReal (|C| / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    (hC W hW X hX u v).trans (ENNReal.ofReal_le_ofReal (by
      have := vecNorm_nonneg u; have := vecNorm_nonneg v
      gcongr; exact le_abs_self C))
  have hcs := enorm_bilinearCovariance_le μ (freshU b E X) v₁ v₂ v₃ v₄
    (measurable_bilinear_centered b E X _ v₁ v₂).aemeasurable
    (measurable_bilinear_centered b E X _ v₃ v₄).aemeasurable
  have hprod := hcs.trans (mul_le_mul' (hle v₁ v₂) (hle v₃ v₄))
  have hn := fun v : Fin W → ℂ => vecNorm_nonneg v
  have ha : 0 ≤ |C| / Real.sqrt W * vecNorm v₁ * vecNorm v₂ := by
    have := hn v₁; have := hn v₂; positivity
  rw [← ENNReal.ofReal_mul ha, ← ofReal_norm] at hprod
  have hb' := (ENNReal.ofReal_le_ofReal_iff (by have := hn v₃; have := hn v₄; positivity)).mp hprod
  refine hb'.trans (le_of_eq ?_)
  rw [fourNorm]
  rcases (Nat.cast_nonneg W : (0 : ℝ) ≤ W).lt_or_eq with hWp | hWz
  · have hs : Real.sqrt W ^ 2 = W := Real.sq_sqrt hWp.le
    have hs0 : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hWp).ne'
    field_simp
    rw [hs]
    ring
  · rw [← hWz]; simp

end BlockBand.Transmission.PassiveCovariance
