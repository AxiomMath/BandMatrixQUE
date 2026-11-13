module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanSD

/-!
# The right mean identity for `F = 𝒢₁₂𝒢₂₁` (strictly passive `X`)

With `F = 𝒢₁₂𝒢₂₁` (`fGap`), `τ₀ = ⟨F⟩`, `τ₁ = ⟨𝒢₂₂²⟩` (the blocks of `T = 𝒢P₂𝒢`), `⟨𝒢₁₁⟩ = physTr`,
`⟨𝒢₂₂⟩ = portTr`:
* `meanSD_gap_matrix`: `E·EF + EF·X = -c E[τ₀𝒢₁₁ + ⟨𝒢₁₁⟩F] - b E[τ₁𝒢₁₁ + ⟨𝒢₂₂⟩F]`
  (from `meanSD_gap_right_of` and `TV = 𝒢P₂ - TH₀`, `(𝒢P₂)₁₁ = 0`).

This identity gives the exact form of `EΓ` in `gap_mean_eq`:
`EΓ = (z+E)E[L𝒢₂₁] + c(E[τ₀K𝒢₁₁] + E[⟨𝒢₁₁⟩L𝒢₂₁]) + b(E[τ₁K𝒢₁₁] + E[⟨𝒢₂₂⟩L𝒢₂₁])`.
As in `delta_mean_eq`, only `K` times the identity is used (`EΓ = K·EF·K`,
`EF·K = z·EF - EF·X`), so every term carries a bounded letter.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer (passiveLetter layerAt g11 g12 g21 g22 kG11 lAt)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `F = 𝒢₁₂𝒢₂₁`. -/
abbrev fGap (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  passiveLetter E (boundaryZ b E) X ω 1 * passiveLetter E (boundaryZ b E) X ω 2

/-- `τ₀ = ⟨𝒢₁₂𝒢₂₁⟩`. -/
abbrev tau0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (fGap b E X ω).trace

/-- `τ₁ = ⟨𝒢₂₂𝒢₂₂⟩`. -/
abbrev tau1 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 3 * passiveLetter E (boundaryZ b E) X ω 3).trace

theorem tGap_phys (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (x : Fin W) (β : LayerSite W .oneBlockOnePort) :
    tGap b E X ω (phys x) β = ∑ k, gRes b E X ω (phys x) (port k) * gRes b E X ω (port k) β := by
  simp only [tGap, Matrix.mul_apply, portProj, fromBlocks]
  simp [Matrix.one_apply]
  rw [Fintype.sum_prod_type]; simp

theorem tGap_port (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (x : Fin W) (β : LayerSite W .oneBlockOnePort) :
    tGap b E X ω (port x) β = ∑ k, gRes b E X ω (port x) (port k) * gRes b E X ω (port k) β := by
  simp only [tGap, Matrix.mul_apply, portProj, fromBlocks]
  simp [Matrix.one_apply]
  rw [Fintype.sum_prod_type]; simp

theorem fGap_apply (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (x y : Fin W) : fGap b E X ω x y = tGap b E X ω (phys x) (phys y) := by
  rw [tGap_phys]; rfl

theorem sum_tGap_phys (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ∑ a, tGap b E X ω (phys a) (phys a) = (fGap b E X ω).trace := by
  simp only [Matrix.trace, Matrix.diag, fGap_apply]

theorem sum_tGap_port (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ∑ a, tGap b E X ω (port a) (port a) =
      (passiveLetter E (boundaryZ b E) X ω 3 * passiveLetter E (boundaryZ b E) X ω 3).trace := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tGap_port]; rfl

theorem norm_g11_le' (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖g11 E w X ω‖ ≤ ‖layerAt E w X ω‖ := by
  have : g11 E w X ω = (layerAt E w X ω).submatrix (fun x => Sum.inl ((0 : Fin 1), x))
      (fun y => Sum.inl ((0 : Fin 1), y)) := by ext; rfl
  rw [this]
  exact PassiveLayer.norm_submatrix_le _ (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)

/-- `‖ℓ_k‖ ≤ ‖𝒢‖` for the four resolvent blocks. -/
theorem norm_letter_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (k : Fin 4) : ‖passiveLetter E (boundaryZ b E) X ω k.castSucc.castSucc‖ ≤ ‖gRes b E X ω‖ := by
  fin_cases k
  · exact norm_g11_le' E _ X ω
  · exact FullSource.norm_g12_le E _ X ω
  · exact norm_g21_le E _ X ω
  · exact norm_g22_le E _ X ω

theorem norm_fGap_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ‖fGap b E X ω‖ ≤ ‖gRes b E X ω‖ ^ 2 := by
  have h1 := norm_letter_le b E X ω 1
  have h2 := norm_letter_le b E X ω 2
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

section Eq
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C4 C6 : ℝ}

/-- Entry integrability of the five random matrices of `meanSD_gap_matrix`. -/
theorem gap_integrable
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hm6 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (3 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C6) (x y : Fin W) :
    let μ := layerLaw W b .oneBlockOnePort
    Integrable (fun ω => fGap b E X ω x y) μ ∧
      Integrable (fun ω => (tau0 b E X ω • passiveLetter E (boundaryZ b E) X ω 0) x y) μ ∧
      Integrable (fun ω => (physTr b E X ω • fGap b E X ω) x y) μ ∧
      Integrable (fun ω => (tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 0) x y) μ ∧
      Integrable (fun ω => (portTr b E X ω • fGap b E X ω) x y) μ := by
  intro μ
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hL : ∀ k : Fin 6, Measurable fun ω => passiveLetter E (boundaryZ b E) X ω k := by
    intro k
    exact PassiveLayer.measurable_passiveLetter (W := W) E (boundaryZ b E) X k
  have hF : Measurable fun ω => fGap b E X ω := (hL 1).mul (hL 2)
  have htr : ∀ {f : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ}, Measurable f →
      Measurable fun ω => (W : ℂ)⁻¹ * (f ω).trace := fun hf =>
    measurable_const.mul (continuous_id.matrix_trace.measurable.comp hf)
  have hn : ∀ M : Matrix (Fin W) (Fin W) ℂ, ‖(W : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ := PathScalar.norm_normTrace_le
  have hg := fun ω => norm_nonneg (gRes b E X ω)
  have hl0 := fun ω => norm_letter_le b E X ω 0
  have hl3 := fun ω => norm_letter_le b E X ω 3
  refine ⟨(memLp_two_of_le_pow hF.eval_matrix zero_le_one 2 (by norm_num) hm4 fun ω => ?_).integrable
    one_le_two, (memLp_two_of_le_pow
    (f := fun ω => (tau0 b E X ω • passiveLetter E (boundaryZ b E) X ω 0) x y)
    ((htr hF).smul (hL 0)).eval_matrix zero_le_one 3 (by norm_num)
    hm6 fun ω => ?_).integrable one_le_two, (memLp_two_of_le_pow
    (f := fun ω => (physTr b E X ω • fGap b E X ω) x y) ((htr (hL 0)).smul hF).eval_matrix
    zero_le_one 3 (by norm_num) hm6 fun ω => ?_).integrable one_le_two,
    (memLp_two_of_le_pow (f := fun ω => (tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 0) x y)
    ((htr ((hL 3).mul (hL 3))).smul (hL 0)).eval_matrix zero_le_one 3
    (by norm_num) hm6 fun ω => ?_).integrable one_le_two, (memLp_two_of_le_pow
    (f := fun ω => (portTr b E X ω • fGap b E X ω) x y)
    ((htr (hL 3)).smul hF).eval_matrix zero_le_one 3 (by norm_num) hm6 fun ω => ?_).integrable
    one_le_two⟩
  · rw [one_mul]; exact (norm_entry_le' _ x y).trans (norm_fGap_le b E X ω)
  · rw [one_mul, Matrix.smul_apply, smul_eq_mul, norm_mul, pow_succ]
    exact mul_le_mul ((hn _).trans (norm_fGap_le b E X ω))
      ((norm_entry_le' _ x y).trans (hl0 ω)) (norm_nonneg _) (by positivity)
  · rw [one_mul, Matrix.smul_apply, smul_eq_mul, norm_mul, pow_succ, mul_comm]
    exact mul_le_mul ((norm_entry_le' _ x y).trans (norm_fGap_le b E X ω)) ((hn _).trans (hl0 ω))
      (norm_nonneg _) (by positivity)
  · rw [one_mul, Matrix.smul_apply, smul_eq_mul, norm_mul, pow_succ]
    have h33 : ‖passiveLetter E (boundaryZ b E) X ω 3 * passiveLetter E (boundaryZ b E) X ω 3‖ ≤
        ‖gRes b E X ω‖ ^ 2 := by
      rw [sq]; exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul (hl3 ω) (hl3 ω) (norm_nonneg _)
        (hg ω))
    exact mul_le_mul ((hn _).trans h33) ((norm_entry_le' _ x y).trans (hl0 ω)) (norm_nonneg _)
      (by positivity)
  · rw [one_mul, Matrix.smul_apply, smul_eq_mul, norm_mul, pow_succ, mul_comm]
    exact mul_le_mul ((norm_entry_le' _ x y).trans (norm_fGap_le b E X ω)) ((hn _).trans (hl3 ω))
      (norm_nonneg _) (by positivity)

theorem portProj_apply_phys (γ : LayerSite W .oneBlockOnePort) (y : Fin W) :
    (portProj : LayerMat W) γ (phys y) = 0 := by
  rcases γ with ⟨i, k⟩ | ⟨i, k⟩ <;> simp [portProj, fromBlocks]

theorem mul_portProj_phys (M : LayerMat W) (α : LayerSite W .oneBlockOnePort) (y : Fin W) :
    (M * portProj : LayerMat W) α (phys y) = 0 := by
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun γ _ => by rw [portProj_apply_phys, mul_zero]

theorem matrixExpect_add' {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F G : Ω → Matrix n n ℂ) (hF : ∀ x y, Integrable (fun ω => F ω x y) μ)
    (hG : ∀ x y, Integrable (fun ω => G ω x y) μ) :
    matrixExpect μ (fun ω => F ω + G ω) = matrixExpect μ F + matrixExpect μ G := by
  ext x y
  simp only [matrixExpect, Matrix.of_apply, Matrix.add_apply]
  exact integral_add (hF x y) (hG x y)

/-- **The right mean identity for `F = 𝒢₁₂𝒢₂₁` in matrix form.** -/
theorem meanSD_gap_matrix (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hX : (passiveY X).PosDef)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hm6 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (3 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C6) (hW : 0 < W) :
    let μ := layerLaw W b .oneBlockOnePort
    let F0 := matrixExpect μ (fGap b E X)
    (E : ℂ) • F0 + F0 * X =
      -((1 - 2 * b : ℝ) : ℂ) • matrixExpect μ (fun ω => tau0 b E X ω •
          passiveLetter E (boundaryZ b E) X ω 0 + physTr b E X ω • fGap b E X ω) -
        (b : ℂ) • matrixExpect μ (fun ω => tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 0 +
          portTr b E X ω • fGap b E X ω) := by
  intro μ F0
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  ext x y
  have hint := fun x y => gap_integrable (b := b) (E := E) (X := X) hm4 hm6 x y
  have hSD := meanSD_gap_right_of hη hX hm4 hm6 (phys x) y
  set H₀ := layerMatrix .oneBlockOnePort E (boundaryZ b E)
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0
  have hl : ∫ ω, (tGap b E X ω * layerLin ω) (phys x) (phys y) ∂μ =
      (E : ℂ) * F0 x y + ∑ k, F0 x k * X k y := by
    have hi : ∀ k, Integrable (fun ω => fGap b E X ω x k * X k y) μ :=
      fun k => (hint x k).1.mul_const _
    calc ∫ ω, (tGap b E X ω * layerLin ω) (phys x) (phys y) ∂μ
        = ∫ ω, (E : ℂ) * fGap b E X ω x y + ∑ k, fGap b E X ω x k * X k y ∂μ := by
          refine integral_congr_ae ((FullSource.ae_mul_layerLin hb h1 h2 hX).mono fun ω h => ?_)
          have e : tGap b E X ω * layerLin ω = gRes b E X ω * portProj - tGap b E X ω * H₀ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h]
            simp only [tGap, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
            rfl
          have h0 : (gRes b E X ω * portProj : LayerMat W) (phys x) (phys y) = 0 := by
            exact mul_portProj_phys _ _ _
          dsimp only
          rw [e, Matrix.sub_apply, FullSource.H0_phys_right, h0]
          simp only [fGap_apply]; ring
      _ = _ := by
          rw [integral_add ((hint x y).1.const_mul _) (integrable_finsetSum _ fun k _ => hi k),
            integral_const_mul, integral_finsetSum _ fun k _ => hi k]
          simp only [integral_mul_const, F0, matrixExpect, Matrix.of_apply]
          rfl
  rw [gueVar_cast hb, ginVar_cast hb0] at hSD
  have e1 : ∫ ω, (∑ a, tGap b E X ω (phys a) (phys a)) * gRes b E X ω (phys x) (phys y) +
      (∑ a, gRes b E X ω (phys a) (phys a)) * tGap b E X ω (phys x) (phys y) ∂μ =
      (W : ℂ) * ∫ ω, (tau0 b E X ω • passiveLetter E (boundaryZ b E) X ω 0 +
        physTr b E X ω • fGap b E X ω) x y ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω
    rw [sum_tGap_phys, ← fGap_apply, ← trace_letter0]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, tau0, physTr]
    field_simp; rfl
  have e2 : ∫ ω, (∑ a, tGap b E X ω (port a) (port a)) * gRes b E X ω (phys x) (phys y) +
      (∑ a, gRes b E X ω (port a) (port a)) * tGap b E X ω (phys x) (phys y) ∂μ =
      (W : ℂ) * ∫ ω, (tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 0 +
        portTr b E X ω • fGap b E X ω) x y ∂μ := by
    rw [← integral_const_mul]; congr 1; funext ω
    rw [sum_tGap_port, ← fGap_apply, ← trace_letter3]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, tau1, portTr]
    field_simp; rfl
  calc ((E : ℂ) • F0 + F0 * X) x y = (E : ℂ) * F0 x y + ∑ k, F0 x k * X k y := by
        simp [Matrix.add_apply, Matrix.mul_apply]
    _ = ∫ ω, (tGap b E X ω * layerLin ω) (phys x) (phys y) ∂μ := hl.symm
    _ = -(((1 - 2 * b : ℝ) : ℂ) * ∫ ω, (tau0 b E X ω • passiveLetter E (boundaryZ b E) X ω 0 +
          physTr b E X ω • fGap b E X ω) x y ∂μ) -
          (b : ℂ) * ∫ ω, (tau1 b E X ω • passiveLetter E (boundaryZ b E) X ω 0 +
            portTr b E X ω • fGap b E X ω) x y ∂μ := by
        rw [hSD, e1, e2]; field_simp
    _ = _ := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, matrixExpect,
          Matrix.of_apply, neg_mul]

end Eq

end BlockBand.SourceProcess.CompleteSourceGap
