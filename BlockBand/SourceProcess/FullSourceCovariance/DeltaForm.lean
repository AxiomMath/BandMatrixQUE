module

public import BlockBand.SourceProcess.FullSourceCovariance.DeltaIBP
public import BlockBand.Transmission.LengthUniform.BulkReplica

/-!
# `Δ`-forms as resolvent forms, their layer derivatives and their integrability

Bilinear forms of `Δ` are resolvent forms of the layer matrix; this gives their layer derivatives
and the integrability needed for the integration by parts `delta_ibp`.

* `resFormDeriv G u v : N ↦ -u*𝒢N𝒢v` and `hasLayerDeriv_resForm`: the layer derivative of
  `ω ↦ u*𝒢v` at strictly passive `X`.
* `delta_eq_resForm`: `x*Δy = (K̂ᴴι₁x)*𝒢(K̂ι₁y) - x*Ky` (exact; `K̂ = diag(K, I)`).
* `norm_entry_le_btFun`, `norm_form_le`, `mul_pow_bound`: with `B = btFun`
  (`3‖𝒢‖ + ‖K𝒢₁₁‖ + ‖L‖`), every integrand that
  `delta_ibp` needs for the tests `Ψ = u*𝒢v + κ` and `Ψ = conj(u*𝒢v) + κ` is bounded by
  `M(1+B)³` (constants depend on `X` and the vectors; only finiteness is used).
* `ibp_hyps_bulk hA`: hence, for `W ≥ W₀` (`W₀` uniform on `bulkInterval κ`), all five
  integrability hypotheses of `delta_ibp` hold for both tests (`PassiveBoundsStatement`, via
  `memLp_two_of_poly_bulk`, `integrable_poly_bulk`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `N ↦ -u*𝒢N𝒢v`, the layer derivative of `u*𝒢v`. -/
def resFormDeriv (G : LayerMat W) (u v : LayerSite W .oneBlockOnePort → ℂ) :
    LayerMat W →ₗ[ℂ] ℂ where
  toFun N := -(star u ⬝ᵥ ((G * N * G) *ᵥ v))
  map_add' N N' := by
    simp only [Matrix.mul_add, Matrix.add_mul, add_mulVec, dotProduct_add]; ring
  map_smul' c N := by
    simp [smul_mulVec, dotProduct_smul]

theorem resFormDeriv_apply (G : LayerMat W) (u v : LayerSite W .oneBlockOnePort → ℂ)
    (N : LayerMat W) : resFormDeriv G u v N = -(star u ⬝ᵥ ((G * N * G) *ᵥ v)) := rfl

theorem resFormDeriv_single (G : LayerMat W) (u v : LayerSite W .oneBlockOnePort → ℂ)
    (β γ : LayerSite W .oneBlockOnePort) :
    resFormDeriv G u v (Matrix.single β γ 1) = -((star u ᵥ* G) β * (G *ᵥ v) γ) := by
  rw [resFormDeriv_apply, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec]
  congr 1
  simp [dotProduct, vecMul, mulVec, Matrix.single_apply, ite_and]

theorem hasLayerDeriv_resForm {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) (u v : LayerSite W .oneBlockOnePort → ℂ) :
    HasLayerDeriv (fun ω => star u ⬝ᵥ (gRes b E X ω *ᵥ v))
      (fun ω => resFormDeriv (gRes b E X ω) u v) := by
  intro ω hω Δ _
  have h := hasDerivAt_layerResolvent E (boundaryZ b E) _ ω Δ
    (isUnit_layerMatrix_strict hη hY ω hω)
  have h2 := (formL u v).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  show HasDerivAt (fun s : ℝ => star u ⬝ᵥ (gRes b E X (ω + (s : ℂ) • Δ) *ᵥ v))
    (resFormDeriv (gRes b E X ω) u v (layerLin Δ)) 0
  rw [show resFormDeriv (gRes b E X ω) u v (layerLin Δ) =
    formL u v (-(gRes b E X ω * layerLin Δ * gRes b E X ω)) by
      rw [resFormDeriv_apply]; simp [formL, neg_mulVec]]
  exact h2

theorem blkAt_mul_kHat_zero (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (M : LayerMat W) :
    blkAt (M * kHat b E X) 0 0 = blkAt M 0 0 * (boundaryZ b E • 1 - X) := by
  obtain ⟨k00, -, k10, -⟩ := SourceMixing.blkAt_kHat b E X
  rw [blkAt_mul, Fin.sum_univ_two, k00, k10, Matrix.mul_zero, add_zero]

/-- `x*Δy = (K̂ᴴι₁x)*𝒢(K̂ι₁y) - x*Ky`. -/
theorem delta_eq_resForm (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (x y : Fin W → ℂ) :
    bilinear x (freshDelta b E X ω) y =
      star ((kHat b E X)ᴴ *ᵥ physVec x) ⬝ᵥ (gRes b E X ω *ᵥ (kHat b E X *ᵥ physVec y)) -
        bilinear x (boundaryZ b E • 1 - X) y := by
  rw [← star_dotProduct_mul_mulVec, mulVec_mulVec, form_physVec, blkAt_mul_kHat_zero,
    (SourceMixing.blkAt_kHat_mul_zero b E X _).1, blkAt_gRes_zero, FullSource.freshDelta_eq,
    PassiveCovariance.bilinear_sub]

section Bounds
variable (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)

theorem norm_entry_le_btFun (α β : LayerSite W .oneBlockOnePort) :
    ‖gRes b E X ω α β‖ ≤ 1 + btFun b E X ω := by
  have h1 := FullSource.norm_entry_le_op (gRes b E X ω) α β
  linarith [norm_gRes_le_btFun b E X ω]

theorem norm_gRes_le_one_add (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖gRes b E X ω‖ ≤ 1 + btFun b E X ω := by
  linarith [norm_gRes_le_btFun b E X ω]

theorem norm_form_le (u v : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W) :
    ‖star u ⬝ᵥ (M *ᵥ v)‖ ≤ vecNorm u * vecNorm v * ‖M‖ := by
  have := PassiveCovariance.norm_bilinear_le u M v
  simp only [bilinear] at this
  linarith

/-- Products of bounds in powers of `B' = 1 + B ≥ 1`. -/
theorem mul_pow_bound {f g B M₁ M₂ : ℝ} (hB : 1 ≤ B) (h₁ : 0 ≤ M₁) (h₂ : 0 ≤ M₂) {i j : ℕ}
    (hij : i + j ≤ 3) (hf : 0 ≤ f) (hf' : f ≤ M₁ * B ^ i) (hg : g ≤ M₂ * B ^ j) :
    f * g ≤ M₁ * M₂ * B ^ 3 := by
  have hB0 : 0 ≤ B := by linarith
  have hj : 0 ≤ M₂ * B ^ j := mul_nonneg h₂ (pow_nonneg hB0 j)
  calc f * g ≤ f * (M₂ * B ^ j) := mul_le_mul_of_nonneg_left hg hf
    _ ≤ (M₁ * B ^ i) * (M₂ * B ^ j) := mul_le_mul_of_nonneg_right hf' hj
    _ = M₁ * M₂ * B ^ (i + j) := by ring
    _ ≤ M₁ * M₂ * B ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hij) (mul_nonneg h₁ h₂)

end Bounds

/-- **The integrability hypotheses of `delta_ibp`** for every test `Ψ` with
`|Ψ| ≤ M(1+B)` and `|DΨ(N)| ≤ M'‖N‖(1+B)²`, `W₀` uniform on `bulkInterval κ`. -/
theorem ibp_hyps_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ (a c : LayerSite W .oneBlockOnePort → ℂ) (M M' : ℝ),
      0 ≤ M → 0 ≤ M' →
      ∀ (Ψ : LayerSample W .oneBlockOnePort → ℂ)
        (DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ),
      Measurable Ψ → (∀ N, Measurable fun ω => DΨ ω N) →
      (∀ ω, ‖Ψ ω‖ ≤ M * (1 + btFun b E X ω) ^ 1) →
      (∀ ω N, ‖DΨ ω N‖ ≤ (M' * ‖N‖) * (1 + btFun b E X ω) ^ 2) →
      (∀ α γ, MemLp (fun ω => gRes b E X ω α γ * Ψ ω) 2 (layerLaw W b .oneBlockOnePort)) ∧
      (∀ α γ N, Integrable (fun ω => gRes b E X ω α γ * DΨ ω N) (layerLaw W b .oneBlockOnePort)) ∧
      (∀ α γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) α γ)
        (layerLaw W b .oneBlockOnePort)) ∧
      (∀ α β γ, Integrable (fun ω => Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β))
        (layerLaw W b .oneBlockOnePort)) ∧
      Integrable (fun ω => (star a ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ c)) * Ψ ω)
        (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₁, hm⟩ := LengthUniform.memLp_two_of_poly_bulk hA hb0 hb hκ 3 (by norm_num)
  obtain ⟨W₂, hi⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 3
  refine ⟨max W₁ W₂, fun W hW E hE X hY a c M M' hM hM' Ψ DΨ hΨm hDm hΨ hD => ?_⟩
  have hW₁ := le_of_max_le_left hW
  have hW₂ := le_of_max_le_right hW
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  set B := fun ω => 1 + btFun b E X ω
  have hB : ∀ ω, 1 ≤ B ω := fun ω => one_le_one_add_btFun b E X ω
  have hG1 : ∀ ω α β, ‖gRes b E X ω α β‖ ≤ 1 * B ω ^ 1 := fun ω α β => by
    rw [one_mul, pow_one]; exact norm_entry_le_btFun b E X ω α β
  have hΨ0 : ∀ ω, 0 ≤ ‖Ψ ω‖ := fun _ => norm_nonneg _
  have int3 := fun (F : LayerSample W .oneBlockOnePort → ℂ) (hF : Measurable F) (K : ℝ)
    (hK : ∀ ω, ‖F ω‖ ≤ K * B ω ^ 3) => hi W hW₂ E hE X hY.posSemidef F hF.aestronglyMeasurable K hK
  refine ⟨fun α γ => hm W hW₁ E hE X hY.posSemidef _
      (hGm.eval_matrix.mul hΨm).aestronglyMeasurable (1 * M) fun ω => ?_, fun α γ N => ?_,
    fun α γ N => ?_, fun α β γ => ?_, ?_⟩
  · rw [norm_mul]
    exact mul_pow_bound (hB ω) zero_le_one hM (by norm_num) (norm_nonneg _) (hG1 ω α γ) (hΨ ω)
  · refine int3 _ (hGm.eval_matrix.mul (hDm N)) (1 * (M' * ‖N‖)) fun ω => ?_
    rw [norm_mul]
    exact mul_pow_bound (hB ω) zero_le_one (by positivity) (by norm_num) (norm_nonneg _)
      (hG1 ω α γ) (hD ω N)
  · have hc : Continuous fun G : LayerMat W => (G * N * G) α γ :=
      ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).matrix_elem α γ
    refine int3 _ (hΨm.mul (hc.measurable.comp hGm)) (M * ‖N‖) fun ω => ?_
    rw [norm_mul]
    have h2 : ‖(gRes b E X ω * N * gRes b E X ω) α γ‖ ≤ ‖N‖ * B ω ^ 2 := by
      refine (FullSource.norm_entry_le_op _ α γ).trans ?_
      have hg := norm_gRes_le_one_add b E X ω
      calc ‖gRes b E X ω * N * gRes b E X ω‖ ≤ ‖gRes b E X ω‖ * ‖N‖ * ‖gRes b E X ω‖ :=
            (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
        _ ≤ B ω * ‖N‖ * B ω := by
            have := hB ω
            gcongr
        _ = ‖N‖ * B ω ^ 2 := by ring
    exact mul_pow_bound (hB ω) hM (norm_nonneg _) (by norm_num) (norm_nonneg _) (hΨ ω) h2
  · refine int3 _ (hΨm.mul (hGm.eval_matrix.mul hGm.eval_matrix)) (M * (1 * 1)) fun ω => ?_
    rw [norm_mul]
    have h2 : ‖gRes b E X ω γ γ * gRes b E X ω α β‖ ≤ (1 * 1) * B ω ^ 2 := by
      rw [norm_mul]
      have := mul_pow_bound (i := 1) (j := 1) (hB ω) zero_le_one zero_le_one (by norm_num)
        (norm_nonneg _) (hG1 ω γ γ) (hG1 ω α β)
      have h3 : B ω ^ 2 ≤ B ω ^ 3 := pow_le_pow_right₀ (hB ω) (by norm_num)
      have h4 : ‖gRes b E X ω γ γ‖ * ‖gRes b E X ω α β‖ ≤ B ω ^ 2 := by
        have e1 := hG1 ω γ γ; have e2 := hG1 ω α β
        rw [one_mul, pow_one] at e1 e2
        calc _ ≤ B ω * B ω := mul_le_mul e1 e2 (norm_nonneg _) (by linarith [hB ω])
          _ = B ω ^ 2 := by ring
      linarith
    exact mul_pow_bound (hB ω) hM (by norm_num) (by norm_num) (norm_nonneg _) (hΨ ω) h2
  · have hc : Continuous fun G : LayerMat W => star a ⬝ᵥ ((kHat b E X * G) *ᵥ c) :=
      continuous_const.dotProduct ((continuous_const.matrix_mul continuous_id).matrix_mulVec
        continuous_const)
    refine int3 _ ((hc.measurable.comp hGm).mul hΨm) ((vecNorm a * vecNorm c) * M) fun ω => ?_
    rw [norm_mul]
    have h1 : ‖star a ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ c)‖ ≤ (vecNorm a * vecNorm c) * B ω ^ 2 := by
      refine (norm_form_le a c _).trans ?_
      have hk : ‖kHat b E X * gRes b E X ω‖ ≤ B ω ^ 2 := by
        have := wBound_kHat_le b E X ω
        simp only [wBound] at this
        have : ‖kHat b E X * gRes b E X ω‖ ≤ B ω := by
          simp only [B]; linarith [norm_nonneg (gRes b E X ω)]
        nlinarith [hB ω]
      have := PassiveCovariance.vecNorm_nonneg a; have := PassiveCovariance.vecNorm_nonneg c
      exact mul_le_mul_of_nonneg_left hk (by positivity)
    exact mul_pow_bound (i := 2) (j := 1) (hB ω) (by
      have := PassiveCovariance.vecNorm_nonneg a; have := PassiveCovariance.vecNorm_nonneg c
      positivity) hM (by norm_num) (norm_nonneg _) h1 (hΨ ω)

end BlockBand.SourceProcess.FullSourceCovariance
