module

public import BlockBand.SourceProcess.FullSourceCovariance.DeltaForm

/-!
# The integrability hypotheses of `delta_ibp` for quadratic tests

`ibp_hyps_bulk` with the exponents
`(1, 2)` replaced by `(2, 3)`: tests with `‖Ψ‖ ≤ M(1+B)²` and `‖DΨ(N)‖ ≤ M'‖N‖(1+B)³`,
`B = btFun` (for instance a two-resolvent form). `W₀` uniform on `bulkInterval κ`.

* `mul_pow_bound4`: products of bounds in powers of `B ≥ 1`, total degree `≤ 4`;
* **`ibp_hyps23_bulk hA`**.
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

theorem mul_pow_bound4 {f g B M₁ M₂ : ℝ} (hB : 1 ≤ B) (h₁ : 0 ≤ M₁) (h₂ : 0 ≤ M₂) {i j : ℕ}
    (hij : i + j ≤ 4) (hf : 0 ≤ f) (hf' : f ≤ M₁ * B ^ i) (hg : g ≤ M₂ * B ^ j) :
    f * g ≤ M₁ * M₂ * B ^ 4 := by
  have hB0 : 0 ≤ B := by linarith
  have hj : 0 ≤ M₂ * B ^ j := mul_nonneg h₂ (pow_nonneg hB0 j)
  calc f * g ≤ f * (M₂ * B ^ j) := mul_le_mul_of_nonneg_left hg hf
    _ ≤ (M₁ * B ^ i) * (M₂ * B ^ j) := mul_le_mul_of_nonneg_right hf' hj
    _ = M₁ * M₂ * B ^ (i + j) := by ring
    _ ≤ M₁ * M₂ * B ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hij) (mul_nonneg h₁ h₂)

/-- **The integrability hypotheses of `delta_ibp`** for tests with `|Ψ| ≤ M(1+B)²` and
`|DΨ(N)| ≤ M'‖N‖(1+B)³`. -/
theorem ibp_hyps23_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ (a c : LayerSite W .oneBlockOnePort → ℂ) (M M' : ℝ),
      0 ≤ M → 0 ≤ M' →
      ∀ (Ψ : LayerSample W .oneBlockOnePort → ℂ)
        (DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ),
      Measurable Ψ → (∀ N, Measurable fun ω => DΨ ω N) →
      (∀ ω, ‖Ψ ω‖ ≤ M * (1 + btFun b E X ω) ^ 2) →
      (∀ ω N, ‖DΨ ω N‖ ≤ (M' * ‖N‖) * (1 + btFun b E X ω) ^ 3) →
      (∀ α γ, MemLp (fun ω => gRes b E X ω α γ * Ψ ω) 2 (layerLaw W b .oneBlockOnePort)) ∧
      (∀ α γ N, Integrable (fun ω => gRes b E X ω α γ * DΨ ω N) (layerLaw W b .oneBlockOnePort)) ∧
      (∀ α γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) α γ)
        (layerLaw W b .oneBlockOnePort)) ∧
      (∀ α β γ, Integrable (fun ω => Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β))
        (layerLaw W b .oneBlockOnePort)) ∧
      Integrable (fun ω => (star a ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ c)) * Ψ ω)
        (layerLaw W b .oneBlockOnePort) := by
  obtain ⟨W₁, hm⟩ := LengthUniform.memLp_two_of_poly_bulk hA hb0 hb hκ 3 (by norm_num)
  obtain ⟨W₂, hi⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 4
  refine ⟨max W₁ W₂, fun W hW E hE X hY a c M M' hM hM' Ψ DΨ hΨm hDm hΨ hD => ?_⟩
  have hW₁ := le_of_max_le_left hW
  have hW₂ := le_of_max_le_right hW
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  set B := fun ω => 1 + btFun b E X ω
  have hB : ∀ ω, 1 ≤ B ω := fun ω => one_le_one_add_btFun b E X ω
  have hG1 : ∀ ω α β, ‖gRes b E X ω α β‖ ≤ 1 * B ω ^ 1 := fun ω α β => by
    rw [one_mul, pow_one]; exact norm_entry_le_btFun b E X ω α β
  have int4 := fun (F : LayerSample W .oneBlockOnePort → ℂ) (hF : Measurable F) (K : ℝ)
    (hK : ∀ ω, ‖F ω‖ ≤ K * B ω ^ 4) => hi W hW₂ E hE X hY.posSemidef F hF.aestronglyMeasurable K hK
  refine ⟨fun α γ => hm W hW₁ E hE X hY.posSemidef _
      (hGm.eval_matrix.mul hΨm).aestronglyMeasurable (1 * M) fun ω => ?_, fun α γ N => ?_,
    fun α γ N => ?_, fun α β γ => ?_, ?_⟩
  · rw [norm_mul]
    exact mul_pow_bound (hB ω) zero_le_one hM (by norm_num) (norm_nonneg _) (hG1 ω α γ) (hΨ ω)
  · refine int4 _ (hGm.eval_matrix.mul (hDm N)) (1 * (M' * ‖N‖)) fun ω => ?_
    rw [norm_mul]
    exact mul_pow_bound4 (hB ω) zero_le_one (by positivity) (by norm_num) (norm_nonneg _)
      (hG1 ω α γ) (hD ω N)
  · have hc : Continuous fun G : LayerMat W => (G * N * G) α γ :=
      ((continuous_id.matrix_mul continuous_const).matrix_mul continuous_id).matrix_elem α γ
    refine int4 _ (hΨm.mul (hc.measurable.comp hGm)) (M * ‖N‖) fun ω => ?_
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
    exact mul_pow_bound4 (hB ω) hM (norm_nonneg _) (by norm_num) (norm_nonneg _) (hΨ ω) h2
  · refine int4 _ (hΨm.mul (hGm.eval_matrix.mul hGm.eval_matrix)) (M * (1 * 1)) fun ω => ?_
    rw [norm_mul]
    have h2 : ‖gRes b E X ω γ γ * gRes b E X ω α β‖ ≤ (1 * 1) * B ω ^ 2 := by
      rw [norm_mul]
      have e1 := hG1 ω γ γ; have e2 := hG1 ω α β
      rw [one_mul, pow_one] at e1 e2
      calc _ ≤ B ω * B ω := mul_le_mul e1 e2 (norm_nonneg _) (by linarith [hB ω])
        _ = (1 * 1) * B ω ^ 2 := by ring
    exact mul_pow_bound4 (hB ω) hM (by norm_num) (by norm_num) (norm_nonneg _) (hΨ ω) h2
  · have hc : Continuous fun G : LayerMat W => star a ⬝ᵥ ((kHat b E X * G) *ᵥ c) :=
      continuous_const.dotProduct ((continuous_const.matrix_mul continuous_id).matrix_mulVec
        continuous_const)
    refine int4 _ ((hc.measurable.comp hGm).mul hΨm) ((vecNorm a * vecNorm c) * M) fun ω => ?_
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
    exact mul_pow_bound4 (i := 2) (j := 2) (hB ω) (by
      have := PassiveCovariance.vecNorm_nonneg a; have := PassiveCovariance.vecNorm_nonneg c
      positivity) hM (by norm_num) (norm_nonneg _) h1 (hΨ ω)

end BlockBand.SourceProcess.FullSourceCovariance
