module

public import BlockBand.Transmission.PassiveCovariance.MeanField

/-!
# The mean Schwinger–Dyson equation on the port rows

These are the port-row analogues of `meanSD_phys` and `meanField_phys`, from
`replica_identity_port` with `Ψ = 1`. **Hypothesis:** `PassiveBoundsStatement`
(`moments`, `traceMatrix`).

* `meanSD_port`: `E[(V𝒢)_{x̄β}] = -(b/W) E[(Tr𝒢₁₁)𝒢_{x̄β}]`.
* `meanField_port`: for strictly passive `X`,
  `|E[(V𝒢)_{x̄,·}] + bE⟨𝒢₁₁⟩E𝒢_{x̄,·}| ≤ C/W²` on the `𝒢₂₁` and `𝒢₂₂` columns.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem meanSD_port (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ (x : Fin W) (β : LayerSite W .oneBlockOnePort),
        ∫ ω, (layerLin ω * gRes b E X ω) (port x) β ∂layerLaw W b .oneBlockOnePort =
          -((ginVar W b : ℂ) * ∫ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (port x) β
            ∂layerLaw W b .oneBlockOnePort) := by
  obtain ⟨C2, W2, m2⟩ := layer_moments hA hb0 hb h1 h2 (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments hA hb0 hb h1 h2 (2 * (2 : ℕ)) (by norm_num)
  refine ⟨max W2 W4, fun W hW X hX x β => ?_⟩
  have hη := etaZ_pos b E (by linarith) h1 h2
  set μ := layerLaw W b .oneBlockOnePort
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hgm : Measurable fun ω => ‖gRes b E X ω‖ := continuous_norm.measurable.comp hGm
  have hfin : ∀ (c C : ℝ) (k : ℕ), ENNReal.ofReal c * ENNReal.ofReal C ^ k ≠ ∞ := fun c C k =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hL2 : ∀ γ, MemLp (fun ω => gRes b E X ω γ β * 1) 2 μ := fun γ =>
    lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound (hGm.eval_matrix.mul_const _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable zero_le_one 1 le_rfl
      (fun ω => by simpa using norm_entry_le' (gRes b E X ω) γ β)
      (m2 W (le_trans (le_max_left _ _) hW) X hX.posSemidef)) (hfin _ _ _).lt_top
  have hI2 : ∀ γ N, Integrable (fun ω => (1 : ℂ) * (gRes b E X ω * N * gRes b E X ω) γ β) μ :=
    fun γ N => MemLp.integrable one_le_two (lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound
      ((((hGm.mul_const N).mul hGm).eval_matrix).const_mul _).aestronglyMeasurable
      (fun ω => norm_nonneg _) hgm.aestronglyMeasurable (norm_nonneg N) 2 (by norm_num)
      (fun ω => by
        rw [one_mul]
        exact (norm_entry_le' _ γ β).trans (norm_mul_mul_le _ _))
      (m4 W (le_trans (le_max_right _ _) hW) X hX.posSemidef)) (hfin _ _ _).lt_top)
  have hR := replica_identity_port b E X (Ψ := fun _ => 1) (DΨ := fun _ => 0) hη hX
    (hasLayerDeriv_const 1) measurable_const x β hL2 (fun _ _ => by simp) hI2
  simp only [mul_one, LinearMap.zero_apply, mul_zero, zero_sub, one_mul] at hR
  have hint : ∀ γ δ, Integrable (fun ω => gRes b E X ω γ δ * gRes b E X ω (port x) β) μ := by
    intro γ δ
    have := hI2 γ (Matrix.single δ (port x) 1)
    simpa only [one_mul, mul_single_mul_apply] using this
  rw [hR]
  simp only [integral_neg, mul_neg, Finset.sum_neg_distrib]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun y _ => hint _ _)]
  simp only [Finset.sum_mul]

/-- **The mean Schwinger–Dyson equation with its `W⁻²` error, port rows**: for strictly passive
`X` and the entries `m ∈ {2, 3}` (`𝒢₂₁`, `𝒢₂₂`), `|E[(V𝒢)_{x̄,·}] + bE⟨𝒢₁₁⟩E𝒢_{x̄,·}| ≤ C/W²`. -/
theorem meanField_port (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
      ∀ (m : Fin 6) (x y : Fin W), (m = 2 ∨ m = 3) →
        let μ := layerLaw W b .oneBlockOnePort
        let G := fun ω => passiveLetter E (boundaryZ b E) X ω m x y
        let β : LayerSite W .oneBlockOnePort := if m = 2 then phys y else port y
        ‖(∫ ω, (layerLin ω * gRes b E X ω) (port x) β ∂μ) +
            (b : ℂ) * (∫ ω, (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace ∂μ) *
              (∫ ω, G ω ∂μ)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨W₁, hSD⟩ := meanSD_port hA hb0 hb h1 h2
  obtain ⟨C, W₂, hcov⟩ := letter_traceCov hA hb0 hb h1 h2
  refine ⟨C, max (max W₁ W₂) 1, fun W hW X hX m x y hm => ?_⟩
  intro μ G β
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWpos : (W : ℂ) ≠ 0 := by
    have : 1 ≤ W := le_trans (le_max_right _ _) hW
    exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  have hGβ : ∀ ω, gRes b E X ω (port x) β = G ω := fun ω => by
    rcases hm with rfl | rfl <;> rfl
  obtain ⟨-, -, -, c0⟩ := hcov W hW2 X hX.posSemidef 0 m x y
  rw [hSD W hW1 X hX x β]
  simp only [hGβ]
  have e0 : ∀ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * G ω =
      (W : ℂ) * ((W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace * G ω) := fun ω => by
    rw [trace_letter0]; field_simp
  simp only [e0, integral_const_mul, ginVar_cast hb0]
  simp only [integral_const_mul] at c0
  set A0 := ∫ ω, (W : ℂ)⁻¹ * (passiveLetter E (boundaryZ b E) X ω 0).trace * G ω ∂μ
  set F0 := (W : ℂ)⁻¹ * ∫ ω, (passiveLetter E (boundaryZ b E) X ω 0).trace ∂μ
  set g := ∫ ω, G ω ∂μ
  have key : -((b : ℂ) / W * ((W : ℂ) * A0)) + (b : ℂ) * F0 * g = -((b : ℂ) * (A0 - F0 * g)) := by
    field_simp; ring
  rw [key, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hC : 0 ≤ C / (W : ℝ) ^ 2 := le_trans (norm_nonneg _) c0
  calc b * ‖A0 - F0 * g‖ ≤ b * (C / (W : ℝ) ^ 2) := mul_le_mul_of_nonneg_left c0 hb0.le
    _ ≤ C / (W : ℝ) ^ 2 := by nlinarith

end BlockBand.Transmission.PassiveCovariance
