module

public import BlockBand.SourceProcess.FullSource.DeltaMeanScalar

/-!
# `‖EΔ‖ ≤ C(δ₀ + W⁻²)` for strictly passive `X` on the scalar domain

Hypothesis: `PassiveBoundsStatement`.

**`deltaMean_strict`**. With `v = E⟨𝒢₁₁⟩`, `u = E⟨𝒢₂₂⟩` (`= E W⁻¹Tr R₊`) and
`Ω = (z+E) + cv + bu = c(v - a) + b(u - a)` (since `z + E = -(1-b)a`), `delta_mean_eq` gives
`EΔ = Ω·E[K𝒢₁₁] + c·Cov(⟨𝒢₁₁⟩, K𝒢₁₁) + b·Cov(⟨𝒢₂₂⟩, K𝒢₁₁)`, that is `EΔ = ΩKM + O(W⁻²)`.
The covariances are bounded by `traceMatrix` for one-letter words (`wordCov_u`, `≤ C/W²`, with
the letter `K𝒢₁₁` itself), `‖E[K𝒢₁₁]‖ ≤ C` by `moments`, and `|Ω| ≤ C(δ₀ + W⁻²)` is
`meanScalars_close`. Uniform in `W ≥ W₀`, `E ∈ bulkInterval κ`, `(passiveY X).PosDef`,
`δ₀(X) ≤ d₁`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem boundaryZ_add_E {b E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    boundaryZ b E + E = -((1 - b : ℝ) : ℂ) * matchedA E := by
  rw [boundaryZ, matchedA_inv E h1 h2]
  apply Complex.ext <;> simp [matchedA] <;> ring

theorem integral_portTr_eq {b E : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∫ ω, portTr b E X ω ∂freshLaw W b = ∫ ω, freshPortTrace b E X ω ∂freshLaw W b := by
  refine integral_congr_ae ?_
  filter_upwards [ae_isUnit_layerF hb hW E X] with ω hF
  rw [freshPortTrace_eq_layer b E X ω hF, portTr, trace_letter3]; rfl

/-- **`‖EΔ‖ ≤ C(δ₀ + W⁻²)`**, strictly passive `X`, scalar domain. -/
theorem deltaMean_strict (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (d₁ C : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hsc⟩ := meanScalars_close hA hb0 hb hκ
  obtain ⟨C2, W2, m2⟩ := layer_moments_u hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_u hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  obtain ⟨Cc, Wc, hcov⟩ := wordCov_u hA hb0 hb hκ 1 le_rfl
  obtain ⟨CK, WK, hK⟩ := hA.moments b hb0 hb κ hκ 1 le_rfl
  set CK' := max CK 0
  set Cc' := max Cc 0
  refine ⟨d₁, CK' * Cs + Cc', max (max (max Ws W2) (max W4 Wc)) (max WK 1), hd₁,
    by positivity, fun W hW E hE X hX hδ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWs, hW2⟩, hW4, hWc⟩, hWK, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hW0 : 0 < W := by omega
  set z := boundaryZ b E
  set μ := freshLaw W b
  have hz : z ∈ paramDisk b E := boundaryZ_mem_paramDisk (by linarith) h1 h2
  have hone : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  have hl4 : ∀ ω, (1 : Matrix (Fin W) (Fin W) ℂ) * passiveLetter E z X ω 4 = kG11 E z X ω :=
    fun ω => by rw [Matrix.one_mul]; rfl
  obtain ⟨-, hU0, hP0, -⟩ := hcov W hWc E hE X hX.posSemidef 0 0 1 hone
  obtain ⟨-, -, hQ0, -⟩ := hcov W hWc E hE X hX.posSemidef 3 0 1 hone
  obtain ⟨-, hU4, -, hc1⟩ := hcov W hWc E hE X hX.posSemidef 0 4 1 hone
  obtain ⟨-, -, -, hc2⟩ := hcov W hWc E hE X hX.posSemidef 3 4 1 hone
  simp only [Matrix.one_mul] at hU0 hP0 hQ0
  simp only [Matrix.one_mul] at hU4 hc1 hc2
  have hEq := delta_mean_eq hb0 hb h1 h2 hX (m2 W hW2 E hE X hX.posSemidef)
    (m4 W hW4 E hE X hX.posSemidef) hU0 hP0 hQ0 hW0
  -- `‖E[K𝒢₁₁]‖ ≤ CK'`
  have hKm := (letter_momBd (b := b) (hK W hWK E hE z hz X hX.posSemidef).2).2.1
  have hKm' : MomBd μ (fun ω => ‖kG11 E z X ω‖) ((1 : ℕ) : ℝ) CK' := by simpa using hKm
  obtain ⟨hKi, hKle⟩ := integral_abs_pow_le (ν := μ) (n := 1) le_rfl (le_max_right _ _) hKm'
  simp only [pow_one, abs_norm] at hKi hKle
  have hEK : ‖matrixExpect μ (fun ω => kG11 E z X ω)‖ ≤ CK' :=
    (norm_matrixExpect_le _ hU4 hKi).trans hKle
  -- the decomposition
  set v := ∫ ω, physTr b E X ω ∂μ
  set u := ∫ ω, freshPortTrace b E X ω ∂μ
  have hu' : ∫ ω, portTr b E X ω ∂μ = u := integral_portTr_eq hb hW1 X
  rw [hu'] at hc2
  obtain ⟨hv, hu⟩ := hsc W hWs E hE X hX hδ
  set EK := matrixExpect μ (fun ω => kG11 E z X ω)
  set R1 := matrixExpect μ (fun ω => physTr b E X ω • kG11 E z X ω) - v • EK
  set R2 := matrixExpect μ (fun ω => portTr b E X ω • kG11 E z X ω) - u • EK
  set c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
  have hdec : matrixExpect μ (freshDelta b E X) =
      ((z + E) + c * v + (b : ℂ) * u) • EK + c • R1 + (b : ℂ) • R2 := by
    rw [hEq]; simp only [R1, R2, smul_sub, smul_smul, add_smul]; abel
  have hΩ : (z + E) + c * v + (b : ℂ) * u =
      c * (v - matchedA E) + (b : ℂ) * (u - matchedA E) := by
    rw [boundaryZ_add_E h1 h2]; simp only [c]; push_cast; ring
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hnc : ‖c‖ = 1 - 2 * b := by simp only [c, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hnb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  set δw := jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2
  have hδw : 0 ≤ δw := add_nonneg (norm_nonneg _) (by positivity)
  have hW2' : ((W : ℝ)⁻¹) ^ 2 ≤ δw := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    simp only [δw]; linarith
  have hR : ∀ R : Matrix (Fin W) (Fin W) ℂ, ‖R‖ ≤ Cc / (W : ℝ) ^ 2 → ‖R‖ ≤ Cc' * δw := by
    intro R hR'
    refine hR'.trans ?_
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_le_mul (le_max_left _ _) hW2' (by positivity) (le_max_right _ _)
  have hR1 := hR R1 hc1
  have hR2 := hR R2 hc2
  have hΩn : ‖(z + E) + c * v + (b : ℂ) * u‖ ≤ Cs * δw := by
    rw [hΩ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hnc, hnb]
    have : (1 - 2 * b) * ‖v - matchedA E‖ + b * ‖u - matchedA E‖ ≤
        (1 - 2 * b) * (Cs * δw) + b * (Cs * δw) :=
      add_le_add (mul_le_mul_of_nonneg_left hv hc0) (mul_le_mul_of_nonneg_left hu hb0.le)
    have h3 : 0 ≤ Cs * δw := mul_nonneg hCs hδw
    have h4 : 0 ≤ b * (Cs * δw) := mul_nonneg hb0.le h3
    linarith
  rw [hdec]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_smul, norm_smul, norm_smul, hnc, hnb]
  have e1 : ‖(z + E) + c * v + (b : ℂ) * u‖ * ‖EK‖ ≤ Cs * δw * CK' :=
    mul_le_mul hΩn hEK (norm_nonneg _) (mul_nonneg hCs hδw)
  have e2 : (1 - 2 * b) * ‖R1‖ ≤ (1 - 2 * b) * (Cc' * δw) := mul_le_mul_of_nonneg_left hR1 hc0
  have e3 : b * ‖R2‖ ≤ b * (Cc' * δw) := mul_le_mul_of_nonneg_left hR2 hb0.le
  have e4 : 0 ≤ Cc' * δw := mul_nonneg (le_max_right _ _) hδw
  have e5 : (CK' * Cs + Cc') * δw = Cs * δw * CK' + Cc' * δw := by ring
  have e6 : 0 ≤ b * (Cc' * δw) := mul_nonneg hb0.le e4
  rw [e5]
  linarith

end BlockBand.SourceProcess.FullSource
