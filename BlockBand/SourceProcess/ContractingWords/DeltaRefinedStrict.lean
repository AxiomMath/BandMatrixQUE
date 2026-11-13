module

public import BlockBand.SourceProcess.FullSource.DeltaMeanStrict
public import BlockBand.SourceProcess.TagBirth.FreshTrace

/-!
# The refined mean `E_jΔ = Ω·I + O(δ₀² + W⁻²)`, strictly passive input

**`deltaMean_strict_refined`**: on the scalar domain `δ₀ ≤ d₁`, for strictly passive `X`,
`‖EΔ - Ω₀·I‖ ≤ C(δ₀² + W⁻²)` with `|Ω₀| ≤ C(δ₀ + W⁻²)`; uniform in `W ≥ W₀`, `E ∈ bulkInterval κ`.
Operator norm, `freshLaw W b`. Hypothesis: `PassiveBoundsStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `E[K𝒢₁₁] = EΔ·R + I`, from `Δ = K𝒢₁₁K - K` and `KR = I`. -/
theorem expect_kG11_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hU : ∀ x y, Integrable (fun ω => kG11 E (boundaryZ b E) X ω x y) (freshLaw W b)) :
    matrixExpect (freshLaw W b) (fun ω => kG11 E (boundaryZ b E) X ω) =
      matrixExpect (freshLaw W b) (freshDelta b E X) * passiveResolvent b E X + 1 := by
  set K : Matrix (Fin W) (Fin W) ℂ := boundaryZ b E • 1 - X
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hKu : IsUnit K.det :=
    (Matrix.isUnit_iff_isUnit_det K).mp (BlockBand.SourceProcess.TagBirth.isUnit_pencil hη hY)
  have hKR : K * passiveResolvent b E X = 1 := Matrix.mul_nonsing_inv K hKu
  have hΔ : freshDelta b E X = fun ω => 1 * kG11 E (boundaryZ b E) X ω * K - K := by
    funext ω; rw [freshDelta_eq, kG11, Matrix.one_mul]
  have hE : matrixExpect (freshLaw W b) (freshDelta b E X) =
      matrixExpect (freshLaw W b) (fun ω => kG11 E (boundaryZ b E) X ω) * K - K := by
    rw [hΔ, matrixExpect_sandwich 1 K K _ hU, Matrix.one_mul]
  rw [hE, Matrix.sub_mul, Matrix.mul_assoc, hKR, Matrix.mul_one]
  abel

theorem arith_refined {Cs C0 ηi Cc δ w : ℝ} (hCs : 0 ≤ Cs) (hC0 : 0 ≤ C0) (hη : 0 ≤ ηi)
    (hCc : 0 ≤ Cc) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    Cs * (δ + w) * (C0 * (δ + w) * ηi) + Cc * w ≤ (4 * Cs * C0 * ηi + Cc + 1) * (δ ^ 2 + w) := by
  have hK : 0 ≤ Cs * C0 * ηi := by positivity
  have h1 : (δ + w) ^ 2 ≤ 2 * (δ ^ 2 + w) := by nlinarith [sq_nonneg (δ - w)]
  have e : Cs * (δ + w) * (C0 * (δ + w) * ηi) = Cs * C0 * ηi * (δ + w) ^ 2 := by ring
  rw [e]
  have h2 := mul_le_mul_of_nonneg_left h1 hK
  have h3 : 0 ≤ δ ^ 2 + w := by positivity
  nlinarith [mul_nonneg hK h3, mul_nonneg hCc h3]

/-- **The refined mean of `Δ`**, strictly passive `X` on the scalar domain. -/
theorem deltaMean_strict_refined (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₁ C : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
        ∃ Ω : ℂ, ‖matrixExpect (freshLaw W b) (freshDelta b E X) - Ω • 1‖ ≤
          C * (jetDistance0 b E X ^ 2 + ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hsc⟩ := meanScalars_close hA hb0 hb hκ
  obtain ⟨d₂, C0, W0', hd₂, hC0, hmean⟩ := deltaMean_strict hA hb0 hb hκ
  obtain ⟨C2, W2, m2⟩ := layer_moments_u hA hb0 hb hκ (2 * (1 : ℕ)) (by norm_num)
  obtain ⟨C4, W4, m4⟩ := layer_moments_u hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  obtain ⟨Cc, Wc, hcov⟩ := wordCov_u hA hb0 hb hκ 1 le_rfl
  set Cc' := max Cc 0
  set ηi := ((1 - b) * κ / 4)⁻¹
  have hη₀ : 0 < (1 - b) * κ / 4 := by have : 0 < 1 - b := by linarith
                                       positivity
  refine ⟨min d₁ d₂, 4 * Cs * C0 * ηi + Cc' + 1, max (max (max Ws W2) (max W4 Wc)) (max W0' 1),
    lt_min hd₁ hd₂, by positivity, fun W hW E hE X hX hδ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWs, hW2⟩, hW4, hWc⟩, hW0', hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hW0 : 0 < W := by omega
  set z := boundaryZ b E
  set μ := freshLaw W b
  have hone : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  obtain ⟨-, hU0, hP0, -⟩ := hcov W hWc E hE X hX.posSemidef 0 0 1 hone
  obtain ⟨-, -, hQ0, -⟩ := hcov W hWc E hE X hX.posSemidef 3 0 1 hone
  obtain ⟨-, hU4, -, hc1⟩ := hcov W hWc E hE X hX.posSemidef 0 4 1 hone
  obtain ⟨-, -, -, hc2⟩ := hcov W hWc E hE X hX.posSemidef 3 4 1 hone
  simp only [Matrix.one_mul] at hU0 hP0 hQ0
  simp only [Matrix.one_mul] at hU4 hc1 hc2
  have hEq := delta_mean_eq hb0 hb h1 h2 hX (m2 W hW2 E hE X hX.posSemidef)
    (m4 W hW4 E hE X hX.posSemidef) hU0 hP0 hQ0 hW0
  set v := ∫ ω, physTr b E X ω ∂μ
  set u := ∫ ω, freshPortTrace b E X ω ∂μ
  have hu' : ∫ ω, portTr b E X ω ∂μ = u := integral_portTr_eq hb hW1 X
  rw [hu'] at hc2
  obtain ⟨hv, hu⟩ := hsc W hWs E hE X hX (hδ.trans (min_le_left _ _))
  set EK := matrixExpect μ (fun ω => kG11 E z X ω)
  set R1 := matrixExpect μ (fun ω => physTr b E X ω • kG11 E z X ω) - v • EK
  set R2 := matrixExpect μ (fun ω => portTr b E X ω • kG11 E z X ω) - u • EK
  set c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
  set Ω₀ : ℂ := (z + E) + c * v + (b : ℂ) * u
  have hdec : matrixExpect μ (freshDelta b E X) = Ω₀ • EK + c • R1 + (b : ℂ) • R2 := by
    rw [hEq]; simp only [Ω₀, R1, R2, smul_sub, smul_smul, add_smul]; abel
  have hU4' : ∀ x y, Integrable (fun ω => kG11 E z X ω x y) μ := fun x y => hU4 x y
  have hEK : EK = matrixExpect μ (freshDelta b E X) * passiveResolvent b E X + 1 :=
    expect_kG11_eq hb0 hb h1 h2 hX.posSemidef hU4'
  have hΩ : Ω₀ = c * (v - matchedA E) + (b : ℂ) * (u - matchedA E) := by
    simp only [Ω₀]; rw [boundaryZ_add_E h1 h2]; simp only [c]; push_cast; ring
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hnc : ‖c‖ = 1 - 2 * b := by simp only [c, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hnb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  set δ := jetDistance0 b E X
  have hδ0 : 0 ≤ δ := norm_nonneg _
  set δw := δ + ((W : ℝ)⁻¹) ^ 2
  have hδw : 0 ≤ δw := add_nonneg hδ0 (by positivity)
  have hΩn : ‖Ω₀‖ ≤ Cs * δw := by
    rw [hΩ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hnc, hnb]
    have : (1 - 2 * b) * ‖v - matchedA E‖ + b * ‖u - matchedA E‖ ≤
        (1 - 2 * b) * (Cs * δw) + b * (Cs * δw) :=
      add_le_add (mul_le_mul_of_nonneg_left hv hc0) (mul_le_mul_of_nonneg_left hu hb0.le)
    have h3 : 0 ≤ Cs * δw := mul_nonneg hCs hδw
    have h4 : 0 ≤ b * (Cs * δw) := mul_nonneg hb0.le h3
    linarith
  have hEΔ : ‖matrixExpect μ (freshDelta b E X)‖ ≤ C0 * δw :=
    hmean W hW0' E hE X hX (hδ.trans (min_le_right _ _))
  have hR : ‖passiveResolvent b E X‖ ≤ ηi :=
    (norm_passiveResolvent_le hb0 hb h1 h2 hX.posSemidef).trans
      (inv_anti₀ hη₀ (etaZ_ge hb0 hb hκ hE))
  refine ⟨Ω₀, ?_⟩
  have hsplit : matrixExpect μ (freshDelta b E X) - Ω₀ • 1 =
      Ω₀ • (matrixExpect μ (freshDelta b E X) * passiveResolvent b E X) + c • R1 +
        (b : ℂ) • R2 := by
    nth_rewrite 1 [hdec]; rw [hEK]; simp only [smul_add]; abel
  have hcW : Cc / (W : ℝ) ^ 2 = Cc * ((W : ℝ)⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
  have hR1 : ‖R1‖ ≤ Cc' * ((W : ℝ)⁻¹) ^ 2 :=
    hc1.trans (by rw [hcW]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hR2 : ‖R2‖ ≤ Cc' * ((W : ℝ)⁻¹) ^ 2 :=
    hc2.trans (by rw [hcW]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_smul, norm_smul, norm_smul, hnc, hnb]
  have e1 : ‖Ω₀‖ * ‖matrixExpect μ (freshDelta b E X) * passiveResolvent b E X‖ ≤
      Cs * δw * (C0 * δw * ηi) :=
    mul_le_mul hΩn ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hEΔ hR (norm_nonneg _)
      (mul_nonneg hC0 hδw))) (norm_nonneg _) (mul_nonneg hCs hδw)
  have hw2 : ((W : ℝ)⁻¹) ^ 2 ≤ 1 := by
    have h0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW1)
    exact pow_le_one₀ h0 this
  have e2 : (1 - 2 * b) * ‖R1‖ + b * ‖R2‖ ≤ Cc' * ((W : ℝ)⁻¹) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hR1 hc0
    have := mul_le_mul_of_nonneg_left hR2 hb0.le
    have : (1 - 2 * b) * (Cc' * ((W : ℝ)⁻¹) ^ 2) + b * (Cc' * ((W : ℝ)⁻¹) ^ 2) ≤
        Cc' * ((W : ℝ)⁻¹) ^ 2 := by
      have h5 : 0 ≤ b * (Cc' * ((W : ℝ)⁻¹) ^ 2) := by positivity
      linarith
    linarith
  have hfin := arith_refined (δ := δ) hCs hC0 (show 0 ≤ ηi by positivity) (le_max_right Cc 0)
    (show 0 ≤ ((W : ℝ)⁻¹) ^ 2 by positivity) hw2
  linarith

end BlockBand.SourceProcess.ContractingWords
