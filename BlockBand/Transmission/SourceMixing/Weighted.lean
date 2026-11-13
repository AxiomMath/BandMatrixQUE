module

public import BlockBand.Transmission.SourceMixing.MeanExpansion

/-!
# The weighted dressed inverse `K̂D⁻¹` and the weighted mean-field expansion

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
deterministic `X`, operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E`
(and `L_w, K_d`) only.

* `kHat_sub_dressed_blk`: `K̂ - D` is block diagonal with scalar blocks `(z - ζ)I` and
  `(1 - z + bm₁)I` (`D = H₀ - S̄` the dressed matrix, `K̂ = diag(z - X, I)`). The unbounded `X`
  cancels.
* `norm_kHat_dressedInv`: hence `‖K̂D⁻¹‖ = ‖1 + (K̂ - D)D⁻¹‖ ≤ C_K` uniformly, and
  `‖K̂E𝒢 - K̂D⁻¹‖ ≤ C/W²`.
* `weightedExpansion`: for every dressed word `w`,
  `‖K̂·E[𝒢w] - K̂D⁻¹(E[w] + Σ_j 𝒮[E(𝒢α_j)]E[γ_j])‖ ≤ C/W²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

set_option linter.unnecessarySeqFocus false in
theorem blkAt_kHat (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    blkAt (kHat b E X) 0 0 = boundaryZ b E • 1 - X ∧ blkAt (kHat b E X) 0 1 = 0 ∧
      blkAt (kHat b E X) 1 0 = 0 ∧ blkAt (kHat b E X) 1 1 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x y <;>
    simp [blkAt, siteOf, kHat, liftX, Matrix.one_apply, fromBlocks]

/-- `K̂ - D` has scalar diagonal blocks and no off-diagonal blocks. -/
theorem kHat_sub_dressed_blk (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    blkAt (kHat b E X - dressed b E X) 0 0 =
        (boundaryZ b E - zetaOf b E (meanTr b E X 0) (meanTr b E X 3)) • 1 ∧
      blkAt (kHat b E X - dressed b E X) 0 1 = 0 ∧ blkAt (kHat b E X - dressed b E X) 1 0 = 0 ∧
      blkAt (kHat b E X - dressed b E X) 1 1 = (1 - (boundaryZ b E - (b : ℂ) * meanTr b E X 0)) • 1 := by
  obtain ⟨k00, k01, k10, k11⟩ := blkAt_kHat b E X
  obtain ⟨d00, d01, d10, d11⟩ := blkAt_dressed b E X
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [blkAt_sub]
  · rw [k00, d00, sub_smul]; abel
  · rw [k01, d01, sub_zero]
  · rw [k10, d10, sub_zero]
  · rw [k11, d11, sub_smul 1, one_smul]

theorem norm_blkTr_le (M : LayerMat W) (r : Fin 2) : ‖blkTr M r‖ ≤ ‖M‖ :=
  (PassiveCovariance.norm_normTrace_le _).trans (norm_blkAt_le _ _ _)

theorem integral_blkTr {μ : Measure (LayerSample W .oneBlockOnePort)}
    (G : LayerSample W .oneBlockOnePort → LayerMat W) (hG : ∀ α β, Integrable (fun ω => G ω α β) μ)
    (r : Fin 2) : ∫ ω, blkTr (G ω) r ∂μ = blkTr (matrixExpect μ G) r := by
  simp only [blkTr, Matrix.trace, blkAt, Matrix.diag, Matrix.of_apply, matrixExpect]
  rw [integral_const_mul, integral_finsetSum _ fun y _ => hG _ _]

/-- The weighted dressed inverse is bounded, and `E[K̂𝒢] = K̂D⁻¹ + O(W⁻²)`. -/
theorem norm_kHat_dressedInv (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (CK : ℝ) (W₀ : ℕ), 0 ≤ CK ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        IsUnit (dressed b E X) ∧ ‖(dressed b E X)⁻¹‖ ≤ CK ∧
        ‖kHat b E X * (dressed b E X)⁻¹‖ ≤ CK ∧
        ‖kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) -
          kHat b E X * (dressed b E X)⁻¹‖ ≤ CK / (W : ℝ) ^ 2 := by
  obtain ⟨CD, WD, hDI⟩ := dressed_inverse hA hb0 hb h1 h2
  obtain ⟨Cm, Wm, hCm, hmf⟩ := meanField_op hA hb0 hb h1 h2
  obtain ⟨_, Wt, _, hcov⟩ := traceCov_op hA hb0 hb h1 h2
  set CD' := max CD 0
  set Cz := ‖boundaryZ b E‖ + |E| + 2 * CD' + 2 * CD' + 1 + ‖boundaryZ b E‖ + 2 * CD' with hCz
  set CK0 := 1 + 2 * Cz * CD'
  refine ⟨max (max CK0 CD') (CK0 * Cm), max (max WD Wm) (max Wt 1), by positivity,
    fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWD, hWm⟩, hWt, hW1⟩ := hW
  obtain ⟨hU, hDn, hE⟩ := hDI W hWD X hX
  have hDn' : ‖(dressed b E X)⁻¹‖ ≤ CD' := hDn.trans (le_max_left _ _)
  set μ := layerLaw W b .oneBlockOnePort
  set D := dressed b E X
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hWr
  -- `‖E𝒢‖ ≤ 2CD'`
  have hEG : ‖matrixExpect μ (gRes b E X)‖ ≤ 2 * CD' := by
    have h' : ‖matrixExpect μ (gRes b E X) - D⁻¹‖ ≤ CD' := hE.trans (by
      calc CD / (W : ℝ) ^ 2 ≤ CD' / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ CD' := div_le_self (le_max_right _ _) hW2)
    have h := norm_add_le (matrixExpect μ (gRes b E X) - D⁻¹) D⁻¹
    rw [sub_add_cancel] at h
    linarith
  have hGint : ∀ α β, Integrable (fun ω => gRes b E X ω α β) μ :=
    (hcov W hWt X hX.posSemidef 0).2.1
  have hm : ∀ k : Fin 2, ‖meanTr b E X (![0, 3] k)‖ ≤ 2 * CD' := fun k => by
    have e : meanTr b E X (![0, 3] k) = blkTr (matrixExpect μ (gRes b E X)) k := by
      rw [← integral_blkTr _ hGint]
      fin_cases k
      · exact integral_congr_ae (Eventually.of_forall fun ω => trLetter_zero_eq b E X ω)
      · exact integral_congr_ae (Eventually.of_forall fun ω => trLetter_three_eq b E X ω)
    rw [e]; exact (norm_blkTr_le _ _).trans hEG
  have hm0 : ‖meanTr b E X 0‖ ≤ 2 * CD' := hm 0
  have hm3 : ‖meanTr b E X 3‖ ≤ 2 * CD' := hm 1
  -- `‖K̂ - D‖ ≤ 2Cz`
  obtain ⟨e00, e01, e10, e11⟩ := kHat_sub_dressed_blk b E X
  have hΔ : ‖kHat b E X - D‖ ≤ 2 * Cz := by
    have hz : ‖zetaOf b E (meanTr b E X 0) (meanTr b E X 3)‖ ≤ |E| + 2 * CD' + 2 * CD' := by
      unfold zetaOf
      have h1' : ‖((1 - 2 * b : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
      have h2' : ‖(b : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
      calc ‖-(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * meanTr b E X 0 - (b : ℂ) * meanTr b E X 3‖
          ≤ ‖(E : ℂ)‖ + ‖((1 - 2 * b : ℝ) : ℂ)‖ * ‖meanTr b E X 0‖ + ‖(b : ℂ)‖ * ‖meanTr b E X 3‖ := by
            refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) (norm_mul_le _ _))
            rw [norm_neg]; exact add_le_add le_rfl (norm_mul_le _ _)
        _ ≤ |E| + 1 * (2 * CD') + 1 * (2 * CD') := by
            rw [Complex.norm_real, Real.norm_eq_abs]
            gcongr
        _ = _ := by ring
    have hb' : ‖(b : ℂ) * meanTr b E X 0‖ ≤ 2 * CD' := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      nlinarith [norm_nonneg (meanTr b E X 0)]
    calc _ ≤ _ := norm_layerMat_le' _
      _ ≤ (‖boundaryZ b E‖ + (|E| + 2 * CD' + 2 * CD')) + 0 + 0 + (1 + (‖boundaryZ b E‖ + 2 * CD')) := by
        rw [e00, e01, e10, e11, norm_zero]
        gcongr
        · exact (norm_smul_one_le _).trans ((norm_sub_le _ _).trans (add_le_add le_rfl hz))
        · exact (norm_smul_one_le _).trans ((norm_sub_le _ _).trans (add_le_add (by simp)
            ((norm_sub_le _ _).trans (add_le_add le_rfl hb'))))
      _ ≤ 2 * Cz := by
        have := norm_nonneg (boundaryZ b E); have := abs_nonneg E
        have : 0 ≤ CD' := le_max_right _ _
        rw [hCz]; linarith
  -- `K̂D⁻¹ = 1 + (K̂ - D)D⁻¹`
  have hDD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hKD : kHat b E X * D⁻¹ = 1 + (kHat b E X - D) * D⁻¹ := by
    rw [Matrix.sub_mul, hDD]; abel
  have hKDn : ‖kHat b E X * D⁻¹‖ ≤ CK0 := by
    rw [hKD]
    calc ‖1 + (kHat b E X - D) * D⁻¹‖ ≤ 1 + 2 * Cz * CD' :=
          (norm_add_le _ _).trans (add_le_add norm_one_matrix_le ((Matrix.l2_opNorm_mul _ _).trans
            (mul_le_mul hΔ hDn' (norm_nonneg _) (by positivity))))
      _ = CK0 := rfl
  refine ⟨hU, hDn'.trans ((le_max_right _ _).trans (le_max_left _ _)),
    hKDn.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  have hDinvD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have e : kHat b E X * matrixExpect μ (gRes b E X) - kHat b E X * D⁻¹ =
      (kHat b E X * D⁻¹) * (D * matrixExpect μ (gRes b E X) - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.mul_assoc D⁻¹, hDinvD,
      Matrix.one_mul]
  rw [e]
  calc _ ≤ ‖kHat b E X * D⁻¹‖ * ‖D * matrixExpect μ (gRes b E X) - 1‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ CK0 * (Cm / (W : ℝ) ^ 2) := mul_le_mul hKDn (hmf W hWm X hX) (norm_nonneg _) (by positivity)
    _ ≤ max (max CK0 CD') (CK0 * Cm) / (W : ℝ) ^ 2 := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The weighted mean-field expansion. -/
theorem weightedExpansion (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) -
          kHat b E X * (dressed b E X)⁻¹ *
            (matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) +
            ∑ j, selfEnergy b
                (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
                  ∂layerLaw W b .oneBlockOnePort)
                (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
                  ∂layerLaw W b .oneBlockOnePort) *
              matrixExpect (layerLaw W b .oneBlockOnePort)
                (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Ce, We, hCe, hexp⟩ := meanExpansion hA hb0 hb h1 h2 Lw Kd
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv hA hb0 hb h1 h2
  refine ⟨CK * Ce, max We WK, by positivity, fun W hW X hX ℓ hℓ wd D hD => ?_⟩
  obtain ⟨hU, -, hKD, -⟩ := hK W (le_trans (le_max_right _ _) hW) X hX
  have he := hexp W (le_trans (le_max_left _ _) hW) X hX ℓ hℓ wd D hD
  set T := matrixExpect (layerLaw W b .oneBlockOnePort)
    (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D)
  set R := matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) +
    ∑ j, selfEnergy b
        (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
          ∂layerLaw W b .oneBlockOnePort)
        (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
          ∂layerLaw W b .oneBlockOnePort) *
      matrixExpect (layerLaw W b .oneBlockOnePort)
        (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j)
  have hDinvD : (dressed b E X)⁻¹ * dressed b E X = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have e : kHat b E X * T - kHat b E X * (dressed b E X)⁻¹ * R =
      kHat b E X * (dressed b E X)⁻¹ * (dressed b E X * T - R) := by
    rw [Matrix.mul_sub]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (kHat b E X), hDinvD, Matrix.mul_one]
  have he' : ‖dressed b E X * T - R‖ ≤ Ce / (W : ℝ) ^ 2 := by
    have : dressed b E X * T - R = dressed b E X * T -
        matrixExpect (layerLaw W b .oneBlockOnePort)
          (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D) -
        ∑ j, selfEnergy b
            (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 0
              ∂layerLaw W b .oneBlockOnePort)
            (∫ ω, blkTr (gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) 1
              ∂layerLaw W b .oneBlockOnePort) *
          matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) := by
      simp only [R]; abel
    rw [this]; exact he
  rw [e]
  calc _ ≤ ‖kHat b E X * (dressed b E X)⁻¹‖ * ‖dressed b E X * T - R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ CK * (Ce / (W : ℝ) ^ 2) := mul_le_mul hKD he' (norm_nonneg _) hCK
    _ = _ := by ring

end BlockBand.Transmission.SourceMixing
