module

public import BlockBand.Transmission.LengthUniform.BulkMeanField

/-!
# Bulk-uniform mean-field equation in operator norm and dressed inverse

`‖(H₀ - S̄)E𝒢 - I‖ ≤ C/W²` for strictly passive inputs, and the invertibility of `H₀ - S̄` with
`‖E𝒢 - (H₀ - S̄)⁻¹‖ ≤ C/W²`, uniformly in `E ∈ bulkInterval κ`: the constants and `W₀` depend only
on `b`, the bulk margin `κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Bulk-uniform `meanField_op`: `‖(H₀ - S̄)E𝒢 - I‖ ≤ C/W²` for strictly passive `X`, with
`C, W₀` depending on `b, κ` only. -/
theorem meanField_op_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        ‖dressed b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - 1‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨W₁, hSD⟩ := meanSD_phys_bulk hA hb0 hb hκ
  obtain ⟨W₂, hSDp⟩ := meanSD_port_bulk hA hb0 hb hκ
  obtain ⟨C, W₃, hC0, hcov⟩ := traceCov_op_bulk hA hb0 hb hκ
  obtain ⟨_, W₄, hmom⟩ := hA.moments b hb0 hb κ hκ 1 le_rfl
  refine ⟨8 * C, max (max (max W₁ W₂) (max W₃ W₄)) 1, by positivity, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hW1 : W₁ ≤ W := by omega
  have hW2 : W₂ ≤ W := by omega
  have hW3 : W₃ ≤ W := by omega
  have hW4 : W₄ ≤ W := by omega
  have hWc : (W : ℂ) ≠ 0 := by
    have : 1 ≤ W := by omega
    exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  set μ := layerLaw W b .oneBlockOnePort
  set H₀ := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) 0
  obtain ⟨i0, iG, iG0, c0⟩ := hcov W hW3 E hE X hX.posSemidef 0
  obtain ⟨-, -, iG3, c3⟩ := hcov W hW3 E hE X hX.posSemidef 3
  -- (a) `E[V𝒢] = I - H₀ E𝒢`
  have hVG : matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) = 1 - H₀ * matrixExpect μ (gRes b E X) := by
    ext α β
    have hae : ∀ᵐ ω ∂μ, (layerLin ω * gRes b E X ω) α β = (1 : LayerMat W) α β -
        ∑ γ, H₀ α γ * gRes b E X ω γ β := by
      filter_upwards [(hmom W hW4 E hE _
        (boundaryZ_mem_paramDisk (by linarith) h1 h2) X hX.posSemidef).1] with ω hω
      rw [layerLin_mul_gRes b E X ω ((Matrix.isUnit_iff_isUnit_det _).mpr hω)]
      rfl
    show ∫ ω, (layerLin ω * gRes b E X ω) α β ∂μ = (1 - H₀ * matrixExpect μ (gRes b E X)) α β
    rw [integral_congr_ae hae, integral_sub (integrable_const _)
      (integrable_finsetSum _ fun γ _ => (iG γ β).const_mul _), integral_const,
      integral_finsetSum _ fun γ _ => (iG γ β).const_mul _]
    simp [Matrix.sub_apply, Matrix.mul_apply, matrixExpect, integral_const_mul]
    rfl
  -- (b) `E[V𝒢] + S̄E𝒢 = -(diag d₁ Cov₀ + diag d₂ Cov₃)`
  set d₁ : LayerSite W .oneBlockOnePort → ℂ :=
    Sum.elim (fun _ => ((1 - 2 * b : ℝ) : ℂ)) fun _ => (b : ℂ)
  set d₂ : LayerSite W .oneBlockOnePort → ℂ := Sum.elim (fun _ => (b : ℂ)) fun _ => 0
  have hXi : matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) +
      selfEnergy b (meanTr b E X 0) (meanTr b E X 3) * matrixExpect μ (gRes b E X) =
      -(diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
        diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X)) := by
    have h0 : ∀ a : Fin 1, a = 0 := fun a => Subsingleton.elim _ _
    ext α β
    rcases α with ⟨i0, x⟩ | ⟨i0, x⟩ <;> rw [h0 i0]
    · have t0 : ∀ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (phys x) β =
          (W : ℂ) * (trLetter b E X 0 ω * gRes b E X ω (phys x) β) := fun ω => by
        rw [← trace_letter0, trace_letter_eq b E X hWc]; ring
      have t3 : ∀ ω, (∑ y, gRes b E X ω (port y) (port y)) * gRes b E X ω (phys x) β =
          (W : ℂ) * (trLetter b E X 3 ω * gRes b E X ω (phys x) β) := fun ω => by
        rw [← trace_letter3, trace_letter_eq b E X hWc]; ring
      have e := hSD W hW1 E hE X hX x β
      simp only [t0, t3, integral_const_mul, gueVar_cast hb, ginVar_cast hb0] at e
      have lhs : (matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) +
          selfEnergy b (meanTr b E X 0) (meanTr b E X 3) * matrixExpect μ (gRes b E X) :
            LayerMat W) (phys x) β =
          ∫ ω, (layerLin ω * gRes b E X ω) (phys x) β ∂μ +
            (((1 - 2 * b : ℝ) : ℂ) * meanTr b E X 0 + (b : ℂ) * meanTr b E X 3) *
              ∫ ω, gRes b E X ω (phys x) β ∂μ := by
        simp only [Matrix.add_apply, selfEnergy, diagonal_mul]; rfl
      have rhs : (-(diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
          diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X)) : LayerMat W) (phys x) β =
          -(((1 - 2 * b : ℝ) : ℂ) * ((∫ ω, trLetter b E X 0 ω * gRes b E X ω (phys x) β ∂μ) -
              meanTr b E X 0 * ∫ ω, gRes b E X ω (phys x) β ∂μ) +
            (b : ℂ) * ((∫ ω, trLetter b E X 3 ω * gRes b E X ω (phys x) β ∂μ) -
              meanTr b E X 3 * ∫ ω, gRes b E X ω (phys x) β ∂μ)) := by
        simp only [Matrix.neg_apply, Matrix.add_apply, diagonal_mul]; rfl
      rw [lhs, rhs, e]
      field_simp
      ring
    · have t0 : ∀ ω, (∑ y, gRes b E X ω (phys y) (phys y)) * gRes b E X ω (port x) β =
          (W : ℂ) * (trLetter b E X 0 ω * gRes b E X ω (port x) β) := fun ω => by
        rw [← trace_letter0, trace_letter_eq b E X hWc]; ring
      have e := hSDp W hW2 E hE X hX x β
      simp only [t0, integral_const_mul, ginVar_cast hb0] at e
      have lhs : (matrixExpect μ (fun ω => layerLin ω * gRes b E X ω) +
          selfEnergy b (meanTr b E X 0) (meanTr b E X 3) * matrixExpect μ (gRes b E X) :
            LayerMat W) (port x) β =
          ∫ ω, (layerLin ω * gRes b E X ω) (port x) β ∂μ +
            ((b : ℂ) * meanTr b E X 0) * ∫ ω, gRes b E X ω (port x) β ∂μ := by
        simp only [Matrix.add_apply, selfEnergy, diagonal_mul]; rfl
      have rhs : (-(diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
          diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X)) : LayerMat W) (port x) β =
          -((b : ℂ) * ((∫ ω, trLetter b E X 0 ω * gRes b E X ω (port x) β ∂μ) -
              meanTr b E X 0 * ∫ ω, gRes b E X ω (port x) β ∂μ) +
            0 * ((∫ ω, trLetter b E X 3 ω * gRes b E X ω (port x) β ∂μ) -
              meanTr b E X 3 * ∫ ω, gRes b E X ω (port x) β ∂μ)) := by
        simp only [Matrix.neg_apply, Matrix.add_apply, diagonal_mul]; rfl
      rw [lhs, rhs, e]
      field_simp
      ring
  -- (c) `D E𝒢 - I = -Ξ`
  have hD : dressed b E X * matrixExpect μ (gRes b E X) - 1 =
      diagonal d₁ * covMat μ (trLetter b E X 0) (gRes b E X) +
        diagonal d₂ * covMat μ (trLetter b E X 3) (gRes b E X) := by
    rw [← neg_neg (diagonal d₁ * _ + _), ← hXi, hVG, dressed, Matrix.sub_mul]
    abel
  rw [hD]
  have hn1 : ‖diagonal d₁‖ ≤ 1 := norm_diagonal_le _ zero_le_one fun i => by
    rcases i with i | i
    · simp only [d₁, Sum.elim_inl, Complex.norm_real, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b)]
      linarith
    · simp only [d₁, Sum.elim_inr, Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
  have hn2 : ‖diagonal d₂‖ ≤ 1 := norm_diagonal_le _ zero_le_one fun i => by
    rcases i with i | i
    · simp only [d₂, Sum.elim_inl, Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
    · simp [d₂]
  have hc : 0 ≤ 4 * C / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖diagonal d₁‖ * ‖covMat μ (trLetter b E X 0) (gRes b E X)‖ +
        ‖diagonal d₂‖ * ‖covMat μ (trLetter b E X 3) (gRes b E X)‖ :=
        (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
    _ ≤ 1 * (4 * C / (W : ℝ) ^ 2) + 1 * (4 * C / (W : ℝ) ^ 2) := by
        gcongr
    _ = 8 * C / (W : ℝ) ^ 2 := by ring

/-- Bulk-uniform `dressed_inverse`: `H₀ - S̄` is invertible, `‖(H₀ - S̄)⁻¹‖ ≤ C` and
`‖E𝒢 - (H₀ - S̄)⁻¹‖ ≤ C/W²`, with `C, W₀` depending on `b, κ` only. -/
theorem dressed_inverse_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        IsUnit (dressed b E X) ∧ ‖(dressed b E X)⁻¹‖ ≤ C ∧
          ‖matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - (dressed b E X)⁻¹‖ ≤
            C / (W : ℝ) ^ 2 := by
  obtain ⟨Cm, Wm, hCm, hmf⟩ := meanField_op_bulk hA hb0 hb hκ
  obtain ⟨C₁, W₁, hm1⟩ := layer_moments_bulk hA hb0 hb hκ 1 le_rfl
  obtain ⟨_, W₂, _, hcov⟩ := traceCov_op_bulk hA hb0 hb hκ
  set C₁' := max C₁ 0
  refine ⟨max (2 * C₁') (2 * C₁' * Cm), max (max Wm W₁) (max W₂ (⌈2 * Cm⌉₊ + 1)),
    fun W hW E hE X hX => ?_⟩
  have hWm : Wm ≤ W := by omega
  have hW1 : W₁ ≤ W := by omega
  have hW2 : W₂ ≤ W := by omega
  have hW3 : ⌈2 * Cm⌉₊ + 1 ≤ W := by omega
  set μ := layerLaw W b .oneBlockOnePort
  set A := dressed b E X
  set B := matrixExpect μ (gRes b E X)
  set T := A * B - 1
  have hWpos : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hT : ‖T‖ ≤ Cm / (W : ℝ) ^ 2 := hmf W hWm E hE X hX
  have hT2 : Cm / (W : ℝ) ^ 2 ≤ 1 / 2 := by
    have h2C : 2 * Cm ≤ W := by
      have := Nat.le_ceil (2 * Cm)
      have : ((⌈2 * Cm⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW3
      push_cast at this; linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- `‖E𝒢‖ ≤ C₁`
  have hB : ‖B‖ ≤ C₁' := by
    obtain ⟨-, iG, -, -⟩ := hcov W hW2 E hE X hX.posSemidef 0
    have hmem := hm1 W hW1 E hE X hX.posSemidef
    have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
    have hgm : Measurable fun ω => ‖gRes b E X ω‖ := continuous_norm.measurable.comp hGm
    have hmemLp : MemLp (fun ω => ‖gRes b E X ω‖) 1 μ := by
      rw [MemLp, ← ENNReal.ofReal_one]; exact lt_of_le_of_lt hmem ENNReal.ofReal_lt_top
    have hint := hmemLp.integrable le_rfl
    refine (norm_matrixExpect_le _ iG hint).trans ?_
    have h := hmem
    rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm hgm.aestronglyMeasurable] at h
    have hI : ∫ ω, ‖gRes b E X ω‖ ∂μ = (∫⁻ ω, ‖‖gRes b E X ω‖‖ₑ ∂μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
        hgm.aestronglyMeasurable]
      congr 1
      refine lintegral_congr fun ω => ?_
      rw [Real.enorm_eq_ofReal (norm_nonneg _)]
    rw [hI]
    exact (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  -- Neumann series for `A B = 1 + T`
  have hTn : ‖-T‖ < 1 := by rw [norm_neg]; linarith
  set u := Units.oneSub (-T) hTn
  have hu : (u : LayerMat W) = A * B := by
    simp only [u, Units.val_oneSub, sub_neg_eq_add, T]; abel
  set v : LayerMat W := ↑u⁻¹
  have hv1 : A * B * v = 1 := by rw [← hu]; exact u.mul_inv
  have hv2 : v = 1 - T * v := by
    have : (1 + T) * v = 1 := by rw [show 1 + T = A * B by simp [T]]; exact hv1
    rw [add_mul, one_mul] at this
    rw [← this]; abel
  have hvn : ‖v‖ ≤ 2 := by
    have h := norm_sub_le (1 : LayerMat W) (T * v)
    rw [← hv2] at h
    have := Matrix.l2_opNorm_mul T v
    have := norm_one_matrix_le (n := LayerSite W .oneBlockOnePort)
    nlinarith [norm_nonneg v, norm_nonneg T]
  have hAinv : A * (B * v) = 1 := by rw [← Matrix.mul_assoc]; exact hv1
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr
    (IsUnit.of_mul_eq_one _ (by rw [← det_mul, hAinv, det_one]))
  have hinv : A⁻¹ = B * v := Matrix.inv_eq_right_inv hAinv
  have hC₁' : 0 ≤ C₁' := le_max_right _ _
  refine ⟨hAu, ?_, ?_⟩
  · rw [hinv]
    calc ‖B * v‖ ≤ ‖B‖ * ‖v‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ C₁' * 2 := mul_le_mul hB hvn (norm_nonneg _) hC₁'
      _ ≤ _ := by rw [mul_comm]; exact le_max_left _ _
  · rw [hinv]
    have e : B - B * v = B * (T * v) := by
      conv_lhs => rw [hv2]
      rw [Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e]
    calc ‖B * (T * v)‖ ≤ ‖B‖ * (‖T‖ * ‖v‖) :=
          (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _)
            (norm_nonneg _))
      _ ≤ C₁' * (Cm / (W : ℝ) ^ 2 * 2) := by gcongr
      _ = 2 * C₁' * Cm / (W : ℝ) ^ 2 := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end BlockBand.Transmission.LengthUniform
