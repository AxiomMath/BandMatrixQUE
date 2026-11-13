module

public import BlockBand.Transmission.SourceMixing.MeanBlockTools
public import BlockBand.Transmission.SourceMixing.Weighted
public import BlockBand.Transmission.SourceMixing.MassMeanDomain
public import BlockBand.Transmission.LengthUniform.BulkMeanIdentify

/-!
# Bulk-uniform dressed blocks, weighted dressed inverse and matched values

Versions of `dressedBlocks`, `norm_kHat_dressedInv` and `mm_matched0` whose constants and `W₀`
depend only on `b` and the bulk margin `κ`, uniformly in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Bulk-uniform `dressedBlocks`: `D⁻¹ = diag(M, vI)` and `E𝒢 = D⁻¹ + O(W⁻²)` blockwise, with
`CD, W₀` depending on `b, κ` only. -/
theorem dressedBlocks_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (CD : ℝ) (W₀ : ℕ), 0 ≤ CD ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        1 ≤ W ∧ ‖(dressed b E X)⁻¹‖ ≤ CD ∧ ‖mOf b E X‖ ≤ CD ∧ ‖vOf b E X‖ ≤ CD ∧
        (∀ N : LayerMat W, blkAt ((dressed b E X)⁻¹ * N) 0 0 = mOf b E X * blkAt N 0 0) ∧
        (∀ N : LayerMat W, blkAt ((dressed b E X)⁻¹ * N) 1 1 = vOf b E X • blkAt N 1 1) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
          CD / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
          vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2 ∧
        (∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort)) ∧
        (zetaX b E X • 1 - X) * mOf b E X = 1 ∧ mOf b E X * (zetaX b E X • 1 - X) = 1 := by
  obtain ⟨CD, W₁, hCD, hres⟩ := mean_residuals_bulk hA hb0 hb hκ
  obtain ⟨_, Wt, _, hcov⟩ := traceCov_op_bulk hA hb0 hb hκ
  obtain ⟨_, WD, hDI⟩ := dressed_inverse_bulk hA hb0 hb hκ
  refine ⟨CD, max (max W₁ Wt) WD, hCD, fun W hW E hE X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWt⟩, hWD⟩ := hW
  obtain ⟨hU, -, -⟩ := hDI W hWD E hE X hX
  obtain ⟨hW1, hDn, hDc, hMz, -, e11, e01, e10, -⟩ := hres W hW₁ E hE X hX
  have hG := (hcov W hWt E hE X hX.posSemidef 0).2.1
  set N := (dressed b E X)⁻¹
  have hN1 : dressed b E X * N = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  obtain ⟨eA, -, -, -, -, -⟩ := blkAt_dressed_inv b E X hW1 N hN1
  have hv : ‖vOf b E X‖ ≤ CD := by
    have h := norm_entry_le' N (siteOf 1 ⟨0, hW1⟩) (siteOf 1 ⟨0, hW1⟩)
    have e : N (siteOf 1 ⟨0, hW1⟩) (siteOf 1 ⟨0, hW1⟩) = vOf b E X := by
      have := congrFun (congrFun e11 ⟨0, hW1⟩) ⟨0, hW1⟩
      simpa [blkAt, vOf] using this
    rw [e] at h; exact h.trans hDn
  have hBN : ‖matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - N‖ ≤ CD / (W : ℝ) ^ 2 := by
    rw [← div_sq_eq]; exact hDc
  refine ⟨hW1, hDn, (norm_blkAt_le _ _ _).trans hDn, hv, fun M => ?_, fun M => ?_, ?_, ?_, hG,
    eA, hMz⟩
  · rw [blkAt_mul, Fin.sum_univ_two, e01, Matrix.zero_mul, add_zero]; rfl
  · rw [blkAt_mul, Fin.sum_univ_two, e10, Matrix.zero_mul, zero_add, e11, Matrix.smul_mul,
      Matrix.one_mul]; rfl
  · rw [mOf, ← blkAt_sub]; exact (norm_blkAt_le _ _ _).trans hBN
  · have : vOf b E X • (1 : Matrix (Fin W) (Fin W) ℂ) = blkAt N 1 1 := by rw [e11]; rfl
    rw [this, ← blkAt_sub]; exact (norm_blkAt_le _ _ _).trans hBN

/-- Bulk-uniform `norm_kHat_dressedInv`: `‖K̂D⁻¹‖ ≤ C_K` and `E[K̂𝒢] = K̂D⁻¹ + O(W⁻²)`, with
`CK, W₀` depending on `b, κ` only. -/
theorem norm_kHat_dressedInv_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (CK : ℝ) (W₀ : ℕ), 0 ≤ CK ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        IsUnit (dressed b E X) ∧ ‖(dressed b E X)⁻¹‖ ≤ CK ∧
        ‖kHat b E X * (dressed b E X)⁻¹‖ ≤ CK ∧
        ‖kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) -
          kHat b E X * (dressed b E X)⁻¹‖ ≤ CK / (W : ℝ) ^ 2 := by
  obtain ⟨CD, WD, hDI⟩ := dressed_inverse_bulk hA hb0 hb hκ
  obtain ⟨Cm, Wm, hCm, hmf⟩ := meanField_op_bulk hA hb0 hb hκ
  obtain ⟨_, Wt, _, hcov⟩ := traceCov_op_bulk hA hb0 hb hκ
  set CD' := max CD 0
  set Cz := (2 : ℝ) + 2 + 2 * CD' + 2 * CD' + 1 + 2 + 2 * CD' with hCz
  set CK0 := 1 + 2 * Cz * CD'
  refine ⟨max (max CK0 CD') (CK0 * Cm), max (max WD Wm) (max Wt 1), by positivity,
    fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hz2 := bulk_norm_z hb0 hb hκ hE
  have hE2 : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWD, hWm⟩, hWt, hW1⟩ := hW
  obtain ⟨hU, hDn, hEc⟩ := hDI W hWD E hE X hX
  have hDn' : ‖(dressed b E X)⁻¹‖ ≤ CD' := hDn.trans (le_max_left _ _)
  set μ := layerLaw W b .oneBlockOnePort
  set D := dressed b E X
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW2 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ hWr
  -- `‖E𝒢‖ ≤ 2CD'`
  have hEG : ‖matrixExpect μ (gRes b E X)‖ ≤ 2 * CD' := by
    have h' : ‖matrixExpect μ (gRes b E X) - D⁻¹‖ ≤ CD' := hEc.trans (by
      calc CD / (W : ℝ) ^ 2 ≤ CD' / (W : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ CD' := div_le_self (le_max_right _ _) hW2)
    have h := norm_add_le (matrixExpect μ (gRes b E X) - D⁻¹) D⁻¹
    rw [sub_add_cancel] at h
    linarith
  have hGint : ∀ α β, Integrable (fun ω => gRes b E X ω α β) μ :=
    (hcov W hWt E hE X hX.posSemidef 0).2.1
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
    _ ≤ CK0 * (Cm / (W : ℝ) ^ 2) := mul_le_mul hKDn (hmf W hWm E hE X hX) (norm_nonneg _) (by positivity)
    _ ≤ max (max CK0 CD') (CK0 * Cm) / (W : ℝ) ^ 2 := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Bulk-uniform `mm_matched0`: matched values with `δ₀ + W⁻²` errors, with `d₀, C, W₀`
depending on `b, κ` only. -/
theorem mm_matched0_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖boundaryZ b E - zetaX b E X‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ∧
        ‖kmOf b E X - 1‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ∧
        ‖hOf b E X - 1‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hmi⟩ := mean_identify_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨CR, WR, -, hres⟩ := mean_residuals_bulk hA hb0 hb hκ
  set Cv := CD * b * Cm
  refine ⟨d₀, Cm + Cm * CD + (CD + 1) * Cv, max (max Wm WD) WR, hd₀, by positivity,
    fun W hW E hE X hX hd => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWD⟩, hWR⟩ := hW
  obtain ⟨hm1, hm2, -⟩ := hmi W hWm E hE X hX hd
  obtain ⟨-, -, hM, hv, -, -, -, -, -, hzM, -⟩ := hD W hWD E hE X hX
  obtain ⟨-, -, -, -, hβ, -⟩ := hres W hWR E hE X hX
  set e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2
  have he : 0 ≤ e := by have : 0 ≤ jetDistance0 b E X := norm_nonneg _; positivity
  set M := mOf b E X
  set a := matchedA E
  set z := boundaryZ b E
  set ζ := zetaX b E X
  have hz : ‖z - ζ‖ ≤ Cm * e := by
    have h := PathJet.zeta_sub_z b E h1 h2 (meanTr b E X 0) (meanTr b E X 3)
    change ‖boundaryZ b E - zetaOf b E (meanTr b E X 0) (meanTr b E X 3)‖ ≤ _
    rw [← norm_neg, neg_sub, h, norm_neg]
    have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, nc, nb]
    have hc : 0 ≤ 1 - 2 * b := by linarith
    have : 0 ≤ Cm * e := by positivity
    calc (1 - 2 * b) * ‖meanTr b E X 0 - a‖ + b * ‖meanTr b E X 3 - a‖
        ≤ (1 - 2 * b) * (Cm * e) + b * (Cm * e) := by gcongr
      _ ≤ Cm * e := by nlinarith
  have hKM : kmOf b E X - 1 = (z - ζ) • M := by
    have e' : kmOf b E X = (z • 1 - X) * M := (blkAt_kHat_mul_zero b E X _).1
    rw [e', show z • (1 : Matrix (Fin W) (Fin W) ℂ) - X = (z - ζ) • 1 + (ζ • 1 - X) by
      rw [sub_smul]; abel, Matrix.add_mul, hzM, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hKM' : ‖kmOf b E X - 1‖ ≤ Cm * CD * e := by
    rw [hKM]
    calc ‖(z - ζ) • M‖ ≤ ‖z - ζ‖ * ‖M‖ := norm_smul_le _ _
      _ ≤ Cm * e * CD := mul_le_mul hz hM (norm_nonneg _) (by positivity)
      _ = Cm * CD * e := by ring
  have ha0 : a ≠ 0 := matchedA_ne_zero E h1 h2
  have hna : ‖a‖ = 1 := norm_matchedA E h1 h2
  have hva : vOf b E X - a = vOf b E X * a * (b : ℂ) * (meanTr b E X 0 - a) := by
    have hβ' : (a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0 ≠ 0 := hβ
    show ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0)⁻¹ - a =
      ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0)⁻¹ * a * (b : ℂ) * (meanTr b E X 0 - a)
    have hD2 : 1 - a * (b : ℂ) * meanTr b E X 0 + a ^ 2 * (b : ℂ) ≠ 0 := by
      have e' : 1 - a * (b : ℂ) * meanTr b E X 0 + a ^ 2 * (b : ℂ) =
          a * ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0) := by field_simp; ring
      rw [e']; exact mul_ne_zero ha0 hβ'
    have hinv := mul_inv_cancel₀ hD2
    field_simp
    linear_combination hinv
  have hva' : ‖vOf b E X - a‖ ≤ Cv * e := by
    rw [hva, norm_mul, norm_mul, norm_mul, hna, Complex.norm_real, Real.norm_of_nonneg hb0.le,
      mul_one]
    calc ‖vOf b E X‖ * b * ‖meanTr b E X 0 - a‖ ≤ CD * b * (Cm * e) := by gcongr
      _ = Cv * e := by ring
  have hh' : ‖hOf b E X - 1‖ ≤ (CD + 1) * Cv * e := by
    have e' : hOf b E X - 1 = (vOf b E X - a) * conj (vOf b E X) + a * conj (vOf b E X - a) := by
      unfold hOf
      rw [map_sub]
      have : a * conj a = 1 := matchedA_mul_conj E h1 h2
      linear_combination this
    rw [e']
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hna]
    calc ‖vOf b E X - a‖ * ‖vOf b E X‖ + 1 * ‖vOf b E X - a‖ = (‖vOf b E X‖ + 1) *
          ‖vOf b E X - a‖ := by ring
      _ ≤ (CD + 1) * (Cv * e) := mul_le_mul (by linarith) hva' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hCv : 0 ≤ Cv := by positivity
  have p1 : 0 ≤ Cm * CD := by positivity
  have p2 : 0 ≤ (CD + 1) * Cv := by positivity
  have hle : ∀ K : ℝ, 0 ≤ K → K ≤ Cm + Cm * CD + (CD + 1) * Cv →
      K * e ≤ (Cm + Cm * CD + (CD + 1) * Cv) * e := fun K _ hK => mul_le_mul_of_nonneg_right hK he
  exact ⟨hz.trans (hle _ hCm (by linarith)), hKM'.trans (hle _ p1 (by linarith)),
    hh'.trans (hle _ p2 (by linarith))⟩

end BlockBand.Transmission.LengthUniform
