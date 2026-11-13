module

public import BlockBand.Transmission.PassiveCovariance.MeanBlocks
public import BlockBand.Transmission.PathScalar.MeanEqStrict

/-!
# Identification of the mean matrix: `E𝒢 = diag(R, aI) + O(δ₀ + W⁻²)` (`𝖬 = R, a`)

At the stationary scalar point the mean blocks are `𝖬₁ = R`, `𝖬₂ = a`. **Hypothesis:**
`PassiveBoundsStatement`. Stability of the 2-scalar mean equations is
`PathScalar.passiveMean_stability` and `mean_stage_one`, applied to the mean traces
`m₁ = E⟨𝒢₁₁⟩`, `m₂ = E⟨𝒢₂₂⟩` with the residuals read off `dressed_inverse` (block
form: `MeanBlocks`).

`mean_identify`: fixed `b, E ∈ (-2, 2)`; then `d₀ > 0`, `C`, `W₀`; for `W ≥ W₀` and every strictly
passive `X` with `δ₀(X) ≤ d₀`, under `layerLaw W b .oneBlockOnePort`:
`|m₁ - a| + |m₂ - a| ≤ C(δ₀ + W⁻²)` and `‖E𝒢 - diag(R, aI)‖ ≤ C(δ₀ + W⁻²)` (operator norm,
`meanTarget`). Uniform in `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PathScalar
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- The limiting mean matrix `diag(R, aI)`, `R = (z - X)⁻¹`. -/
def meanTarget (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : LayerMat W :=
  fromBlocks (liftX (passiveResolvent b E X)) 0 0 (matchedA E • 1)

theorem blkAt_meanTarget (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    blkAt (meanTarget b E X) 0 0 = passiveResolvent b E X ∧ blkAt (meanTarget b E X) 0 1 = 0 ∧
      blkAt (meanTarget b E X) 1 0 = 0 ∧ blkAt (meanTarget b E X) 1 1 = matchedA E • 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x y <;>
    simp [blkAt, siteOf, meanTarget, liftX, Matrix.one_apply]

theorem normTrace_smul_one (c : ℂ) (hW : 1 ≤ W) :
    (W : ℂ)⁻¹ * (c • (1 : Matrix (Fin W) (Fin W) ℂ)).trace = c := by
  have : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]; field_simp

theorem norm_smul_one_le (c : ℂ) : ‖c • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ ‖c‖ :=
  (norm_smul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_left norm_one_matrix_le (norm_nonneg c))

theorem norm_le_of_smul_one {c : ℂ} {M : Matrix (Fin W) (Fin W) ℂ} (hW : 1 ≤ W)
    (h : M = c • 1) : ‖c‖ ≤ ‖M‖ := by
  have e : M ⟨0, hW⟩ ⟨0, hW⟩ = c := by rw [h]; simp
  calc ‖c‖ = ‖M ⟨0, hW⟩ ⟨0, hW⟩‖ := by rw [e]
    _ ≤ ‖M‖ := norm_entry_le' M _ _

/-- `m_k` is the normalized trace of a diagonal block of `E𝒢`. -/
theorem meanTr_eq_blk (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort)) :
    meanTr b E X 0 = (W : ℂ)⁻¹ * (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0).trace ∧
      meanTr b E X 3 = (W : ℂ)⁻¹ *
        (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1).trace := by
  constructor
  · simp only [meanTr, trLetter, trace_letter0, integral_const_mul]
    rw [integral_finsetSum _ fun x _ => hG _ _]
    congr 1
  · simp only [meanTr, trLetter, trace_letter3, integral_const_mul]
    rw [integral_finsetSum _ fun x _ => hG _ _]
    congr 1

/-- **Residuals of the 2-scalar mean equations** from `dressed_inverse` (block form). -/
theorem mean_residuals (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (CD : ℝ) (W₀ : ℕ), 0 ≤ CD ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        1 ≤ W ∧ ‖(dressed b E X)⁻¹‖ ≤ CD ∧
        ‖matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - (dressed b E X)⁻¹‖ ≤
          CD * (W : ℝ)⁻¹ ^ 2 ∧
        blkAt (dressed b E X)⁻¹ 0 0 *
          (zetaOf b E (meanTr b E X 0) (meanTr b E X 3) • 1 - X) = 1 ∧
        boundaryZ b E - (b : ℂ) * meanTr b E X 0 ≠ 0 ∧
        blkAt (dressed b E X)⁻¹ 1 1 = (boundaryZ b E - (b : ℂ) * meanTr b E X 0)⁻¹ • 1 ∧
        blkAt (dressed b E X)⁻¹ 0 1 = 0 ∧ blkAt (dressed b E X)⁻¹ 1 0 = 0 ∧
        (meanTr b E X 0).im ≤ 0 ∧ ‖meanTr b E X 0‖ ≤ 2 * CD ∧
        ‖meanTr b E X 0 - stieltjes X (zetaOf b E (meanTr b E X 0) (meanTr b E X 3))‖ ≤
          CD * (W : ℝ)⁻¹ ^ 2 ∧
        ‖meanTr b E X 3 * (boundaryZ b E - (b : ℂ) * meanTr b E X 0) - 1‖ ≤
          (‖boundaryZ b E‖ + b * (2 * CD)) * (CD * (W : ℝ)⁻¹ ^ 2) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨CD, WD, hDI⟩ := dressed_inverse hA hb0 hb h1 h2
  obtain ⟨_, Wt, _, hcov⟩ := traceCov_op hA hb0 hb h1 h2
  refine ⟨max CD 0, max (max WD Wt) 1, le_max_right _ _, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWD, hWt⟩, hW1⟩ := hW
  have hCD : 0 ≤ max CD 0 := le_max_right _ _
  obtain ⟨hDu, hDn, hDc⟩ := hDI W hWD X hX
  obtain ⟨hPi, hG, -, -⟩ := hcov W hWt X hX.posSemidef 0
  set μ := layerLaw W b .oneBlockOnePort
  set N := (dressed b E X)⁻¹
  set B := matrixExpect μ (gRes b E X)
  have hN1 : dressed b E X * N = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hDu)
  obtain ⟨eA, eA', hβ, e11, e01, e10⟩ := blkAt_dressed_inv b E X hW1 N hN1
  obtain ⟨hm1, hm2⟩ := meanTr_eq_blk b E X hG
  have hNn : ‖N‖ ≤ max CD 0 := hDn.trans (le_max_left _ _)
  have hBN : ‖B - N‖ ≤ max CD 0 * (W : ℝ)⁻¹ ^ 2 := by
    refine hDc.trans ?_
    rw [div_eq_mul_inv, inv_pow]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hWinv : (W : ℝ)⁻¹ ^ 2 ≤ 1 := by
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWr
    nlinarith [inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ W)]
  have hBn : ‖B‖ ≤ 2 * max CD 0 := by
    have h0 : max CD 0 * (W : ℝ)⁻¹ ^ 2 ≤ max CD 0 := by nlinarith
    calc ‖B‖ = ‖B - 0‖ := by rw [sub_zero]
      _ ≤ ‖B - N‖ + ‖N - 0‖ := norm_sub_le_norm_sub_add_norm_sub B N 0
      _ ≤ max CD 0 + max CD 0 := by rw [sub_zero]; linarith
      _ = 2 * max CD 0 := by ring
  have hm1C : ‖meanTr b E X 0‖ ≤ 2 * max CD 0 := by
    rw [hm1]; exact (norm_normTrace_le _).trans ((norm_blkAt_le _ _ _).trans hBn)
  have hAinv : (zetaOf b E (meanTr b E X 0) (meanTr b E X 3) • (1 : Matrix (Fin W) (Fin W) ℂ) -
      X)⁻¹ = blkAt N 0 0 := Matrix.inv_eq_right_inv eA
  have hr : ‖meanTr b E X 0 - stieltjes X (zetaOf b E (meanTr b E X 0) (meanTr b E X 3))‖ ≤
      max CD 0 * (W : ℝ)⁻¹ ^ 2 := by
    have e : meanTr b E X 0 - stieltjes X (zetaOf b E (meanTr b E X 0) (meanTr b E X 3)) =
        (W : ℂ)⁻¹ * (blkAt (B - N) 0 0).trace := by
      rw [stieltjes, hAinv, blkAt_sub, trace_sub, mul_sub, ← hm1]
    rw [e]
    exact (norm_normTrace_le _).trans ((norm_blkAt_le _ _ _).trans hBN)
  set β := boundaryZ b E - (b : ℂ) * meanTr b E X 0
  have hm2β : ‖meanTr b E X 3 - β⁻¹‖ ≤ max CD 0 * (W : ℝ)⁻¹ ^ 2 := by
    have e : meanTr b E X 3 - β⁻¹ = (W : ℂ)⁻¹ * (blkAt (B - N) 1 1).trace := by
      rw [blkAt_sub, trace_sub, mul_sub, e11, normTrace_smul_one _ hW1, ← hm2]
    rw [e]
    exact (norm_normTrace_le _).trans ((norm_blkAt_le _ _ _).trans hBN)
  have hs : ‖meanTr b E X 3 * β - 1‖ ≤
      (‖boundaryZ b E‖ + b * (2 * max CD 0)) * (max CD 0 * (W : ℝ)⁻¹ ^ 2) := by
    have e : meanTr b E X 3 * β - 1 = β * (meanTr b E X 3 - β⁻¹) := by field_simp
    rw [e, norm_mul]
    have hβn : ‖β‖ ≤ ‖boundaryZ b E‖ + b * (2 * max CD 0) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hm1C hb0.le)
    exact mul_le_mul hβn hm2β (norm_nonneg _) (by positivity)
  have hv0 : (meanTr b E X 0).im ≤ 0 := by
    have : (meanTr b E X 0).im = ∫ ω, (physTr b E X ω).im ∂μ := (integral_im hPi).symm
    rw [this]
    exact integral_nonpos_of_ae ((ae_layer_herm b).mono fun ω hA' => im_physTr_nonpos hη hX ω hA')
  exact ⟨hW1, hNn, hBN, eA', hβ, e11, e01, e10, hv0, hm1C, hr, hs⟩

/-- **Deterministic closeness** of the dressed inverse to `diag(R, aI)` from `|m_i - a| ≤ A_i`. -/
theorem dressedInv_close {b E κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hW : 1 ≤ W) (N : LayerMat W) (m₁ m₂ : ℂ) {CD A₁ A₂ : ℝ} (hCD : 0 ≤ CD) (hNn : ‖N‖ ≤ CD)
    (eA' : blkAt N 0 0 * (zetaOf b E m₁ m₂ • 1 - X) = 1) (hβ : boundaryZ b E - (b : ℂ) * m₁ ≠ 0)
    (e11 : blkAt N 1 1 = (boundaryZ b E - (b : ℂ) * m₁)⁻¹ • 1) (e01 : blkAt N 0 1 = 0)
    (e10 : blkAt N 1 0 = 0) (h₁ : ‖m₁ - matchedA E‖ ≤ A₁) (h₂ : ‖m₂ - matchedA E‖ ≤ A₂) :
    ‖N - meanTarget b E X‖ ≤
      CD * ((1 - 2 * b) * A₁ + b * A₂) * (etaZ b E)⁻¹ + CD * (b * A₁) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨t00, t01, t10, t11⟩ := blkAt_meanTarget b E X
  obtain ⟨-, hKR, -⟩ := passive_inverse_constructed _ _ hη hY (matrixImaginaryPart_nearPencil b E X)
  set ζ := zetaOf b E m₁ m₂
  set β := boundaryZ b E - (b : ℂ) * m₁
  have hz : boundaryZ b E - ζ = ((1 - 2 * b : ℝ) : ℂ) * (m₁ - matchedA E) +
      (b : ℂ) * (m₂ - matchedA E) := by
    rw [bulk_z_eq (b := b) hκ hE]; simp only [ζ, zetaOf]; ring
  have hzn : ‖boundaryZ b E - ζ‖ ≤ (1 - 2 * b) * A₁ + b * A₂ := by
    rw [hz]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b), Real.norm_of_nonneg hb0.le]
    exact add_le_add (mul_le_mul_of_nonneg_left h₁ (by linarith))
      (mul_le_mul_of_nonneg_left h₂ hb0.le)
  have h00 : ‖blkAt (N - meanTarget b E X) 0 0‖ ≤ CD * ((1 - 2 * b) * A₁ + b * A₂) * (etaZ b E)⁻¹ := by
    rw [blkAt_sub, t00]
    have e : blkAt N 0 0 - passiveResolvent b E X =
        blkAt N 0 0 * ((boundaryZ b E - ζ) • (1 : Matrix (Fin W) (Fin W) ℂ)) *
          passiveResolvent b E X := by
      have h3 : (boundaryZ b E - ζ) • (1 : Matrix (Fin W) (Fin W) ℂ) =
          (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) - (ζ • 1 - X) := by
        rw [sub_smul]; abel
      rw [h3, Matrix.mul_sub, Matrix.sub_mul, eA', Matrix.one_mul, Matrix.mul_assoc, passiveResolvent,
        hKR, Matrix.mul_one]
    rw [e]
    have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    refine mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans ?_) hR (norm_nonneg _)
      (mul_nonneg hCD ((norm_nonneg _).trans hzn))
    exact mul_le_mul ((norm_blkAt_le _ _ _).trans hNn) ((norm_smul_one_le _).trans hzn)
      (norm_nonneg _) hCD
  have h11 : ‖blkAt (N - meanTarget b E X) 1 1‖ ≤ CD * (b * A₁) := by
    rw [blkAt_sub, t11, e11, ← sub_smul]
    refine (norm_smul_one_le _).trans ?_
    have hβi : ‖β⁻¹‖ ≤ CD :=
      (norm_le_of_smul_one hW e11).trans ((norm_blkAt_le _ _ _).trans hNn)
    have e1 : β⁻¹ - matchedA E = β⁻¹ * (1 - β * matchedA E) := by
      rw [mul_sub, mul_one, inv_mul_cancel_left₀ hβ]
    have e2 : 1 - β * matchedA E = matchedA E * (b : ℂ) * (m₁ - matchedA E) := by
      have ha := bulk_a_mul (b := b) hκ hE
      show 1 - (boundaryZ b E - (b : ℂ) * m₁) * matchedA E = _
      linear_combination (-1 : ℂ) * ha
    rw [e1, e2, norm_mul, norm_mul, norm_mul, bulk_norm_a hκ hE, Complex.norm_real,
      Real.norm_of_nonneg hb0.le, one_mul]
    exact mul_le_mul hβi (mul_le_mul_of_nonneg_left h₁ hb0.le)
      (mul_nonneg hb0.le (norm_nonneg _)) hCD
  refine (norm_layerMat_le' _).trans ?_
  have z01 : blkAt (N - meanTarget b E X) 0 1 = 0 := by rw [blkAt_sub, e01, t01, sub_zero]
  have z10 : blkAt (N - meanTarget b E X) 1 0 = 0 := by rw [blkAt_sub, e10, t10, sub_zero]
  rw [z01, z10, norm_zero, add_zero, add_zero]
  exact add_le_add h00 h11

/-- **Identification of the mean matrix**: `m₁, m₂ = a + O(δ₀ + W⁻²)` and
`‖E𝒢 - diag(R, aI)‖ ≤ C(δ₀ + W⁻²)`, uniformly over strictly passive `X` near the jet. -/
theorem mean_identify (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖meanTr b E X 0 - matchedA E‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ∧
        ‖meanTr b E X 3 - matchedA E‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ∧
        ‖matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - meanTarget b E X‖ ≤
          C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE : E ∈ bulkInterval (min (2 + E) (2 - E)) := mem_bulkInterval_min E
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨CD, W₁, hCD, hres⟩ := mean_residuals hA hb0 hb h1 h2
  have hCv : 0 ≤ 2 * CD := by linarith
  obtain ⟨d₀, ρ, C', ε₀, hd₀, hρ0, -, hC', hε₀, hst⟩ := passiveMean_stability hb0 hb hκ hCv
  obtain ⟨K, hK0, hKdef⟩ : ∃ K : ℝ, 0 ≤ K ∧ K = (‖boundaryZ b E‖ + b * (2 * CD) + 1) * CD :=
    ⟨_, mul_nonneg (by have := norm_nonneg (boundaryZ b E); nlinarith) hCD, rfl⟩
  have he₁ : 0 < min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD)) := lt_min hε₀ (eps1_pos hb0 hb hκ hCv)
  obtain ⟨C1, hC1, hC1def⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C1 = C1c b (min (2 + E) (2 - E)) (2 * CD) :=
    ⟨_, (C1c_pos hb0 hb hκ hCv).le, rfl⟩
  have hdpos : 0 < min d₀ (b * etaLow b (min (2 + E) (2 - E)) / 2) :=
    lt_min hd₀ (div_pos (mul_pos hb0 (etaLow_pos (by linarith : b < 1) hκ)) two_pos)
  set A1c := C1 * (1 + K)
  set A2c := ρ + C' * K
  have hA1 : 0 ≤ A1c := mul_nonneg hC1 (by linarith)
  have hA2 : 0 ≤ A2c := add_nonneg hρ0 (mul_nonneg hC' hK0)
  set Cm := CD * ((1 - 2 * b) * A1c + b * A2c) * (etaZ b E)⁻¹ + CD * (b * A1c) + CD
  have hCm : 0 ≤ Cm := by
    have : 0 ≤ (1 - 2 * b) * A1c + b * A2c :=
      add_nonneg (mul_nonneg (by linarith) hA1) (mul_nonneg hb0.le hA2)
    have := inv_nonneg.mpr hη.le
    positivity
  refine ⟨min d₀ (b * etaLow b (min (2 + E) (2 - E)) / 2), A1c + A2c + Cm,
    max W₁ (⌈K / min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD))⌉₊ + 1), hdpos, by linarith,
    fun W hW X hX hδ => ?_⟩
  obtain ⟨hW1, hNn, hBN, eA', hβ, e11, e01, e10, hv0, hm1C, hr, hs⟩ :=
    hres W (le_trans (le_max_left _ _) hW) X hX
  set δ := jetDistance0 b E X
  set w := (W : ℝ)⁻¹ ^ 2
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hw0 : 0 ≤ w := by positivity
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  -- the residual size `ε = K w ≤ ε₁`
  have hK1 : 1 ≤ ‖boundaryZ b E‖ + b * (2 * CD) + 1 := by
    have := norm_nonneg (boundaryZ b E); have := mul_nonneg hb0.le hCv; linarith
  have hCDK : CD ≤ K := by rw [hKdef]; exact le_mul_of_one_le_left hCD hK1
  have hrK : ‖meanTr b E X 0 - stieltjes X (zetaOf b E (meanTr b E X 0) (meanTr b E X 3))‖ ≤
      K * w := hr.trans (mul_le_mul_of_nonneg_right hCDK hw0)
  have hsK' : (‖boundaryZ b E‖ + b * (2 * CD)) * (CD * w) ≤ K * w := by
    rw [hKdef, mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hCD hw0)
  have hsK : ‖meanTr b E X 3 * (boundaryZ b E - (b : ℂ) * meanTr b E X 0) - 1‖ ≤ K * w :=
    hs.trans hsK'
  have hεe : K * w ≤ min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD)) := by
    have hc : K / min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD)) < W := by
      have := Nat.le_ceil (K / min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD)))
      have : ((⌈K / min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD))⌉₊ + 1 : ℕ) : ℝ) ≤ W := by
        exact_mod_cast le_trans (le_max_right _ _) hW
      push_cast at this; linarith
    have h2' : w ≤ (W : ℝ)⁻¹ := by
      have h0 : 0 ≤ (W : ℝ)⁻¹ := by positivity
      have := inv_le_one_of_one_le₀ hWr
      simp only [w]; nlinarith
    have : K * (W : ℝ)⁻¹ ≤ min ε₀ (eps1 b (min (2 + E) (2 - E)) (2 * CD)) := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]
      rw [div_lt_iff₀ he₁] at hc; linarith
    exact (mul_le_mul_of_nonneg_left h2' hK0).trans this
  have hu := hst W E hE X hX.posSemidef _ _ (K * w) hv0 hm1C hsK hrK (mul_nonneg hK0 hw0)
    (hεe.trans (min_le_left _ _)) (hδ.trans (min_le_left _ _))
  obtain ⟨-, hv⟩ := mean_stage_one hb0 hb hκ hE hCv hX.posSemidef hv0 hm1C hsK hrK
    (mul_nonneg hK0 hw0) (hεe.trans (min_le_right _ _)) le_rfl (hδ.trans (min_le_right _ _))
  rw [← hC1def] at hv
  have hv' : ‖meanTr b E X 0 - matchedA E‖ ≤ A1c * (δ + w) := hv.trans (by
    have : K * w ≤ K * (δ + w) := mul_le_mul_of_nonneg_left (by linarith) hK0
    calc C1 * (δ + K * w) ≤ C1 * ((δ + w) + K * (δ + w)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC1
      _ = A1c * (δ + w) := by ring)
  have hu' : ‖meanTr b E X 3 - matchedA E‖ ≤ A2c * (δ + w) := hu.trans (by
    calc ρ * δ + C' * (K * w) ≤ ρ * (δ + w) + C' * (K * (δ + w)) :=
          add_le_add (mul_le_mul_of_nonneg_left (by linarith) hρ0)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hK0) hC')
      _ = A2c * (δ + w) := by ring)
  have hNT := dressedInv_close hb0 hb hκ hE hX.posSemidef hW1 _ _ _ hCD hNn eA' hβ e11 e01 e10
    hv' hu'
  have hτ : 0 ≤ δ + w := by linarith
  have hBT : ‖matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X) - meanTarget b E X‖ ≤
      Cm * (δ + w) := by
    refine (norm_sub_le_norm_sub_add_norm_sub _ ((dressed b E X)⁻¹) _).trans ?_
    have hB : CD * w ≤ CD * (δ + w) := mul_le_mul_of_nonneg_left (by linarith) hCD
    calc _ ≤ CD * (δ + w) + (CD * ((1 - 2 * b) * (A1c * (δ + w)) + b * (A2c * (δ + w))) *
          (etaZ b E)⁻¹ + CD * (b * (A1c * (δ + w)))) := add_le_add (hBN.trans hB) hNT
      _ = Cm * (δ + w) := by ring
  refine ⟨hv'.trans ?_, hu'.trans ?_, hBT.trans ?_⟩ <;>
    exact mul_le_mul_of_nonneg_right (by linarith) hτ

end BlockBand.Transmission.PassiveCovariance
