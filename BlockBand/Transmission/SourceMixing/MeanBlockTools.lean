module

public import BlockBand.Transmission.SourceMixing.PassiveMeanBlock

/-!
# Block tools for the scalar mean systems

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`), operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E`
(and `L_w, K_d`) only, uniformly in `W ≥ W₀`, `X`.

Block decompositions of the dressed resolvent and its mean, used to derive the scalar mean
equations.

* `mOf = blkAt D⁻¹ 0 0` (`= M = (ζ - X)⁻¹`), `vOf = (z - bm₁)⁻¹` (`= v`);
* `dressedBlocks`: `D⁻¹ = diag(M, vI)` acts blockwise, `‖M‖, |v| ≤ C`,
  `E𝒢 = diag(M, vI) + O(W⁻²)` blockwise, `(ζ - X)M = M(ζ - X) = 1`;
* `unweightedExpansion`: `‖E[𝒢w] - D⁻¹(E w + Σ_j 𝒮[E𝒢α_j]Eγ_j)‖ ≤ C/W²` (from `meanExpansion`);
* block algebra of `P₂·`, `𝒮·`, scalar multiples and normalized traces.
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

/-- `M = blkAt D⁻¹ 0 0`. -/
def mOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  blkAt (dressed b E X)⁻¹ 0 0

/-- `v = (z - bm₁)⁻¹`. -/
def vOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (boundaryZ b E - (b : ℂ) * meanTr b E X 0)⁻¹

/-- `ζ = -E - cm₁ - bm₂`. -/
abbrev zetaX (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  zetaOf b E (meanTr b E X 0) (meanTr b E X 3)

theorem blkAt_smul (c : ℂ) (M : LayerMat W) (r s : Fin 2) : blkAt (c • M) r s = c • blkAt M r s := by
  ext x y; rfl

theorem blkAt_portProj_mul_one (M : LayerMat W) : blkAt (pTwo * M) 1 1 = blkAt M 1 1 := by
  rw [blkAt_mul, Fin.sum_univ_two, blkAt_portProj, blkAt_portProj]
  simp

theorem blkAt_selfEnergy_mul (b : ℝ) (m₁ m₂ : ℂ) (N : LayerMat W) :
    blkAt (selfEnergy b m₁ m₂ * N) 0 0 = (((1 - 2 * b : ℝ) : ℂ) * m₁ + (b : ℂ) * m₂) • blkAt N 0 0 ∧
      blkAt (selfEnergy b m₁ m₂ * N) 1 1 = ((b : ℂ) * m₁) • blkAt N 1 1 := by
  have h10 : blkAt (selfEnergy b m₁ m₂ : LayerMat W) 1 0 = 0 := by
    ext x y; simp [blkAt, siteOf, selfEnergy]
  have h11 : blkAt (selfEnergy b m₁ m₂ : LayerMat W) 1 1 = ((b : ℂ) * m₁) • 1 := by
    ext x y; simp [blkAt, siteOf, selfEnergy, Matrix.diagonal_apply, Matrix.one_apply]
  obtain ⟨h00, h01⟩ := blkAt_selfEnergy (W := W) b m₁ m₂
  constructor
  · rw [blkAt_mul, Fin.sum_univ_two, h00, h01, Matrix.zero_mul, add_zero, Matrix.smul_mul,
      Matrix.one_mul]
  · rw [blkAt_mul, Fin.sum_univ_two, h10, h11, Matrix.zero_mul, zero_add, Matrix.smul_mul,
      Matrix.one_mul]

theorem blkTr_def (F : LayerMat W) (r : Fin 2) : blkTr F r = (W : ℂ)⁻¹ * (blkAt F r r).trace := rfl

/-- `|⟨F⟩_r - W⁻¹Tr B| ≤ ‖F_rr - B‖`. -/
theorem norm_blkTr_sub_le (F : LayerMat W) (r : Fin 2) (B : Matrix (Fin W) (Fin W) ℂ) :
    ‖blkTr F r - (W : ℂ)⁻¹ * B.trace‖ ≤ ‖blkAt F r r - B‖ := by
  rw [blkTr_def, ← mul_sub, ← trace_sub]; exact PassiveCovariance.norm_normTrace_le _

theorem normTrace_smul_one (hW : 1 ≤ W) (c : ℂ) :
    (W : ℂ)⁻¹ * (c • (1 : Matrix (Fin W) (Fin W) ℂ)).trace = c := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]; field_simp

theorem div_sq_eq (C : ℝ) : C * (W : ℝ)⁻¹ ^ 2 = C / (W : ℝ) ^ 2 := by
  rw [div_eq_mul_inv, inv_pow]

/-- `D⁻¹ = diag(M, vI)` and `E𝒢 = D⁻¹ + O(W⁻²)` blockwise. -/
theorem dressedBlocks (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (CD : ℝ) (W₀ : ℕ), 0 ≤ CD ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        1 ≤ W ∧ ‖(dressed b E X)⁻¹‖ ≤ CD ∧ ‖mOf b E X‖ ≤ CD ∧ ‖vOf b E X‖ ≤ CD ∧
        (∀ N : LayerMat W, blkAt ((dressed b E X)⁻¹ * N) 0 0 = mOf b E X * blkAt N 0 0) ∧
        (∀ N : LayerMat W, blkAt ((dressed b E X)⁻¹ * N) 1 1 = vOf b E X • blkAt N 1 1) ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
          CD / (W : ℝ) ^ 2 ∧
        ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
          vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2 ∧
        (∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort)) ∧
        (zetaX b E X • 1 - X) * mOf b E X = 1 ∧ mOf b E X * (zetaX b E X • 1 - X) = 1 := by
  obtain ⟨CD, W₁, hCD, hres⟩ := mean_residuals hA hb0 hb h1 h2
  obtain ⟨_, Wt, _, hcov⟩ := traceCov_op hA hb0 hb h1 h2
  obtain ⟨_, WD, hDI⟩ := dressed_inverse hA hb0 hb h1 h2
  refine ⟨CD, max (max W₁ Wt) WD, hCD, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWt⟩, hWD⟩ := hW
  obtain ⟨hU, -, -⟩ := hDI W hWD X hX
  obtain ⟨hW1, hDn, hDc, hMz, -, e11, e01, e10, -⟩ := hres W hW₁ X hX
  have hG := (hcov W hWt X hX.posSemidef 0).2.1
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

/-- The unweighted expansion `E[𝒢w] = D⁻¹(E w + Σ_j 𝒮_j Eγ_j) + O(W⁻²)`. -/
theorem unweightedExpansion (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (Lw : ℕ) (Kd : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ ℓ : ℕ, ℓ ≤ Lw → ∀ (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W),
      (∀ j, ‖D j‖ ≤ Kd) →
        ‖matrixExpect (layerLaw W b .oneBlockOnePort)
            (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) wd D) -
          (dressed b E X)⁻¹ *
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
  obtain ⟨hU, hDn, -, -⟩ := hK W (le_trans (le_max_right _ _) hW) X hX
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
  have e : T - (dressed b E X)⁻¹ * R = (dressed b E X)⁻¹ * (dressed b E X * T - R) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hDinvD, Matrix.one_mul]
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
  calc _ ≤ ‖(dressed b E X)⁻¹‖ * ‖dressed b E X * T - R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ CK * (Ce / (W : ℝ) ^ 2) := mul_le_mul hDn he' (norm_nonneg _) hCK
    _ = _ := by ring

end BlockBand.Transmission.SourceMixing
