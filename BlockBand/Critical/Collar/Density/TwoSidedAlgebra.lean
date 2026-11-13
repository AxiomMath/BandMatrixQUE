module

public import BlockBand.Critical.Collar.Density.RegularBound

/-!
# Two-sided conditional comparison on the regular event

Deterministic; no measure. Common-port layer sample `ω = (A, B)`, Hermitian `A_j`, `X`, `|e| < 2`.

* `conjTranspose_sub_smul_mul_self`: `(F - z)ᴴ(F - z) = (F - Re z)² + (Im z)²` (Hermitian `F`).
* `zeroHeightOperator_eq`, `freshGamma_eq_zeroHeight`: `Γ_F(0)` and the certificate's
  zero-height operator are the same Gram inverse.
* `abs_sub_le_of_two_sided`: scalar combination of two relative comparisons.
* `quadForm_condCollarDensity_two_sided`: from the relative density bounds of `Σ_F(0)`
  (`relativeMatrixDensity`, error `ε`) and the certificate bounds at `μ = ā`
  (`Palm.certificate_full_uniform`, constant `C_c`, defect `χ = |W⁻¹Tr 𝒢_port - a|`),
  `|q*K_XTΣ_F(0)T*K_X*q - ρ(E)c‖L*q‖²| ≤ (C_cχ/π + ε + (π⁻¹ + C_cχ/π + ε)C_cχ)c‖L*q‖²`
  (the sharp conditional collar comparison, with `Γ_F(0) ≈ cHH*`, `L = K_XTH`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `(F - z)ᴴ(F - z) = (F - Re z)² + (Im z)²` for Hermitian `F`. -/
theorem conjTranspose_sub_smul_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (z : ℂ) :
    (F - z • (1 : Matrix ι ι ℂ))ᴴ * (F - z • 1) =
      (F - ((z.re : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) ^ 2 + (((z.im ^ 2 : ℝ)) : ℂ) • 1 := by
  rw [conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one, sq]
  have h1 : star z + z = 2 * ((z.re : ℝ) : ℂ) := by
    rw [Complex.star_def, add_comm, Complex.add_conj]; push_cast; ring
  have h2 : star z * z = ((z.re : ℝ) : ℂ) ^ 2 + (((z.im ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_apply]; push_cast; ring
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  linear_combination (norm := module) h1 • (-F) + h2 • (1 : Matrix ι ι ℂ)

/-- The zero-height operator of the certificate as a Gram inverse. -/
theorem zeroHeightOperator_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Matrix ι ι ℂ}
    (hF : F.IsHermitian) (c : ℝ) (μ z : ℂ) (hre : z.re = 0 + c * μ.re)
    (him : z.im ^ 2 = (c * μ.im) ^ 2) :
    BlockBand.Palm.zeroHeightOperator F 0 c μ.re μ.im =
      (c : ℂ) • ((F - z • (1 : Matrix ι ι ℂ))ᴴ * (F - z • 1))⁻¹ := by
  rw [conjTranspose_sub_smul_mul_self hF z, hre, him]
  rfl

/-- `Γ_F(0) = zeroHeightOperator F 0 c (Re m) (Im m)`, `m = m_{F,c}(0)`. -/
theorem freshGamma_eq_zeroHeight {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (c : ℝ) :
    freshGamma F c 0 = BlockBand.Palm.zeroHeightOperator F 0 c (freshDyson F c ((0 : ℝ) : ℂ)).re
      (freshDyson F c ((0 : ℝ) : ℂ)).im := by
  rw [zeroHeightOperator_eq hF c (freshDyson F c ((0 : ℝ) : ℂ))
    (((0 : ℝ) : ℂ) + (c : ℂ) * freshDyson F c ((0 : ℝ) : ℂ)) (by simp) (by simp)]
  rfl

/-- Scalar combination of the two relative comparisons. -/
theorem abs_sub_le_of_two_sided {S g z0 r ρ₀ ε χ δr : ℝ} (hz0 : 0 ≤ z0) (hχ : 0 ≤ χ)
    (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hρ₀ : 0 ≤ ρ₀) (hδr : |r - ρ₀| ≤ δr)
    (hg1 : (1 - χ) * z0 ≤ g) (hg2 : g ≤ (1 + χ) * z0)
    (hS1 : (r - ε) * g ≤ S) (hS2 : S ≤ (r + ε) * g) :
    |S - ρ₀ * z0| ≤ (δr + ε + (ρ₀ + δr + ε) * χ) * z0 := by
  have hr := abs_le.1 hδr
  rw [abs_le]
  constructor
  · rcases le_or_gt 0 (r - ε) with h | h
    · have h1 : (r - ε) * ((1 - χ) * z0) ≤ (r - ε) * g := mul_le_mul_of_nonneg_left hg1 h
      have h2 : (r - ε) * χ * z0 ≤ (ρ₀ + δr + ε) * χ * z0 := by
        have : r - ε ≤ ρ₀ + δr + ε := by linarith
        have := mul_le_mul_of_nonneg_right this (mul_nonneg hχ hz0)
        nlinarith
      nlinarith
    · have h1 : (r - ε) * ((1 + χ) * z0) ≤ (r - ε) * g :=
        mul_le_mul_of_nonpos_left hg2 h.le
      have h2 : -ε * χ * z0 ≤ (r - ε) * χ * z0 := by
        have := mul_le_mul_of_nonneg_right (show -ε ≤ r - ε by linarith) (mul_nonneg hχ hz0)
        nlinarith
      have h3 : 0 ≤ (ρ₀ + δr) * χ * z0 := by
        have : 0 ≤ δr := (abs_nonneg _).trans hδr
        positivity
      nlinarith
  · have h1 : (r + ε) * g ≤ (r + ε) * ((1 + χ) * z0) :=
      mul_le_mul_of_nonneg_left hg2 (by linarith)
    have h2 : (r + ε) * (χ * z0) ≤ (ρ₀ + δr + ε) * (χ * z0) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hχ hz0)
    nlinarith

/-- `((F - w)ᴴ(F - w))⁻¹ = H Hᴴ`, `H = (F - w)⁻¹`. -/
theorem inv_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    (Mᴴ * M)⁻¹ = M⁻¹ * (M⁻¹)ᴴ := by
  rw [Matrix.mul_inv_rev, conjTranspose_nonsing_inv]

/-- **Pointwise two-sided conditional comparison on the regular event**:
with the relative density bounds of `Σ_F(0)` (`relativeMatrixDensity`, error `ε`) and the
certificate bounds (`Palm.certificate_full_uniform` at `μ = ā`, constant `C_c`, defect `χ`),
`|q*K_X T Σ_F(0) T* K_X* q - ρ(E) c ‖L*q‖²| ≤ (C_cχ/π + ε + (π⁻¹ + C_cχ/π + ε)C_cχ) c ‖L*q‖²`,
`ρ(E) = Im ā / π`, `c = 1 - 2b`. -/
theorem quadForm_condCollarDensity_two_sided (hW : 0 < W) {b e : ℝ} (hb : b < 1 / 2)
    (he : |e| < 2) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian)
    (hD : IsUnit (collarTopBlock e X ω).det) {ε : ℝ} (hε : 0 ≤ ε)
    (hrel : (((ε : ℝ) : ℂ) • freshGamma (collarFW e X ω) (1 - 2 * b) 0 -
        relativeDeviation (collarFW e X ω) (1 - 2 * b) 0
          (sigma (collarFW e X ω) (1 - 2 * b) 0)).PosSemidef ∧
      (relativeDeviation (collarFW e X ω) (1 - 2 * b) 0 (sigma (collarFW e X ω) (1 - 2 * b) 0) +
        ((ε : ℝ) : ℂ) • freshGamma (collarFW e X ω) (1 - 2 * b) 0).PosSemidef)
    {Cc : ℝ} (hCc : 0 ≤ Cc)
    (hm : ‖BlockBand.Palm.certificateCanonicalDyson
        (collarFW_isHermitian e hX hA).eigenvalues (1 - 2 * b) ((0 : ℝ) : ℂ) -
          star (matchedA e)‖ ≤
        Cc * ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0 (star (matchedA e))‖)
    (hZ1 : (BlockBand.Palm.zeroHeightOperator (collarFW e X ω) 0 (1 - 2 * b)
        (BlockBand.Palm.certificateCanonicalDyson
          (collarFW_isHermitian e hX hA).eigenvalues (1 - 2 * b) ((0 : ℝ) : ℂ)).re
        (BlockBand.Palm.certificateCanonicalDyson
          (collarFW_isHermitian e hX hA).eigenvalues (1 - 2 * b) ((0 : ℝ) : ℂ)).im -
      ((1 - Cc * ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0
          (star (matchedA e))‖ : ℝ) : ℂ) •
        BlockBand.Palm.zeroHeightOperator (collarFW e X ω) 0 (1 - 2 * b)
          (star (matchedA e)).re (star (matchedA e)).im).PosSemidef)
    (hZ2 : (((1 + Cc * ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0
          (star (matchedA e))‖ : ℝ) : ℂ) •
        BlockBand.Palm.zeroHeightOperator (collarFW e X ω) 0 (1 - 2 * b)
          (star (matchedA e)).re (star (matchedA e)).im -
      BlockBand.Palm.zeroHeightOperator (collarFW e X ω) 0 (1 - 2 * b)
        (BlockBand.Palm.certificateCanonicalDyson
          (collarFW_isHermitian e hX hA).eigenvalues (1 - 2 * b) ((0 : ℝ) : ℂ)).re
        (BlockBand.Palm.certificateCanonicalDyson
          (collarFW_isHermitian e hX hA).eigenvalues (1 - 2 * b) ((0 : ℝ) : ℂ)).im).PosSemidef)
    (hm0 : 0 ≤ (BlockBand.Palm.certificateCanonicalDyson
        (collarFW_isHermitian e hX hA).eigenvalues (1 - 2 * b) ((0 : ℝ) : ℂ)).im)
    (q : Fin 2 × Fin W → ℂ) :
    |quadForm (matchedLeadK b e X * condCollarDensity b e X ω * (matchedLeadK b e X)ᴴ) q -
        (star (matchedA e)).im / Real.pi *
          ((1 - 2 * b) * ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2)| ≤
      (Cc * ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0 (star (matchedA e))‖ /
          Real.pi + ε + (Real.pi⁻¹ + Cc * ‖BlockBand.Palm.certificateChi (collarFW e X ω)
            (1 - 2 * b) 0 (star (matchedA e))‖ / Real.pi + ε) *
          (Cc * ‖BlockBand.Palm.certificateChi (collarFW e X ω) (1 - 2 * b) 0
            (star (matchedA e))‖)) *
        ((1 - 2 * b) * ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hF := collarFW_isHermitian e hX hA
  set F := collarFW e X ω with hFdef
  set c : ℝ := 1 - 2 * b with hcdef
  set χ := ‖BlockBand.Palm.certificateChi F c 0 (star (matchedA e))‖ with hχdef
  set mc := BlockBand.Palm.certificateCanonicalDyson hF.eigenvalues c ((0 : ℝ) : ℂ) with hmcdef
  set μ := star (matchedA e) with hμdef
  have hmm : freshDyson F c ((0 : ℝ) : ℂ) = mc :=
    BlockBand.Palm.CoarseRelative.freshDyson_eq_certificate hF hW hc (by simp)
  set w := collarShiftW b e with hwdef
  have hw_eq : w = (c : ℂ) * matchedA e := collarShiftW_eq he.le
  have hwim : w.im < 0 := by
    rw [hw_eq]
    have := BlockBand.Layers.matchedA_im_neg he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hc this
  set Hw := (F - w • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹ with hHw
  set K := matchedLeadK b e X
  set T := collarTW e X ω
  set u : Fin W → ℂ := Tᴴ *ᵥ (Kᴴ *ᵥ q) with hu
  set Q := ∑ a, ‖((commonPortL b e X ω)ᴴ *ᵥ q) a‖ ^ 2 with hQ
  -- the form of the conditional density
  have hf : quadForm (K * condCollarDensity b e X ω * Kᴴ) q =
      quadForm (sigma F c 0) u := by
    have h1 : K * condCollarDensity b e X ω * Kᴴ =
        (Tᴴ * Kᴴ)ᴴ * sigma F c 0 * (Tᴴ * Kᴴ) := by
      simp only [condCollarDensity, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    rw [h1, quadForm_conjTranspose_mul_mul, ← mulVec_mulVec]
  -- the leading Gram form
  have hZμ : BlockBand.Palm.zeroHeightOperator F 0 c μ.re μ.im = (c : ℂ) • (Hw * Hwᴴ) := by
    rw [zeroHeightOperator_eq hF c μ w (by rw [hw_eq, hμdef]; simp) (by
      rw [hw_eq, hμdef]; simp), inv_conjTranspose_mul_self]
  have hS := isUnit_det_collarF_sub (b := b) hX hA hwim
  have hz0 : quadForm (BlockBand.Palm.zeroHeightOperator F 0 c μ.re μ.im) u = c * Q := by
    rw [hZμ, quadForm_real_smul]
    congr 1
    have h1 : Hw * Hwᴴ = (Hwᴴ)ᴴ * 1 * Hwᴴ := by rw [conjTranspose_conjTranspose, Matrix.mul_one]
    rw [h1, quadForm_conjTranspose_mul_mul, quadForm_one, hu, mulVec_mulVec, mulVec_mulVec]
    have h2 : Hwᴴ * Tᴴ * Kᴴ = (K * T * Hw)ᴴ := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [h2, show K * T * Hw = (commonPortL b e X ω).submatrix id (portEquiv W).symm from
      commonPortL_submatrix_eq b e X ω hD hS, sum_norm_sq_conjTranspose_submatrix]
  -- the comparisons
  have hΓ : freshGamma F c 0 = BlockBand.Palm.zeroHeightOperator F 0 c mc.re mc.im := by
    rw [freshGamma_eq_zeroHeight hF c, hmm]
  set g := quadForm (freshGamma F c 0) u with hg
  have hg1 : (1 - Cc * χ) * (c * Q) ≤ g := by
    have := quadForm_nonneg_of_posSemidef hZ1 u
    rw [quadForm_sub, quadForm_real_smul, ← hΓ, hz0] at this
    linarith
  have hg2 : g ≤ (1 + Cc * χ) * (c * Q) := by
    have := quadForm_nonneg_of_posSemidef hZ2 u
    rw [quadForm_sub, quadForm_real_smul, ← hΓ, hz0] at this
    linarith
  set r := (freshDyson F c ((0 : ℝ) : ℂ)).im / Real.pi with hr
  have hS1 : (r - ε) * g ≤ quadForm (sigma F c 0) u := by
    have := quadForm_nonneg_of_posSemidef hrel.2 u
    rw [quadForm_add, relativeDeviation, quadForm_sub, quadForm_real_smul,
      quadForm_real_smul] at this
    simp only [← hr] at this
    linarith
  have hS2 : quadForm (sigma F c 0) u ≤ (r + ε) * g := by
    have := quadForm_nonneg_of_posSemidef hrel.1 u
    rw [quadForm_sub, relativeDeviation, quadForm_sub, quadForm_real_smul,
      quadForm_real_smul] at this
    simp only [← hr] at this
    linarith
  have hpi := Real.pi_pos
  have hr0 : 0 ≤ r := by rw [hr, hmm]; positivity
  have hμim : 0 ≤ μ.im := by
    rw [hμdef, Complex.star_def, Complex.conj_im]
    linarith [BlockBand.Layers.matchedA_im_neg he]
  have hμ1 : μ.im ≤ 1 := by
    have := Complex.abs_im_le_norm μ
    rw [hμdef, norm_star, BlockBand.Layers.norm_matchedA he.le] at this
    linarith [le_abs_self μ.im]
  have hδr : |r - μ.im / Real.pi| ≤ Cc * χ / Real.pi := by
    rw [hr, hmm, ← sub_div, abs_div, abs_of_pos hpi]
    gcongr
    calc |mc.im - μ.im| = |(mc - μ).im| := by rw [Complex.sub_im]
      _ ≤ ‖mc - μ‖ := Complex.abs_im_le_norm _
      _ ≤ Cc * χ := hm
  have hQ0 : 0 ≤ Q := by positivity
  have hz00 : 0 ≤ c * Q := by positivity
  have hχ0 : 0 ≤ Cc * χ := by positivity
  have key := abs_sub_le_of_two_sided hz00 hχ0 hε hr0 (div_nonneg hμim hpi.le) hδr hg1 hg2 hS1 hS2
  rw [hf]
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have : μ.im / Real.pi ≤ Real.pi⁻¹ := by
    rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (inv_nonneg.2 hpi.le) hμ1
  gcongr

end BlockBand.Critical.Collar.Density
