module

public import BlockBand.Layers.CompensatedCore

/-!
# Uniform inverse moments along the heat interpolation

The inverse moments in the proof of the compensated-phase lemma: "For `t ≥ 1/2` the proof of the
Gaussian absorption lemma applies at variances `tc, tb`; the extra nonnegative top height can only
improve its imaginary quadratic-form estimate. For `t ≤ 1/2` the deterministic heights are bounded
below." This is done for the four heat matrices of `CompensatedHeat` and `CompensatedCore`
(`chtHeat` with `β ∈ [0, 2b]`, `chtCoreHeat1`, `chtCoreHeat2`).

Law: the Gaussian coordinates of the layer (`gaussianProduct (tflVar W b σ)`, image `layerLaw`)
resp. of the two-block core (`gaussianProduct (coreVar W b)`, image `coreLaw2`). Domain:
`b ∈ (0, 1/2)`, `E ∈ bulkInterval κ`, `t ∈ [0, 1)`, every Hermitian `X`, `W ≥ W₀`. Norm: `ℓ²`
operator norm; `L⁴` in the coordinates.

* §1 `hms_inv_dissip` (deterministic): if `‖K⁻¹‖ ≤ R` and `‖Δ v‖² ≤ η Im⟨v, (K + Δ) v⟩`, then
  `‖(K + Δ)⁻¹‖ ≤ 2R + ηR² + 1`. (Note: `‖(K + iηP)⁻¹‖ ≤ ‖K⁻¹‖` is false for a non-scalar
  projection `P`; the quadratic loss is harmless.)
* §2 the block form `hmsBlk` of the heat matrices (`hms_heat_blk`, `hms_core1_blk`,
  `hms_core2_blk`), the rescaling `ℋ = √t (K + iηP_top)` with `K` a layer matrix at
  `(E', z', X') = (-Re w/√t, z/√t, X/√t)` (`hms_blk_rescale`), the pointwise bound
  `‖ℋ⁻¹‖ ≤ 4(1 + ‖K⁻¹‖²)` for `√t ≥ 1/2` (`hms_blk_inv_le`) and the deterministic heights
  (`hms_blk_coercive`).
* §3 **`hms_layer_moments`, `hms_core1_moments`, `hms_core2_moments`**: there are `C_A, W₀`
  (depending on `b, κ` and the PSSS constant only) with `‖‖ℋ_t⁻¹‖‖_{L⁴} ≤ C_A` for all
  `t ∈ [0, 1)`; for `t ≥ 1/2` from `GaussianAbsorptionContract` (`gaussianAbsorption_holds`) at
  `p = 8`, `η₀ = (1-2b)α₀`, `M = 4`; for `t < 1/2` from the heights `≥ min(α₀/4, (1-2b)α₀)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. Dissipative perturbations
-/

section Dissip

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Scalar step: `x ≤ R y + R p`, `p² ≤ η x y` give `x ≤ (2R + ηR²) y`. -/
theorem hms_scalar_dissip {x y p R η : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hη : 0 ≤ η) (h1 : x ≤ R * y + R * p) (h2 : p ^ 2 ≤ η * x * y) :
    x ≤ (2 * R + η * R ^ 2) * y := by
  have hq : 0 ≤ x / 2 + R ^ 2 * η * y / 2 := by positivity
  have hRp : R * p ≤ x / 2 + R ^ 2 * η * y / 2 := by
    by_contra hc
    rw [not_le] at hc
    have e1 : (x / 2 + R ^ 2 * η * y / 2) ^ 2 < (R * p) ^ 2 := by
      exact pow_lt_pow_left₀ hc hq two_ne_zero
    have e2 : (R * p) ^ 2 ≤ R ^ 2 * (η * x * y) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg R)
    nlinarith [sq_nonneg (x / 2 - R ^ 2 * η * y / 2)]
  nlinarith

/-- **Dissipative perturbation of an invertible matrix.** If `‖K⁻¹‖ ≤ R` and the perturbation
`Δ` satisfies `‖Δ v‖² ≤ η Im⟨v, (K + Δ) v⟩` for every `v` (e.g. `Δ = iη P` with `P` an orthogonal
projection and `Im⟨v, K v⟩ ≥ 0`), then `K + Δ` is invertible and `‖(K + Δ)⁻¹‖ ≤ 2R + ηR² + 1`. -/
theorem hms_inv_dissip {K Δ : Matrix n n ℂ} (hK : IsUnit K.det) {R η : ℝ} (hR : ‖K⁻¹‖ ≤ R)
    (hη : 0 ≤ η) (hdis : ∀ v, cplSq (Δ *ᵥ v) ≤ η * cplForm (K + Δ) v) :
    IsUnit (K + Δ).det ∧ ‖(K + Δ)⁻¹‖ ≤ 2 * R + η * R ^ 2 + 1 := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hc : 0 < (2 * R + η * R ^ 2 + 1)⁻¹ := by positivity
  have h := isUnit_det_and_norm_inv_le_of_lower (T := K + Δ) hc fun ξ => ?_
  · rw [inv_inv] at h; exact h
  set v : n → ℂ := ofLp ξ with hv
  have hξ : ξ = toLp 2 v := rfl
  set M := K + Δ with hM
  set x := ‖ξ‖
  set y := ‖toEuclideanLin M ξ‖
  have hy : toEuclideanLin M ξ = toLp 2 (M *ᵥ v) := by rw [hξ, toLpLin_apply]
  set p := ‖(toLp 2 (Δ *ᵥ v) : EuclideanSpace ℂ n)‖ with hp
  -- `x ≤ R ‖K v‖`
  have hKv : v = K⁻¹ *ᵥ (K *ᵥ v) := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hK, one_mulVec]
  have h1 : x ≤ R * ‖(toLp 2 (K *ᵥ v) : EuclideanSpace ℂ n)‖ := by
    have := norm_toLp_mulVec_le K⁻¹ (K *ᵥ v)
    rw [← hKv] at this
    exact this.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have h2 : ‖(toLp 2 (K *ᵥ v) : EuclideanSpace ℂ n)‖ ≤ y + p := by
    have e : (toLp 2 (K *ᵥ v) : EuclideanSpace ℂ n) = toLp 2 (M *ᵥ v) - toLp 2 (Δ *ᵥ v) := by
      rw [← WithLp.toLp_sub, hM, add_mulVec, add_sub_cancel_right]
    rw [e, ← hy]
    exact norm_sub_le _ _
  have h3 : cplForm M v ≤ x * y := by
    unfold cplForm
    have : star v ⬝ᵥ (M *ᵥ v) = ⟪ξ, toEuclideanLin M ξ⟫_ℂ := by
      rw [hy, hξ, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rw [this]
    exact (Complex.im_le_norm _).trans (norm_inner_le_norm _ _)
  have h4 : p ^ 2 ≤ η * x * y := by
    rw [hp, cpl_norm_toLp_sq]
    calc cplSq (Δ *ᵥ v) ≤ η * cplForm M v := hdis v
      _ ≤ η * (x * y) := mul_le_mul_of_nonneg_left h3 hη
      _ = η * x * y := by ring
  have hmain := hms_scalar_dissip (norm_nonneg _) (norm_nonneg _) hη
    (h1.trans (by nlinarith [mul_le_mul_of_nonneg_left h2 hR0])) h4
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (toEuclideanLin M ξ)]

end Dissip

section Blk

variable {W : ℕ} (σ : LayerShape)

/-- The block form `[[s A + w - Y, s B], [s Bᴴ, z]]` of the heat matrices. -/
def hmsBlk (s : ℝ) (w z : ℂ) (Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (s • blockDiag ω.1 + w • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - Y)
    (s • bondMatrix σ ω.2) (s • (bondMatrix σ ω.2)ᴴ) (z • 1)

/-- The projection onto the physical sites. -/
def hmsPtop : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => 0))

variable {σ}

theorem hms_blk_rescale {s : ℝ} (hs : 0 < s) (w z : ℂ) (Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) :
    hmsBlk σ s w z Y ω = s • (layerMatrix σ (-w.re / s) (z / s) (s⁻¹ • Y) ω +
      (((w.im / s : ℝ) : ℂ) * I) • hmsPtop σ) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [hmsBlk, layerMatrix, hmsPtop, ← fromBlocks_diagonal, fromBlocks_smul, fromBlocks_add,
    fromBlocks_smul]
  simp only [diagonal_zero, smul_zero, add_zero]
  congr 1
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      diagonal_apply, smul_eq_mul, Complex.real_smul]
    split_ifs
    · conv_lhs => rw [← Complex.re_add_im w]
      push_cast
      field_simp
      ring
    · push_cast; field_simp; ring
  · ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Complex.real_smul]
    split_ifs <;> field_simp

/-- `Im ⟨v, (H + diag(i d)) v⟩ = Σ d_p |v_p|²` for Hermitian `H`, real `d`. -/
theorem hms_form_herm_diag {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (d : n → ℝ) (v : n → ℂ) :
    cplForm (H + diagonal (fun p => (d p : ℂ) * I)) v = ∑ p, d p * ‖v p‖ ^ 2 := by
  have e : H + diagonal (fun p => (d p : ℂ) * I) = H - diagonal (fun p => -((d p : ℂ) * I)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, diagonal_apply]
    split_ifs <;> simp
  unfold cplForm
  rw [e, cmp_im_form H hH]
  simp

theorem hms_layerMatrix_split (E : ℝ) (z : ℂ) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (ω : LayerSample W σ) (η : ℝ) :
    layerMatrix σ E z X ω + (((η : ℝ) : ℂ) * I) • hmsPtop σ =
      fromBlocks (blockDiag ω.1 - (E : ℂ) • 1 - X) (bondMatrix σ ω.2) (bondMatrix σ ω.2)ᴴ
          ((z.re : ℂ) • 1) +
        diagonal (fun p => ((Sum.elim (fun _ => η) (fun _ => z.im) p : ℝ) : ℂ) * I) := by
  have e : (fun p => ((Sum.elim (fun _ => η) (fun _ => z.im) p : ℝ) : ℂ) * I) =
      Sum.elim (fun _ : PhysSite W σ => (η : ℂ) * I) (fun _ : PortSite W σ => (z.im : ℂ) * I) := by
    funext p; cases p <;> rfl
  rw [e, layerMatrix, hmsPtop, ← fromBlocks_diagonal, ← fromBlocks_diagonal, fromBlocks_smul,
    fromBlocks_add, fromBlocks_add]
  simp only [diagonal_zero, smul_zero, add_zero]
  congr 1
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  · ext i j
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, diagonal_apply, smul_eq_mul]
    split_ifs
    · conv_lhs => rw [← Complex.re_add_im z]
      ring
    · simp

end Blk

section Blk2
variable {W : ℕ} {σ : LayerShape}

theorem hms_inv_real_smul {n : Type} [Fintype n] [DecidableEq n] {s : ℝ} (hs : s ≠ 0)
    {M : Matrix n n ℂ} (hM : IsUnit M.det) : (s • M)⁻¹ = s⁻¹ • M⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [smul_mul_smul_comm, nonsing_inv_mul _ hM, inv_mul_cancel₀ hs, one_smul]

theorem hms_isUnit_real_smul {n : Type} [Fintype n] [DecidableEq n] {s : ℝ} (hs : s ≠ 0)
    {M : Matrix n n ℂ} (hM : IsUnit M.det) : IsUnit (s • M).det := by
  rw [← Complex.coe_smul, det_smul]
  exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs))).mul hM

/-- **Pointwise inverse bound for `t ≥ 1/4`** (`s = √t ≥ 1/2`): the extra nonnegative top height
`Im w ≤ s` costs only `‖ℋ⁻¹‖ ≤ 4(1 + ‖K⁻¹‖²)`, `K` the layer matrix at `(E', z', X')`. -/
theorem hms_blk_inv_le {s : ℝ} (hs : 1 / 2 ≤ s) {w z : ℂ} (hw0 : 0 ≤ w.im) (hws : w.im ≤ s)
    (hz : 0 ≤ z.im) {Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hY : Y.IsHermitian)
    {ω : LayerSample W σ} (hD : (blockDiag ω.1).IsHermitian)
    (hK : IsUnit (layerMatrix σ (-w.re / s) (z / s) (s⁻¹ • Y) ω).det) :
    IsUnit (hmsBlk σ s w z Y ω).det ∧
      ‖(hmsBlk σ s w z Y ω)⁻¹‖ ≤ 4 * (1 + ‖layerResolvent σ (-w.re / s) (z / s) (s⁻¹ • Y) ω‖ ^ 2) := by
  have hs0 : 0 < s := by linarith
  set K := layerMatrix σ (-w.re / s) (z / s) (s⁻¹ • Y) ω with hKdef
  set η := w.im / s with hη
  have hη0 : 0 ≤ η := div_nonneg hw0 hs0.le
  have hη1 : η ≤ 1 := (div_le_one hs0).mpr hws
  set Δ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := (((η : ℝ) : ℂ) * I) • hmsPtop σ with hΔ
  have hzs : 0 ≤ (z / s).im := by
    rw [Complex.div_ofReal_im]; exact div_nonneg hz hs0.le
  have hHh : (fromBlocks (blockDiag ω.1 - ((-w.re / s : ℝ) : ℂ) • 1 - s⁻¹ • Y) (bondMatrix σ ω.2)
      (bondMatrix σ ω.2)ᴴ (((z / s).re : ℂ) • (1 : Matrix (PortSite W σ) (PortSite W σ) ℂ))).IsHermitian := by
    refine IsHermitian.fromBlocks ((hD.sub ?_).sub ?_) rfl ?_
    · unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    · unfold IsHermitian; rw [conjTranspose_smul, hY.eq, star_trivial]
    · unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
  have hdis : ∀ v, cplSq (Δ *ᵥ v) ≤ η * cplForm (K + Δ) v := by
    intro v
    rw [hKdef, hΔ, hms_layerMatrix_split, hms_form_herm_diag hHh]
    have hΔv : ∀ p, (((((η : ℝ) : ℂ) * I) • hmsPtop σ) *ᵥ v) p =
        ((η : ℂ) * I) * (Sum.elim (fun _ => (1 : ℂ)) (fun _ => 0) p * v p) := by
      intro p
      rw [hmsPtop, smul_mulVec, Pi.smul_apply, mulVec_diagonal, smul_eq_mul]
    unfold cplSq
    simp only [hΔv, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, one_mul, zero_mul,
      mul_zero, norm_zero, norm_mul, norm_one, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hη0]
    have h1 : ∑ x : PortSite W σ, (0 : ℝ) ^ 2 = 0 := by simp
    rw [h1, add_zero, mul_add]
    have h2 : 0 ≤ η * ∑ x : PortSite W σ, (z / s).im * ‖v (Sum.inr x)‖ ^ 2 :=
      mul_nonneg hη0 (Finset.sum_nonneg fun _ _ => mul_nonneg hzs (sq_nonneg _))
    have h3 : ∑ x : PhysSite W σ, (η * 1 * ‖v (Sum.inl x)‖) ^ 2 =
        η * ∑ x : PhysSite W σ, η * ‖v (Sum.inl x)‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  obtain ⟨hU, hN⟩ := hms_inv_dissip (K := K) (Δ := Δ) hK le_rfl hη0 hdis
  have heq : hmsBlk σ s w z Y ω = s • (K + Δ) := hms_blk_rescale hs0 w z Y ω
  refine ⟨heq ▸ hms_isUnit_real_smul hs0.ne' hU, ?_⟩
  rw [heq, hms_inv_real_smul hs0.ne' hU, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs0.le)]
  set R := ‖K⁻¹‖ with hR
  have hR' : ‖layerResolvent σ (-w.re / s) (z / s) (s⁻¹ • Y) ω‖ = R := rfl
  rw [hR']
  have hsi : s⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hs0 two_pos]; linarith
  have hR0 : 0 ≤ R := norm_nonneg _
  have e1 : 2 * R + η * R ^ 2 + 1 ≤ 2 * (1 + R ^ 2) := by
    nlinarith [sq_nonneg (R - 1), mul_le_mul_of_nonneg_right hη1 (sq_nonneg R)]
  calc s⁻¹ * ‖(K + Δ)⁻¹‖ ≤ 2 * (2 * (1 + R ^ 2)) :=
        mul_le_mul hsi (hN.trans e1) (norm_nonneg _) zero_le_two
    _ = 4 * (1 + R ^ 2) := by ring

/-- **Deterministic heights**: `cplCoercive (min (Im w) (Im z))` for Hermitian blocks. -/
theorem hms_blk_coercive (s : ℝ) {w z : ℂ} (hw : 0 < w.im) (hz : 0 < z.im)
    {Y : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hY : Y.IsHermitian)
    {ω : LayerSample W σ} (hD : (blockDiag ω.1).IsHermitian) :
    cplCoercive (min w.im z.im) (hmsBlk σ s w z Y ω) := by
  have e : hmsBlk σ s w z Y ω = fromBlocks (w • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) 0 0
      (z • (1 : Matrix (PortSite W σ) (PortSite W σ) ℂ)) +
      (1 : ℝ) • fromBlocks (s • blockDiag ω.1 - Y) (s • bondMatrix σ ω.2)
        (s • (bondMatrix σ ω.2)ᴴ) 0 := by
    rw [hmsBlk, one_smul, fromBlocks_add]
    congr 1 <;> abel
  rw [e]
  refine cht_coercive_add_herm (cht_coercive_fromBlocks (lt_min hw hz)
    (cpl_coercive_mono (min_le_left _ _) cpl_coercive_scalar)
    (cpl_coercive_mono (min_le_right _ _) cpl_coercive_scalar)) ?_ 1
  refine IsHermitian.fromBlocks ?_ ?_ isHermitian_zero
  · refine IsHermitian.sub ?_ hY
    unfold IsHermitian; rw [conjTranspose_smul, hD.eq, star_trivial]
  · rw [conjTranspose_smul, star_trivial]

end Blk2

section Moments

theorem hms_moment_of_pointwise {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G R : Ω → ℝ} (hGm : AEStronglyMeasurable G μ) (hRm : AEStronglyMeasurable R μ)
    (hpt : ∀ᵐ ω ∂μ, ‖G ω‖ ≤ 4 * (1 + R ω ^ 2)) {C : ℝ} (hC : 0 ≤ C)
    (hR : eLpNorm R 8 μ ≤ ENNReal.ofReal C) :
    eLpNorm G 4 μ ≤ ENNReal.ofReal (4 * (1 + C ^ 2)) := by
  have hR2m : AEStronglyMeasurable (fun ω => R ω ^ 2) μ := hRm.pow 2
  have h1 : eLpNorm G 4 μ ≤ eLpNorm ((4 : ℝ) • fun ω => 1 + R ω ^ 2) 4 μ :=
    eLpNorm_mono_ae_real hGm (by simpa [smul_eq_mul] using hpt)
  rw [eLpNorm_const_smul] at h1
  have h2 : eLpNorm (fun ω => 1 + R ω ^ 2) 4 μ ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) 4 μ +
      eLpNorm (fun ω => R ω ^ 2) 4 μ :=
    eLpNorm_add_le (f := fun _ : Ω => (1 : ℝ)) (g := fun ω => R ω ^ 2) (by norm_num)
  have h3 : eLpNorm (fun _ : Ω => (1 : ℝ)) 4 μ = 1 := by
    rw [eLpNorm_const _ (by norm_num) (NeZero.ne μ), measure_univ, ENNReal.one_rpow, mul_one]
    simp
  have h4 : eLpNorm (fun ω => R ω ^ 2) 4 μ ≤ ENNReal.ofReal (C ^ 2) := by
    have e : (fun ω => R ω ^ 2) = fun ω => ‖R ω‖ ^ (2 : ℝ) := by
      funext ω; rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    rw [e, eLpNorm_norm_rpow R hRm two_pos]
    have e8 : (4 : ℝ≥0∞) * ENNReal.ofReal 2 = 8 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
    rw [e8]
    calc eLpNorm R 8 μ ^ (2 : ℝ) ≤ ENNReal.ofReal C ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hR (by norm_num)
      _ = ENNReal.ofReal (C ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hC (by norm_num), Real.rpow_two]
  calc eLpNorm G 4 μ ≤ ‖(4 : ℝ)‖ₑ * eLpNorm (fun ω => 1 + R ω ^ 2) 4 μ := h1
    _ ≤ ‖(4 : ℝ)‖ₑ * (1 + ENNReal.ofReal (C ^ 2)) := by
        gcongr; rw [← h3]; exact h2.trans (by rw [h3]; gcongr)
    _ = ENNReal.ofReal (4 * (1 + C ^ 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add zero_le_one (sq_nonneg _),
          ENNReal.ofReal_one, Real.enorm_eq_ofReal (by norm_num)]

variable {W : ℕ}

/-- The layer heat matrix in block form: `w = -E - (1-t)(1-b)a`, `z = a⁻¹ + tβa`. -/
theorem hms_heat_blk (σ : LayerShape) (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (β t : ℝ) (ω : LayerSample W σ) :
    chtHeat σ b E X β t ω = hmsBlk σ (Real.sqrt t)
      (-(E : ℂ) - ((1 - t : ℝ) : ℂ) * (((1 - b : ℝ) : ℂ) * matchedA E))
      ((matchedA E)⁻¹ + (t : ℂ) * ((β : ℂ) * matchedA E)) X ω := by
  rw [chtHeat, chtC0, chtC1, chtLinS, hmsBlk, fromBlocks_smul, fromBlocks_smul, fromBlocks_add,
    fromBlocks_add]
  simp only [smul_zero, add_zero, zero_add]
  congr 1
  · ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.real_smul]
    split_ifs <;> ring

theorem hms_smul_one_blocks {m p : Type} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (c : ℂ) : (c • (1 : Matrix (m ⊕ p) (m ⊕ p) ℂ)) = fromBlocks (c • 1) 0 0 (c • 1) := by
  rw [← fromBlocks_one, fromBlocks_smul]; simp only [smul_zero]

/-- The one-block core heat matrix in block form: `w = a⁻¹ + ta`, `z = a⁻¹ + tba`. -/
theorem hms_core1_blk (b E t : ℝ) (ω : LayerSample W .oneBlockTwoPorts) :
    chtCoreHeat1 b E t ω = hmsBlk .oneBlockTwoPorts (Real.sqrt t)
      ((matchedA E)⁻¹ + (t : ℂ) * matchedA E) ((matchedA E)⁻¹ + (t : ℂ) * ((b : ℂ) * matchedA E))
      0 ω := by
  rw [chtCoreHeat1, chtKC0, chtC1, chtLinS, hmsBlk, hms_smul_one_blocks, fromBlocks_smul,
    fromBlocks_smul, fromBlocks_add, fromBlocks_add]
  simp only [smul_zero, add_zero, zero_add, sub_zero]
  congr 1
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.real_smul]
    split_ifs <;> ring

/-- The two-block core heat matrix in block form, `Y = -√t coreOff β`. -/
theorem hms_core2_blk (b E t : ℝ) (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate) :
    chtCoreHeat2 b E t q = hmsBlk .separate (Real.sqrt t)
      ((matchedA E)⁻¹ + (t : ℂ) * matchedA E) ((matchedA E)⁻¹ + (t : ℂ) * ((b : ℂ) * matchedA E))
      (-(Real.sqrt t • coreOff q.1)) q.2 := by
  rw [chtCoreHeat2, chtKC0, chtC1, chtLinS, coreLb, hmsBlk, hms_smul_one_blocks, fromBlocks_add,
    fromBlocks_smul, fromBlocks_smul, fromBlocks_add, fromBlocks_add]
  simp only [smul_zero, add_zero, zero_add, sub_neg_eq_add]
  congr 1
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.real_smul]
    split_ifs <;> push_cast <;> ring
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Complex.real_smul]
    split_ifs <;> ring

end Moments

section LayerMoments

/-- Scalar bulk facts: `|a| = 1`, `a⁻¹ = ā`, `α₀ ≤ -Im a ≤ 1`. -/
theorem hms_a_facts {E α₀ : ℝ} (hE2 : |E| < 2) (ha1 : ‖matchedA E‖ = 1)
    (haim : (matchedA E).im ≤ -α₀) :
    ((matchedA E)⁻¹).im = -(matchedA E).im ∧ ‖(matchedA E)⁻¹‖ = 1 ∧ α₀ ≤ -(matchedA E).im ∧
      -(matchedA E).im ≤ 1 := by
  refine ⟨by rw [inv_matchedA hE2.le, Complex.conj_im], by rw [norm_inv, ha1, inv_one],
    by linarith, ?_⟩
  have := Complex.abs_im_le_norm (matchedA E)
  rw [ha1] at this
  linarith [neg_abs_le (matchedA E).im]

/-- `t ≥ 1/2` gives `1/2 ≤ √t ≤ 1` and `1 - t ≤ √t`. -/
theorem hms_sqrt_facts {t : ℝ} (ht : 1 / 2 ≤ t) (ht1 : t < 1) :
    1 / 2 ≤ Real.sqrt t ∧ Real.sqrt t ≤ 1 ∧ 1 - t ≤ Real.sqrt t := by
  have h1 : 1 / 2 ≤ Real.sqrt t := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  refine ⟨h1, ?_, by linarith⟩
  rw [Real.sqrt_le_one]; linarith

/-- **The two regimes of the heat inverse moments.** Either deterministic heights
`Im w, Im z ≥ δ₀ > 0`, or `s ≥ 1/2`, `0 ≤ Im w ≤ s`, `Im z ≥ 0` with the layer resolvent at
`(E', z', X') = (-Re w/s, z/s, s⁻¹ Y)` a.s. defined and `‖‖K⁻¹‖‖₈ ≤ C`. Then
`‖‖ℋ⁻¹‖‖₄ ≤ max(4(1 + C²), δ₀⁻¹)`. -/
theorem hms_blk_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℕ} {σ : LayerShape} {ℓ : Ω → LayerSample W σ}
    {Y : Ω → Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hD : ∀ x, (blockDiag (ℓ x).1).IsHermitian)
    (hY : ∀ x, (Y x).IsHermitian) {s : ℝ} {w z : ℂ}
    (hGm : AEStronglyMeasurable (fun x => ‖(hmsBlk σ s w z (Y x) (ℓ x))⁻¹‖) μ) {δ₀ C : ℝ}
    (hδ₀ : 0 < δ₀) (hC : 0 ≤ C)
    (hcase : (δ₀ ≤ w.im ∧ δ₀ ≤ z.im) ∨
      (1 / 2 ≤ s ∧ 0 ≤ w.im ∧ w.im ≤ s ∧ 0 ≤ z.im ∧
        (∀ᵐ x ∂μ, IsUnit (layerMatrix σ (-w.re / s) (z / s) (s⁻¹ • Y x) (ℓ x)).det) ∧
        AEStronglyMeasurable (fun x => ‖layerResolvent σ (-w.re / s) (z / s) (s⁻¹ • Y x) (ℓ x)‖) μ ∧
        eLpNorm (fun x => ‖layerResolvent σ (-w.re / s) (z / s) (s⁻¹ • Y x) (ℓ x)‖) 8 μ ≤
          ENNReal.ofReal C)) :
    eLpNorm (fun x => ‖(hmsBlk σ s w z (Y x) (ℓ x))⁻¹‖) 4 μ ≤
      ENNReal.ofReal (max (4 * (1 + C ^ 2)) δ₀⁻¹) := by
  rcases hcase with ⟨hwδ, hzδ⟩ | ⟨hs1, hw0, hws, hz0, hunit, hRm, hR⟩
  · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    refine (eLpNorm_le_of_ae_bound (C := δ₀⁻¹) hGm (ae_of_all _ fun x => ?_)).trans ?_
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      have hw : 0 < w.im := lt_of_lt_of_le hδ₀ hwδ
      have hz : 0 < z.im := lt_of_lt_of_le hδ₀ hzδ
      refine (cpl_coercive_inv (lt_min hw hz) (hms_blk_coercive s hw hz (hY x) (hD x))).2.trans ?_
      exact inv_anti₀ hδ₀ (le_min hwδ hzδ)
    · rw [measure_univ, ENNReal.one_rpow, one_mul]
  · refine le_trans ?_ (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    refine hms_moment_of_pointwise hGm hRm ?_ hC hR
    filter_upwards [hunit] with x hx
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (hms_blk_inv_le hs1 hw0 hws hz0 (hY x) (hD x) hx).2

/-- The contract parameters on the bulk: `α₀`, then `ε₁, C` of `GaussianAbsorptionContract` at
`η₀ = (1-2b)α₀`, `M = 4`. -/
theorem hms_contract_setup (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ α₀ ε₁ C : ℝ, 0 < α₀ ∧ 0 < ε₁ ∧ 0 < C ∧
      (∀ E ∈ bulkInterval κ, |E| < 2 ∧ ‖matchedA E‖ = 1 ∧ (matchedA E).im ≤ -α₀) ∧
      ∀ (W : ℕ), 0 < W → ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ),
        X.IsHermitian → ∀ (E : ℝ) (z : ℂ), (1 - 2 * b) * α₀ ≤ z.im → ‖z‖ ≤ 4 →
          (∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det) ∧
          ∀ p : ℝ, 1 ≤ p → p ≤ ε₁ * W →
            eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p) (layerLaw W b σ) ≤
              ENNReal.ofReal C := by
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  have hη₀0 : 0 < (1 - 2 * b) * α₀ := mul_pos (by linarith) hα₀
  obtain ⟨ε₁, C, hε₁, hC, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 _ 4 hη₀0
  exact ⟨α₀, ε₁, C, hα₀, hε₁, hC, hbulk, habs⟩

theorem hms_eight_le {ε₁ : ℝ} (hε₁ : 0 < ε₁) {W : ℕ} (hW₀ : ⌈8 / ε₁⌉₊ ≤ W) :
    (8 : ℝ) ≤ ε₁ * W := by
  have := Nat.le_ceil (8 / ε₁)
  have h' : (⌈8 / ε₁⌉₊ : ℝ) ≤ W := by exact_mod_cast hW₀
  rw [div_le_iff₀ hε₁] at this
  nlinarith

/-- **Uniform inverse moments of the layer heat matrix** (in the paper: "for `t ≥ 1/2` the
proof of the Gaussian absorption lemma applies at variances `tc, tb`; the extra nonnegative top
height can only improve its imaginary quadratic-form estimate"). For `b ∈ (0, 1/2)` and the bulk
there are `C_A > 0`, `W₀`; for `W ≥ W₀`, every shape `σ`, `β ∈ [0, 2b]`, Hermitian `X`,
`E ∈ I` and `t ∈ [0, 1)`: `‖ ‖ℋ_t⁻¹‖ ‖_{L⁴} ≤ C_A` in the Gaussian coordinates of the layer. -/
theorem hms_layer_moments (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (CA : ℝ) (W₀ : ℕ), 0 < CA ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ (σ : LayerShape) (β : ℝ),
      0 ≤ β → β ≤ 2 * b → ∀ X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, ∀ t ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (fun x => ‖(chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) t x)⁻¹‖) 4
          (gaussianProduct (tflVar W b σ)) ≤ ENNReal.ofReal CA := by
  obtain ⟨α₀, ε₁, C, hα₀, hε₁, hC, hbulk, habs⟩ := hms_contract_setup hcount hb0 hb1 hκ
  set η₀ := (1 - 2 * b) * α₀ with hη₀
  have hη₀0 : 0 < η₀ := mul_pos (by linarith) hα₀
  set δ₀ := min (α₀ / 4) η₀ with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) hη₀0
  refine ⟨max (4 * (1 + C ^ 2)) δ₀⁻¹, ⌈8 / ε₁⌉₊, lt_max_of_lt_right (inv_pos.mpr hδ₀0), ?_⟩
  intro W hW hW₀ σ β hβ0 hβ X hX E hE t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t < 1 := ht.2
  obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
  obtain ⟨hinv, hinvn, hα, hle1⟩ := hms_a_facts hE2 ha1 haim
  set a := matchedA E with ha
  set μ := gaussianProduct (tflVar W b σ)
  set w : ℂ := -(E : ℂ) - ((1 - t : ℝ) : ℂ) * (((1 - b : ℝ) : ℂ) * a) with hw
  set z : ℂ := a⁻¹ + (t : ℂ) * ((β : ℂ) * a) with hz
  have hwim : w.im = (1 - t) * (1 - b) * (-a.im) := by
    simp only [hw, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re]
    ring
  have hzim : z.im = (1 - t * β) * (-a.im) := by
    simp only [hz, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hinv]
    ring
  have htβ : t * β ≤ 2 * b := by nlinarith
  have hzη : η₀ ≤ z.im := by
    rw [hzim, hη₀]
    exact mul_le_mul (by linarith) hα hα₀.le (by linarith)
  have hG : (fun x => ‖(chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) t x)⁻¹‖) =
      fun x => ‖(hmsBlk σ (Real.sqrt t) w z ((fun _ => X) x) (tflEmbed W b σ x))⁻¹‖ := by
    funext x; rw [← cht_heat_embed, hms_heat_blk]
  have hPc : Continuous (fun x => chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) t x) := by
    unfold chtPath; fun_prop
  have hGm : AEStronglyMeasurable
      (fun x => ‖(chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) t x)⁻¹‖) μ :=
    (measurable_matrix_inv.comp hPc.measurable).norm.aestronglyMeasurable
  rw [hG] at hGm ⊢
  refine hms_blk_moments (fun x => tflEmbed_blockDiag_isHermitian W b σ x) (fun _ => hX) hGm
    hδ₀0 hC.le ?_
  by_cases htl : t < 1 / 2
  · left
    refine ⟨(min_le_left _ _).trans ?_, (min_le_right _ _).trans hzη⟩
    rw [hwim]
    have h3 : (1 / 2) * (1 / 2) ≤ (1 - t) * (1 - b) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    nlinarith
  · right
    rw [not_lt] at htl
    obtain ⟨hs1, hs2, hs3⟩ := hms_sqrt_facts htl ht1
    set s := Real.sqrt t with hs
    have hs0 : 0 < s := by linarith
    have hzs : η₀ ≤ (z / (s : ℂ)).im := by
      rw [Complex.div_ofReal_im, le_div_iff₀ hs0]; nlinarith
    have hzn : ‖z‖ ≤ 2 := by
      rw [hz]
      refine (norm_add_le _ _).trans ?_
      rw [hinvn, norm_mul, norm_mul, ha1, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg ht0, Real.norm_of_nonneg hβ0, mul_one]
      nlinarith
    have hzM : ‖z / (s : ℂ)‖ ≤ 4 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le, div_le_iff₀ hs0]
      linarith
    have hXs : (s⁻¹ • X).IsHermitian := by
      unfold IsHermitian; rw [conjTranspose_smul, hX.eq, star_trivial]
    obtain ⟨hunit, hmom⟩ := habs W hW σ (s⁻¹ • X) hXs (-w.re / s) (z / s) hzs hzM
    have hR := hmom 8 (by norm_num) (hms_eight_le hε₁ hW₀)
    rw [ENNReal.ofReal_ofNat] at hR
    have hlaw : layerLaw W b σ = μ.map (tflEmbed W b σ) := tfl_layerLaw_eq_map W b σ
    have hΦ := tfl_measurable_embed W b σ
    have hRm : Measurable (fun ω => ‖layerResolvent σ (-w.re / s) (z / s) (s⁻¹ • X) ω‖) :=
      (measurable_layerResolvent σ _ _ _).norm
    rw [hlaw, eLpNorm_map_measure hRm.aestronglyMeasurable hΦ.aemeasurable] at hR
    rw [hlaw] at hunit
    refine ⟨hs1, ?_, ?_, hη₀0.le.trans hzη, ae_of_ae_map hΦ.aemeasurable hunit,
      (hRm.comp hΦ).aestronglyMeasurable, hR⟩
    · rw [hwim]
      have : 0 ≤ 1 - t := by linarith
      have : 0 ≤ 1 - b := by linarith
      have : 0 ≤ -a.im := by linarith
      positivity
    · rw [hwim]
      have : (1 - t) * (1 - b) * (-a.im) ≤ (1 - t) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hle1 (by linarith)
          (by linarith)
      linarith

/-- Scalars of the core heat matrices: `w = a⁻¹ + ta`, `z = a⁻¹ + tba`. -/
theorem hms_core_scalars {b E t α₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (hα₀ : 0 < α₀) (hE2 : |E| < 2) (ha1 : ‖matchedA E‖ = 1)
    (haim : (matchedA E).im ≤ -α₀) :
    ((matchedA E)⁻¹ + (t : ℂ) * matchedA E).im = (1 - t) * (-(matchedA E).im) ∧
      (1 - 2 * b) * α₀ ≤ ((matchedA E)⁻¹ + (t : ℂ) * ((b : ℂ) * matchedA E)).im ∧
      ‖(matchedA E)⁻¹ + (t : ℂ) * ((b : ℂ) * matchedA E)‖ ≤ 2 ∧
      -(matchedA E).im ≤ 1 ∧ α₀ ≤ -(matchedA E).im := by
  obtain ⟨hinv, hinvn, hα, hle1⟩ := hms_a_facts hE2 ha1 haim
  have e0 : ((matchedA E)⁻¹ + (t : ℂ) * matchedA E).im = (1 - t) * (-(matchedA E).im) := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hinv]; ring
  refine ⟨e0, ?_, ?_, hle1, hα⟩
  · have e : ((matchedA E)⁻¹ + (t : ℂ) * ((b : ℂ) * matchedA E)).im =
        (1 - t * b) * (-(matchedA E).im) := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hinv]; ring
    rw [e]
    have : t * b ≤ 2 * b := by nlinarith
    exact mul_le_mul (by linarith) hα hα₀.le (by nlinarith)
  · refine (norm_add_le _ _).trans ?_
    rw [hinvn, norm_mul, norm_mul, ha1, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ht0, Real.norm_of_nonneg hb0.le, mul_one]
    nlinarith

/-- **Uniform inverse moments of the one-block core heat matrix** (`chtCoreHeat1`). -/
theorem hms_core1_moments (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (CA : ℝ) (W₀ : ℕ), 0 < CA ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ t ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (fun x => ‖(chtPath (chtKC0 .oneBlockTwoPorts E) (chtC1 .oneBlockTwoPorts 0 E b)
          (meqLc W b .oneBlockTwoPorts) t x)⁻¹‖) 4
          (gaussianProduct (tflVar W b .oneBlockTwoPorts)) ≤ ENNReal.ofReal CA := by
  obtain ⟨α₀, ε₁, C, hα₀, hε₁, hC, hbulk, habs⟩ := hms_contract_setup hcount hb0 hb1 hκ
  set η₀ := (1 - 2 * b) * α₀ with hη₀
  have hη₀0 : 0 < η₀ := mul_pos (by linarith) hα₀
  set δ₀ := min (α₀ / 4) η₀ with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) hη₀0
  refine ⟨max (4 * (1 + C ^ 2)) δ₀⁻¹, ⌈8 / ε₁⌉₊, lt_max_of_lt_right (inv_pos.mpr hδ₀0), ?_⟩
  intro W hW hW₀ E hE t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t < 1 := ht.2
  obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
  obtain ⟨hwim, hzη, hzn, hle1, hα⟩ := hms_core_scalars hb0 hb1 ht0 ht1 hα₀ hE2 ha1 haim
  set a := matchedA E with ha
  set μ := gaussianProduct (tflVar W b .oneBlockTwoPorts)
  set w : ℂ := a⁻¹ + (t : ℂ) * a with hw
  set z : ℂ := a⁻¹ + (t : ℂ) * ((b : ℂ) * a) with hz
  have hG : (fun x => ‖(chtPath (chtKC0 .oneBlockTwoPorts E) (chtC1 .oneBlockTwoPorts 0 E b)
      (meqLc W b .oneBlockTwoPorts) t x)⁻¹‖) =
      fun x => ‖(hmsBlk .oneBlockTwoPorts (Real.sqrt t) w z ((fun _ => 0) x)
        (tflEmbed W b .oneBlockTwoPorts x))⁻¹‖ := by
    funext x
    rw [← hms_core1_blk, chtCoreHeat1, chtPath, cht_linS_embed]
  have hPc : Continuous (fun x => chtPath (chtKC0 .oneBlockTwoPorts E)
      (chtC1 .oneBlockTwoPorts 0 E b) (meqLc W b .oneBlockTwoPorts) t x) := by
    unfold chtPath; fun_prop
  have hGm : AEStronglyMeasurable (fun x => ‖(chtPath (chtKC0 .oneBlockTwoPorts E)
      (chtC1 .oneBlockTwoPorts 0 E b) (meqLc W b .oneBlockTwoPorts) t x)⁻¹‖) μ :=
    (measurable_matrix_inv.comp hPc.measurable).norm.aestronglyMeasurable
  rw [hG] at hGm ⊢
  refine hms_blk_moments (fun x => tflEmbed_blockDiag_isHermitian W b _ x)
    (fun _ => isHermitian_zero) hGm hδ₀0 hC.le ?_
  by_cases htl : t < 1 / 2
  · left
    refine ⟨(min_le_left _ _).trans ?_, (min_le_right _ _).trans hzη⟩
    rw [hwim]; nlinarith
  · right
    rw [not_lt] at htl
    obtain ⟨hs1, hs2, hs3⟩ := hms_sqrt_facts htl ht1
    set s := Real.sqrt t with hs
    have hs0 : 0 < s := by linarith
    have hzs : η₀ ≤ (z / (s : ℂ)).im := by
      rw [Complex.div_ofReal_im, le_div_iff₀ hs0]; nlinarith
    have hzM : ‖z / (s : ℂ)‖ ≤ 4 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le, div_le_iff₀ hs0]
      linarith
    have hXs : (s⁻¹ • (0 : Matrix (PhysSite W .oneBlockTwoPorts) (PhysSite W .oneBlockTwoPorts) ℂ)).IsHermitian := by
      rw [smul_zero]; exact isHermitian_zero
    obtain ⟨hunit, hmom⟩ := habs W hW .oneBlockTwoPorts _ hXs (-w.re / s) (z / s) hzs hzM
    have hR := hmom 8 (by norm_num) (hms_eight_le hε₁ hW₀)
    rw [ENNReal.ofReal_ofNat] at hR
    have hlaw : layerLaw W b .oneBlockTwoPorts = μ.map (tflEmbed W b .oneBlockTwoPorts) :=
      tfl_layerLaw_eq_map W b _
    have hΦ := tfl_measurable_embed W b .oneBlockTwoPorts
    have hRm := (measurable_layerResolvent (W := W) .oneBlockTwoPorts (-w.re / s) (z / s)
      (s⁻¹ • 0)).norm
    rw [hlaw, eLpNorm_map_measure hRm.aestronglyMeasurable hΦ.aemeasurable] at hR
    rw [hlaw] at hunit
    refine ⟨hs1, ?_, ?_, hη₀0.le.trans hzη, ae_of_ae_map hΦ.aemeasurable hunit,
      (hRm.comp hΦ).aestronglyMeasurable, hR⟩
    · rw [hwim]
      have : 0 ≤ 1 - t := by linarith
      have : 0 ≤ -a.im := by linarith
      positivity
    · rw [hwim]; nlinarith

/-- **Uniform inverse moments of the two-block core heat matrix** (`chtCoreHeat2`, internal bond
included; conditionally on the bond through `core_mom2`). -/
theorem hms_core2_moments (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (CA : ℝ) (W₀ : ℕ), 0 < CA ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ t ∈ Set.Ico (0 : ℝ) 1,
        eLpNorm (fun x => ‖(chtPath (chtKC0 .separate E) (chtC1 .separate 0 E b)
          (coreLin W b) t x)⁻¹‖) 4 (gaussianProduct (coreVar W b)) ≤ ENNReal.ofReal CA := by
  obtain ⟨α₀, ε₁, C, hα₀, hε₁, hC, hbulk, habs⟩ := hms_contract_setup hcount hb0 hb1 hκ
  set η₀ := (1 - 2 * b) * α₀ with hη₀
  have hη₀0 : 0 < η₀ := mul_pos (by linarith) hα₀
  set δ₀ := min (α₀ / 4) η₀ with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by linarith) hη₀0
  refine ⟨max (4 * (1 + C ^ 2)) δ₀⁻¹, ⌈8 / ε₁⌉₊, lt_max_of_lt_right (inv_pos.mpr hδ₀0), ?_⟩
  intro W hW hW₀ E hE t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t < 1 := ht.2
  obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
  obtain ⟨hwim, hzη, hzn, hle1, hα⟩ := hms_core_scalars hb0 hb1 ht0 ht1 hα₀ hE2 ha1 haim
  set a := matchedA E with ha
  set μ := gaussianProduct (coreVar W b)
  set w : ℂ := a⁻¹ + (t : ℂ) * a with hw
  set z : ℂ := a⁻¹ + (t : ℂ) * ((b : ℂ) * a) with hz
  have hG : (fun x => ‖(chtPath (chtKC0 .separate E) (chtC1 .separate 0 E b)
      (coreLin W b) t x)⁻¹‖) =
      fun x => ‖(hmsBlk .separate (Real.sqrt t) w z (-(Real.sqrt t • coreOff (coreEmbed W b x).1))
        (coreEmbed W b x).2)⁻¹‖ := by
    funext x
    rw [← hms_core2_blk, chtCoreHeat2, chtPath, coreLin_apply]
    congr 4
    rw [coreEmbed, cht_linS_embed, meqLc_apply, add_comm]
  have hPc : Continuous (fun x => chtPath (chtKC0 .separate E) (chtC1 .separate 0 E b)
      (coreLin W b) t x) := by
    unfold chtPath; fun_prop
  have hGm : AEStronglyMeasurable (fun x => ‖(chtPath (chtKC0 .separate E)
      (chtC1 .separate 0 E b) (coreLin W b) t x)⁻¹‖) μ :=
    (measurable_matrix_inv.comp hPc.measurable).norm.aestronglyMeasurable
  rw [hG] at hGm ⊢
  have hYh : ∀ x : CoreCoord W → ℝ,
      (-(Real.sqrt t • coreOff (coreEmbed W b x).1)).IsHermitian := fun x => by
    refine IsHermitian.neg ?_
    unfold IsHermitian; rw [conjTranspose_smul, (coreOff_isHermitian _).eq, star_trivial]
  have hD2 : ∀ x : CoreCoord W → ℝ, (blockDiag (coreEmbed W b x).2.1).IsHermitian := fun x =>
    tflEmbed_blockDiag_isHermitian W b .separate (fun c => x (Sum.inr c))
  refine hms_blk_moments (ℓ := fun x => (coreEmbed W b x).2)
    (Y := fun x => -(Real.sqrt t • coreOff (coreEmbed W b x).1)) hD2 hYh hGm hδ₀0 hC.le ?_
  by_cases htl : t < 1 / 2
  · left
    refine ⟨(min_le_left _ _).trans ?_, (min_le_right _ _).trans hzη⟩
    rw [hwim]; nlinarith
  · right
    rw [not_lt] at htl
    obtain ⟨hs1, hs2, hs3⟩ := hms_sqrt_facts htl ht1
    set s := Real.sqrt t with hs
    have hs0 : 0 < s := by linarith
    have hzs : η₀ ≤ (z / (s : ℂ)).im := by
      rw [Complex.div_ofReal_im, le_div_iff₀ hs0]; nlinarith
    have hzM : ‖z / (s : ℂ)‖ ≤ 4 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs0.le, div_le_iff₀ hs0]
      linarith
    have hYs : ∀ x : CoreCoord W → ℝ,
        s⁻¹ • -(s • coreOff (coreEmbed W b x).1) = -coreOff (coreEmbed W b x).1 := fun x => by
      rw [smul_neg, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
    simp only [hYs]
    have hunit2 := core_ae_unit2 (b := b) (E := -w.re / s) (z := z / s)
      fun X hX => (habs W hW .separate X hX (-w.re / s) (z / s) hzs hzM).1
    have hmom2 := core_mom2 (b := b) (E := -w.re / s) (z := z / s) (q := 8) (by norm_num)
      (by norm_num) (C := C) fun X hX => by
        have := (habs W hW .separate X hX (-w.re / s) (z / s) hzs hzM).2 8 (by norm_num)
          (hms_eight_le hε₁ hW₀)
        rwa [ENNReal.ofReal_ofNat] at this
    have hlaw : coreLaw2 W b = μ.map (coreEmbed W b) := by rw [coreLaw2, core_law_eq_map]
    have hΦ := core_measurable_embed W b
    have hRm := (measurable_coreG2 (W := W) (-w.re / s) (z / s)).norm
    rw [hlaw, eLpNorm_map_measure hRm.aestronglyMeasurable hΦ.aemeasurable] at hmom2
    rw [hlaw] at hunit2
    refine ⟨hs1, ?_, ?_, hη₀0.le.trans hzη, ae_of_ae_map hΦ.aemeasurable hunit2,
      (hRm.comp hΦ).aestronglyMeasurable, hmom2⟩
    · rw [hwim]
      have : 0 ≤ 1 - t := by linarith
      have : 0 ≤ -a.im := by linarith
      positivity
    · rw [hwim]; nlinarith

end LayerMoments

end BlockBand.Layers
