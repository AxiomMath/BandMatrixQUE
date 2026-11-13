module

public import BlockBand.Layers.LayerCoordinates
public import BlockBand.Layers.LayerResolventBound
public import BlockBand.Layers.LayerMeasurability

/-!
# The fresh trace fluctuation bound

The `fluctuation` field of `TraceMatrixContract` (the trace–matrix lemma): "For a single trace,
`d𝒢 = -𝒢(d𝓗)𝒢` gives a Hilbert–Schmidt gradient bounded by `CW^{-1/2}‖𝒢‖²`. The dimension-free
Gaussian `L^p` gradient inequality, with covariance `O(W^{-1})`, gives the fresh trace fluctuation
bound ... Smooth cutoff approximation is justified by the same inverse moments." The hypotheses of
`traceFluctuation_holds` are `GaussianLpGradient` and `GaussianAbsorptionContract`
(a.s. invertibility and `‖‖𝒢‖‖_{L^q} ≤ C_A` for `1 ≤ q ≤ ε₁W`).

Law and normalization: `layerLaw W b σ` (`A_a ~ GUE_W(c/W)`, `c = 1-2b`, bonds `Gin(b/W)`),
realized as the image of `gaussianProduct (tflVar W b σ)` under `tflEmbed`
(`tfl_layerLaw_eq_map`, `BlockBand.Layers.LayerCoordinates`). Norms: `ℓ²` operator norm on
matrices, Euclidean norm on vectors.

Proof.
1. **Regularization (smooth cutoff).** `Gκ = (𝒢⁻¹ + iκ)⁻¹`, `κ > 0`. Since
   `Im ⟨ξ, (𝒢⁻¹ + iκ) ξ⟩ = κ‖ξ‖² + Im z ‖ξ_ports‖²` for Hermitian diagonal blocks and `X`,
   `𝒢⁻¹ + iκ` is invertible at **every** sample with `‖Gκ‖ ≤ κ⁻¹` (`tfl_reg_inv_le`); from
   `Gκ = 𝒢 - iκ 𝒢 Gκ`, `‖Gκ‖ ≤ 2‖𝒢‖` wherever `𝒢⁻¹` is invertible (`tfl_reg_inv_le_two`).
   In the coordinates, `𝒢⁻¹ + iκ` is affine, so `f_κ = W⁻¹ Tr(D Gκ)` is `C^∞`
   (`tflF_contDiff`) with `d f_κ(v) = -W⁻¹ Tr(D Gκ (Λv) Gκ)` (`tflF_fderiv`).
2. **Gradient.** `Σᵢ vᵢ |∂ᵢ f_κ|² ≤ W⁻² (2t_A + 2t_B) ‖Gκ D Gκ‖²_HS ≤ (4‖D‖‖Gκ‖²/W)²`
   (`tfl_weighted_trace_le`, `‖K‖²_HS ≤ |sites| ‖K‖²`, `|sites| ≤ 4W`, `t_A, t_B ≤ 1/W`):
   `tflF_gradient_le`.
3. **`L^p` step.** `GaussianLpGradient` and `‖‖𝒢‖²‖_p = ‖‖𝒢‖‖²_{2p} ≤ C_A²` (`2p ≤ ε₁W`) give
   `‖f_κ - Ef_κ‖_p ≤ C_g √p (16‖D‖/W) C_A²` for every `κ > 0`.
4. **`κ → 0`.** `f_κ → f` a.s. (continuity of inversion at the a.s. invertible `𝒢⁻¹`),
   dominated by `8‖D‖‖𝒢‖ ∈ L¹`; dominated convergence for the means and Fatou for the
   `L^p` norm (`Lp.eLpNorm_lim_le_liminf_eLpNorm`): `tfl_fluctuation_core`.

Constants: `ε₃ = ε₁/2`, `C = 16 C_g K C_A²` (`C_g` absolute; `ε₁, C_A` depend only on
`b, η₀, M`), uniform in `W ≥ 1`, the shape, Hermitian `X`, real `E`, `Im z ≥ η₀`, `|z| ≤ M`,
`‖D‖ ≤ K`, `2 ≤ p ≤ ε₃W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. Deterministic matrix facts
-/

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The regularization `N + iκ` of a square matrix. -/
def tflReg (κ : ℝ) (N : Matrix n n ℂ) : Matrix n n ℂ :=
  N + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ)

/-- Column mass: `Σₓ |K_{xy}|² ≤ ‖K‖²`. -/
theorem tfl_col_sq_le (K : Matrix n n ℂ) (y : n) : ∑ x, ‖K x y‖ ^ 2 ≤ ‖K‖ ^ 2 := by
  have h := norm_toEuclideanLin_le K (EuclideanSpace.single y 1)
  have hs : ‖EuclideanSpace.single y (1 : ℂ)‖ = 1 := by simp
  rw [hs, mul_one] at h
  have h2 : ‖toEuclideanLin K (EuclideanSpace.single y 1)‖ ^ 2 ≤ ‖K‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [EuclideanSpace.norm_sq_eq] at h2
  convert h2 using 3 with x
  simp [toLpLin_apply, EuclideanSpace.single, mulVec_single]

/-- Entry bound `|K_{xy}| ≤ ‖K‖`. -/
theorem tfl_entry_le (K : Matrix n n ℂ) (x y : n) : ‖K x y‖ ≤ ‖K‖ := by
  have h1 : ‖K x y‖ ^ 2 ≤ ∑ x', ‖K x' y‖ ^ 2 :=
    Finset.single_le_sum (f := fun x' => ‖K x' y‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ x)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (h1.trans (tfl_col_sq_le K y))

/-- Hilbert–Schmidt versus operator norm: `‖K‖²_HS ≤ (dim) ‖K‖²`. -/
theorem tfl_hs_le (K : Matrix n n ℂ) :
    ∑ x, ∑ y, ‖K x y‖ ^ 2 ≤ Fintype.card n * ‖K‖ ^ 2 := by
  rw [Finset.sum_comm]
  calc ∑ y, ∑ x, ‖K x y‖ ^ 2 ≤ ∑ _y : n, ‖K‖ ^ 2 := Finset.sum_le_sum fun y _ => tfl_col_sq_le K y
    _ = Fintype.card n * ‖K‖ ^ 2 := by simp

/-- `|Tr A| ≤ (dim) ‖A‖`. -/
theorem tfl_trace_le (A : Matrix n n ℂ) : ‖A.trace‖ ≤ Fintype.card n * ‖A‖ := by
  calc ‖A.trace‖ ≤ ∑ x, ‖A x x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : n, ‖A‖ := Finset.sum_le_sum fun x _ => tfl_entry_le A x x
    _ = Fintype.card n * ‖A‖ := by simp

/-- **Comparison of the regularized inverse.** If `N` is invertible, `c ≠ 0`, and `N + c` is
invertible with `‖(N + c)⁻¹‖ ≤ |c|⁻¹`, then `‖(N + c)⁻¹‖ ≤ 2 ‖N⁻¹‖`. -/
theorem tfl_inv_add_le_two {N : Matrix n n ℂ} {c : ℂ} (hc : c ≠ 0) (hN : IsUnit N.det)
    (hNc : IsUnit (N + c • (1 : Matrix n n ℂ)).det)
    (hb : ‖(N + c • (1 : Matrix n n ℂ))⁻¹‖ ≤ ‖c‖⁻¹) :
    ‖(N + c • (1 : Matrix n n ℂ))⁻¹‖ ≤ 2 * ‖N⁻¹‖ := by
  set G := N⁻¹ with hG
  set Gc := (N + c • (1 : Matrix n n ℂ))⁻¹ with hGc
  have hcp : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hid : Gc = G - c • (G * Gc) := by
    have h1 : G * (N + c • (1 : Matrix n n ℂ)) * Gc = G := by
      rw [Matrix.mul_assoc, mul_nonsing_inv _ hNc, Matrix.mul_one]
    have h2 : G * (N + c • (1 : Matrix n n ℂ)) * Gc = Gc + c • (G * Gc) := by
      rw [Matrix.mul_add, nonsing_inv_mul _ hN, Matrix.add_mul, Matrix.one_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul]
    exact eq_sub_of_add_eq (h2.symm.trans h1)
  have hle : ‖Gc‖ ≤ ‖G‖ + ‖c‖ * (‖G‖ * ‖Gc‖) := by
    calc ‖Gc‖ = ‖G - c • (G * Gc)‖ := by rw [← hid]
      _ ≤ ‖G‖ + ‖c • (G * Gc)‖ := norm_sub_le _ _
      _ ≤ ‖G‖ + ‖c‖ * (‖G‖ * ‖Gc‖) := by
        gcongr
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
  have hG0 := norm_nonneg G
  have hGc0 := norm_nonneg Gc
  by_cases hsmall : ‖c‖ * ‖G‖ ≤ 1 / 2
  · nlinarith
  · replace hsmall := not_le.mp hsmall
    have : ‖c‖⁻¹ ≤ 2 * ‖G‖ := by
      rw [inv_le_iff_one_le_mul₀ hcp]; nlinarith
    exact hb.trans this

/-- Coercivity of `Hf + i diag(q)` with `Hf` Hermitian and `q ≥ κ > 0`:
`κ ‖ξ‖ ≤ ‖(Hf + i diag q) ξ‖`. -/
theorem tfl_lower_of_herm_add_diag {Hf : Matrix n n ℂ} (hH : Hf.IsHermitian) (q : n → ℝ)
    {κ : ℝ} (hq : ∀ x, κ ≤ q x) (ξ : EuclideanSpace ℂ n) :
    κ * ‖ξ‖ ≤
      ‖toEuclideanLin (Hf + Complex.I • diagonal (fun x => (q x : ℂ))) ξ‖ := by
  set T := Hf + Complex.I • diagonal (fun x => (q x : ℂ)) with hT
  have hS : (toEuclideanLin Hf).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hH
  have h1 : (⟪ξ, toEuclideanLin Hf ξ⟫_ℂ).im = 0 := by
    have e1 := hS.coe_re_inner_apply_self ξ
    rw [hS ξ ξ] at e1
    rw [← e1]; simp
  have h2 : (⟪ξ, toEuclideanLin (diagonal (fun x => (q x : ℂ))) ξ⟫_ℂ) =
      ((∑ x, q x * ‖ξ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [toLpLin_apply, mulVec_diagonal, PiLp.toLp_apply]
    rw [show (q x : ℂ) * ξ x = (q x : ℂ) • ξ x from rfl, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    rfl
  have h3 : κ * ‖ξ‖ ^ 2 ≤ (⟪ξ, toEuclideanLin T ξ⟫_ℂ).im := by
    rw [hT, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right,
      inner_smul_right, Complex.add_im, h1, h2, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    simp only [one_mul, mul_zero, zero_add]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hq x) (by positivity)
  have h4 : (⟪ξ, toEuclideanLin T ξ⟫_ℂ).im ≤ ‖ξ‖ * ‖toEuclideanLin T ξ‖ :=
    (Complex.im_le_norm _).trans (norm_inner_le_norm _ _)
  have hξ := norm_nonneg ξ
  rcases hξ.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : ‖ξ‖ * (κ * ‖ξ‖) ≤ ‖ξ‖ * ‖toEuclideanLin T ξ‖ := by nlinarith
    exact le_of_mul_le_mul_left this hpos

end General

/-!
## 2. The regularized layer matrix
-/

/-- The Hermitian part of the regularized layer matrix. -/
def tflHerm {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - X) (bondMatrix σ ω.2)
    (bondMatrix σ ω.2)ᴴ ((z.re : ℂ) • 1)

theorem tflReg_layerMatrix_eq {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) (κ : ℝ) :
    tflReg κ (layerMatrix σ E z X ω) = tflHerm σ E z X ω +
      Complex.I • diagonal (fun x => ((Sum.elim (fun _ => κ) (fun _ => κ + z.im) x : ℝ) : ℂ)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [tflReg, tflHerm, layerMatrix, Matrix.one_apply, diagonal]
  · split_ifs <;> ring
  · split_ifs
    · conv_lhs => rw [← Complex.re_add_im z]
      ring
    · simp

theorem tflHerm_isHermitian {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian) :
    (tflHerm σ E z X ω).IsHermitian := by
  refine IsHermitian.fromBlocks (layerDiag_isHermitian E X hX ω hA) rfl ?_
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- **The regularized layer matrix is invertible, `‖(𝒢⁻¹ + iκ)⁻¹‖ ≤ κ⁻¹`**, for every sample
with Hermitian diagonal blocks, Hermitian `X`, `Im z ≥ 0` and `κ > 0`
(`Im ⟨ξ, (𝒢⁻¹ + iκ) ξ⟩ ≥ κ ‖ξ‖²`). -/
theorem tfl_reg_inv_le {W : ℕ} (σ : LayerShape) (E : ℝ) {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ}
    (hκ : 0 < κ) :
    IsUnit (tflReg κ (layerMatrix σ E z X ω)).det ∧
      ‖(tflReg κ (layerMatrix σ E z X ω))⁻¹‖ ≤ κ⁻¹ := by
  refine isUnit_det_and_norm_inv_le_of_lower hκ fun ξ => ?_
  rw [tflReg_layerMatrix_eq]
  refine tfl_lower_of_herm_add_diag (tflHerm_isHermitian σ E z hX ω hA) _ ?_ ξ
  rintro (x | x)
  · simp
  · simp only [Sum.elim_inr]; linarith

/-- **`‖(𝒢⁻¹ + iκ)⁻¹‖ ≤ 2 ‖𝒢‖`** whenever the layer matrix is invertible (every `κ > 0`). -/
theorem tfl_reg_inv_le_two {W : ℕ} (σ : LayerShape) (E : ℝ) {z : ℂ}
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (ω : LayerSample W σ)
    (hA : (Internal.Contracts.Layers.blockDiag ω.1).IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ}
    (hκ : 0 < κ) (hN : IsUnit (layerMatrix σ E z X ω).det) :
    ‖(tflReg κ (layerMatrix σ E z X ω))⁻¹‖ ≤ 2 * ‖layerResolvent σ E z X ω‖ := by
  obtain ⟨hu, hb⟩ := tfl_reg_inv_le σ E hX ω hA hz hκ
  have hc : ((κ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne') Complex.I_ne_zero
  have hnc : ‖(κ : ℂ) * Complex.I‖ = κ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  refine tfl_inv_add_le_two hc hN hu ?_
  rw [hnc]; exact hb

/-!
## 3. The regularized trace as a smooth function of the real coordinates
-/

section Coordinates

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

/-- The regularized layer matrix `𝒢⁻¹ + iκ` as an affine function of the coordinates. -/
def tflPsi (κ : ℝ) (x : TflCoord W σ → ℝ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  (tflConst σ E z X + ((κ : ℂ) * Complex.I) • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) +
    LinearMap.toContinuousLinearMap (tflLinMap W b σ) x

theorem tflPsi_eq (κ : ℝ) (x : TflCoord W σ → ℝ) :
    tflPsi W b σ E z X κ x = tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x)) := by
  rw [tflReg, tfl_layerMatrix_embed, tflPsi, LinearMap.coe_toContinuousLinearMap']
  change _ + tflLin W b σ x = _
  abel

theorem tflEmbed_blockDiag_isHermitian (x : TflCoord W σ → ℝ) :
    (Internal.Contracts.Layers.blockDiag (tflEmbed W b σ x).1).IsHermitian :=
  blockDiag_isHermitian fun _ => gueOfCoords_isHermitian _ _ _

variable {X} in
theorem tflPsi_isUnit (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : IsUnit (tflPsi W b σ E z X κ x) := by
  rw [tflPsi_eq, Matrix.isUnit_iff_isUnit_det]
  exact (tfl_reg_inv_le σ E hX _ (tflEmbed_blockDiag_isHermitian W b σ x) hz hκ).1

/-- The normalized trace functional `N ↦ W⁻¹ Tr(D N)` (real-linear). -/
def tflTraceLin (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ →ₗ[ℝ] ℂ where
  toFun N := (W : ℂ)⁻¹ * (D * N).trace
  map_add' N N' := by simp [Matrix.trace_add, mul_add]
  map_smul' r N := by simp [Matrix.trace_smul]; ring

/-- The normalized trace functional as a continuous linear map. -/
def tflTraceCLM (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (tflTraceLin W σ D)

theorem tflTraceCLM_apply (D N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    tflTraceCLM W σ D N = (W : ℂ)⁻¹ * (D * N).trace := rfl

/-- The regularized trace `f_κ(x) = W⁻¹ Tr(D (𝒢⁻¹ + iκ)⁻¹)` in real coordinates. -/
def tflF (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (κ : ℝ) (x : TflCoord W σ → ℝ) : ℂ :=
  tflTraceCLM W σ D (Ring.inverse (tflPsi W b σ E z X κ x))

theorem tflF_eq (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (κ : ℝ) (x : TflCoord W σ → ℝ) :
    tflF W b σ E z X D κ x =
      (W : ℂ)⁻¹ * (D * (tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x)))⁻¹).trace := by
  rw [tflF, tflTraceCLM_apply, ← Matrix.nonsing_inv_eq_ringInverse, tflPsi_eq]

variable {X} in
/-- `f_κ` is `C¹` (indeed `C^∞`): inversion is smooth on invertible matrices. -/
theorem tflF_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    {κ : ℝ} (hκ : 0 < κ) : ContDiff ℝ 1 (tflF W b σ E z X D κ) := by
  have hL : ContDiff ℝ 1 (tflPsi W b σ E z X κ) :=
    contDiff_const.add (ContinuousLinearMap.contDiff _)
  refine (ContinuousLinearMap.contDiff _).comp ?_
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := contDiffAt_ringInverse ℝ (n := 1) (tflPsi_isUnit W b σ E z hX hz hκ x).unit
  rw [IsUnit.unit_spec] at h
  exact h.comp x hL.contDiffAt

variable {X} in
/-- The derivative of `f_κ`: `d f_κ (v) = -W⁻¹ Tr(D Gκ (Λ v) Gκ)`, `Gκ = (𝒢⁻¹ + iκ)⁻¹`. -/
theorem tflF_fderiv (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {κ : ℝ} (hκ : 0 < κ)
    (x v : TflCoord W σ → ℝ) :
    fderiv ℝ (tflF W b σ E z X D κ) x v =
      -((W : ℂ)⁻¹ * (D * (Ring.inverse (tflPsi W b σ E z X κ x) * tflLin W b σ v *
        Ring.inverse (tflPsi W b σ E z X κ x))).trace) := by
  set u := (tflPsi_isUnit W b σ E z hX hz hκ x).unit with hu
  have hL : HasFDerivAt (tflPsi W b σ E z X κ)
      (LinearMap.toContinuousLinearMap (tflLinMap W b σ)) x :=
    (ContinuousLinearMap.hasFDerivAt _).const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) ↑u⁻¹ ↑u⁻¹))
      (tflPsi W b σ E z X κ x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [IsUnit.unit_spec] at this
  have h2 := h.comp x hL
  have h3 := (tflTraceCLM W σ D).hasFDerivAt.comp x h2
  rw [show tflF W b σ E z X D κ = (tflTraceCLM W σ D) ∘ (Ring.inverse ∘ tflPsi W b σ E z X κ)
    from rfl, h3.fderiv]
  have hinv : (↑u⁻¹ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) =
      Ring.inverse (tflPsi W b σ E z X κ x) := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec]
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, LinearMap.coe_toContinuousLinearMap', hinv,
    map_neg, tflTraceCLM_apply]
  rfl

/-- `|LayerSite| ≤ 4W`. -/
theorem tfl_card_layerSite_le : (Fintype.card (LayerSite W σ) : ℝ) ≤ 4 * W := by
  have hb : σ.blocks ≤ 2 := by cases σ <;> decide
  have hp : σ.ports ≤ 2 := by cases σ <;> decide
  have : Fintype.card (LayerSite W σ) ≤ 4 * W := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  exact_mod_cast this

variable {W b} in
/-- Both coordinate variances are at most `1/W` for `0 < b < 1/2`. -/
theorem tfl_TA_TB_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) :
    (tflTA W b : ℝ) ≤ 1 / W ∧ (tflTB W b : ℝ) ≤ 1 / W := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  constructor
  · rw [tflTA, Real.coe_toNNReal']
    refine max_le ?_ (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  · rw [tflTB, Real.coe_toNNReal']
    refine max_le ?_ (by positivity)
    exact div_le_div_of_nonneg_right (by linarith) hW'.le

variable {X} in
/-- **Gradient bound**. For `W ≥ 1`, `0 < b < 1/2`, Hermitian `X`,
`Im z ≥ 0` and `κ > 0`, at every point,
`(Σᵢ vᵢ |∂ᵢ f_κ|²)^{1/2} ≤ 4 ‖D‖ ‖Gκ‖² / W`, `Gκ = (𝒢⁻¹ + iκ)⁻¹`. -/
theorem tflF_gradient_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) :
    weightedGradientNorm (tflVar W b σ) (tflF W b σ E z X D κ) x ≤
      4 * ‖D‖ * ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ ^ 2 / W := by
  set G := Ring.inverse (tflPsi W b σ E z X κ x) with hG
  set K := G * D * G with hK
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hder : ∀ i : TflCoord W σ, ‖fderiv ℝ (tflF W b σ E z X D κ) x (Pi.single i 1)‖ ^ 2 =
      ((W : ℝ)⁻¹) ^ 2 * ‖(K * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 := by
    intro i
    have htr : (D * (G * tflLin W b σ (Pi.single i 1) * G)).trace =
        (K * tflLin W b σ (Pi.single i 1)).trace := by
      rw [hK, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc]
    rw [tflF_fderiv W b σ E z hX hz D hκ, norm_neg, ← hG, htr, norm_mul, mul_pow, norm_inv,
      Complex.norm_natCast]
  have hK' : ‖K‖ ≤ ‖D‖ * ‖G‖ ^ 2 := by
    calc ‖K‖ ≤ ‖G * D‖ * ‖G‖ := norm_mul_le _ _
      _ ≤ ‖G‖ * ‖D‖ * ‖G‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖D‖ * ‖G‖ ^ 2 := by ring
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  have hsum : ∑ i, (tflVar W b σ i : ℝ) *
      ‖fderiv ℝ (tflF W b σ E z X D κ) x (Pi.single i 1)‖ ^ 2 ≤
      (4 * ‖D‖ * ‖G‖ ^ 2 / W) ^ 2 := by
    simp_rw [hder]
    have e : ∑ i, (tflVar W b σ i : ℝ) * (((W : ℝ)⁻¹) ^ 2 *
        ‖(K * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2) = ((W : ℝ)⁻¹) ^ 2 *
        ∑ i, (tflVar W b σ i : ℝ) * ‖(K * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 := tfl_weighted_trace_le W b σ K
    have h2 := tfl_hs_le K
    have h3 := tfl_card_layerSite_le W σ
    have hHS0 : 0 ≤ ∑ x, ∑ y, ‖K x y‖ ^ 2 := by positivity
    have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
      have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
      rw [this]; linarith
    have hK2 : ‖K‖ ^ 2 ≤ (‖D‖ * ‖G‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hK' 2
    calc ((W : ℝ)⁻¹) ^ 2 * ∑ i, (tflVar W b σ i : ℝ) *
          ‖(K * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2
        ≤ ((W : ℝ)⁻¹) ^ 2 * ((4 / W) * (4 * W * ‖K‖ ^ 2)) := by
          gcongr
          refine h1.trans ?_
          have hcoef : 0 ≤ 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) := by positivity
          calc (2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ)) * ∑ x, ∑ y, ‖K x y‖ ^ 2
              ≤ (4 / W) * ∑ x, ∑ y, ‖K x y‖ ^ 2 := mul_le_mul_of_nonneg_right hc hHS0
            _ ≤ (4 / W) * (4 * W * ‖K‖ ^ 2) := by
                gcongr
                exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
      _ = 16 * ‖K‖ ^ 2 / W ^ 2 := by field_simp; ring
      _ ≤ 16 * (‖D‖ * ‖G‖ ^ 2) ^ 2 / W ^ 2 := by gcongr
      _ = (4 * ‖D‖ * ‖G‖ ^ 2 / W) ^ 2 := by ring
  unfold weightedGradientNorm
  calc Real.sqrt (∑ i, (tflVar W b σ i : ℝ) *
        ‖fderiv ℝ (tflF W b σ E z X D κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt ((4 * ‖D‖ * ‖G‖ ^ 2 / W) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 4 * ‖D‖ * ‖G‖ ^ 2 / W := Real.sqrt_sq (by positivity)

theorem tflPsi_inv_eq (κ : ℝ) (x : TflCoord W σ → ℝ) :
    Ring.inverse (tflPsi W b σ E z X κ x) =
      (tflReg κ (layerMatrix σ E z X (tflEmbed W b σ x)))⁻¹ := by
  rw [← Matrix.nonsing_inv_eq_ringInverse, tflPsi_eq]

variable {X} in
theorem tflPsi_inv_le (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ ≤ κ⁻¹ := by
  rw [tflPsi_inv_eq]
  exact (tfl_reg_inv_le σ E hX _ (tflEmbed_blockDiag_isHermitian W b σ x) hz hκ).2

variable {X} in
theorem tflPsi_inv_le_two (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) (hN : IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det) :
    ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ ≤
      2 * ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ := by
  rw [tflPsi_inv_eq]
  exact tfl_reg_inv_le_two σ E hX _ (tflEmbed_blockDiag_isHermitian W b σ x) hz hκ hN

variable {W} in
/-- `|f_κ| ≤ 4 ‖D‖ ‖Gκ‖` (`|Tr A| ≤ (dim) ‖A‖`, `dim ≤ 4W`). -/
theorem tflF_norm_le (hW : 0 < W) (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (κ : ℝ)
    (x : TflCoord W σ → ℝ) :
    ‖tflF W b σ E z X D κ x‖ ≤ 4 * ‖D‖ * ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ := by
  set G := Ring.inverse (tflPsi W b σ E z X κ x)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [tflF, tflTraceCLM_apply, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := tfl_trace_le (D * G)
  have h2 := tfl_card_layerSite_le W σ
  have h3 : ‖D * G‖ ≤ ‖D‖ * ‖G‖ := norm_mul_le _ _
  calc (W : ℝ)⁻¹ * ‖(D * G).trace‖ ≤ (W : ℝ)⁻¹ * (4 * W * (‖D‖ * ‖G‖)) := by
        gcongr
        exact h1.trans (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
    _ = 4 * ‖D‖ * ‖G‖ := by field_simp

end Coordinates

/-!
## 4. The fluctuation bound
-/

instance tfl_isProbabilityMeasure_gaussianProduct {ι : Type} [Fintype ι] (v : ι → ℝ≥0) :
    IsProbabilityMeasure (gaussianProduct v) := by
  unfold gaussianProduct; infer_instance

/-- The single-trace observable `ω ↦ W⁻¹ Tr(D 𝒢(ω))` is measurable. -/
theorem tfl_measurable_trace {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Measurable (fun ω : LayerSample W σ => (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace) := by
  have hc : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      (W : ℂ)⁻¹ * (D * N).trace) :=
    continuous_const.mul (continuous_const.matrix_mul continuous_id).matrix_trace
  exact hc.measurable.comp (measurable_layerResolvent σ E z X)

/-- **Core fluctuation bound** in the real coordinates, from the gradient inequality with
constant `Cg`, a.e. invertibility and the `L^{2p}` bound `CA` on `‖𝒢‖`:
`‖f - Ef‖_p ≤ Cg √p (16 ‖D‖/W) CA²`. -/
theorem tfl_fluctuation_core {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (σ : LayerShape)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ) {z : ℂ}
    (hz : 0 ≤ z.im) (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {p : ℝ} (hp : 1 ≤ p)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hmom : eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal (2 * p))
      (layerLaw W b σ) ≤ ENNReal.ofReal CA) :
    eLpNorm (fun ω => (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace -
        ∫ ω', (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω').trace ∂layerLaw W b σ)
        (ENNReal.ofReal p) (layerLaw W b σ) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (16 * ‖D‖ / W) * CA ^ 2) := by
  set μ := gaussianProduct (tflVar W b σ) with hμ
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μ.map Φ := tfl_layerLaw_eq_map W b σ
  set f : LayerSample W σ → ℂ := fun ω => (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace
    with hfdef
  have hf : Measurable f := tfl_measurable_trace σ E z X D
  set F : (TflCoord W σ → ℝ) → ℂ := fun x => f (Φ x) with hFdef
  have hF : Measurable F := hf.comp hΦ
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hGr : Measurable Gr := (measurable_layerResolvent σ E z X).comp hΦ
  -- transfer to the coordinates
  have htransfer : eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b σ) (ENNReal.ofReal p)
      (layerLaw W b σ) = eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ := by
    rw [hlaw, integral_map hΦ.aemeasurable hf.aestronglyMeasurable,
      eLpNorm_map_measure (hf.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
    rfl
  change eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b σ) (ENNReal.ofReal p)
      (layerLaw W b σ) ≤ _
  rw [htransfer]
  have hp0 : 0 ≤ p := by linarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  -- a.e. invertibility and moments in the coordinates
  have hinvμ : ∀ᵐ x ∂μ, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hmomμ : eLpNorm Gr (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal CA := by
    rw [hlaw, eLpNorm_map_measure (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable
      hΦ.aemeasurable] at hmom
    rw [← eLpNorm_norm _ hGr.aestronglyMeasurable]
    exact hmom
  have hGrmem : MemLp (fun x => ‖Gr x‖) (ENNReal.ofReal (2 * p)) μ := by
    rw [memLp_iff, eLpNorm_norm _ hGr.aestronglyMeasurable]
    exact lt_of_le_of_lt hmomμ ENNReal.ofReal_lt_top
  have hGrint : Integrable (fun x => ‖Gr x‖) μ :=
    hGrmem.integrable (by rw [ENNReal.one_le_ofReal]; linarith)
  -- the square moment: `‖ ‖G‖² ‖_p ≤ CA²`
  have hsq : eLpNorm (fun x => ‖Gr x‖ ^ 2) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (CA ^ 2) := by
    have e1 : (fun x => ‖Gr x‖ ^ 2) = fun x => ‖Gr x‖ ^ (2 : ℝ) := by
      funext x; rw [Real.rpow_two]
    rw [e1, eLpNorm_norm_rpow Gr hGr.aestronglyMeasurable two_pos,
      ← ENNReal.ofReal_mul hp0, mul_comm p 2, ENNReal.ofReal_pow hCA]
    calc eLpNorm Gr (ENNReal.ofReal (2 * p)) μ ^ (2 : ℝ) ≤ ENNReal.ofReal CA ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hmomμ (by norm_num)
      _ = ENNReal.ofReal CA ^ 2 := by rw [← ENNReal.rpow_natCast]; norm_num
  set c : ℝ := 16 * ‖D‖ / W with hc
  have hc0 : 0 ≤ c := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p * c * CA ^ 2) with hB
  -- the bound for each regularization `κ > 0`
  have hstep : ∀ κ : ℝ, 0 < κ →
      eLpNorm (fun x => tflF W b σ E z X D κ x - ∫ y, tflF W b σ E z X D κ y ∂μ)
        (ENNReal.ofReal p) μ ≤ B := by
    intro κ hκ
    have hC := tflF_contDiff W b σ E z hX hz D hκ
    have hcont : Continuous (tflF W b σ E z X D κ) := hC.continuous
    have hmem : MemLp (tflF W b σ E z X D κ) (ENNReal.ofReal p) μ := by
      refine MemLp.of_bound hcont.aestronglyMeasurable (4 * ‖D‖ * κ⁻¹)
        (ae_of_all _ fun x => ?_)
      refine (tflF_norm_le b σ E z X hW D κ x).trans ?_
      gcongr
      exact tflPsi_inv_le W b σ E z hX hz hκ x
    have h1 := hgr p hp (TflCoord W σ) (tflVar W b σ) (tflF W b σ E z X D κ) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm (tflVar W b σ) (tflF W b σ E z X D κ)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm (tflVar W b σ) (tflF W b σ E z X D κ) x‖ ≤
        ‖c * ‖Gr x‖ ^ 2‖ := by
      filter_upwards [hinvμ] with x hx
      have hg := tflF_gradient_le W b σ E z hW hb0 hb1 hX hz D hκ x
      have h2 := tflPsi_inv_le_two W b σ E z hX hz hκ x hx
      have hg0 : 0 ≤ weightedGradientNorm (tflVar W b σ) (tflF W b σ E z X D κ) x :=
        Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg (by positivity)]
      refine hg.trans ?_
      have h3 : ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ ^ 2 ≤ (2 * ‖Gr x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc 4 * ‖D‖ * ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ ^ 2 / W
          ≤ 4 * ‖D‖ * (2 * ‖Gr x‖) ^ 2 / W := by gcongr
        _ = c * ‖Gr x‖ ^ 2 := by rw [hc]; ring
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => c * ‖Gr x‖ ^ 2) (ENNReal.ofReal p) μ =
        ENNReal.ofReal c * eLpNorm (fun x => ‖Gr x‖ ^ 2) (ENNReal.ofReal p) μ := by
      rw [show (fun x => c * ‖Gr x‖ ^ 2) = c • (fun x => ‖Gr x‖ ^ 2) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]
    calc ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm (tflVar W b σ) (tflF W b σ E z X D κ)) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal c * ENNReal.ofReal (CA ^ 2)) := by
          gcongr
          exact h4.trans (h5.le.trans (by gcongr))
      _ = B := by
          rw [hB, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  -- the limit `κ = 1/(m+1) → 0`
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Fm : ℕ → (TflCoord W σ → ℝ) → ℂ := fun m => tflF W b σ E z X D (κm m) with hFm
  have hFmc : ∀ m, Continuous (Fm m) := fun m =>
    (tflF_contDiff W b σ E z hX hz D (hκpos m)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x) atTop (𝓝 (F x)) := by
    filter_upwards [hinvμ] with x hx
    set N := layerMatrix σ E z X (Φ x) with hN
    have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
    have hcN : Continuous (fun κ : ℝ => N + ((κ : ℂ) * Complex.I) •
        (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) := by fun_prop
    have h1 : Tendsto (fun m => tflPsi W b σ E z X (κm m) x) atTop (𝓝 N) := by
      have := (hcN.tendsto 0).comp hκlim
      simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      rw [tflPsi_eq, tflReg]
    have h2 : Tendsto (fun m => Ring.inverse (tflPsi W b σ E z X (κm m) x)) atTop
        (𝓝 (Ring.inverse N)) := by
      have hc := NormedRing.inverse_continuousAt hU.unit
      rw [IsUnit.unit_spec] at hc
      exact hc.tendsto.comp h1
    have h3 := ((tflTraceCLM W σ D).continuous.tendsto _).comp h2
    have hFx : F x = tflTraceCLM W σ D (Ring.inverse N) := by
      rw [tflTraceCLM_apply, ← Matrix.nonsing_inv_eq_ringInverse]
      rfl
    rw [hFx]
    exact h3
  have hbound : ∀ m, ∀ᵐ x ∂μ, ‖Fm m x‖ ≤ 8 * ‖D‖ * ‖Gr x‖ := by
    intro m
    filter_upwards [hinvμ] with x hx
    refine (tflF_norm_le b σ E z X hW D (κm m) x).trans ?_
    have := tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
    calc 4 * ‖D‖ * ‖Ring.inverse (tflPsi W b σ E z X (κm m) x)‖ ≤ 4 * ‖D‖ * (2 * ‖Gr x‖) := by
          gcongr
      _ = 8 * ‖D‖ * ‖Gr x‖ := by ring
  have hint : Tendsto (fun m => ∫ x, Fm m x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => 8 * ‖D‖ * ‖Gr x‖)
      (fun m => (hFmc m).aestronglyMeasurable) (hGrint.const_mul _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x - ∫ y, Fm m y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun m => ((hFmc m).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  exact hstep (κm m) (hκpos m)

/-- **The fresh trace fluctuation bound**: the `fluctuation` field of `TraceMatrixContract`, from
`GaussianLpGradient` and `GaussianAbsorptionContract`. With `ε₁, C_A` from
`GaussianAbsorptionContract b η₀ M` and `C_g` from `GaussianLpGradient`: `ε₃ = ε₁/2` and
`C = 16 C_g K C_A²`; uniformly in `W ≥ 1`, the shape, Hermitian `X`, real `E`, `Im z ≥ η₀`,
`|z| ≤ M`, `‖D‖ ≤ K` and `2 ≤ p ≤ ε₃ W`: `‖f - Ef‖_{L^p(layerLaw)} ≤ C √p / W` for
`f = W⁻¹ Tr(D 𝒢)`. -/
theorem traceFluctuation_holds (hgrad : GaussianLpGradient)
    (habs : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ η₀ M : ℝ, 0 < η₀ → ∀ K : ℝ,
    ∃ ε₃ C : ℝ, 0 < ε₃ ∧ ∀ (W : ℕ), 0 < W →
      ∀ (σ : LayerShape) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ), X.IsHermitian →
      ∀ (E : ℝ) (z : ℂ), η₀ ≤ z.im → ‖z‖ ≤ M →
      ∀ D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖D‖ ≤ K →
      ∀ p : ℝ, 2 ≤ p → p ≤ ε₃ * W →
        let μ := layerLaw W b σ
        let f : LayerSample W σ → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (D * layerResolvent σ E z X ω).trace
        eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂μ) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 η₀ M hη K
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  obtain ⟨ε₁, CA, hε₁, hCA, habs'⟩ := habs b hb0 hb1 η₀ M hη
  refine ⟨ε₁ / 2, 16 * Cg * K * CA ^ 2, by positivity, ?_⟩
  intro W hW σ X hX E z hz hzM D hD p hp2 hpε μ f
  obtain ⟨hinv, hmom⟩ := habs' W hW σ X hX E z hz hzM
  have hz0 : 0 ≤ z.im := le_trans hη.le hz
  have h2p1 : 1 ≤ 2 * p := by linarith
  have h2pε : 2 * p ≤ ε₁ * W := by linarith
  have hcore := tfl_fluctuation_core hCg.le hgr hW hb0 hb1 σ hX E hz0 D (by linarith : (1 : ℝ) ≤ p)
    hCA.le hinv (hmom (2 * p) h2p1 h2pε)
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hD
  have hsp : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  calc Cg * Real.sqrt p * (16 * ‖D‖ / W) * CA ^ 2
      = 16 * Cg * ‖D‖ * CA ^ 2 * Real.sqrt p / W := by ring
    _ ≤ 16 * Cg * K * CA ^ 2 * Real.sqrt p / W := by gcongr

/-- `traceFluctuation_holds` has exactly the type of `TraceMatrixContract.fluctuation`. -/
example (hgrad : GaussianLpGradient) (habs : GaussianAbsorptionContract)
    (hT : TraceMatrixContract) : hT.fluctuation = traceFluctuation_holds hgrad habs := rfl

end BlockBand.Layers
