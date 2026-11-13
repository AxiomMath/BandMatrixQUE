module

public import BlockBand.Critical.MatrixClosing.Mean.Spectral
public import BlockBand.Critical.Collar.Density.SecondMoment
public import BlockBand.Critical.Collar.Density.RegularBound
public import BlockBand.Critical.CommonPort.Moments
public import BlockBand.Critical.MatrixClosing.MiddleShift.Params

/-!
# Matrix closing, mean clause: the distant collar bound

*Law.* `collarLaw W b`, `0 < b < 1/2`; deterministic Hermitian `X` (no norm bound);
`e ∈ bulkInterval κ`.

* `sum_cauchyKernel_one_eq`: `Σ_ℓ P₁(λ_ℓ)|y*u_ℓ|² = π⁻¹‖(K - i)⁻¹y‖²` (simple spectrum).
* `sum_norm_sq_inv_sub_I_le_frame`: `‖(F + G - i)⁻¹(F - w̄)z₀‖² ≤ 18‖z₀‖² + 4‖Gz₀‖²`
  (deterministic form of the distant collar bound; `|w| ≤ 1`). Instead of fresh norm moments of
  `‖G‖`, only `E_G‖Gz₀‖² = c‖z₀‖²` (`lintegral_norm_sq_mulVec_gue`) is used.
* `collarTW_conj_eq_frame`: `T*K*q = (F - w̄)(L')*q`, `L' = KTH`, `H = (F - ca)⁻¹`.
* **`lintegral_spectralSum_one_le`**: `E_collar Σ_ℓ P₁(λ_ℓ(Q))|(T*K*q)*u_ℓ|² ≤ C₁‖q‖²` for
  `W ≥ W₁`, uniformly in `e`, Hermitian `X` and `q`; from `CommonPortMeanContract.moments`
  (`p = 2`, `E‖L‖² ≤ C²`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Coarea.FreshPalm
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

/-!
## Deterministic resolvent bounds at height one
-/

section Det

variable {N : ℕ}

theorem I_eq_mk : Complex.I = (⟨0, 1⟩ : ℂ) := rfl

/-- `‖(K - i)⁻¹a‖² ≤ ‖a‖²` for Hermitian `K`. -/
theorem sum_norm_sq_inv_sub_I_mulVec_le {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (a : Fin N → ℂ) :
    ∑ i, ‖((K - Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ a) i‖ ^ 2 ≤
      ∑ i, ‖a i‖ ^ 2 := by
  have h1 := im_dotProduct_inv_mulVec hK (z := Complex.I) (by simp) a
  have h2 := Collar.Density.im_dotProduct_inv_sub_I_le hK a
  rw [← I_eq_mk, h1, Complex.I_im, one_mul, BlockBand.Wegner.re_star_dotProduct_self] at h2
  exact h2

/-- On simple spectrum, `Σ_ℓ P₁(λ_ℓ)|y*u_ℓ|² = π⁻¹‖(K - i)⁻¹y‖²`. -/
theorem sum_cauchyKernel_one_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (y : Fin N → ℂ) :
    ∑ ℓ, cauchyKernel 1 (freshEigenvalue K ℓ) * ‖star y ⬝ᵥ freshEigenvector K ℓ‖ ^ 2 =
      Real.pi⁻¹ * ∑ i, ‖((K - Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ y) i‖ ^ 2 := by
  have h1 := im_dotProduct_inv_mulVec hK.1 (z := Complex.I) (by simp) y
  rw [Complex.I_im, one_mul, BlockBand.Wegner.re_star_dotProduct_self] at h1
  rw [← h1, hK.inv_eq_sum (by simp), Matrix.sum_mulVec, dotProduct_sum, Complex.im_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, star_dotProduct_freshProjector_mulVec,
    Complex.im_mul_ofReal]
  set l := freshEigenvalue K ℓ
  have hd : (((l : ℝ) : ℂ) - Complex.I)⁻¹.im = 1 / (l ^ 2 + 1) := by
    rw [Complex.inv_im, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, Complex.sub_im,
      Complex.ofReal_im, Complex.I_im]
    ring
  rw [hd, cauchyKernel]
  field_simp

/-- **The distant-collar bound** (deterministic form): if `K = F + G`
Hermitian and `y = (F - w̄)z₀`, `|w| ≤ 1`, then
`‖(K - i)⁻¹y‖² ≤ 18‖z₀‖² + 4‖Gz₀‖²`. -/
theorem sum_norm_sq_inv_sub_I_le_frame {F G : Matrix (Fin N) (Fin N) ℂ}
    (hK : (F + G).IsHermitian) {w : ℂ} (hw1 : ‖w‖ ≤ 1) (z₀ : Fin N → ℂ) :
    ∑ i, ‖((F + G - Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ
        ((F - star w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ z₀)) i‖ ^ 2 ≤
      18 * ∑ i, ‖z₀ i‖ ^ 2 + 4 * ∑ i, ‖(G *ᵥ z₀) i‖ ^ 2 := by
  set M := F + G - Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hMu : IsUnit M.det := isUnit_det_sub_smul_one hK (by simp)
  set a := G *ᵥ z₀ + (star w - Complex.I) • z₀
  have hMz : M *ᵥ z₀ = (F - star w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ z₀ + a := by
    simp only [M, a, sub_mulVec, add_mulVec, smul_mulVec, one_mulVec, sub_smul]
    abel
  have hRy : M⁻¹ *ᵥ ((F - star w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ z₀) =
      z₀ + -(M⁻¹ *ᵥ a) := by
    have h : M⁻¹ *ᵥ (M *ᵥ z₀) = z₀ := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hMu, one_mulVec]
    rw [hMz, mulVec_add] at h
    rw [← sub_eq_add_neg]
    exact eq_sub_of_add_eq h
  rw [hRy]
  have hneg : ∑ i, ‖(-(M⁻¹ *ᵥ a)) i‖ ^ 2 = ∑ i, ‖(M⁻¹ *ᵥ a) i‖ ^ 2 := by
    simp only [Pi.neg_apply, norm_neg]
  have h1 := sum_norm_sq_add_le z₀ (-(M⁻¹ *ᵥ a))
  have h2 := sum_norm_sq_inv_sub_I_mulVec_le hK a
  have h3 := sum_norm_sq_add_le (G *ᵥ z₀) ((star w - Complex.I) • z₀)
  have hc : ‖star w - Complex.I‖ ≤ 2 := by
    calc ‖star w - Complex.I‖ ≤ ‖star w‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_star, Complex.norm_I]; linarith
      _ = 2 := by norm_num
  have h4 : ∑ i, ‖((star w - Complex.I) • z₀) i‖ ^ 2 ≤ 4 * ∑ i, ‖z₀ i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    have : ‖star w - Complex.I‖ ^ 2 ≤ 4 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hc 2; norm_num at this; exact this
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rw [hneg] at h1
  have : 0 ≤ ∑ i, ‖z₀ i‖ ^ 2 := by positivity
  linarith

end Det

/-!
## The collar tail at height one
-/

section Collar

variable {W : ℕ}

/-- `y = T*K*q = (F - w̄)H*y`, `H*y = (L')*q`, `L' = KTH` (`H = (F - w)⁻¹`, `w = ca`). -/
theorem collarTW_conj_eq_frame {b e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian)
    (hD : IsUnit (Collar.Density.collarTopBlock e X ω).det)
    (hw : (Collar.Density.collarShiftW b e).im < 0) (q : Fin 2 × Fin W → ℂ) :
    (Collar.Density.collarTW e X ω)ᴴ *ᵥ ((matchedLeadK b e X)ᴴ *ᵥ q) =
      (Collar.Density.collarFW e X ω - star (Collar.Density.collarShiftW b e) •
          (1 : Matrix (Fin W) (Fin W) ℂ)) *ᵥ
        (((commonPortL b e X ω).submatrix id (Collar.Density.portEquiv W).symm)ᴴ *ᵥ q) := by
  set F := Collar.Density.collarFW e X ω
  set w := Collar.Density.collarShiftW b e
  have hF : F.IsHermitian := Collar.Density.collarFW_isHermitian e hX hA
  have hS := Collar.Density.isUnit_det_collarF_sub (b := b) hX hA hw
  rw [← Collar.Density.commonPortL_submatrix_eq b e X ω hD hS]
  have hH : (F - w • (1 : Matrix (Fin W) (Fin W) ℂ))ᴴ = F - star w • 1 := by
    rw [conjTranspose_sub, hF.eq, conjTranspose_smul, conjTranspose_one]
  have hu : IsUnit (F - star w • (1 : Matrix (Fin W) (Fin W) ℂ)).det := by
    rw [← hH, det_conjTranspose]
    exact (Collar.Density.isUnit_det_collarFW_sub hX hA hw).star
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, hH]
  simp only [mulVec_mulVec]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]

/-- **Pointwise distant bound.** For Hermitian end blocks and a simple middle Schur complement,
`Σ_ℓ P₁(λ_ℓ(Q))|y*u_ℓ|² ≤ π⁻¹(18‖L*q‖² + 4‖G z₀‖²)`, `z₀ = (L')*q`. -/
theorem spectralSum_one_le {b e : ℝ} (he : |e| < 2) (hb0 : 0 < b) (hb : b < 1 / 2)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {ω₁ : LayerSample W .common} (hA : ∀ k, (ω₁.1 k).IsHermitian)
    {G : Matrix (PortSite W .common) (PortSite W .common) ℂ}
    (hS : SimpleSpectrum (portSchurFin e X (ω₁, G))) (q : Fin 2 × Fin W → ℂ) :
    spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) (ω₁, G) ≤
      ENNReal.ofReal (Real.pi⁻¹ * (18 * ∑ a, ‖((commonPortL b e X ω₁)ᴴ *ᵥ q) a‖ ^ 2 +
        4 * ∑ a, ‖(Matrix.reindex (portEquiv W) (portEquiv W) G *ᵥ
          (((commonPortL b e X ω₁).submatrix id (Collar.Density.portEquiv W).symm)ᴴ *ᵥ q)) a‖
            ^ 2)) := by
  have hc : 0 < 1 - 2 * b := by linarith
  have hw_eq := Collar.Density.collarShiftW_eq (b := b) he.le
  have hwim : (Collar.Density.collarShiftW b e).im < 0 := by
    rw [hw_eq]
    have := BlockBand.Layers.matchedA_im_neg he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_neg_of_pos_of_neg hc this
  have hw1 : ‖Collar.Density.collarShiftW b e‖ ≤ 1 := by
    rw [hw_eq, norm_mul, BlockBand.Layers.norm_matchedA he.le, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hc]
    linarith
  have hk0 : ∀ x, 0 ≤ cauchyKernel 1 x := cauchyKernel_nonneg zero_le_one
  have hsum : spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) (ω₁, G) =
      ENNReal.ofReal (∑ ℓ, cauchyKernel 1 (freshEigenvalue (portSchurFin e X (ω₁, G)) ℓ) *
        ‖star ((Collar.Density.collarTW e X ω₁)ᴴ *ᵥ ((matchedLeadK b e X)ᴴ *ᵥ q)) ⬝ᵥ
          freshEigenvector (portSchurFin e X (ω₁, G)) ℓ‖ ^ 2) := by
    rw [spectralSum, ENNReal.ofReal_sum_of_nonneg fun ℓ _ => mul_nonneg (hk0 _) (sq_nonneg _)]
  rw [hsum, sum_cauchyKernel_one_eq hS]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 Real.pi_pos.le))
  by_cases hD : IsUnit (Collar.Density.collarTopBlock e X ω₁).det
  · rw [collarTW_conj_eq_frame hX hA hD hwim q, portSchurFin_eq e X ω₁ G]
    have hK : (Collar.Density.collarFW e X ω₁ +
        Matrix.reindex (portEquiv W) (portEquiv W) G).IsHermitian := by
      rw [← portSchurFin_eq e X ω₁ G]; exact hS.1
    have h := sum_norm_sq_inv_sub_I_le_frame hK hw1
      (((commonPortL b e X ω₁).submatrix id (Collar.Density.portEquiv W).symm)ᴴ *ᵥ q)
    rwa [Collar.Density.sum_norm_sq_conjTranspose_submatrix] at h
  · have hT : Collar.Density.collarTW e X ω₁ = 0 := by
      have : (Collar.Density.collarTopBlock e X ω₁)⁻¹ = 0 := nonsing_inv_apply_not_isUnit _ hD
      ext i j
      simp [Collar.Density.collarTW, Collar.Density.collarT, this]
    rw [hT]
    simp only [conjTranspose_zero, zero_mulVec, mulVec_zero, Pi.zero_apply, norm_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity

theorem lintegral_ofReal_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ ≤ ENNReal.ofReal (C ^ 2) := by
  rw [eLpNorm_eq_eLpNorm' (by simp) ENNReal.ofReal_ne_top hfm.aestronglyMeasurable,
    eLpNorm'_eq_lintegral_enorm] at h
  have h2 : (ENNReal.ofReal 2).toReal = 2 := by simp
  rw [h2] at h
  have hpt : ∀ ω, ‖f ω‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f ω ^ 2) := fun ω => by
    rw [Real.enorm_of_nonneg (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) (by norm_num)]
    norm_cast
  simp_rw [hpt] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)] at h'
  refine h'.trans (le_of_eq ?_)
  norm_cast

/-- The fresh Gaussian second moment through the port reindexing:
`E_G ‖Gz‖² = W(c/W)‖z‖²`. -/
theorem lintegral_norm_sq_reindex_mulVec (t : ℝ≥0) (z : Fin W → ℂ) :
    ∫⁻ G, ENNReal.ofReal (∑ a, ‖(Matrix.reindex (portEquiv W) (portEquiv W) G *ᵥ z) a‖ ^ 2)
        ∂gueMeasure (PortSite W .common) t =
      ENNReal.ofReal (W * t * ∑ a, ‖z a‖ ^ 2) := by
  have hm : Measurable fun G : Matrix (Fin W) (Fin W) ℂ =>
      ENNReal.ofReal (∑ a, ‖(G *ᵥ z) a‖ ^ 2) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun a _ => ?_)
    refine (Measurable.norm ?_).pow_const 2
    simp only [mulVec, dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply a)).mul_const _
  have h := lintegral_map hm (measurable_reindex_port (W := W)) (μ := gueMeasure (PortSite W .common) t)
  rw [BlockBand.Coarea.GUELaw.gueMeasure_map_reindex] at h
  rw [← h, lintegral_norm_sq_mulVec_gue]

/-- **The distant collar bound** (with the common-port mean moments and the fresh Gaussian
second moment): `E_collar Σ_ℓ P₁(λ_ℓ(Q))|(T*K*q)*u_ℓ|² ≤ C₁‖q‖²`, uniformly in
`W ≥ W₁`, `e ∈ bulkInterval κ`, Hermitian `X` (no norm bound, no distance bound) and `q`. -/
theorem lintegral_spectralSum_one_le (hCM : CommonPortMeanContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C₁ : ℝ) (W₁ : ℕ), 0 ≤ C₁ ∧ ∀ W : ℕ, 0 < W → W₁ ≤ W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        ∀ q : Fin 2 × Fin W → ℂ,
          ∫⁻ ω, spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) ω
              ∂collarLaw W b ≤ ENNReal.ofReal (C₁ * ∑ a, ‖q a‖ ^ 2) := by
  obtain ⟨C, W₁, hmom⟩ := hCM.moments b hb0 hb κ hκ 2 (by norm_num)
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hpi := Real.pi_pos
  refine ⟨Real.pi⁻¹ * 22 * C' ^ 2, W₁, by positivity, ?_⟩
  intro W hW hW₁ e he X hX q
  have he2 : |e| < 2 := BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have hWt : (W : ℝ) * t ≤ 1 := by
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    rw [Real.coe_toNNReal _ (div_nonneg hc0 hWr.le), mul_div_cancel₀ _ hWr.ne']
    linarith
  have hWt0 : 0 ≤ (W : ℝ) * t := by positivity
  set nq := ∑ a, ‖q a‖ ^ 2
  have hnq : 0 ≤ nq := by positivity
  set nL : LayerSample W .common → ℝ := fun ω₁ =>
    ∑ a, ‖((commonPortL b e X ω₁)ᴴ *ᵥ q) a‖ ^ 2 with hnL
  have hnL0 : ∀ ω₁, 0 ≤ nL ω₁ := fun ω₁ => by positivity
  set z₀ : LayerSample W .common → Fin W → ℂ := fun ω₁ =>
    ((commonPortL b e X ω₁).submatrix id (Collar.Density.portEquiv W).symm)ᴴ *ᵥ q
  have hz₀ : ∀ ω₁, ∑ a, ‖z₀ ω₁ a‖ ^ 2 = nL ω₁ := fun ω₁ =>
    Collar.Density.sum_norm_sq_conjTranspose_submatrix _ q
  -- the `G`-integral
  have hG : ∀ ω₁ : LayerSample W .common, (∀ k, (ω₁.1 k).IsHermitian) →
      ∫⁻ G, spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) (ω₁, G)
        ∂gueMeasure (PortSite W .common) t ≤ ENNReal.ofReal (Real.pi⁻¹ * 22 * nL ω₁) := by
    intro ω₁ hA
    have hgm : Measurable fun G : Matrix (PortSite W .common) (PortSite W .common) ℂ =>
        ENNReal.ofReal (∑ a, ‖(Matrix.reindex (portEquiv W) (portEquiv W) G *ᵥ z₀ ω₁) a‖ ^ 2) := by
      refine ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun a _ => ?_)
      refine (Measurable.norm ?_).pow_const 2
      simp only [mulVec, dotProduct, reindex_apply, submatrix_apply]
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply _).comp (measurable_pi_apply _)).mul_const _
    calc ∫⁻ G, spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) (ω₁, G)
          ∂gueMeasure (PortSite W .common) t
        ≤ ∫⁻ G, (ENNReal.ofReal (Real.pi⁻¹ * 18 * nL ω₁) + ENNReal.ofReal (Real.pi⁻¹ * 4) *
            ENNReal.ofReal (∑ a, ‖(Matrix.reindex (portEquiv W) (portEquiv W) G *ᵥ z₀ ω₁) a‖
              ^ 2)) ∂gueMeasure (PortSite W .common) t := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_port_good hb hW e 0 X hX ω₁ hA] with G hGd
          refine (spectralSum_one_le he2 hb0 hb hX hA hGd.2 q).trans (le_of_eq ?_)
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          ring
      _ = ENNReal.ofReal (Real.pi⁻¹ * 18 * nL ω₁) + ENNReal.ofReal (Real.pi⁻¹ * 4) *
            ENNReal.ofReal (W * t * nL ω₁) := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul _ hgm,
            lintegral_norm_sq_reindex_mulVec, hz₀]
          simp only [lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (Real.pi⁻¹ * 22 * nL ω₁) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : Real.pi⁻¹ * 4 * (W * t * nL ω₁) ≤ Real.pi⁻¹ * 4 * nL ω₁ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith [hnL0 ω₁]
          linarith
  have hP : IsProbabilityMeasure (layerLaw W b .common) := by unfold layerLaw; infer_instance
  have hLm := BlockBand.Critical.CommonPort.measurable_commonPortL (W := W) b e X
  have hnLm : Measurable fun ω => ‖commonPortL b e X ω‖ := continuous_norm.measurable.comp hLm
  have hmom2 := lintegral_ofReal_sq_le hnLm (fun ω => norm_nonneg _) hC'
    (((hmom W hW hW₁ X hX e he).1).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hmeas := measurable_spectralSum (W := W) (measurable_cauchyKernel 1) e X
    ((matchedLeadK b e X)ᴴ *ᵥ q)
  calc ∫⁻ ω, spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) ω ∂collarLaw W b
      = ∫⁻ ω₁, ∫⁻ G, spectralSum (cauchyKernel 1) e X ((matchedLeadK b e X)ᴴ *ᵥ q) (ω₁, G)
          ∂gueMeasure (PortSite W .common) t ∂layerLaw W b .common := by
        unfold collarLaw
        exact lintegral_prod _ hmeas.aemeasurable
    _ ≤ ∫⁻ ω₁, ENNReal.ofReal (Real.pi⁻¹ * 22 * nq) *
          ENNReal.ofReal (‖commonPortL b e X ω₁‖ ^ 2) ∂layerLaw W b .common := by
        refine lintegral_mono_ae ?_
        filter_upwards [BlockBand.Layers.lct_ae_blocks_isHermitian W b .common] with ω₁ hA
        refine (hG ω₁ hA).trans ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := Collar.Density.sumsq_mulVec_le_opNorm (commonPortL b e X ω₁)ᴴ q
        rw [Matrix.l2_opNorm_conjTranspose] at h
        have : Real.pi⁻¹ * 22 * nL ω₁ ≤ Real.pi⁻¹ * 22 * (‖commonPortL b e X ω₁‖ ^ 2 * nq) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        linarith
    _ = ENNReal.ofReal (Real.pi⁻¹ * 22 * nq) *
          ∫⁻ ω₁, ENNReal.ofReal (‖commonPortL b e X ω₁‖ ^ 2) ∂layerLaw W b .common :=
        lintegral_const_mul _ (hnLm.pow_const 2).ennreal_ofReal
    _ ≤ ENNReal.ofReal (Real.pi⁻¹ * 22 * nq) * ENNReal.ofReal (C' ^ 2) := by gcongr
    _ = ENNReal.ofReal (Real.pi⁻¹ * 22 * C' ^ 2 * nq) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Collar

end BlockBand.Critical.MatrixClosing.Mean
