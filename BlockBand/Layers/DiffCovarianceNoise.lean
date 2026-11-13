module

public import BlockBand.Layers.DiffCovarianceFactors

/-!
# Fluctuation of the differentiated trace

The noise clause of the differentiated-covariance lemma: for `ġ_i = -W⁻¹ Tr P_i 𝒢 Ŝ 𝒢`,
`‖ġ_i - E(ġ_i | X,S)‖_p ≤ C_p W^{-3/2} ‖Y‖_HS ≤ C_p u/√W`. The gradient of `ġ_i` in the fresh
Gaussian entries contains one source insertion in each of its two terms; factoring it as in the
covariance factorization bounds its Hilbert–Schmidt norm by `C_p W⁻¹ ‖Y‖_HS`, and the variance
`O(W⁻¹)` of the entries gives a further factor `W^{-1/2}`.

Setting. `layerLaw W b σ` (fresh layer only; conditioning on the old path is the deterministic
`X`, `S`), a deterministic direction `P` of `𝒢⁻¹` (the source `Ŝ`, or `Ŝ + D₀`), a deterministic
`D` with `‖D‖ ≤ 1` (the block projection `P_i`, `‖P_i‖ ≤ 1`), `ġ = -W⁻¹ Tr(D 𝒢 P 𝒢)`. Norms:
`ℓ²` operator norm; `dcvHS` the squared Hilbert–Schmidt norm; `L^p` norms are `eLpNorm`.

Proof.
1. **Regularization.** `G_κ = (𝒢⁻¹ + iκ)⁻¹` (`tcvG`), `f_κ = -W⁻¹ Tr(D G_κ P G_κ)` (`dcvF`) is
   `C¹` with `∂ᵢ f_κ = W⁻¹ Tr(M Λᵢ)`, `M = T D G_κ + G_κ D T`, `T = G_κ P G_κ`
   (`dcvF_fderiv`).
2. **Gradient** (`dcvF_gradient_le`). With the factorization hypothesis
   `‖G P G‖²_HS ≤ s₂ Θ(G)⁴` for every `G` (`dcv_factor_hs_le`, `dcv_dir_hs_le`),
   `‖M‖²_HS ≤ 4 s₂ Θ(G_κ)⁶`, and `tfl_weighted_trace_le` (`t_A, t_B ≤ 1/W`) gives
   `|∇f_κ| ≤ 4 √s₂ Θ(G_κ)³ / (W √W)`.
3. **`L^p` step and `κ → 0`** (`dcv_noise_core`). `Inputs.GaussianLpGradient`, `Θ(G_κ) ≤ 2Θ(𝒢)`
   a.s. (`dcv_theta_reg_layer`) and `‖Θ(𝒢)³‖_p = ‖Θ(𝒢)‖_{3p}³` give the bound for each `κ`;
   `f_κ → ġ` a.s., dominated convergence for the mean and Fatou for the `L^p` norm.
4. **The clause** (`dcv_noise_clause`): `s₂ = Re Tr Y²` for `P = Ŝ` and
   `s₂ = 2 Re Tr Y² + 8W ‖D₀‖²` for `P = Ŝ + D₀`; `√(Re Tr Y²) ≤ Re Tr Y = W u`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient
  ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The regularized derivative trace in the real coordinates
-/

section Coordinates

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

/-- `|W⁻¹ Tr(D N)| ≤ 4 ‖D‖ ‖N‖`. -/
theorem dcv_traceCLM_le {W : ℕ} (hW : 0 < W) (D N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖tflTraceCLM W σ D N‖ ≤ 4 * ‖D‖ * ‖N‖ := by
  have h := tcv_tr_le σ hW (D * N)
  rw [tcvTr_apply] at h
  rw [tflTraceCLM_apply]
  calc _ ≤ 4 * ‖D * N‖ := h
    _ ≤ 4 * (‖D‖ * ‖N‖) := by gcongr; exact norm_mul_le _ _
    _ = 4 * ‖D‖ * ‖N‖ := by ring

variable {X} in
/-- `d(G P G)(v) = -(G (Λv) (G P G) + (G P G) (Λv) G)` for `G = G_κ`. -/
theorem dcv_T_hasFDerivAt (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (x : TflCoord W σ → ℝ) :
    ∃ T : (TflCoord W σ → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      HasFDerivAt (fun y => tcvG W b σ E z X κ y * P * tcvG W b σ E z X κ y) T x ∧
        ∀ v, T v = -(tcvG W b σ E z X κ x * tcvLam W b σ v *
            (tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x) +
          (tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x) * tcvLam W b σ v *
            tcvG W b σ E z X κ x) := by
  obtain ⟨TG, hTG, hTGv⟩ := tcv_G_hasFDerivAt W b σ E z hX hz hκ x
  have h1 := (hTG.mul' (hasFDerivAt_const P x)).mul' hTG
  refine ⟨_, h1, fun v => ?_⟩
  simp only [_root_.add_apply, _root_.smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, smul_eq_mul, _root_.zero_apply, hTGv, Pi.mul_apply]
  noncomm_ring

/-- The regularized differentiated trace `f_κ = -W⁻¹ Tr(D G_κ P G_κ)`. -/
def dcvF (D P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (κ : ℝ) (x : TflCoord W σ → ℝ) : ℂ :=
  -(tflTraceCLM W σ D (tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x))

variable {X} in
theorem dcvF_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (D P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (dcvF W b σ E z X D P κ) := by
  have hG := tcv_G_contDiff W b σ E z hX hz hκ
  exact ((tflTraceCLM W σ D).contDiff.comp ((hG.mul contDiff_const).mul hG)).neg

variable {X} in
/-- `∂_v f_κ = W⁻¹ Tr(M Λv)`, `M = T D G + G D T`, `T = G P G`. -/
theorem dcvF_fderiv (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (D P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {κ : ℝ} (hκ : 0 < κ)
    (x v : TflCoord W σ → ℝ) :
    fderiv ℝ (dcvF W b σ E z X D P κ) x v =
      (W : ℂ)⁻¹ * (((tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x) * D *
          tcvG W b σ E z X κ x + tcvG W b σ E z X κ x * D *
          (tcvG W b σ E z X κ x * P * tcvG W b σ E z X κ x)) * tcvLam W b σ v).trace := by
  obtain ⟨T', hT', hT'v⟩ := dcv_T_hasFDerivAt W b σ E z hX hz hκ P x
  have hf : HasFDerivAt (dcvF W b σ E z X D P κ) (-((tflTraceCLM W σ D).comp T')) x :=
    ((tflTraceCLM W σ D).hasFDerivAt.comp x hT').neg
  rw [hf.fderiv]
  set G := tcvG W b σ E z X κ x
  set T := G * P * G
  set L := tcvLam W b σ v
  simp only [_root_.neg_apply, ContinuousLinearMap.comp_apply, hT'v, tflTraceCLM_apply]
  rw [Matrix.mul_neg, trace_neg, mul_neg, neg_neg]
  congr 1
  rw [Matrix.mul_add, trace_add, Matrix.add_mul, trace_add]
  congr 1
  · rw [show D * (G * L * T) = (D * G * L) * T by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show T * (D * G * L) = T * D * G * L by simp only [Matrix.mul_assoc]]
  · rw [show D * (T * L * G) = (D * T * L) * G by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show G * (D * T * L) = G * D * T * L by simp only [Matrix.mul_assoc]]

variable {X W b} in
/-- **Gradient bound**: if `‖G P G‖²_HS ≤ s₂ Θ(G)⁴` for every `G` and
`‖D‖ ≤ 1`, then `(Σᵢ vᵢ |∂ᵢ f_κ|²)^{1/2} ≤ 4 √s₂ Θ(G_κ)³ / (W √W)`. -/
theorem dcvF_gradient_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hD : ‖D‖ ≤ 1)
    (P Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {s2 : ℝ} (hs2 : 0 ≤ s2)
    (hP : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      dcvHS (G * P * G) ≤ s2 * dcvTheta Kh G ^ 4) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) :
    weightedGradientNorm (tflVar W b σ) (dcvF W b σ E z X D P κ) x ≤
      4 * Real.sqrt s2 / (W * Real.sqrt W) * dcvTheta Kh (tcvG W b σ E z X κ x) ^ 3 := by
  set G := tcvG W b σ E z X κ x with hG
  set T := G * P * G with hT
  set M := T * D * G + G * D * T with hM
  set Θ := dcvTheta Kh G with hΘ
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hΘ0 : 0 ≤ Θ := dcvTheta_nonneg Kh G
  have hGΘ : ‖G‖ ≤ Θ := dcv_norm_le_theta Kh G
  have hder : ∀ i : TflCoord W σ, ‖fderiv ℝ (dcvF W b σ E z X D P κ) x (Pi.single i 1)‖ ^ 2 =
      ((W : ℝ)⁻¹) ^ 2 * ‖(M * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 := by
    intro i
    rw [dcvF_fderiv W b σ E z hX hz D P hκ, ← hG, tcvLam_apply, norm_mul, mul_pow, norm_inv,
      Complex.norm_natCast]
  -- the Hilbert–Schmidt bound on `M`
  have hDG : ‖D * G‖ ≤ ‖G‖ := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg G, norm_nonneg D])
  have hGD : ‖G * D‖ ≤ ‖G‖ := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg G, norm_nonneg D])
  have hTs := hP G
  have hG2 : ‖G‖ ^ 2 ≤ Θ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hGΘ 2
  have hHT := dcvHS_nonneg T
  have h1 : dcvHS (T * D * G) ≤ dcvHS T * ‖G‖ ^ 2 := by
    rw [Matrix.mul_assoc]
    refine (dcvHS_mul_right_le T (D * G)).trans ?_
    gcongr
  have h2 : dcvHS (G * D * T) ≤ ‖G‖ ^ 2 * dcvHS T := by
    refine (dcvHS_mul_left_le (G * D) T).trans ?_
    gcongr
  have hMs : dcvHS M ≤ 4 * s2 * Θ ^ 6 := by
    have h3 := dcvHS_add_le (T * D * G) (G * D * T)
    have h4 : dcvHS T * ‖G‖ ^ 2 ≤ s2 * Θ ^ 4 * Θ ^ 2 := by
      have := mul_le_mul hTs hG2 (by positivity) (by positivity)
      linarith
    nlinarith
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
    have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
    rw [this]; linarith
  have hsum : ∑ i, (tflVar W b σ i : ℝ) *
      ‖fderiv ℝ (dcvF W b σ E z X D P κ) x (Pi.single i 1)‖ ^ 2 ≤
      (4 * Real.sqrt s2 / (W * Real.sqrt W) * Θ ^ 3) ^ 2 := by
    simp_rw [hder]
    have e : ∑ i, (tflVar W b σ i : ℝ) * (((W : ℝ)⁻¹) ^ 2 *
        ‖(M * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2) = ((W : ℝ)⁻¹) ^ 2 *
        ∑ i, (tflVar W b σ i : ℝ) * ‖(M * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have hw := tfl_weighted_trace_le W b σ M
    have hM0 : 0 ≤ dcvHS M := dcvHS_nonneg M
    have hcoef : 0 ≤ 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) := by positivity
    have hstep : ∑ i, (tflVar W b σ i : ℝ) * ‖(M * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 ≤
        4 / W * (4 * s2 * Θ ^ 6) := by
      refine hw.trans ?_
      change (2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ)) * dcvHS M ≤ _
      exact mul_le_mul hc hMs hM0 (by positivity)
    have hsq : (4 * Real.sqrt s2 / (W * Real.sqrt W) * Θ ^ 3) ^ 2 =
        ((W : ℝ)⁻¹) ^ 2 * (4 / W * (4 * s2 * Θ ^ 6)) := by
      have hsW : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW'.le
      have hss : Real.sqrt s2 ^ 2 = s2 := Real.sq_sqrt hs2
      have hsW0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW'
      field_simp
      rw [hsW, hss]
      ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  unfold weightedGradientNorm
  calc Real.sqrt (∑ i, (tflVar W b σ i : ℝ) *
        ‖fderiv ℝ (dcvF W b σ E z X D P κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt ((4 * Real.sqrt s2 / (W * Real.sqrt W) * Θ ^ 3) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 4 * Real.sqrt s2 / (W * Real.sqrt W) * Θ ^ 3 := Real.sqrt_sq (by positivity)

end Coordinates

/-!
## 2. The noise bound for one direction
-/

/-- Integrability of integer powers from an `L^r` bound (`m ≤ r`, probability measure). -/
theorem dcv_integrable_pow {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {r C : ℝ}
    (h : eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal C) {m : ℕ} (hm1 : 1 ≤ m)
    (hmr : (m : ℝ) ≤ r) : Integrable (fun ω => ‖f ω‖ ^ m) μ := by
  have hmem : MemLp f (ENNReal.ofReal r) μ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hle : (m : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hmr
  have hmem' : MemLp f (m : ℝ≥0∞) μ := hmem.mono_exponent hle
  exact hmem'.integrable_norm_pow (by omega)

/-- **Core noise bound** in the coordinates, transferred to `layerLaw`: from the gradient
inequality (constant `Cg`), a.e. invertibility, the factorization hypothesis
`‖G P G‖²_HS ≤ s₂ Θ(G)⁴` and `‖Θ(𝒢)‖_{3p} ≤ C_Θ`:
`‖ġ - Eġ‖_p ≤ Cg √p (4 √s₂ / (W √W)) (8 C_Θ³)`, `ġ = -W⁻¹ Tr(D 𝒢 P 𝒢)`. -/
theorem dcv_noise_core {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (σ : LayerShape)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ) {z : ℂ}
    (hz : 0 ≤ z.im) {D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hD : ‖D‖ ≤ 1)
    (P Kh : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {s2 : ℝ} (hs2 : 0 ≤ s2)
    (hP : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      dcvHS (G * P * G) ≤ s2 * dcvTheta Kh G ^ 4) {p : ℝ} (hp : 1 ≤ p)
    {CT : ℝ} (hCT : 0 ≤ CT)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hmom : eLpNorm (fun ω => dcvTheta Kh (layerResolvent σ E z X ω)) (ENNReal.ofReal (3 * p))
      (layerLaw W b σ) ≤ ENNReal.ofReal CT) :
    eLpNorm (fun ω => -((W : ℂ)⁻¹ * (D * (layerResolvent σ E z X ω * P *
          layerResolvent σ E z X ω)).trace) -
        ∫ ω', -((W : ℂ)⁻¹ * (D * (layerResolvent σ E z X ω' * P *
          layerResolvent σ E z X ω')).trace) ∂layerLaw W b σ)
        (ENNReal.ofReal p) (layerLaw W b σ) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (4 * Real.sqrt s2 / (W * Real.sqrt W)) *
        (8 * CT ^ 3)) := by
  set μ := gaussianProduct (tflVar W b σ) with hμ
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μ.map Φ := tfl_layerLaw_eq_map W b σ
  set φ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ → ℂ := fun N => -(tflTraceCLM W σ D (N * P * N))
    with hφ
  have hφc : Continuous φ :=
    ((tflTraceCLM W σ D).continuous.comp ((continuous_id.mul continuous_const).mul
      continuous_id)).neg
  set f : LayerSample W σ → ℂ := fun ω => φ (layerResolvent σ E z X ω) with hfdef
  have hf : Measurable f := hφc.measurable.comp (measurable_layerResolvent σ E z X)
  change eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b σ) (ENNReal.ofReal p)
    (layerLaw W b σ) ≤ _
  set F : (TflCoord W σ → ℝ) → ℂ := fun x => f (Φ x) with hFdef
  have hF : Measurable F := hf.comp hΦ
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hGr : Measurable Gr := (measurable_layerResolvent σ E z X).comp hΦ
  have htransfer : eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂layerLaw W b σ) (ENNReal.ofReal p)
      (layerLaw W b σ) = eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ := by
    rw [hlaw, integral_map hΦ.aemeasurable hf.aestronglyMeasurable,
      eLpNorm_map_measure (hf.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
    rfl
  rw [htransfer]
  have hp0 : 0 ≤ p := by linarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hinvμ : ∀ᵐ x ∂μ, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  set Θr : (TflCoord W σ → ℝ) → ℝ := fun x => dcvTheta Kh (Gr x) with hΘr
  have hΘrm : Measurable Θr := (dcv_continuous_theta Kh).measurable.comp hGr
  have hΘr0 : ∀ x, 0 ≤ Θr x := fun x => dcvTheta_nonneg Kh (Gr x)
  have hmomμ : eLpNorm Θr (ENNReal.ofReal (3 * p)) μ ≤ ENNReal.ofReal CT := by
    have hm : Measurable (fun ω => dcvTheta Kh (layerResolvent σ E z X ω)) :=
      (dcv_continuous_theta Kh).measurable.comp (measurable_layerResolvent σ E z X)
    rw [hlaw, eLpNorm_map_measure hm.aestronglyMeasurable hΦ.aemeasurable] at hmom
    exact hmom
  -- the cube moment: `‖Θ³‖_p ≤ C_Θ³`
  have hcube : eLpNorm (fun x => Θr x ^ 3) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (CT ^ 3) := by
    have e1 : (fun x => Θr x ^ 3) = fun x => ‖Θr x‖ ^ (3 : ℝ) := by
      funext x; rw [Real.norm_of_nonneg (hΘr0 x), ← Real.rpow_natCast]; norm_num
    rw [e1, eLpNorm_norm_rpow Θr hΘrm.aestronglyMeasurable (by norm_num : (0 : ℝ) < 3),
      ← ENNReal.ofReal_mul hp0, mul_comm p 3, ENNReal.ofReal_pow hCT]
    calc eLpNorm Θr (ENNReal.ofReal (3 * p)) μ ^ (3 : ℝ) ≤ ENNReal.ofReal CT ^ (3 : ℝ) :=
          ENNReal.rpow_le_rpow hmomμ (by norm_num)
      _ = ENNReal.ofReal CT ^ 3 := by rw [← ENNReal.rpow_natCast]; norm_num
  set c : ℝ := 4 * Real.sqrt s2 / (W * Real.sqrt W) with hc
  have hc0 : 0 ≤ c := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p * c * (8 * CT ^ 3)) with hB
  -- the bound for each regularization `κ > 0`
  have hstep : ∀ κ : ℝ, 0 < κ →
      eLpNorm (fun x => dcvF W b σ E z X D P κ x - ∫ y, dcvF W b σ E z X D P κ y ∂μ)
        (ENNReal.ofReal p) μ ≤ B := by
    intro κ hκ
    have hC := dcvF_contDiff W b σ E z hX hz D P hκ
    have hcont : Continuous (dcvF W b σ E z X D P κ) := hC.continuous
    have hmem : MemLp (dcvF W b σ E z X D P κ) (ENNReal.ofReal p) μ := by
      refine MemLp.of_bound hcont.aestronglyMeasurable (4 * ‖D‖ * (κ⁻¹ * ‖P‖ * κ⁻¹))
        (ae_of_all _ fun x => ?_)
      rw [dcvF, norm_neg]
      refine (dcv_traceCLM_le σ hW D _).trans ?_
      have hG := tcv_G_le W b σ E z hX hz hκ x
      gcongr
      refine (norm_mul_le _ _).trans ?_
      gcongr
      exact (norm_mul_le _ _).trans (by gcongr)
    have h1 := hgr p hp (TflCoord W σ) (tflVar W b σ) (dcvF W b σ E z X D P κ) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm (tflVar W b σ) (dcvF W b σ E z X D P κ)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm (tflVar W b σ) (dcvF W b σ E z X D P κ) x‖ ≤
        ‖(8 * c) * Θr x ^ 3‖ := by
      filter_upwards [hinvμ] with x hx
      have hg := dcvF_gradient_le σ E z hW hb0 hb1 hX hz hD P Kh hs2 hP hκ x
      have h2 : dcvTheta Kh (tcvG W b σ E z X κ x) ≤ 2 * Θr x := by
        rw [tcvG, tflPsi_inv_eq]
        exact dcv_theta_reg_layer σ E hX _ (tflEmbed_blockDiag_isHermitian W b σ x) hz hκ hx Kh
      have hg0 : 0 ≤ weightedGradientNorm (tflVar W b σ) (dcvF W b σ E z X D P κ) x :=
        Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg (by have := hΘr0 x; positivity)]
      refine hg.trans ?_
      have h3 : dcvTheta Kh (tcvG W b σ E z X κ x) ^ 3 ≤ (2 * Θr x) ^ 3 :=
        pow_le_pow_left₀ (dcvTheta_nonneg _ _) h2 3
      calc c * dcvTheta Kh (tcvG W b σ E z X κ x) ^ 3 ≤ c * (2 * Θr x) ^ 3 := by gcongr
        _ = 8 * c * Θr x ^ 3 := by ring
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => (8 * c) * Θr x ^ 3) (ENNReal.ofReal p) μ =
        ENNReal.ofReal (8 * c) * eLpNorm (fun x => Θr x ^ 3) (ENNReal.ofReal p) μ := by
      rw [show (fun x => (8 * c) * Θr x ^ 3) = (8 * c) • (fun x => Θr x ^ 3) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    calc ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm (tflVar W b σ) (dcvF W b σ E z X D P κ))
            (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal (8 * c) *
            ENNReal.ofReal (CT ^ 3)) := by
          gcongr
          exact h4.trans (h5.le.trans (by gcongr))
      _ = B := by
          rw [hB, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  -- the limit `κ = 1/(m+1) → 0`
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Fm : ℕ → (TflCoord W σ → ℝ) → ℂ := fun m => dcvF W b σ E z X D P (κm m) with hFm
  have hFmc : ∀ m, Continuous (Fm m) := fun m =>
    (dcvF_contDiff W b σ E z hX hz D P (hκpos m)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x) atTop (𝓝 (F x)) := by
    filter_upwards [hinvμ] with x hx
    have h1 := tcv_G_tendsto σ E z hx hκlim (b := b)
    exact (hφc.tendsto _).comp h1
  -- domination by `16 ‖P‖ ‖𝒢‖² ≤ 16 ‖P‖ Θ²`
  have hΘ2 : Integrable (fun x => ‖Θr x‖ ^ 2) μ :=
    dcv_integrable_pow hmomμ (by norm_num) (by push_cast; linarith)
  have hbound : ∀ m, ∀ᵐ x ∂μ, ‖Fm m x‖ ≤ 16 * ‖P‖ * ‖Θr x‖ ^ 2 := by
    intro m
    filter_upwards [hinvμ] with x hx
    have h2 := tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
    have h3 : ‖Gr x‖ ≤ ‖Θr x‖ := by
      rw [Real.norm_of_nonneg (hΘr0 x)]; exact dcv_norm_le_theta Kh (Gr x)
    have hGm : ‖tcvG W b σ E z X (κm m) x‖ ≤ 2 * ‖Θr x‖ := by
      rw [tcvG]; exact h2.trans (by gcongr)
    have hGm0 := norm_nonneg (tcvG W b σ E z X (κm m) x)
    simp only [hFm, dcvF, norm_neg]
    refine (dcv_traceCLM_le σ hW D _).trans ?_
    have hT : ‖tcvG W b σ E z X (κm m) x * P * tcvG W b σ E z X (κm m) x‖ ≤
        ‖tcvG W b σ E z X (κm m) x‖ * ‖P‖ * ‖tcvG W b σ E z X (κm m) x‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) hGm0)
    have hP0 := norm_nonneg P
    calc 4 * ‖D‖ * ‖tcvG W b σ E z X (κm m) x * P * tcvG W b σ E z X (κm m) x‖
        ≤ 4 * 1 * (‖tcvG W b σ E z X (κm m) x‖ * ‖P‖ * ‖tcvG W b σ E z X (κm m) x‖) := by
          gcongr
      _ ≤ 4 * 1 * ((2 * ‖Θr x‖) * ‖P‖ * (2 * ‖Θr x‖)) := by gcongr
      _ = 16 * ‖P‖ * ‖Θr x‖ ^ 2 := by ring
  have hint : Tendsto (fun m => ∫ x, Fm m x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => 16 * ‖P‖ * ‖Θr x‖ ^ 2)
      (fun m => (hFmc m).aestronglyMeasurable) (hΘ2.const_mul _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x - ∫ y, Fm m y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun m => ((hFmc m).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  exact (hstep (κm m) (hκpos m)).trans (le_of_eq (by rw [hB]))

/-!
## 3. The derivative-noise bound and its insertion variant
-/

/-- `|LayerSite W .separate| = 4W`. -/
theorem dcv_card_layerSite (W : ℕ) : (Fintype.card (LayerSite W .separate) : ℝ) = 4 * W := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, LayerShape.blocks,
    LayerShape.ports]
  push_cast; ring

/-- Elementary bound for the insertion variant:
`A s / (w² w) ≤ A (2 + 3K) (1 + u) / w` when `s ≤ 2w²u + 3wK`, `w ≥ 1`. -/
theorem dcv_noise_arith {A u K w s : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) (hK : 0 ≤ K) (hw : 1 ≤ w)
    (hsle : s ≤ 2 * w ^ 2 * u + 3 * w * K) :
    A * s / (w ^ 2 * w) ≤ A * (2 + 3 * K) * (1 + u) / w := by
  have hw0 : 0 < w := by linarith
  rw [div_le_div_iff₀ (by positivity) hw0]
  have h1 : s ≤ (2 + 3 * K) * (1 + u) * w ^ 2 := by
    have hww : w ≤ w ^ 2 := by nlinarith
    have : 3 * w * K ≤ 3 * w ^ 2 * K := by nlinarith [mul_le_mul_of_nonneg_left hww hK]
    nlinarith [mul_nonneg hK hu, sq_nonneg w]
  have h2 : A * s ≤ A * ((2 + 3 * K) * (1 + u) * w ^ 2) := mul_le_mul_of_nonneg_left h1 hA
  nlinarith [mul_le_mul_of_nonneg_right h2 hw0.le]

/-- `√s₂ ≤ 2w²u + 3wK` for `s₂ = 2a + 8WK²`, `√a ≤ Wu`, `W = w²`, `w ≥ 1`. -/
theorem dcv_sqrt_arith {a s2 W u w K : ℝ} (ha0 : 0 ≤ a) (hu : 0 ≤ u) (hK : 0 ≤ K) (hw1 : 1 ≤ w)
    (hww : W = w ^ 2) (hsa : Real.sqrt a ≤ W * u) (hs2 : s2 = 2 * a + 2 * (4 * W * K ^ 2)) :
    Real.sqrt s2 ≤ 2 * w ^ 2 * u + 3 * w * K := by
  have hw0 : 0 ≤ w := by linarith
  rw [Real.sqrt_le_left (by positivity)]
  have ha2 : a ≤ (W * u) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg a) hsa 2
    rwa [Real.sq_sqrt ha0] at this
  subst hs2 hww
  nlinarith [mul_nonneg (mul_nonneg hw0 hu) hK, sq_nonneg w, sq_nonneg K,
    mul_nonneg (mul_nonneg (mul_nonneg hw0 hw0) hw0) (mul_nonneg hu hK)]

/-- **The derivative-noise bound** with the pointwise derivative and the insertion variant
(the noise half of `DiffCovarianceStatement`; see that docstring for the full statement). -/
theorem dcv_noise_clause (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hwl : WeightedLayerContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∀ K₀ p : ℝ, 1 ≤ p → ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
    ∀ E ∈ bulkInterval κ,
    ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
    ∀ D₀ : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D₀‖ ≤ K₀ →
      let μ := layerLaw W b .separate
      let z := boundaryZ b E
      let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Y := (K⁻¹)ᴴ * S * K⁻¹
      let u := (W : ℝ)⁻¹ * Y.trace.re
      let G := fun ω => layerResolvent .separate E z X ω
      let gdot := fun (P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) ω =>
        -((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)
      (∀ᵐ ω ∂μ, HasDerivAt (fun h : ℝ =>
          (W : ℂ)⁻¹ * (D * layerResolvent .separate E z (X - (h : ℂ) • S) ω).trace)
        (gdot (dcvHat S) ω) 0) ∧
      eLpNorm (fun ω => gdot (dcvHat S) ω - ∫ ω', gdot (dcvHat S) ω' ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp / (W * Real.sqrt W) * Real.sqrt (Y * Y).trace.re) ∧
      Cp / (W * Real.sqrt W) * Real.sqrt (Y * Y).trace.re ≤ Cp * u / Real.sqrt W ∧
      eLpNorm (fun ω => gdot (dcvHat S + D₀) ω - ∫ ω', gdot (dcvHat S + D₀) ω' ∂μ)
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp * (1 + u) / Real.sqrt W) := by
  intro b hb0 hb1 κ hκ K₀ p hp
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  obtain ⟨CT, W₀, hCT, hT⟩ := dcv_theta_eLpNorm hcount hwl hb0 hb1 hκ (q := 3 * p) (by linarith)
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  set K₁ := max K₀ 0 with hK₁
  have hK₁0 : 0 ≤ K₁ := le_max_right _ _
  set A := 32 * Cg * Real.sqrt p * CT ^ 3 with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A * (2 + 3 * K₁), W₀, ?_⟩
  intro W hW hWW X S hX hS E hE D hD D₀ hD₀ μ z K Y u G gdot
  obtain ⟨hzim, hzM, -⟩ := hbulk E hE
  have hzpos : 0 < z.im := lt_of_lt_of_le hη₀ hzim
  have hinv := (habs W hW .separate X hX E z hzim hzM).1
  have hKu : IsUnit K.det := dcv_K_isUnit hX hzpos
  have hSY : S = Kᴴ * Y * K := dcv_source_eq hKu
  have hYp : Y.PosSemidef := dcv_Y_posSemidef hS
  obtain ⟨hY0, -, hYhs, hYe⟩ := dcv_Y_bounds hYp
  have hmom := hT W hW hWW X hX E hE
  have hShat : (dcvHat S : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) =
      (dcvKh K)ᴴ * dcvHat Y * dcvKh K := dcv_hat_source_eq hSY
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set w := Real.sqrt (W : ℝ) with hw
  have hw1 : 1 ≤ w := by rw [hw]; exact Real.one_le_sqrt.mpr hW1
  have hww : (W : ℝ) = w ^ 2 := (Real.sq_sqrt hW'.le).symm
  have hu0 : 0 ≤ u := mul_nonneg (inv_nonneg.mpr hW'.le) hY0
  have hWu : Y.trace.re = W * u := by
    change Y.trace.re = W * ((W : ℝ)⁻¹ * Y.trace.re)
    field_simp
  set a := (Y * Y).trace.re with ha
  have ha0 : 0 ≤ a := by have := dcvHS_nonneg Y; rw [hYe] at this; exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the pointwise derivative
    filter_upwards [hinv] with ω hω
    have h := dcv_hasDerivAt_resolvent .separate E z X S ω hω
    have h2 := (tflTraceCLM W .separate D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    convert h2 using 1
    · rfl
    · rw [tflTraceCLM_apply, Matrix.mul_neg, trace_neg, mul_neg]
  · -- the main bound
    have hP : ∀ Gm : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        dcvHS (Gm * dcvHat S * Gm) ≤ a * dcvTheta (dcvKh K) Gm ^ 4 := fun Gm => by
      rw [hShat]
      have := dcv_factor_hs_le (dcvKh K) (dcvHat Y) Gm
      rwa [dcvHS_hat, hYe] at this
    have hc := dcv_noise_core hCg.le hgr hW hb0 hb1 .separate hX E hzpos.le hD (dcvHat S) (dcvKh K)
      ha0 hP hp hCT hinv hmom
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsa := Real.sqrt_nonneg a
    have h1 : (1 : ℝ) ≤ 2 + 3 * K₁ := by linarith
    have e : Cg * Real.sqrt p * (4 * Real.sqrt a / (W * w)) * (8 * CT ^ 3) =
        A / (W * w) * Real.sqrt a := by rw [hAdef]; ring
    rw [e]
    have hpos : 0 ≤ A / (W * w) * Real.sqrt a := by positivity
    calc A / (W * w) * Real.sqrt a = A / (W * w) * Real.sqrt a * 1 := by ring
      _ ≤ A / (W * w) * Real.sqrt a * (2 + 3 * K₁) := mul_le_mul_of_nonneg_left h1 hpos
      _ = A * (2 + 3 * K₁) / (W * w) * Real.sqrt a := by ring
  · -- `W^{-3/2} ‖Y‖_HS ≤ u / √W`
    have hC0 : 0 ≤ A * (2 + 3 * K₁) := by positivity
    have hs : Real.sqrt a ≤ W * u := hWu ▸ hYhs
    calc A * (2 + 3 * K₁) / (W * w) * Real.sqrt a ≤ A * (2 + 3 * K₁) / (W * w) * (W * u) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = A * (2 + 3 * K₁) * u / w := by field_simp
  · -- the insertion variant
    obtain ⟨s2, hs2⟩ : ∃ s2 : ℝ, s2 = 2 * a + 2 * (4 * W * K₁ ^ 2) := ⟨_, rfl⟩
    have hK2 : 0 ≤ 4 * (W : ℝ) * K₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg K₁)
    have hs20 : 0 ≤ s2 := by rw [hs2]; linarith
    have hD₀' : ‖D₀‖ ≤ K₁ := hD₀.trans (le_max_left _ _)
    have hP : ∀ Gm : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        dcvHS (Gm * (dcvHat S + D₀) * Gm) ≤ s2 * dcvTheta (dcvKh K) Gm ^ 4 := fun Gm => by
      rw [hShat]
      have h1 := dcv_dir_hs_le (dcvKh K) (dcvHat Y) D₀ Gm
      rw [dcvHS_hat, hYe, dcv_card_layerSite] at h1
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have : ‖D₀‖ ^ 2 ≤ K₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD₀' 2
      rw [hs2]; nlinarith
    have hc := dcv_noise_core hCg.le hgr hW hb0 hb1 .separate hX E hzpos.le hD (dcvHat S + D₀)
      (dcvKh K) hs20 hP hp hCT hinv hmom
    refine hc.trans (ENNReal.ofReal_le_ofReal ?_)
    have hss : Real.sqrt s2 ≤ 2 * w ^ 2 * u + 3 * w * K₁ :=
      dcv_sqrt_arith ha0 hu0 hK₁0 hw1 hww (hWu ▸ hYhs) hs2
    have e : Cg * Real.sqrt p * (4 * Real.sqrt s2 / (W * w)) * (8 * CT ^ 3) =
        A * Real.sqrt s2 / (w ^ 2 * w) := by rw [hAdef, hww]; ring
    rw [e]
    exact dcv_noise_arith hA0 hu0 hK₁0 hw1 hss

end BlockBand.Layers
