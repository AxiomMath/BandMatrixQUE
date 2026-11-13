module

public import BlockBand.Layers.MeanEquations
public import BlockBand.Layers.TraceCovariance

/-!
# Common-port mean: the two-resolvent Schwinger–Dyson identity

Notation: `G = G_κ = (𝒢⁻¹ + iκ)⁻¹ = meqG`, `F = G P Gᴴ`, `Λ(x) = tflLin x`,
`𝒮(N) = meqS N = Σᵢ vᵢ Λᵢ N Λᵢ`, `C_κ = tflConst + iκ`.

* `sdF`, `sdF_norm_le`, `sdF_continuous`.
* `sd_ibp_coord`, `sd_ibp`: `E[Λ F] = -E[𝒮(G) F] - E[𝒮(F) Gᴴ]` (`ou_ibp` coordinatewise,
  `∂ᵢF = -GΛᵢF - FΛᵢGᴴ`, `Λᵢᴴ = Λᵢ`).
* `sd_reg_core`: `C_κ E F - E[𝒮(G)F] - E[𝒮(F)Gᴴ] = P E Gᴴ`.
* `sd_limit_core`, `sd_limit_law`: the limit `κ → 0` under a.s. invertibility and `‖𝒢‖³ ∈ L¹`
  (dominated convergence by `1 + ‖𝒢‖³`), in coordinates and on `layerLaw W b σ`.
* `sdResid`, `sd_expand`: two-function covariance expansion
  `E[𝒮(g(Y))Z] = 𝒮(ḡ(Y))EZ + Σ Cov(g(Y), P_a Z)…` (any probability law, `‖Y‖‖Z‖, Z ∈ L¹`).
* `twoResolvent_equation`: `(𝒟 - 𝒮(ḡ)) E[𝒢P𝒢ᴴ] = P E𝒢ᴴ + 𝒮(t̄) E𝒢ᴴ + sdResid(𝒢, F) +
  sdResid(F, 𝒢ᴴ)` on `layerLaw`, every `W ≥ 1`, `0 ≤ b ≤ 1/2`, every deterministic `P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

section Star

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `N ↦ Nᴴ` as a continuous `ℝ`-linear map. -/
def sdStar : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => Nᴴ
      map_add' := fun N N' => conjTranspose_add N N'
      map_smul' := fun r N => by
        simp only [RingHom.id_apply]
        rw [conjTranspose_smul, star_trivial] }

omit [DecidableEq n] in
/-- Deterministic: `sdStar N = Nᴴ` (definitional). -/
theorem sdStar_apply (N : Matrix n n ℂ) : sdStar N = Nᴴ := rfl

end Star

section Coordinates

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)

/-- `F_κ(x) = G_κ(x) P G_κ(x)ᴴ`. -/
def sdF (κ : ℝ) (x : TflCoord W σ → ℝ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  meqG W b σ E z X κ x * P * (meqG W b σ E z X κ x)ᴴ

variable {X}

/-- Deterministic, real coordinates `x`, regularization `κ > 0`, Hermitian `X`, `Im z ≥ 0`, any
deterministic `P`: `‖F_κ(x)‖ ≤ ‖P‖ κ⁻²` (operator norm; from `‖G_κ‖ ≤ κ⁻¹`, `meqG_norm_le`). -/
theorem sdF_norm_le (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : ‖sdF W b σ E z X P κ x‖ ≤ ‖P‖ * κ⁻¹ ^ 2 := by
  have hG := meqG_norm_le W b σ E z hX hz hκ x
  unfold sdF
  calc ‖meqG W b σ E z X κ x * P * (meqG W b σ E z X κ x)ᴴ‖
      ≤ ‖meqG W b σ E z X κ x‖ * ‖P‖ * ‖meqG W b σ E z X κ x‖ := by
        refine (norm_mul_le _ _).trans ?_
        rw [l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ κ⁻¹ * ‖P‖ * κ⁻¹ := by gcongr
    _ = ‖P‖ * κ⁻¹ ^ 2 := by ring

/-- Deterministic: `x ↦ F_κ(x) = G_κ(x) P G_κ(x)ᴴ` is continuous on the real coordinates
(`κ > 0`, Hermitian `X`, `Im z ≥ 0`). -/
theorem sdF_continuous (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (sdF W b σ E z X P κ) := by
  have hG := meqG_continuous W b σ E z hX hz hκ
  unfold sdF
  exact (hG.mul continuous_const).mul hG.matrix_conjTranspose

/-- `x ↦ Λ F_κ(x)` has derivative `w ↦ Λ(G' w P Gᴴ + G P (G' w)ᴴ)`, `G' w = -G Λ(w) G`. -/
theorem sd_hasFDerivAt (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (Λ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (x : TflCoord W σ → ℝ) :
    HasFDerivAt (fun y => Λ * sdF W b σ E z X P κ y)
      ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Λ).comp
        ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).precompR _
            (meqG W b σ E z X κ x * P)
            (sdStar.comp ((-(ContinuousLinearMap.mulLeftRight ℝ
              (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (meqG W b σ E z X κ x)
              (meqG W b σ E z X κ x))).comp (meqLc W b σ))) +
          (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).precompL _
            ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).flip P |>.comp
              ((-(ContinuousLinearMap.mulLeftRight ℝ
                (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (meqG W b σ E z X κ x)
                (meqG W b σ E z X κ x))).comp (meqLc W b σ)))
            (meqG W b σ E z X κ x)ᴴ)) x := by
  have hG := meqG_hasFDerivAt W b σ E z hX hz hκ x
  have hGP : HasFDerivAt (fun y => meqG W b σ E z X κ y * P)
      (((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).flip P).comp
        ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
          (meqG W b σ E z X κ x) (meqG W b σ E z X κ x))).comp (meqLc W b σ))) x :=
    (((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).flip P).hasFDerivAt).comp
      x hG
  have hGH : HasFDerivAt (fun y => sdStar (meqG W b σ E z X κ y))
      (sdStar.comp ((-(ContinuousLinearMap.mulLeftRight ℝ
        (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (meqG W b σ E z X κ x)
        (meqG W b σ E z X κ x))).comp (meqLc W b σ))) x :=
    (sdStar.hasFDerivAt).comp x hG
  have hF := (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).hasFDerivAt_of_bilinear
    hGP hGH
  exact ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Λ).hasFDerivAt).comp
    x hF

/-- The derivative of `x ↦ Λ F_κ(x)` evaluated: `Λ (G P (-(GΛ(w)G))ᴴ + (-(GΛ(w)G)) P Gᴴ)`. -/
theorem sd_fderiv_apply (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (Λ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (x w : TflCoord W σ → ℝ) :
    fderiv ℝ (fun y => Λ * sdF W b σ E z X P κ y) x w =
      Λ * (meqG W b σ E z X κ x * P *
          (-(meqG W b σ E z X κ x * tflLin W b σ w * meqG W b σ E z X κ x))ᴴ +
        -(meqG W b σ E z X κ x * tflLin W b σ w * meqG W b σ E z X κ x) * P *
          (meqG W b σ E z X κ x)ᴴ) := by
  rw [(sd_hasFDerivAt W b σ E z P hX hz hκ Λ x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply,
    _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, meqLc_apply,
    ContinuousLinearMap.compL_apply]
  rfl

/-- The same derivative, in the contracted form `-(ΛGΛ'F) - (ΛFΛ'Gᴴ)` for `Λ' = Λ(w)`
Hermitian. -/
theorem sd_fderiv_eq (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (Λ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (x w : TflCoord W σ → ℝ) :
    fderiv ℝ (fun y => Λ * sdF W b σ E z X P κ y) x w =
      -(Λ * meqG W b σ E z X κ x * tflLin W b σ w * sdF W b σ E z X P κ x) -
        Λ * sdF W b σ E z X P κ x * tflLin W b σ w * (meqG W b σ E z X κ x)ᴴ := by
  rw [sd_fderiv_apply W b σ E z P hX hz hκ Λ x w]
  unfold sdF
  set G := meqG W b σ E z X κ x
  set L := tflLin W b σ w
  have hL : Lᴴ = L := tcv_lin_herm W b σ w
  simp only [conjTranspose_neg, conjTranspose_mul, hL, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_add, Matrix.mul_assoc]
  abel

/-- Deterministic: `x ↦ Λ F_κ(x)` is `C¹` on the real coordinates for every fixed matrix `Λ`
(`κ > 0`, Hermitian `X`, `Im z ≥ 0`); input of `ou_ibp`. -/
theorem sd_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (Λ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ContDiff ℝ 1 (fun y => Λ * sdF W b σ E z X P κ y) := by
  have hG := meqG_contDiff W b σ E z hX hz hκ
  have hGP : ContDiff ℝ 1 (fun y => meqG W b σ E z X κ y * P) :=
    ((ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).flip P).contDiff.comp hG
  have hGH : ContDiff ℝ 1 (fun y => sdStar (meqG W b σ E z X κ y)) :=
    (sdStar (n := LayerSite W σ)).contDiff.comp hG
  have hF : ContDiff ℝ 1 (fun y => (ContinuousLinearMap.mul ℝ
      (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) (meqG W b σ E z X κ y * P)
        (sdStar (meqG W b σ E z X κ y))) :=
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ)).isBoundedBilinearMap.contDiff.comp
      (hGP.prodMk hGH)
  exact (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) Λ).contDiff.comp hF

/-- Deterministic uniform derivative bound (operator norms), needed by `ou_ibp`:
`‖d(Λ F_κ)(x)‖ ≤ ‖Λ‖ · 2 κ⁻¹ ‖P‖ κ⁻¹ ‖Λ_lin‖ κ⁻¹` for all `x` (`κ > 0`, Hermitian `X`,
`Im z ≥ 0`, `Λ_lin = meqLc`). -/
theorem sd_fderiv_norm_le (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (Λ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (x : TflCoord W σ → ℝ) :
    ‖fderiv ℝ (fun y => Λ * sdF W b σ E z X P κ y) x‖ ≤
      ‖Λ‖ * (2 * (κ⁻¹ * ‖P‖ * (κ⁻¹ * ‖meqLc W b σ‖ * κ⁻¹))) := by
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [sd_fderiv_apply W b σ E z P hX hz hκ Λ x w]
  set G := meqG W b σ E z X κ x
  have hG : ‖G‖ ≤ κ⁻¹ := meqG_norm_le W b σ E z hX hz hκ x
  have hL : ‖tflLin W b σ w‖ ≤ ‖meqLc W b σ‖ * ‖w‖ := (meqLc W b σ).le_opNorm w
  have hT : ‖G * tflLin W b σ w * G‖ ≤ κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹ :=
    (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hG hL
      (norm_nonneg _) hκi)) hG (norm_nonneg _) (by positivity))
  have h1 : ‖G * P * (-(G * tflLin W b σ w * G))ᴴ‖ ≤
      κ⁻¹ * ‖P‖ * (κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹) := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg _))) ?_ (norm_nonneg _) (by positivity))
    rw [l2_opNorm_conjTranspose, norm_neg]; exact hT
  have h2 : ‖-(G * tflLin W b σ w * G) * P * Gᴴ‖ ≤
      κ⁻¹ * ‖P‖ * (κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹) := by
    refine (norm_mul_le _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖-(G * tflLin W b σ w * G) * P‖ * ‖G‖
        ≤ (κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹ * ‖P‖) * κ⁻¹ := by
          refine mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_
            (norm_nonneg _))) hG (norm_nonneg _) (by positivity)
          rw [norm_neg]; exact hT
      _ = κ⁻¹ * ‖P‖ * (κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹) := by ring
  calc ‖Λ * (G * P * (-(G * tflLin W b σ w * G))ᴴ + -(G * tflLin W b σ w * G) * P * Gᴴ)‖
      ≤ ‖Λ‖ * (κ⁻¹ * ‖P‖ * (κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹) +
          κ⁻¹ * ‖P‖ * (κ⁻¹ * (‖meqLc W b σ‖ * ‖w‖) * κ⁻¹)) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
          (add_le_add h1 h2)) (norm_nonneg _))
    _ = ‖Λ‖ * (2 * (κ⁻¹ * ‖P‖ * (κ⁻¹ * ‖meqLc W b σ‖ * κ⁻¹))) * ‖w‖ := by ring

/-- **Coordinate IBP for the two-resolvent word** (every coordinate `i`):
`E[xᵢ ΛᵢF] = vᵢ E[-(ΛᵢGΛᵢF) - ΛᵢFΛᵢGᴴ]`. -/
theorem sd_ibp_coord (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (i : TflCoord W σ) :
    ∫ x, x i • (tflLin W b σ (Pi.single i 1) * sdF W b σ E z X P κ x)
        ∂gaussianProduct (tflVar W b σ) =
      (tflVar W b σ i : ℝ) • ∫ x, (-(tflLin W b σ (Pi.single i 1) * meqG W b σ E z X κ x *
          tflLin W b σ (Pi.single i 1) * sdF W b σ E z X P κ x) -
        tflLin W b σ (Pi.single i 1) * sdF W b σ E z X P κ x * tflLin W b σ (Pi.single i 1) *
          (meqG W b σ E z X κ x)ᴴ) ∂gaussianProduct (tflVar W b σ) := by
  set Λ := tflLin W b σ (Pi.single i 1) with hΛ
  have hk := sd_contDiff W b σ E z P hX hz hκ Λ
  have hb : ∀ x, ‖Λ * sdF W b σ E z X P κ x‖ ≤ ‖Λ‖ * (‖P‖ * κ⁻¹ ^ 2) := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (sdF_norm_le W b σ E z P hX hz hκ x)
      (norm_nonneg _))
  rw [ou_ibp (tflVar W b σ) i hk hb (sd_fderiv_norm_le W b σ E z P hX hz hκ Λ)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  exact sd_fderiv_eq W b σ E z P hX hz hκ Λ x (Pi.single i 1)

/-- **Gaussian integration by parts for `F = G P Gᴴ`**:
`E[Λ(x) F] = -E[𝒮(G) F] - E[𝒮(F) Gᴴ]`. -/
theorem sd_ibp (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    ∫ x, tflLin W b σ x * sdF W b σ E z X P κ x ∂gaussianProduct (tflVar W b σ) =
      -∫ x, meqS W b σ (meqG W b σ E z X κ x) * sdF W b σ E z X P κ x
          ∂gaussianProduct (tflVar W b σ) -
        ∫ x, meqS W b σ (sdF W b σ E z X P κ x) * (meqG W b σ E z X κ x)ᴴ
          ∂gaussianProduct (tflVar W b σ) := by
  set μ := gaussianProduct (tflVar W b σ)
  set G := meqG W b σ E z X κ with hG
  set F := sdF W b σ E z X P κ with hF
  have hGc : Continuous G := meqG_continuous W b σ E z hX hz hκ
  have hFc : Continuous F := sdF_continuous W b σ E z P hX hz hκ
  have hGb : ∀ x, ‖G x‖ ≤ κ⁻¹ := meqG_norm_le W b σ E z hX hz hκ
  have hFb : ∀ x, ‖F x‖ ≤ ‖P‖ * κ⁻¹ ^ 2 := sdF_norm_le W b σ E z P hX hz hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hdec : ∀ x, tflLin W b σ x * F x = ∑ i, x i • (tflLin W b σ (Pi.single i 1) * F x) := by
    intro x
    rw [meq_lin_decomp, Finset.sum_mul]
    simp only [Matrix.smul_mul]
  have hint : ∀ i : TflCoord W σ,
      Integrable (fun x => x i • (tflLin W b σ (Pi.single i 1) * F x)) μ := by
    intro i
    refine ou_integrable_of_norm_le μ
      ((continuous_apply i).smul (continuous_const.mul hFc)).aestronglyMeasurable 0
      (‖tflLin W b σ (Pi.single i 1)‖ * (‖P‖ * κ⁻¹ ^ 2)) fun x => ?_
    rw [norm_smul, zero_add]
    have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    have h2 : ‖tflLin W b σ (Pi.single i 1) * F x‖ ≤
        ‖tflLin W b σ (Pi.single i 1)‖ * (‖P‖ * κ⁻¹ ^ 2) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hFb x) (norm_nonneg _))
    calc ‖x i‖ * ‖tflLin W b σ (Pi.single i 1) * F x‖
        ≤ ‖x‖ * (‖tflLin W b σ (Pi.single i 1)‖ * (‖P‖ * κ⁻¹ ^ 2)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = ‖tflLin W b σ (Pi.single i 1)‖ * (‖P‖ * κ⁻¹ ^ 2) * ‖x‖ := by ring
  have hbd : ∀ (B D : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
      (a d : ℝ), Continuous B → Continuous D → (∀ x, ‖B x‖ ≤ a) → (∀ x, ‖D x‖ ≤ d) →
      ∀ (L : Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
      Integrable (fun x => L * B x * L * D x) μ := by
    intro B D a d hB hD hBb hDb L
    refine Integrable.of_bound (((continuous_const.mul hB).mul continuous_const).mul hD
      |>.aestronglyMeasurable) (‖L‖ * a * ‖L‖ * d) (ae_of_all _ fun x => ?_)
    calc ‖L * B x * L * D x‖ ≤ ‖L * B x * L‖ * ‖D x‖ := norm_mul_le _ _
      _ ≤ ‖L * B x‖ * ‖L‖ * ‖D x‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖L‖ * ‖B x‖ * ‖L‖ * ‖D x‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖L‖ * a * ‖L‖ * d := by
          have ha : 0 ≤ a := (norm_nonneg _).trans (hBb x)
          exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hBb x)
            (norm_nonneg _)) (norm_nonneg _)) (hDb x) (norm_nonneg _) (by positivity)
  have iGF : ∀ i : TflCoord W σ, Integrable (fun x => tflLin W b σ (Pi.single i 1) * G x *
      tflLin W b σ (Pi.single i 1) * F x) μ := fun i =>
    hbd G F κ⁻¹ (‖P‖ * κ⁻¹ ^ 2) hGc hFc hGb hFb _
  have hGHc : Continuous (fun x => (G x)ᴴ) := hGc.matrix_conjTranspose
  have hGHb : ∀ x, ‖(G x)ᴴ‖ ≤ κ⁻¹ := fun x => by rw [l2_opNorm_conjTranspose]; exact hGb x
  have iFG : ∀ i : TflCoord W σ, Integrable (fun x => tflLin W b σ (Pi.single i 1) * F x *
      tflLin W b σ (Pi.single i 1) * (G x)ᴴ) μ := fun i =>
    hbd F (fun x => (G x)ᴴ) (‖P‖ * κ⁻¹ ^ 2) κ⁻¹ hFc hGHc hFb hGHb _
  have hpt : ∀ x, -(meqS W b σ (G x) * F x) - meqS W b σ (F x) * (G x)ᴴ =
      ∑ i, (tflVar W b σ i : ℝ) • (-(tflLin W b σ (Pi.single i 1) * G x *
          tflLin W b σ (Pi.single i 1) * F x) -
        tflLin W b σ (Pi.single i 1) * F x * tflLin W b σ (Pi.single i 1) * (G x)ᴴ) := by
    intro x
    unfold meqS
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, smul_sub, smul_neg]
  have hint3 : ∀ i : TflCoord W σ, Integrable (fun x => (tflVar W b σ i : ℝ) •
      (-(tflLin W b σ (Pi.single i 1) * G x * tflLin W b σ (Pi.single i 1) * F x) -
        tflLin W b σ (Pi.single i 1) * F x * tflLin W b σ (Pi.single i 1) * (G x)ᴴ)) μ :=
    fun i => ((iGF i).neg.sub (iFG i)).fun_smul (tflVar W b σ i : ℝ)
  have iSG : Integrable (fun x => meqS W b σ (G x) * F x) μ := by
    refine Integrable.of_bound (((meq_continuous_meqS b).comp hGc).mul hFc).aestronglyMeasurable
      (meqCS W b σ * κ⁻¹ * (‖P‖ * κ⁻¹ ^ 2)) (ae_of_all _ fun x => ?_)
    exact (norm_mul_le _ _).trans (mul_le_mul ((meq_norm_meqS_le b _).trans
      (mul_le_mul_of_nonneg_left (hGb x) (meqCS_nonneg W b σ))) (hFb x) (norm_nonneg _)
      (by have := meqCS_nonneg W b σ; positivity))
  have iSF : Integrable (fun x => meqS W b σ (F x) * (G x)ᴴ) μ := by
    refine Integrable.of_bound (((meq_continuous_meqS b).comp hFc).mul hGHc).aestronglyMeasurable
      (meqCS W b σ * (‖P‖ * κ⁻¹ ^ 2) * κ⁻¹) (ae_of_all _ fun x => ?_)
    exact (norm_mul_le _ _).trans (mul_le_mul ((meq_norm_meqS_le b _).trans
      (mul_le_mul_of_nonneg_left (hFb x) (meqCS_nonneg W b σ))) (hGHb x) (norm_nonneg _)
      (by have := meqCS_nonneg W b σ; positivity))
  have hsub := integral_sub iSG.neg iSF
  simp only [Pi.neg_apply] at hsub
  rw [integral_congr_ae (ae_of_all _ hdec), integral_finsetSum _ fun i _ => hint i,
    ← integral_neg, ← hsub, integral_congr_ae (ae_of_all _ hpt),
    integral_finsetSum _ fun i _ => hint3 i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul]
  exact sd_ibp_coord W b σ E z P hX hz hκ i

/-- **Regularized two-resolvent Schwinger–Dyson identity in coordinates**:
`C_κ E[F] - E[𝒮(G)F] - E[𝒮(F)Gᴴ] = P E[Gᴴ]`, `C_κ = tflConst + iκ`, `F = G P Gᴴ`. -/
theorem sd_reg_core (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    (tflConst σ E z X + ((κ : ℂ) * Complex.I) • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) *
        ∫ x, sdF W b σ E z X P κ x ∂gaussianProduct (tflVar W b σ) -
      ∫ x, meqS W b σ (meqG W b σ E z X κ x) * sdF W b σ E z X P κ x
        ∂gaussianProduct (tflVar W b σ) -
      ∫ x, meqS W b σ (sdF W b σ E z X P κ x) * (meqG W b σ E z X κ x)ᴴ
        ∂gaussianProduct (tflVar W b σ) =
      P * ∫ x, (meqG W b σ E z X κ x)ᴴ ∂gaussianProduct (tflVar W b σ) := by
  set μ := gaussianProduct (tflVar W b σ)
  set G := meqG W b σ E z X κ with hG
  set F := sdF W b σ E z X P κ with hF
  set C := tflConst σ E z X + ((κ : ℂ) * Complex.I) •
    (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) with hC
  have hGc : Continuous G := meqG_continuous W b σ E z hX hz hκ
  have hFc : Continuous F := sdF_continuous W b σ E z P hX hz hκ
  have hFb : ∀ x, ‖F x‖ ≤ ‖P‖ * κ⁻¹ ^ 2 := sdF_norm_le W b σ E z P hX hz hκ
  have hFi : Integrable F μ := Integrable.of_bound hFc.aestronglyMeasurable _ (ae_of_all _ hFb)
  have hGHi : Integrable (fun x => (G x)ᴴ) μ :=
    Integrable.of_bound hGc.matrix_conjTranspose.aestronglyMeasurable κ⁻¹ (ae_of_all _ fun x => by
      rw [l2_opNorm_conjTranspose]; exact meqG_norm_le W b σ E z hX hz hκ x)
  have hpt : ∀ x, C * F x + tflLin W b σ x * F x = P * (G x)ᴴ := by
    intro x
    rw [← add_mul]
    have : C + tflLin W b σ x = tflPsi W b σ E z X κ x := rfl
    rw [this, hF]
    unfold sdF
    rw [show meqG W b σ E z X κ x = Ring.inverse (tflPsi W b σ E z X κ x) from rfl,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Ring.mul_inverse_cancel _ (tflPsi_isUnit W b σ E z hX hz hκ x), Matrix.one_mul]
    rfl
  have hint2 : Integrable (fun x => tflLin W b σ x * F x) μ := by
    refine ou_integrable_of_norm_le μ
      (((meqLc W b σ).continuous.mul hFc).aestronglyMeasurable) 0
      (‖meqLc W b σ‖ * (‖P‖ * κ⁻¹ ^ 2)) fun x => ?_
    rw [zero_add]
    calc ‖tflLin W b σ x * F x‖ ≤ ‖tflLin W b σ x‖ * ‖F x‖ := norm_mul_le _ _
      _ ≤ (‖meqLc W b σ‖ * ‖x‖) * (‖P‖ * κ⁻¹ ^ 2) := by
          gcongr
          · exact (meqLc W b σ).le_opNorm x
          · exact hFb x
      _ = ‖meqLc W b σ‖ * (‖P‖ * κ⁻¹ ^ 2) * ‖x‖ := by ring
  have h1 : ∫ x, (C * F x + tflLin W b σ x * F x) ∂μ = P * ∫ x, (G x)ᴴ ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) P).integral_comp_comm
      hGHi
  rw [integral_add (hFi.const_mul C) hint2, sd_ibp W b σ E z P hX hz hκ] at h1
  have h2 : ∫ x, C * F x ∂μ = C * ∫ x, F x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) C).integral_comp_comm hFi
  rw [h2] at h1
  rw [← h1]
  abel

/-- Elementary: `t ≤ 1 + t³`, `t² ≤ 1 + t³` for `t ≥ 0`. -/
theorem sd_le_one_add_cube {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ 3 ∧ t ^ 2 ≤ 1 + t ^ 3 := by
  constructor <;> nlinarith [sq_nonneg (t - 1), sq_nonneg t, mul_nonneg ht (sq_nonneg (t - 1))]

/-- **The `κ → 0` limit of the two-resolvent identity in coordinates**: if the layer matrix is
a.s. invertible and `‖𝒢‖³ ∈ L¹`, then
`𝒟 E[𝒢P𝒢ᴴ] - E[𝒮(𝒢)𝒢P𝒢ᴴ] - E[𝒮(𝒢P𝒢ᴴ)𝒢ᴴ] = P E[𝒢ᴴ]`. -/
theorem sd_limit_core (hX : X.IsHermitian) (hz : 0 ≤ z.im)
    (hinv : ∀ᵐ x ∂gaussianProduct (tflVar W b σ),
      IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det)
    (hG3 : Integrable (fun x => ‖layerResolvent σ E z X (tflEmbed W b σ x)‖ ^ 3)
      (gaussianProduct (tflVar W b σ))) :
    tflConst σ E z X * ∫ x, layerResolvent σ E z X (tflEmbed W b σ x) * P *
        (layerResolvent σ E z X (tflEmbed W b σ x))ᴴ ∂gaussianProduct (tflVar W b σ) -
      ∫ x, meqS W b σ (layerResolvent σ E z X (tflEmbed W b σ x)) *
        (layerResolvent σ E z X (tflEmbed W b σ x) * P *
          (layerResolvent σ E z X (tflEmbed W b σ x))ᴴ) ∂gaussianProduct (tflVar W b σ) -
      ∫ x, meqS W b σ (layerResolvent σ E z X (tflEmbed W b σ x) * P *
          (layerResolvent σ E z X (tflEmbed W b σ x))ᴴ) *
        (layerResolvent σ E z X (tflEmbed W b σ x))ᴴ ∂gaussianProduct (tflVar W b σ) =
      P * ∫ x, (layerResolvent σ E z X (tflEmbed W b σ x))ᴴ ∂gaussianProduct (tflVar W b σ) := by
  set μ := gaussianProduct (tflVar W b σ)
  set Φ := tflEmbed W b σ with hΦdef
  set G0 : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hG0
  have hG0m : Measurable G0 :=
    (measurable_layerResolvent σ E z X).comp (tfl_measurable_embed W b σ)
  set Dm : (TflCoord W σ → ℝ) → ℝ := fun x => 1 + ‖G0 x‖ ^ 3 with hDm
  have hDi : Integrable Dm μ := (integrable_const 1).add hG3
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun m => meqG W b σ E z X (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m => meqG_continuous W b σ E z hX hz (hκpos m)
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (G0 x)) := by
    filter_upwards [hinv] with x hx
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
    have hG0x : G0 x = Ring.inverse N := by
      rw [hG0]
      simp only [layerResolvent]
      rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [hG0x]
    exact h2
  have hbd : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ 2 * ‖G0 x‖ := by
    intro m
    filter_upwards [hinv] with x hx
    exact tflPsi_inv_le_two W b σ E z hX hz (hκpos m) x hx
  -- continuous maps of the resolvent
  have cF : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => N * P * Nᴴ) :=
    (continuous_id.mul continuous_const).mul continuous_id.matrix_conjTranspose
  have cS1 : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      meqS W b σ N * (N * P * Nᴴ)) := (meq_continuous_meqS b).mul cF
  have cS2 : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      meqS W b σ (N * P * Nᴴ) * Nᴴ) :=
    ((meq_continuous_meqS b).comp cF).mul continuous_id.matrix_conjTranspose
  have cH : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => Nᴴ) :=
    continuous_id.matrix_conjTranspose
  -- norm bounds
  have nF : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ, ‖N * P * Nᴴ‖ ≤ ‖P‖ * ‖N‖ ^ 2 := by
    intro N
    refine (norm_mul_le _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖N * P‖ * ‖N‖ ≤ ‖N‖ * ‖P‖ * ‖N‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖P‖ * ‖N‖ ^ 2 := by ring
  have nS1 : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ‖meqS W b σ N * (N * P * Nᴴ)‖ ≤ meqCS W b σ * ‖P‖ * ‖N‖ ^ 3 := by
    intro N
    refine (norm_mul_le _ _).trans ?_
    calc ‖meqS W b σ N‖ * ‖N * P * Nᴴ‖ ≤ (meqCS W b σ * ‖N‖) * (‖P‖ * ‖N‖ ^ 2) :=
          mul_le_mul (meq_norm_meqS_le b N) (nF N) (norm_nonneg _)
            (mul_nonneg (meqCS_nonneg W b σ) (norm_nonneg _))
      _ = meqCS W b σ * ‖P‖ * ‖N‖ ^ 3 := by ring
  have nS2 : ∀ N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ‖meqS W b σ (N * P * Nᴴ) * Nᴴ‖ ≤ meqCS W b σ * ‖P‖ * ‖N‖ ^ 3 := by
    intro N
    refine (norm_mul_le _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖meqS W b σ (N * P * Nᴴ)‖ * ‖N‖ ≤ (meqCS W b σ * (‖P‖ * ‖N‖ ^ 2)) * ‖N‖ := by
          gcongr
          exact (meq_norm_meqS_le b _).trans (mul_le_mul_of_nonneg_left (nF N)
            (meqCS_nonneg W b σ))
      _ = meqCS W b σ * ‖P‖ * ‖N‖ ^ 3 := by ring
  have hCS := meqCS_nonneg W b σ
  -- the four limits
  have lim : ∀ (f : Matrix (LayerSite W σ) (LayerSite W σ) ℂ →
      Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (c : ℝ), Continuous f → 0 ≤ c →
      (∀ m, ∀ᵐ x ∂μ, ‖f (Gm m x)‖ ≤ c * Dm x) →
      Tendsto (fun m => ∫ x, f (Gm m x) ∂μ) atTop (𝓝 (∫ x, f (G0 x) ∂μ)) := by
    intro f c hf hc hb
    exact tendsto_integral_of_dominated_convergence (fun x => c * Dm x)
      (fun m => (hf.comp (hGmc m)).aestronglyMeasurable) (hDi.const_mul c) hb
      (hconv.mono fun x hx => (hf.tendsto _).comp hx)
  have hcube : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ^ 3 ≤ 8 * Dm x ∧ ‖Gm m x‖ ^ 2 ≤ 4 * Dm x ∧
      ‖Gm m x‖ ≤ 2 * Dm x := by
    intro m
    filter_upwards [hbd m] with x hx
    have h0 := norm_nonneg (G0 x)
    obtain ⟨e1, e2⟩ := sd_le_one_add_cube h0
    have hc3 : ‖Gm m x‖ ^ 3 ≤ (2 * ‖G0 x‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hx 3
    have hc2 : ‖Gm m x‖ ^ 2 ≤ (2 * ‖G0 x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    simp only [hDm]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  have l1 := lim (fun N => N * P * Nᴴ) (4 * ‖P‖) cF (by positivity) fun m => by
    filter_upwards [hcube m] with x hx
    exact (nF _).trans (by nlinarith [norm_nonneg P, hx.2.1])
  have l2 := lim (fun N => meqS W b σ N * (N * P * Nᴴ)) (8 * (meqCS W b σ * ‖P‖)) cS1
    (by positivity) fun m => by
      filter_upwards [hcube m] with x hx
      refine (nS1 _).trans ?_
      have : 0 ≤ meqCS W b σ * ‖P‖ := by positivity
      nlinarith [hx.1]
  have l3 := lim (fun N => meqS W b σ (N * P * Nᴴ) * Nᴴ) (8 * (meqCS W b σ * ‖P‖)) cS2
    (by positivity) fun m => by
      filter_upwards [hcube m] with x hx
      refine (nS2 _).trans ?_
      have : 0 ≤ meqCS W b σ * ‖P‖ := by positivity
      nlinarith [hx.1]
  have l4 := lim (fun N => Nᴴ) 2 cH (by norm_num) fun m => by
    filter_upwards [hcube m] with x hx
    rw [l2_opNorm_conjTranspose]; exact hx.2.2
  have hcC : Continuous (fun κ : ℝ => tflConst σ E z X + ((κ : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) := by fun_prop
  have hlimC : Tendsto (fun m => tflConst σ E z X + ((κm m : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) atTop (𝓝 (tflConst σ E z X)) := by
    have := (hcC.tendsto 0).comp hκlim
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
    exact this
  have hlim := ((hlimC.mul l1).sub l2).sub l3
  have hconst : (fun m => (tflConst σ E z X + ((κm m : ℂ) * Complex.I) •
      (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) * ∫ x, Gm m x * P * (Gm m x)ᴴ ∂μ -
        ∫ x, meqS W b σ (Gm m x) * (Gm m x * P * (Gm m x)ᴴ) ∂μ -
        ∫ x, meqS W b σ (Gm m x * P * (Gm m x)ᴴ) * (Gm m x)ᴴ ∂μ) =
      fun m => P * ∫ x, (Gm m x)ᴴ ∂μ := by
    funext m
    exact sd_reg_core W b σ E z P hX hz (hκpos m)
  rw [hconst] at hlim
  have hlimP : Tendsto (fun m => P * ∫ x, (Gm m x)ᴴ ∂μ) atTop (𝓝 (P * ∫ x, (G0 x)ᴴ ∂μ)) :=
    tendsto_const_nhds.mul l4
  exact tendsto_nhds_unique hlim hlimP

end Coordinates

/-!
## Transfer to the layer law and covariance expansion
-/

section Law

variable {W : ℕ} {σ : LayerShape}

/-- **Exact two-resolvent identity on `layerLaw`** under a.s. invertibility and `‖𝒢‖³ ∈ L¹`. -/
theorem sd_limit_law (b : ℝ) (E : ℝ) {z : ℂ} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) (hz : 0 ≤ z.im) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hG3 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 3) (layerLaw W b σ)) :
    tflConst σ E z X * ∫ ω, layerResolvent σ E z X ω * P * (layerResolvent σ E z X ω)ᴴ
        ∂layerLaw W b σ -
      ∫ ω, meqS W b σ (layerResolvent σ E z X ω) *
        (layerResolvent σ E z X ω * P * (layerResolvent σ E z X ω)ᴴ) ∂layerLaw W b σ -
      ∫ ω, meqS W b σ (layerResolvent σ E z X ω * P * (layerResolvent σ E z X ω)ᴴ) *
        (layerResolvent σ E z X ω)ᴴ ∂layerLaw W b σ =
      P * ∫ ω, (layerResolvent σ E z X ω)ᴴ ∂layerLaw W b σ := by
  have hΦ := tfl_measurable_embed W b σ
  have hm := measurable_layerResolvent σ E z X
  have cF : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => N * P * Nᴴ) :=
    (continuous_id.mul continuous_const).mul continuous_id.matrix_conjTranspose
  rw [tfl_layerLaw_eq_map] at hinv hG3 ⊢
  rw [integral_map (f := fun ω => layerResolvent σ E z X ω * P * (layerResolvent σ E z X ω)ᴴ)
      hΦ.aemeasurable (cF.measurable.comp hm).aestronglyMeasurable,
    integral_map (f := fun ω => meqS W b σ (layerResolvent σ E z X ω) *
      (layerResolvent σ E z X ω * P * (layerResolvent σ E z X ω)ᴴ)) hΦ.aemeasurable
      (((meq_continuous_meqS b).mul cF).measurable.comp hm).aestronglyMeasurable,
    integral_map (f := fun ω => meqS W b σ (layerResolvent σ E z X ω * P *
      (layerResolvent σ E z X ω)ᴴ) * (layerResolvent σ E z X ω)ᴴ) hΦ.aemeasurable
      ((((meq_continuous_meqS b).comp cF).mul continuous_id.matrix_conjTranspose).measurable.comp
        hm).aestronglyMeasurable,
    integral_map (f := fun ω => (layerResolvent σ E z X ω)ᴴ) hΦ.aemeasurable
      (continuous_id.matrix_conjTranspose.measurable.comp hm).aestronglyMeasurable]
  rw [integrable_map_measure (g := fun ω => ‖layerResolvent σ E z X ω‖ ^ 3)
    ((continuous_norm.pow 3).measurable.comp hm).aestronglyMeasurable hΦ.aemeasurable] at hG3
  exact sd_limit_core W b σ E z P hX hz (ae_of_ae_map hΦ.aemeasurable hinv) hG3

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The two-function covariance residual
`Σ_a c Cov(g_a(Y), P_a Z) + Σ_{a~j} b (Cov(g_{port j}(Y), P_a Z) + Cov(g_a(Y), Q_j Z))`. -/
def sdResid (ν : Measure Ω) (c b : ℂ) (Y Z : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  ∑ a, c • meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPhysProj a * Z ω) +
    ∑ a, ∑ j, (b * meqInc σ a j) •
      (meqCov ν (fun ω => portBlockTrace (Y ω) j) (fun ω => meqPhysProj a * Z ω) +
        meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPortProj j * Z ω))

/-- Integrability of `f(Y) • (P Z)` for any finite law `ν`, continuous `f` with `|f(M)| ≤ ‖M‖`
(e.g. a normalized block trace), deterministic `P`, measurable `Y, Z` with `‖Y‖‖Z‖ ∈ L¹`. -/
theorem sd_integrable_trace_smul {ν : Measure Ω}
    {Y Z : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hYm : AEStronglyMeasurable Y ν)
    (hZm : AEStronglyMeasurable Z ν) (hYZ : Integrable (fun ω => ‖Y ω‖ * ‖Z ω‖) ν)
    {f : Matrix (LayerSite W σ) (LayerSite W σ) ℂ → ℂ} (hf : Continuous f)
    (hfb : ∀ M, ‖f M‖ ≤ ‖M‖) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Integrable (fun ω => f (Y ω) • (P * Z ω)) ν := by
  refine Integrable.mono' (hYZ.const_mul ‖P‖)
    ((hf.comp_aestronglyMeasurable hYm).smul
      ((continuous_const.mul continuous_id).comp_aestronglyMeasurable hZm))
    (ae_of_all _ fun ω => ?_)
  rw [norm_smul]
  calc ‖f (Y ω)‖ * ‖P * Z ω‖ ≤ ‖Y ω‖ * (‖P‖ * ‖Z ω‖) :=
        mul_le_mul (hfb _) (norm_mul_le _ _) (norm_nonneg _) (norm_nonneg _)
    _ = ‖P‖ * (‖Y ω‖ * ‖Z ω‖) := by ring

/-- **Two-function covariance expansion**: `E[𝒮_{c,b}(g(Y)) Z] = 𝒮_{c,b}(ḡ(Y)) E[Z] +
sdResid ν c b Y Z`, for `‖Y‖‖Z‖ ∈ L¹`, `Z ∈ L¹`, any probability law. -/
theorem sd_expand {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Y Z : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hYm : AEStronglyMeasurable Y ν)
    (hZm : AEStronglyMeasurable Z ν) (hYZ : Integrable (fun ω => ‖Y ω‖ * ‖Z ω‖) ν)
    (hZi : Integrable Z ν) (c b : ℂ) :
    ∫ ω, meqShift σ c b (physBlockTrace (Y ω)) (portBlockTrace (Y ω)) * Z ω ∂ν =
      meqShift σ c b (meqMeanA ν Y) (meqMeanP ν Y) * ∫ ω, Z ω ∂ν + sdResid ν c b Y Z := by
  have iPA : ∀ a : Fin σ.blocks, Integrable (fun ω => meqPhysProj a * Z ω) ν :=
    fun a => hZi.const_mul _
  have iPQ : ∀ j : Fin σ.ports, Integrable (fun ω => meqPortProj j * Z ω) ν :=
    fun j => hZi.const_mul _
  have iAA : ∀ (a a' : Fin σ.blocks), Integrable
      (fun ω => physBlockTrace (Y ω) a • (meqPhysProj a' * Z ω)) ν := fun a a' =>
    sd_integrable_trace_smul hYm hZm hYZ (meq_continuous_physBlockTrace a)
      (fun M => meq_norm_physBlockTrace_le M a) _
  have iPA' : ∀ (j : Fin σ.ports) (a : Fin σ.blocks), Integrable
      (fun ω => portBlockTrace (Y ω) j • (meqPhysProj a * Z ω)) ν := fun j a =>
    sd_integrable_trace_smul hYm hZm hYZ (meq_continuous_portBlockTrace j)
      (fun M => meq_norm_portBlockTrace_le M j) _
  have iAQ : ∀ (a : Fin σ.blocks) (j : Fin σ.ports), Integrable
      (fun ω => physBlockTrace (Y ω) a • (meqPortProj j * Z ω)) ν := fun a j =>
    sd_integrable_trace_smul hYm hZm hYZ (meq_continuous_physBlockTrace a)
      (fun M => meq_norm_physBlockTrace_le M a) _
  have hcomm : ∀ P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ∫ ω, P * Z ω ∂ν = P * ∫ ω, Z ω ∂ν := fun P =>
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) P).integral_comp_comm
      hZi
  have hpt : ∀ ω, meqShift σ c b (physBlockTrace (Y ω)) (portBlockTrace (Y ω)) * Z ω =
      ∑ a, c • (physBlockTrace (Y ω) a • (meqPhysProj a * Z ω)) +
        ∑ a, ∑ j, (b * meqInc σ a j) • (portBlockTrace (Y ω) j • (meqPhysProj a * Z ω) +
          physBlockTrace (Y ω) a • (meqPortProj j * Z ω)) := by
    intro ω
    rw [meqShift_eq_sum]
    simp only [Matrix.add_mul, Finset.sum_mul, Matrix.smul_mul, smul_smul]
  have hI1 : Integrable (fun ω => ∑ a, c • (physBlockTrace (Y ω) a • (meqPhysProj a * Z ω))) ν :=
    integrable_finsetSum _ fun a _ => (iAA a a).fun_smul c
  have hI2 : ∀ a, Integrable (fun ω => ∑ j, (b * meqInc σ a j) •
      (portBlockTrace (Y ω) j • (meqPhysProj a * Z ω) +
        physBlockTrace (Y ω) a • (meqPortProj j * Z ω))) ν := fun a =>
    integrable_finsetSum _ fun j _ => ((iPA' j a).add (iAQ a j)).fun_smul _
  have e1 : ∀ a, ∫ ω, c • (physBlockTrace (Y ω) a • (meqPhysProj a * Z ω)) ∂ν =
      c • ∫ ω, physBlockTrace (Y ω) a • (meqPhysProj a * Z ω) ∂ν := fun a => integral_smul _ _
  have e2 : ∀ a, ∫ ω, ∑ j, (b * meqInc σ a j) • (portBlockTrace (Y ω) j • (meqPhysProj a * Z ω) +
      physBlockTrace (Y ω) a • (meqPortProj j * Z ω)) ∂ν =
      ∑ j, (b * meqInc σ a j) • (∫ ω, portBlockTrace (Y ω) j • (meqPhysProj a * Z ω) ∂ν +
        ∫ ω, physBlockTrace (Y ω) a • (meqPortProj j * Z ω) ∂ν) := by
    intro a
    rw [integral_finsetSum _ fun j _ => ((iPA' j a).fun_add (iAQ a j)).fun_smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul, integral_add (iPA' j a) (iAQ a j)]
  have hc1 : ∀ a, meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPhysProj a * Z ω) =
      ∫ ω, physBlockTrace (Y ω) a • (meqPhysProj a * Z ω) ∂ν -
        (∫ ω, physBlockTrace (Y ω) a ∂ν) • ∫ ω, meqPhysProj a * Z ω ∂ν :=
    fun a => meq_cov_eq (iAA a a) (iPA a)
  have hc2 : ∀ a j, meqCov ν (fun ω => portBlockTrace (Y ω) j) (fun ω => meqPhysProj a * Z ω) =
      ∫ ω, portBlockTrace (Y ω) j • (meqPhysProj a * Z ω) ∂ν -
        (∫ ω, portBlockTrace (Y ω) j ∂ν) • ∫ ω, meqPhysProj a * Z ω ∂ν :=
    fun a j => meq_cov_eq (iPA' j a) (iPA a)
  have hc3 : ∀ a j, meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPortProj j * Z ω) =
      ∫ ω, physBlockTrace (Y ω) a • (meqPortProj j * Z ω) ∂ν -
        (∫ ω, physBlockTrace (Y ω) a ∂ν) • ∫ ω, meqPortProj j * Z ω ∂ν :=
    fun a j => meq_cov_eq (iAQ a j) (iPQ j)
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_add hI1 (integrable_finsetSum _ fun a _ => hI2 a),
    integral_finsetSum _ fun a _ => (iAA a a).fun_smul c,
    integral_finsetSum _ fun a _ => hI2 a,
    Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_congr rfl fun a _ => e2 a]
  rw [sdResid, meqShift_eq_sum]
  simp only [hc1, hc2, hc3]
  simp only [Matrix.add_mul, Finset.sum_mul, Matrix.smul_mul, hcomm, meqMeanA, meqMeanP]
  simp only [smul_sub, smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_smul]
  abel

/-- **The two-resolvent Schwinger–Dyson equation.** Law `layerLaw W b σ` (conditional on the deformation: deterministic
Hermitian `X`), `W ≥ 1`, `0 ≤ b ≤ 1/2`, `c = 1 - 2b`, real `E`, `Im z ≥ 0`, every deterministic
`P`; hypotheses: a.s. invertibility of the layer matrix and `‖𝒢‖³ ∈ L¹`. With `F = 𝒢P𝒢ᴴ`,
`ḡ = g(E𝒢)`, `t̄ = g(EF)` (normalized block traces) and entrywise expectations:
`(𝒟 - 𝒮_{c,b}(ḡ)) EF = P E𝒢ᴴ + 𝒮_{c,b}(t̄) E𝒢ᴴ + sdResid(𝒢, F) + sdResid(F, 𝒢ᴴ)`,
`𝒟 = tflConst = diag(-E - X, z)`. -/
theorem twoResolvent_equation {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    {σ : LayerShape} {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ)
    {z : ℂ} (hz : 0 ≤ z.im) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hG3 : Integrable (fun ω => ‖layerResolvent σ E z X ω‖ ^ 3) (layerLaw W b σ)) :
    let ν := layerLaw W b σ
    let G := layerResolvent σ E z X
    let F := fun ω => G ω * P * (G ω)ᴴ
    (tflConst σ E z X - meqShift σ (1 - 2 * (b : ℂ)) b (meqMeanA ν G) (meqMeanP ν G)) *
        matrixExpect ν F =
      P * matrixExpect ν (fun ω => (G ω)ᴴ) +
        meqShift σ (1 - 2 * (b : ℂ)) b (meqMeanA ν F) (meqMeanP ν F) *
          matrixExpect ν (fun ω => (G ω)ᴴ) +
        sdResid ν (1 - 2 * (b : ℂ)) b G F + sdResid ν (1 - 2 * (b : ℂ)) b F (fun ω => (G ω)ᴴ) := by
  intro ν G F
  have hm : Measurable G := measurable_layerResolvent σ E z X
  have hGm : AEStronglyMeasurable G ν := hm.aestronglyMeasurable
  have cF : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => N * P * Nᴴ) :=
    (continuous_id.mul continuous_const).mul continuous_id.matrix_conjTranspose
  have hFm : AEStronglyMeasurable F ν := (cF.measurable.comp hm).aestronglyMeasurable
  have hHm : AEStronglyMeasurable (fun ω => (G ω)ᴴ) ν :=
    (continuous_id.matrix_conjTranspose.measurable.comp hm).aestronglyMeasurable
  have hD : Integrable (fun ω => 1 + ‖G ω‖ ^ 3) ν := (integrable_const 1).add hG3
  have hG1 : Integrable (fun ω => ‖G ω‖) ν :=
    hD.mono' hGm.norm (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact (sd_le_one_add_cube (norm_nonneg _)).1)
  have nF : ∀ ω, ‖F ω‖ ≤ ‖P‖ * ‖G ω‖ ^ 2 := by
    intro ω
    refine (norm_mul_le _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖G ω * P‖ * ‖G ω‖ ≤ ‖G ω‖ * ‖P‖ * ‖G ω‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖P‖ * ‖G ω‖ ^ 2 := by ring
  have hFi : Integrable F ν :=
    (hD.const_mul ‖P‖).mono' hFm (ae_of_all _ fun ω => (nF ω).trans
      (mul_le_mul_of_nonneg_left (sd_le_one_add_cube (norm_nonneg _)).2 (norm_nonneg _)))
  have hHi : Integrable (fun ω => (G ω)ᴴ) ν :=
    hG1.mono' hHm (ae_of_all _ fun ω => by rw [l2_opNorm_conjTranspose])
  have hGF : Integrable (fun ω => ‖G ω‖ * ‖F ω‖) ν :=
    (hG3.const_mul ‖P‖).mono' (hGm.norm.mul hFm.norm) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖G ω‖ * ‖F ω‖ ≤ ‖G ω‖ * (‖P‖ * ‖G ω‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (nF ω) (norm_nonneg _)
        _ = ‖P‖ * ‖G ω‖ ^ 3 := by ring)
  have hFH : Integrable (fun ω => ‖F ω‖ * ‖(G ω)ᴴ‖) ν :=
    (hG3.const_mul ‖P‖).mono' (hFm.norm.mul hHm.norm) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by positivity), l2_opNorm_conjTranspose]
      calc ‖F ω‖ * ‖G ω‖ ≤ (‖P‖ * ‖G ω‖ ^ 2) * ‖G ω‖ :=
            mul_le_mul_of_nonneg_right (nF ω) (norm_nonneg _)
        _ = ‖P‖ * ‖G ω‖ ^ 3 := by ring)
  have h := sd_limit_law b E hX hz P hinv hG3
  simp only [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0] at h
  rw [sd_expand hGm hFm hGF hFi, sd_expand hFm hHm hFH hHi] at h
  rw [meq_matrixExpect_eq hFi, meq_matrixExpect_eq hHi, sub_mul]
  change tflConst σ E z X * ∫ ω, F ω ∂ν - _ = _
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at h
  rw [← h]
  abel

end Law

end BlockBand.Critical.CommonPort
