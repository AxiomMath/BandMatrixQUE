module

public import BlockBand.Layers.CoreDyson
public import BlockBand.Layers.MeanEquations
public import BlockBand.Layers.LayerMeanBounds
public import BlockBand.Layers.PathGrowthLaw
public import BlockBand.Layers.TraceMatrix

/-!
# Schwinger–Dyson identities, fluctuations and covariances of the cores

Steps 1–2 of the proof of the matched-traces theorem for the cores: Gaussian integration by parts
in every Gaussian entry gives the vector Dyson equation, whose error collects covariances between
a normalized trace and a matrix entry, and the Gaussian Poincaré inequality bounds the fluctuation
of a normalized trace around its mean by `C√p/W` in `L^p`.

Law: a finite real Gaussian vector `x ~ gaussianProduct v` (`Inputs.gaussianProduct`, independent
centered coordinates of variances `v`). Norms: `ℓ²` operator norm on matrices, modulus on `ℂ`.

## §0. Affine Gaussian families (coordinate-free form of `MeanEquations` §2 and
`TraceFluctuation` §4)

For `x ↦ C₀ + L x` with `L` real-linear and the regularity hypothesis `CoreReg C₀ L`
(`Ψ_κ(x) = C₀ + iκ + L x` invertible with `‖Ψ_κ(x)⁻¹‖ ≤ κ⁻¹` for all `x`, `κ > 0`):
* `core_reg_identity`: `(C₀ + iκ) E[G_κ] - E[S(G_κ) G_κ] = I`, `S(G) = Σᵢ vᵢ Λᵢ G Λᵢ`;
* `core_limit_identity`: `C₀ E[G] - E[S(G) G] = I` under a.s. invertibility and `‖G‖ ∈ L²`;
* `core_fluctuation`: `‖w Tr(D G) - E‖_p ≤ Cg √p (4|w|Γ‖D‖) C_A²` from the Gaussian gradient
  inequality (constant `Cg`), the coordinate-trace bound `Σᵢ vᵢ |Tr(K Λᵢ)|² ≤ Γ² ‖K‖²` and
  `‖‖G‖‖_{2p} ≤ C_A`.

## §1–2. Block traces and `L^p` bookkeeping

* `core_vector_dyson` (the vector Dyson equation): a block-constant identity
  `diag(h) E[G] - E[diag(Σ_γ w_βγ g_γ) G] = I` gives
  `(h_β - Σ_γ w_βγ ḡ_γ) ḡ_β = 1 + Σ_γ w_βγ Cov(g_γ, g_β)` (block traces `g = coreTr G`).
* `core_cov_le`, `core_cov_tr`: `|Cov(g_γ, g_β)| ≤ A²` from `‖g - ḡ‖₂ ≤ A` (Cauchy–Schwarz);
  this replaces `TraceMatrixContract.covariance` (only traces of the residual are needed).
* `core_final` (Minkowski), `core_eLpNorm_prod_le` and `core_ae_prod` (Tonelli/Fubini for
  conditioning on an independent coordinate), `core_norm_mean_le`, `core_resid_le`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 0. Schwinger–Dyson identity and fluctuation for an affine Gaussian family

A finite real Gaussian vector `x ~ gaussianProduct v` and an affine matrix family
`x ↦ C₀ + L x`, regularized as `Ψ_κ(x) = C₀ + iκ + L x`, under the hypothesis `CoreReg`:
`Ψ_κ(x)` is invertible with `‖Ψ_κ(x)⁻¹‖ ≤ κ⁻¹` for every `x` and `κ > 0`. This is the
coordinate-free form of `MeanEquations` (§2) and `TraceFluctuation` (§4); it is used for the
two-block core, whose internal bond is one more Gaussian coordinate.
-/

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
  {n : Type} [Fintype n] [DecidableEq n]
  (C0 : Matrix n n ℂ) (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ)

/-- The regularized affine family `Ψ_κ(x) = C₀ + iκ + L x`. -/
def corePsi (κ : ℝ) (x : ι → ℝ) : Matrix n n ℂ :=
  C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) + L x

/-- The regularized resolvent `G_κ = Ψ_κ⁻¹`. -/
def coreG (κ : ℝ) (x : ι → ℝ) : Matrix n n ℂ := Ring.inverse (corePsi C0 L κ x)

/-- The Gaussian contraction `S(G) = Σᵢ vᵢ Λᵢ G Λᵢ`, `Λᵢ = L eᵢ`. -/
def coreS (G : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (v i : ℝ) • (L (Pi.single i 1) * G * L (Pi.single i 1))

/-- The regularity hypothesis. -/
def CoreReg : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ x : ι → ℝ, IsUnit (corePsi C0 L κ x) ∧ ‖Ring.inverse (corePsi C0 L κ x)‖ ≤ κ⁻¹

variable {C0 L}

omit [DecidableEq ι] in
theorem coreG_hasFDerivAt (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) :
    HasFDerivAt (coreG C0 L κ)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (coreG C0 L κ x)
        (coreG C0 L κ x))).comp L) x := by
  set u := (hreg κ hκ x).1.unit with hu
  have hL : HasFDerivAt (corePsi C0 L κ) L x := L.hasFDerivAt.const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹ ↑u⁻¹)) (corePsi C0 L κ x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [IsUnit.unit_spec] at this
  have hinv : (↑u⁻¹ : Matrix n n ℂ) = coreG C0 L κ x := by
    rw [coreG, ← Ring.inverse_unit, IsUnit.unit_spec]
  rw [hinv] at h
  exact h.comp x hL

omit [DecidableEq ι] in
theorem coreG_contDiff (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (coreG C0 L κ) := by
  have hL : ContDiff ℝ 1 (corePsi C0 L κ) := contDiff_const.add L.contDiff
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := contDiffAt_ringInverse ℝ (n := 1) (hreg κ hκ x).1.unit
  rw [IsUnit.unit_spec] at h
  exact h.comp x hL.contDiffAt

omit [Fintype ι] [DecidableEq ι] in
theorem coreG_norm_le (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) :
    ‖coreG C0 L κ x‖ ≤ κ⁻¹ := (hreg κ hκ x).2

omit [DecidableEq ι] in
theorem coreG_continuous (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (coreG C0 L κ) := (coreG_contDiff hreg hκ).continuous

omit [Fintype n] [DecidableEq n] in
theorem core_lin_decomp (x : ι → ℝ) : L x = ∑ i, x i • L (Pi.single i 1) := by
  have h := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] Matrix n n ℂ) x
  have hs : ∀ i : ι, (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 :=
    fun i => by funext j; simp [Pi.single_apply, eq_comm]
  simp only [hs] at h
  exact h

theorem core_ibp_coord (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) (i : ι) :
    ∫ x, x i • (L (Pi.single i 1) * coreG C0 L κ x) ∂gaussianProduct v =
      (v i : ℝ) • ∫ x, -(L (Pi.single i 1) * coreG C0 L κ x *
        L (Pi.single i 1) * coreG C0 L κ x) ∂gaussianProduct v := by
  set Λ := L (Pi.single i 1) with hΛ
  set G := coreG C0 L κ with hG
  have hk : ContDiff ℝ 1 (fun x => Λ * G x) :=
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) Λ).contDiff.comp (coreG_contDiff hreg hκ)
  have hder : ∀ x, HasFDerivAt (fun x => Λ * G x)
      ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) Λ).comp
        ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (G x) (G x))).comp L)) x :=
    fun x => ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) Λ).hasFDerivAt).comp x
      (coreG_hasFDerivAt hreg hκ x)
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hb : ∀ x, ‖Λ * G x‖ ≤ ‖Λ‖ * κ⁻¹ := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (coreG_norm_le hreg hκ x) (norm_nonneg _))
  have hb' : ∀ x, ‖fderiv ℝ (fun x => Λ * G x) x‖ ≤ ‖Λ‖ * (κ⁻¹ * ‖L‖ * κ⁻¹) := by
    intro x
    rw [(hder x).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
    have hGx := coreG_norm_le hreg hκ x
    calc ‖Λ * -(G x * L w * G x)‖ ≤ ‖Λ‖ * (‖G x‖ * ‖L w‖ * ‖G x‖) := by
          refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          rw [norm_neg]
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ ‖Λ‖ * (κ⁻¹ * (‖L‖ * ‖w‖) * κ⁻¹) := by
          gcongr
          exact L.le_opNorm w
      _ = ‖Λ‖ * (κ⁻¹ * ‖L‖ * κ⁻¹) * ‖w‖ := by ring
  rw [ou_ibp v i hk hb hb']
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  beta_reduce
  rw [(hder x).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply]
  rw [← hΛ]
  simp only [Matrix.mul_neg, Matrix.mul_assoc]

/-- **Gaussian integration by parts**: `E[L(x) G_κ] = -E[S(G_κ) G_κ]`. -/
theorem core_ibp (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) :
    ∫ x, L x * coreG C0 L κ x ∂gaussianProduct v =
      -∫ x, coreS v L (coreG C0 L κ x) * coreG C0 L κ x ∂gaussianProduct v := by
  set μ := gaussianProduct v
  set G := coreG C0 L κ with hG
  have hGc : Continuous G := coreG_continuous hreg hκ
  have hGb : ∀ x, ‖G x‖ ≤ κ⁻¹ := coreG_norm_le hreg hκ
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hdec : ∀ x, L x * G x = ∑ i, x i • (L (Pi.single i 1) * G x) := by
    intro x
    rw [core_lin_decomp x, Finset.sum_mul]
    simp only [Matrix.smul_mul]
  have hint : ∀ i : ι, Integrable (fun x => x i • (L (Pi.single i 1) * G x)) μ := by
    intro i
    refine ou_integrable_of_norm_le μ
      ((continuous_apply i).smul (continuous_const.mul hGc)).aestronglyMeasurable 0
      (‖L (Pi.single i 1)‖ * κ⁻¹) fun x => ?_
    rw [norm_smul, zero_add]
    have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    have h2 : ‖L (Pi.single i 1) * G x‖ ≤ ‖L (Pi.single i 1)‖ * κ⁻¹ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _))
    calc ‖x i‖ * ‖L (Pi.single i 1) * G x‖
        ≤ ‖x‖ * (‖L (Pi.single i 1)‖ * κ⁻¹) :=
          mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = ‖L (Pi.single i 1)‖ * κ⁻¹ * ‖x‖ := by ring
  have hint2 : ∀ i : ι, Integrable (fun x => -(L (Pi.single i 1) * G x *
      L (Pi.single i 1) * G x)) μ := by
    intro i
    refine Integrable.of_bound (by fun_prop) (‖L (Pi.single i 1)‖ ^ 2 * κ⁻¹ ^ 2)
      (ae_of_all _ fun x => ?_)
    set Λ := L (Pi.single i 1)
    rw [norm_neg]
    calc ‖Λ * G x * Λ * G x‖ ≤ ‖Λ * G x * Λ‖ * ‖G x‖ := norm_mul_le _ _
      _ ≤ ‖Λ * G x‖ * ‖Λ‖ * ‖G x‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖Λ‖ * ‖G x‖ * ‖Λ‖ * ‖G x‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖Λ‖ * κ⁻¹ * ‖Λ‖ * κ⁻¹ := by gcongr <;> exact hGb x
      _ = ‖Λ‖ ^ 2 * κ⁻¹ ^ 2 := by ring
  have hpt : ∀ x, -(coreS v L (G x) * G x) = ∑ i, (v i : ℝ) •
      -(L (Pi.single i 1) * G x * L (Pi.single i 1) * G x) := by
    intro x
    unfold coreS
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, smul_neg]
  have hint3 : ∀ i : ι, Integrable (fun x => (v i : ℝ) •
      -(L (Pi.single i 1) * G x * L (Pi.single i 1) * G x)) μ :=
    fun i => (hint2 i).fun_smul (v i : ℝ)
  rw [integral_congr_ae (ae_of_all _ hdec), integral_finsetSum _ fun i _ => hint i,
    ← integral_neg, integral_congr_ae (ae_of_all _ hpt),
    integral_finsetSum _ fun i _ => hint3 i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul]
  exact core_ibp_coord v hreg hκ i

/-- **Regularized Schwinger–Dyson identity**: `(C₀ + iκ) E[G_κ] - E[S(G_κ) G_κ] = I`. -/
theorem core_reg_identity (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) :
    (C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ)) * ∫ x, coreG C0 L κ x ∂gaussianProduct v -
      ∫ x, coreS v L (coreG C0 L κ x) * coreG C0 L κ x ∂gaussianProduct v = 1 := by
  set μ := gaussianProduct v
  set G := coreG C0 L κ with hG
  set C := C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) with hC
  have hGc : Continuous G := coreG_continuous hreg hκ
  have hGi : Integrable G μ := Integrable.of_bound hGc.aestronglyMeasurable κ⁻¹
    (ae_of_all _ fun x => coreG_norm_le hreg hκ x)
  have hpt : ∀ x, C * G x + L x * G x = 1 := by
    intro x
    rw [← add_mul]
    exact Ring.mul_inverse_cancel _ (hreg κ hκ x).1
  have hint2 : Integrable (fun x => L x * G x) μ := by
    refine ou_integrable_of_norm_le μ ((L.continuous.mul hGc).aestronglyMeasurable) 0
      (‖L‖ * κ⁻¹) fun x => ?_
    rw [zero_add]
    calc ‖L x * G x‖ ≤ ‖L x‖ * ‖G x‖ := norm_mul_le _ _
      _ ≤ (‖L‖ * ‖x‖) * κ⁻¹ := by
          gcongr
          · exact L.le_opNorm x
          · exact coreG_norm_le hreg hκ x
      _ = ‖L‖ * κ⁻¹ * ‖x‖ := by ring
  have h1 : ∫ x, (C * G x + L x * G x) ∂μ = 1 := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const, probReal_univ, one_smul]
  rw [integral_add (hGi.const_mul C) hint2, core_ibp v hreg hκ] at h1
  have h2 : ∫ x, C * G x ∂μ = C * ∫ x, G x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) C).integral_comp_comm hGi
  rw [h2] at h1
  rw [sub_eq_add_neg]
  exact h1

/-- The operator-norm constant of `S`. -/
def coreCS (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ) : ℝ := ∑ i, (v i : ℝ) * ‖L (Pi.single i 1)‖ ^ 2

theorem coreCS_nonneg (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ) : 0 ≤ coreCS v L :=
  Finset.sum_nonneg fun i _ => mul_nonneg (v i).2 (by positivity)

theorem core_norm_S_le (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ) (G : Matrix n n ℂ) : ‖coreS v L G‖ ≤ coreCS v L * ‖G‖ := by
  unfold coreS coreCS
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  set Λ := L (Pi.single i 1)
  have hv : ‖((v i : ℝ≥0) : ℝ)‖ = (v i : ℝ) := by simp
  have h1 : ‖Λ * G * Λ‖ ≤ ‖Λ‖ ^ 2 * ‖G‖ :=
    calc ‖Λ * G * Λ‖ ≤ ‖Λ * G‖ * ‖Λ‖ := norm_mul_le _ _
      _ ≤ ‖Λ‖ * ‖G‖ * ‖Λ‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖Λ‖ ^ 2 * ‖G‖ := by ring
  calc ‖(v i : ℝ) • (Λ * G * Λ)‖ = (v i : ℝ) * ‖Λ * G * Λ‖ := by rw [norm_smul, hv]
    _ ≤ (v i : ℝ) * (‖Λ‖ ^ 2 * ‖G‖) := mul_le_mul_of_nonneg_left h1 (v i).2
    _ = (v i : ℝ) * ‖Λ‖ ^ 2 * ‖G‖ := by ring

omit [DecidableEq n] in
theorem core_continuous_S_mul (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ) :
    Continuous (fun G : Matrix n n ℂ => coreS v L G * G) := by
  unfold coreS
  exact (continuous_finsetSum _ fun i _ => by fun_prop).mul continuous_id

omit [Fintype ι] [DecidableEq ι] in
/-- The regularized inverse is at most twice the inverse (wherever `C₀ + L x` is invertible). -/
theorem coreG_le_two (hreg : CoreReg C0 L) {κ : ℝ} (hκ : 0 < κ) {x : ι → ℝ}
    (hx : IsUnit (C0 + L x).det) : ‖coreG C0 L κ x‖ ≤ 2 * ‖(C0 + L x)⁻¹‖ := by
  have hc : ((κ : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne') Complex.I_ne_zero
  have hnc : ‖(κ : ℂ) * Complex.I‖ = κ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  have he : corePsi C0 L κ x = (C0 + L x) + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) := by
    unfold corePsi; abel
  have hu := (hreg κ hκ x).1
  have hb := (hreg κ hκ x).2
  rw [he, ← Matrix.nonsing_inv_eq_ringInverse] at hb
  rw [he, Matrix.isUnit_iff_isUnit_det] at hu
  rw [coreG, he, ← Matrix.nonsing_inv_eq_ringInverse]
  refine tfl_inv_add_le_two hc hx hu ?_
  rw [hnc]; exact hb

/-- **Exact Schwinger–Dyson identity** under a.s. invertibility and `‖(C₀ + L x)⁻¹‖ ∈ L²`:
`C₀ E[G] - E[S(G) G] = I`. -/
theorem core_limit_identity (hreg : CoreReg C0 L)
    (hinv : ∀ᵐ x ∂gaussianProduct v, IsUnit (C0 + L x).det)
    (hG2 : Integrable (fun x => ‖(C0 + L x)⁻¹‖ ^ 2) (gaussianProduct v)) :
    C0 * ∫ x, (C0 + L x)⁻¹ ∂gaussianProduct v -
      ∫ x, coreS v L ((C0 + L x)⁻¹) * (C0 + L x)⁻¹ ∂gaussianProduct v = 1 := by
  set μ := gaussianProduct v
  set G0 : (ι → ℝ) → Matrix n n ℂ := fun x => (C0 + L x)⁻¹ with hG0
  have hG0c : Measurable G0 :=
    measurable_matrix_inv.comp (continuous_const.add L.continuous).measurable
  have hG1 : Integrable (fun x => ‖G0 x‖) μ :=
    meq_integrable_norm_of_sq hG0c.aestronglyMeasurable hG2
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Gm : ℕ → (ι → ℝ) → Matrix n n ℂ := fun m => coreG C0 L (κm m) with hGm
  have hGmc : ∀ m, Continuous (Gm m) := fun m => coreG_continuous hreg (hκpos m)
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Gm m x) atTop (𝓝 (G0 x)) := by
    filter_upwards [hinv] with x hx
    set N := C0 + L x with hN
    have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
    have hcN : Continuous (fun κ : ℝ => C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) + L x) := by
      fun_prop
    have h1 : Tendsto (fun m => corePsi C0 L (κm m) x) atTop (𝓝 N) := by
      have := (hcN.tendsto 0).comp hκlim
      simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
      exact this
    have h2 : Tendsto (fun m => Ring.inverse (corePsi C0 L (κm m) x)) atTop
        (𝓝 (Ring.inverse N)) := by
      have hc := NormedRing.inverse_continuousAt hU.unit
      rw [IsUnit.unit_spec] at hc
      exact hc.tendsto.comp h1
    have hG0x : G0 x = Ring.inverse N := by
      rw [hG0]; simp only; rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [hG0x]
    exact h2
  have hbd : ∀ m, ∀ᵐ x ∂μ, ‖Gm m x‖ ≤ 2 * ‖G0 x‖ := by
    intro m
    filter_upwards [hinv] with x hx
    exact coreG_le_two hreg (hκpos m) hx
  have hlim1 : Tendsto (fun m => ∫ x, Gm m x ∂μ) atTop (𝓝 (∫ x, G0 x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => 2 * ‖G0 x‖)
      (fun m => (hGmc m).aestronglyMeasurable) (hG1.const_mul 2) hbd hconv
  have hbd2 : ∀ m, ∀ᵐ x ∂μ, ‖coreS v L (Gm m x) * Gm m x‖ ≤ 4 * coreCS v L * ‖G0 x‖ ^ 2 := by
    intro m
    filter_upwards [hbd m] with x hx
    have h1 : ‖coreS v L (Gm m x) * Gm m x‖ ≤ coreCS v L * ‖Gm m x‖ ^ 2 :=
      calc ‖coreS v L (Gm m x) * Gm m x‖ ≤ ‖coreS v L (Gm m x)‖ * ‖Gm m x‖ := norm_mul_le _ _
        _ ≤ coreCS v L * ‖Gm m x‖ * ‖Gm m x‖ := by gcongr; exact core_norm_S_le v L _
        _ = coreCS v L * ‖Gm m x‖ ^ 2 := by ring
    have h0 : ‖Gm m x‖ ^ 2 ≤ (2 * ‖G0 x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have hCS := coreCS_nonneg v L
    nlinarith
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => coreS v L (Gm m x) * Gm m x) atTop
      (𝓝 (coreS v L (G0 x) * G0 x)) :=
    hconv.mono fun x hx => ((core_continuous_S_mul v L).tendsto _).comp hx
  have hlim2 : Tendsto (fun m => ∫ x, coreS v L (Gm m x) * Gm m x ∂μ) atTop
      (𝓝 (∫ x, coreS v L (G0 x) * G0 x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => 4 * coreCS v L * ‖G0 x‖ ^ 2)
      (fun m => ((core_continuous_S_mul v L).comp (hGmc m)).aestronglyMeasurable)
      (hG2.const_mul _) hbd2 hconv2
  have hcC : Continuous (fun κ : ℝ => C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ)) := by
    fun_prop
  have hlimC : Tendsto (fun m => C0 + ((κm m : ℂ) * Complex.I) • (1 : Matrix n n ℂ)) atTop
      (𝓝 C0) := by
    have := (hcC.tendsto 0).comp hκlim
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
    exact this
  have hlim := (hlimC.mul hlim1).sub hlim2
  have hconst : (fun m => (C0 + ((κm m : ℂ) * Complex.I) • (1 : Matrix n n ℂ)) *
      ∫ x, Gm m x ∂μ - ∫ x, coreS v L (Gm m x) * Gm m x ∂μ) = fun _ => 1 := by
    funext m
    exact core_reg_identity v hreg (hκpos m)
  rw [hconst] at hlim
  exact (tendsto_nhds_unique hlim tendsto_const_nhds)

/-- The weighted trace functional `M ↦ w Tr(D M)` (real-linear). -/
def coreTrLin (w : ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℝ] ℂ where
  toFun M := (w : ℂ) * (D * M).trace
  map_add' M N := by simp [Matrix.trace_add, mul_add]
  map_smul' r M := by simp [Matrix.trace_smul]; ring

theorem coreTrLin_apply (w : ℝ) (D M : Matrix n n ℂ) :
    coreTrLin w D M = (w : ℂ) * (D * M).trace := rfl

/-- The regularized trace `f_κ(x) = w Tr(D G_κ(x))`. -/
def coreF (C0 : Matrix n n ℂ) (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ) (w : ℝ) (D : Matrix n n ℂ)
    (κ : ℝ) (x : ι → ℝ) : ℂ :=
  LinearMap.toContinuousLinearMap (coreTrLin w D) (coreG C0 L κ x)

omit [DecidableEq ι] in
theorem coreF_contDiff (hreg : CoreReg C0 L) (w : ℝ) (D : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (coreF C0 L w D κ) :=
  (ContinuousLinearMap.contDiff _).comp (coreG_contDiff hreg hκ)

omit [DecidableEq ι] in
theorem coreF_fderiv (hreg : CoreReg C0 L) (w : ℝ) (D : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ)
    (x y : ι → ℝ) :
    fderiv ℝ (coreF C0 L w D κ) x y =
      -((w : ℂ) * (coreG C0 L κ x * D * coreG C0 L κ x * L y).trace) := by
  have h := ((LinearMap.toContinuousLinearMap (coreTrLin w D)).hasFDerivAt).comp x
    (coreG_hasFDerivAt hreg hκ x)
  rw [show coreF C0 L w D κ = (LinearMap.toContinuousLinearMap (coreTrLin w D)) ∘ coreG C0 L κ
    from rfl, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, LinearMap.coe_toContinuousLinearMap', map_neg,
    coreTrLin_apply]
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]

/-- **Gradient bound** of the regularized trace, from the weighted coordinate-trace bound
`Σᵢ vᵢ |Tr(K Λᵢ)|² ≤ Γ² ‖K‖²`: `|∇f_κ|_v ≤ |w| Γ ‖D‖ ‖G_κ‖²`. -/
theorem coreF_gradient_le (hreg : CoreReg C0 L) {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hgw : ∀ K : Matrix n n ℂ, ∑ i, (v i : ℝ) * ‖(K * L (Pi.single i 1)).trace‖ ^ 2 ≤
      Γ ^ 2 * ‖K‖ ^ 2) (w : ℝ) (D : Matrix n n ℂ) {κ : ℝ} (hκ : 0 < κ) (x : ι → ℝ) :
    weightedGradientNorm v (coreF C0 L w D κ) x ≤ |w| * Γ * ‖D‖ * ‖coreG C0 L κ x‖ ^ 2 := by
  set G := coreG C0 L κ x
  set K := G * D * G with hK
  have hK' : ‖K‖ ≤ ‖D‖ * ‖G‖ ^ 2 := by
    calc ‖K‖ ≤ ‖G * D‖ * ‖G‖ := norm_mul_le _ _
      _ ≤ ‖G‖ * ‖D‖ * ‖G‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖D‖ * ‖G‖ ^ 2 := by ring
  have hder : ∀ i : ι, ‖fderiv ℝ (coreF C0 L w D κ) x (Pi.single i 1)‖ ^ 2 =
      w ^ 2 * ‖(K * L (Pi.single i 1)).trace‖ ^ 2 := by
    intro i
    rw [coreF_fderiv hreg w D hκ, norm_neg, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hsum : ∑ i, (v i : ℝ) * ‖fderiv ℝ (coreF C0 L w D κ) x (Pi.single i 1)‖ ^ 2 ≤
      (|w| * Γ * ‖D‖ * ‖G‖ ^ 2) ^ 2 := by
    simp_rw [hder]
    have e : ∑ i, (v i : ℝ) * (w ^ 2 * ‖(K * L (Pi.single i 1)).trace‖ ^ 2) =
        w ^ 2 * ∑ i, (v i : ℝ) * ‖(K * L (Pi.single i 1)).trace‖ ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have hK2 : ‖K‖ ^ 2 ≤ (‖D‖ * ‖G‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hK' 2
    calc w ^ 2 * ∑ i, (v i : ℝ) * ‖(K * L (Pi.single i 1)).trace‖ ^ 2
        ≤ w ^ 2 * (Γ ^ 2 * ‖K‖ ^ 2) := by gcongr; exact hgw K
      _ ≤ w ^ 2 * (Γ ^ 2 * (‖D‖ * ‖G‖ ^ 2) ^ 2) := by gcongr
      _ = (|w| * Γ * ‖D‖ * ‖G‖ ^ 2) ^ 2 := by
          have : |w| ^ 2 = w ^ 2 := sq_abs w
          linear_combination (-(Γ ^ 2 * ‖D‖ ^ 2 * (‖G‖ ^ 2) ^ 2)) * this
  unfold weightedGradientNorm
  calc Real.sqrt (∑ i, (v i : ℝ) * ‖fderiv ℝ (coreF C0 L w D κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt ((|w| * Γ * ‖D‖ * ‖G‖ ^ 2) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = |w| * Γ * ‖D‖ * ‖G‖ ^ 2 := Real.sqrt_sq (by positivity)

omit [Fintype ι] [DecidableEq ι] in
theorem coreF_norm_le (w : ℝ) (D : Matrix n n ℂ) (κ : ℝ) (x : ι → ℝ) :
    ‖coreF C0 L w D κ x‖ ≤ |w| * (Fintype.card n * (‖D‖ * ‖coreG C0 L κ x‖)) := by
  rw [coreF, LinearMap.coe_toContinuousLinearMap', coreTrLin_apply, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  gcongr
  exact (tfl_trace_le _).trans (by gcongr; exact norm_mul_le _ _)

/-- **Fluctuation bound for an affine Gaussian family** (`tfl_fluctuation_core` without the layer
structure): with the gradient inequality constant `Cg`, `CoreReg`, the coordinate-trace bound
`Γ`, a.s. invertibility of `C₀ + L x` and `‖‖(C₀ + L x)⁻¹‖‖_{2p} ≤ C_A`:
`‖F - EF‖_p ≤ Cg √p (4|w|Γ‖D‖) C_A²` for `F(x) = w Tr(D (C₀ + L x)⁻¹)`. -/
theorem core_fluctuation {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    (hreg : CoreReg C0 L) {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hgw : ∀ K : Matrix n n ℂ, ∑ i, (v i : ℝ) * ‖(K * L (Pi.single i 1)).trace‖ ^ 2 ≤
      Γ ^ 2 * ‖K‖ ^ 2) (w : ℝ) (D : Matrix n n ℂ) {p : ℝ} (hp : 1 ≤ p) {CA : ℝ} (hCA : 0 ≤ CA)
    (hinv : ∀ᵐ x ∂gaussianProduct v, IsUnit (C0 + L x).det)
    (hmom : eLpNorm (fun x => ‖(C0 + L x)⁻¹‖) (ENNReal.ofReal (2 * p)) (gaussianProduct v) ≤
      ENNReal.ofReal CA) :
    eLpNorm (fun x => (w : ℂ) * (D * (C0 + L x)⁻¹).trace -
        ∫ y, (w : ℂ) * (D * (C0 + L y)⁻¹).trace ∂gaussianProduct v)
        (ENNReal.ofReal p) (gaussianProduct v) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (4 * |w| * Γ * ‖D‖) * CA ^ 2) := by
  set μ := gaussianProduct v with hμ
  set Gr : (ι → ℝ) → Matrix n n ℂ := fun x => (C0 + L x)⁻¹ with hGrdef
  have hGr : Measurable Gr :=
    measurable_matrix_inv.comp (continuous_const.add L.continuous).measurable
  set F : (ι → ℝ) → ℂ := fun x => (w : ℂ) * (D * Gr x).trace with hFdef
  have hFc : Continuous (fun M : Matrix n n ℂ => (w : ℂ) * (D * M).trace) :=
    continuous_const.mul (continuous_const.matrix_mul continuous_id).matrix_trace
  have hF : Measurable F := hFc.measurable.comp hGr
  change eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ ≤ _
  have hp0 : 0 ≤ p := by linarith
  have hGrmem : MemLp (fun x => ‖Gr x‖) (ENNReal.ofReal (2 * p)) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hmom ENNReal.ofReal_lt_top
  have hGrint : Integrable (fun x => ‖Gr x‖) μ :=
    hGrmem.integrable (by rw [ENNReal.one_le_ofReal]; linarith)
  have hsq : eLpNorm (fun x => ‖Gr x‖ ^ 2) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (CA ^ 2) := by
    have e1 : (fun x => ‖Gr x‖ ^ 2) = fun x => ‖Gr x‖ ^ (2 : ℝ) := by
      funext x; rw [Real.rpow_two]
    rw [e1, eLpNorm_norm_rpow Gr hGr.aestronglyMeasurable two_pos,
      ← ENNReal.ofReal_mul hp0, mul_comm p 2, ENNReal.ofReal_pow hCA]
    have hmom' : eLpNorm Gr (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal CA := by
      rw [← eLpNorm_norm _ hGr.aestronglyMeasurable]; exact hmom
    calc eLpNorm Gr (ENNReal.ofReal (2 * p)) μ ^ (2 : ℝ) ≤ ENNReal.ofReal CA ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hmom' (by norm_num)
      _ = ENNReal.ofReal CA ^ 2 := by rw [← ENNReal.rpow_natCast]; norm_num
  set c : ℝ := 4 * |w| * Γ * ‖D‖ with hc
  have hc0 : 0 ≤ c := by positivity
  set B : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p * c * CA ^ 2) with hB
  have hstep : ∀ κ : ℝ, 0 < κ →
      eLpNorm (fun x => coreF C0 L w D κ x - ∫ y, coreF C0 L w D κ y ∂μ)
        (ENNReal.ofReal p) μ ≤ B := by
    intro κ hκ
    have hC := coreF_contDiff hreg w D hκ
    have hmem : MemLp (coreF C0 L w D κ) (ENNReal.ofReal p) μ := by
      refine MemLp.of_bound hC.continuous.aestronglyMeasurable
        (|w| * (Fintype.card n * (‖D‖ * κ⁻¹))) (ae_of_all _ fun x => ?_)
      refine (coreF_norm_le w D κ x).trans ?_
      gcongr
      exact coreG_norm_le hreg hκ x
    have h1 := hgr p hp ι v (coreF C0 L w D κ) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm v (coreF C0 L w D κ)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm v (coreF C0 L w D κ) x‖ ≤ ‖c * ‖Gr x‖ ^ 2‖ := by
      filter_upwards [hinv] with x hx
      have hg := coreF_gradient_le v hreg hΓ hgw w D hκ x
      have h2 := coreG_le_two hreg hκ hx
      have hg0 : 0 ≤ weightedGradientNorm v (coreF C0 L w D κ) x := Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg (by positivity)]
      refine hg.trans ?_
      have h3 : ‖coreG C0 L κ x‖ ^ 2 ≤ (2 * ‖Gr x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      calc |w| * Γ * ‖D‖ * ‖coreG C0 L κ x‖ ^ 2 ≤ |w| * Γ * ‖D‖ * (2 * ‖Gr x‖) ^ 2 := by gcongr
        _ ≤ c * ‖Gr x‖ ^ 2 := by
            rw [hc]
            have : 0 ≤ |w| * Γ * ‖D‖ * ‖Gr x‖ ^ 2 := by positivity
            nlinarith
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => c * ‖Gr x‖ ^ 2) (ENNReal.ofReal p) μ =
        ENNReal.ofReal c * eLpNorm (fun x => ‖Gr x‖ ^ 2) (ENNReal.ofReal p) μ := by
      rw [show (fun x => c * ‖Gr x‖ ^ 2) = c • (fun x => ‖Gr x‖ ^ 2) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]
    calc ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm v (coreF C0 L w D κ)) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal c * ENNReal.ofReal (CA ^ 2)) := by
          gcongr
          exact h4.trans (h5.le.trans (by gcongr))
      _ = B := by
          rw [hB, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  set κm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1) with hκm
  have hκpos : ∀ m, 0 < κm m := fun m => by rw [hκm]; positivity
  have hκlim : Tendsto κm atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Fm : ℕ → (ι → ℝ) → ℂ := fun m => coreF C0 L w D (κm m) with hFm
  have hFmc : ∀ m, Continuous (Fm m) := fun m => (coreF_contDiff hreg w D (hκpos m)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x) atTop (𝓝 (F x)) := by
    filter_upwards [hinv] with x hx
    set N := C0 + L x with hN
    have hU : IsUnit N := (Matrix.isUnit_iff_isUnit_det N).mpr hx
    have hcN : Continuous (fun κ : ℝ => C0 + ((κ : ℂ) * Complex.I) • (1 : Matrix n n ℂ) + L x) := by
      fun_prop
    have h1 : Tendsto (fun m => corePsi C0 L (κm m) x) atTop (𝓝 N) := by
      have := (hcN.tendsto 0).comp hκlim
      simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
      exact this
    have h2 : Tendsto (fun m => Ring.inverse (corePsi C0 L (κm m) x)) atTop
        (𝓝 (Ring.inverse N)) := by
      have hc := NormedRing.inverse_continuousAt hU.unit
      rw [IsUnit.unit_spec] at hc
      exact hc.tendsto.comp h1
    have h3 := (((LinearMap.toContinuousLinearMap (coreTrLin w D)).continuous.tendsto _)).comp h2
    have hFx : F x = LinearMap.toContinuousLinearMap (coreTrLin w D) (Ring.inverse N) := by
      rw [LinearMap.coe_toContinuousLinearMap', coreTrLin_apply,
        ← Matrix.nonsing_inv_eq_ringInverse]
    rw [hFx]
    exact h3
  have hbound : ∀ m, ∀ᵐ x ∂μ, ‖Fm m x‖ ≤ 2 * (|w| * (Fintype.card n * ‖D‖)) * ‖Gr x‖ := by
    intro m
    filter_upwards [hinv] with x hx
    refine (coreF_norm_le w D (κm m) x).trans ?_
    have := coreG_le_two hreg (hκpos m) hx
    calc |w| * (Fintype.card n * (‖D‖ * ‖coreG C0 L (κm m) x‖))
        ≤ |w| * (Fintype.card n * (‖D‖ * (2 * ‖Gr x‖))) := by gcongr
      _ = 2 * (|w| * (Fintype.card n * ‖D‖)) * ‖Gr x‖ := by ring
  have hint : Tendsto (fun m => ∫ x, Fm m x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence _
      (fun m => (hFmc m).aestronglyMeasurable) (hGrint.const_mul _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun m => Fm m x - ∫ y, Fm m y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun m => ((hFmc m).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun m => ?_))
  exact hstep (κm m) (hκpos m)

end Generic

/-!
## 1. Block traces of a layer matrix
-/

section BlockTraces

variable {W : ℕ} {σ : LayerShape}

/-- The block (physical block or port) of a layer site. -/
def coreBlk : LayerSite W σ → Fin σ.blocks ⊕ Fin σ.ports := Sum.map Prod.fst Prod.fst

/-- The normalized block trace of every block (physical blocks `inl a`, ports `inr j`). -/
def coreTr (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Fin σ.blocks ⊕ Fin σ.ports → ℂ :=
  Sum.elim (physBlockTrace M) (portBlockTrace M)

/-- The block projection (`P_a` or `Q_j`). -/
def coreProj : Fin σ.blocks ⊕ Fin σ.ports → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  Sum.elim meqPhysProj meqPortProj

/-- The normalized block trace as a continuous linear map. -/
def coreTrCLM : Fin σ.blocks ⊕ Fin σ.ports →
    (Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℂ] ℂ)
  | .inl a => meqPhysTraceCLM a
  | .inr j => meqPortTraceCLM j

theorem coreTrCLM_apply (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (β : Fin σ.blocks ⊕ Fin σ.ports) : coreTrCLM β M = coreTr M β := by
  rcases β with a | j <;> rfl

theorem core_tr_eq_trace (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (β : Fin σ.blocks ⊕ Fin σ.ports) : coreTr M β = (W : ℂ)⁻¹ * (coreProj β * M).trace := by
  rcases β with a | j
  · exact lct_phys_eq_trace M a
  · exact lct_port_eq_trace M j

theorem core_norm_proj_le (β : Fin σ.blocks ⊕ Fin σ.ports) :
    ‖(coreProj β : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤ 1 := by
  rcases β with a | j
  · exact meq_norm_physProj_le a
  · exact meq_norm_portProj_le j

theorem core_norm_tr_le (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (β : Fin σ.blocks ⊕ Fin σ.ports) : ‖coreTr M β‖ ≤ ‖M‖ := by
  rcases β with a | j
  · exact meq_norm_physBlockTrace_le M a
  · exact meq_norm_portBlockTrace_le M j

theorem core_continuous_tr (β : Fin σ.blocks ⊕ Fin σ.ports) :
    Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => coreTr M β) := by
  rcases β with a | j
  · exact meq_continuous_physBlockTrace a
  · exact meq_continuous_portBlockTrace j

/-- Block traces of a block-constant diagonal matrix times `M`. -/
theorem core_tr_diag_mul (f : Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (β : Fin σ.blocks ⊕ Fin σ.ports) :
    coreTr (diagonal (fun x => f (coreBlk x)) * M) β = f β * coreTr M β := by
  rcases β with a | j
  · simp only [coreTr, Sum.elim_inl, physBlockTrace, diagonal_mul, coreBlk, Sum.map_inl,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [coreTr, Sum.elim_inr, portBlockTrace, diagonal_mul, coreBlk, Sum.map_inr,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem core_tr_one (hW : 0 < W) (β : Fin σ.blocks ⊕ Fin σ.ports) :
    coreTr (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) β = 1 := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  rcases β with a | j <;>
    simp [coreTr, physBlockTrace, portBlockTrace, hW']

/-- **Block traces of a Bochner mean identity.** If
`diag(h) E[G] - E[diag(s(ω)) G] = I` with block-constant diagonals, then for every block
`β`: `h_β E[g_β] - E[s_β g_β] = 1`, `g_β = coreTr G β`. -/
theorem core_trace_identity {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} (hW : 0 < W)
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hGi : Integrable G ν)
    (h : Fin σ.blocks ⊕ Fin σ.ports → ℂ) (s : Ω → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (hsi : Integrable (fun ω => diagonal (fun x => s ω (coreBlk x)) * G ω) ν)
    (hid : diagonal (fun x => h (coreBlk x)) * ∫ ω, G ω ∂ν -
      ∫ ω, diagonal (fun x => s ω (coreBlk x)) * G ω ∂ν = 1)
    (β : Fin σ.blocks ⊕ Fin σ.ports) :
    h β * ∫ ω, coreTr (G ω) β ∂ν - ∫ ω, s ω β * coreTr (G ω) β ∂ν = 1 := by
  have h1 := congrArg (coreTrCLM β) hid
  rw [map_sub, coreTrCLM_apply, coreTrCLM_apply, core_tr_diag_mul, ← coreTrCLM_apply,
    ← (coreTrCLM β).integral_comp_comm hGi, ← coreTrCLM_apply,
    ← (coreTrCLM β).integral_comp_comm hsi, coreTrCLM_apply, core_tr_one hW] at h1
  simp only [coreTrCLM_apply, core_tr_diag_mul] at h1
  exact h1

/-- **Vector Dyson equation from a block-constant Schwinger–Dyson identity**
(the vector Dyson equation): if `diag(h) E[G] - E[diag(s(G)) G] = I` with
`s(G)_β = Σ_γ w_βγ g_γ(G)` (block traces `g = coreTr G`), `G` measurable with `‖G‖ ∈ L²`, then
`(h_β - Σ_γ w_βγ ḡ_γ) ḡ_β = 1 + Σ_γ w_βγ (E[g_γ g_β] - ḡ_γ ḡ_β)`. -/
theorem core_vector_dyson {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    (hW : 0 < W) {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGm : AEStronglyMeasurable G ν) (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) ν)
    (h : Fin σ.blocks ⊕ Fin σ.ports → ℂ) (w : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (hid : diagonal (fun x => h (coreBlk x)) * ∫ ω, G ω ∂ν -
      ∫ ω, diagonal (fun x => ∑ γ, w (coreBlk x) γ * coreTr (G ω) γ) * G ω ∂ν = 1)
    (β : Fin σ.blocks ⊕ Fin σ.ports) :
    (h β - ∑ γ, w β γ * ∫ ω, coreTr (G ω) γ ∂ν) * ∫ ω, coreTr (G ω) β ∂ν =
      1 + ∑ γ, w β γ * ((∫ ω, coreTr (G ω) γ * coreTr (G ω) β ∂ν) -
        (∫ ω, coreTr (G ω) γ ∂ν) * ∫ ω, coreTr (G ω) β ∂ν) := by
  have hG1 := meq_integrable_norm_of_sq hGm hG2
  have hGi : Integrable G ν := Integrable.mono' hG1 hGm (ae_of_all _ fun _ => le_rfl)
  have htrm : ∀ γ, AEStronglyMeasurable (fun ω => coreTr (G ω) γ) ν :=
    fun γ => (core_continuous_tr γ).comp_aestronglyMeasurable hGm
  have hpair : ∀ γ γ', Integrable (fun ω => coreTr (G ω) γ * coreTr (G ω) γ') ν := by
    intro γ γ'
    refine Integrable.mono' hG2 ((htrm γ).mul (htrm γ')) (ae_of_all _ fun ω => ?_)
    rw [norm_mul, sq]
    exact mul_le_mul (core_norm_tr_le _ _) (core_norm_tr_le _ _) (norm_nonneg _) (norm_nonneg _)
  have hsi : Integrable (fun ω => diagonal (fun x => ∑ γ, w (coreBlk x) γ * coreTr (G ω) γ) * G ω) ν := by
    have hmeas : AEStronglyMeasurable
        (fun ω => diagonal (fun x => ∑ γ, w (coreBlk x) γ * coreTr (G ω) γ) * G ω) ν := by
      have hc : Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
          diagonal (fun x => ∑ γ, w (coreBlk x) γ * coreTr M γ) * M) := by
        refine Continuous.mul ?_ continuous_id
        refine continuous_pi fun x => continuous_pi fun y => ?_
        simp only [diagonal_apply]
        split_ifs
        · exact continuous_finsetSum _ fun γ _ => continuous_const.mul (core_continuous_tr γ)
        · exact continuous_const
      exact hc.comp_aestronglyMeasurable hGm
    set Cw : ℝ := ∑ x : LayerSite W σ, ∑ γ, ‖w (coreBlk x) γ‖
    refine Integrable.mono' (hG2.const_mul Cw) hmeas (ae_of_all _ fun ω => ?_)
    refine (norm_mul_le _ _).trans ?_
    have hd : ‖(diagonal (fun x : LayerSite W σ => ∑ γ, w (coreBlk x) γ * coreTr (G ω) γ) :
        Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤ Cw * ‖G ω‖ := by
      rw [l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun x => ?_
      calc ‖∑ γ, w (coreBlk x) γ * coreTr (G ω) γ‖ ≤ ∑ γ, ‖w (coreBlk x) γ‖ * ‖G ω‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ _ => ?_)
            rw [norm_mul]; gcongr; exact core_norm_tr_le _ _
        _ = (∑ γ, ‖w (coreBlk x) γ‖) * ‖G ω‖ := by rw [Finset.sum_mul]
        _ ≤ Cw * ‖G ω‖ := by
            gcongr
            exact Finset.single_le_sum (f := fun x : LayerSite W σ => ∑ γ, ‖w (coreBlk x) γ‖)
              (fun _ _ => by positivity) (Finset.mem_univ x)
    calc ‖(diagonal (fun x : LayerSite W σ => ∑ γ, w (coreBlk x) γ * coreTr (G ω) γ) :
          Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ * ‖G ω‖
        ≤ Cw * ‖G ω‖ * ‖G ω‖ := by gcongr
      _ = Cw * ‖G ω‖ ^ 2 := by ring
  have hid' := core_trace_identity hW hGi h (fun ω β => ∑ γ, w β γ * coreTr (G ω) γ) hsi hid β
  have hexp : ∫ ω, (∑ γ, w β γ * coreTr (G ω) γ) * coreTr (G ω) β ∂ν =
      ∑ γ, w β γ * ∫ ω, coreTr (G ω) γ * coreTr (G ω) β ∂ν := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ fun γ _ => ?_]
    · refine Finset.sum_congr rfl fun γ _ => ?_
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    · simp_rw [mul_assoc]; exact (hpair γ β).const_mul _
  rw [hexp] at hid'
  rw [← hid']
  simp only [mul_sub, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  ring_nf

end BlockTraces

/-!
## 2. Covariances and the final `L^p` assembly
-/

section Lp

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

/-- **Covariance from fluctuations** (Cauchy–Schwarz): for `f, g ∈ L²`,
`|E[fg] - E f E g| ≤ ‖f - Ef‖₂ ‖g - Eg‖₂`. -/
theorem core_cov_le {f g : Ω → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {A B : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : eLpNorm (fun ω => f ω - ∫ ω', f ω' ∂ν) 2 ν ≤ ENNReal.ofReal A)
    (hB : eLpNorm (fun ω => g ω - ∫ ω', g ω' ∂ν) 2 ν ≤ ENNReal.ofReal B) :
    ‖(∫ ω, f ω * g ω ∂ν) - (∫ ω, f ω ∂ν) * ∫ ω, g ω ∂ν‖ ≤ A * B := by
  set cf := ∫ ω, f ω ∂ν
  set cg := ∫ ω, g ω ∂ν
  have hf' : MemLp (fun ω => f ω - cf) 2 ν := hf.sub (memLp_const cf)
  have hg' : MemLp (fun ω => g ω - cg) 2 ν := hg.sub (memLp_const cg)
  have hfi : Integrable f ν := hf.integrable one_le_two
  have hgi : Integrable g ν := hg.integrable one_le_two
  have hfg : Integrable (fun ω => f ω * g ω) ν := hf.integrable_mul hg
  have hprod : Integrable (fun ω => (f ω - cf) * (g ω - cg)) ν := hf'.integrable_mul hg'
  have hexp : (∫ ω, f ω * g ω ∂ν) - cf * cg = ∫ ω, (f ω - cf) * (g ω - cg) ∂ν := by
    have e : (fun ω => (f ω - cf) * (g ω - cg)) =
        fun ω => (f ω * g ω - (cg * f ω + cf * g ω)) + cf * cg := by
      funext ω; ring
    have i1 := integral_add (μ := ν) (f := fun ω => f ω * g ω - (cg * f ω + cf * g ω))
      (g := fun _ => cf * cg) (hfg.sub ((hfi.const_mul cg).add (hgi.const_mul cf)))
      (integrable_const _)
    have i2 := integral_sub (μ := ν) (f := fun ω => f ω * g ω)
      (g := fun ω => cg * f ω + cf * g ω) hfg ((hfi.const_mul cg).add (hgi.const_mul cf))
    have i3 := integral_add (μ := ν) (f := fun ω => cg * f ω) (g := fun ω => cf * g ω)
      (hfi.const_mul cg) (hgi.const_mul cf)
    rw [e, i1, i2, i3, integral_const_mul, integral_const_mul, integral_const, probReal_univ,
      one_smul]
    ring
  rw [hexp]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [norm_mul]
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := fun ω => f ω - cf)
    (g := fun ω => g ω - cg) Real.HolderConjugate.two_two
    (by simpa using hf') (by simpa using hg')
  refine hH.trans ?_
  have hnA : (∫ ω, ‖f ω - cf‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤ A := by
    have e := hf'.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat] at e
    rw [e] at hA
    rw [one_div]; exact (ENNReal.ofReal_le_ofReal_iff hA0).mp hA
  have hnB : (∫ ω, ‖g ω - cg‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤ B := by
    have e := hg'.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat] at e
    rw [e] at hB
    rw [one_div]; exact (ENNReal.ofReal_le_ofReal_iff hB0).mp hB
  exact mul_le_mul hnA hnB (by positivity) hA0

/-- **Final assembly** (Minkowski): `‖max_j |g_j - a|‖_p ≤ 2A + B` from
`‖g_j - c_j‖_p ≤ A` and `|c_j - a| ≤ B` (`1 ≤ p`, probability law). -/
theorem core_final {p : ℝ} (hp : 1 ≤ p) {g0 g1 : Ω → ℂ} (hg0 : AEStronglyMeasurable g0 ν)
    (hg1 : AEStronglyMeasurable g1 ν) (c0 c1 a : ℂ) {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (h0 : eLpNorm (fun ω => g0 ω - c0) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A)
    (h1 : eLpNorm (fun ω => g1 ω - c1) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A)
    (hc0 : ‖c0 - a‖ ≤ B) (hc1 : ‖c1 - a‖ ≤ B) :
    eLpNorm (fun ω => max ‖g0 ω - a‖ ‖g1 ω - a‖) (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (2 * A + B) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hm0 : AEStronglyMeasurable (fun ω => ‖g0 ω - c0‖) ν := (hg0.sub aestronglyMeasurable_const).norm
  have hm1 : AEStronglyMeasurable (fun ω => ‖g1 ω - c1‖) ν := (hg1.sub aestronglyMeasurable_const).norm
  have hpt : ∀ ω, ‖max ‖g0 ω - a‖ ‖g1 ω - a‖‖ ≤ ‖‖g0 ω - c0‖ + ‖g1 ω - c1‖ + B‖ := by
    intro ω
    have e0 : ‖g0 ω - a‖ ≤ ‖g0 ω - c0‖ + B := by
      calc ‖g0 ω - a‖ = ‖(g0 ω - c0) + (c0 - a)‖ := by ring_nf
        _ ≤ ‖g0 ω - c0‖ + ‖c0 - a‖ := norm_add_le _ _
        _ ≤ ‖g0 ω - c0‖ + B := by gcongr
    have e1 : ‖g1 ω - a‖ ≤ ‖g1 ω - c1‖ + B := by
      calc ‖g1 ω - a‖ = ‖(g1 ω - c1) + (c1 - a)‖ := by ring_nf
        _ ≤ ‖g1 ω - c1‖ + ‖c1 - a‖ := norm_add_le _ _
        _ ≤ ‖g1 ω - c1‖ + B := by gcongr
    rw [Real.norm_of_nonneg (le_max_of_le_left (norm_nonneg _)),
      Real.norm_of_nonneg (by positivity)]
    exact max_le (by linarith [norm_nonneg (g1 ω - c1)]) (by linarith [norm_nonneg (g0 ω - c0)])
  refine (eLpNorm_mono ((hg0.sub aestronglyMeasurable_const).norm.sup
    (hg1.sub aestronglyMeasurable_const).norm) hpt).trans ?_
  refine (eLpNorm_add_le (f := fun ω => ‖g0 ω - c0‖ + ‖g1 ω - c1‖) (g := fun _ => B)
    hp').trans ?_
  refine (add_le_add (eLpNorm_add_le (f := fun ω => ‖g0 ω - c0‖) (g := fun ω => ‖g1 ω - c1‖)
    hp') le_rfl).trans ?_
  have hc : eLpNorm (fun _ : Ω => B) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B := by
    rw [eLpNorm_const _ (by positivity) (NeZero.ne ν), measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal hB0]
  have e0 : eLpNorm (fun ω => ‖g0 ω - c0‖) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A := by
    exact (eLpNorm_norm (fun ω => g0 ω - c0) (hg0.sub aestronglyMeasurable_const)).le.trans h0
  have e1 : eLpNorm (fun ω => ‖g1 ω - c1‖) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A := by
    exact (eLpNorm_norm (fun ω => g1 ω - c1) (hg1.sub aestronglyMeasurable_const)).le.trans h1
  calc eLpNorm (fun ω => ‖g0 ω - c0‖) (ENNReal.ofReal p) ν +
        eLpNorm (fun ω => ‖g1 ω - c1‖) (ENNReal.ofReal p) ν +
        eLpNorm (fun _ : Ω => B) (ENNReal.ofReal p) ν
      ≤ ENNReal.ofReal A + ENNReal.ofReal A + ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal (2 * A + B) := by
        rw [← ENNReal.ofReal_add hA0 hA0, ← ENNReal.ofReal_add (by positivity) hB0]
        ring_nf

omit [IsProbabilityMeasure ν] in
/-- **`L^q` bound on a product from uniform fibre bounds** (Tonelli): if every fibre has
`‖f(x, ·)‖_{L^q(ν)} ≤ C`, then `‖f‖_{L^q(μ ⊗ ν)} ≤ C` for a probability `μ`. -/
theorem core_eLpNorm_prod_le {β : Type*} [MeasurableSpace β] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ν' : Measure β) [SFinite ν'] {f : Ω × β → ℝ} (hf : Measurable f)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ∞) {C : ℝ≥0∞}
    (h : ∀ x, eLpNorm (fun y => f (x, y)) q ν' ≤ C) : eLpNorm f q (μ.prod ν') ≤ C := by
  have hr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [eLpNorm_eq_eLpNorm' hq0 hqt hf.aestronglyMeasurable, eLpNorm']
  have hfib : ∀ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ q.toReal ∂ν' ≤ C ^ q.toReal := by
    intro x
    have hx := h x
    rw [eLpNorm_eq_eLpNorm' hq0 hqt (f := fun y => f (x, y))
      (hf.comp measurable_prodMk_left).aestronglyMeasurable, eLpNorm'] at hx
    have h2 := ENNReal.rpow_le_rpow hx hr.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one] at h2
  have hint : ∫⁻ z, ‖f z‖ₑ ^ q.toReal ∂μ.prod ν' ≤ C ^ q.toReal := by
    rw [lintegral_prod _ (hf.enorm.pow_const _).aemeasurable]
    calc ∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ q.toReal ∂ν' ∂μ ≤ ∫⁻ _x, C ^ q.toReal ∂μ := lintegral_mono hfib
      _ = C ^ q.toReal := by rw [lintegral_const, measure_univ, mul_one]
  have h3 := ENNReal.rpow_le_rpow hint (by positivity : 0 ≤ 1 / q.toReal)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one] at h3

omit [IsProbabilityMeasure ν] in
/-- Almost-sure statements on a product from every fibre. -/
theorem core_ae_prod {β : Type*} [MeasurableSpace β] (μ : Measure Ω) [SFinite μ]
    (ν' : Measure β) [SFinite ν'] {P : Ω × β → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ x, ∀ᵐ y ∂ν', P (x, y)) : ∀ᵐ z ∂μ.prod ν', P z :=
  (Measure.ae_prod_iff_ae_ae hP).2 (ae_of_all _ h)

/-- **Trace covariances from trace fluctuations**: if every block trace of `G` (with
`‖G‖ ∈ L²`) satisfies `‖g_β - ḡ_β‖₂ ≤ A`, then `|E[g_γ g_β] - ḡ_γ ḡ_β| ≤ A²`. -/
theorem core_cov_tr {W : ℕ} {σ : LayerShape} {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGm : AEStronglyMeasurable G ν) (hG2 : Integrable (fun ω => ‖G ω‖ ^ 2) ν) {A : ℝ}
    (hA0 : 0 ≤ A)
    (hfl : ∀ β : Fin σ.blocks ⊕ Fin σ.ports,
      eLpNorm (fun ω => coreTr (G ω) β - ∫ ω', coreTr (G ω') β ∂ν) 2 ν ≤ ENNReal.ofReal A)
    (γ β : Fin σ.blocks ⊕ Fin σ.ports) :
    ‖(∫ ω, coreTr (G ω) γ * coreTr (G ω) β ∂ν) -
      (∫ ω, coreTr (G ω) γ ∂ν) * ∫ ω, coreTr (G ω) β ∂ν‖ ≤ A * A := by
  have hGn : MemLp (fun ω => ‖G ω‖) 2 ν :=
    (memLp_two_iff_integrable_sq hGm.norm).mpr hG2
  have hmem : ∀ δ, MemLp (fun ω => coreTr (G ω) δ) 2 ν := fun δ =>
    hGn.of_le ((core_continuous_tr δ).comp_aestronglyMeasurable hGm)
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact core_norm_tr_le _ _)
  exact core_cov_le (hmem γ) (hmem β) hA0 hA0 (hfl γ) (hfl β)

/-- The weighted residual of the vector Dyson equation. -/
theorem core_resid_le {κ : Type*} [Fintype κ] (w : κ → ℂ) (c : κ → ℂ) {A : ℝ}
    (hw : ∑ γ, ‖w γ‖ ≤ 1) (hc : ∀ γ, ‖c γ‖ ≤ A) (hA : 0 ≤ A) :
    ‖∑ γ, w γ * c γ‖ ≤ A := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ γ, ‖w γ * c γ‖ ≤ ∑ γ, ‖w γ‖ * A := Finset.sum_le_sum fun γ _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hc γ) (norm_nonneg _)
    _ = (∑ γ, ‖w γ‖) * A := by rw [Finset.sum_mul]
    _ ≤ 1 * A := by gcongr
    _ = A := one_mul A

omit [IsProbabilityMeasure ν] in
/-- `|E g_β| ≤ ‖‖G‖‖_{L¹}`. -/
theorem core_norm_mean_le {W : ℕ} {σ : LayerShape}
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hGm : AEStronglyMeasurable G ν) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : eLpNorm (fun ω => ‖G ω‖) 1 ν ≤ ENNReal.ofReal K)
    (β : Fin σ.blocks ⊕ Fin σ.ports) : ‖∫ ω, coreTr (G ω) β ∂ν‖ ≤ K := by
  have hmem : MemLp (fun ω => ‖G ω‖) 1 ν :=
    memLp_iff.mpr (lt_of_le_of_lt hK ENNReal.ofReal_lt_top)
  have hint : Integrable (fun ω => ‖G ω‖) ν := memLp_one_iff_integrable.mp hmem
  have hI : ∫ ω, ‖G ω‖ ∂ν ≤ K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => norm_nonneg _)
      hmem.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal hK0 ?_
    rw [eLpNorm_one_eq_lintegral_enorm hGm.norm] at hK
    refine le_trans (le_of_eq ?_) hK
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (norm_nonneg _)]
  calc ‖∫ ω, coreTr (G ω) β ∂ν‖ ≤ ∫ ω, ‖coreTr (G ω) β‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖G ω‖ ∂ν := integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint
          (ae_of_all _ fun ω => core_norm_tr_le _ _)
    _ ≤ K := hI

end Lp

end BlockBand.Layers
