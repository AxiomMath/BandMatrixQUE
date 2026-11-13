module

public import BlockBand.Native.ErdosRiabov.VS.Band

set_option autoImplicit false

/-!
# Itô's formula along the VS band process; slicing of second derivatives

Setting: `RingSample p` with law `driverLaw μ` (any probability law `μ` of the unused initial
state) and the filtration `driverAugmented μ`; `Y_t - Y_0 = vsNoise p t = ringCoords H_t`.

* **`vsBand_ito`** (Itô's formula `semimartingaleItoFormula_holds`, with zero drift): for
  every Borel `φ : ℝ × ℝ^d → ℝ` that is `C²` on `ℝ × U`, `U` open and containing `Y_t - Y_0`
  for all `t` a.s., `φ(t, Y_t - Y_0)` is a continuous semimartingale with drift
  `∂_t φ + ½ ∑_i v_i ∂_i² φ` and bracket density `∑_i v_i (∂_i φ)²` (no `-½X` term).
  `vsNoise_itoFormula` is the same with `itoDrift`/`itoBracket`;
  `itoDrift_zero_diagonal`, `itoBracket_diagonal` are the (sure, algebraic) identifications.
* **Slicing** (`fderiv_slice`, `fderiv_fderiv_slice`, `partialSpace_eq_slice`,
  `partialSpace2_eq_slice`): if `φ` is `C²` at `(t, y)` (jointly), then
  `D²φ(t, y)[(0, u), (0, w)] = D²(φ(t, ·))(y)[u, w]` and `Dφ(t, y)[(0, u)] = D(φ(t, ·))(y)[u]`;
  so the spatial partials in Itô's formula are the fixed-time derivatives of `Chains`.
  `partialTime_eq_deriv`: `∂_t φ(t, y) = d/ds φ(s, y)|_{s=t}` when `φ` is differentiable at
  `(t, y)`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal Matrix

/-!
### Zero drift and diagonal covariance
-/

section Algebra

variable {d : ℕ}

/-- The Itô drift for zero drift and diagonal covariance `diag v`:
`∂_t φ + ½ ∑_i v_i ∂_i² φ`. -/
theorem itoDrift_zero_diagonal (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0)
    (v : Fin d → ℝ) :
    itoDrift φ y t 0 (Matrix.diagonal v) =
      partialTime φ ((t : ℝ), y) + 1 / 2 * ∑ i, v i * partialSpace2 φ ((t : ℝ), y) i i := by
  simp only [itoDrift, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero,
    Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The Itô bracket density for diagonal covariance `diag v`: `∑_i v_i (∂_i φ)²`. -/
theorem itoBracket_diagonal (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0)
    (v : Fin d → ℝ) :
    itoBracket φ y t (Matrix.diagonal v) = ∑ i, v i * partialSpace φ ((t : ℝ), y) i ^ 2 := by
  simp only [itoBracket, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => by ring

end Algebra

/-!
### Itô's formula along `Y_t - Y_0`
-/

section Ito

variable {p : BlockBand.Parameters}

/-- Itô's formula along the VS coordinates, with `itoDrift` and `itoBracket`
at zero drift and covariance `diag v`. -/
theorem vsNoise_itoFormula (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {U : Set (Fin (ringDim p) → ℝ)} (hU : IsOpen U)
    (hYU : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t, vsNoise p t x ∈ U)
    {φ : ℝ × (Fin (ringDim p) → ℝ) → ℝ} (hφm : Measurable φ)
    (hφ : ContDiffOn ℝ 2 φ (Set.univ ×ˢ U)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) => φ ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => itoDrift φ (vsNoise p t x) t 0
        (Matrix.diagonal (ringVariance p)))
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        itoBracket φ (vsNoise p t x) t (Matrix.diagonal (ringVariance p))) :=
  SemimartingaleIto.semimartingaleItoFormula_holds (ringDim p) (RingSample p) _ _ _ _ _
    (isContinuousSemimartingale_vsNoise μ) U hU hYU φ hφm hφ

/-- **Itô's formula along the VS band process (zero drift).** For every probability law
`μ` of the initial state, every open `U` containing `Y_t - Y_0 = ringCoords H_t` for all `t` a.s.,
and every Borel `φ : ℝ × ℝ^d → ℝ` that is `C²` on `ℝ × U`, the process `φ(t, Y_t - Y_0)` is a
continuous semimartingale for `(driverLaw μ, driverAugmented μ)` with drift
`∂_t φ + ½ ∑_i v_i ∂_i² φ` and bracket density `∑_i v_i (∂_i φ)²` at `(t, Y_t - Y_0)`,
`v = ringVariance p`. -/
theorem vsBand_ito (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {U : Set (Fin (ringDim p) → ℝ)} (hU : IsOpen U)
    (hYU : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t, vsNoise p t x ∈ U)
    {φ : ℝ × (Fin (ringDim p) → ℝ) → ℝ} (hφm : Measurable φ)
    (hφ : ContDiffOn ℝ 2 φ (Set.univ ×ˢ U)) :
    IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ)
      (fun t x (_ : Fin 1) => φ ((t : ℝ), vsNoise p t x))
      (fun t x (_ : Fin 1) => partialTime φ ((t : ℝ), vsNoise p t x) +
        1 / 2 * ∑ i, ringVariance p i * partialSpace2 φ ((t : ℝ), vsNoise p t x) i i)
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        ∑ i, ringVariance p i * partialSpace φ ((t : ℝ), vsNoise p t x) i ^ 2) := by
  refine isContinuousSemimartingale_congr_data (vsNoise_itoFormula μ hU hYU hφm hφ) rfl ?_ ?_
  · funext t x _
    exact itoDrift_zero_diagonal φ _ t _
  · funext t x
    simp only [itoBracket_diagonal]

end Ito

/-!
### Slicing: spatial derivatives at fixed time
-/

section Slice

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- First spatial derivative = derivative of the time slice. -/
theorem fderiv_slice {φ : ℝ × E → F} {t : ℝ} {y : E} (h : DifferentiableAt ℝ φ (t, y))
    (u : E) : fderiv ℝ (fun y' => φ (t, y')) y u = fderiv ℝ φ (t, y) ((0 : ℝ), u) := by
  have hc := h.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)
  change fderiv ℝ (φ ∘ fun y' => (t, y')) y u = _
  rw [hc.fderiv]
  rfl

/-- **Slicing of second derivatives.** If `φ` is `C²` at `(t, y)` jointly, then
`D²φ(t, y)[(0, u), (0, w)] = D²(φ(t, ·))(y)[u, w]`. -/
theorem fderiv_fderiv_slice {φ : ℝ × E → F} {t : ℝ} {y : E} (h : ContDiffAt ℝ 2 φ (t, y))
    (u w : E) :
    fderiv ℝ (fderiv ℝ (fun y' => φ (t, y'))) y u w =
      fderiv ℝ (fderiv ℝ φ) (t, y) ((0 : ℝ), u) ((0 : ℝ), w) := by
  set R : ((ℝ × E) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) F).flip (ContinuousLinearMap.inr ℝ ℝ E) with hR
  have hev : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 φ (t, y') :=
    ((continuous_const.prodMk continuous_id).tendsto y).eventually (h.eventually (by simp))
  have heq : (fderiv ℝ fun y' => φ (t, y')) =ᶠ[𝓝 y] fun y' => R (fderiv ℝ φ (t, y')) := by
    filter_upwards [hev] with y' hy'
    refine ContinuousLinearMap.ext fun u' => ?_
    rw [fderiv_slice (hy'.differentiableAt (by norm_num)) u']
    rfl
  have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (t, y)) (t, y) :=
    ((h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := (R.hasFDerivAt.comp (t, y) hD).comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) t y)
  rw [heq.fderiv_eq]
  change fderiv ℝ ((R ∘ fderiv ℝ φ) ∘ fun y' => (t, y')) y u w = _
  rw [hc.fderiv]
  rfl

/-- `∂_t φ(t, y) = d/ds φ(s, y)|_{s=t}` when `φ` is differentiable at `(t, y)`. -/
theorem fderiv_time_eq_deriv {φ : ℝ × E → F} {t : ℝ} {y : E} (h : DifferentiableAt ℝ φ (t, y)) :
    fderiv ℝ φ (t, y) ((1 : ℝ), (0 : E)) = deriv (fun s => φ (s, y)) t := by
  have hc := h.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact (hc.deriv).symm

end Slice

section SliceFin

variable {d : ℕ}

theorem partialSpace_eq_slice {φ : ℝ × (Fin d → ℝ) → ℝ} {t : ℝ} {y : Fin d → ℝ}
    (h : DifferentiableAt ℝ φ (t, y)) (i : Fin d) :
    partialSpace φ (t, y) i = fderiv ℝ (fun y' => φ (t, y')) y (Pi.single i 1) :=
  (fderiv_slice h _).symm

/-- The spatial second partials of Itô's formula are fixed-time second derivatives. -/
theorem partialSpace2_eq_slice {φ : ℝ × (Fin d → ℝ) → ℝ} {t : ℝ} {y : Fin d → ℝ}
    (h : ContDiffAt ℝ 2 φ (t, y)) (i j : Fin d) :
    partialSpace2 φ (t, y) i j =
      fderiv ℝ (fderiv ℝ (fun y' => φ (t, y'))) y (Pi.single i 1) (Pi.single j 1) :=
  (fderiv_fderiv_slice h _ _).symm

theorem partialTime_eq_deriv {φ : ℝ × (Fin d → ℝ) → ℝ} {t : ℝ} {y : Fin d → ℝ}
    (h : DifferentiableAt ℝ φ (t, y)) :
    partialTime φ (t, y) = deriv (fun s => φ (s, y)) t :=
  fderiv_time_eq_deriv h

end SliceFin

end BlockBand.Native.ErdosRiabov.VS
