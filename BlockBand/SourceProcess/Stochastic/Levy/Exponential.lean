module
public import BlockBand.Internal.Contracts.Transmission
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The exponential test functions of Lévy's characterization

For `u ∈ ℝ^d`, `θ ∈ ℝ` and `c = |u|²/2` the space-time function
`levyPhi u θ (t, x) = e^{c t} cos(⟨u, x⟩ - θ)` (`θ = 0`: real part, `θ = π/2`: imaginary part
of `e^{c t} e^{i⟨u,x⟩}`) is smooth, and its Itô drift for the characteristics `(β, α) = (0, I)`
vanishes identically (`itoDrift_levyPhi`): `∂_t φ + ½ Δφ = c φ - ½ |u|² φ = 0`.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ}

/-- `|u|² = ∑ u_i²`. -/
def sqNorm (u : Fin d → ℝ) : ℝ := ∑ i, u i ^ 2

/-- The linear form `(t, x) ↦ ⟨u, x⟩` on space-time. -/
def spaceForm (u : Fin d → ℝ) : (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ :=
  ∑ i, u i • ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ)))

theorem spaceForm_apply (u : Fin d → ℝ) (p : ℝ × (Fin d → ℝ)) :
    spaceForm u p = ∑ i, u i * p.2 i := by
  simp [spaceForm]

/-- The time form `(t, x) ↦ t`. -/
abbrev timeForm (d : ℕ) : (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ _

/-- `levyPhi u θ (t, x) = exp(|u|² t / 2) cos(⟨u, x⟩ - θ)`. -/
def levyPhi (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  Real.exp (sqNorm u / 2 * p.1) * Real.cos (∑ i, u i * p.2 i - θ)

theorem levyPhi_eq (u : Fin d → ℝ) (θ : ℝ) :
    levyPhi u θ = fun p => Real.exp (sqNorm u / 2 * timeForm d p) *
      Real.cos (spaceForm u p - θ) := by
  funext p; simp [levyPhi, spaceForm_apply]

theorem contDiff_levyPhi (u : Fin d → ℝ) (θ : ℝ) : ContDiff ℝ 2 (levyPhi u θ) := by
  rw [levyPhi_eq]
  exact (Real.contDiff_exp.comp (contDiff_const.mul (timeForm d).contDiff)).mul
    (Real.contDiff_cos.comp ((spaceForm u).contDiff.sub contDiff_const))

theorem continuous_levyPhi (u : Fin d → ℝ) (θ : ℝ) : Continuous (levyPhi u θ) :=
  (contDiff_levyPhi u θ).continuous

/-- First-derivative coefficient along the time form. -/
def g₁ (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  sqNorm u / 2 * (Real.exp (sqNorm u / 2 * timeForm d p) * Real.cos (spaceForm u p - θ))

/-- First-derivative coefficient along the space form. -/
def g₂ (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  -(Real.exp (sqNorm u / 2 * timeForm d p) * Real.sin (spaceForm u p - θ))

theorem hasFDerivAt_levyPhi (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) :
    HasFDerivAt (levyPhi u θ) (g₁ u θ p • timeForm d + g₂ u θ p • spaceForm u) p := by
  rw [levyPhi_eq]
  have h := ((((timeForm d).hasFDerivAt (x := p)).const_mul (sqNorm u / 2)).exp).mul
    ((((spaceForm u).hasFDerivAt (x := p)).sub_const θ).cos)
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [g₁, g₂, add_apply, smul_apply, smul_eq_mul]
  ring

theorem fderiv_levyPhi (u : Fin d → ℝ) (θ : ℝ) :
    fderiv ℝ (levyPhi u θ) = fun p => g₁ u θ p • timeForm d + g₂ u θ p • spaceForm u :=
  funext fun p => (hasFDerivAt_levyPhi u θ p).fderiv

theorem hasFDerivAt_g₂ (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) :
    HasFDerivAt (g₂ u θ) (-(Real.exp (sqNorm u / 2 * timeForm d p) •
      (Real.cos (spaceForm u p - θ) • spaceForm u) +
      Real.sin (spaceForm u p - θ) • (Real.exp (sqNorm u / 2 * timeForm d p) •
        ((sqNorm u / 2) • timeForm d)))) p := by
  have h := (((((timeForm d).hasFDerivAt (x := p)).const_mul (sqNorm u / 2)).exp).mul
    ((((spaceForm u).hasFDerivAt (x := p)).sub_const θ).sin)).neg
  exact h

theorem differentiable_g₁ (u : Fin d → ℝ) (θ : ℝ) : Differentiable ℝ (g₁ u θ) := by
  intro p
  unfold g₁
  fun_prop

theorem hasFDerivAt_fderiv_levyPhi (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) :
    HasFDerivAt (fderiv ℝ (levyPhi u θ))
      ((fderiv ℝ (g₁ u θ) p).smulRight (timeForm d) +
        (fderiv ℝ (g₂ u θ) p).smulRight (spaceForm u)) p := by
  rw [fderiv_levyPhi]
  exact ((differentiable_g₁ u θ p).hasFDerivAt.smul_const _).add
    ((hasFDerivAt_g₂ u θ p).differentiableAt.hasFDerivAt.smul_const (spaceForm u))

theorem spaceForm_single (u : Fin d → ℝ) (i : Fin d) :
    spaceForm u ((0 : ℝ), (Pi.single i 1 : Fin d → ℝ)) = u i := by
  rw [spaceForm_apply]
  simp [Pi.single_apply]

theorem partialTime_levyPhi (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) :
    partialTime (levyPhi u θ) p = sqNorm u / 2 * levyPhi u θ p := by
  rw [partialTime, (hasFDerivAt_levyPhi u θ p).fderiv]
  simp [g₁, g₂, spaceForm_apply, levyPhi, timeForm]

theorem partialSpace2_levyPhi (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) (i j : Fin d) :
    partialSpace2 (levyPhi u θ) p i j = -(u i * u j * levyPhi u θ p) := by
  rw [partialSpace2, (hasFDerivAt_fderiv_levyPhi u θ p).fderiv, (hasFDerivAt_g₂ u θ p).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    neg_apply, smul_apply, smul_eq_mul,
    spaceForm_single]
  simp [timeForm, levyPhi, spaceForm_apply]
  ring

/-- **The Itô drift of `levyPhi` for the characteristics `(0, I)` vanishes.** -/
theorem itoDrift_levyPhi (u : Fin d → ℝ) (θ : ℝ) (y : Fin d → ℝ) (t : ℝ≥0) :
    itoDrift (levyPhi u θ) y t 0 1 = 0 := by
  simp only [itoDrift, partialTime_levyPhi, partialSpace2_levyPhi, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [sqNorm, Finset.sum_neg_distrib, ← Finset.sum_mul, sq]
  ring

theorem levyPhi_abs_le (u : Fin d → ℝ) (θ : ℝ) (p : ℝ × (Fin d → ℝ)) :
    |levyPhi u θ p| ≤ Real.exp (sqNorm u / 2 * p.1) := by
  rw [levyPhi, abs_mul, Real.abs_exp]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

end BlockBand.SourceProcess.Stochastic.Levy
