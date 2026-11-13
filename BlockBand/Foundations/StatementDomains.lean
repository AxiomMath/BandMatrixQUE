module

public import BlockBand.Statements
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Inhabitants of the smooth endpoint test domains

The endpoint theorem quantifies nonnegative unit-integral real weights in `C_c^∞` and smooth
nonconstant real tests on `ℝ/ℤ`. These constructors inhabit the `ContDiff ℝ ∞` domains. They do
not prove any matrix-model existence, variance, limiting law or endpoint assertion.

The spectral normalization is under real Lebesgue measure `volume`.
A smooth compactly supported bump from Mathlib is normalized by its own
positive Lebesgue integral; no identification of an auxiliary Haar measure
with volume is assumed. The profile is the explicit one-periodic cosine,
transported through the rescaling homeomorphism R/Z → R/(2πZ).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Foundations

open MeasureTheory
open scoped ContDiff

/-- A nonnegative smooth compactly supported real function of Lebesgue mass one.
No probability-law or asymptotic hypothesis enters this existence result. -/
theorem exists_smooth_nonnegative_integral_one :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧ (∫ x, f x) = 1 := by
  let u : ℝ → ℝ := ExistsContDiffBumpBase.u
  have hs : ContDiff ℝ ∞ u := ExistsContDiffBumpBase.u_smooth ℝ
  have hc : HasCompactSupport u := ExistsContDiffBumpBase.u_compact_support ℝ
  have hn : ∀ x, 0 ≤ u x := ExistsContDiffBumpBase.u_nonneg
  have hi : Integrable u := hs.continuous.integrable_of_hasCompactSupport hc
  have hp : 0 < ∫ x, u x := by
    apply (integral_pos_iff_support_of_nonneg hn hi).mpr
    change 0 < volume (Function.support (ExistsContDiffBumpBase.u : ℝ → ℝ))
    rw [ExistsContDiffBumpBase.u_support ℝ]
    norm_num [Real.ball_eq_Ioo]
  refine ⟨fun x => (∫ y, u y)⁻¹ * u x,
    contDiff_const.mul hs, hc.mul_left, ?_, ?_⟩
  · intro x
    exact mul_nonneg (inv_nonneg.mpr hp.le) (hn x)
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hp.ne'

/-- The spectral-weight quantifier is inhabited, by a smooth bump. -/
theorem spectralWeight_nonempty : Nonempty SpectralWeight := by
  obtain ⟨f, hs, hc, hn, hi⟩ := exists_smooth_nonnegative_integral_one
  exact ⟨{
    toContinuousMap := ⟨f, hs.continuous⟩
    smooth := hs
    compactSupport := hc
    nonnegative := hn
    integral_eq_one := hi }⟩

/-- Rescale the unit torus to the angle quotient with period 2π. -/
def torusToAngle : Torus ≃ₜ Real.Angle :=
  AddCircle.homeomorphAddCircle (1 : ℝ) (2 * Real.pi)
    one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)

/-- The explicit continuous profile test whose lift is cos(2πx). -/
def cosineProfile : ContinuousMap Torus ℝ :=
  ⟨fun r => Real.Angle.cos (torusToAngle r),
    Real.Angle.continuous_cos.comp torusToAngle.continuous⟩

/-- The profile has exactly the one-periodic cosine lift. -/
theorem cosineProfile_mk (x : ℝ) :
    cosineProfile (QuotientAddGroup.mk x) = Real.cos (2 * Real.pi * x) := by
  change Real.Angle.cos
    (AddCircle.homeomorphAddCircle (1 : ℝ) (2 * Real.pi)
      one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (x : AddCircle (1 : ℝ))) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  change Real.cos (x * ((1 : ℝ)⁻¹ * (2 * Real.pi))) = _
  simp only [inv_one, one_mul]
  congr 1
  ring

/-- Values at the unit-torus points 0 and 1/2 distinguish the profile. -/
theorem cosineProfile_nonconstant :
    ∃ x y : Torus, cosineProfile x ≠ cosineProfile y := by
  refine ⟨QuotientAddGroup.mk (0 : ℝ), QuotientAddGroup.mk (1 / 2 : ℝ), ?_⟩
  rw [cosineProfile_mk, cosineProfile_mk]
  rw [mul_zero, Real.cos_zero, show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring,
    Real.cos_pi]
  norm_num

/-- The corrected smooth nonconstant profile-test quantifier is inhabited. -/
theorem profileTest_nonempty : Nonempty ProfileTest := by
  refine ⟨{
    toContinuousMap := cosineProfile
    smooth_lift := ?_
    nonconstant := cosineProfile_nonconstant }⟩
  have h : (fun x : ℝ => cosineProfile (QuotientAddGroup.mk x)) =
      (fun x : ℝ => Real.cos (2 * Real.pi * x)) := by
    funext x
    exact cosineProfile_mk x
  rw [h]
  exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

end BlockBand.Foundations
