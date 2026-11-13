module

public import BlockBand.Coarea.Native.BlockBand.Analysis.CauchyPoisson
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Radial layer cake for the Poisson kernel

This module supplies the scalar calculus used to pass from closed-interval
counting estimates to a sharp Poisson-kernel estimate.  The radial weight is
the negative derivative of `η / (r² + η²)`.  Its tail reproduces the Poisson
kernel, and its first radial moment is exactly `π`; this is the source of the
sharp constant in the one-block projected-Wegner bound.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Filter MeasureTheory Set
open scoped Topology

/-- Positive radial density whose tail is the Cauchy Poisson kernel. -/
def poissonRadialWeight (η r : ℝ) : ℝ :=
  2 * η * r / (r ^ 2 + η ^ 2) ^ 2

/-- A primitive of `poissonRadialWeight η`. -/
def poissonRadialPrimitive (η r : ℝ) : ℝ :=
  -(η / (r ^ 2 + η ^ 2))

/-- Derivative of the Poisson radial primitive. -/
theorem hasDerivAt_poissonRadialPrimitive
    {η : ℝ} (_hη : 0 < η) (r : ℝ) :
    HasDerivAt (poissonRadialPrimitive η) (poissonRadialWeight η r) r := by
  have hden : r ^ 2 + η ^ 2 ≠ 0 := by positivity
  unfold poissonRadialPrimitive poissonRadialWeight
  have hquot := (hasDerivAt_const r η).div
    (((hasDerivAt_id r).pow 2).add_const (η ^ 2)) hden
  convert hquot.neg using 1
  · funext x
    simp only [id_eq, Pi.div_apply, Pi.pow_apply, Pi.neg_apply]
  · simp only [id_eq, Nat.cast_ofNat, zero_mul]
    field_simp [hden]
    simp only [Pi.pow_apply, id_eq]
    ring

/-- The primitive vanishes at positive infinity. -/
theorem tendsto_poissonRadialPrimitive_atTop
    {η : ℝ} (_hη : 0 < η) :
    Tendsto (poissonRadialPrimitive η) atTop (𝓝 0) := by
  unfold poissonRadialPrimitive
  have hsquare : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hden : Tendsto (fun r : ℝ => r ^ 2 + η ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop _ hsquare
  simpa using (hden.const_div_atTop η).neg

/-- Exact tail formula for the radial density. -/
theorem integral_poissonRadialWeight_Ioi
    {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) :
    (∫ r : ℝ in Ioi a, poissonRadialWeight η r) =
      η / (a ^ 2 + η ^ 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r _ => hasDerivAt_poissonRadialPrimitive hη r)
    (fun r hr => by
      have hr0 : 0 < r := ha.trans_lt hr
      unfold poissonRadialWeight
      positivity)
    (tendsto_poissonRadialPrimitive_atTop hη)
  simpa [poissonRadialPrimitive] using h

/-- The radial density is integrable on every nonnegative tail.
This is the integrability input needed when the real layer-cake identity is
transported to an `ℝ≥0∞` Tonelli argument. -/
theorem integrableOn_poissonRadialWeight_Ioi
    {η a : ℝ} (hη : 0 < η) (ha : 0 ≤ a) :
    IntegrableOn (poissonRadialWeight η) (Ioi a) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := poissonRadialPrimitive η)
  · intro r _hr
    exact hasDerivAt_poissonRadialPrimitive hη r
  · intro r hr
    have hr0 : 0 < r := ha.trans_lt hr
    unfold poissonRadialWeight
    positivity
  · exact tendsto_poissonRadialPrimitive_atTop hη

/-- Pointwise layer-cake representation of the centered Poisson kernel. -/
theorem integral_poissonRadialWeight_Ioi_abs
    {η x : ℝ} (hη : 0 < η) :
    (∫ r : ℝ in Ioi |x|, poissonRadialWeight η r) =
      η / (x ^ 2 + η ^ 2) := by
  rw [integral_poissonRadialWeight_Ioi hη (abs_nonneg x)]
  congr 2
  exact sq_abs x

private theorem integrable_inv_one_add_sq_sq' :
    Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹ ^ 2) := by
  have h₁ : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  apply h₁.mono'
  · fun_prop (discharger := intro x; positivity)
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnonneg : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
    have hle : (1 + t ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity : 0 < 1 + t ^ 2)]
      nlinarith [sq_nonneg t]
    nlinarith

private theorem integrable_base_poisson_moment :
    Integrable (fun t : ℝ => 4 * t ^ 2 / (1 + t ^ 2) ^ 2) := by
  have h₁ : Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  have h₂ := integrable_inv_one_add_sq_sq'
  refine ((h₁.sub h₂).const_mul 4).congr ?_
  filter_upwards with t
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- The first radial moment is integrable at every positive scale. -/
theorem integrableOn_mul_poissonRadialWeight_Ioi
    {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun r => (2 * r) * poissonRadialWeight η r) (Ioi 0) := by
  let g : ℝ → ℝ := fun r => (2 * r) * poissonRadialWeight η r
  have hpoint : (fun t : ℝ => g (η * t)) =
      fun t => η⁻¹ * (4 * t ^ 2 / (1 + t ^ 2) ^ 2) := by
    funext t
    dsimp [g, poissonRadialWeight]
    field_simp [hη.ne']
    ring
  have hcomp : IntegrableOn (fun t => g (η * t)) (Ioi 0) := by
    rw [hpoint]
    exact integrable_base_poisson_moment.integrableOn.const_mul η⁻¹
  have hg := (integrableOn_Ioi_comp_mul_left_iff g 0 hη).mp hcomp
  simpa only [g, mul_zero] using hg

/-- The dimensionless first moment of the radial density is `π`. -/
theorem integral_base_poisson_moment_Ioi :
    (∫ t : ℝ in Ioi 0, 4 * t ^ 2 / (1 + t ^ 2) ^ 2) = Real.pi := by
  let f : ℝ → ℝ := fun t => 4 * t ^ 2 / (1 + t ^ 2) ^ 2
  have habs : (fun t : ℝ => f |t|) = f := by
    funext t
    simp [f, sq_abs]
  have hfull : (∫ t : ℝ, f t) = 2 * Real.pi := by
    rw [show f = fun t : ℝ =>
      4 * ((1 + t ^ 2)⁻¹ - (1 + t ^ 2)⁻¹ ^ 2) by
      funext t
      dsimp [f]
      field_simp
      ring]
    rw [integral_const_mul, integral_sub integrable_inv_one_add_sq
      integrable_inv_one_add_sq_sq']
    rw [integral_univ_inv_one_add_sq, integral_inv_one_add_sq_sq]
    ring
  have hhalf := integral_comp_abs (f := f)
  rw [habs, hfull] at hhalf
  linarith

/-- Sharp first radial moment at scale `η`. -/
theorem integral_mul_poissonRadialWeight_Ioi
    {η : ℝ} (hη : 0 < η) :
    (∫ r : ℝ in Ioi 0, (2 * r) * poissonRadialWeight η r) = Real.pi := by
  let g : ℝ → ℝ := fun r => (2 * r) * poissonRadialWeight η r
  have hscale := integral_comp_mul_left_Ioi g 0 hη
  have hpoint : (fun t : ℝ => g (η * t)) =
      fun t => η⁻¹ * (4 * t ^ 2 / (1 + t ^ 2) ^ 2) := by
    funext t
    dsimp [g, poissonRadialWeight]
    field_simp [hη.ne']
    ring
  rw [hpoint, integral_const_mul, integral_base_poisson_moment_Ioi] at hscale
  dsimp [g] at hscale
  have hscale0 :
      η⁻¹ * Real.pi =
        η⁻¹ * ∫ x : ℝ in Ioi 0, (2 * x) * poissonRadialWeight η x := by
    simpa only [mul_zero] using hscale
  have hscale' :
      (∫ x : ℝ in Ioi 0, (2 * x) * poissonRadialWeight η x) =
        Real.pi := by
    calc
      (∫ x : ℝ in Ioi 0, (2 * x) * poissonRadialWeight η x) =
          η * (η⁻¹ *
            ∫ x : ℝ in Ioi 0, (2 * x) * poissonRadialWeight η x) := by
              field_simp
      _ = η * (η⁻¹ * Real.pi) := by
            rw [← hscale0]
      _ = Real.pi := by field_simp
  calc
    (∫ r : ℝ in Ioi 0, (2 * r) * poissonRadialWeight η r)
        = Real.pi := hscale'

end CoareaNative.BlockBand
