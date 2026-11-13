module

public import BlockBand.PointProcess.Vague

/-!
# Explicit specifications of the endpoint point-process laws

These predicates are mathematical characterizations, not opaque names for the
desired endpoints. The construction and uniqueness theorems are future proof
obligations.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand

open MeasureTheory

/-- The intensity-one sine kernel, including its diagonal value. -/
def sineKernel (x y : ℝ) : ℝ :=
  Real.sinc (Real.pi * (x - y))

/-- A law has unit Poisson Laplace functional. The compactly supported test is
required to be nonnegative. -/
def IsUnitPoissonLaw
    (law : ProbabilityMeasure (VaguePointMeasure ℝ)) : Prop :=
  ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
    ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(law : Measure (VaguePointMeasure ℝ)) =
      Real.exp (-∫ x, (1 - Real.exp (-f x)))

/-- Fredholm expansion of the sine-kernel Laplace functional. This is an
explicit determinantal characterization, using the intensity-one kernel
`sin (π(x-y))/(π(x-y))`. -/
def sineLaplaceFunctional
    (f : CompactlySupportedContinuousMap ℝ ℝ) : ℝ :=
  ∑' k : ℕ, ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
    ∫ x : Fin k → ℝ,
      Matrix.det (fun i j : Fin k => sineKernel (x i) (x j)) *
        ∏ i : Fin k, (1 - Real.exp (-f (x i)))
      ∂Measure.pi (fun _ : Fin k => volume)

/-- A law is the intensity-one determinantal sine process when it is simple
and its Laplace functional agrees with the sine-kernel Fredholm expansion for
every nonnegative compactly supported continuous test. -/
def IsSineLaw
    (law : ProbabilityMeasure (VaguePointMeasure ℝ)) : Prop :=
  (∀ᵐ ξ ∂(law : Measure (VaguePointMeasure ℝ)), IsSimplePointMeasure ξ) ∧
  ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) →
    ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure)
        ∂(law : Measure (VaguePointMeasure ℝ)) =
      sineLaplaceFunctional f

end BlockBand
