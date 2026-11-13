module

public import BlockBand.PointProcess.Specifications

/-!
# Fredholm expansions of determinantal Laplace functionals

For a kernel `K`, a measure `ν` and a weight `φ`, the Fredholm series is
`∑' k, (-1)^k / k! ∫ det [K (x i) (x j)] ∏ φ (x i) dν^k` (`fredholmSeries`). The sine Laplace
functional is the Fredholm series of the sine kernel against Lebesgue measure with weight
`1 - exp (-f)` (`sineLaplaceFunctional_eq_fredholmSeries`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory

/-- The `k`-th unsigned Fredholm integral
`∫ det [K (x i) (x j)] ∏ φ (x i) dν^k`. -/
def fredholmIntegral (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ x : Fin k → ℝ,
    Matrix.det (fun i j : Fin k => K (x i) (x j)) * ∏ i : Fin k, φ (x i)
    ∂Measure.pi (fun _ : Fin k => ν)

/-- The `k`-th signed Fredholm term `(-1)^k / k! * fredholmIntegral`. -/
def fredholmTerm (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ)) * fredholmIntegral K ν φ k

/-- Fredholm expansion `∑' k, (-1)^k / k! ∫ det [K (x i) (x j)] ∏ φ (x i) dν^k`. -/
def fredholmSeries (K : ℝ → ℝ → ℝ) (ν : Measure ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∑' k : ℕ, fredholmTerm K ν φ k

/-- The sine Laplace functional is the Fredholm expansion of the sine kernel against Lebesgue
measure with weight `1 - exp (-f)`. -/
theorem sineLaplaceFunctional_eq_fredholmSeries
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    sineLaplaceFunctional f =
      fredholmSeries sineKernel volume (fun x => 1 - Real.exp (-f x)) := rfl

end BlockBand.Endpoints
