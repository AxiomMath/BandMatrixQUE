module

public import Mathlib

/-!
# Factorial moments of eigenvalue counts

This file defines the falling-factorial moments of a natural-valued count and the bound
`E[count(count - 1)⋯(count - r + 1)] ≤ (C · dimension · intervalLength)^r`, the form of the
factorial-moment bound of PSSS for eigenvalue counts in an interval. The PSSS theorem concerns
block matrices with independent blocks `G_j ~ GUE_{d_j}(1/d_j)` plus an arbitrary deterministic
Hermitian deformation, of total dimension `d = Σ_j d_j`, with one absolute constant `C` chosen
before the dimensions, the deformation, the interval and the order. Here the count is an
arbitrary observable; no Gaussian law is assumed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.External.PSSS

open MeasureTheory

/-- The falling factorial `count(count - 1)⋯(count - r + 1)` as a real number; it is `1` for
`r = 0` and `0` when `r > count`. -/
def factorialCount {Ω : Type*} (count : Ω → ℕ) (r : ℕ) : Ω → ℝ :=
  fun ω => (Nat.descFactorial (count ω) r : ℝ)

/-- The factorial-moment bound of order `r`:
`∫ factorialCount count r dμ ≤ (C · dimension · intervalLength)^r`, where `dimension` is the
matrix dimension and `intervalLength = b - a` for an interval `[a, b]`. Integrability of bounded
measurable counts is proved separately (`integrable_factorialCount`). -/
def FactorialMomentBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (count : Ω → ℕ) (dimension : ℕ)
    (intervalLength C : ℝ) (r : ℕ) : Prop :=
  (∫ ω, factorialCount count r ω ∂μ) ≤
    (C * (dimension : ℝ) * intervalLength) ^ r

end BlockBand.External.PSSS
