module

public import BlockBand.Prelude
public import BlockBand.Foundations.Spectral.OrderedEigenpairs

/-!
# Definitions for the physical finite-log recovery

The kernels and spectral statistics used in the finite-log recovery lemma:

- `poissonKernel t x = t / (π (x² + t²))` (the Cauchy kernel `p_t`);
- `logKernel δ x = (2πδ)⁻¹ log (1 + δ²/x²)` (`k_δ`; at `x = 0` Lean's
  `δ²/0 = 0` gives the value `0`, a single point);
- `positiveLogStatistic H E Λ δ P f` is the positive log statistic `𝓡_δ^C(H; f)`, with
  absorber projector `P = P_C`:
  `(πδ)⁻¹ ∫ f x · log |det (H - E - x/Λ + i δ P/Λ) / det (H - E - x/Λ)| dx`;
- `unfoldedSpectralSum H hH E Λ f = Tr f(Λ(H - E)) = Σ_α f (Λ (λ_α - E))`,
  with the repository's increasing-eigenvalue convention (multiplicity).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory

/-- Cauchy (Poisson) kernel `p_t(x) = t / (π (x² + t²))`. -/
def poissonKernel (t x : ℝ) : ℝ := t / (Real.pi * (x ^ 2 + t ^ 2))

/-- Logarithmic kernel `k_δ(x) = (2πδ)⁻¹ log (1 + δ²/x²)`. -/
def logKernel (δ x : ℝ) : ℝ := (2 * Real.pi * δ)⁻¹ * Real.log (1 + δ ^ 2 / x ^ 2)

/-- The shifted resolvent argument `H - (E + x/Λ) + i a P`, as a complex matrix. -/
def absorbedShift {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (E Λ x a : ℝ) (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  H - ((E + x / Λ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) + ((a : ℂ) * Complex.I) • P

/-- The positive log statistic `𝓡_δ^C(H; f)` with absorber projector `P = P_C`. -/
def positiveLogStatistic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (E Λ δ : ℝ) (P : Matrix ι ι ℂ) (f : ℝ → ℝ) : ℝ :=
  (Real.pi * δ)⁻¹ * ∫ x, f x * Real.log
    (‖(absorbedShift H E Λ x (δ / Λ) P).det‖ / ‖(absorbedShift H E Λ x 0 P).det‖)

/-- `Tr f(Λ(H - E)) = Σ_α f (Λ (λ_α - E))`, eigenvalues with multiplicity. -/
def unfoldedSpectralSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (E Λ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, f (Λ * (BlockBand.Foundations.Spectral.increasingEigenvalue hH i - E))

end BlockBand.Endpoints
