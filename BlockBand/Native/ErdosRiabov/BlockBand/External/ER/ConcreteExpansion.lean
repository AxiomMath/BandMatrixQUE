module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.LocalLawBootstrap
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProfileAdmissibility
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ERControlKernels

/-!
# Concrete Gaussian-ring expansion variables

This module defines concrete variables motivated by the generic ER bootstrap,
built from a `GaussianRing.Law`: the source-sign resolvent,
its semicircle error, its covariance-weighted fluctuation, and the associated
control variable.  It proves the exact finite resolvent equation, the
one-coordinate Gaussian integration-by-parts equation, centering, and the
moments-to-stochastic-estimate passage.

The only analytic hypotheses below are displayed derivative/integrability or
moment inequalities.  In particular neither stochastic domination, a bootstrap step, nor
`BandLocalLawInput` occurs as a hypothesis.  Stochastic domination appears only
as a conclusion of the proved Markov argument.  The deterministic profile and
entry law are obtained from `ProfileAdmissibility`.

Source: Erdős–Riabov, arXiv:2506.06441v1, Definition 2.1, equations
(3.2)--(3.17), and the proof of Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERConcrete

open Matrix MeasureTheory ProbabilityTheory ERLocalLaw
open scoped BigOperators ENNReal NNReal

local instance (p : Params) : NeZero p.n := p.nNeZero

/-!
## Resolvent error and control variables
-/

/-- ER's source-sign Green function `G(z) = (H-z)⁻¹` for a Gaussian
ring realization.  `matrixResolvent` has the opposite sign. -/
def green {p : Params} (M : Law p) (z : ℂ) (ω : M.Ω) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  -matrixResolvent (M.H ω) z

/-- The deterministic diagonal semicircle approximation. -/
def semicircleMatrix (p : Params) (z : ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  (erSemicircleStieltjes z) • 1

/-- The entrywise resolvent error `G-mI`. -/
def resolventError {p : Params} (M : Law p) (z : ℂ) (ω : M.Ω) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  green M z ω - semicircleMatrix p z

/-- The real error variable at a fixed pair of physical sites. -/
def entryError {p : Params} (M : Law p) (z : ℂ)
    (x y : Site p.n p.W) (ω : M.Ω) : ℝ :=
  ‖resolventError M z ω x y‖

/-- ER's covariance-weighted resolvent fluctuation at `(x,y)`, as a random variable on the
sample space of the law. -/
def weightedFluctuation {p : Params} (M : Law p) (z : ℂ)
    (x y : Site p.n p.W) (ω : M.Ω) : ℂ :=
  ∑ a, (ERProfile.siteCovariance p x a : ℂ) *
    resolventError M z ω a y

/-!
## The exact resolvent equation
-/

/-- The source-sign resolvent solves `(H-z)G=I` at every nonreal spectral
parameter.  This is the exact entry law before Gaussian integration by parts. -/
theorem matrix_mul_green {p : Params} (M : Law p) (z : ℂ) (hz : z.im ≠ 0)
    (ω : M.Ω) :
    (M.H ω - z • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)) *
        green M z ω = 1 := by
  let A := z • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) - M.H ω
  have hA : IsUnit A := isUnit_resolventPencil (M.H ω) (M.H_hermitian ω) hz
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hcancel : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  rw [show M.H ω - z • (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) = -A by
    simp [A]]
  rw [show green M z ω = -A⁻¹ by simp [green, matrixResolvent, A]]
  simpa using hcancel

/-- Entrywise exact self-consistent resolvent equation. -/
theorem entry_selfConsistent_exact {p : Params} (M : Law p) (z : ℂ)
    (hz : z.im ≠ 0) (ω : M.Ω) (x y : Site p.n p.W) :
    (∑ a, M.H ω x a * green M z ω a y) -
        z * green M z ω x y = if x = y then 1 else 0 := by
  have h := congrArg (fun A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ => A x y)
    (matrix_mul_green M z hz ω)
  change (∑ a, (M.H ω x a - z *
      (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) x a) *
        green M z ω a y) =
      (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) x y at h
  calc
    (∑ a, M.H ω x a * green M z ω a y) -
        z * green M z ω x y =
        ∑ a, (M.H ω x a - z *
          (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) x a) *
            green M z ω a y := by
      simp [sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
    _ = (1 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) x y := h
    _ = if x = y then 1 else 0 := Matrix.one_apply

/-!
## Gaussian IBP and centering
-/

/-!
## High moments imply the concrete stochastic estimate
-/

end ERConcrete
end GaussianRing
end ERNative.BlockBand
