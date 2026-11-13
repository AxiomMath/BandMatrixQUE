module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ResolventIdentities
public import BlockBand.Native.ErdosRiabov.BlockBand.CriticalSequences
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import BlockBand.Native.ErdosRiabov.BlockBand.Probability.GaussianIntegrationByParts
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Generic machinery for the Erdős–Riabov local-law bootstrap

This module isolates reusable algebraic and probabilistic steps of the short-ring
local-law argument.  It does **not** assert a local law.

* exact first- and second-order inverse-matrix expansions (`nonsingInv_sub_nonsingInv`,
  `nonsingInv_secondOrder`);
* the Gaussian cumulant specialization (all cumulants of order at least three
  vanish, `GaussianCumulantSequence`) and the Gaussian integration-by-parts identity
  (`gaussian_ibp`);
* the geometric continuity grid in the imaginary height (`heightGrid`).

Source: Erdős–Riabov, *The zigzag strategy for random band matrices*,
arXiv:2506.06441v1, proof of Theorem 3.3.  These declarations neither construct the
short-ring covariance operator nor assume the conclusion of Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace ERLocalLaw

open Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal

/-!
## Inverse-matrix differentiation identities
-/

/-- Exact first variation of matrix inversion.  This is the algebraic identity
whose difference quotient gives `D(A⁻¹)[H] = -A⁻¹HA⁻¹`.  Unlike a formal
Taylor series it has an exact remainder and works over every commutative base
ring for which both displayed matrices are units. -/
theorem nonsingInv_sub_nonsingInv
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  rw [Matrix.inv_sub_inv]
  exact ⟨fun _ => hB, fun _ => hA⟩

/-- Exact second-order remainder for inverse-matrix differentiation.  The
linear term is `-A⁻¹ (B-A) A⁻¹`; the right side contains two perturbation
factors and the inverse at the perturbed point. -/
theorem nonsingInv_secondOrder
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (hA : IsUnit A) (hB : IsUnit B) :
    B⁻¹ - A⁻¹ + A⁻¹ * (B - A) * A⁻¹ =
      A⁻¹ * (B - A) * A⁻¹ * (B - A) * B⁻¹ := by
  have h := nonsingInv_sub_nonsingInv A B hA hB
  calc
    B⁻¹ - A⁻¹ + A⁻¹ * (B - A) * A⁻¹ =
        -(A⁻¹ * (B - A) * B⁻¹) + A⁻¹ * (B - A) * A⁻¹ := by
          rw [show B⁻¹ - A⁻¹ = -(A⁻¹ - B⁻¹) by abel, h]
    _ = A⁻¹ * (B - A) * (A⁻¹ - B⁻¹) := by noncomm_ring
    _ = A⁻¹ * (B - A) * (A⁻¹ * (B - A) * B⁻¹) := by rw [h]
    _ = A⁻¹ * (B - A) * A⁻¹ * (B - A) * B⁻¹ := by noncomm_ring

/-!
## Gaussian cumulants and integration by parts
-/

/-- The cumulant sequence of a centered real Gaussian coordinate of variance
`variance`.  Indices follow the usual convention: orders zero and one vanish,
order two is the covariance, and every higher cumulant vanishes. -/
structure GaussianCumulantSequence (variance : ℂ) (cumulant : ℕ → ℂ) : Prop where
  orderZero : cumulant 0 = 0
  orderOne : cumulant 1 = 0
  orderTwo : cumulant 2 = variance
  higher : ∀ r : ℕ, 3 ≤ r → cumulant r = 0

/-- The real Gaussian integration-by-parts formula used after the cumulant
specialization.  This theorem is an ER-facing name for the unconditional
one-coordinate result, retaining all derivative and integrability hypotheses. -/
theorem gaussian_ibp
    (v : NNReal) (hv : v ≠ 0) (f f' : ℝ → ℂ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hxf : Integrable (fun x =>
      ((x * ProbabilityTheory.gaussianPDFReal 0 v x : ℝ) : ℂ) * f x))
    (hdf : Integrable (fun x =>
      ((ProbabilityTheory.gaussianPDFReal 0 v x : ℝ) : ℂ) * f' x))
    (hf : Integrable (fun x =>
      ((ProbabilityTheory.gaussianPDFReal 0 v x : ℝ) : ℂ) * f x)) :
    (∫ x : ℝ, ((x : ℂ) * f x) ∂ProbabilityTheory.gaussianReal 0 v) =
      (v : ℝ) * ∫ x : ℝ, f' x ∂ProbabilityTheory.gaussianReal 0 v :=
  realGaussianIntegrationByParts_density v hv f f' hderiv hxf hdf hf

/-!
## Admissible covariance operators and weighted averaging
-/

/-!
## Self-consistency and finite imaginary-height descent
-/

/-- The deterministic geometric grid used for continuity in the imaginary
height.  `heightGrid η₀ ratio k = η₀ ratio^k`; finite descent never appeals to
an infinitary choice of spectral parameters. -/
def heightGrid (η₀ ratio : ℝ) (k : ℕ) : ℝ := η₀ * ratio ^ k

@[simp] theorem heightGrid_zero (η₀ ratio : ℝ) :
    heightGrid η₀ ratio 0 = η₀ := by simp [heightGrid]

@[simp] theorem heightGrid_succ (η₀ ratio : ℝ) (k : ℕ) :
    heightGrid η₀ ratio (k + 1) = ratio * heightGrid η₀ ratio k := by
  simp [heightGrid, pow_succ]
  ring

/-!
## Explicit tail quantifiers
-/

end ERLocalLaw
end ERNative.BlockBand
