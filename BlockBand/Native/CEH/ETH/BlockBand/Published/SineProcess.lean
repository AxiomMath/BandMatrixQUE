module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.RationalWindowPointState
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# Conditional interface for the intensity-one sine process

The paper (the definition of the sine process, and the discussion following the
sine-endpoint comparison) uses the simple determinantal point process on `ℝ` whose
kernel is

`K(x,y) = sin (π (x-y)) / (π (x-y))`, with diagonal value `1`.

Mathlib has finite/product measures and probability measures, but no construction of
locally finite point processes or determinantal point processes.  The common
point-state representation used here is `RationalWindowPointState`: a
consistent sequence of finite window measures with natural masses on every rational
interval.  Accordingly this file does **not** assert existence of the sine process.
It gives the kernel and determinant densities, spells out their exact factorial-moment
meaning in that representation, and packages a law satisfying that characterization
as explicit input data.  Every downstream conditional theorem must receive a
`SineProcessInput` parameter; constructing one is separate published-input debt.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory
open scoped ENNReal NNReal Topology

/-- The intensity-one complex-Hermitian sine kernel.  The separate diagonal branch is
part of the normalization in the definition of the sine process in the paper; in particular there is no removable
`0 / 0` ambiguity in the Lean definition. -/
def sineKernel (x y : ℝ) : ℝ :=
  if x = y then 1 else Real.sin (Real.pi * (x - y)) / (Real.pi * (x - y))

/-- The `k`-point sine correlation density: the determinant of the sine-kernel
matrix.  This is the complex-Hermitian (`β = 2`) determinantal normalization used by
the paper. -/
def sineCorrelation (k : ℕ) (x : Fin k → ℝ) : ℝ :=
  (Matrix.of fun i j => sineKernel (x i) (x j)).det

/-- The diagonal normalization of the sine kernel is exactly one. -/
@[simp] theorem sineKernel_self (x : ℝ) : sineKernel x x = 1 := by
  simp [sineKernel]

/-- Away from the diagonal, the kernel is the normalized sine quotient of the paper. -/
theorem sineKernel_of_ne {x y : ℝ} (h : x ≠ y) :
    sineKernel x y =
      Real.sin (Real.pi * (x - y)) / (Real.pi * (x - y)) := by
  simp [sineKernel, h]

/-- The one-point determinant is one, recording the intensity-one normalization. -/
@[simp] theorem sineCorrelation_one (x : Fin 1 → ℝ) :
    sineCorrelation 1 x = 1 := by
  simp [sineCorrelation]

/-- The unmarked spatial finite measure in one exhaustion window of the repository's
local point-state representation.  The `Unit` mark is forgotten. -/
def RationalWindowPointState.spatialWindow
    (ξ : RationalWindowPointState) (n : ℕ) : FiniteMeasure ℝ :=
  ξ.window n |>.map Prod.fst

/-- The ordered `k`-fold product of a local spatial window, restricted to tuples of
distinct locations and then evaluated on `B`.  For a simple counting measure this is
exactly its local `k`th factorial measure on `B`. -/
def localFactorialMass (k n : ℕ) (ξ : RationalWindowPointState)
    (B : Set (Fin k → ℝ)) : ENNReal :=
  Measure.pi (fun _ : Fin k => (ξ.spatialWindow n : Measure ℝ))
    ({x | Function.Injective x} ∩ B)

/-- A local point state is simple when no spatial singleton has mass greater than one
in any exhaustion window.  Requiring this explicitly prevents a correlation interface
from silently treating multiplicities as distinct points. -/
def IsSimplePointState (ξ : RationalWindowPointState) : Prop :=
  ∀ n x, (ξ.spatialWindow n : Measure ℝ) {x} ≤ 1

/-- Exact factorial-correlation characterization of the intensity-one sine law.

For every order `k`, every exhaustion window, and every measurable set `B` contained
in the open window cube, the expected ordered distinct-tuple count is the integral of
`det (K(xᵢ,xⱼ))`.  The separate measurability clause makes the expectation a
Lebesgue integral rather than relying on Mathlib's convention for nonmeasurable
integrands.  Quantification over all `k` includes `k = 1`, hence fixes intensity one. -/
def HasSineKernelCorrelations
    (law : ProbabilityMeasure RationalWindowPointState) : Prop :=
  (∀ᵐ ξ ∂(law : Measure RationalWindowPointState), IsSimplePointState ξ) ∧
  ∀ (k n : ℕ) (B : Set (Fin k → ℝ)),
    MeasurableSet B →
    B ⊆ Set.pi Set.univ (fun _ : Fin k => Set.Ioo (-(n : ℝ)) (n : ℝ)) →
      Measurable (fun ξ : RationalWindowPointState => localFactorialMass k n ξ B) ∧
      ∫⁻ ξ, localFactorialMass k n ξ B ∂(law : Measure RationalWindowPointState) =
        ∫⁻ x in B, ENNReal.ofReal (sineCorrelation k x) ∂volume

/-- The order-one specialization of the determinant characterization is exactly
Lebesgue intensity one on every measurable local tuple set. -/
theorem HasSineKernelCorrelations.intensityOne
    {law : ProbabilityMeasure RationalWindowPointState}
    (h : HasSineKernelCorrelations law) (n : ℕ)
    (B : Set (Fin 1 → ℝ)) (hB : MeasurableSet B)
    (hlocal : B ⊆ Set.pi Set.univ
      (fun _ : Fin 1 => Set.Ioo (-(n : ℝ)) (n : ℝ))) :
    Measurable (fun ξ : RationalWindowPointState => localFactorialMass 1 n ξ B) ∧
      ∫⁻ ξ, localFactorialMass 1 n ξ B ∂(law : Measure RationalWindowPointState) =
        volume B := by
  simpa using h.2 1 n B hB hlocal

/-- The sine process, as an explicit conditional input.

A value supplies existence (`law`) together with the exact simplicity and
sine-determinantal correlation characterization (`correlations`).  This is data, not
an existence theorem or axiom.  It is intentionally a `Type`, so consumers cannot
mention a global sine law without visibly receiving a witness. -/
structure SineProcessInput where
  law : ProbabilityMeasure RationalWindowPointState
  correlations : HasSineKernelCorrelations law

/-- The conditional sine-process law supplied by an explicit `SineProcessInput` witness. -/
def sineProcess (input : SineProcessInput) :
    ProbabilityMeasure RationalWindowPointState :=
  input.law

/-- Unfolding the conditional law reveals exactly the supplied probability measure. -/
@[simp] theorem sineProcess_eq_law (input : SineProcessInput) :
    sineProcess input = input.law := rfl

/-- The supplied sine law has the exact sine-kernel factorial correlations. -/
theorem sineProcess_hasSineKernelCorrelations (input : SineProcessInput) :
    HasSineKernelCorrelations (sineProcess input) :=
  input.correlations

end CEHNative.BlockBand
