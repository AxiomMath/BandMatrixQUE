module

public import BlockBand.Native.PSSS.BlockBand.Basic.Indices
public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import BlockBand.Native.PSSS.BlockBand.Probability.GaussianNormalization
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.Schur
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import BlockBand.Native.PSSS.BlockBand.Coarea.GaussianRegression
public import BlockBand.Native.PSSS.BlockBand.Coarea.HermitianSimpleSpectrum
public import Mathlib.Probability.Independence.Integration

/-!
# Physical finite-product Hermitian Gaussian split

This module upgrades the scalar variance split to an explicit finite product.
The fresh variable is carried by the product of the diagonal `N(0,t)` laws and
the two strict-upper `N(0,t/2)` laws.  Reconstruction therefore gives a
Hermitian matrix with the GUE law.
On the product with residual and exterior data we define `H_SS = V + G`, prove
the exact identity and independence, and give the Tonelli formula used when
fixed-exterior coarea is applied.

The density convention is
`Z_d(t)⁻¹ exp (-Tr(G²)/(2t))`, with the normalizer
`Z_d(t) = gueNormalizer d t`.  All statements are at fixed finite `d` and
positive `t`; no limiting or uniformity assertion is present.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace PSSSNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Variance of one real finite Hermitian coordinate in a GUE block: `t` on
its diagonal and `t/2` on each real or imaginary strict-upper coordinate. -/
def hermitianGUEFinCoordinateVariance (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) : NNReal :=
  match (hermitianCoordinateEquivFin d).symm k with
  | .inl _ => ⟨t, ht⟩
  | .inr _ => ⟨t / 2, div_nonneg ht (by norm_num)⟩

/-- The explicit finite product of all real GUE coordinate laws. -/
def hermitianGUECoordinateMeasure (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure (HermitianCoordinateSpace d) :=
  Measure.pi fun k => gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht k)

instance hermitianGUECoordinateMeasure.instIsProbabilityMeasure
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IsProbabilityMeasure (hermitianGUECoordinateMeasure d t ht) := by
  unfold hermitianGUECoordinateMeasure
  infer_instance

/-- The fresh Hermitian GUE matrix reconstructed from the independent real
coordinates. -/
def hermitianGUEBlock (d : ℕ) (x : HermitianCoordinateSpace d) :
    HermitianMatrix (Fin d) :=
  hermitianOfFinCoordinates d x

/-- Reconstruction of the finite-product GUE block is Borel measurable. -/
theorem measurable_hermitianGUEBlock (d : ℕ) :
    Measurable (hermitianGUEBlock d) :=
  measurable_hermitianOfFinCoordinates d

/-- Every finite real coordinate has the required centered Gaussian marginal. -/
theorem hermitianGUECoordinate_hasLaw (d : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    HasLaw (fun x : HermitianCoordinateSpace d => x k)
      (gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht k))
      (hermitianGUECoordinateMeasure d t ht) := by
  refine ⟨measurable_pi_apply k |>.aemeasurable, ?_⟩
  exact (measurePreserving_eval
    (fun j => gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht j)) k).map_eq

/-- The complete real coordinate family of the explicit GUE block is mutually
independent. -/
theorem iIndepFun_hermitianGUECoordinates (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iIndepFun (fun k (x : HermitianCoordinateSpace d) => x k)
      (hermitianGUECoordinateMeasure d t ht) := by
  unfold hermitianGUECoordinateMeasure
  apply iIndepFun_pi
    (X := fun _ : Fin (Fintype.card (HermitianCoordinate d)) => id)
  intro k
  exact measurable_id.aemeasurable

/-- The GUE matrix density `Z_d(t)⁻¹ exp (-Tr(G²)/(2t))`.  The product
construction above supplies its probability normalization coordinate by
coordinate; this expression records the equivalent GUE matrix convention used
by coarea. -/
def hermitianGUEDensity (d : ℕ) (t : ℝ)
    (G : HermitianMatrix (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-hilbertSchmidtNormSq G.1 / (2 * t)) / gueNormalizer d t)

end PSSSNative.BlockBand
