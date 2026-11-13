module

public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measurability of the increasing Hermitian spectrum

Each increasingly ordered eigenvalue of a Hermitian matrix is a Lipschitz, hence continuous and
Borel measurable, function of the matrix entries.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

section OrderedSpectrum

variable {ι : Type*} [fintypeι : Fintype ι] [decEqι : DecidableEq ι]

set_option linter.unusedSectionVars false in
/-- The coercion from Hermitian matrices to matrices is Borel measurable. -/
theorem measurable_coe_hermitianMatrix :
    Measurable (Subtype.val : HermitianMatrix ι → Matrix ι ι ℂ) :=
  measurable_subtype_coe

/-- Every coordinate of the increasing ordered spectrum is continuous in
the entrywise matrix topology.  The proof uses the `card ι * ε` entrywise
perturbation bound `orderedEigenvalue_entrywisePerturbation` and does not assume
simple spectrum.
-/
theorem continuous_orderedEigenvalue (i : Fin (Fintype.card ι)) :
    Continuous (fun A : HermitianMatrix ι => orderedEigenvalue A i) := by
  let _ : PseudoMetricSpace (Matrix ι ι ℂ) :=
    inferInstanceAs (PseudoMetricSpace (ι → ι → ℂ))
  apply (show LipschitzWith (Fintype.card ι : NNReal)
      (fun A : HermitianMatrix ι => orderedEigenvalue A i) from
        LipschitzWith.of_dist_le_mul ?_).continuous
  intro A B
  change |orderedEigenvalue A i - orderedEigenvalue B i| ≤
    (Fintype.card ι : ℝ) * dist A B
  apply orderedEigenvalue_entrywisePerturbation A B
  intro p q
  calc
    ‖(A : Matrix ι ι ℂ) p q - (B : Matrix ι ι ℂ) p q‖ =
        dist ((A : Matrix ι ι ℂ) p q) ((B : Matrix ι ι ℂ) p q) := by
          rw [dist_eq_norm]
    _ ≤ dist ((A : Matrix ι ι ℂ) p) ((B : Matrix ι ι ℂ) p) :=
      dist_le_pi_dist _ _ q
    _ ≤ dist (A : Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :=
      dist_le_pi_dist _ _ p
    _ = dist A B := rfl

/-- Every increasing ordered eigenvalue coordinate is Borel measurable. -/
theorem measurable_orderedEigenvalue (i : Fin (Fintype.card ι)) :
    Measurable (fun A : HermitianMatrix ι => orderedEigenvalue A i) :=
  (continuous_orderedEigenvalue i).measurable

end OrderedSpectrum

end PSSSNative.BlockBand
