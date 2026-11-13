module

public import BlockBand.Model.Construction.OrderedEigenvalues
public import BlockBand.Foundations.Spectral.OrderedEigenpairs
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measurability of the increasing Hermitian spectrum

The increasing eigenvalues of a Hermitian matrix, with multiplicity, are continuous and Borel
measurable functions of the matrix, individually and as the full ordered spectrum.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Model.Construction

open BlockBand.Foundations.Spectral

abbrev HermitianMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  {A : Matrix ι ι ℂ // A.IsHermitian}

noncomputable def orderedEigenvalue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) := increasingEigenvalue A.property

section OrderedSpectrum

variable {ι : Type*} [fintypeι : Fintype ι] [decEqι : DecidableEq ι]

/-- The Hermitian subtype carries the measurable space induced from raw matrices. -/
theorem measurableSpace_hermitianMatrix :
    (inferInstance : MeasurableSpace (HermitianMatrix ι)) =
      MeasurableSpace.comap
        (Subtype.val : HermitianMatrix ι → Matrix ι ι ℂ)
        (borel (Matrix ι ι ℂ)) := by
  change MeasurableSpace.comap Subtype.val
      (inferInstance : MeasurableSpace (Matrix ι ι ℂ)) =
    MeasurableSpace.comap Subtype.val (borel (Matrix ι ι ℂ))
  rw [show (inferInstance : MeasurableSpace (Matrix ι ι ℂ)) =
    borel (Matrix ι ι ℂ) from BorelSpace.measurable_eq]

set_option linter.unusedSectionVars false in
/-- Coercion from the Hermitian subtype to the raw matrix is Borel measurable. -/
theorem measurable_coe_hermitianMatrix :
    Measurable (Subtype.val : HermitianMatrix ι → Matrix ι ι ℂ) :=
  measurable_subtype_coe

/-- Every coordinate of the increasing ordered spectrum is continuous in the entrywise matrix
topology. The proof uses the `card ι * ε` entrywise perturbation bound and does not assume
simple spectrum. -/
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
  refine A.property.abs_eigenvalues₀_sub_le_of_entry_le B.property (fun p q => ?_) i.rev
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

/-- The complete finite increasing ordered spectrum is Borel measurable as a
function-valued map. -/
theorem measurable_orderedSpectrum :
    Measurable (fun A : HermitianMatrix ι =>
      (fun i : Fin (Fintype.card ι) => orderedEigenvalue A i)) :=
  measurable_pi_iff.mpr fun i => measurable_orderedEigenvalue i

/-- Continuity of `increasingEigenvalue`, with multiplicities. -/
theorem continuous_increasingEigenvalue (i : Fin (Fintype.card ι)) :
    Continuous (fun A : HermitianMatrix ι =>
      BlockBand.Foundations.Spectral.increasingEigenvalue A.property i) :=
  continuous_orderedEigenvalue i

/-- Borel measurability of the increasing rank coordinate. -/
theorem measurable_increasingEigenvalue (i : Fin (Fintype.card ι)) :
    Measurable (fun A : HermitianMatrix ι =>
      BlockBand.Foundations.Spectral.increasingEigenvalue A.property i) :=
  measurable_orderedEigenvalue i

end OrderedSpectrum

end BlockBand.Model.Construction
