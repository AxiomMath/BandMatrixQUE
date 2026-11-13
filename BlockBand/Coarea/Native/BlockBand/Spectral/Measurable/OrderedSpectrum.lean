module

public import BlockBand.Coarea.Native.BlockBand.Spectral.Ordered
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Measurability of the increasing Hermitian spectrum

The increasing ordered eigenvalues of a Hermitian matrix are Borel-measurable
functions of the matrix, coordinatewise and as a function-valued map.  These
statements are needed for the random spectral constructions of the paper; no
measurable eigenvector selection or simple-spectrum hypothesis is involved.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

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
/-- Coercion from the Hermitian subtype to the raw matrix is Borel
measurable. -/
theorem measurable_coe_hermitianMatrix :
    Measurable (Subtype.val : HermitianMatrix ι → Matrix ι ι ℂ) :=
  measurable_subtype_coe

/-- Every coordinate of the increasing ordered spectrum is continuous in the entrywise matrix
topology. The proof uses the `card ι * ε` entrywise perturbation bound (a Lipschitz bound) and
does not assume simple spectrum. -/
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

/-- The complete finite increasing ordered spectrum is Borel measurable as a
function-valued map. -/
theorem measurable_orderedSpectrum :
    Measurable (fun A : HermitianMatrix ι =>
      (fun i : Fin (Fintype.card ι) => orderedEigenvalue A i)) :=
  measurable_pi_iff.mpr fun i => measurable_orderedEigenvalue i

end OrderedSpectrum

end CoareaNative.BlockBand
