module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEUnitaryTransport

/-!
# Public canonical GUE law for the PSSS interface

`GUE d t` is the law of a `d × d` Hermitian matrix with independent Gaussian coordinates: diagonal
entries of variance `t` and real and imaginary parts of the strictly upper entries of variance
`t/2` (negative `t` is replaced by `0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open MeasureTheory ProbabilityTheory

/-- At nonnegative `t` this is the pushforward of the independent Hermitian
coordinate product with diagonal variance `t` and strict-upper real/imaginary
variance `t/2`. For `t > 0` its density is `Z_d(t)⁻¹ exp (-Tr(A²)/(2t)) dA`, with the GUE
normalizing constant `Z_d(t)`. -/
def GUE (d : ℕ) (t : ℝ) : ProbabilityMeasure (HermitianMatrix (Fin d)) :=
  ⟨PSSS.canonicalHermitianGUEPushforward d (max t 0) (le_max_right t 0), by
    unfold PSSS.canonicalHermitianGUEPushforward
    infer_instance⟩

/-- For `t ≥ 0`, the public law is the canonical Hermitian coordinate-GUE pushforward. -/
theorem GUE_toMeasure_eq_canonicalHermitianGUEPushforward
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (GUE d t : Measure (HermitianMatrix (Fin d))) =
      PSSS.canonicalHermitianGUEPushforward d t ht := by
  simp [GUE, max_eq_left ht]

/-- The reconstruction map used to define the public GUE law is Borel
measurable. -/
theorem measurable_GUE_reconstruction (d : ℕ) :
    Measurable (hermitianGUEBlock d) :=
  measurable_hermitianGUEBlock d

/-- The canonical independent-coordinate sample has the public GUE law at
nonnegative variance. -/
theorem hasLaw_hermitianGUEBlock_GUE (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasLaw (hermitianGUEBlock d) (GUE d t)
      (hermitianGUECoordinateMeasure d t ht) := by
  refine ⟨(measurable_GUE_reconstruction d).aemeasurable, ?_⟩
  rw [GUE_toMeasure_eq_canonicalHermitianGUEPushforward d t ht]
  rfl

/-- Law equality in the `Measure.map` form used by PSSS consumers. -/
theorem map_hermitianGUEBlock_eq_GUE (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht) =
      (GUE d t : Measure (HermitianMatrix (Fin d))) :=
  (hasLaw_hermitianGUEBlock_GUE d t ht).map_eq

end PSSSNative.BlockBand
