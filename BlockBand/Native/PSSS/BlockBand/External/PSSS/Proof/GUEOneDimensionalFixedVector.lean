module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEFixedCompressionConditionalTail

/-!
# One-dimensional canonical fixed-vector tail

The empty-compression case is proved directly from the scalar Gaussian law.
The positive-compression conditional estimate is also packaged as a proposition
ready for later almost-everywhere integration, without assuming that a random
compression is invertible.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set

/-- The canonical vector in the one-dimensional complex Euclidean space. -/
def canonicalUnitVectorOne : Fin 1 → ℂ := fun _ => 1

/-- Exact inverse-vector norm for a one-dimensional Hermitian matrix. -/
theorem norm_inv_mulVec_canonicalUnitVectorOne
    (H : Matrix (Fin 1) (Fin 1) ℂ) :
    ‖(WithLp.toLp 2 (H⁻¹ *ᵥ canonicalUnitVectorOne) :
        EuclideanSpace ℂ (Fin 1))‖ = ‖(H 0 0)⁻¹‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [canonicalUnitVectorOne, Matrix.mulVec, dotProduct]

/-- Unconditional canonical `N=1` fixed-vector inverse tail.  The normalized
GUE variance is exactly one and the absolute constant is `2`. -/
theorem canonicalGUE_one_fixedVector_inverse_tail
    (A : HermitianMatrix (Fin 1)) (t : ℝ) (ht : 1 ≤ t) :
    canonicalHermitianGUEPushforward 1 (canonicalGUEVariance 1)
      (canonicalGUEVariance_nonneg 1)
      {V | t ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
        canonicalUnitVectorOne) : EuclideanSpace ℂ (Fin 1))‖} ≤
      ENNReal.ofReal (2 / t) := by
  let P := canonicalHermitianGUEPushforward 1 (canonicalGUEVariance 1)
    (canonicalGUEVariance_nonneg 1)
  let f := matrixStandardizedFirstRow 0
  let c : ℝ := (A.1 0 0).re
  let E : Set (HermitianMatrix (Fin 1)) :=
    {V | t ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
      canonicalUnitVectorOne) : EuclideanSpace ℂ (Fin 1))‖}
  let I : Set (ConcreteFirstRowCoordinate 0 → ℝ) :=
    {u | |u (.inl ()) + c| ≤ 1 / t}
  have hsub : E ⊆ f ⁻¹' I := by
    intro V hV
    change t ≤ ‖(WithLp.toLp 2 ((A.1 + V.1)⁻¹ *ᵥ
      canonicalUnitVectorOne) : EuclideanSpace ℂ (Fin 1))‖ at hV
    rw [norm_inv_mulVec_canonicalUnitVectorOne] at hV
    have hrealA : (c : ℂ) = A.1 0 0 := by
      exact A.2.coe_re_apply_self 0
    have hrealV : ((V.1 0 0).re : ℂ) = V.1 0 0 := by
      exact V.2.coe_re_apply_self 0
    have hz : 0 < |c + (V.1 0 0).re| := by
      by_contra hn
      have hz0 : c + (V.1 0 0).re = 0 := abs_eq_zero.mp (le_antisymm
        (le_of_not_gt hn) (abs_nonneg _))
      have hentry : A.1 0 0 + V.1 0 0 = 0 := by
        rw [← hrealA, ← hrealV]
        exact_mod_cast hz0
      rw [Matrix.add_apply, hentry, _root_.inv_zero, norm_zero] at hV
      linarith
    have hnormInv :
        ‖(A.1 0 0 + V.1 0 0)⁻¹‖ =
          1 / |c + (V.1 0 0).re| := by
      rw [norm_inv, ← hrealA, ← hrealV]
      rw [← Complex.ofReal_add, Complex.norm_real]
      simp [Real.norm_eq_abs, div_eq_mul_inv]
    have hmul : t * |c + (V.1 0 0).re| ≤ 1 := by
      apply (le_div_iff₀ hz).mp
      rw [Matrix.add_apply, hnormInv] at hV
      exact hV
    have habs : |c + (V.1 0 0).re| ≤ 1 / t := by
      exact (le_div_iff₀ (by linarith : 0 < t)).2 (by
        simpa [mul_comm] using hmul)
    change |f V (.inl ()) + c| ≤ 1 / t
    simpa [f, matrixStandardizedFirstRow, add_comm] using habs
  have hscalar : MeasurableSet {x : ℝ | |x + c| ≤ 1 / t} := by
    apply measurableSet_le <;> fun_prop
  have hI : MeasurableSet I := by
    exact hscalar.preimage
      (measurePreserving_eval
        (fun _ : ConcreteFirstRowCoordinate 0 => gaussianReal 0 1)
        (.inl ())).measurable
  have hlaw : HasLaw f
      (Measure.pi fun _ : ConcreteFirstRowCoordinate 0 => gaussianReal 0 1) P := by
    simpa [f, P] using hasLaw_matrixStandardizedFirstRow 0
  calc
    P E ≤ P (f ⁻¹' I) := measure_mono hsub
    _ = (Measure.pi fun _ : ConcreteFirstRowCoordinate 0 => gaussianReal 0 1) I := by
      rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable hI]
    _ = gaussianReal 0 1 {x | |x + c| ≤ 1 / t} := by
      let e := measurePreserving_eval
        (fun _ : ConcreteFirstRowCoordinate 0 => gaussianReal 0 1) (.inl ())
      change (Measure.pi fun _ : ConcreteFirstRowCoordinate 0 =>
        gaussianReal 0 1)
          (Function.eval (.inl ()) ⁻¹' {x : ℝ | |x + c| ≤ 1 / t}) =
        gaussianReal 0 1 {x : ℝ | |x + c| ≤ 1 / t}
      exact e.measure_preimage hscalar.nullMeasurableSet
    _ ≤ ENNReal.ofReal (2 / t) := by
      simpa [sub_neg_eq_add, div_eq_mul_inv] using
        gaussianReal_smallInterval (-c) (1 / t) (by positivity)

end PSSSNative.BlockBand.PSSS
