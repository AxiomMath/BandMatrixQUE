module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedGlobalSuccessor

/-!
# Joint measurability for the corrected global Minami mesh

The exterior sample is kept as a measurable variable.  These results
supply the measurability hypotheses for moving the single corrected-mesh liminf
through the exterior and analytic-parameter integrals.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 12000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Exterior sample together with sphere/selected sample and analytic
parameters. -/
abbrev CorrectedGlobalEventVariables {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :=
  BlockProductDisintegration.ExteriorSample dims j ×
    CorrectedCellEventVariables dims j

/-- The corrected auxiliary Hermitian matrix is jointly measurable in the
exterior, selected, and all three analytic variables (the sphere coordinate
is ignored). -/
theorem measurable_correctedGlobalAuxiliary
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) :
    Measurable (fun p : CorrectedGlobalEventVariables dims j =>
      correctedCellAuxiliary A₀ j heta p.1 p.2) := by
  exact (measurable_correctedSelectedAuxiliaryHermitian dims A₀ j heta).comp
    (by fun_prop)

/-- Joint measurability of a corrected cell occupancy indicator, without
freezing the exterior sample. -/
theorem measurable_correctedGlobalCellOccupiedIndicator
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (M : ℕ) (n : Fin (2 ^ M)) :
    Measurable (fun p : CorrectedGlobalEventVariables dims j =>
      correctedCellOccupiedIndicator A₀ j heta p.1 M n p.2) := by
  have hH := measurable_correctedGlobalAuxiliary dims A₀ j heta
  have hs : MeasurableSet {p : CorrectedGlobalEventVariables dims j |
      gridCellOccupied (correctedCellAuxiliary A₀ j heta p.1 p.2)
        (-p.2.2.2) (correctedMinamiCellWidth p.2.2.2 M) n} := by
    unfold gridCellOccupied
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.inter
    · exact measurableSet_le (by unfold correctedMinamiCellWidth; fun_prop)
        ((measurable_orderedEigenvalue i).comp hH)
    · exact measurableSet_lt ((measurable_orderedEigenvalue i).comp hH)
        (by unfold correctedMinamiCellWidth; fun_prop)
  unfold correctedCellOccupiedIndicator
  exact Measurable.indicator measurable_const hs

/-- The generic midpoint inverse is jointly measurable with the exterior
sample variable. -/
theorem measurable_correctedGlobalCellMidpointInverse
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (M : ℕ) (n : Fin (2 ^ M)) :
    Measurable (fun p : CorrectedGlobalEventVariables dims j =>
      correctedCellMidpointInverse A₀ j heta p.1 M n p.2) := by
  let H := fun p : CorrectedGlobalEventVariables dims j =>
    correctedCellAuxiliary A₀ j heta p.1 p.2
  let c := fun p : CorrectedGlobalEventVariables dims j =>
    correctedMinamiCellMidpoint p.2.2.2 M n
  have hH : Measurable H := measurable_correctedGlobalAuxiliary dims A₀ j heta
  have hc : Measurable c := by
    unfold c correctedMinamiCellMidpoint correctedMinamiCellWidth
    fun_prop
  have hshift : Measurable (fun p : CorrectedGlobalEventVariables dims j =>
      (H p).1 - (c p : ℂ) •
        (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ)) := by
    rw [Matrix.measurable_iff]
    intro x y
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    exact ((Matrix.measurable_iff.mp (measurable_subtype_coe.comp hH) x y).sub
      ((Complex.continuous_ofReal.measurable.comp hc).mul measurable_const))
  exact Measurable.matrix_inv hshift

/-- Joint measurability of the generic midpoint large-image indicator. -/
theorem measurable_correctedGlobalCellLargeImageIndicator
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (M : ℕ) (n : Fin (2 ^ M)) :
    Measurable (fun p : CorrectedGlobalEventVariables dims j =>
      correctedCellLargeImageIndicator A₀ j heta p.1 M n p.2) := by
  let Q := fun p : CorrectedGlobalEventVariables dims j =>
    correctedCellMidpointInverse A₀ j heta p.1 M n p.2
  have hQ : Measurable Q :=
    measurable_correctedGlobalCellMidpointInverse dims A₀ j heta M n
  have hs : MeasurableSet {p : CorrectedGlobalEventVariables dims j |
      ‖Q p‖ / (10 * Real.sqrt (dims j)) ≤
        ‖(WithLp.toLp 2 (Q p *ᵥ WithLp.ofLp p.2.1.1) :
          EuclideanSpace ℂ (Fin (dims j)))‖} := by
    apply measurableSet_le
    · exact (measurable_norm.comp hQ).div_const _
    · apply measurable_norm.comp
      apply (WithLp.measurable_toLp 2 _).comp
      rw [measurable_pi_iff]
      intro x
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.measurable_sum
      intro y hy
      exact (Matrix.measurable_iff.mp hQ x y).mul
        ((measurable_pi_apply y).comp
          ((WithLp.measurable_ofLp 2 _).comp
            (measurable_fst.comp (measurable_fst.comp measurable_snd))))
  unfold correctedCellLargeImageIndicator
  exact Measurable.indicator measurable_const hs

end PSSSNative.BlockBand.PSSS
