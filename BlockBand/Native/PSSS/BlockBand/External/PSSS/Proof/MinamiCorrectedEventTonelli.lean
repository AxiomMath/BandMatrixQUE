module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedOpenGridFatou
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFullCompressionEndpointTransport

/-!
# Event-enriched Tonelli for the corrected Minami mesh

The kernel in this module retains the midpoint-inverse large-direction
event used in the finite-cell estimate.  It contains the fixed-target
predecessor on `Icc a b`, while the mesh itself covers only `Ioo (-xi) xi`.
The declarations below justify moving the sphere and selected-block variables
across `(e,t,xi)` and the finite mesh sum.  No sphere event of the regulated
resolvent itself is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Sphere direction, selected block, and the three analytic parameters. -/
abbrev CorrectedCellEventVariables {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :=
  (EuclideanSpace ℂ (Fin (dims j)) ×
    BlockProductDisintegration.SelectedSample dims j) × ((ℝ × ℝ) × ℝ)

/-- The auxiliary matrix viewed on the event-Tonelli variable space. -/
def correctedCellAuxiliary
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (p : CorrectedCellEventVariables dims j) :
    HermitianMatrix (Fin (dims j)) :=
  correctedSelectedAuxiliaryHermitian A₀ j heta
    ((((Gext, p.1.2), p.2.1.1), p.2.1.2), p.2.2)

/-- The inverse at the midpoint of one corrected mesh cell. -/
def correctedCellMidpointInverse
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M))
    (p : CorrectedCellEventVariables dims j) :
    Matrix (Fin (dims j)) (Fin (dims j)) ℂ :=
  ((correctedCellAuxiliary A₀ j heta Gext p).1 -
    (correctedMinamiCellMidpoint p.2.2 M n : ℂ) •
      (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹

/-- Occupancy indicator of one moving corrected cell. -/
def correctedCellOccupiedIndicator
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M))
    (p : CorrectedCellEventVariables dims j) : ℝ≥0∞ :=
  Set.indicator {_u : Unit |
      gridCellOccupied (correctedCellAuxiliary A₀ j heta Gext p)
        (-p.2.2) (correctedMinamiCellWidth p.2.2 M) n}
    (fun _ => (1 : ℝ≥0∞)) ()

/-- Generic midpoint-inverse large-image indicator. -/
def correctedCellLargeImageIndicator
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M))
    (p : CorrectedCellEventVariables dims j) : ℝ≥0∞ :=
  let Q := correctedCellMidpointInverse A₀ j heta Gext M n p
  Set.indicator {v : EuclideanSpace ℂ (Fin (dims j)) |
      ‖Q‖ / (10 * Real.sqrt (dims j)) ≤
        ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
          EuclideanSpace ℂ (Fin (dims j)))‖}
    (fun _ => (1 : ℝ≥0∞)) p.1.1

/-- A single normalized corrected mesh cell.  Both indicators are the
finite-mesh events: auxiliary cell occupancy and the generic midpoint-inverse
large-image event. -/
def correctedCellEventKernel
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (a b : ℝ) (M r : ℕ) (n : Fin (2 ^ M))
    (p : CorrectedCellEventVariables dims j) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight p.2.1.2) *
      correctedCellOccupiedIndicator A₀ j heta Gext M n p *
      correctedCellLargeImageIndicator A₀ j heta Gext M n p *
      fixedSelectedPredecessorWeight A₀ j p.1.1 a b r (Gext, p.1.2) *
      ENNReal.ofReal (poissonRadialWeight eta p.2.2)

/-- Joint measurability of occupancy of one moving corrected cell. -/
theorem measurableSet_correctedCellOccupied
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M)) :
    MeasurableSet {p : CorrectedCellEventVariables dims j |
      gridCellOccupied
        (correctedCellAuxiliary A₀ j heta Gext p)
        (-p.2.2) (correctedMinamiCellWidth p.2.2 M) n} := by
  have hH : Measurable (correctedCellAuxiliary A₀ j heta Gext) :=
    (measurable_correctedSelectedAuxiliaryHermitian dims A₀ j heta).comp (by fun_prop)
  unfold gridCellOccupied
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.inter
  · exact measurableSet_le
      (by
        unfold correctedMinamiCellWidth
        fun_prop)
      ((measurable_orderedEigenvalue i).comp hH)
  · exact measurableSet_lt
      ((measurable_orderedEigenvalue i).comp hH)
      (by
        unfold correctedMinamiCellWidth
        fun_prop)

/-- The moving midpoint inverse is jointly measurable. -/
theorem measurable_correctedCellMidpointInverse
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M)) :
    Measurable (correctedCellMidpointInverse A₀ j heta Gext M n) := by
  let H := correctedCellAuxiliary A₀ j heta Gext
  let c := fun p : CorrectedCellEventVariables dims j =>
    correctedMinamiCellMidpoint p.2.2 M n
  have hH : Measurable H :=
    (measurable_correctedSelectedAuxiliaryHermitian dims A₀ j heta).comp (by fun_prop)
  have hc : Measurable c := by
    unfold c correctedMinamiCellMidpoint correctedMinamiCellWidth
    fun_prop
  have hshift : Measurable (fun p : CorrectedCellEventVariables dims j =>
      (H p).1 - (c p : ℂ) •
        (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ)) := by
    rw [Matrix.measurable_iff]
    intro x y
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    exact ((Matrix.measurable_iff.mp (measurable_subtype_coe.comp hH) x y).sub
      ((Complex.continuous_ofReal.measurable.comp hc).mul measurable_const))
  exact Measurable.matrix_inv hshift

/-- The generic midpoint-inverse large-image indicator is measurable. -/
theorem measurable_correctedCellLargeImageIndicator
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M)) :
    Measurable (correctedCellLargeImageIndicator A₀ j heta Gext M n) := by
  let Q := correctedCellMidpointInverse A₀ j heta Gext M n
  have hQ : Measurable Q :=
    measurable_correctedCellMidpointInverse dims A₀ j heta Gext M n
  have hlarge : MeasurableSet {p : CorrectedCellEventVariables dims j |
      ‖Q p‖ / (10 * Real.sqrt (dims j)) ≤
        ‖(WithLp.toLp 2 (Q p *ᵥ WithLp.ofLp p.1.1) :
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
        ((measurable_pi_apply (X := fun _ : Fin (dims j) => ℂ) y).comp
          ((WithLp.measurable_ofLp 2 _).comp
            (measurable_fst.comp measurable_fst)))
  unfold correctedCellLargeImageIndicator
  exact (measurable_const.indicator hlarge).comp measurable_id

/-- The occupancy indicator is measurable. -/
theorem measurable_correctedCellOccupiedIndicator
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (M : ℕ) (n : Fin (2 ^ M)) :
    Measurable (correctedCellOccupiedIndicator A₀ j heta Gext M n) := by
  unfold correctedCellOccupiedIndicator
  exact measurable_const.indicator
    (measurableSet_correctedCellOccupied dims A₀ j heta Gext M n)

/-- The corrected fixed-target predecessor pulled back to the event space is
jointly measurable in the sphere and selected sample variables. -/
theorem measurable_correctedCellFixedPredecessor
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (a b : ℝ) (r : ℕ) :
    Measurable (fun p : CorrectedCellEventVariables dims j =>
      fixedSelectedPredecessorWeight A₀ j p.1.1 a b r (Gext, p.1.2)) := by
  let pull := fun p : CorrectedCellEventVariables dims j =>
    (p.1.1, (Gext, p.1.2))
  have hpull : Measurable pull :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_const.prodMk (measurable_snd.comp measurable_fst))
  have h := (measurable_joint_fixedSelectedPredecessorWeight
    dims A₀ j a b r).comp hpull
  change Measurable ((fun q : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      fixedSelectedPredecessorWeight A₀ j q.1 a b r q.2) ∘ pull)
  exact h

/-- Joint measurability of one normalized event cell. -/
theorem measurable_correctedCellEventKernel
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (a b : ℝ) (M r : ℕ) (n : Fin (2 ^ M)) :
    Measurable (correctedCellEventKernel A₀ j heta Gext a b M r n) := by
  have hocc := measurable_correctedCellOccupiedIndicator
    dims A₀ j heta Gext M n
  have hlarge := measurable_correctedCellLargeImageIndicator
    dims A₀ j heta Gext M n
  have hW : Measurable (fun p : CorrectedCellEventVariables dims j =>
      fixedSelectedPredecessorWeight A₀ j p.1.1 a b r (Gext, p.1.2)) :=
    measurable_correctedCellFixedPredecessor dims A₀ j Gext a b r
  have hcauchy : Measurable (fun p : CorrectedCellEventVariables dims j =>
      ENNReal.ofReal (standardCauchyWeight p.2.1.2)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold standardCauchyWeight
    fun_prop (discharger := intro x; positivity)
  have hradial : Measurable (fun p : CorrectedCellEventVariables dims j =>
      ENNReal.ofReal (poissonRadialWeight eta p.2.2)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold poissonRadialWeight
    fun_prop
  let f0 := fun p : CorrectedCellEventVariables dims j =>
    ENNReal.ofReal (1 / Real.pi) *
      ENNReal.ofReal (standardCauchyWeight p.2.1.2)
  let f1 := fun p : CorrectedCellEventVariables dims j =>
    f0 p * correctedCellOccupiedIndicator A₀ j heta Gext M n p
  let f2 := fun p : CorrectedCellEventVariables dims j =>
    f1 p * correctedCellLargeImageIndicator A₀ j heta Gext M n p
  let f3 := fun p : CorrectedCellEventVariables dims j =>
    f2 p * fixedSelectedPredecessorWeight A₀ j p.1.1 a b r (Gext, p.1.2)
  let f4 := fun p : CorrectedCellEventVariables dims j =>
    f3 p * ENNReal.ofReal (poissonRadialWeight eta p.2.2)
  have hf0 : Measurable f0 := measurable_const.mul hcauchy
  have hf1 : Measurable f1 := hf0.mul hocc
  have hf2 : Measurable f2 := hf1.mul hlarge
  have hf3 : Measurable f3 := hf2.mul hW
  have hf4 : Measurable f4 := hf3.mul hradial
  change Measurable (fun p : CorrectedCellEventVariables dims j =>
    ENNReal.ofReal (1 / Real.pi) *
      ENNReal.ofReal (standardCauchyWeight p.2.1.2) *
      correctedCellOccupiedIndicator A₀ j heta Gext M n p *
      correctedCellLargeImageIndicator A₀ j heta Gext M n p *
      fixedSelectedPredecessorWeight A₀ j p.1.1 a b r (Gext, p.1.2) *
      ENNReal.ofReal (poissonRadialWeight eta p.2.2))
  exact hf4

/-- Sum over all corrected cells at one mesh resolution. -/
def correctedMeshEventKernel
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (a b : ℝ) (M r : ℕ) (p : CorrectedCellEventVariables dims j) : ℝ≥0∞ :=
  ∑ n : Fin (2 ^ M), correctedCellEventKernel A₀ j heta Gext a b M r n p

/-- The finite event-enriched mesh sum is jointly measurable. -/
theorem measurable_correctedMeshEventKernel
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (a b : ℝ) (M r : ℕ) :
    Measurable (correctedMeshEventKernel A₀ j heta Gext a b M r) := by
  unfold correctedMeshEventKernel
  apply Finset.measurable_sum
  intro n hn
  exact measurable_correctedCellEventKernel dims A₀ j heta Gext a b M r n

/-- Expand the sphere/selected-block product for fixed analytic parameters. -/
theorem lintegral_correctedMeshEvent_sampleProduct_eq_nested
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (a b : ℝ) (M r : ℕ) (q : (ℝ × ℝ) × ℝ) :
    (∫⁻ s, correctedMeshEventKernel A₀ j heta Gext a b M r (s, q)
      ∂(uniformSphere (dims j)).prod
        (BlockProductDisintegration.selectedMeasure dims hd j)) =
      ∫⁻ φ, ∫⁻ Gj,
        correctedMeshEventKernel A₀ j heta Gext a b M r ((φ, Gj), q)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j) := by
  let f := fun s : EuclideanSpace ℂ (Fin (dims j)) ×
      BlockProductDisintegration.SelectedSample dims j =>
    correctedMeshEventKernel A₀ j heta Gext a b M r (s, q)
  have hf : Measurable f :=
    (measurable_correctedMeshEventKernel
      dims A₀ j heta Gext a b M r).comp (measurable_id.prodMk measurable_const)
  exact MeasureTheory.lintegral_prod f hf.aemeasurable

end PSSSNative.BlockBand.PSSS
