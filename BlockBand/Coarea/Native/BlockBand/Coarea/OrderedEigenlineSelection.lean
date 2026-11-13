module

public import BlockBand.Coarea.Native.BlockBand.Coarea.OrderedProjectionMeasurable
public import Mathlib.Data.Finset.Max

/-!
# Measurable least-chart ordered eigenlines

For each ordered eigenvalue on the simple-spectrum locus, the rank-one
Lagrange projector has a nonzero entry.  This module orders the finite set of
entry charts lexicographically, selects the least available chart, and uses
the phase-fixed affine reconstruction to obtain a measurable unit
eigenvector.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

abbrev OrderedEigenlineChartIndex (d : ℕ) := Lex (Fin d × Fin d)

local instance (d : ℕ) : MeasurableSpace (OrderedEigenlineChartIndex d) := ⊤

/-- Available nonzero-entry charts at a simple-spectrum coordinate point. -/
def availableOrderedEigenlineCharts (d : ℕ) (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    Finset (OrderedEigenlineChartIndex d) := by
  classical
  exact Finset.univ.filter fun p =>
    x.1 ∈ hermitianLagrangeProjectorChartSource d r (ofLex p).1 (ofLex p).2

theorem availableOrderedEigenlineCharts_nonempty
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    (availableOrderedEigenlineCharts d r x).Nonempty := by
  obtain ⟨i, j, hij⟩ :=
    exists_simple_Lagrange_chart (hermitianLagrangeFunctionalCalculus d) r x
  exact ⟨toLex (i, j), by
    simp [availableOrderedEigenlineCharts, hij]⟩

/-- The lexicographically least nonzero projector-entry chart. -/
def leastOrderedEigenlineChart (d : ℕ) (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    OrderedEigenlineChartIndex d :=
  (availableOrderedEigenlineCharts d r x).min'
    (availableOrderedEigenlineCharts_nonempty r x)

theorem leastOrderedEigenlineChart_mem
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    x.1 ∈ hermitianLagrangeProjectorChartSource d r
      (ofLex (leastOrderedEigenlineChart d r x)).1
      (ofLex (leastOrderedEigenlineChart d r x)).2 := by
  have h := Finset.min'_mem (availableOrderedEigenlineCharts d r x)
    (availableOrderedEigenlineCharts_nonempty r x)
  simpa [leastOrderedEigenlineChart, availableOrderedEigenlineCharts] using h

/-- The measurable region on which a fixed entry chart is the least
nonzero-entry chart. -/
def leastOrderedEigenlineChartRegion (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Set (hermitianSimpleSpectrumCoordinates d) :=
  {x | x.1 ∈ hermitianLagrangeProjectorChartSource d r (ofLex p).1 (ofLex p).2 ∧
    ∀ q : OrderedEigenlineChartIndex d, q < p →
      x.1 ∉ hermitianLagrangeProjectorChartSource d r (ofLex q).1 (ofLex q).2}

theorem measurableSet_leastOrderedEigenlineChartRegion
    (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (leastOrderedEigenlineChartRegion d r p) := by
  have hp : MeasurableSet {x : hermitianSimpleSpectrumCoordinates d |
      x.1 ∈ hermitianLagrangeProjectorChartSource d r (ofLex p).1 (ofLex p).2} :=
    (measurableSet_hermitianLagrangeProjectorChartSource d r (ofLex p).1 (ofLex p).2).preimage
      measurable_subtype_coe
  have hq : MeasurableSet {x : hermitianSimpleSpectrumCoordinates d |
      ∀ q : OrderedEigenlineChartIndex d, q < p →
        x.1 ∉ hermitianLagrangeProjectorChartSource d r (ofLex q).1 (ofLex q).2} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro hqp
    exact (measurableSet_hermitianLagrangeProjectorChartSource
      d r (ofLex q).1 (ofLex q).2).preimage measurable_subtype_coe |>.compl
  exact hp.inter hq

theorem leastOrderedEigenlineChart_eq_iff
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (p : OrderedEigenlineChartIndex d) :
    leastOrderedEigenlineChart d r x = p ↔
      x ∈ leastOrderedEigenlineChartRegion d r p := by
  rw [leastOrderedEigenlineChart, Finset.min'_eq_iff]
  simp only [leastOrderedEigenlineChartRegion, Set.mem_ofPred_eq,
    availableOrderedEigenlineCharts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hleast⟩
    refine ⟨hp, ?_⟩
    intro q hqp hq
    exact (not_le_of_gt hqp) (hleast q (by simp [hq]))
  · rintro ⟨hp, hmin⟩
    refine ⟨hp, ?_⟩
    intro q hq
    by_contra h
    exact hmin q (lt_of_not_ge h) (by simpa using hq)

/-- The least-chart index is measurable because its finitely many fibers are
the measurable least-chart regions above. -/
theorem measurable_leastOrderedEigenlineChart
    (d : ℕ) (r : HermitianEigenRank d) :
    Measurable (leastOrderedEigenlineChart d r) := by
  apply measurable_to_countable'
  intro p
  rw [show leastOrderedEigenlineChart d r ⁻¹' {p} =
      leastOrderedEigenlineChartRegion d r p by
    ext x
    simp [leastOrderedEigenlineChart_eq_iff]]
  exact measurableSet_leastOrderedEigenlineChartRegion d r p

/-- Total version of a fixed phase chart; division is total in `ℂ`, while the
least-chart construction only evaluates it where the distinguished entry is
nonzero. -/
def orderedEigenlineChartCandidate (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) : EuclideanSpace ℂ (Fin d) :=
  projectiveUnitReconstruction (ofLex p).1
    (projectiveEigenvectorChart (ofLex p).1
      (hermitianLagrangeProjectorColumn d r (ofLex p).2 x.1))

theorem measurable_orderedEigenlineChartCandidate
    (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Measurable (orderedEigenlineChartCandidate d r p) := by
  apply (measurable_projectiveUnitReconstruction (ofLex p).1).comp
  rw [measurable_pi_iff]
  intro q
  have hP : Measurable (fun x : hermitianSimpleSpectrumCoordinates d =>
      hermitianLagrangeSpectralProjector d r x.1) :=
    (measurable_hermitianLagrangeSpectralProjector d r).comp
      measurable_subtype_coe
  exact (hP.eval_matrix.div hP.eval_matrix)

/-- Global phase-fixed ordered eigenline, assembled from the finite measurable
least-chart partition. -/
def orderedEigenlineSelection (d : ℕ) (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) : EuclideanSpace ℂ (Fin d) :=
  ∑ p : OrderedEigenlineChartIndex d,
    if leastOrderedEigenlineChart d r x = p then
      orderedEigenlineChartCandidate d r p x else 0

theorem measurable_orderedEigenlineSelection
    (d : ℕ) (r : HermitianEigenRank d) :
    Measurable (orderedEigenlineSelection d r) := by
  classical
  unfold orderedEigenlineSelection
  apply Finset.measurable_sum
  intro p hp
  have hregion :
      MeasurableSet {x : hermitianSimpleSpectrumCoordinates d |
        leastOrderedEigenlineChart d r x = p} := by
    rw [show {x : hermitianSimpleSpectrumCoordinates d |
        leastOrderedEigenlineChart d r x = p} =
        leastOrderedEigenlineChartRegion d r p by
      ext x
      exact leastOrderedEigenlineChart_eq_iff r x p]
    exact measurableSet_leastOrderedEigenlineChartRegion d r p
  exact (measurable_orderedEigenlineChartCandidate d r p).piecewise
    hregion measurable_const

theorem orderedEigenlineSelection_eq_candidate
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    orderedEigenlineSelection d r x =
      orderedEigenlineChartCandidate d r
        (leastOrderedEigenlineChart d r x) x := by
  classical
  rw [orderedEigenlineSelection, Fintype.sum_eq_single
    (leastOrderedEigenlineChart d r x)]
  · simp
  · intro p hp
    simp [Ne.symm hp]

/-- The selected vector is normalized. -/
@[simp] theorem norm_orderedEigenlineSelection
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    ‖orderedEigenlineSelection d r x‖ = 1 := by
  rw [orderedEigenlineSelection_eq_candidate]
  exact norm_projectiveUnitReconstruction _ _

/-- The lexicographically selected chart fixes the phase by requiring its
distinguished coordinate to be strictly positive real. -/
theorem orderedEigenlineSelection_selectedCoordinate_re_pos
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    0 < (orderedEigenlineSelection d r x
      (ofLex (leastOrderedEigenlineChart d r x)).1).re := by
  rw [orderedEigenlineSelection_eq_candidate]
  exact projectiveUnitReconstruction_self_re_pos _ _

/-- The selected vector satisfies the ordered Hermitian eigenvector equation. -/
theorem orderedEigenlineSelection_eigenvector
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    ((hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ).mulVec
      (orderedEigenlineSelection d r x)) =
    ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ) •
      orderedEigenlineSelection d r x := by
  rw [orderedEigenlineSelection_eq_candidate]
  let p := leastOrderedEigenlineChart d r x
  have hp := leastOrderedEigenlineChart_mem r x
  change
    ((hermitianOfFinCoordinates d x.1 : Matrix (Fin d) (Fin d) ℂ).mulVec
      (phaseFixedLagrangeProjectorColumn d r (ofLex p).1 (ofLex p).2
        ⟨x.1, hp⟩)) =
    ((orderedEigenvalue (hermitianOfFinCoordinates d x.1) r : ℝ) : ℂ) •
      phaseFixedLagrangeProjectorColumn d r (ofLex p).1 (ofLex p).2
        ⟨x.1, hp⟩
  exact phaseFixedLagrangeProjectorColumn_eigenvector
    ⟨x.1, hp⟩
    (hermitianLagrangeProjectorCorrect_of_separable x.1 x.2 r)

/-- The exact ordered Lagrange projection fixes the selected unit vector. -/
theorem orderedEigenlineSelection_projector
    {d : ℕ} (r : HermitianEigenRank d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    (hermitianLagrangeSpectralProjector d r x.1).mulVec
      (orderedEigenlineSelection d r x) =
      orderedEigenlineSelection d r x := by
  rw [orderedEigenlineSelection_eq_candidate]
  let p := leastOrderedEigenlineChart d r x
  have hp := leastOrderedEigenlineChart_mem r x
  let P := hermitianLagrangeSpectralProjector d r x.1
  let v := hermitianLagrangeProjectorColumn d r (ofLex p).2 x.1
  let a : ℂ :=
    ((‖projectiveAffineRepresentative (ofLex p).1 v‖⁻¹ : ℝ) : ℂ) *
      (v (ofLex p).1)⁻¹
  have hv : v (ofLex p).1 ≠ 0 := by
    simpa [v, hermitianLagrangeProjectorColumn,
      hermitianLagrangeProjectorChartSource] using hp
  have hphase :
      orderedEigenlineChartCandidate d r p x = a • v := by
    rw [orderedEigenlineChartCandidate, projectiveUnitReconstruction,
      projectiveEigenvectorReconstruction_chart (ofLex p).1 _ hv,
      projectiveAffineRepresentative]
    apply PiLp.ext
    intro q
    simp [a, v, projectiveAffineRepresentative, mul_assoc]
  rw [hphase]
  change P.mulVec (a • v.ofLp) = a • v.ofLp
  rw [Matrix.mulVec_smul]
  have hcorrect :=
    hermitianLagrangeProjectorCorrect_of_separable x.1 x.2 r
  have hcol : P.mulVec v.ofLp = v.ofLp := by
    funext i
    have hij := congrArg
      (fun M : Matrix (Fin d) (Fin d) ℂ => M i (ofLex p).2)
      hcorrect.idempotent
    change (P * P) i (ofLex p).2 = P i (ofLex p).2 at hij
    change (∑ k, P i k * P k (ofLex p).2) = P i (ofLex p).2
    simpa [Matrix.mul_apply] using hij
  rw [hcol]

end CoareaNative.BlockBand
