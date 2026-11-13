module

public import BlockBand.Prelude

/-!
# The full current contraction

The signed current `J = P' - P` of two projections, its traces against the near and far
projections (`∓` the conductance), and the source/current contraction `-D₀ g Tr(QJ)/2`.
-/

@[expose] public section

noncomputable section

namespace BlockBand.SourceProcess

open Matrix

/-- Full signed current, independent of any source normalization. -/
def fullCurrent {ι : Type*} (P P' : Matrix ι ι ℂ) : Matrix ι ι ℂ := P' - P

/-- Complex trace form of the physical conductance; real for Hermitian pairs. -/
def currentConductance {ι : Type*} [Fintype ι] (P P' : Matrix ι ι ℂ) : ℂ :=
  ((fullCurrent P P') * (fullCurrent P P')).trace / 2

/-- Equal-rank projections have zero current trace. -/
theorem fullCurrent_trace_zero {ι : Type*} [Fintype ι]
    (P P' : Matrix ι ι ℂ) (hrank : P'.trace = P.trace) :
    (fullCurrent P P').trace = 0 := by
  simp [fullCurrent, Matrix.trace_sub, hrank]

/-- The current-near-projection trace is minus the physical conductance. -/
theorem fullCurrent_near_trace {ι : Type*} [Fintype ι]
    (P P' : Matrix ι ι ℂ) (hP : P * P = P) (hP' : P' * P' = P')
    (hrank : P'.trace = P.trace) :
    (fullCurrent P P' * P).trace = -currentConductance P P' := by
  simp only [fullCurrent, currentConductance, sub_mul, mul_sub, Matrix.trace_sub,
    hP, hP', hrank]
  rw [Matrix.trace_mul_comm P P']
  ring

/-- The current-far-projection trace is plus the physical conductance. -/
theorem fullCurrent_far_trace {ι : Type*} [Fintype ι]
    (P P' : Matrix ι ι ℂ) (hP : P * P = P) (hP' : P' * P' = P')
    (hrank : P'.trace = P.trace) :
    (fullCurrent P P' * P').trace = currentConductance P P' := by
  have hn := fullCurrent_near_trace P P' hP hP' hrank
  have hs : (fullCurrent P P' * P').trace - (fullCurrent P P' * P).trace =
      2 * currentConductance P P' := by
    simp only [currentConductance]
    rw [← Matrix.trace_sub, ← mul_sub]
    change (fullCurrent P P' * fullCurrent P P').trace =
      2 * ((fullCurrent P P' * fullCurrent P P').trace / 2)
    ring
  linear_combination hs + hn

/-- The opposite-sign source/current contraction gives `-D₀ g Tr(QJ)/2`. -/
theorem source_current_contraction {ι : Type*} [Fintype ι]
    (P P' Q : Matrix ι ι ℂ) (D : ℂ)
    (hP : P * P = P) (hP' : P' * P' = P') (hrank : P'.trace = P.trace) :
    D / 2 * ((Q * P).trace * (fullCurrent P P' * P').trace +
      (Q * P').trace * (fullCurrent P P' * P).trace) =
        -(D / 2 * currentConductance P P') * (Q * fullCurrent P P').trace := by
  rw [fullCurrent_near_trace P P' hP hP' hrank,
    fullCurrent_far_trace P P' hP hP' hrank]
  simp only [fullCurrent, mul_sub, Matrix.trace_sub]
  ring

end BlockBand.SourceProcess
