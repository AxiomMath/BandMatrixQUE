module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairCoareaAssembly

/-!
# Explicit phase-fixed Householder completion

For a unit vector `v` whose distinguished coordinate is positive real, the
reflection

`H(v) = -I + (v + e)(v + e)ᴴ / (1 + vᵢ)`

is nonsingular on the entire phase-fixed affine chart and sends the distinguished
coordinate vector `e` to `v`.  Unlike the usual `v - e` Householder formula, this
choice has denominator `1 + vᵢ`, so it has no singularity at `v = e`.

This module constructs that frame explicitly, proves its chart-column identity
and regularity, and specializes it to the measurable ordered eigenline selection.
Unitarity is stated as the elementary finite-sum identity
`PhaseFixedHouseholderUnitaryIdentity`, a hypothesis of the unitarity results here; it is
proved as `phaseFixedHouseholderUnitaryIdentity`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix Set

/-- The standard coordinate vector at `i`. -/
def phaseFixedCoordinateVector {ι : Type*} [DecidableEq ι]
    (i : ι) : ι → ℂ := Pi.single i 1

/-- The vector `v + eᵢ` used by the nonsingular phase-fixed Householder formula. -/
def phaseFixedHouseholderShift {ι : Type*} [DecidableEq ι]
    (i : ι) (v : ι → ℂ) : ι → ℂ :=
  v + phaseFixedCoordinateVector i

/-- Explicit Householder completion on the positive-real phase chart.

The definition is total; the chart hypotheses below guarantee that the real
denominator is positive. -/
def phaseFixedHouseholderFrame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℂ) : Matrix ι ι ℂ :=
  -(1 : Matrix ι ι ℂ) +
    (((1 + (v i).re)⁻¹ : ℝ) : ℂ) •
      Matrix.vecMulVec (phaseFixedHouseholderShift i v)
        (star (phaseFixedHouseholderShift i v))

/-- On the phase chart the Householder denominator is strictly positive. -/
theorem phaseFixedHouseholder_denominator_pos
    {ι : Type*} (i : ι) (v : ι → ℂ) (hvi : 0 < (v i).re) :
    0 < 1 + (v i).re := by
  linarith

/-- Entrywise formula for the explicit completion. -/
theorem phaseFixedHouseholderFrame_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i a b : ι) (v : ι → ℂ) :
    phaseFixedHouseholderFrame i v a b =
      -(if a = b then 1 else 0) +
        (((1 + (v i).re)⁻¹ : ℝ) : ℂ) *
          phaseFixedHouseholderShift i v a *
          star (phaseFixedHouseholderShift i v b) := by
  simp [phaseFixedHouseholderFrame, Matrix.one_apply,
    Matrix.vecMulVec_apply, mul_assoc]

/-- The explicit frame sends the distinguished coordinate vector to `v`.
This is the key local completion identity and uses only that `vᵢ` is real and
`1 + vᵢ` is nonzero. -/
theorem phaseFixedHouseholderFrame_mulVec_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℂ)
    (hreal : v i = ((v i).re : ℂ)) (hden : 1 + (v i).re ≠ 0) :
    (phaseFixedHouseholderFrame i v).mulVec
      (phaseFixedCoordinateVector i) = v := by
  let a : ℝ := (v i).re
  have hva : v i = (a : ℂ) := hreal
  have ha : 1 + a ≠ 0 := hden
  rw [phaseFixedCoordinateVector, Matrix.mulVec_single_one]
  funext j
  change phaseFixedHouseholderFrame i v j i = v j
  rw [phaseFixedHouseholderFrame_apply]
  have hshift_i :
      phaseFixedHouseholderShift i v i =
        (((1 + a : ℝ)) : ℂ) := by
    rw [phaseFixedHouseholderShift]
    change v i + phaseFixedCoordinateVector i i =
      (((1 + a : ℝ)) : ℂ)
    rw [hva]
    simp only [phaseFixedCoordinateVector, Pi.single_eq_same]
    push_cast
    ring
  by_cases hji : j = i
  · subst j
    rw [show (if i = i then (1 : ℂ) else 0) = 1 by simp, hshift_i, hva]
    change -(1 : ℂ) + (↑((1 + a)⁻¹) : ℂ) *
      (↑(1 + a) : ℂ) * star (↑(1 + a) : ℂ) = (a : ℂ)
    rw [show star (↑(1 + a) : ℂ) = (↑(1 + a) : ℂ) by simp]
    rw [show (↑((1 + a)⁻¹) : ℂ) * (↑(1 + a) : ℂ) = 1 by
      norm_cast
      exact inv_mul_cancel₀ ha]
    push_cast
    ring
  · have hshift_j : phaseFixedHouseholderShift i v j = v j := by
      rw [phaseFixedHouseholderShift]
      change v j + phaseFixedCoordinateVector i j = v j
      rw [phaseFixedCoordinateVector, Pi.single_eq_of_ne hji]
      exact add_zero _
    rw [show (if j = i then (1 : ℂ) else 0) = 0 by
      simp only [hji, ↓reduceIte], hshift_j, hshift_i]
    change -(0 : ℂ) + (↑((1 + a)⁻¹) : ℂ) *
      v j * star (↑(1 + a) : ℂ) = v j
    rw [show star (↑(1 + a) : ℂ) = (↑(1 + a) : ℂ) by simp]
    calc
      -(0 : ℂ) + (↑((1 + a)⁻¹) : ℂ) *
          v j * (↑(1 + a) : ℂ) =
          ((↑((1 + a)⁻¹) : ℂ) * (↑(1 + a) : ℂ)) * v j := by ring
      _ = v j := by
        rw [show (↑((1 + a)⁻¹) : ℂ) * (↑(1 + a) : ℂ) = 1 by
          norm_cast
          exact inv_mul_cancel₀ ha]
        exact one_mul _

/-- The Householder frame depends continuously on `v` wherever its denominator
is nonzero. -/
theorem continuousAt_phaseFixedHouseholderFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hden : 1 + (v i).re ≠ 0) :
    ContinuousAt (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w) v := by
  change ContinuousAt (fun w : EuclideanSpace ℂ ι =>
    fun a b => phaseFixedHouseholderFrame i w a b) v
  rw [continuousAt_pi]
  intro a
  rw [continuousAt_pi]
  intro b
  rw [show (fun w : EuclideanSpace ℂ ι =>
      phaseFixedHouseholderFrame i w a b) =
      fun w : EuclideanSpace ℂ ι => -(if a = b then 1 else 0) +
        (((1 + (w i).re)⁻¹ : ℝ) : ℂ) *
          phaseFixedHouseholderShift i w a *
          star (phaseFixedHouseholderShift i w b) by
    funext w
    exact phaseFixedHouseholderFrame_apply i a b w]
  have heval (k : ι) :
      Continuous (fun w : EuclideanSpace ℂ ι => w k) := by
    exact (continuous_apply k).comp
      (PiLp.continuous_ofLp 2 (fun _ : ι => ℂ))
  have hre : ContinuousAt
      (fun w : EuclideanSpace ℂ ι => (w i).re) v :=
    Complex.continuous_re.continuousAt.comp' (heval i).continuousAt
  have hcoeff : ContinuousAt
      (fun w : EuclideanSpace ℂ ι =>
        (((1 + (w i).re)⁻¹ : ℝ) : ℂ)) v := by
    exact Complex.continuous_ofReal.continuousAt.comp'
      ((continuousAt_const.add hre).inv₀ hden)
  have hshift (k : ι) : ContinuousAt
      (fun w : EuclideanSpace ℂ ι =>
        phaseFixedHouseholderShift i w k) v := by
    change ContinuousAt
      (fun w : EuclideanSpace ℂ ι =>
        w k + phaseFixedCoordinateVector i k) v
    exact (heval k).continuousAt.add continuousAt_const
  exact (continuousAt_const.add
    ((hcoeff.mul (hshift a)).mul (hshift b).star))

/-- A fixed least-entry phase chart has an explicit Householder frame. -/
def orderedEigenlineHouseholderFrame (d : ℕ) (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) : Matrix (Fin d) (Fin d) ℂ :=
  phaseFixedHouseholderFrame (ofLex p).1
    (orderedEigenlineChartCandidate d r p x)

/-- The selected coordinate of every fixed chart candidate is real. -/
theorem orderedEigenlineChartCandidate_selectedCoordinate_im
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    (orderedEigenlineChartCandidate d r p x (ofLex p).1).im = 0 := by
  rw [orderedEigenlineChartCandidate,
    projectiveUnitReconstruction_apply_self]
  simp

/-- The selected coordinate of every fixed chart candidate is strictly positive. -/
theorem orderedEigenlineChartCandidate_selectedCoordinate_re_pos
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    0 < (orderedEigenlineChartCandidate d r p x (ofLex p).1).re := by
  exact projectiveUnitReconstruction_self_re_pos _ _

/-- The explicit Householder frame has the fixed-chart candidate as its
selected column. -/
theorem orderedEigenlineHouseholderFrame_mulVec_coordinate
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    (orderedEigenlineHouseholderFrame d r p x).mulVec
        (phaseFixedCoordinateVector (ofLex p).1) =
      orderedEigenlineChartCandidate d r p x := by
  apply phaseFixedHouseholderFrame_mulVec_coordinate
  · apply Complex.ext
    · rfl
    · simpa using orderedEigenlineChartCandidate_selectedCoordinate_im r p x
  · exact ne_of_gt (phaseFixedHouseholder_denominator_pos _ _
      (orderedEigenlineChartCandidate_selectedCoordinate_re_pos r p x))

/-- On the least-chart region, the explicit Householder frame completes the
globally selected ordered eigenline. -/
theorem orderedEigenlineHouseholderFrame_mulVec_eq_selection
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d)
    (hx : x ∈ orderedEigenpairReconstructionChartRegion d r p) :
    (orderedEigenlineHouseholderFrame d r p x).mulVec
        (phaseFixedCoordinateVector (ofLex p).1) =
      orderedEigenlineSelection d r x := by
  rw [orderedEigenlineHouseholderFrame_mulVec_coordinate]
  rw [orderedEigenlineSelection_eq_candidate,
    (leastOrderedEigenlineChart_eq_iff r x p).2 hx]

/-- The pure algebraic identity for the explicit formula: the displayed
Householder matrix is unitary for a unit phase-fixed vector.  It contains no
measurable selection, topology, reconstruction, or Jacobian data.  It is proved
as `phaseFixedHouseholderUnitaryIdentity`. -/
structure PhaseFixedHouseholderUnitaryIdentity : Prop where
  unitary : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι),
    ‖v‖ = 1 → v i = ((v i).re : ℂ) → 0 < (v i).re →
      (phaseFixedHouseholderFrame i v)ᴴ *
        phaseFixedHouseholderFrame i v = 1

/-- Once the elementary Householder identity is supplied, every ordered
least-entry chart carries an explicit unitary frame with the selected eigenline
as its distinguished column. -/
theorem orderedEigenlineHouseholderFrame_unitary
    (hH : PhaseFixedHouseholderUnitaryIdentity)
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    (orderedEigenlineHouseholderFrame d r p x)ᴴ *
      orderedEigenlineHouseholderFrame d r p x = 1 := by
  change
    (phaseFixedHouseholderFrame (ofLex p).1
      (orderedEigenlineChartCandidate d r p x))ᴴ *
      phaseFixedHouseholderFrame (ofLex p).1
        (orderedEigenlineChartCandidate d r p x) = 1
  exact hH.unitary (ι := Fin d) (ofLex p).1
    (orderedEigenlineChartCandidate d r p x)
    (norm_projectiveUnitReconstruction _ _)
    (by
      apply Complex.ext
      · rfl
      · simpa using
          orderedEigenlineChartCandidate_selectedCoordinate_im r p x)
    (orderedEigenlineChartCandidate_selectedCoordinate_re_pos r p x)

end CoareaNative.BlockBand
