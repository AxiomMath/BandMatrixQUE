module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalConditionalCoareaExact

/-!
# Dependent physical eigenpair coarea weights

The physical Schur regression and compression data depend on the incidence energy and
projective coordinate.  Here the chart formula is proved with a source weight that is an
arbitrary function of the full incidence coordinate, and is then specialized to the concrete
data `physicalCoarea_f`, `physicalCoarea_q`, `physicalCoareaFv`, and `physicalCoareaT`.

This is the fixed-exterior chart step of the coarea theorem; no exceptional-event or
probability-law assertion is made here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- Change of variables on an incidence chart with an arbitrary source-dependent
nonnegative weight. -/
theorem lintegral_fixedRankEigenpairIncidence_chart_weight
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (s : Set (HermitianCoordinateSpace d))
    (hs : MeasurableSet s)
    (hsource : s ⊆ {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates (ofLex p).1 x ∈
        selectedOrderedEigenpairChartSource r p})
    (hgap : ∀ x ∈ s, (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2.1).det ≠ 0)
    (w g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' s,
      eigenpairChartTransportWeight (ofLex p).1 s w K * g K) =
      ∫⁻ x in s,
        ENNReal.ofReal (eigenpairIncidenceDensity (ofLex p).1 x) * w x *
          g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  let i := (ofLex p).1
  have hinj : Set.InjOn (selectedEigenpairFinCoordinateChartDecode i) s :=
    (injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource r p).mono hsource
  rw [lintegral_fixedRankEigenpairIncidence_chart r p s hs hsource hgap
    (fun K => eigenpairChartTransportWeight i s w K * g K)]
  apply MeasureTheory.setLIntegral_congr_fun hs
  intro x hx
  change
    ENNReal.ofReal (eigenpairIncidenceDensity i x) *
        (eigenpairChartTransportWeight i s w
          (selectedEigenpairFinCoordinateChartDecode i x) *
            g (selectedEigenpairFinCoordinateChartDecode i x)) =
      ENNReal.ofReal (eigenpairIncidenceDensity i x) * w x *
        g (selectedEigenpairFinCoordinateChartDecode i x)
  rw [eigenpairChartTransportWeight_decode i s w hinj hx]
  ac_rfl

/-- The concrete fixed-exterior Gaussian/regression/crossing weight, with every Schur
datum evaluated at the incidence energy and projective coordinate. -/
def physicalSchurOuterWeight
    {r d : ℕ} (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) (x : HermitianCoordinateSpace d) : ℝ≥0∞ :=
  let y := eigenpairIncidenceCoordinates i x
  physicalEigenpairOuterWeight t y.1
    (physicalCoarea_f H_R C V y.1 y.2.1)
    (physicalCoarea_q H_R C V y.1 y.2.1)
    (physicalCoareaFv H_R C V y.1 y.2.1)
    (physicalCoareaT H_R C y.1) y.2.1 y.2.2

/-- On the prescribed additive-inertia sector, the specialized physical density is the
source-dependent outer weight times the incidence Jacobian. -/
theorem physicalSchurCoareaDensity_eq_outerWeight_mul_incidence
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (i : Fin d) (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d)
    (hrank : physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2) :
    physicalSchurCoareaDensity α R i t H_R C V x =
      physicalSchurOuterWeight t H_R C V i x *
        ENNReal.ofReal (eigenpairIncidenceDensity i x) := by
  simp only [physicalSchurCoareaDensity_eq, physicalEigenpairCoareaDensity,
    ite_eq_left hrank, physicalSchurOuterWeight]

/-- Exact chart coarea with the energy/projective-dependent physical Schur data.
The source set itself supplies the additive rank sector and gap nonvanishing. -/
theorem lintegral_physicalSchurCoarea_chart
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (rank : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d))
    (hs : MeasurableSet s)
    (hsource : s ⊆ {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates (ofLex p).1 x ∈
        selectedOrderedEigenpairChartSource rank p})
    (hgap : ∀ x ∈ s, (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2.1).det ≠ 0)
    (hrank : ∀ x ∈ s, physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' s,
      eigenpairChartTransportWeight (ofLex p).1 s
        (physicalSchurOuterWeight t H_R C V (ofLex p).1) K * g K) =
      ∫⁻ x in s,
        physicalSchurCoareaDensity α R (ofLex p).1 t H_R C V x *
          g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [lintegral_fixedRankEigenpairIncidence_chart_weight rank p s hs hsource hgap
    (physicalSchurOuterWeight t H_R C V (ofLex p).1) g]
  apply MeasureTheory.setLIntegral_congr_fun hs
  intro x hx
  change
    ENNReal.ofReal (eigenpairIncidenceDensity (ofLex p).1 x) *
        physicalSchurOuterWeight t H_R C V (ofLex p).1 x *
          g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) =
      physicalSchurCoareaDensity α R (ofLex p).1 t H_R C V x *
        g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)
  rw [physicalSchurCoareaDensity_eq_outerWeight_mul_incidence
    α R (ofLex p).1 t H_R C V x (hrank x hx)]
  ac_rfl

/-- Finite disjoint pole/chart cover with the dependent physical Schur data.
This is the correction-free fixed-exterior incidence formula needed by the paper;
`physicalSchurCoareaDensity_eq_exact` expands every factor and proves the correction
defect is one on each source. -/
theorem lintegral_physicalSchurCoarea_finiteCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∑ a : κ, ∑ rank : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 ''
          cover.source a rank p,
        eigenpairChartTransportWeight (ofLex p).1 (cover.source a rank p)
          (physicalSchurOuterWeight t H_R C V (ofLex p).1) K * g K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurCoareaDensity α R (ofLex p).1 t H_R C V x *
            g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro rank _
  apply Finset.sum_congr rfl
  intro p _
  exact lintegral_physicalSchurCoarea_chart α R rank p t H_R C V
    (cover.source a rank p) (cover.source_measurable a rank p)
    (cover.source_in_chart a rank p) (cover.source_gap a rank p)
    (cover.source_rank a rank p) g

/-- Moving-Schur coverage and the dependent-data fixed-exterior coarea identity in one
statement.  Thus every prescribed-rank physical eigen-energy on every pole interval is
represented uniquely, while the incidence integral uses the `(E,z)`-dependent
regression and compression data. -/
theorem physicalDependentCoarea_globalCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin d) (Fin d) ℂ) (coupling : Matrix (Fin d) n ℂ)
    (D : Matrix n n ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (α : Fin (Fintype.card (Fin d ⊕ n)))
    (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α.val R)
    (hpoleFree : ∀ a E, E ∈ cover.interval a →
      IsUnit (physicalExteriorPencil D E).det)
    (hloewner : ∀ a E₁, E₁ ∈ cover.interval a →
      ∀ E₂, E₂ ∈ cover.interval a → E₁ < E₂ →
        physicalSchurMatrix A coupling D E₂ ≤
          physicalSchurMatrix A coupling D E₁ -
            ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ a E, E ∈ cover.interval a →
      Function.Injective
        (orderedEigenvalue (physicalSchurFamily A coupling D hA hD E)))
    (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∀ a : κ,
      Function.Bijective
          (physicalFixedRankEigenEnergyMap A coupling D hA hD
            (cover.interval a) α (hpoleFree a)) ∧
        ∀ p q : MovingFixedRankSchurCrossing
            (physicalSchurFamily A coupling D hA hD) (cover.interval a)
            (fun E => negativeEigenvalueCount
              (physicalExteriorFamily D hD E).property) α.val,
          p.1.1 = q.1.1 → p.1.2 = q.1.2) ∧
    ((∑ a : κ, ∑ rank : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 ''
          cover.source a rank p,
        eigenpairChartTransportWeight (ofLex p).1 (cover.source a rank p)
          (physicalSchurOuterWeight t H_R C V (ofLex p).1) K * g K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurCoareaDensity α.val R (ofLex p).1 t H_R C V x *
            g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)) := by
  constructor
  · intro a
    exact physicalMovingSchur_globalCover A coupling D hA hD
      (cover.interval a) α (hpoleFree a) (hloewner a) (hsimple a)
  · exact lintegral_physicalSchurCoarea_finiteCover α.val R cover
      t H_R C V g

end CoareaNative.BlockBand
