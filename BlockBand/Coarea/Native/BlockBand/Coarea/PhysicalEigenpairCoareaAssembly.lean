module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairGaussianCoareaFactors
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairIncidenceChangeOfVariables
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoareaGoodSet
public import BlockBand.Coarea.Native.BlockBand.Coarea.SchurData

/-!
# Physical fixed-rank eigenpair coarea assembly

For fixed exterior data this module combines the proved incidence-chart
change of variables with the Gaussian regression factor, the consecutive GUE
normalization, the affine projective density, the squared spectral-gap
determinant, the Schur-clock crossing form, and the additive inertia sector.

The formula is local to a measurable injectivity piece of a concrete ordered
chart.  The moving-frame projective correction remains the completely defined
`coherentEigenpairProjectiveJacobianDefect`; no correction-free global formula
is asserted before its determinant is identified.  All quantifiers are at
fixed finite matrix sizes, fixed positive variance, and fixed exterior data;
there is no limiting or uniformity assertion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal ComplexOrder

/-- The real Schur-clock crossing quadratic form evaluated on the normalized
phase-fixed representative of an affine projective coordinate. -/
def physicalEigenpairCrossingQuadratic {d : ℕ} {n : Type*}
    [Fintype n] (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (z : Fin (d - 1) → ℂ) : ℝ :=
  (star (canonicalProjectiveUnitVector z) ⬝ᵥ
    (schurClock T *ᵥ canonicalProjectiveUnitVector z)).re

/-- The additive exterior-plus-complementary inertia predicate selecting the
one-based rank `α + 1` at energy `E`. -/
def physicalEigenpairFixedRank {dR d : ℕ} (α : ℕ)
    (R : HermitianCoordinateSpace dR) (E : ℝ)
    (B : RealHermitianMatrix (Fin (d - 1))) : Prop :=
  coareaRankIndex dR (d - 1)
    (R, (E, (hermitianFinCoordinatesLinearEquiv (d - 1)).symm B)) = α + 1

/-- The physical factors outside the eigenpair incidence Jacobian.  They are
kept as a product of `ofReal` factors, which records the paper's
normalization without imposing artificial sign hypotheses at the definition. -/
def physicalEigenpairOuterWeight {d : ℕ} {n : Type*} [Fintype n]
    (t E f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1))) : ℝ≥0∞ :=
  ENNReal.ofReal (coareaGaussianDensityConstant d t) *
    ENNReal.ofReal (canonicalGaussianRegressionFactor E f t q) *
    ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq (B.1 - Fv) / (2 * t))) *
    ENNReal.ofReal (physicalEigenpairCrossingQuadratic T z)

/-- The full physical source density in one selected eigenpair chart.  The
incidence factor contains exactly one affine-projective density, one squared
gap determinant, and the moving-frame correction defect. -/
def physicalEigenpairCoareaDensity {dR d : ℕ} {n : Type*} [Fintype n]
    (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) : ℝ≥0∞ := by
  classical
  let y := eigenpairIncidenceCoordinates i x
  exact if physicalEigenpairFixedRank α R y.1 y.2.2 then
    physicalEigenpairOuterWeight t y.1 f q Fv T y.2.1 y.2.2 *
      ENNReal.ofReal (eigenpairIncidenceDensity i x)
  else 0

/-- Pointwise expansion of the physical density.  This displays the exact
constant `c_{d,t}`, regression factor, complementary Gaussian, Schur-clock
crossing form, affine projective Haar density, `Complex.normSq` gap
determinant, and the explicit correction defect, without double-counting any
Jacobian factor. -/
theorem physicalEigenpairCoareaDensity_eq_explicit
    {dR d : ℕ} {n : Type*} [Fintype n]
    (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d)
    (hrank : physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2)
    (hgap : (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0) :
    physicalEigenpairCoareaDensity α R i t f q Fv T x =
      ENNReal.ofReal (coareaGaussianDensityConstant d t) *
      ENNReal.ofReal (canonicalGaussianRegressionFactor
        (eigenpairIncidenceCoordinates i x).1 f t q) *
      ENNReal.ofReal (Real.exp
        (-hilbertSchmidtNormSq
          ((eigenpairIncidenceCoordinates i x).2.2.1 - Fv) / (2 * t))) *
      ENNReal.ofReal (physicalEigenpairCrossingQuadratic T
        (eigenpairIncidenceCoordinates i x).2.1) *
      ENNReal.ofReal (canonicalProjectiveAffineDensity
        (eigenpairIncidenceCoordinates i x).2.1 *
        Complex.normSq (eigenpairGapMatrix
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.2.1).det *
        coherentEigenpairProjectiveJacobianDefect i
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1
          (eigenpairIncidenceCoordinates i x).2.2 hgap) := by
  simp only [physicalEigenpairCoareaDensity, ite_eq_left hrank]
  rw [eigenpairIncidenceDensity]
  simp only [dite_eq_left hgap]
  rw [eigenpairLocalRealJacobianDensity_eq_normSq_det]
  rfl

/-- Transport a source weight to the image of a chart by choosing its unique
preimage in `s`.  It is constructed from the decoder and the set. -/
def eigenpairChartTransportWeight {d : ℕ} (i : Fin d)
    (s : Set (HermitianCoordinateSpace d))
    (w : HermitianCoordinateSpace d → ℝ≥0∞)
    (K : HermitianCoordinateSpace d) : ℝ≥0∞ := by
  classical
  exact if h : ∃ x, x ∈ s ∧
      selectedEigenpairFinCoordinateChartDecode i x = K then
    w (Classical.choose h)
  else 0

/-- On an injectivity piece, the transported weight reads back the original
source weight exactly. -/
theorem eigenpairChartTransportWeight_decode
    {d : ℕ} (i : Fin d) (s : Set (HermitianCoordinateSpace d))
    (w : HermitianCoordinateSpace d → ℝ≥0∞)
    (hinj : Set.InjOn (selectedEigenpairFinCoordinateChartDecode i) s)
    {x : HermitianCoordinateSpace d} (hx : x ∈ s) :
    eigenpairChartTransportWeight i s w
      (selectedEigenpairFinCoordinateChartDecode i x) = w x := by
  classical
  let hmem : ∃ y, y ∈ s ∧
      selectedEigenpairFinCoordinateChartDecode i y =
        selectedEigenpairFinCoordinateChartDecode i x := ⟨x, hx, rfl⟩
  rw [eigenpairChartTransportWeight, dite_eq_left hmem]
  apply congrArg w
  apply hinj (Classical.choose_spec hmem).1 hx
  exact (Classical.choose_spec hmem).2

/-- The unconditional physical fixed-rank incidence-chart formula.  The left
side integrates the concretely transported Gaussian/regression/crossing weight
on a measurable image chart; the right side is the full physical coarea
density in the additive inertia sector.  The projective correction defect is
retained explicitly through `physicalEigenpairCoareaDensity`. -/
theorem lintegral_physical_fixedRankEigenpairCoarea_chart
    {dR d : ℕ} {n : Type*} [Fintype n]
    (α : ℕ) (R : HermitianCoordinateSpace dR)
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d))
    (hs : MeasurableSet s)
    (hsource : s ⊆ {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates (ofLex p).1 x ∈
        selectedOrderedEigenpairChartSource r p})
    (hgap : ∀ x ∈ s, (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2.1).det ≠ 0)
    (hrank : ∀ x ∈ s, physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' s,
      eigenpairChartTransportWeight (ofLex p).1 s
        (fun x => physicalEigenpairOuterWeight t
          (eigenpairIncidenceCoordinates (ofLex p).1 x).1 f q Fv T
          (eigenpairIncidenceCoordinates (ofLex p).1 x).2.1
          (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) K * g K) =
      ∫⁻ x in s, physicalEigenpairCoareaDensity α R (ofLex p).1
        t f q Fv T x *
          g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  let i := (ofLex p).1
  let w : HermitianCoordinateSpace d → ℝ≥0∞ := fun x =>
    physicalEigenpairOuterWeight t
      (eigenpairIncidenceCoordinates i x).1 f q Fv T
      (eigenpairIncidenceCoordinates i x).2.1
      (eigenpairIncidenceCoordinates i x).2.2
  have hinj : Set.InjOn (selectedEigenpairFinCoordinateChartDecode i) s :=
    (injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource r p).mono hsource
  rw [lintegral_fixedRankEigenpairIncidence_chart r p s hs hsource hgap]
  apply MeasureTheory.setLIntegral_congr_fun hs
  intro x hx
  change
    ENNReal.ofReal (eigenpairIncidenceDensity i x) *
        (eigenpairChartTransportWeight i s w
          (selectedEigenpairFinCoordinateChartDecode i x) *
          g (selectedEigenpairFinCoordinateChartDecode i x)) =
      physicalEigenpairCoareaDensity α R i t f q Fv T x *
        g (selectedEigenpairFinCoordinateChartDecode i x)
  rw [eigenpairChartTransportWeight_decode i s w hinj hx]
  dsimp only [w]
  have hrank' : physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2 := by
    simpa only [i] using hrank x hx
  rw [show physicalEigenpairCoareaDensity α R i t f q Fv T x =
      physicalEigenpairOuterWeight t
        (eigenpairIncidenceCoordinates i x).1 f q Fv T
        (eigenpairIncidenceCoordinates i x).2.1
        (eigenpairIncidenceCoordinates i x).2.2 *
          ENNReal.ofReal (eigenpairIncidenceDensity i x) by
    simp only [physicalEigenpairCoareaDensity, ite_eq_left hrank']]
  ac_rfl

end CoareaNative.BlockBand
