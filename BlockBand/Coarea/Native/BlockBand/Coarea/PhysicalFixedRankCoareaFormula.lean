module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalMovingSchurCover
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalEigenpairCoareaAssembly

/-!
# Global fixed-rank physical coarea, on a finite pole cover

This module performs the finite assembly which is available without identifying
the arbitrary-projective moving-frame correction.  A `PhysicalCoareaPoleChartCover`
contains only the measurable pole-interval/chart pieces on which the already
proved physical incidence change of variables applies.  Its two disjointness
fields record that neither pole intervals nor their decoded matrix images are
counted twice.  The encoder, decoder, Jacobian and density are the concrete ones
of the physical eigenpair coarea assembly; none is assumed.

The final theorem simultaneously supplies the physical moving-Schur bijection
on every pole interval and the sum of the exact chart formulas.  Its integrand
contains the Gaussian regression factor, consecutive GUE normalization,
projective density, squared complementary gap, Schur-clock factor, additive
inertia sector, and the correction defect.  No defect-one corollary is
stated: the available theorem that a *diagonal model* has defect one does not
identify it with the moving-frame correction.  All sizes, the variance
parameter, and the finite interval cover are fixed; no limiting or uniformity
claim is made.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- Finite measurable pieces of the physical fixed-rank incidence atlas.

The source conditions are precisely those required by the concrete chart
change of variables.  Pairwise disjoint decoded images and pole intervals are
part of what it means to be a cover, so the finite sum below has no overlap.
The sources may be smaller local-diffeomorphism neighborhoods; this is the
strongest global assembly justified before measurability of the full nonlinear
chart targets is proved. -/
structure PhysicalCoareaPoleChartCover
    (κ : Type*) [Fintype κ] {dR d : ℕ} (α : ℕ)
    (R : HermitianCoordinateSpace dR) where
  energyRegion : Set ℝ
  interval : κ → Set ℝ
  interval_iUnion : (⋃ a, interval a) = energyRegion
  source : κ → HermitianEigenRank d → OrderedEigenlineChartIndex d →
    Set (HermitianCoordinateSpace d)
  interval_pairwise_disjoint : Pairwise (Function.onFun Disjoint interval)
  decodedImage_pairwise_disjoint : Pairwise (Function.onFun Disjoint
    (fun arp : κ × HermitianEigenRank d × OrderedEigenlineChartIndex d =>
      selectedEigenpairFinCoordinateChartDecode (ofLex arp.2.2).1 ''
        source arp.1 arp.2.1 arp.2.2))
  source_measurable : ∀ a r p, MeasurableSet (source a r p)
  source_in_chart : ∀ a r p,
    source a r p ⊆ {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates (ofLex p).1 x ∈
        selectedOrderedEigenpairChartSource r p}
  source_gap : ∀ a r p x, x ∈ source a r p →
    (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2.1).det ≠ 0
  source_rank : ∀ a r p x, x ∈ source a r p →
    physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates (ofLex p).1 x).1
      (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2
  source_energy_mem : ∀ a r p x, x ∈ source a r p →
    (eigenpairIncidenceCoordinates (ofLex p).1 x).1 ∈ interval a

/-- The disjoint union of all decoded physical chart pieces. -/
def PhysicalCoareaPoleChartCover.decodedUnion
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ}
    {R : HermitianCoordinateSpace dR}
    (C : PhysicalCoareaPoleChartCover κ (d := d) α R) :
    Set (HermitianCoordinateSpace d) :=
  ⋃ arp : κ × HermitianEigenRank d × OrderedEigenlineChartIndex d,
    selectedEigenpairFinCoordinateChartDecode (ofLex arp.2.2).1 ''
      C.source arp.1 arp.2.1 arp.2.2

/-- Membership in the physical fixed-rank predicate is exactly membership in
`CoareaGoodSet`'s measurable additive inertia sector (with the same exterior,
energy, and complementary Hermitian coordinates). -/
theorem physicalEigenpairFixedRank_iff_mem_coareaRankSector
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    physicalEigenpairFixedRank α R E B ↔
      (R, (E, (hermitianFinCoordinatesLinearEquiv (d - 1)).symm B)) ∈
        coareaRankSector dR (d - 1) α := by
  rfl

/-- Finite disjoint assembly of the exact physical chart coarea formulas.

The left side is written as the sum of integrals over the pairwise-disjoint
images certified by `C.decodedImage_pairwise_disjoint`; hence it is the
integral over the corresponding disjoint chart/pole pieces, without a hidden
multiplicity.  The right side retains the projective correction defect
inside `physicalEigenpairCoareaDensity`. -/
theorem lintegral_physical_fixedRankEigenpairCoarea_finiteCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {dR d : ℕ} (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (C : PhysicalCoareaPoleChartCover κ α R)
    {n : Type*} [Fintype n]
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∑ a : κ, ∑ r : HermitianEigenRank d, ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' C.source a r p,
        eigenpairChartTransportWeight (ofLex p).1 (C.source a r p)
          (fun x => physicalEigenpairOuterWeight t
            (eigenpairIncidenceCoordinates (ofLex p).1 x).1 f q Fv T
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.1
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) K * g K) =
      ∑ a : κ, ∑ r : HermitianEigenRank d, ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in C.source a r p,
          physicalEigenpairCoareaDensity α R (ofLex p).1 t f q Fv T x *
            g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  exact lintegral_physical_fixedRankEigenpairCoarea_chart
    α R r p t f q Fv T
      (C.source a r p) (C.source_measurable a r p) (C.source_in_chart a r p)
      (C.source_gap a r p) (C.source_rank a r p) g

/-- The fully expanded physical chart density, made total by assigning
zero on the complementary collision locus.  On every cover source the gap is
nonzero, so this is precisely the paper's product with the defect. -/
def physicalEigenpairExpandedDensity {d : ℕ} {n : Type*} [Fintype n]
    (i : Fin d) (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) : ℝ≥0∞ := by
  classical
  let y := eigenpairIncidenceCoordinates i x
  exact if hgap : (eigenpairGapMatrix y.1 y.2.2.1).det ≠ 0 then
    ENNReal.ofReal (coareaGaussianDensityConstant d t) *
      ENNReal.ofReal (canonicalGaussianRegressionFactor y.1 f t q) *
      ENNReal.ofReal (Real.exp
        (-hilbertSchmidtNormSq (y.2.2.1 - Fv) / (2 * t))) *
      ENNReal.ofReal (physicalEigenpairCrossingQuadratic T y.2.1) *
      ENNReal.ofReal (canonicalProjectiveAffineDensity y.2.1 *
        Complex.normSq (eigenpairGapMatrix y.1 y.2.2.1).det *
        coherentEigenpairProjectiveJacobianDefect i y.1 y.2.1 y.2.2 hgap)
  else 0

/-- On the fixed-rank collision-free source, the physical density is its fully
expanded Gaussian/projective/gap/crossing/defect product. -/
theorem physicalEigenpairCoareaDensity_eq_expanded
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
      physicalEigenpairExpandedDensity i t f q Fv T x := by
  rw [physicalEigenpairCoareaDensity_eq_explicit α R i t f q Fv T x hrank hgap]
  simp only [physicalEigenpairExpandedDensity, dite_eq_left hgap]

/-- The finite-cover formula with every factor displayed through
`physicalEigenpairExpandedDensity`. -/
theorem lintegral_physical_fixedRankEigenpairCoarea_finiteCover_explicit
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : PhysicalCoareaPoleChartCover κ α R)
    {n : Type*} [Fintype n]
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∑ a : κ, ∑ r : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' C.source a r p,
        eigenpairChartTransportWeight (ofLex p).1 (C.source a r p)
          (fun x => physicalEigenpairOuterWeight t
            (eigenpairIncidenceCoordinates (ofLex p).1 x).1 f q Fv T
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.1
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) K * g K) =
      ∑ a : κ, ∑ r : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in C.source a r p,
          physicalEigenpairExpandedDensity (ofLex p).1 t f q Fv T x *
            g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [lintegral_physical_fixedRankEigenpairCoarea_finiteCover
    α R C t f q Fv T g]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  apply MeasureTheory.setLIntegral_congr_fun (C.source_measurable a r p)
  intro x hx
  change physicalEigenpairCoareaDensity α R (ofLex p).1 t f q Fv T x *
      g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) =
    physicalEigenpairExpandedDensity (ofLex p).1 t f q Fv T x *
      g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)
  rw [physicalEigenpairCoareaDensity_eq_expanded α R (ofLex p).1
    t f q Fv T x (C.source_rank a r p x hx) (C.source_gap a r p x hx)]

/-- Global fixed ordered-rank physical conclusion over a finite pole cover.

For each pole interval, the first component is the unique moving-Schur
representation of every physical eigen-energy in the prescribed full-matrix
rank, and uniqueness of a zero on each ordered Schur branch.  The second
component is the disjoint finite-chart coarea identity above. -/
theorem physical_fixedRank_coarea_formula
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {dR d : ℕ}
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin d) n ℂ)
    (D : Matrix n n ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (α : Fin (Fintype.card (Fin d ⊕ n)))
    (R : HermitianCoordinateSpace dR)
    (C : PhysicalCoareaPoleChartCover κ α.val R)
    (hpoleFree : ∀ a E, E ∈ C.interval a →
      IsUnit (physicalExteriorPencil D E).det)
    (hloewner : ∀ a E₁, E₁ ∈ C.interval a → ∀ E₂, E₂ ∈ C.interval a → E₁ < E₂ →
      physicalSchurMatrix A V D E₂ ≤
        physicalSchurMatrix A V D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ a E, E ∈ C.interval a →
      Function.Injective
        (orderedEigenvalue (physicalSchurFamily A V D hA hD E)))
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∀ a : κ,
      Function.Bijective
          (physicalFixedRankEigenEnergyMap A V D hA hD (C.interval a) α
            (hpoleFree a)) ∧
        ∀ p q : MovingFixedRankSchurCrossing
            (physicalSchurFamily A V D hA hD) (C.interval a)
            (fun E => negativeEigenvalueCount
              (physicalExteriorFamily D hD E).property) α.val,
          p.1.1 = q.1.1 → p.1.2 = q.1.2) ∧
    ((∑ a : κ, ∑ r : HermitianEigenRank d, ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' C.source a r p,
        eigenpairChartTransportWeight (ofLex p).1 (C.source a r p)
          (fun x => physicalEigenpairOuterWeight t
            (eigenpairIncidenceCoordinates (ofLex p).1 x).1 f q Fv T
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.1
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) K * g K) =
      ∑ a : κ, ∑ r : HermitianEigenRank d, ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in C.source a r p,
          physicalEigenpairExpandedDensity (ofLex p).1 t f q Fv T x *
            g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)) := by
  refine ⟨fun a => physicalMovingSchur_globalCover A V D hA hD
    (C.interval a) α (hpoleFree a) (hloewner a) (hsimple a), ?_⟩
  exact lintegral_physical_fixedRankEigenpairCoarea_finiteCover_explicit
    α.val R C t f q Fv T g

end CoareaNative.BlockBand
