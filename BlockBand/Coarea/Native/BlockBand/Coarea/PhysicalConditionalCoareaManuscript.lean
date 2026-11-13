module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalDependentCoarea

/-!
# Fixed-exterior conditional coarea assembly

The finite-product GUE/Tonelli identity combined with the dependent physical Schur coarea
formula.  The chart density is expanded with the exact arbitrary-coordinate projective
Jacobian, so no correction defect remains.  Observables depend only on the zero-extended
ordered Lagrange projector and are therefore phase-free.

No physical exceptional complement is discarded here.  The final theorem records two exact but
logically separate equalities; it is not the single global coarea identity.  The raw-volume
chart integral differs from the normalized projective-Haar × `GUE_(d-1)` formulation by the
factor `chartGUENormalizationRatio`.

All dimensions, ranks, exterior data and pole charts are fixed; no limit or uniformity is
asserted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- Read a Hermitian matrix back into the finite real coordinate convention
used by the incidence atlas. -/
def hermitianFinCoordinateReadback (d : ℕ)
    (H : HermitianMatrix (Fin d)) : HermitianCoordinateSpace d :=
  (hermitianFinCoordinatesLinearEquiv d).symm H

/-- Finite-dimensional Hermitian coordinate readback is Borel measurable. -/
theorem measurable_hermitianFinCoordinateReadback (d : ℕ) :
    Measurable (hermitianFinCoordinateReadback d) := by
  exact
    ((hermitianFinCoordinatesLinearEquiv d).symm.toLinearMap
      |>.continuous_of_finiteDimensional).measurable

/-- A matrix-side phase-free projector observable, expressed in the same
finite-coordinate convention as the coarea atlas. -/
def physicalMatrixPhaseFreeObservable {d : ℕ}
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (H : HermitianMatrix (Fin d)) : ℝ≥0∞ :=
  phaseFreeOrderedProjectorObservable ρ Ψ
    (hermitianFinCoordinateReadback d H)

/-- Every measurable function of the ordered projector gives a measurable
matrix-side observable. -/
theorem measurable_physicalMatrixPhaseFreeObservable {d : ℕ}
    (ρ : HermitianEigenRank d)
    {Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    Measurable (physicalMatrixPhaseFreeObservable ρ Ψ) :=
  (measurable_phaseFreeOrderedProjectorObservable ρ hΨ).comp
    (measurable_hermitianFinCoordinateReadback d)

/-- The assembled residual-plus-fresh Hermitian block is measurable on the
concrete split sample space. -/
theorem measurable_physicalHermitianExposedPair
    {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] :
    Measurable
      (physicalHermitianExposedPair :
        PhysicalHermitianSplitSample d Ξ → HermitianMatrix (Fin d)) := by
  have hres : Measurable
      (physicalHermitianResidual :
        PhysicalHermitianSplitSample d Ξ → HermitianMatrix (Fin d)) :=
    (measurable_hermitianOfFinCoordinates d).comp
      (measurable_fst.comp measurable_fst)
  have hfresh : Measurable
      (physicalHermitianFreshGUE :
        PhysicalHermitianSplitSample d Ξ → HermitianMatrix (Fin d)) :=
    (measurable_hermitianGUEBlock d).comp measurable_snd
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro i j
  exact ((measurable_subtype_coe.comp hres).eval_matrix).add
    ((measurable_subtype_coe.comp hfresh).eval_matrix)

/-- The finite-product GUE/Tonelli input specialized to the same arbitrary
measurable phase-free ordered-projector observable used by the chart formula. -/
theorem lintegral_physicalPhaseFreeGaussian_split
    {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure Ξ)
    (ρ : HermitianEigenRank (2 * p.W))
    (Ψ : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → ℝ≥0∞)
    (hΨ : Measurable Ψ) :
    (∫⁻ ω,
      physicalMatrixPhaseFreeObservable ρ Ψ
        (physicalHermitianExposedPair ω)
      ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw) =
      ∫⁻ z, (∫⁻ g,
          physicalMatrixPhaseFreeObservable ρ Ψ
            (hermitianMatrixAdd
              (hermitianOfFinCoordinates (2 * p.W) z.1)
              (hermitianGUEBlock (2 * p.W) g))
          ∂hermitianGUECoordinateMeasure (2 * p.W)
            (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0))
        ∂((physicalExposedPairResidualMeasure p hs0 hsc hsb).prod exteriorLaw) := by
  apply physicalConditionalGaussianSplit p hs0 hsc hsb exteriorLaw
    (fun H _ => physicalMatrixPhaseFreeObservable ρ Ψ H)
  exact ((measurable_physicalMatrixPhaseFreeObservable ρ hΨ).comp
    measurable_physicalHermitianExposedPair).aemeasurable

/-- Coordinate-density identification for the fresh finite-product GUE law.
`PhysicalFreshGUEDensity` proves this proposition under `0 < t` and proves it
false at `t = 0` in positive dimension.  By itself it does not identify the
raw-volume chart integral with the normalized measure. -/
def FreshGUECoordinateDensityIdentification (d : ℕ) (t : ℝ) (ht : 0 ≤ t) : Prop :=
  hermitianGUECoordinateMeasure d t ht =
    volume.withDensity (fun x =>
      hermitianGUEDensity d t (hermitianGUEBlock d x))

/-- The correction-free density of the paper, with all physical Schur inputs
evaluated at the incidence energy and projective coordinate. -/
def physicalSchurManuscriptDensity
    {r d : ℕ} (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) (x : HermitianCoordinateSpace d) : ℝ≥0∞ :=
  ENNReal.ofReal (coareaGaussianDensityConstant d t) *
    ENNReal.ofReal (canonicalGaussianRegressionFactor
      (eigenpairIncidenceCoordinates i x).1
      (physicalCoarea_f H_R C V
        (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.1) t
      (physicalCoarea_q H_R C V
        (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.1)) *
    ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
      ((eigenpairIncidenceCoordinates i x).2.2.1 -
        physicalCoareaFv H_R C V
          (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.1) / (2 * t))) *
    ENNReal.ofReal ((star (canonicalProjectiveUnitVector
        (eigenpairIncidenceCoordinates i x).2.1) ⬝ᵥ
      (physicalCoareaD H_R C
          (eigenpairIncidenceCoordinates i x).1 *ᵥ
        canonicalProjectiveUnitVector
          (eigenpairIncidenceCoordinates i x).2.1)).re) *
    ENNReal.ofReal (canonicalProjectiveAffineDensity
      (eigenpairIncidenceCoordinates i x).2.1 *
      Complex.normSq (eigenpairGapMatrix
        (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2.1).det)

/-- On the additive inertia and collision-free sector, the dependent Schur
density is exactly the correction-free product of the paper. -/
theorem physicalSchurCoareaDensity_eq_manuscript
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (i : Fin d) (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d)
    (hrank : physicalEigenpairFixedRank α R
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2)
    (hgap : (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0) :
    physicalSchurCoareaDensity α R i t H_R C V x =
      physicalSchurManuscriptDensity t H_R C V i x := by
  exact physicalSchurCoareaDensity_eq_exact
    α R i t H_R C V x hrank hgap

/-- Dependent fixed-exterior coarea with the correction-free density of the paper
and an arbitrary measurable phase-free ordered-projector observable. -/
theorem lintegral_physicalSchurCoarea_manuscript_finiteCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    (t : ℝ)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (_hΨ : Measurable Ψ) :
    (∑ a : κ, ∑ rank : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 ''
          cover.source a rank p,
        eigenpairChartTransportWeight (ofLex p).1 (cover.source a rank p)
          (physicalSchurOuterWeight t H_R C V (ofLex p).1) K *
            phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurManuscriptDensity t H_R C V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [lintegral_physicalSchurCoarea_finiteCover α R cover t H_R C V
    (phaseFreeOrderedProjectorObservable ρ Ψ)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro rank _
  apply Finset.sum_congr rfl
  intro p _
  apply MeasureTheory.setLIntegral_congr_fun (cover.source_measurable a rank p)
  intro x hx
  change physicalSchurCoareaDensity α R (ofLex p).1 t H_R C V x * _ =
    physicalSchurManuscriptDensity t H_R C V (ofLex p).1 x * _
  rw [physicalSchurCoareaDensity_eq_manuscript α R (ofLex p).1 t H_R C V x
    (cover.source_rank a rank p x hx) (cover.source_gap a rank p x hx)]

/-- Moving-root coverage plus the exact dependent, correction-free coarea
identity of the paper. -/
theorem physicalConditionalCoareaManuscript_globalCover
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
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (hΨ : Measurable Ψ) :
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
          (physicalSchurOuterWeight t H_R C V (ofLex p).1) K *
            phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurManuscriptDensity t H_R C V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)) := by
  refine ⟨(physicalDependentCoarea_globalCover A coupling D hA hD α R cover
    hpoleFree hloewner hsimple t H_R C V
      (phaseFreeOrderedProjectorObservable ρ Ψ)).1, ?_⟩
  exact lintegral_physicalSchurCoarea_manuscript_finiteCover
    α.val R cover t H_R C V ρ Ψ hΨ

/-- The fresh finite-product GUE/Tonelli equality and the dependent,
correction-free local-chart identity hold simultaneously for the same
phase-free projector observable.  This conjunction makes no
claim that the two right-hand sides are equal: the chart side
uses raw coordinate volume, whereas the paper uses normalized
projective-Haar and `GUE_(d-1)` measures. -/
theorem physicalConditionalCoareaManuscript_bridge
    {Ξ : Type*} [MeasurableSpace Ξ]
    (p₀ : Params) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p₀.c) (hsb : s ≤ p₀.b)
    (exteriorLaw : Measure Ξ)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin (2 * p₀.W)) (Fin (2 * p₀.W)) ℂ)
    (coupling : Matrix (Fin (2 * p₀.W)) n ℂ)
    (D : Matrix n n ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (α : Fin (Fintype.card (Fin (2 * p₀.W) ⊕ n)))
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
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (2 * p₀.W - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (2 * p₀.W - 1))
      (Unit ⊕ Fin (2 * p₀.W - 1)) ℂ)
    (ρ : HermitianEigenRank (2 * p₀.W))
    (Ψ : Matrix (Fin (2 * p₀.W)) (Fin (2 * p₀.W)) ℂ → ℝ≥0∞)
    (hΨ : Measurable Ψ) :
    ((∫⁻ ω,
      physicalMatrixPhaseFreeObservable ρ Ψ
        (physicalHermitianExposedPair ω)
      ∂physicalHermitianSplitMeasure (2 * p₀.W) (coareaGUEVariance p₀ s)
        (coareaGUEVariance_nonneg p₀ hs0)
        (physicalExposedPairResidualMeasure p₀ hs0 hsc hsb) exteriorLaw) =
      ∫⁻ z, (∫⁻ g,
          physicalMatrixPhaseFreeObservable ρ Ψ
            (hermitianMatrixAdd
              (hermitianOfFinCoordinates (2 * p₀.W) z.1)
              (hermitianGUEBlock (2 * p₀.W) g))
          ∂hermitianGUECoordinateMeasure (2 * p₀.W)
            (coareaGUEVariance p₀ s) (coareaGUEVariance_nonneg p₀ hs0))
        ∂((physicalExposedPairResidualMeasure p₀ hs0 hsc hsb).prod exteriorLaw)) ∧
    ((∀ a : κ,
      Function.Bijective
          (physicalFixedRankEigenEnergyMap A coupling D hA hD
            (cover.interval a) α (hpoleFree a)) ∧
        ∀ u v : MovingFixedRankSchurCrossing
            (physicalSchurFamily A coupling D hA hD) (cover.interval a)
            (fun E => negativeEigenvalueCount
              (physicalExteriorFamily D hD E).property) α.val,
          u.1.1 = v.1.1 → u.1.2 = v.1.2) ∧
    ((∑ a : κ, ∑ rank : HermitianEigenRank (2 * p₀.W),
      ∑ chart : OrderedEigenlineChartIndex (2 * p₀.W),
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex chart).1 ''
          cover.source a rank chart,
        eigenpairChartTransportWeight (ofLex chart).1
          (cover.source a rank chart)
          (physicalSchurOuterWeight (coareaGUEVariance p₀ s)
            H_R C V (ofLex chart).1) K *
            phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank (2 * p₀.W),
        ∑ chart : OrderedEigenlineChartIndex (2 * p₀.W),
        ∫⁻ x in cover.source a rank chart,
          physicalSchurManuscriptDensity (coareaGUEVariance p₀ s)
            H_R C V (ofLex chart).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode
                (ofLex chart).1 x))) := by
  constructor
  · exact lintegral_physicalPhaseFreeGaussian_split
      p₀ hs0 hsc hsb exteriorLaw ρ Ψ hΨ
  · exact physicalConditionalCoareaManuscript_globalCover
      A coupling D hA hD α R cover hpoleFree hloewner hsimple
      (coareaGUEVariance p₀ s) H_R C V ρ Ψ hΨ

end CoareaNative.BlockBand
