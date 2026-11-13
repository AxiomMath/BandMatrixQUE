module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalHermitianGaussianSplit
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurCoareaData
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalMovingRootAreaFormula
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalFixedRankCoareaFormula
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalCoareaExceptionalNull
public import BlockBand.Coarea.Native.BlockBand.Coarea.OrderedProjectionMeasurable

/-!
# Fixed-exterior physical conditional coarea

Conditioning means the exact finite-product Tonelli identity at fixed residual and exterior
coordinates; no regular conditional probability is introduced.  On each finite pole/chart cover
the incidence formula is applied to an arbitrary measurable observable of the zero-extended
ordered spectral projector.

The displayed density is `physicalEigenpairExpandedDensity`, and hence contains
`coareaGaussianDensityConstant`, the Gaussian regression factor, the GUE
quadratic exponential, the Schur crossing quadratic form, the affine
projective density, the squared complementary gap determinant, the additive
fixed-rank sector, and `coherentEigenpairProjectiveJacobianDefect`.

The results split the integral into the good event and its measurable complement.  A separate
general lemma deletes that complement when a measure-zero proof is supplied.

All dimensions, the exposed block, exterior data, ordered rank, variance, and finite pole cover
are fixed.  There is no asymptotic uniformity or limit assertion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- A phase-free observable of the selected eigenline: the observable sees
only the zero-extended ordered Lagrange projector, never a chosen eigenvector
phase. -/
def phaseFreeOrderedProjectorObservable {d : ℕ}
    (r : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (x : HermitianCoordinateSpace d) : ℝ≥0∞ :=
  Ψ (zeroExtendedOrderedEigenprojection d r x)

/-- Measurability of every measurable phase-free projector observable. -/
theorem measurable_phaseFreeOrderedProjectorObservable {d : ℕ}
    (r : HermitianEigenRank d)
    {Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    Measurable (phaseFreeOrderedProjectorObservable r Ψ) :=
  hΨ.comp (measurable_zeroExtendedOrderedEigenprojection d r)

/-- Exact physical finite-product Gaussian splitting at fixed exterior data.
This is the conditional integral statement supplied by independence: after
fixing `(V,ξ)`, the inner integral is solely over the fresh correctly
normalized GUE block. -/
theorem physicalConditionalGaussianSplit
    {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure Ξ)
    (Φ : HermitianMatrix (Fin (2 * p.W)) → Ξ → ℝ≥0∞)
    (hΦ : AEMeasurable
      (fun ω : PhysicalHermitianSplitSample (2 * p.W) Ξ =>
        Φ (physicalHermitianExposedPair ω) ω.1.2)
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw)) :
    (∫⁻ ω, Φ (physicalHermitianExposedPair ω) ω.1.2
      ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw) =
      ∫⁻ z, (∫⁻ g,
          Φ (hermitianMatrixAdd (hermitianOfFinCoordinates (2 * p.W) z.1)
            (hermitianGUEBlock (2 * p.W) g)) z.2
          ∂hermitianGUECoordinateMeasure (2 * p.W)
            (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0))
        ∂((physicalExposedPairResidualMeasure p hs0 hsc hsb).prod exteriorLaw) :=
  lintegral_physicalExposedPairGaussian_split p hs0 hsc hsb exteriorLaw Φ hΦ

/-- The exact fixed-exterior, fixed-rank chart formula for an arbitrary
measurable phase-free projector observable.  The cover sources carry the
additive inertia predicate, and `physicalEigenpairExpandedDensity` retains the
projective correction defect. -/
theorem physicalConditionalCoarea_fixedExterior
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : PhysicalCoareaPoleChartCover κ α R)
    {n : Type*} [Fintype n]
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (_hΨ : Measurable Ψ) :
    (∑ a : κ, ∑ r : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' C.source a r p,
        eigenpairChartTransportWeight (ofLex p).1 (C.source a r p)
          (fun x => physicalEigenpairOuterWeight t
            (eigenpairIncidenceCoordinates (ofLex p).1 x).1 f q Fv T
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.1
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) K *
          phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ r : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in C.source a r p,
          physicalEigenpairExpandedDensity (ofLex p).1 t f q Fv T x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  exact lintegral_physical_fixedRankEigenpairCoarea_finiteCover_explicit
    α R C t f q Fv T (phaseFreeOrderedProjectorObservable ρ Ψ)

/-- Global moving-root cover together with the fixed-exterior incidence
identity for a phase-free projector observable.  The first component is the
concrete physical Schur-root bijection on every pole interval; the second is
the exact finite-chart formula with the correction defect. -/
theorem physicalConditionalCoarea_globalCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {dR d : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin d) (Fin d) ℂ) (V : Matrix (Fin d) n ℂ)
    (D : Matrix n n ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (α : Fin (Fintype.card (Fin d ⊕ n)))
    (R : HermitianCoordinateSpace dR)
    (C : PhysicalCoareaPoleChartCover κ α.val R)
    (hpoleFree : ∀ a E, E ∈ C.interval a →
      IsUnit (physicalExteriorPencil D E).det)
    (hloewner : ∀ a E₁, E₁ ∈ C.interval a →
      ∀ E₂, E₂ ∈ C.interval a → E₁ < E₂ →
        physicalSchurMatrix A V D E₂ ≤
          physicalSchurMatrix A V D E₁ - ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ a E, E ∈ C.interval a →
      Function.Injective
        (orderedEigenvalue (physicalSchurFamily A V D hA hD E)))
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (_hΨ : Measurable Ψ) :
    (∀ a : κ,
      Function.Bijective
          (physicalFixedRankEigenEnergyMap A V D hA hD (C.interval a) α
            (hpoleFree a)) ∧
        ∀ p q : MovingFixedRankSchurCrossing
            (physicalSchurFamily A V D hA hD) (C.interval a)
            (fun E => negativeEigenvalueCount
              (physicalExteriorFamily D hD E).property) α.val,
          p.1.1 = q.1.1 → p.1.2 = q.1.2) ∧
    ((∑ a : κ, ∑ r : HermitianEigenRank d,
      ∑ p : OrderedEigenlineChartIndex d,
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' C.source a r p,
        eigenpairChartTransportWeight (ofLex p).1 (C.source a r p)
          (fun x => physicalEigenpairOuterWeight t
            (eigenpairIncidenceCoordinates (ofLex p).1 x).1 f q Fv T
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.1
            (eigenpairIncidenceCoordinates (ofLex p).1 x).2.2) K *
          phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ r : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in C.source a r p,
          physicalEigenpairExpandedDensity (ofLex p).1 t f q Fv T x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)) := by
  exact physical_fixedRank_coarea_formula A V D hA hD α R C hpoleFree
    hloewner hsimple t f q Fv T (phaseFreeOrderedProjectorObservable ρ Ψ)

/-- Every nonnegative observable decomposes exactly into its selected physical
coarea-good part and its bad measurable complement.  This is the
exceptional-event conclusion available from the current physical law. -/
theorem GaussianRing.Law.lintegral_selectedCoareaGood_add_compl
    {p : Params} (M : GaussianRing.Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p))
    (Φ : M.Ω → ℝ≥0∞) :
    (∫⁻ ω in M.physicalSelectedCoareaGoodEvent j r, Φ ω ∂M.P) +
      (∫⁻ ω in (M.physicalSelectedCoareaGoodEvent j r)ᶜ, Φ ω ∂M.P) =
        ∫⁻ ω, Φ ω ∂M.P :=
  lintegral_add_compl Φ (M.measurableSet_physicalSelectedCoareaGoodEvent j r)

/-- A measurable exceptional set can be deleted from a nonnegative integral
once its complement is null. -/
theorem lintegral_restrict_eq_of_compl_null
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (good : Set Ω) (hgood : MeasurableSet good)
    (hnull : μ goodᶜ = 0) (Φ : Ω → ℝ≥0∞) :
    (∫⁻ ω in good, Φ ω ∂μ) = ∫⁻ ω, Φ ω ∂μ := by
  have hbad : (∫⁻ ω in goodᶜ, Φ ω ∂μ) = 0 :=
    setLIntegral_measure_zero goodᶜ Φ hnull
  calc
    (∫⁻ ω in good, Φ ω ∂μ) =
        (∫⁻ ω in good, Φ ω ∂μ) + (∫⁻ ω in goodᶜ, Φ ω ∂μ) := by
          rw [hbad, add_zero]
    _ = ∫⁻ ω, Φ ω ∂μ := lintegral_add_compl Φ hgood

end CoareaNative.BlockBand
