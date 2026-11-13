module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalConditionalCoarea
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveCorrectionExact

/-!
# Exact fixed-exterior physical conditional coarea

The arbitrary-chart Householder determinant is exact, so the projective correction defect is
one (`coherentEigenpairProjectiveJacobianDefect_eq_one`).  This file removes it from the finite
physical coarea density and specializes the fixed-exterior chart and moving-root cover
identities to arbitrary measurable observables of the ordered spectral projector.  It also
retains the explicit finite-product GUE splitting theorem.

No exceptional event is discarded.  `PhysicalCoareaPoleChartCover`'s incidence formula accepts
fixed parameters `f,q,Fv,T`, whereas `PhysicalSchurCoareaData` makes those parameters functions
of `(E,z)`; the global-cover theorem below is stated for fixed fields, and the subsequent
pointwise theorem is its Schur specialization.

All exterior data, ranks, pole intervals, and dimensions are fixed, with no asymptotic or
uniformity claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- The canonical selected-first projective chart has exactly the complementary
`Fin (d-1)` coordinates. -/
private def canonicalProjectiveChartCoordinateEquiv (d : ℕ) :
    ProjectiveChartCoordinate
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)) ≃ Fin (d - 1) where
  toFun j := by
    rcases j with ⟨u | a, h⟩
    · exact False.elim (h (by cases u; rfl))
    · exact a
  invFun a := ⟨Sum.inr a, by simp⟩
  left_inv j := by
    rcases j with ⟨u | a, h⟩
    · exact False.elim (h (by cases u; rfl))
    · rfl
  right_inv _ := rfl

/-- Concrete formula for the canonical affine projective density. -/
theorem canonicalProjectiveAffineDensity_eq {d : ℕ}
    (i : Fin d) (z : Fin (d - 1) → ℂ) :
    canonicalProjectiveAffineDensity z =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d := by
  unfold canonicalProjectiveAffineDensity projectiveAffineDensity
  have hd : 0 < d := Fin.pos_iff_nonempty.mpr ⟨i⟩
  have hcard : Fintype.card (Unit ⊕ Fin (d - 1)) = d := by
    simp
    omega
  rw [hcard]
  congr 1
  unfold projectiveAffineRadiusSq
  congr 2
  exact Fintype.sum_equiv (canonicalProjectiveChartCoordinateEquiv d)
    (fun j => Complex.normSq (canonicalProjectiveChartCoordinates z j))
    (fun j => Complex.normSq (z j)) (by
      intro j
      rcases j with ⟨u | a, h⟩
      · exact False.elim (h (by cases u; rfl))
      · rfl)

/-- The concrete Jacobian defect used by the incidence formula is one at every
collision-free affine coordinate. -/
theorem coherentEigenpairProjectiveJacobianDefect_eq_one {d : ℕ}
    (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    coherentEigenpairProjectiveJacobianDefect i E z B hgap = 1 := by
  unfold coherentEigenpairProjectiveJacobianDefect
  rw [canonicalProjectiveAffineDensity_eq i]
  simpa [div_eq_mul_inv, mul_comm] using
    coherentEigenpairProjectiveCorrection_defect_eq_one i E z B hgap

/-- Correction-free physical chart density.  It displays the exact GUE
normalizer ratio, regression factor, crossing quadratic, affine projective
Haar density, and squared complementary gap determinant. -/
def physicalEigenpairExactDensity {d : ℕ} {n : Type*} [Fintype n]
    (i : Fin d) (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) : ℝ≥0∞ := by
  classical
  let y := eigenpairIncidenceCoordinates i x
  exact if (eigenpairGapMatrix y.1 y.2.2.1).det ≠ 0 then
    ENNReal.ofReal (coareaGaussianDensityConstant d t) *
      ENNReal.ofReal (canonicalGaussianRegressionFactor y.1 f t q) *
      ENNReal.ofReal (Real.exp
        (-hilbertSchmidtNormSq (y.2.2.1 - Fv) / (2 * t))) *
      ENNReal.ofReal (physicalEigenpairCrossingQuadratic T y.2.1) *
      ENNReal.ofReal (canonicalProjectiveAffineDensity y.2.1 *
        Complex.normSq (eigenpairGapMatrix y.1 y.2.2.1).det)
  else 0

/-- The projective correction defect disappears globally. -/
theorem physicalEigenpairExpandedDensity_eq_exact
    {d : ℕ} {n : Type*} [Fintype n]
    (i : Fin d) (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) :
    physicalEigenpairExpandedDensity i t f q Fv T x =
      physicalEigenpairExactDensity i t f q Fv T x := by
  classical
  unfold physicalEigenpairExpandedDensity physicalEigenpairExactDensity
  dsimp only
  split_ifs with hgap
  · rw [coherentEigenpairProjectiveJacobianDefect_eq_one i _ _ _ hgap]
    simp
  · rfl

/-- The fresh input to the exact conditional coarea assembly is the concrete
finite product of diagonal `N(0,t)` and strict-upper `N(0,t/2)` coordinates.
This restates the matrix-level Tonelli split at the exact variance dictated by
the physical parameters; no abstract Gaussian hypothesis is used. -/
theorem physicalConditionalCoareaExact_gaussianInput
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
  physicalConditionalGaussianSplit p hs0 hsc hsb exteriorLaw Φ hΦ

/-- Exact energy- and projective-dependent physical Schur density.  Unlike the
finite-cover formula below, every regression, compression, and crossing
factor here is the concrete function of `(H_R,C,V,E,z)` from
`PhysicalSchurCoareaData`; the correction factor is absent. -/
theorem physicalSchurCoareaDensity_eq_exact
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
          (eigenpairIncidenceCoordinates i x).2.2.1).det) := by
  rw [physicalSchurCoareaDensity_eq_explicit α R i t H_R C V x hrank hgap]
  rw [coherentEigenpairProjectiveJacobianDefect_eq_one i _ _ _ hgap]
  simp

/-- Exact correction-free finite-cover conditional coarea identity for an
arbitrary measurable phase-free ordered-projector observable.  The additive
inertia sector and collision-free hypothesis are carried by the concrete cover
sources. -/
theorem physicalConditionalCoareaExact_fixedExterior
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {dR d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : PhysicalCoareaPoleChartCover κ α R)
    {n : Type*} [Fintype n]
    (t f : ℝ) (q : Fin (d - 1) → ℂ)
    (Fv : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞)
    (hΨ : Measurable Ψ) :
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
          physicalEigenpairExactDensity (ofLex p).1 t f q Fv T x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [physicalConditionalCoarea_fixedExterior α R C t f q Fv T ρ Ψ hΨ]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro p _
  apply MeasureTheory.setLIntegral_congr_fun (C.source_measurable a r p)
  intro x _
  change physicalEigenpairExpandedDensity (ofLex p).1 t f q Fv T x *
      phaseFreeOrderedProjectorObservable ρ Ψ
        (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) =
    physicalEigenpairExactDensity (ofLex p).1 t f q Fv T x *
      phaseFreeOrderedProjectorObservable ρ Ψ
        (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)
  rw [physicalEigenpairExpandedDensity_eq_exact]

/-- The exact moving-root cover and correction-free fixed-exterior chart
identity, for the finite pole cover. -/
theorem physicalConditionalCoareaExact_globalCover
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
    (hΨ : Measurable Ψ) :
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
          physicalEigenpairExactDensity (ofLex p).1 t f q Fv T x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x)) := by
  refine ⟨(physicalConditionalCoarea_globalCover A V D hA hD α R C
    hpoleFree hloewner hsimple t f q Fv T ρ Ψ hΨ).1, ?_⟩
  exact physicalConditionalCoareaExact_fixedExterior
    α.val R C t f q Fv T ρ Ψ hΨ

end CoareaNative.BlockBand
