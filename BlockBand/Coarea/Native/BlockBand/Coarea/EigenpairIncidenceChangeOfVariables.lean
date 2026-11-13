module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ConcreteEigenpairSmoothAtlas
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairGlobalDeterminant
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairSmoothCharts

/-!
# Fixed-rank eigenpair incidence change of variables

The concrete ordered-eigenpair atlas gives exact two-sided algebraic
charts and a globally `C¹` decoder.  This module proves the following measure
theorem: on every measurable injectivity piece of a fixed-rank concrete chart,
change of variables holds with an explicit density containing

`(1 + ∑ ‖z_j‖²)⁻ᵈ · det(E I - B)²`

and a completely defined correction defect.  The defect is the ratio of the
correction determinant to the affine projective density; it is defined
explicitly, not assumed.  It equals one
(`coherentEigenpairProjectiveCorrection_defect_eq_one`).  The theorems take any
measurable piece; the full chart source is measurable
(`measurableSet_selectedOrderedEigenpairChartSource_complete`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal

/-- The affine projective density in the canonical selected-first indexing. -/
def canonicalProjectiveAffineDensity {d : ℕ} (z : Fin (d - 1) → ℂ) : ℝ :=
  projectiveAffineDensity (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1))
    (canonicalProjectiveChartCoordinates z)

/-- The explicit defect between the moving-frame correction determinant
and the expected affine projective density.  It is defined from the
Fréchet derivative, not supplied as an input. -/
def coherentEigenpairProjectiveJacobianDefect {d : ℕ} (i : Fin d)
    (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) : ℝ :=
  |LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap)| /
    canonicalProjectiveAffineDensity z

/-- The affine projective density is strictly positive at every chart
coordinate, so the correction defect loses no information. -/
theorem canonicalProjectiveAffineDensity_pos {d : ℕ}
    (z : Fin (d - 1) → ℂ) :
    0 < canonicalProjectiveAffineDensity z := by
  unfold canonicalProjectiveAffineDensity projectiveAffineDensity
  have hsum : 0 ≤ ∑ j : ProjectiveChartCoordinate
      (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)),
      Complex.normSq (canonicalProjectiveChartCoordinates z j) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hr : 0 < projectiveAffineRadiusSq
      (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1))
      (canonicalProjectiveChartCoordinates z) := by
    unfold projectiveAffineRadiusSq
    linarith
  positivity

/-- Exact arbitrary-coordinate determinant factorization with the correct
affine projective density displayed explicitly.  The final defect is concrete;
the expected formula is the specialization where it is proved to be
one. -/
theorem abs_det_fderiv_coherentSelectedEigenpairDecode_eq_projective_gap_defect
    {d : ℕ} (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    |LinearMap.det ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap)| =
      canonicalProjectiveAffineDensity z *
        eigenpairLocalRealJacobianDensity E B.1 *
          coherentEigenpairProjectiveJacobianDefect i E z B hgap := by
  rw [abs_det_fderiv_coherentSelectedEigenpairDecode_factorization
    i E z B hgap]
  unfold coherentEigenpairProjectiveJacobianDefect
  have hp : canonicalProjectiveAffineDensity z ≠ 0 :=
    (canonicalProjectiveAffineDensity_pos z).ne'
  field_simp

/-- Block coordinates extracted from an arbitrary finite Hermitian
coordinate parameter. -/
def eigenpairIncidenceCoordinates {d : ℕ} (i : Fin d)
    (x : HermitianCoordinateSpace d) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  selectedEigenpairFinCoordinateLinearEquiv i x

/-- Total fixed-chart incidence density.  On the collision-free locus it is the
affine projective factor times the squared gap factor and the explicit defect;
on the collision locus it is set to zero. -/
def eigenpairIncidenceDensity {d : ℕ} (i : Fin d)
    (x : HermitianCoordinateSpace d) : ℝ := by
  let y := eigenpairIncidenceCoordinates i x
  classical
  exact if hgap : (eigenpairGapMatrix y.1 y.2.2.1).det ≠ 0 then
    canonicalProjectiveAffineDensity y.2.1 *
      eigenpairLocalRealJacobianDensity y.1 y.2.2.1 *
        coherentEigenpairProjectiveJacobianDefect i y.1 y.2.1 y.2.2 hgap
  else 0

/-- The finite-coordinate decoder is the coherent decoder conjugated by the
canonical continuous-linear equivalence. -/
theorem selectedEigenpairFinCoordinateChartDecode_eq_coherent_conjugation
    {d : ℕ} (i : Fin d) (x : HermitianCoordinateSpace d) :
    selectedEigenpairFinCoordinateChartDecode i x =
      coherentHermitianCoordinatesEquiv d
        (coherentSelectedEigenpairDecode i
          ((coherentHermitianCoordinatesEquiv d).symm x)) := by
  rw [coherentSelectedEigenpairDecode_eq_finiteCoordinateDecode]
  rfl

/-- The concrete finite-coordinate decoder is differentiable everywhere. -/
theorem differentiableAt_selectedEigenpairFinCoordinateChartDecode
    {d : ℕ} (i : Fin d) (x : HermitianCoordinateSpace d) :
    DifferentiableAt ℝ (selectedEigenpairFinCoordinateChartDecode i) x := by
  rw [show selectedEigenpairFinCoordinateChartDecode i =
      fun y => coherentHermitianCoordinatesEquiv d
        (coherentSelectedEigenpairDecode i
          ((coherentHermitianCoordinatesEquiv d).symm y)) by
    funext y
    exact selectedEigenpairFinCoordinateChartDecode_eq_coherent_conjugation i y]
  exact (coherentHermitianCoordinatesEquiv d).differentiableAt.comp x
    ((differentiableAt_coherentSelectedEigenpairDecode i
      ((coherentHermitianCoordinatesEquiv d).symm x)).comp x
        (coherentHermitianCoordinatesEquiv d).symm.differentiableAt)

/-- Conjugation through the coherent carrier does not change the real absolute
Jacobian determinant of the finite-coordinate decoder. -/
theorem abs_det_fderiv_selectedEigenpairFinCoordinateChartDecode
    {d : ℕ} (i : Fin d) (x : HermitianCoordinateSpace d) :
    |LinearMap.det ((fderiv ℝ (selectedEigenpairFinCoordinateChartDecode i) x).toLinearMap)| =
      |LinearMap.det ((fderiv ℝ (coherentSelectedEigenpairDecode i)
        ((coherentHermitianCoordinatesEquiv d).symm x)).toLinearMap)| := by
  let e := coherentHermitianCoordinatesEquiv d
  let L := fderiv ℝ (coherentSelectedEigenpairDecode i) (e.symm x)
  have hfinite : HasFDerivAt (selectedEigenpairFinCoordinateChartDecode i)
      (e.toContinuousLinearMap.comp (L.comp e.symm.toContinuousLinearMap)) x := by
    rw [show selectedEigenpairFinCoordinateChartDecode i =
        fun y => e (coherentSelectedEigenpairDecode i (e.symm y)) by
      funext y
      exact selectedEigenpairFinCoordinateChartDecode_eq_coherent_conjugation i y]
    exact e.hasFDerivAt.comp x
      ((differentiableAt_coherentSelectedEigenpairDecode i (e.symm x)).hasFDerivAt.comp
        x e.symm.hasFDerivAt)
  rw [hfinite.fderiv]
  have hdet : LinearMap.det
      (e.toLinearEquiv.toLinearMap.comp
        (L.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)) =
      LinearMap.det L.toLinearMap := by
    have h := LinearMap.det_conj L.toLinearMap e.toLinearEquiv
    rw [← h]
    congr 1
  change
    |LinearMap.det
      (e.toLinearEquiv.toLinearMap.comp
        (L.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap))| =
      |LinearMap.det L.toLinearMap|
  rw [hdet]

/-- Off the complementary collision set, the finite-coordinate incidence
density is exactly the absolute determinant of the decoder derivative. -/
theorem eigenpairIncidenceDensity_eq_abs_det_fderiv
    {d : ℕ} (i : Fin d) (x : HermitianCoordinateSpace d)
    (hgap : (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0) :
    eigenpairIncidenceDensity i x =
      |LinearMap.det ((fderiv ℝ
        (selectedEigenpairFinCoordinateChartDecode i) x).toLinearMap)| := by
  let y := eigenpairIncidenceCoordinates i x
  have hx : coherentEigenpairGlobalInput i y.1 y.2.1 y.2.2 =
      (coherentHermitianCoordinatesEquiv d).symm x := by
    apply (coherentSelectedBlockCoordinateLinearEquiv i).injective
    change (coherentSelectedBlockCoordinateLinearEquiv i)
      (coherentEigenpairGlobalInput i y.1 y.2.1 y.2.2) = y
    exact (coherentSelectedBlockCoordinateLinearEquiv i).apply_symm_apply y
  rw [eigenpairIncidenceDensity]
  simp only [dite_eq_left hgap]
  rw [← abs_det_fderiv_coherentSelectedEigenpairDecode_eq_projective_gap_defect
    i y.1 y.2.1 y.2.2 hgap, hx,
    abs_det_fderiv_selectedEigenpairFinCoordinateChartDecode]

/-- On the fixed-rank chart source, the concrete finite-coordinate
decoder is injective.  This follows from the two-sided concrete atlas. -/
theorem injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d) :
    Set.InjOn
      (selectedEigenpairFinCoordinateChartDecode (ofLex p).1)
      {x : HermitianCoordinateSpace d |
        eigenpairIncidenceCoordinates (ofLex p).1 x ∈
          selectedOrderedEigenpairChartSource r p} := by
  intro x hx y hy hxy
  rcases hx with ⟨X, hX, hXenc⟩
  rcases hy with ⟨Y, hY, hYenc⟩
  change selectedOrderedEigenpairChartEncode r p X =
    selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1 x at hXenc
  change selectedOrderedEigenpairChartEncode r p Y =
    selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1 y at hYenc
  have hxparam : x =
      (selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1).symm
        (selectedOrderedEigenpairChartEncode r p X) := by
    rw [hXenc]
    exact (selectedEigenpairFinCoordinateLinearEquiv
      (ofLex p).1).symm_apply_apply x |>.symm
  have hyparam : y =
      (selectedEigenpairFinCoordinateLinearEquiv (ofLex p).1).symm
        (selectedOrderedEigenpairChartEncode r p Y) := by
    rw [hYenc]
    exact (selectedEigenpairFinCoordinateLinearEquiv
      (ofLex p).1).symm_apply_apply y |>.symm
  have hdecodeX :
      selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x = X.1 := by
    have h := coherentSelectedEigenpairDecode_encoded r p X hX
    rw [coherentSelectedEigenpairDecode_eq_finiteCoordinateDecode] at h
    have hv := congrArg CoherentAnalyticCarrier.value h
    simpa [hxparam] using hv
  have hdecodeY :
      selectedEigenpairFinCoordinateChartDecode (ofLex p).1 y = Y.1 := by
    have h := coherentSelectedEigenpairDecode_encoded r p Y hY
    rw [coherentSelectedEigenpairDecode_eq_finiteCoordinateDecode] at h
    have hv := congrArg CoherentAnalyticCarrier.value h
    simpa [hyparam] using hv
  have hXY : X = Y := by
    apply Subtype.ext
    rw [← hdecodeX, ← hdecodeY, hxy]
  subst Y
  rw [hxparam, hyparam]

/-- Exact measure-level chart formula on any measurable, collision-free
injectivity piece of the concrete selected decoder.  Such pieces are what the
local inverse theorem supplies.  The affine projective density is visibly
inside the integral through `eigenpairIncidenceDensity`; no global coverage or
change-of-variables assertion is postulated. -/
theorem lintegral_image_selectedEigenpairFinCoordinateChartDecode_incidence
    {d : ℕ} (i : Fin d) (s : Set (HermitianCoordinateSpace d))
    (hs : MeasurableSet s)
    (hinj : Set.InjOn (selectedEigenpairFinCoordinateChartDecode i) s)
    (hgap : ∀ x ∈ s, (eigenpairGapMatrix
      (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in selectedEigenpairFinCoordinateChartDecode i '' s, g K) =
      ∫⁻ x in s, ENNReal.ofReal (eigenpairIncidenceDensity i x) *
        g (selectedEigenpairFinCoordinateChartDecode i x) := by
  calc
    (∫⁻ K in selectedEigenpairFinCoordinateChartDecode i '' s, g K) =
        ∫⁻ x in s,
          ENNReal.ofReal
            |LinearMap.det ((fderiv ℝ
              (selectedEigenpairFinCoordinateChartDecode i) x).toLinearMap)| *
              g (selectedEigenpairFinCoordinateChartDecode i x) := by
      exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        hs (fun x _ =>
          (differentiableAt_selectedEigenpairFinCoordinateChartDecode i x).hasFDerivAt.hasFDerivWithinAt)
        hinj g
    _ = ∫⁻ x in s, ENNReal.ofReal (eigenpairIncidenceDensity i x) *
        g (selectedEigenpairFinCoordinateChartDecode i x) := by
      apply MeasureTheory.setLIntegral_congr_fun hs
      intro x hx
      change
        ENNReal.ofReal
            |LinearMap.det ((fderiv ℝ
              (selectedEigenpairFinCoordinateChartDecode i) x).toLinearMap)| *
              g (selectedEigenpairFinCoordinateChartDecode i x) =
          ENNReal.ofReal (eigenpairIncidenceDensity i x) *
            g (selectedEigenpairFinCoordinateChartDecode i x)
      rw [eigenpairIncidenceDensity_eq_abs_det_fderiv i x (hgap x hx)]

/-- Fixed-rank concrete-chart specialization: `s` is any measurable
collision-free piece whose incidence coordinates lie in the chart source.
Injectivity is discharged by the concrete atlas inverse identities. -/
theorem lintegral_fixedRankEigenpairIncidence_chart
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
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex p).1 '' s, g K) =
      ∫⁻ x in s,
        ENNReal.ofReal (eigenpairIncidenceDensity (ofLex p).1 x) *
          g (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  exact lintegral_image_selectedEigenpairFinCoordinateChartDecode_incidence
    (ofLex p).1 s hs
    ((injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource r p).mono
      hsource)
    hgap g

end CoareaNative.BlockBand
