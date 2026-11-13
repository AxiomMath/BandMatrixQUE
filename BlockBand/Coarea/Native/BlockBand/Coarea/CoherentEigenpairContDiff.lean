module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveHouseholderSmooth
public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentEigenpairGlobalSmooth
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Continuous differentiability of the coherent eigenpair chart

The coherent affine-projective reconstruction, its Householder completion, the
moving-frame conjugation, and the selected-coordinate readback are `C¹` on
their whole finite-dimensional coordinate spaces.  In fact the proofs below
establish pointwise smoothness of every order before recording the global
`C¹` and continuous-`fderiv` interfaces needed by the inverse-function step.
All finite products are assembled on the coherent carriers, avoiding the
competing `PiLp` algebraic instance paths.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Normalized affine reconstruction is smooth at every coherent projective
coordinate. -/
theorem contDiffAt_coherentProjectiveUnitReconstruction
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    ContDiffAt ℝ ⊤ (coherentProjectiveUnitReconstruction k) z := by
  have hr : ContDiffAt ℝ ⊤ (projectiveEigenvectorReconstruction k) z.value := by
    apply contDiffAt_piLp' 2
    intro j
    simp only [projectiveEigenvectorReconstruction]
    split_ifs <;> fun_prop
  have hn : ContDiffAt ℝ ⊤
      (fun w : ProjectiveChartCoordinate k → ℂ =>
        ‖projectiveEigenvectorReconstruction k w‖) z.value :=
    hr.norm ℂ (projectiveEigenvectorReconstruction_ne_zero k z.value)
  have hi : ContDiffAt ℝ ⊤
      (fun w : ProjectiveChartCoordinate k → ℂ =>
        ‖projectiveEigenvectorReconstruction k w‖⁻¹) z.value :=
    hn.inv (norm_ne_zero_iff.mpr
      (projectiveEigenvectorReconstruction_ne_zero k z.value))
  have hbase : ContDiffAt ℝ ⊤ (projectiveUnitReconstruction k) z.value := by
    change ContDiffAt ℝ ⊤ (fun w : ProjectiveChartCoordinate k → ℂ =>
      ‖projectiveEigenvectorReconstruction k w‖⁻¹ •
        projectiveEigenvectorReconstruction k w) z.value
    exact hi.smul hr
  have hin := hbase.comp z (coherentProjectiveCoordinatesEquiv k).contDiff.contDiffAt
  have hout := (coherentUnitVectorEquiv ι).symm.contDiff.contDiffAt.comp z hin
  change ContDiffAt ℝ ⊤
    (fun w : CoherentProjectiveCoordinates k =>
      (⟨projectiveUnitReconstruction k w.value⟩ : CoherentUnitVector ι)) z
  convert hout using 1
  funext w
  rfl

/-- Every phase-fixed Householder entry is smooth at every coherent unit
vector whose selected denominator is nonzero. -/
theorem contDiffAt_coherentPhaseFixedHouseholderFrameEntry
    (k a b : ι) (v : CoherentUnitVector ι)
    (hden : 1 + (v.value k).re ≠ 0) :
    ContDiffAt ℝ ⊤ (coherentPhaseFixedHouseholderFrameEntry k a b) v := by
  rw [show coherentPhaseFixedHouseholderFrameEntry k a b =
      fun w : CoherentUnitVector ι => -(if a = b then 1 else 0) +
        (((1 + (w.value k).re)⁻¹ : ℝ) : ℂ) *
          (w.value a + phaseFixedCoordinateVector k a) *
          star (w.value b + phaseFixedCoordinateVector k b) by
    funext w
    rw [coherentPhaseFixedHouseholderFrameEntry,
      phaseFixedHouseholderFrame_apply]
    rfl]
  have hea (j : ι) : ContDiffAt ℝ ⊤
      (fun w : CoherentUnitVector ι => w.value j) v :=
    (coherentUnitEvaluationCLM j).contDiff.contDiffAt
  have hre := Complex.reCLM.contDiff.contDiffAt.comp v (hea k)
  have hdenom : ContDiffAt ℝ ⊤
      (fun w : CoherentUnitVector ι => 1 + (w.value k).re) v := by
    exact (contDiffAt_const (x := v) (c := (1 : ℝ))).add hre
  have hinv := hdenom.inv hden
  have hcoeff := Complex.ofRealCLM.contDiff.contDiffAt.comp v hinv
  have hleft : ContDiffAt ℝ ⊤
      (fun w : CoherentUnitVector ι =>
        w.value a + phaseFixedCoordinateVector k a) v := by
    fun_prop
  have hright : ContDiffAt ℝ ⊤
      (fun w : CoherentUnitVector ι =>
        star (w.value b + phaseFixedCoordinateVector k b)) v := by
    exact Complex.conjCLE.contDiff.contDiffAt.comp v
      ((hea b).add (contDiffAt_const (x := v)
        (c := phaseFixedCoordinateVector k b)))
  exact (contDiffAt_const (x := v)
    (c := (-(if a = b then (1 : ℂ) else 0)))).add
      ((hcoeff.mul hleft).mul hright)

/-- Every coherent projective Householder entry is smooth throughout the
whole affine chart. -/
theorem contDiffAt_coherentProjectiveHouseholderFrameEntry
    (k a b : ι) (z : CoherentProjectiveCoordinates k) :
    ContDiffAt ℝ ⊤
      (fun w : CoherentProjectiveCoordinates k =>
        coherentProjectiveHouseholderFrame k w a b) z := by
  have hden :
      1 + ((coherentProjectiveUnitReconstruction k z).value k).re ≠ 0 := by
    change 1 + (projectiveUnitReconstruction k z.value k).re ≠ 0
    have hpos := projectiveUnitReconstruction_self_re_pos k z.value
    linarith
  exact (contDiffAt_coherentPhaseFixedHouseholderFrameEntry
    k a b (coherentProjectiveUnitReconstruction k z) hden).comp z
      (contDiffAt_coherentProjectiveUnitReconstruction k z)

/-- The coherently packed Householder matrix is smooth at every affine
projective coordinate. -/
theorem contDiffAt_coherentProjectiveHouseholderMatrix
    (k : ι) (z : CoherentProjectiveCoordinates k) :
    ContDiffAt ℝ ⊤ (coherentProjectiveHouseholderMatrix k) z := by
  have hfun : ContDiffAt ℝ ⊤
      (fun w : CoherentProjectiveCoordinates k => fun ij : ι × ι =>
        coherentProjectiveHouseholderFrame k w ij.1 ij.2) z :=
    contDiffAt_pi.mpr fun ij =>
      contDiffAt_coherentProjectiveHouseholderFrameEntry k ij.1 ij.2 z
  let eR : EuclideanSpace ℂ (ι × ι) ≃L[ℝ] ((ι × ι) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv (ι × ι) ℂ).toLinearEquiv.restrictScalars ℝ)
  have heuclid : ContDiffAt ℝ ⊤
      (coherentProjectiveHouseholderEuclidean k) z := by
    have h := eR.symm.contDiff.contDiffAt.comp z hfun
    convert h using 1
    funext w
    rfl
  change ContDiffAt ℝ ⊤ (fun w =>
    (⟨coherentProjectiveHouseholderEuclidean k w⟩ :
      CoherentComplexMatrix ι)) z
  have h := (coherentAnalyticCarrierContinuousLinearEquiv
    (EuclideanSpace ℂ (ι × ι))).symm.contDiff.contDiffAt.comp z heuclid
  exact h

/-- The packed coherent Householder chart is globally `C¹`. -/
theorem contDiff_coherentProjectiveHouseholderMatrix (k : ι) :
    ContDiff ℝ 1 (coherentProjectiveHouseholderMatrix k) :=
  contDiff_iff_contDiffAt.mpr fun z =>
    (contDiffAt_coherentProjectiveHouseholderMatrix k z).of_le (by norm_num)

/-- Its explicit bundled derivative varies continuously over the whole affine
chart. -/
theorem continuous_fderiv_coherentProjectiveHouseholderMatrix (k : ι) :
    Continuous (fderiv ℝ (coherentProjectiveHouseholderMatrix k)) :=
  (contDiff_coherentProjectiveHouseholderMatrix k).continuous_fderiv (by norm_num)

/-- Equivalently, the explicit coherent matrix differential constructed from
the entry differentials varies continuously with the projective coordinate. -/
theorem continuous_coherentProjectiveHouseholderMatrixDifferentialAt (k : ι) :
    Continuous (fun z =>
      coherentProjectiveHouseholderMatrixDifferentialAt k z) := by
  rw [show (fun z =>
      coherentProjectiveHouseholderMatrixDifferentialAt k z) =
      fderiv ℝ (coherentProjectiveHouseholderMatrix k) from
    funext fun z => (fderiv_coherentProjectiveHouseholderMatrix k z).symm]
  exact continuous_fderiv_coherentProjectiveHouseholderMatrix k

/-- Coherent moving-frame conjugation is smooth at every point. -/
theorem contDiffAt_coherentEigenpairConjugation
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    ContDiffAt ℝ ⊤ (coherentEigenpairConjugation i) x := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  let P := coherentSelectedProjectiveInputCLM i
  have hHentry (a b : Unit ⊕ Fin (d - 1)) : ContDiffAt ℝ ⊤
      (fun y => coherentProjectiveHouseholderFrame e (P y) a b) x :=
    (contDiffAt_coherentProjectiveHouseholderFrameEntry e a b (P x)).comp
      x P.contDiff.contDiffAt
  have hD (a b : Unit ⊕ Fin (d - 1)) : ContDiffAt ℝ ⊤
      (fun y => coherentBlockDiagonalEntryCLM i a b y) x :=
    (coherentBlockDiagonalEntryCLM i a b).contDiff.contDiffAt
  have hstar (b c : Unit ⊕ Fin (d - 1)) : ContDiffAt ℝ ⊤
      (fun y => star (coherentProjectiveHouseholderFrame e (P y) b c)) x :=
    Complex.conjCLE.contDiff.contDiffAt.comp x (hHentry b c)
  have hentry (a b : Unit ⊕ Fin (d - 1)) : ContDiffAt ℝ ⊤
      (fun y =>
        let H := coherentProjectiveHouseholderFrame e (P y)
        let D := canonicalBlockDiagonalLinearMap
          (coherentSelectedBlockInputLinearMap i y)
        (H * D * Matrix.conjTranspose H) a b) x := by
    change ContDiffAt ℝ ⊤ (fun y => ∑ c, (∑ q,
      coherentProjectiveHouseholderFrame e (P y) a q *
        coherentBlockDiagonalEntryCLM i q c y) *
      star (coherentProjectiveHouseholderFrame e (P y) b c)) x
    fun_prop
  have hfun : ContDiffAt ℝ ⊤ (fun y => fun
      (ab : (Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) =>
      let H := coherentProjectiveHouseholderFrame e (P y)
      let D := canonicalBlockDiagonalLinearMap
        (coherentSelectedBlockInputLinearMap i y)
      (H * D * Matrix.conjTranspose H) ab.1 ab.2) x :=
    contDiffAt_pi.mpr fun ab => hentry ab.1 ab.2
  let eR : EuclideanSpace ℂ ((Unit ⊕ Fin (d - 1)) ×
      (Unit ⊕ Fin (d - 1))) ≃L[ℝ]
      (((Unit ⊕ Fin (d - 1)) × (Unit ⊕ Fin (d - 1))) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv _ ℂ).toLinearEquiv.restrictScalars ℝ)
  have heuclid : ContDiffAt ℝ ⊤
      (coherentEigenpairConjugationEuclidean i) x := by
    have h := eR.symm.contDiff.contDiffAt.comp x hfun
    convert h using 1
    funext y
    rfl
  change ContDiffAt ℝ ⊤ (fun y =>
    (⟨coherentEigenpairConjugationEuclidean i y⟩ :
      CoherentComplexMatrix (Unit ⊕ Fin (d - 1)))) x
  exact (coherentAnalyticCarrierContinuousLinearEquiv
    (EuclideanSpace ℂ ((Unit ⊕ Fin (d - 1)) ×
      (Unit ⊕ Fin (d - 1))))).symm.contDiff.contDiffAt.comp x heuclid

/-- Coherent moving-frame conjugation is globally `C¹`. -/
theorem contDiff_coherentEigenpairConjugation {d : ℕ} (i : Fin d) :
    ContDiff ℝ 1 (coherentEigenpairConjugation i) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    (contDiffAt_coherentEigenpairConjugation i x).of_le (by norm_num)

/-- The moving-frame conjugation derivative is continuous. -/
theorem continuous_fderiv_coherentEigenpairConjugation
    {d : ℕ} (i : Fin d) :
    Continuous (fderiv ℝ (coherentEigenpairConjugation i)) :=
  (contDiff_coherentEigenpairConjugation i).continuous_fderiv (by norm_num)

/-- Selected-coordinate readback is smooth at every coherent input. -/
theorem contDiffAt_coherentSelectedEigenpairDecode
    {d : ℕ} (i : Fin d) (x : CoherentHermitianCoordinates d) :
    ContDiffAt ℝ ⊤ (coherentSelectedEigenpairDecode i) x := by
  exact (coherentSelectedMatrixReadbackCLM i).contDiff.contDiffAt.comp x
    (contDiffAt_coherentEigenpairConjugation i x)

/-- The coherent selected decoder is globally `C¹`, discharging the analytic
premise of the coherent local inverse theorem. -/
theorem contDiff_coherentSelectedEigenpairDecode {d : ℕ} (i : Fin d) :
    ContDiff ℝ 1 (coherentSelectedEigenpairDecode i) :=
  contDiff_iff_contDiffAt.mpr fun x =>
    (contDiffAt_coherentSelectedEigenpairDecode i x).of_le (by norm_num)

/-- The selected readback decoder has a continuous bundled derivative. -/
theorem continuous_fderiv_coherentSelectedEigenpairDecode
    {d : ℕ} (i : Fin d) :
    Continuous (fderiv ℝ (coherentSelectedEigenpairDecode i)) :=
  (contDiff_coherentSelectedEigenpairDecode i).continuous_fderiv (by norm_num)

end CoareaNative.BlockBand
