module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EuclideanEigenpairSmoothChart

/-!
# Coherent analytic carriers for the eigenpair chart

Mathlib gives finite `Pi`/`WithLp` types two non-definitionally equal
routes to additive and module structures.  This module introduces a single
newtype used uniformly for real Hermitian coordinates, complex affine
projective coordinates, and complex unit vectors.  Its normed structures are
pulled back from the underlying space but expose only one algebraic hierarchy.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

/-- A typeclass-coherent analytic copy of a real normed space. -/
structure CoherentAnalyticCarrier (X : Type*) where
  value : X

/-- Underlying type equivalence. -/
def coherentAnalyticCarrierEquiv (X : Type*) :
    CoherentAnalyticCarrier X ≃ X where
  toFun := CoherentAnalyticCarrier.value
  invFun := CoherentAnalyticCarrier.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

noncomputable instance (X : Type*) [NormedAddCommGroup X] :
    NormedAddCommGroup (CoherentAnalyticCarrier X) := by
  let e := coherentAnalyticCarrierEquiv X
  letI : AddCommGroup (CoherentAnalyticCarrier X) := e.addCommGroup
  let ea : CoherentAnalyticCarrier X ≃+ X :=
    { e with map_add' := by intro x y; rfl }
  exact NormedAddCommGroup.induced _ _ ea ea.injective

noncomputable instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (CoherentAnalyticCarrier X) := by
  let e := coherentAnalyticCarrierEquiv X
  let ea : CoherentAnalyticCarrier X ≃+ X :=
    { e with map_add' := by intro x y; rfl }
  let m : Module ℝ (CoherentAnalyticCarrier X) := ea.module ℝ
  exact
    { toModule := m
      norm_smul_le := by
        intro c x
        change ‖c • x.value‖ ≤ ‖c‖ * ‖x.value‖
        exact norm_smul_le c x.value }

@[simp] theorem CoherentAnalyticCarrier.value_add
    {X : Type*} [NormedAddCommGroup X]
    (x y : CoherentAnalyticCarrier X) :
    (x + y).value = x.value + y.value := by rfl

@[simp] theorem CoherentAnalyticCarrier.value_smul
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c : ℝ) (x : CoherentAnalyticCarrier X) :
    (c • x).value = c • x.value := by rfl

/-- Real-linear equivalence with the underlying data. -/
def coherentAnalyticCarrierLinearEquiv
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    CoherentAnalyticCarrier X ≃ₗ[ℝ] X where
  toFun := CoherentAnalyticCarrier.value
  invFun := CoherentAnalyticCarrier.mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    FiniteDimensional ℝ (CoherentAnalyticCarrier X) :=
  (coherentAnalyticCarrierLinearEquiv X).symm.finiteDimensional

/-- Lift a real continuous linear map between possibly incoherent underlying
spaces to the coherent copies. -/
def coherentLiftCLM
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) :
    CoherentAnalyticCarrier X →L[ℝ] CoherentAnalyticCarrier Y :=
  let T : CoherentAnalyticCarrier X →ₗ[ℝ] CoherentAnalyticCarrier Y :=
    { toFun := fun x => ⟨L x.value⟩
      map_add' := by
        rintro ⟨x⟩ ⟨y⟩
        congr 1
        exact L.map_add x y
      map_smul' := by
        rintro c ⟨x⟩
        congr 1
        exact L.map_smul c x }
  T.toContinuousLinearMap

/-- Lift a function between underlying spaces. -/
def coherentLift {X Y : Type*} (f : X → Y) :
    CoherentAnalyticCarrier X → CoherentAnalyticCarrier Y :=
  fun x => ⟨f x.value⟩

/-- Coherent real Hermitian-coordinate carrier. -/
abbrev CoherentHermitianCoordinates (d : ℕ) :=
  CoherentAnalyticCarrier (HermitianCoordinateSpace d)

/-- Coherent complex affine-projective carrier. -/
abbrev CoherentProjectiveCoordinates {ι : Type*} (k : ι) :=
  CoherentAnalyticCarrier (ProjectiveChartCoordinate k → ℂ)

/-- Coherent complex unit-vector carrier. -/
abbrev CoherentUnitVector (ι : Type*) :=
  CoherentAnalyticCarrier (EuclideanSpace ℂ ι)

/-- Coherent finite complex square-matrix carrier. -/
abbrev CoherentComplexMatrix (ι : Type*) :=
  CoherentAnalyticCarrier (EuclideanSpace ℂ (ι × ι))

/-- Continuous linear equivalence from the coherent carrier to its underlying
finite-dimensional real normed space. -/
def coherentAnalyticCarrierContinuousLinearEquiv
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] :
    CoherentAnalyticCarrier X ≃L[ℝ] X :=
  (coherentAnalyticCarrierLinearEquiv X).toContinuousLinearEquiv

/-- Named continuous linear equivalence for coherent Hermitian coordinates. -/
def coherentHermitianCoordinatesEquiv (d : ℕ) :
    CoherentHermitianCoordinates d ≃L[ℝ] HermitianCoordinateSpace d :=
  coherentAnalyticCarrierContinuousLinearEquiv (HermitianCoordinateSpace d)

/-- Named continuous linear equivalence for coherent projective coordinates. -/
def coherentProjectiveCoordinatesEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι) :
    CoherentProjectiveCoordinates k ≃L[ℝ]
      (ProjectiveChartCoordinate k → ℂ) :=
  coherentAnalyticCarrierContinuousLinearEquiv
    (ProjectiveChartCoordinate k → ℂ)

/-- Named continuous linear equivalence for coherent unit vectors. -/
def coherentUnitVectorEquiv (ι : Type*) [Fintype ι] :
    CoherentUnitVector ι ≃L[ℝ] EuclideanSpace ℂ ι :=
  coherentAnalyticCarrierContinuousLinearEquiv (EuclideanSpace ℂ ι)

/-- Flatten a finite complex matrix into Euclidean coordinates. -/
def euclideanMatrixLinearEquiv (ι : Type*) [Fintype ι] :
    EuclideanSpace ℂ (ι × ι) ≃ₗ[ℝ] Matrix ι ι ℂ where
  toFun u i j := u (i, j)
  invFun A := WithLp.toLp 2 fun ij => A ij.1 ij.2
  left_inv u := by ext ij; rfl
  right_inv A := by ext i j; rfl
  map_add' u v := by ext i j; rfl
  map_smul' c u := by ext i j; rfl

/-- Named continuous linear equivalence from the coherent matrix carrier to
Mathlib's entrywise matrix topology. -/
def coherentComplexMatrixEquiv (ι : Type*) [Fintype ι] :
    CoherentComplexMatrix ι ≃L[ℝ] Matrix ι ι ℂ :=
  (coherentAnalyticCarrierContinuousLinearEquiv
    (EuclideanSpace ℂ (ι × ι))).trans
      (euclideanMatrixLinearEquiv ι).toContinuousLinearEquiv

@[simp] theorem coherentAnalyticCarrierContinuousLinearEquiv_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (x : CoherentAnalyticCarrier X) :
    coherentAnalyticCarrierContinuousLinearEquiv X x = x.value := by
  rfl

@[simp] theorem coherentAnalyticCarrierContinuousLinearEquiv_symm_apply
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (x : X) :
    (coherentAnalyticCarrierContinuousLinearEquiv X).symm x = ⟨x⟩ := by
  rfl

/-- Fréchet derivatives transport functorially to coherent carriers. -/
theorem hasFDerivAt_coherentLift
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {f : X → Y} {L : X →L[ℝ] Y} {x : X}
    (h : HasFDerivAt f L x) :
    HasFDerivAt (coherentLift f) (coherentLiftCLM L)
      (⟨x⟩ : CoherentAnalyticCarrier X) := by
  let eX := coherentAnalyticCarrierContinuousLinearEquiv X
  let eY := coherentAnalyticCarrierContinuousLinearEquiv Y
  have hin : HasFDerivAt (fun z : CoherentAnalyticCarrier X => f (eX z))
      (L.comp (eX : CoherentAnalyticCarrier X →L[ℝ] X)) ⟨x⟩ := by
    exact h.comp ⟨x⟩ eX.hasFDerivAt
  have hout := eY.symm.hasFDerivAt.comp (⟨x⟩ : CoherentAnalyticCarrier X) hin
  convert hout using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    rfl

/-- Transport only the output of a Fréchet derivative to the coherent copy. -/
theorem HasFDerivAt.coherentOutput
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {f : X → Y} {L : X →L[ℝ] Y} {x : X}
    (h : HasFDerivAt f L x) :
    HasFDerivAt (fun z => (⟨f z⟩ : CoherentAnalyticCarrier Y))
      ({ toFun := fun u => ⟨L u⟩
         map_add' := by intro u v; congr 1; exact L.map_add u v
         map_smul' := by intro c u; congr 1; exact L.map_smul c u } :
        X →ₗ[ℝ] CoherentAnalyticCarrier Y).toContinuousLinearMap x := by
  let eY := coherentAnalyticCarrierContinuousLinearEquiv Y
  have hout := eY.symm.hasFDerivAt.comp x h
  convert hout using 1
  · funext z
    rfl
  · apply ContinuousLinearMap.ext
    intro u
    rfl

section Projective

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Phase-fixed unit reconstruction between the coherent projective and unit
vector carriers. -/
def coherentProjectiveUnitReconstruction (k : ι) :
    CoherentProjectiveCoordinates k → CoherentUnitVector ι :=
  coherentLift (projectiveUnitReconstruction k)

/-- Coherent lift of complementary-coordinate tangent insertion. -/
def coherentProjectiveChartTangentInsertion (k : ι) :
    CoherentProjectiveCoordinates k →L[ℝ] CoherentUnitVector ι :=
  coherentLiftCLM (projectiveChartTangentInsertion k).toContinuousLinearMap

/-- The phase-fixed coherent unit reconstruction has the expected
Fréchet derivative at the affine-chart origin. -/
theorem hasFDerivAt_coherentProjectiveUnitReconstruction_zero (k : ι) :
    HasFDerivAt (coherentProjectiveUnitReconstruction k)
      (coherentProjectiveChartTangentInsertion k)
      (⟨0⟩ : CoherentProjectiveCoordinates k) := by
  simpa [coherentProjectiveUnitReconstruction,
    coherentProjectiveChartTangentInsertion] using
    hasFDerivAt_coherentLift
      (hasFDerivAt_projectiveUnitReconstruction_zero k)

/-- The phase-fixed Householder frame read from a coherent unit-vector
carrier. -/
def coherentPhaseFixedHouseholderFrame (k : ι) :
    CoherentUnitVector ι → Matrix ι ι ℂ :=
  fun v => phaseFixedHouseholderFrame k v.value

/-- The coherent projective chart followed by Householder completion. -/
def coherentProjectiveHouseholderFrame (k : ι) :
    CoherentProjectiveCoordinates k → Matrix ι ι ℂ :=
  fun z => phaseFixedHouseholderFrame k
    (coherentProjectiveUnitReconstruction k z).value

/-- The projective Householder differential with coherent source. -/
def coherentProjectiveHouseholderFrameDifferential (k : ι) :
    CoherentProjectiveCoordinates k →L[ℝ] Matrix ι ι ℂ :=
  (projectiveHouseholderFrameDifferential k).toContinuousLinearMap.comp
    (coherentAnalyticCarrierContinuousLinearEquiv
      (ProjectiveChartCoordinate k → ℂ) :
        CoherentProjectiveCoordinates k →L[ℝ]
          (ProjectiveChartCoordinate k → ℂ))

/-- Coordinate evaluation on the coherent unit-vector carrier. -/
def coherentUnitEvaluationCLM (j : ι) : CoherentUnitVector ι →L[ℝ] ℂ :=
  let T : CoherentUnitVector ι →ₗ[ℝ] ℂ :=
    { toFun := fun v => v.value j
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  T.toContinuousLinearMap

/-- Every coordinate of the nonlinear coherent projective unit chart has the
expected derivative at the affine origin. -/
theorem hasFDerivAt_coherentProjectiveUnitReconstruction_apply_zero
    (k j : ι) :
    HasFDerivAt (fun z : CoherentProjectiveCoordinates k =>
      (coherentProjectiveUnitReconstruction k z).value j)
      ((coherentUnitEvaluationCLM j).comp
        (coherentProjectiveChartTangentInsertion k))
      (⟨0⟩ : CoherentProjectiveCoordinates k) := by
  exact (coherentUnitEvaluationCLM j).hasFDerivAt.comp
    (⟨0⟩ : CoherentProjectiveCoordinates k)
    (hasFDerivAt_coherentProjectiveUnitReconstruction_zero k)

/-- Entrywise Householder completion on coherent unit vectors. -/
def coherentPhaseFixedHouseholderFrameEntry (k a b : ι) :
    CoherentUnitVector ι → ℂ :=
  fun v => phaseFixedHouseholderFrame k v.value a b

/-- Exact entry derivative of the Householder frame on the coherent
unit-vector carrier. -/
def coherentPhaseFixedHouseholderFrameEntryDifferential
    (k a b : ι) (v : CoherentUnitVector ι) :
    CoherentUnitVector ι →L[ℝ] ℂ :=
  let T : CoherentUnitVector ι →ₗ[ℝ] ℂ :=
    { toFun := fun u =>
        phaseFixedHouseholderAlgebraicDifferential k v.value u.value a b
      map_add' := by
        intro u w
        exact congrFun (congrFun
          ((phaseFixedHouseholderAlgebraicDifferential k v.value).map_add
            u.value w.value) a) b
      map_smul' := by
        intro c u
        exact congrFun (congrFun
          ((phaseFixedHouseholderAlgebraicDifferential k v.value).map_smul
            c u.value) a) b }
  T.toContinuousLinearMap

/-- The phase-fixed Householder formula is differentiable entrywise
on the coherent unit-vector carrier.  This is the scalar derivative interface
needed to continue the eigenpair-chart chain without giving the underlying
`EuclideanSpace` either of its competing additive instances. -/
theorem hasFDerivAt_coherentPhaseFixedHouseholderFrameEntry
    (k a b : ι) (v : CoherentUnitVector ι)
    (hden : 1 + (v.value k).re ≠ 0) :
    HasFDerivAt (coherentPhaseFixedHouseholderFrameEntry k a b)
      (coherentPhaseFixedHouseholderFrameEntryDifferential k a b v) v := by
  rw [show coherentPhaseFixedHouseholderFrameEntry k a b =
      fun w : CoherentUnitVector ι => -(if a = b then 1 else 0) +
        (((1 + (w.value k).re)⁻¹ : ℝ) : ℂ) *
          (w.value a + phaseFixedCoordinateVector k a) *
          star (w.value b + phaseFixedCoordinateVector k b) by
    funext w
    rw [coherentPhaseFixedHouseholderFrameEntry,
      phaseFixedHouseholderFrame_apply]
    rfl]
  have hea (j : ι) : HasFDerivAt
      (fun w : CoherentUnitVector ι => w.value j)
      (coherentUnitEvaluationCLM j) v :=
    (coherentUnitEvaluationCLM j).hasFDerivAt
  have hre := Complex.reCLM.hasFDerivAt.comp v (hea k)
  have hdenom : HasFDerivAt
      (fun w : CoherentUnitVector ι => 1 + (w.value k).re)
      (Complex.reCLM.comp (coherentUnitEvaluationCLM k)) v := by
    have h := (hasFDerivAt_const (1 : ℝ) v).add hre
    convert h using 1
    · funext w
      rfl
    · simp
  have hinv := (hasFDerivAt_inv hden).comp v hdenom
  have hcoeff := Complex.ofRealCLM.hasFDerivAt.comp v hinv
  have hleft := (hea a).add
    (hasFDerivAt_const (phaseFixedCoordinateVector k a) v)
  have hright := ((hea b).add
    (hasFDerivAt_const (phaseFixedCoordinateVector k b) v)).star
  apply ((hasFDerivAt_const
    (-(if a = b then (1 : ℂ) else 0)) v).add
      ((hcoeff.mul hleft).mul hright)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro u
  simp [coherentPhaseFixedHouseholderFrameEntryDifferential,
    coherentUnitEvaluationCLM,
    phaseFixedHouseholderAlgebraicDifferential,
    Matrix.vecMulVec_apply, phaseFixedHouseholderShift, smul_eq_mul]
  ring

/-- Entrywise differentiability corollary. -/
theorem differentiableAt_coherentPhaseFixedHouseholderFrameEntry
    (k a b : ι) (v : CoherentUnitVector ι)
    (hden : 1 + (v.value k).re ≠ 0) :
    DifferentiableAt ℝ (coherentPhaseFixedHouseholderFrameEntry k a b) v :=
  (hasFDerivAt_coherentPhaseFixedHouseholderFrameEntry k a b v hden).differentiableAt

/-- Householder completion flattened into Euclidean matrix entries. -/
def coherentProjectiveHouseholderEuclidean (k : ι) :
    CoherentProjectiveCoordinates k → EuclideanSpace ℂ (ι × ι) :=
  fun z => WithLp.toLp 2 fun ij =>
    coherentProjectiveHouseholderFrame k z ij.1 ij.2

/-- Exact Euclidean-entry differential of Householder completion. -/
def coherentProjectiveHouseholderEuclideanDifferential (k : ι) :
    CoherentProjectiveCoordinates k →L[ℝ] EuclideanSpace ℂ (ι × ι) :=
  ((LinearEquiv.toContinuousLinearEquiv
      ((EuclideanSpace.equiv (ι × ι) ℂ).symm.toLinearEquiv.restrictScalars ℝ)) :
    ((ι × ι) → ℂ) ≃L[ℝ] EuclideanSpace ℂ (ι × ι)).toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun ij =>
        let v0 : CoherentUnitVector ι :=
          coherentProjectiveUnitReconstruction k
            (⟨0⟩ : CoherentProjectiveCoordinates k)
        (coherentPhaseFixedHouseholderFrameEntryDifferential
          k ij.1 ij.2 v0).comp
            (coherentProjectiveChartTangentInsertion k))

/-- Householder completion with coherent matrix output. -/
def coherentProjectiveHouseholderMatrix (k : ι) :
    CoherentProjectiveCoordinates k → CoherentComplexMatrix ι :=
  fun z => ⟨coherentProjectiveHouseholderEuclidean k z⟩

/-- Coherent matrix-valued Householder differential. -/
def coherentProjectiveHouseholderMatrixDifferential (k : ι) :
    CoherentProjectiveCoordinates k →L[ℝ] CoherentComplexMatrix ι :=
  let T : CoherentProjectiveCoordinates k →ₗ[ℝ] CoherentComplexMatrix ι :=
    { toFun := fun u => ⟨coherentProjectiveHouseholderEuclideanDifferential k u⟩
      map_add' := by intro u v; congr 1; exact (coherentProjectiveHouseholderEuclideanDifferential k).map_add u v
      map_smul' := by intro c u; congr 1; exact (coherentProjectiveHouseholderEuclideanDifferential k).map_smul c u }
  T.toContinuousLinearMap

/-- The nonlinear projective Householder chart has a matrix-valued
Fréchet derivative at zero on coherent carriers. -/
theorem hasFDerivAt_coherentProjectiveHouseholderMatrix_zero (k : ι) :
    HasFDerivAt (coherentProjectiveHouseholderMatrix k)
      (coherentProjectiveHouseholderMatrixDifferential k)
      (⟨0⟩ : CoherentProjectiveCoordinates k) := by
  let z0 : CoherentProjectiveCoordinates k := ⟨0⟩
  let v0 := coherentProjectiveUnitReconstruction k z0
  have hv : 1 + (v0.value k).re ≠ 0 := by
    simp only [v0, z0, coherentProjectiveUnitReconstruction, coherentLift]
    rw [show projectiveUnitReconstruction k 0 = projectiveSelectedVector k by simp]
    change 1 + (projectiveEigenvectorReconstruction k 0 k).re ≠ 0
    simp
  have hentry (ij : ι × ι) : HasFDerivAt
      (fun z : CoherentProjectiveCoordinates k =>
        coherentProjectiveHouseholderFrame k z ij.1 ij.2)
      ((coherentPhaseFixedHouseholderFrameEntryDifferential
          k ij.1 ij.2 v0).comp
        (coherentProjectiveChartTangentInsertion k)) z0 := by
    have hf := hasFDerivAt_coherentPhaseFixedHouseholderFrameEntry
      k ij.1 ij.2 v0 hv
    exact hf.comp z0
      (hasFDerivAt_coherentProjectiveUnitReconstruction_zero k)
  have hfun := hasFDerivAt_pi.mpr hentry
  have heuclid : HasFDerivAt (coherentProjectiveHouseholderEuclidean k)
      (coherentProjectiveHouseholderEuclideanDifferential k) z0 := by
    let eR : EuclideanSpace ℂ (ι × ι) ≃L[ℝ] ((ι × ι) → ℂ) :=
      LinearEquiv.toContinuousLinearEquiv
        ((EuclideanSpace.equiv (ι × ι) ℂ).toLinearEquiv.restrictScalars ℝ)
    apply (eR.comp_hasFDerivAt_iff).mp
    convert hfun using 1
    · funext z ij
      rfl
    · apply ContinuousLinearMap.ext
      intro u
      rfl
  convert HasFDerivAt.coherentOutput heuclid using 1
  · rfl
  · rfl

/-- Each Householder-frame entry along the coherent nonlinear projective chart
has a Fréchet derivative at the chart origin. -/
theorem hasFDerivAt_coherentProjectiveHouseholderFrameEntry_zero
    (k a b : ι) :
    HasFDerivAt (fun z : CoherentProjectiveCoordinates k =>
      coherentPhaseFixedHouseholderFrameEntry k a b
        (coherentProjectiveUnitReconstruction k z))
      (fderiv ℝ (fun z : CoherentProjectiveCoordinates k =>
        coherentPhaseFixedHouseholderFrameEntry k a b
          (coherentProjectiveUnitReconstruction k z))
        (⟨0⟩ : CoherentProjectiveCoordinates k))
      (⟨0⟩ : CoherentProjectiveCoordinates k) := by
  have hv : 1 + ((coherentProjectiveUnitReconstruction k
      (⟨0⟩ : CoherentProjectiveCoordinates k)).value k).re ≠ 0 := by
    simp only [coherentProjectiveUnitReconstruction, coherentLift]
    rw [show projectiveUnitReconstruction k 0 = projectiveSelectedVector k by simp]
    change 1 + (projectiveEigenvectorReconstruction k 0 k).re ≠ 0
    simp
  have hf := differentiableAt_coherentPhaseFixedHouseholderFrameEntry
    k a b (coherentProjectiveUnitReconstruction k
      (⟨0⟩ : CoherentProjectiveCoordinates k)) hv
  exact (hf.comp (⟨0⟩ : CoherentProjectiveCoordinates k)
    (hasFDerivAt_coherentProjectiveUnitReconstruction_zero k).differentiableAt).hasFDerivAt

end Projective

end CoareaNative.BlockBand
