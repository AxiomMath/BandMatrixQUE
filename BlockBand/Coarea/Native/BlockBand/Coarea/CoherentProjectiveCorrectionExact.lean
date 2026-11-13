module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveCorrectionEntryShear

/-!
# Exact arbitrary-chart determinant of the coherent projective correction

At an arbitrary affine projective coordinate `z`, the derivative of
`coherentSelectedEigenpairDecode` is `H (D' + A D - D A) Hᴴ`, where `H` is the
phase-fixed Householder frame at `z` (Hermitian and unitary), `D = diag(E,B)`
and `A = Hᴴ H'` is the skew-Hermitian frame connection.  In selected block
coordinates, `D' + A D - D A` factors exactly as

`gap(E,B) ∘ diag(1, T_z, 1) ∘ (complement shear)`,

where `T_z u = s (-u + s²/(1+s) · z ⟨z,u⟩)`, `s = (1 + |z|²)^{-1/2}`, is the
projective column of `A` (computed from `H e = v` and `Hᴴ H = 1`), whose real
determinant is `(1 + |z|²)^{-d}`.  Conjugation by the Hermitian unitary `H`
has absolute determinant one.  Consequently the absolute Jacobian is the
affine projective density times `|det (E I - B)|²` for every `z`, and the
defect of the canonical projective correction is exactly one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

/-- A unipotent shear `(x, y) ↦ (x, y + g x)` of a product has determinant one. -/
theorem det_prodShear_eq_one {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [Module.Free ℝ X] [Module.Finite ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [Module.Free ℝ Y] [Module.Finite ℝ Y]
    (g : X →ₗ[ℝ] Y) :
    LinearMap.det ((LinearMap.id : X × Y →ₗ[ℝ] X × Y) +
      (LinearMap.inr ℝ X Y).comp (g.comp (LinearMap.fst ℝ X Y))) = 1 := by
  classical
  let bX := Module.Free.chooseBasis ℝ X
  let bY := Module.Free.chooseBasis ℝ Y
  rw [← LinearMap.det_toMatrix (bX.prod bY)]
  have hM : LinearMap.toMatrix (bX.prod bY) (bX.prod bY)
      ((LinearMap.id : X × Y →ₗ[ℝ] X × Y) +
        (LinearMap.inr ℝ X Y).comp (g.comp (LinearMap.fst ℝ X Y))) =
      Matrix.fromBlocks 1 0
        (Matrix.of fun a b => bY.repr (g (bX b)) a) 1 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply,
        eq_comm, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [hM, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one,
    mul_one]

section TangentDeterminant

/-- Householder tangent map u ↦ s·(-u + c z ⟨z,u⟩), c = s²/(1+s). -/
def projectiveHouseholderTangentMap {n : ℕ} (s : ℝ) (z : Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun u := fun j => (s : ℂ) * (-u j +
    (((1 + s)⁻¹ * s ^ 2 : ℝ) : ℂ) * z j * ∑ k, star (z k) * u k)
  map_add' := by
    intro u v
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro r u
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
    simp only [mul_neg, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro k _; ring

/-- The Householder tangent map is the real restriction of the complex matrix
`(-s) • (1 + vecMulVec (-c • z) (star z))`, with `c = s²/(1+s)`. -/
theorem projectiveHouseholderTangentMap_eq {n : ℕ} (s : ℝ) (z : Fin n → ℂ) :
    projectiveHouseholderTangentMap s z =
      (Matrix.toLin' ((-(s : ℂ)) • (1 + vecMulVec (-((((1 + s)⁻¹ * s ^ 2 : ℝ) : ℂ)) • z)
        (star z)))).restrictScalars ℝ := by
  refine LinearMap.ext fun u => funext fun j => ?_
  simp only [projectiveHouseholderTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.coe_restrictScalars, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.mul_sum]
  simp only [mul_add, mul_neg, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib,
    neg_neg]
  congr 1
  apply Finset.sum_congr rfl; intro k _; ring

theorem det_projectiveHouseholderTangentMap {n : ℕ} (s : ℝ) (z : Fin n → ℂ)
    (hs : 0 < s) (hsz : s ^ 2 * (1 + ∑ j, Complex.normSq (z j)) = 1) :
    LinearMap.det (projectiveHouseholderTangentMap s z) =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ (n + 1) := by
  set N := ∑ j, Complex.normSq (z j) with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  rw [projectiveHouseholderTangentMap_eq, LinearMap.det_restrictScalars, LinearMap.det_toLin',
    Matrix.det_smul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
    Algebra.norm_complex_apply, Fintype.card_fin]
  have hdot : (star z) ⬝ᵥ (-((((1 + s)⁻¹ * s ^ 2 : ℝ) : ℂ)) • z)
      = ((-((1 + s)⁻¹ * s ^ 2 * N) : ℝ) : ℂ) := by
    rw [dotProduct_smul, hN]
    simp only [dotProduct, Pi.star_apply, smul_eq_mul]
    push_cast
    rw [neg_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  have hinv : (1 + N)⁻¹ = s ^ 2 :=
    (mul_eq_one_iff_inv_eq₀ (by positivity)).1 (by linarith)
  have hc : 1 + -((1 + s)⁻¹ * s ^ 2 * N) = s := by
    have h1 : s ^ 2 * N = 1 - s ^ 2 := by linarith
    have hs1 : (1 + s) ≠ 0 := by positivity
    rw [mul_assoc, h1]
    field_simp
    ring
  rw [hdot, ← Complex.ofReal_one, ← Complex.ofReal_add, hc, ← Complex.ofReal_neg,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.normSq_ofReal, hinv, ← pow_two,
    mul_pow, ← pow_mul, Even.neg_pow ⟨n, by ring⟩]
  ring

end TangentDeterminant

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The phase-fixed Householder frame is Hermitian. -/
theorem phaseFixedHouseholderFrame_conjTranspose (k : ι) (v : ι → ℂ) :
    (phaseFixedHouseholderFrame k v)ᴴ = phaseFixedHouseholderFrame k v := by
  ext a b
  rw [Matrix.conjTranspose_apply, phaseFixedHouseholderFrame_apply,
    phaseFixedHouseholderFrame_apply]
  by_cases hab : a = b
  · subst hab
    simp only [ite_true, star_add, star_neg, star_one, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab]
    simp only [star_add, star_neg, star_zero, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring

/-- The coherent projective Householder frame is the phase-fixed frame of the
unit affine reconstruction. -/
theorem coherentProjectiveHouseholderFrame_eq (k : ι)
    (w : CoherentProjectiveCoordinates k) :
    coherentProjectiveHouseholderFrame k w =
      phaseFixedHouseholderFrame k (projectiveUnitReconstruction k w.value) :=
  rfl

/-- The coherent projective Householder frame is unitary at every affine
coordinate. -/
theorem coherentProjectiveHouseholderFrame_conjTranspose_mul (k : ι)
    (w : CoherentProjectiveCoordinates k) :
    (coherentProjectiveHouseholderFrame k w)ᴴ *
      coherentProjectiveHouseholderFrame k w = 1 := by
  rw [coherentProjectiveHouseholderFrame_eq]
  apply phaseFixedHouseholderFrame_unitary
  · exact norm_projectiveUnitReconstruction k w.value
  · rw [projectiveUnitReconstruction_apply_self, Complex.ofReal_re]
  · exact projectiveUnitReconstruction_self_re_pos k w.value

/-- The coherent projective Householder frame is Hermitian. -/
theorem coherentProjectiveHouseholderFrame_conjTranspose (k : ι)
    (w : CoherentProjectiveCoordinates k) :
    (coherentProjectiveHouseholderFrame k w)ᴴ =
      coherentProjectiveHouseholderFrame k w :=
  phaseFixedHouseholderFrame_conjTranspose k _

/-- Right unitarity of the coherent projective Householder frame. -/
theorem coherentProjectiveHouseholderFrame_mul_conjTranspose (k : ι)
    (w : CoherentProjectiveCoordinates k) :
    coherentProjectiveHouseholderFrame k w *
      (coherentProjectiveHouseholderFrame k w)ᴴ = 1 :=
  mul_eq_one_comm.mp
    (coherentProjectiveHouseholderFrame_conjTranspose_mul k w)

/-- The distinguished column of the frame is the unit affine reconstruction. -/
theorem coherentProjectiveHouseholderFrame_apply_col (k a : ι)
    (w : CoherentProjectiveCoordinates k) :
    coherentProjectiveHouseholderFrame k w a k =
      projectiveUnitReconstruction k w.value a := by
  have h := phaseFixedHouseholderFrame_mulVec_coordinate k
    (projectiveUnitReconstruction k w.value)
    (by rw [projectiveUnitReconstruction_apply_self, Complex.ofReal_re])
    (by
      have := projectiveUnitReconstruction_self_re_pos k w.value
      linarith)
  have h2 := congrFun h a
  rw [phaseFixedCoordinateVector, Matrix.mulVec_single_one] at h2
  exact h2

end Frame

section Derivative

variable {d : ℕ} (i : Fin d)

/-- The coherent Householder frame along a selected Hermitian input. -/
def coherentEigenpairFrameAt (y : CoherentHermitianCoordinates d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  coherentProjectiveHouseholderFrame (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i y)

/-- The matrix of the Householder-frame differential at `x` in the
direction `u`. -/
def coherentEigenpairFrameDerivAt (x u : CoherentHermitianCoordinates d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  fun a b => coherentEigenpairHouseholderEntryDifferentialAt i x a b u

/-- Differentiating `Hᴴ H = 1`: the frame derivative is infinitesimally
unitary. -/
theorem coherentEigenpairFrameDerivAt_skew (x u : CoherentHermitianCoordinates d) :
    (coherentEigenpairFrameDerivAt i x u)ᴴ * coherentEigenpairFrameAt i x +
      (coherentEigenpairFrameAt i x)ᴴ * coherentEigenpairFrameDerivAt i x u = 0 := by
  ext a b
  have hH (p q : Unit ⊕ Fin (d - 1)) :=
    hasFDerivAt_coherentEigenpairHouseholderEntry_global i x p q
  have hf := HasFDerivAt.sum (u := Finset.univ) (x := x) fun c _ =>
    (hH c a).star.mul (hH c b)
  have hf2 := hf.congr_of_eventuallyEq (f₁ := fun _ : CoherentHermitianCoordinates d =>
      (1 : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) a b) (by
    filter_upwards with y
    rw [← coherentProjectiveHouseholderFrame_conjTranspose_mul
      (Sum.inl Unit.unit) (coherentSelectedProjectiveInputCLM i y)]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_apply])
  have h0 := congrArg (fun L => L u) (hf2.unique (hasFDerivAt_const _ x))
  simp only [FunLike.coe_sum, Finset.sum_apply,
    _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply,
    _root_.zero_apply, smul_eq_mul] at h0
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.zero_apply, coherentEigenpairFrameDerivAt, coherentEigenpairFrameAt,
    ← Finset.sum_add_distrib]
  rw [← h0]
  apply Finset.sum_congr rfl
  intro c _
  simp
  ring

/-- Inverse affine radius `‖(1,z)‖⁻¹` along a selected input. -/
def coherentEigenpairInvRadius (y : CoherentHermitianCoordinates d) : ℝ :=
  ‖projectiveEigenvectorReconstruction (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i y).value‖⁻¹

/-- Coordinates of the affine representative `(1,z)` along a selected input. -/
def coherentEigenpairAffinePoint (c : Unit ⊕ Fin (d - 1))
    (y : CoherentHermitianCoordinates d) : ℂ :=
  projectiveEigenvectorReconstruction (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i y).value c

/-- The (linear) variation of the affine representative `(1,z)`. -/
def coherentEigenpairAffineDirectionCLM (c : Unit ⊕ Fin (d - 1)) :
    CoherentHermitianCoordinates d →L[ℝ] ℂ :=
  if h : c = Sum.inl Unit.unit then 0 else
    (ContinuousLinearMap.proj (⟨c, h⟩ : ProjectiveChartCoordinate
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)))).comp
      ((coherentProjectiveCoordinatesEquiv
          (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1))).toContinuousLinearMap.comp
        (coherentSelectedProjectiveInputCLM i))

theorem hasFDerivAt_coherentEigenpairAffinePoint (c : Unit ⊕ Fin (d - 1))
    (x : CoherentHermitianCoordinates d) :
    HasFDerivAt (coherentEigenpairAffinePoint i c)
      (coherentEigenpairAffineDirectionCLM i c) x := by
  by_cases h : c = Sum.inl Unit.unit
  · subst h
    have hfun : coherentEigenpairAffinePoint i (Sum.inl Unit.unit) = fun _ => 1 := by
      funext y
      simp [coherentEigenpairAffinePoint]
    rw [hfun]
    simpa [coherentEigenpairAffineDirectionCLM] using hasFDerivAt_const (1 : ℂ) x
  · have hfun : coherentEigenpairAffinePoint i c =
        coherentEigenpairAffineDirectionCLM i c := by
      funext y
      simp [coherentEigenpairAffinePoint, coherentEigenpairAffineDirectionCLM, h,
        projectiveEigenvectorReconstruction]
      rfl
    rw [hfun]
    exact (coherentEigenpairAffineDirectionCLM i c).hasFDerivAt

theorem differentiableAt_coherentEigenpairInvRadius
    (x : CoherentHermitianCoordinates d) :
    DifferentiableAt ℝ (coherentEigenpairInvRadius i) x := by
  let e : Unit ⊕ Fin (d - 1) := Sum.inl Unit.unit
  have hr := (hasFDerivAt_projectiveEigenvectorReconstruction e
    (coherentSelectedProjectiveInputCLM i x).value).differentiableAt
  have hn : DifferentiableAt ℝ
      (fun w : ProjectiveChartCoordinate e → ℂ =>
        ‖projectiveEigenvectorReconstruction e w‖⁻¹)
      (coherentSelectedProjectiveInputCLM i x).value :=
    (hr.norm ℂ (projectiveEigenvectorReconstruction_ne_zero e _)).inv
      (norm_ne_zero_iff.mpr (projectiveEigenvectorReconstruction_ne_zero e _))
  have hP : DifferentiableAt ℝ (fun y : CoherentHermitianCoordinates d =>
      (coherentSelectedProjectiveInputCLM i y).value) x :=
    ((coherentProjectiveCoordinatesEquiv e).toContinuousLinearMap.comp
        (coherentSelectedProjectiveInputCLM i)).differentiableAt
  exact DifferentiableAt.comp (g := fun w : ProjectiveChartCoordinate e → ℂ =>
      ‖projectiveEigenvectorReconstruction e w‖⁻¹) x hn hP

/-- The distinguished column of the frame derivative is the derivative of the
normalized affine representative `s(z) (1,z)`. -/
theorem coherentEigenpairFrameDerivAt_col (x u : CoherentHermitianCoordinates d)
    (c : Unit ⊕ Fin (d - 1)) :
    coherentEigenpairFrameDerivAt i x u c (Sum.inl Unit.unit) =
      (coherentEigenpairInvRadius i x : ℂ) *
          coherentEigenpairAffineDirectionCLM i c u +
        ((fderiv ℝ (coherentEigenpairInvRadius i) x u : ℝ) : ℂ) *
          coherentEigenpairAffinePoint i c x := by
  have hS := (differentiableAt_coherentEigenpairInvRadius i x).hasFDerivAt
  have hv := (Complex.ofRealCLM.hasFDerivAt.comp x hS).mul
    (hasFDerivAt_coherentEigenpairAffinePoint i c x)
  have hH := hasFDerivAt_coherentEigenpairHouseholderEntry_global i x c
    (Sum.inl Unit.unit)
  have hfun : (fun y : CoherentHermitianCoordinates d =>
      coherentProjectiveHouseholderFrame (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i y) c (Sum.inl Unit.unit)) =
      fun y => (Complex.ofRealCLM ∘ coherentEigenpairInvRadius i) y *
        coherentEigenpairAffinePoint i c y := by
    funext y
    rw [coherentProjectiveHouseholderFrame_apply_col]
    simp [projectiveUnitReconstruction, coherentEigenpairInvRadius,
      coherentEigenpairAffinePoint, Complex.real_smul]
  rw [hfun] at hH
  have h := congrArg (fun L => L u) (hH.unique hv)
  simpa [coherentEigenpairFrameDerivAt, mul_comm] using h

/-- Projective coordinates of a selected coherent input, indexed by `Fin`. -/
def coherentEigenpairAffineCoord (y : CoherentHermitianCoordinates d) :
    Fin (d - 1) → ℂ :=
  fun j => (coherentSelectedProjectiveInputCLM i y).value
    ⟨Sum.inr j, by simp⟩

theorem coherentEigenpairAffinePoint_inr (j : Fin (d - 1))
    (y : CoherentHermitianCoordinates d) :
    coherentEigenpairAffinePoint i (Sum.inr j) y = coherentEigenpairAffineCoord i y j := by
  simp [coherentEigenpairAffinePoint, coherentEigenpairAffineCoord,
    projectiveEigenvectorReconstruction]

theorem coherentEigenpairAffineDirectionCLM_inr (j : Fin (d - 1))
    (u : CoherentHermitianCoordinates d) :
    coherentEigenpairAffineDirectionCLM i (Sum.inr j) u =
      coherentEigenpairAffineCoord i u j := by
  simp [coherentEigenpairAffineDirectionCLM, coherentEigenpairAffineCoord]
  rfl

theorem coherentEigenpairAffineDirectionCLM_inl (a : Unit)
    (u : CoherentHermitianCoordinates d) :
    coherentEigenpairAffineDirectionCLM i (Sum.inl a) u = 0 := by
  cases a
  simp [coherentEigenpairAffineDirectionCLM]

/-- The unit reconstruction is the inverse radius times the affine point. -/
theorem coherentEigenpairFrameAt_col (c : Unit ⊕ Fin (d - 1))
    (y : CoherentHermitianCoordinates d) :
    coherentEigenpairFrameAt i y c (Sum.inl Unit.unit) =
      (coherentEigenpairInvRadius i y : ℂ) * coherentEigenpairAffinePoint i c y := by
  rw [coherentEigenpairFrameAt, coherentProjectiveHouseholderFrame_apply_col]
  simp [projectiveUnitReconstruction, coherentEigenpairInvRadius,
    coherentEigenpairAffinePoint, Complex.real_smul]

theorem coherentEigenpairInvRadius_pos (y : CoherentHermitianCoordinates d) :
    0 < coherentEigenpairInvRadius i y :=
  inv_pos.mpr (norm_pos_iff.mpr (projectiveEigenvectorReconstruction_ne_zero _ _))

/-- The inverse radius is the normalization `(1 + |z|²)^{-1/2}`. -/
theorem coherentEigenpairInvRadius_sq_mul (y : CoherentHermitianCoordinates d) :
    coherentEigenpairInvRadius i y ^ 2 *
      (1 + ∑ j, Complex.normSq (coherentEigenpairAffineCoord i y j)) = 1 := by
  have hn := norm_projectiveEigenvectorReconstruction_sq (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i y).value
  have hsum : (∑ j : ProjectiveChartCoordinate
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)),
        Complex.normSq ((coherentSelectedProjectiveInputCLM i y).value j)) =
      ∑ j, Complex.normSq (coherentEigenpairAffineCoord i y j) := by
    let eqv : Fin (d - 1) ≃ ProjectiveChartCoordinate
        (Sum.inl Unit.unit : Unit ⊕ Fin (d - 1)) :=
      { toFun := fun j => ⟨Sum.inr j, by simp⟩
        invFun := fun c => match c with
          | ⟨Sum.inr j, _⟩ => j
          | ⟨Sum.inl u, h⟩ => False.elim (h (by cases u; rfl))
        left_inv := fun j => rfl
        right_inv := by
          rintro ⟨c, hc⟩
          rcases c with u | j
          · exact False.elim (hc (by cases u; rfl))
          · rfl }
    rw [← Equiv.sum_comp eqv]
    rfl
  rw [projectiveAffineRadiusSq, hsum] at hn
  rw [← hn, coherentEigenpairInvRadius, inv_pow, inv_mul_cancel₀]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr
    (projectiveEigenvectorReconstruction_ne_zero _ _))

/-- The projective column of the frame connection `Hᴴ H'` is the explicit
Householder tangent map applied to the affine variation. -/
theorem coherentEigenpairFrameConn_projective (x u : CoherentHermitianCoordinates d)
    (j : Fin (d - 1)) :
    ((coherentEigenpairFrameAt i x)ᴴ * coherentEigenpairFrameDerivAt i x u)
        (Sum.inr j) (Sum.inl Unit.unit) =
      projectiveHouseholderTangentMap (coherentEigenpairInvRadius i x)
        (coherentEigenpairAffineCoord i x) (coherentEigenpairAffineCoord i u) j := by
  have hcolH := fun c => coherentEigenpairFrameAt_col i c x
  set H := coherentEigenpairFrameAt i x with hHdef
  set s := coherentEigenpairInvRadius i x with hsdef
  have hs : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (coherentEigenpairInvRadius_pos i x).ne'
  -- the radial part is annihilated by unitarity
  have horth : ∑ c, star (H c (Sum.inr j)) * coherentEigenpairAffinePoint i c x = 0 := by
    have hunit := congrFun (congrFun
      (coherentProjectiveHouseholderFrame_conjTranspose_mul (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i x)) (Sum.inr j)) (Sum.inl Unit.unit)
    rw [Matrix.mul_apply, Matrix.one_apply_ne (by simp)] at hunit
    have h2 : (s : ℂ) * ∑ c, star (H c (Sum.inr j)) *
        coherentEigenpairAffinePoint i c x = 0 := by
      rw [Finset.mul_sum, ← hunit]
      apply Finset.sum_congr rfl
      intro c _
      rw [Matrix.conjTranspose_apply]
      change _ = star (H c (Sum.inr j)) * H c (Sum.inl Unit.unit)
      rw [hcolH c]
      ring
    exact (mul_eq_zero.mp h2).resolve_left hs
  have hcol (c : Unit ⊕ Fin (d - 1)) := coherentEigenpairFrameDerivAt_col i x u c
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hcol, mul_add]
  rw [Finset.sum_add_distrib]
  have hrad : ∑ c, star (H c (Sum.inr j)) *
      (((fderiv ℝ (coherentEigenpairInvRadius i) x u : ℝ) : ℂ) *
        coherentEigenpairAffinePoint i c x) = 0 := by
    rw [← mul_zero ((fderiv ℝ (coherentEigenpairInvRadius i) x u : ℝ) : ℂ), ← horth,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hrad, add_zero]
  -- explicit Householder entries
  have hHerm : ∀ c, star (H c (Sum.inr j)) = H (Sum.inr j) c := by
    intro c
    have := congrFun (congrFun
      (coherentProjectiveHouseholderFrame_conjTranspose (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i x)) (Sum.inr j)) c
    rw [Matrix.conjTranspose_apply] at this
    exact this
  simp only [hHerm]
  rw [Fintype.sum_sum_type]
  simp only [coherentEigenpairAffineDirectionCLM_inl, mul_zero, Finset.sum_const_zero,
    zero_add, coherentEigenpairAffineDirectionCLM_inr]
  have hentry (k : Fin (d - 1)) : H (Sum.inr j) (Sum.inr k) =
      -(if j = k then 1 else 0) +
        (((1 + s)⁻¹ : ℝ) : ℂ) * ((s : ℂ) * coherentEigenpairAffineCoord i x j) *
          star ((s : ℂ) * coherentEigenpairAffineCoord i x k) := by
    rw [hHdef, coherentEigenpairFrameAt, coherentProjectiveHouseholderFrame_eq,
      phaseFixedHouseholderFrame_apply]
    have hself := projectiveUnitReconstruction_apply_self (Sum.inl Unit.unit)
      (coherentSelectedProjectiveInputCLM i x).value
    have hre : (projectiveUnitReconstruction (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i x).value (Sum.inl Unit.unit)).re = s := by
      rw [hself, Complex.ofReal_re, hsdef]
      rfl
    have hw (m : Fin (d - 1)) : phaseFixedHouseholderShift (Sum.inl Unit.unit)
        (projectiveUnitReconstruction (Sum.inl Unit.unit)
          (coherentSelectedProjectiveInputCLM i x).value) (Sum.inr m) =
        (s : ℂ) * coherentEigenpairAffineCoord i x m := by
      have h1 := coherentEigenpairFrameAt_col i (Sum.inr m) x
      rw [coherentEigenpairFrameAt, coherentProjectiveHouseholderFrame_apply_col,
        coherentEigenpairAffinePoint_inr] at h1
      simp only [phaseFixedHouseholderShift, phaseFixedCoordinateVector, Pi.add_apply]
      rw [Pi.single_eq_of_ne (by simp), add_zero]
      exact h1
    rw [hre, hw, hw]
    simp [Sum.inr.injEq]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hentry k]), ← hsdef]
  simp only [projectiveHouseholderTangentMap, LinearMap.coe_mk, AddHom.coe_mk, add_mul,
    neg_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring

/-- The canonical block-diagonal matrix `diag(E,B)` read from a coherent input. -/
def coherentEigenpairBlockDiagAt (y : CoherentHermitianCoordinates d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  canonicalBlockDiagonalLinearMap (coherentSelectedBlockInputLinearMap i y)

/-- The explicit product-rule differential as a matrix. -/
def coherentEigenpairMatrixDiffAt (x u : CoherentHermitianCoordinates d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  fun a b => coherentEigenpairConjugationEntryDifferentialAt i x a b u

/-- Matrix form of the three-term product rule. -/
theorem coherentEigenpairMatrixDiffAt_eq (x u : CoherentHermitianCoordinates d) :
    coherentEigenpairMatrixDiffAt i x u =
      coherentEigenpairFrameDerivAt i x u * coherentEigenpairBlockDiagAt i x *
          (coherentEigenpairFrameAt i x)ᴴ +
        coherentEigenpairFrameAt i x * coherentEigenpairBlockDiagAt i u *
          (coherentEigenpairFrameAt i x)ᴴ +
        coherentEigenpairFrameAt i x * coherentEigenpairBlockDiagAt i x *
          (coherentEigenpairFrameDerivAt i x u)ᴴ := by
  ext a b
  simp only [coherentEigenpairMatrixDiffAt, coherentEigenpairConjugationEntryDifferentialAt,
    FunLike.coe_sum, Finset.sum_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    smul_eq_mul, Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [coherentEigenpairFrameDerivAt, coherentEigenpairFrameAt,
    coherentEigenpairBlockDiagAt]
  have hD (y : CoherentHermitianCoordinates d) (p r : Unit ⊕ Fin (d - 1)) :
      coherentBlockDiagonalEntryCLM i p r y =
        canonicalBlockDiagonalLinearMap (coherentSelectedBlockInputLinearMap i y) p r := rfl
  simp only [hD, ContinuousLinearEquiv.coe_coe, starL'_apply]
  ring

/-- The frame connection `A = Hᴴ H'` of the Householder frame. -/
def coherentEigenpairFrameConn (x u : CoherentHermitianCoordinates d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  (coherentEigenpairFrameAt i x)ᴴ * coherentEigenpairFrameDerivAt i x u

/-- The differential conjugated back by the base frame: `D' + A D - D A`. -/
def coherentEigenpairConjugatedDiff (x u : CoherentHermitianCoordinates d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  coherentEigenpairBlockDiagAt i u +
    coherentEigenpairFrameConn i x u * coherentEigenpairBlockDiagAt i x -
    coherentEigenpairBlockDiagAt i x * coherentEigenpairFrameConn i x u

/-- The frame connection is skew-Hermitian. -/
theorem coherentEigenpairFrameConn_conjTranspose (x u : CoherentHermitianCoordinates d) :
    (coherentEigenpairFrameConn i x u)ᴴ = -coherentEigenpairFrameConn i x u := by
  rw [coherentEigenpairFrameConn, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  exact eq_neg_of_add_eq_zero_left (coherentEigenpairFrameDerivAt_skew i x u)

/-- Conjugating the explicit differential by the base frame gives
`D' + A D - D A`. -/
theorem coherentEigenpairMatrixDiffAt_conj (x u : CoherentHermitianCoordinates d) :
    (coherentEigenpairFrameAt i x)ᴴ * coherentEigenpairMatrixDiffAt i x u *
        coherentEigenpairFrameAt i x =
      coherentEigenpairConjugatedDiff i x u := by
  have hU := coherentProjectiveHouseholderFrame_conjTranspose_mul (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i x)
  have hS : (coherentEigenpairFrameDerivAt i x u)ᴴ * coherentEigenpairFrameAt i x =
      -coherentEigenpairFrameConn i x u :=
    eq_neg_of_add_eq_zero_left (coherentEigenpairFrameDerivAt_skew i x u)
  change (coherentEigenpairFrameAt i x)ᴴ * coherentEigenpairFrameAt i x = 1 at hU
  rw [coherentEigenpairMatrixDiffAt_eq, coherentEigenpairConjugatedDiff]
  set H := coherentEigenpairFrameAt i x
  set Hd := coherentEigenpairFrameDerivAt i x u
  set D := coherentEigenpairBlockDiagAt i x
  set D' := coherentEigenpairBlockDiagAt i u
  have e1 : Hᴴ * (Hd * D * Hᴴ + H * D' * Hᴴ + H * D * Hdᴴ) * H =
      (Hᴴ * Hd) * D * (Hᴴ * H) + (Hᴴ * H) * D' * (Hᴴ * H) +
        (Hᴴ * H) * D * (Hdᴴ * H) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [e1, hU, hS]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, coherentEigenpairFrameConn]
  abel

/-- Hence the explicit differential is `H (D' + A D - D A) Hᴴ`. -/
theorem coherentEigenpairMatrixDiffAt_eq_conj (x u : CoherentHermitianCoordinates d) :
    coherentEigenpairMatrixDiffAt i x u =
      coherentEigenpairFrameAt i x * coherentEigenpairConjugatedDiff i x u *
        (coherentEigenpairFrameAt i x)ᴴ := by
  have hU := coherentProjectiveHouseholderFrame_mul_conjTranspose (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i x)
  change coherentEigenpairFrameAt i x * (coherentEigenpairFrameAt i x)ᴴ = 1 at hU
  rw [← coherentEigenpairMatrixDiffAt_conj]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The block-diagonal matrix `diag(E,B)` is Hermitian. -/
theorem coherentEigenpairBlockDiagAt_isHermitian (y : CoherentHermitianCoordinates d) :
    (coherentEigenpairBlockDiagAt i y).IsHermitian := by
  change (eigenpairCanonicalMatrix (coherentSelectedBlockInputLinearMap i y).1
    (coherentSelectedBlockInputLinearMap i y).2.2.1).IsHermitian
  rw [eigenpairCanonicalMatrix]
  apply Matrix.isHermitian_fromBlocks_iff.mpr
  refine ⟨?_, by simp, by simp, (coherentSelectedBlockInputLinearMap i y).2.2.2⟩
  rw [Matrix.IsHermitian]
  ext a b
  simp

/-- The conjugated differential is Hermitian. -/
theorem coherentEigenpairConjugatedDiff_isHermitian (x u : CoherentHermitianCoordinates d) :
    (coherentEigenpairConjugatedDiff i x u).IsHermitian := by
  rw [Matrix.IsHermitian, coherentEigenpairConjugatedDiff]
  have hD := (coherentEigenpairBlockDiagAt_isHermitian i x).eq
  have hD' := (coherentEigenpairBlockDiagAt_isHermitian i u).eq
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hD, hD', coherentEigenpairFrameConn_conjTranspose, Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- The explicit differential is Hermitian. -/
theorem coherentEigenpairMatrixDiffAt_isHermitian (x u : CoherentHermitianCoordinates d) :
    (coherentEigenpairMatrixDiffAt i x u).IsHermitian := by
  rw [coherentEigenpairMatrixDiffAt_eq_conj]
  exact Matrix.isHermitian_mul_mul_conjTranspose _
    (coherentEigenpairConjugatedDiff_isHermitian i x u)

end Derivative

section HermitianConjugation

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Two-sided conjugation `M ↦ U M Uᴴ` on the real space of Hermitian matrices. -/
def hermitianMatrixConjLinearMap (U : Matrix n n ℂ) :
    RealHermitianMatrix n →ₗ[ℝ] RealHermitianMatrix n where
  toFun M := ⟨U * M.1 * Uᴴ, Matrix.isHermitian_mul_mul_conjTranspose U M.2⟩
  map_add' M N := by
    apply Subtype.ext
    change U * (M.1 + N.1) * Uᴴ = U * M.1 * Uᴴ + U * N.1 * Uᴴ
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    apply Subtype.ext
    change U * ((c : ℂ) • M.1) * Uᴴ = (c : ℂ) • (U * M.1 * Uᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem hermitianMatrixConjLinearMap_apply_coe (U : Matrix n n ℂ)
    (M : RealHermitianMatrix n) :
    (hermitianMatrixConjLinearMap U M).1 = U * M.1 * Uᴴ := rfl

/-- Conjugation transported to energy/projective/complement block coordinates. -/
def eigenpairBlockConjLinearMap (U : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) :
    EigenpairHermitianBlockCoordinates n →ₗ[ℝ] EigenpairHermitianBlockCoordinates n :=
  (eigenpairHermitianBlockLinearEquiv n).toLinearMap.comp
    ((hermitianMatrixConjLinearMap U).comp
      (eigenpairHermitianBlockLinearEquiv n).symm.toLinearMap)

theorem eigenpairBlockConjLinearMap_apply (U : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
    (M : RealHermitianMatrix (Unit ⊕ n)) :
    eigenpairBlockConjLinearMap U (eigenpairHermitianBlockLinearEquiv n M) =
      eigenpairHermitianBlockLinearEquiv n (hermitianMatrixConjLinearMap U M) := by
  simp [eigenpairBlockConjLinearMap]

/-- Conjugating by `Uᴴ` and then by `U` is the identity for unitary `U`. -/
theorem eigenpairBlockConjLinearMap_comp_conjTranspose
    (U : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) (hU : U * Uᴴ = 1) :
    (eigenpairBlockConjLinearMap U).comp (eigenpairBlockConjLinearMap Uᴴ) =
      LinearMap.id := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨M, rfl⟩ := (eigenpairHermitianBlockLinearEquiv n).surjective ξ
  simp only [LinearMap.comp_apply, eigenpairBlockConjLinearMap_apply, LinearMap.id_apply]
  congr 1
  apply Subtype.ext
  simp only [hermitianMatrixConjLinearMap_apply_coe, Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc,
    hU, Matrix.mul_one]

/-- Conjugation by a Hermitian unitary matrix has absolute determinant one. -/
theorem abs_det_eigenpairBlockConjLinearMap
    (U : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) (hU : U * Uᴴ = 1) (hH : Uᴴ = U) :
    |LinearMap.det (eigenpairBlockConjLinearMap U)| = 1 := by
  have h := congrArg LinearMap.det (eigenpairBlockConjLinearMap_comp_conjTranspose U hU)
  rw [LinearMap.det_comp, LinearMap.det_id, hH] at h
  have h2 : |LinearMap.det (eigenpairBlockConjLinearMap U)| *
      |LinearMap.det (eigenpairBlockConjLinearMap U)| = 1 := by
    rw [← abs_mul, h, abs_one]
  rcases mul_self_eq_one_iff.mp h2 with h3 | h3
  · exact h3
  · exact absurd h3 (by linarith [abs_nonneg (LinearMap.det (eigenpairBlockConjLinearMap U))])

/-- Products with the canonical block-diagonal matrix, distinguished column. -/
theorem mul_eigenpairCanonicalMatrix_inl (A : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
    (E : ℝ) (B : Matrix n n ℂ) (a : Unit ⊕ n) :
    (A * eigenpairCanonicalMatrix E B) a (Sum.inl Unit.unit) =
      A a (Sum.inl Unit.unit) * E := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, eigenpairCanonicalMatrix]

/-- Products with the canonical block-diagonal matrix, distinguished row. -/
theorem eigenpairCanonicalMatrix_mul_inl (A : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
    (E : ℝ) (B : Matrix n n ℂ) (b : Unit ⊕ n) :
    (eigenpairCanonicalMatrix E B * A) (Sum.inl Unit.unit) b =
      E * A (Sum.inl Unit.unit) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, eigenpairCanonicalMatrix]

/-- Products with the canonical block-diagonal matrix, complementary rows. -/
theorem eigenpairCanonicalMatrix_mul_inr (A : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
    (E : ℝ) (B : Matrix n n ℂ) (j : n) (b : Unit ⊕ n) :
    (eigenpairCanonicalMatrix E B * A) (Sum.inr j) b =
      ∑ k, B j k * A (Sum.inr k) b := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, eigenpairCanonicalMatrix]

end HermitianConjugation

section Assembly

variable {d : ℕ} (i : Fin d)

theorem coherentSelectedBlockInputLinearMap_eq (y : CoherentHermitianCoordinates d) :
    coherentSelectedBlockInputLinearMap i y = coherentSelectedBlockCoordinateLinearEquiv i y :=
  rfl

@[simp] theorem coherentSelectedBlockInputLinearMap_symm
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    coherentSelectedBlockInputLinearMap i
      ((coherentSelectedBlockCoordinateLinearEquiv i).symm ξ) = ξ := by
  rw [coherentSelectedBlockInputLinearMap_eq, LinearEquiv.apply_symm_apply]

theorem coherentSelectedProjectiveInputCLM_eq (y : CoherentHermitianCoordinates d) :
    coherentSelectedProjectiveInputCLM i y =
      ⟨canonicalProjectiveChartCoordinates (coherentSelectedBlockInputLinearMap i y).2.1⟩ :=
  rfl

theorem coherentEigenpairAffineCoord_eq (y : CoherentHermitianCoordinates d) :
    coherentEigenpairAffineCoord i y = (coherentSelectedBlockInputLinearMap i y).2.1 :=
  rfl

/-- The frame derivative only sees the projective component of the direction. -/
theorem coherentEigenpairFrameDerivAt_congr (x u u' : CoherentHermitianCoordinates d)
    (h : coherentSelectedProjectiveInputCLM i u = coherentSelectedProjectiveInputCLM i u') :
    coherentEigenpairFrameDerivAt i x u = coherentEigenpairFrameDerivAt i x u' := by
  ext a b
  simp only [coherentEigenpairFrameDerivAt, coherentEigenpairHouseholderEntryDifferentialAt,
    ContinuousLinearMap.coe_comp, Function.comp_apply, h]

/-- In selected block coordinates, the derivative is the block
read-off of the explicit Hermitian matrix differential. -/
theorem coherentSelectedBlockCoordinate_fderiv (x u : CoherentHermitianCoordinates d) :
    coherentSelectedBlockCoordinateLinearEquiv i
        (fderiv ℝ (coherentSelectedEigenpairDecode i) x u) =
      eigenpairHermitianBlockLinearEquiv (Fin (d - 1))
        ⟨coherentEigenpairMatrixDiffAt i x u,
          coherentEigenpairMatrixDiffAt_isHermitian i x u⟩ := by
  rw [(hasFDerivAt_coherentSelectedEigenpairDecode_explicit_global i x).fderiv]
  set M : RealHermitianMatrix (Unit ⊕ Fin (d - 1)) :=
    ⟨coherentEigenpairMatrixDiffAt i x u, coherentEigenpairMatrixDiffAt_isHermitian i x u⟩
  have hdec := selectedMatrixFinCoordinateRead_decode i
    (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M)
  rw [LinearEquiv.symm_apply_apply] at hdec
  have hval : (coherentEigenpairReadbackMatrixDifferentialAt i x u).value =
      selectedMatrixFinCoordinateReadCLM i M.1 := rfl
  change selectedEigenpairFinCoordinateLinearEquiv i
    (coherentEigenpairReadbackMatrixDifferentialAt i x u).value = _
  rw [hval, hdec, LinearEquiv.apply_symm_apply]

/-- The derivative in selected block coordinates, conjugated back by
the base Householder frame. -/
def coherentEigenpairFramedBlockDifferential (x : CoherentHermitianCoordinates d) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  (eigenpairBlockConjLinearMap (coherentEigenpairFrameAt i x)ᴴ).comp
    ((coherentSelectedBlockCoordinateLinearEquiv i).toLinearMap.comp
      ((fderiv ℝ (coherentSelectedEigenpairDecode i) x).toLinearMap.comp
        (coherentSelectedBlockCoordinateLinearEquiv i).symm.toLinearMap))

theorem coherentEigenpairFramedBlockDifferential_apply (x : CoherentHermitianCoordinates d)
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    coherentEigenpairFramedBlockDifferential i x ξ =
      eigenpairHermitianBlockLinearEquiv (Fin (d - 1))
        ⟨coherentEigenpairConjugatedDiff i x
            ((coherentSelectedBlockCoordinateLinearEquiv i).symm ξ),
          coherentEigenpairConjugatedDiff_isHermitian i x _⟩ := by
  simp only [coherentEigenpairFramedBlockDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
  rw [coherentSelectedBlockCoordinate_fderiv, eigenpairBlockConjLinearMap_apply]
  congr 1
  apply Subtype.ext
  simp only [hermitianMatrixConjLinearMap_apply_coe, Matrix.conjTranspose_conjTranspose]
  exact coherentEigenpairMatrixDiffAt_conj i x _

theorem coherentEigenpairBlockDiagAt_eq (y : CoherentHermitianCoordinates d) :
    coherentEigenpairBlockDiagAt i y =
      eigenpairCanonicalMatrix (coherentSelectedBlockInputLinearMap i y).1
        (coherentSelectedBlockInputLinearMap i y).2.2.1 :=
  rfl

/-- Energy block: the framed differential leaves the energy variation fixed. -/
theorem coherentEigenpairFramedBlockDifferential_fst (x : CoherentHermitianCoordinates d)
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    (coherentEigenpairFramedBlockDifferential i x ξ).1 = ξ.1 := by
  rw [coherentEigenpairFramedBlockDifferential_apply]
  change (coherentEigenpairConjugatedDiff i x _ (Sum.inl Unit.unit)
    (Sum.inl Unit.unit)).re = ξ.1
  rw [coherentEigenpairConjugatedDiff, Matrix.sub_apply, Matrix.add_apply,
    coherentEigenpairBlockDiagAt_eq i x, mul_eigenpairCanonicalMatrix_inl,
    eigenpairCanonicalMatrix_mul_inl, coherentEigenpairBlockDiagAt_eq,
    coherentSelectedBlockInputLinearMap_symm]
  rw [mul_comm (coherentEigenpairFrameConn i x _ (Sum.inl Unit.unit) (Sum.inl Unit.unit)),
    add_sub_cancel_right]
  simp [eigenpairCanonicalMatrix]

/-- Projective block: the gap matrix times the frame connection column. -/
theorem coherentEigenpairFramedBlockDifferential_snd_fst
    (x : CoherentHermitianCoordinates d)
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    (coherentEigenpairFramedBlockDifferential i x ξ).2.1 =
      eigenpairGapMatrix (coherentSelectedBlockInputLinearMap i x).1
          (coherentSelectedBlockInputLinearMap i x).2.2.1 *ᵥ
        projectiveHouseholderTangentMap (coherentEigenpairInvRadius i x)
          (coherentEigenpairAffineCoord i x) ξ.2.1 := by
  rw [coherentEigenpairFramedBlockDifferential_apply]
  funext j
  change coherentEigenpairConjugatedDiff i x _ (Sum.inr j) (Sum.inl Unit.unit) = _
  have hcol (k : Fin (d - 1)) :=
    coherentEigenpairFrameConn_projective i x
      ((coherentSelectedBlockCoordinateLinearEquiv i).symm ξ) k
  rw [coherentEigenpairAffineCoord_eq i
    ((coherentSelectedBlockCoordinateLinearEquiv i).symm ξ),
    coherentSelectedBlockInputLinearMap_symm] at hcol
  rw [coherentEigenpairConjugatedDiff, Matrix.sub_apply, Matrix.add_apply,
    coherentEigenpairBlockDiagAt_eq i x, mul_eigenpairCanonicalMatrix_inl,
    eigenpairCanonicalMatrix_mul_inr, coherentEigenpairBlockDiagAt_eq,
    coherentSelectedBlockInputLinearMap_symm]
  simp only [coherentEigenpairFrameConn] at hcol ⊢
  simp only [hcol]
  simp [eigenpairCanonicalMatrix, eigenpairGapMatrix,
    Matrix.mulVec, dotProduct, Matrix.one_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [mul_comm]

/-- Complementary block: identity plus a term depending only on the
projective variation. -/
theorem coherentEigenpairFramedBlockDifferential_snd_snd
    (x : CoherentHermitianCoordinates d)
    (ξ : EigenpairHermitianBlockCoordinates (Fin (d - 1))) :
    (coherentEigenpairFramedBlockDifferential i x ξ).2.2 = ξ.2.2 +
      (coherentEigenpairFramedBlockDifferential i x (0, (ξ.2.1, 0))).2.2 := by
  apply Subtype.ext
  rw [coherentEigenpairFramedBlockDifferential_apply,
    coherentEigenpairFramedBlockDifferential_apply]
  change (coherentEigenpairConjugatedDiff i x _).submatrix Sum.inr Sum.inr =
    ξ.2.2.1 + (coherentEigenpairConjugatedDiff i x _).submatrix Sum.inr Sum.inr
  have hconn : coherentEigenpairFrameConn i x
      ((coherentSelectedBlockCoordinateLinearEquiv i).symm ξ) =
      coherentEigenpairFrameConn i x
        ((coherentSelectedBlockCoordinateLinearEquiv i).symm (0, (ξ.2.1, 0))) := by
    rw [coherentEigenpairFrameConn, coherentEigenpairFrameConn,
      coherentEigenpairFrameDerivAt_congr i x _
        ((coherentSelectedBlockCoordinateLinearEquiv i).symm (0, (ξ.2.1, 0))) (by
        simp only [coherentSelectedProjectiveInputCLM_eq,
          coherentSelectedBlockInputLinearMap_symm])]
  rw [coherentEigenpairConjugatedDiff, coherentEigenpairConjugatedDiff, hconn]
  ext a b
  simp [coherentEigenpairBlockDiagAt_eq, eigenpairCanonicalMatrix]
  ring

/-- Diagonal factor carrying the Householder tangent block. -/
def coherentEigenpairHouseholderBlockDiagonal (x : CoherentHermitianCoordinates d) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  LinearMap.prodMap LinearMap.id
    (LinearMap.prodMap
      (projectiveHouseholderTangentMap (coherentEigenpairInvRadius i x)
        (coherentEigenpairAffineCoord i x)) LinearMap.id)

/-- Unipotent shear of the complementary block by the projective variation. -/
def coherentEigenpairComplementShear (x : CoherentHermitianCoordinates d) :
    EigenpairHermitianBlockCoordinates (Fin (d - 1)) →ₗ[ℝ]
      EigenpairHermitianBlockCoordinates (Fin (d - 1)) :=
  LinearMap.prodMap LinearMap.id
    ((LinearMap.id : ((Fin (d - 1) → ℂ) × RealHermitianMatrix (Fin (d - 1))) →ₗ[ℝ]
        ((Fin (d - 1) → ℂ) × RealHermitianMatrix (Fin (d - 1)))) +
      (LinearMap.inr ℝ (Fin (d - 1) → ℂ) (RealHermitianMatrix (Fin (d - 1)))).comp
        ((eigenpairComplementBlockProjection.comp
          ((coherentEigenpairFramedBlockDifferential i x).comp
            eigenpairProjectiveBlockInclusion)).comp
          (LinearMap.fst ℝ (Fin (d - 1) → ℂ) (RealHermitianMatrix (Fin (d - 1))))))

/-- Exact block-triangular factorization of the framed derivative:
gap block ∘ Householder tangent diagonal ∘ unipotent complement shear. -/
theorem coherentEigenpairFramedBlockDifferential_factorization
    (x : CoherentHermitianCoordinates d) :
    coherentEigenpairFramedBlockDifferential i x =
      (eigenpairHermitianBlockCoordinateDifferential
          (coherentSelectedBlockInputLinearMap i x).1
          (coherentSelectedBlockInputLinearMap i x).2.2.1).comp
        ((coherentEigenpairHouseholderBlockDiagonal i x).comp
          (coherentEigenpairComplementShear i x)) := by
  apply LinearMap.ext
  intro ξ
  rcases ξ with ⟨t, w, C⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [coherentEigenpairFramedBlockDifferential_fst]
    rfl
  · rw [coherentEigenpairFramedBlockDifferential_snd_fst]
    simp [coherentEigenpairComplementShear, coherentEigenpairHouseholderBlockDiagonal,
      eigenpairHermitianBlockCoordinateDifferential_apply]
  · rw [coherentEigenpairFramedBlockDifferential_snd_snd]
    rfl

/-- The complement shear has determinant one. -/
theorem det_coherentEigenpairComplementShear (x : CoherentHermitianCoordinates d) :
    LinearMap.det (coherentEigenpairComplementShear i x) = 1 := by
  rw [coherentEigenpairComplementShear, LinearMap.det_prodMap, LinearMap.det_id,
    det_prodShear_eq_one, one_mul]

/-- The Householder diagonal factor has the exact projective density. -/
theorem det_coherentEigenpairHouseholderBlockDiagonal (x : CoherentHermitianCoordinates d) :
    LinearMap.det (coherentEigenpairHouseholderBlockDiagonal i x) =
      ((1 + ∑ j, Complex.normSq (coherentEigenpairAffineCoord i x j))⁻¹) ^ d := by
  rw [coherentEigenpairHouseholderBlockDiagonal, LinearMap.det_prodMap,
    LinearMap.det_prodMap, LinearMap.det_id, LinearMap.det_id, one_mul, mul_one,
    det_projectiveHouseholderTangentMap _ _ (coherentEigenpairInvRadius_pos i x)
      (coherentEigenpairInvRadius_sq_mul i x)]
  congr 1
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by
    intro hd
    subst hd
    exact Fin.elim0 i))

/-- Determinant of the derivative at an arbitrary coherent input: the
base-frame conjugation factor times the framed block determinant. -/
theorem det_fderiv_coherentSelectedEigenpairDecode_eq (x : CoherentHermitianCoordinates d) :
    LinearMap.det (fderiv ℝ (coherentSelectedEigenpairDecode i) x).toLinearMap =
      LinearMap.det (eigenpairBlockConjLinearMap (coherentEigenpairFrameAt i x)) *
        LinearMap.det (coherentEigenpairFramedBlockDifferential i x) := by
  have hU := coherentProjectiveHouseholderFrame_mul_conjTranspose (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i x)
  change coherentEigenpairFrameAt i x * (coherentEigenpairFrameAt i x)ᴴ = 1 at hU
  rw [← LinearMap.det_comp, coherentEigenpairFramedBlockDifferential, ← LinearMap.comp_assoc,
    eigenpairBlockConjLinearMap_comp_conjTranspose _ hU, LinearMap.id_comp]
  exact (LinearMap.det_conj _ (coherentSelectedBlockCoordinateLinearEquiv i)).symm

/-- Exact absolute Jacobian at an arbitrary coherent input, in terms of its
own selected energy, affine coordinate and complementary block. -/
theorem abs_det_fderiv_coherentSelectedEigenpairDecode_at
    (x : CoherentHermitianCoordinates d) :
    |LinearMap.det (fderiv ℝ (coherentSelectedEigenpairDecode i) x).toLinearMap| =
      ((1 + ∑ j, Complex.normSq (coherentEigenpairAffineCoord i x j))⁻¹) ^ d *
        Complex.normSq (eigenpairGapMatrix (coherentSelectedBlockInputLinearMap i x).1
          (coherentSelectedBlockInputLinearMap i x).2.2.1).det := by
  have hU := coherentProjectiveHouseholderFrame_mul_conjTranspose (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i x)
  have hH := coherentProjectiveHouseholderFrame_conjTranspose (Sum.inl Unit.unit)
    (coherentSelectedProjectiveInputCLM i x)
  change coherentEigenpairFrameAt i x * (coherentEigenpairFrameAt i x)ᴴ = 1 at hU
  change (coherentEigenpairFrameAt i x)ᴴ = coherentEigenpairFrameAt i x at hH
  rw [det_fderiv_coherentSelectedEigenpairDecode_eq, abs_mul,
    abs_det_eigenpairBlockConjLinearMap _ hU hH, one_mul,
    coherentEigenpairFramedBlockDifferential_factorization, LinearMap.det_comp,
    LinearMap.det_comp, det_coherentEigenpairComplementShear, mul_one,
    det_coherentEigenpairHouseholderBlockDiagonal,
    det_eigenpairHermitianBlockCoordinateDifferential,
    eigenpairLocalRealJacobianDensity_eq_normSq_det, abs_mul,
    abs_of_nonneg (Complex.normSq_nonneg _), abs_of_nonneg (pow_nonneg (inv_nonneg.mpr
      (add_nonneg zero_le_one (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _))) _),
    mul_comm]

@[simp] theorem coherentSelectedBlockInputLinearMap_globalInput (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1))) :
    coherentSelectedBlockInputLinearMap i (coherentEigenpairGlobalInput i E z B) =
      (E, (z, B)) := by
  change selectedEigenpairFinCoordinateLinearEquiv i
    ((selectedEigenpairFinCoordinateLinearEquiv i).symm (E, (z, B))) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- **Exact global Jacobian of the coherent eigenpair decoder** (density part of the
eigenpair Jacobian lemma, at an arbitrary point of the affine chart rather than only at
`v = e₁`).

Normalization: real Lebesgue coordinates on both sides (the coherent selected
Hermitian coordinates, i.e. diagonal entries and real/imaginary parts of the
upper entries); the projective factor is the unnormalized affine Fubini–Study
density `(1 + ∑ |z_j|²)^{-d}` in the chart `v = (1,z)/‖(1,z)‖` with distinguished
coordinate `Sum.inl ()`, and the gap factor is `|det (E I - B)|²`.
Quantifiers: for every `i : Fin d`, every energy `E`, every affine coordinate
`z : Fin (d-1) → ℂ` and every complementary Hermitian block `B`; no gap
hypothesis, no zero-slice restriction and no factorization hypothesis.  There is
no limit.  Proof: the derivative is conjugated by the base Householder frame
(a Hermitian unitary transport of absolute determinant one) into the block
lower-triangular form `gap ∘ diag(1, Householder tangent, 1) ∘ shear`. -/
theorem abs_det_fderiv_coherentSelectedEigenpairDecode_globalInput (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det ((fderiv ℝ (coherentSelectedEigenpairDecode i)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap)| =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d *
        Complex.normSq (eigenpairGapMatrix E B.1).det := by
  rw [abs_det_fderiv_coherentSelectedEigenpairDecode_at, coherentEigenpairAffineCoord_eq,
    coherentSelectedBlockInputLinearMap_globalInput]

/-- The projective correction has exactly the affine projective
density as its absolute determinant (off the complementary spectrum). -/
theorem abs_det_coherentEigenpairProjectiveCorrection (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    |LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap)| =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d := by
  have h := abs_det_fderiv_coherentSelectedEigenpairDecode_eq_correction_mul_normSq
    i E z B hgap
  rw [abs_det_fderiv_coherentSelectedEigenpairDecode_globalInput] at h
  have hne : Complex.normSq (eigenpairGapMatrix E B.1).det ≠ 0 :=
    (Complex.normSq_pos.mpr hgap).ne'
  exact (mul_right_cancel₀ hne h).symm

/-- The correction and the verified diagonal model have the same
absolute determinant. -/
theorem abs_det_coherentEigenpairProjectiveCorrection_eq_diagonalModel (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    |LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap)| =
      |LinearMap.det (coherentProjectiveCorrectionDiagonalModel i z)| := by
  rw [abs_det_coherentEigenpairProjectiveCorrection,
    abs_det_coherentProjectiveCorrectionDiagonalModel]

/-- The projective-Jacobian defect of the correction is one. -/
theorem coherentEigenpairProjectiveCorrection_defect_eq_one (E : ℝ)
    (z : Fin (d - 1) → ℂ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hgap : (eigenpairGapMatrix E B.1).det ≠ 0) :
    (((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d)⁻¹ *
      |LinearMap.det (coherentEigenpairProjectiveCorrection i E z B hgap)| = 1 := by
  rw [abs_det_coherentEigenpairProjectiveCorrection_eq_diagonalModel]
  exact coherentProjectiveCorrectionDiagonalModel_defect_eq_one i z

end Assembly

end CoareaNative.BlockBand
