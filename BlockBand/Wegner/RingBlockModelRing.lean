module

public import Mathlib
public import BlockBand.Wegner.RingBlockModelLaw
public import BlockBand.Wegner.PhysicalConditionalCount

/-!
# The physical ring as a `BlockModel`

A proof of `Internal.Contracts.InputsRing.RingAsBlockModel`, used for the finite log
recovery.

Law: the physical ring law `model.law` on `p.SiteMatrix`, for every admissible `p` and
every realization `model`. The presentation (`ringModel`) has sample space `p.SiteMatrix`,
measure `model.law`, and is built from the Hermitian version `X = p.physicalHermitianVersion H`
of the sample in block coordinates (`toBlockCoords`): `A_j = X_jj` (`diagonalBlocks`),
`D = X` off the diagonal blocks (`offDiagonalBlocks`), `Y = 0`. Every sample of `A`, `D` is
Hermitian, and `X = H` almost surely (the law is supported on Hermitian matrices).

Proof. The diagonal blocks are the Johansson reconstruction of their own physical Gaussian
coordinates (`ringA_eq`), whose joint law, after the injective reindexing `coordIdx`, is a
product of centered real Gaussians; splitting real/imaginary parts and currying identifies it
with `Π_j Π_q coordLaw (c/W) q`, hence independent `GUE_W(c/W)` blocks. The bond part is a
function of the remaining coordinates (`ringD_eq`), so it is independent of the blocks by
`PhysicalFresh.fresh_rest_independent` with `R = univ`. No estimate and no cited input is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

namespace RingBlock

open MeasureTheory ProbabilityTheory
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs (gueMatrixLaw BlockModel withoutFreshBlocks)
open BlockBand.Internal.Contracts.InputsRing
open scoped NNReal ComplexOrder

local instance gaussianReal_isProbabilityRing (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal μ v

variable (p : Parameters)

/-! ## Sites of a block -/

/-- The cyclic block carrying block coordinate `j`. -/
def zblk (j : Fin p.n) : ZMod p.n := (ZMod.finEquiv p.n).symm.toEquiv.symm j

theorem zblk_inj {j j' : Fin p.n} : zblk p j = zblk p j' ↔ j = j' :=
  (ZMod.finEquiv p.n).symm.toEquiv.symm.injective.eq_iff

/-- The site of block `j`, coordinate `a`. -/
def site (j : Fin p.n) (a : Fin p.W) : p.Site := (zblk p j, a)

theorem siteBlockEquiv_symm (x : Fin p.n × Fin p.W) :
    (siteBlockEquiv p).symm x = site p x.1 x.2 := rfl

theorem site_inj {j j' : Fin p.n} {a a' : Fin p.W} :
    site p j a = site p j' a' ↔ j = j' ∧ a = a' := by
  simp [site, zblk_inj]

theorem siteIndex_site_lt (j : Fin p.n) (a b : Fin p.W) :
    p.siteIndex (site p j a) < p.siteIndex (site p j b) ↔ a < b := by
  simp only [Parameters.siteIndex, site, Fin.lt_def]
  omega

/-! ## The Johansson coordinates of the diagonal blocks -/

/-- The physical coordinate carrying the real part of the upper pair `σ.2` of block `σ.1`. -/
def reCoord (σ : Σ _ : Fin p.n, Johansson.UpperPair p.W) : p.GaussianCoordinate :=
  if σ.2.1.1 = σ.2.1.2 then .inl (site p σ.1 σ.2.1.1)
  else .inr (site p σ.1 σ.2.1.1, site p σ.1 σ.2.1.2, false)

/-- The physical coordinate carrying the imaginary part (a zero-variance label on the
diagonal). -/
def imCoord (σ : Σ _ : Fin p.n, Johansson.UpperPair p.W) : p.GaussianCoordinate :=
  .inr (site p σ.1 σ.2.1.1, site p σ.1 σ.2.1.2, true)

/-- All block coordinates. -/
def coordIdx : (Σ _ : Fin p.n, Johansson.UpperPair p.W) ⊕ (Σ _ : Fin p.n, Johansson.UpperPair p.W) →
    p.GaussianCoordinate :=
  Sum.elim (reCoord p) (imCoord p)

theorem coordIdx_injective : Function.Injective (coordIdx p) := by
  rintro (⟨j, ⟨⟨a, b⟩, hab⟩⟩ | ⟨j, ⟨⟨a, b⟩, hab⟩⟩) (⟨j', ⟨⟨a', b'⟩, hab'⟩⟩ | ⟨j', ⟨⟨a', b'⟩, hab'⟩⟩) h
  · by_cases h1 : a = b <;> by_cases h2 : a' = b' <;>
      simp only [coordIdx, Sum.elim_inl, reCoord, h1, h2, ↓reduceIte, Sum.inl.injEq,
        Sum.inr.injEq, Prod.mk.injEq, site_inj, reduceCtorEq, and_true] at h
    · obtain ⟨rfl, rfl⟩ := h
      subst h1 h2
      rfl
    · obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := h
      rfl
  · by_cases h1 : a = b <;>
      simp [coordIdx, reCoord, imCoord, h1] at h
  · by_cases h2 : a' = b' <;>
      simp [coordIdx, reCoord, imCoord, h2] at h
  · simp only [coordIdx, Sum.elim_inr, imCoord, Sum.inr.injEq, Prod.mk.injEq, site_inj,
      and_true] at h
    obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := h
    rfl

theorem reCoord_fresh (σ : Σ _ : Fin p.n, Johansson.UpperPair p.W) :
    PhysicalFresh.isFresh p Finset.univ (reCoord p σ) := by
  unfold reCoord
  split
  · exact Finset.mem_univ _
  · exact ⟨rfl, Finset.mem_univ _⟩

theorem imCoord_fresh (σ : Σ _ : Fin p.n, Johansson.UpperPair p.W) :
    PhysicalFresh.isFresh p Finset.univ (imCoord p σ) :=
  ⟨rfl, Finset.mem_univ _⟩

/-- The Johansson coordinates of all diagonal blocks, read off the physical coordinates. -/
def blockCoordsOf (z : p.GaussianCoordinate → ℝ) :
    Fin p.n → Johansson.UpperPair p.W → ℝ × ℝ :=
  fun j q => (z (reCoord p ⟨j, q⟩), z (imCoord p ⟨j, q⟩))

theorem measurable_blockCoordsOf : Measurable (blockCoordsOf p) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun _ =>
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)

theorem coordVar_off (j : Fin p.n) (a b : Fin p.W) (hab : a < b) (t : Bool) :
    p.gaussianCoordinateVariance (.inr (site p j a, site p j b, t)) =
      Real.toNNReal (p.c / p.W) / 2 := by
  have hlt : p.siteIndex (zblk p j, a) < p.siteIndex (zblk p j, b) :=
    (siteIndex_site_lt p j a b).mpr hab
  have hc : 0 ≤ p.c / p.W := div_nonneg p.c_pos.le (Nat.cast_nonneg _)
  apply NNReal.eq
  simp [Parameters.gaussianCoordinateVariance, hlt, Parameters.entryVariance, site,
    Real.coe_toNNReal _ hc]
  rfl

/-- Each block coordinate pair has the law `coordLaw (c/W)` of a `GUE_W(c/W)` coordinate. -/
theorem pair_law (σ : Σ _ : Fin p.n, Johansson.UpperPair p.W) :
    (gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p (.inl σ)))).prod
        (gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p (.inr σ)))) =
      SingularLogLaw.coordLaw (Real.toNNReal (p.c / p.W)) σ.2 := by
  rcases σ with ⟨j, ⟨⟨a, b⟩, hab⟩⟩
  by_cases h : a = b
  · subst h
    rw [SingularLogLaw.coordLaw_diag]
    have hc : 0 ≤ p.c / p.W := div_nonneg p.c_pos.le (Nat.cast_nonneg _)
    have h0 : p.gaussianCoordinateVariance (coordIdx p (.inr ⟨j, ⟨(a, a), hab⟩⟩)) = 0 := by
      simp [coordIdx, imCoord, Parameters.gaussianCoordinateVariance]
    have h1 : p.gaussianCoordinateVariance (coordIdx p (.inl ⟨j, ⟨(a, a), hab⟩⟩)) =
        Real.toNNReal (p.c / p.W) := by
      apply NNReal.eq
      simp [coordIdx, reCoord, Parameters.gaussianCoordinateVariance, Parameters.entryVariance,
        site, Real.coe_toNNReal _ hc]
      rfl
    rw [h0, h1, gaussianReal_zero_var, Measure.prod_dirac]
  · have hlt : a < b := lt_of_le_of_ne hab h
    rw [SingularLogLaw.coordLaw_offdiag _ a b hab h]
    have h1 : coordIdx p (.inl ⟨j, ⟨(a, b), hab⟩⟩) = .inr (site p j a, site p j b, false) := by
      simp [coordIdx, reCoord, h]
    have h2 : coordIdx p (.inr ⟨j, ⟨(a, b), hab⟩⟩) = .inr (site p j a, site p j b, true) := rfl
    rw [h1, h2, coordVar_off p j a b hlt, coordVar_off p j a b hlt]

/-- The physical coordinates of the blocks are independent Gaussians. -/
theorem hasLaw_coords (model : p.GaussianRingModel) :
    HasLaw (fun H t => p.gaussianExtraction H (coordIdx p t))
      (Measure.pi fun t => gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p t)))
      (model.law : Measure p.SiteMatrix) :=
  (model.iIndepFun_gaussianExtraction.precomp (coordIdx_injective p)).hasLaw_pi
    (fun _ => model.gaussianExtraction_coordinate_hasLaw _)

/-- The Johansson coordinates of the blocks have law `Π_j Π_q coordLaw (c/W) q`. -/
theorem hasLaw_blockCoordsOf (model : p.GaussianRingModel) :
    HasLaw (fun H => blockCoordsOf p (p.gaussianExtraction H))
      (Measure.pi fun _ : Fin p.n =>
        Measure.pi (SingularLogLaw.coordLaw (W := p.W) (Real.toNNReal (p.c / p.W))))
      (model.law : Measure p.SiteMatrix) := by
  have h1 := (measurePreserving_sumPiEquivProdPi
    (fun t => gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p t)))).hasLaw.comp
      (hasLaw_coords p model)
  have h2 := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    (Σ _ : Fin p.n, Johansson.UpperPair p.W)
    (fun σ => gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p (.inl σ))))
    (fun σ => gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p (.inr σ))))).symm.hasLaw.comp
      h1
  have h3 : (Measure.pi fun σ : (Σ _ : Fin p.n, Johansson.UpperPair p.W) =>
      (gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p (.inl σ)))).prod
        (gaussianReal 0 (p.gaussianCoordinateVariance (coordIdx p (.inr σ))))) =
      Measure.pi fun σ : (Σ _ : Fin p.n, Johansson.UpperPair p.W) =>
        SingularLogLaw.coordLaw (Real.toNNReal (p.c / p.W)) σ.2 := by
    congr 1
    funext σ
    exact pair_law p σ
  rw [h3] at h2
  exact hasLaw_curry (fun (_ : Fin p.n) q => SingularLogLaw.coordLaw (Real.toNNReal (p.c / p.W)) q)
    h2

/-! ## The presentation -/

/-- The Hermitian version of the sample in block coordinates. -/
def ringBlockMatrix (H : p.SiteMatrix) : Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ :=
  toBlockCoords p (p.physicalHermitianVersion H).1

/-- The diagonal blocks. -/
def ringA (H : p.SiteMatrix) : Fin p.n → Matrix (Fin p.W) (Fin p.W) ℂ :=
  diagonalBlocks (ringBlockMatrix p H)

/-- The bond part. -/
def ringD (H : p.SiteMatrix) : Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ :=
  offDiagonalBlocks (ringBlockMatrix p H)

theorem measurable_ringBlockMatrix : Measurable (ringBlockMatrix p) :=
  (measurable_toBlockCoords p).comp (measurable_subtype_coe.comp p.measurable_physicalHermitianVersion)

theorem ringBlockMatrix_isHermitian (H : p.SiteMatrix) : (ringBlockMatrix p H).IsHermitian :=
  toBlockCoords_isHermitian p (p.physicalHermitianVersion H).2

/-- Each diagonal block is the Johansson reconstruction of its coordinates. -/
theorem ringA_eq (H : p.SiteMatrix) (j : Fin p.n) :
    ringA p H j = Johansson.gaussianMatrixRaw (blockCoordsOf p (p.gaussianExtraction H) j) := by
  ext a b
  simp only [ringA, ringBlockMatrix, diagonalBlocks, toBlockCoords, Matrix.submatrix_apply,
    Parameters.physicalHermitianVersion, siteBlockEquiv_symm]
  by_cases h : a = b
  · subst h
    simp [Parameters.gaussianReconstruction, Johansson.gaussianMatrixRaw, blockCoordsOf, reCoord]
  · have hs : site p j a ≠ site p j b := fun e => h ((site_inj p).mp e).2
    by_cases hlt : a < b
    · have hi := (siteIndex_site_lt p j a b).mpr hlt
      apply Complex.ext <;>
        simp [Parameters.gaussianReconstruction, Johansson.gaussianMatrixRaw, blockCoordsOf,
          reCoord, imCoord, h, hs, hi, hlt.le, Johansson.complexPair]
    · have hi : ¬ p.siteIndex (site p j a) < p.siteIndex (site p j b) :=
        fun e => hlt ((siteIndex_site_lt p j a b).mp e)
      have hle : ¬ a ≤ b := fun e => hlt (lt_of_le_of_ne e h)
      apply Complex.ext <;>
        simp [Parameters.gaussianReconstruction, Johansson.gaussianMatrixRaw, blockCoordsOf,
          reCoord, imCoord, h, Ne.symm h, hs, hi, hle, Johansson.complexPair]

/-- The blocks as a function of the fresh (`R = univ`) coordinates. -/
def freshA (w : {i // PhysicalFresh.isFresh p Finset.univ i} → ℝ) :
    Fin p.n → Matrix (Fin p.W) (Fin p.W) ℂ :=
  fun j => Johansson.gaussianMatrixRaw fun q =>
    (w ⟨reCoord p ⟨j, q⟩, reCoord_fresh p _⟩, w ⟨imCoord p ⟨j, q⟩, imCoord_fresh p _⟩)

theorem measurable_freshA : Measurable (freshA p) :=
  measurable_pi_iff.mpr fun _ => measurable_gaussianMatrixRaw.comp
    (measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).prodMk (measurable_pi_apply _))

theorem ringA_eq_fresh (H : p.SiteMatrix) :
    ringA p H = freshA p (PhysicalFresh.freshCoords p Finset.univ H) := by
  funext j
  rw [ringA_eq]
  rfl

/-- The bond part as a function of the remaining coordinates. -/
def restD (w : {i // ¬PhysicalFresh.isFresh p Finset.univ i} → ℝ) :
    Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ :=
  offDiagonalBlocks (toBlockCoords p (p.gaussianReconstruction (PhysicalFresh.restExt p Finset.univ w)))

theorem measurable_restD : Measurable (restD p) :=
  measurable_offDiagonalBlocks.comp ((measurable_toBlockCoords p).comp
    (p.measurable_gaussianReconstruction.comp (PhysicalFresh.measurable_restExt p Finset.univ)))

theorem ringD_eq (H : p.SiteMatrix) :
    ringD p H = restD p (PhysicalFresh.restCoords p Finset.univ H) := by
  ext x y
  simp only [ringD, restD, offDiagonalBlocks, ringBlockMatrix, toBlockCoords,
    Matrix.submatrix_apply, Parameters.physicalHermitianVersion]
  by_cases h : x.1 = y.1
  · simp [h]
  · have hr := congrFun (congrFun (PhysicalFresh.reconstruction_rest p Finset.univ H)
      ((siteBlockEquiv p).symm x)) ((siteBlockEquiv p).symm y)
    have hne : ¬ (((siteBlockEquiv p).symm x).1 = ((siteBlockEquiv p).symm y).1 ∧
        ((siteBlockEquiv p).symm x).1 ∈ Finset.univ) := by
      rintro ⟨e, -⟩
      exact h ((zblk_inj p).mp e)
    simp only [withoutFreshBlocks, hne, ↓reduceIte] at hr
    simp only [h, ↓reduceIte]
    exact hr.symm

/-- The physical ring presented as a `BlockModel p.n p.W` on `(p.SiteMatrix, model.law)`. -/
def ringModel (model : p.GaussianRingModel) : BlockModel p.n p.W where
  Ω := p.SiteMatrix
  P := (model.law : Measure p.SiteMatrix)
  prob := inferInstance
  A := ringA p
  D := ringD p
  Y := fun _ => 0
  measurable_A := measurable_diagonalBlocks.comp (measurable_ringBlockMatrix p)
  measurable_D := measurable_offDiagonalBlocks.comp (measurable_ringBlockMatrix p)
  measurable_Y := measurable_const
  hermitian_A := fun H j => diagonalBlocks_isHermitian (ringBlockMatrix_isHermitian p H) j
  hermitian_D := fun H => offDiagonalBlocks_isHermitian (ringBlockMatrix_isHermitian p H)
  posSemidef_Y := fun _ => Matrix.PosSemidef.zero

/-- The ring presentation has independent `GUE_W(c/W)` blocks, independent of `(D, Y)`. -/
theorem ringModel_isIndependent (model : p.GaussianRingModel) :
    (ringModel p model).IsIndependent p.c := by
  have hB := hasLaw_blockCoordsOf p model
  have hmB : Measurable (fun H => blockCoordsOf p (p.gaussianExtraction H)) :=
    (measurable_blockCoordsOf p).comp p.measurable_gaussianExtraction
  refine ⟨fun j => ?_, ?_, ?_⟩
  · have hj := (hasLaw_gaussianMatrixRaw (Real.toNNReal (p.c / p.W))).fun_comp
      ((measurePreserving_eval _ j).hasLaw.fun_comp hB)
    exact hj.congr (Filter.Eventually.of_forall fun H => ringA_eq p H j)
  · have hi := (SingularLogLaw.iIndepFun_of_hasLaw_pi
      (fun j => (measurable_pi_apply j).comp hmB) hB).comp
        (fun _ => Johansson.gaussianMatrixRaw) (fun _ => measurable_gaussianMatrixRaw)
    have e : (fun j (H : p.SiteMatrix) => ringA p H j) = fun j =>
        Johansson.gaussianMatrixRaw ∘ (fun f => f j) ∘
          fun H => blockCoordsOf p (p.gaussianExtraction H) := by
      funext j H
      exact ringA_eq p H j
    change iIndepFun (fun j (H : p.SiteMatrix) => ringA p H j) (model.law : Measure p.SiteMatrix)
    rw [e]
    exact hi
  · have hφ : Measurable (fun w : {i // ¬PhysicalFresh.isFresh p Finset.univ i} → ℝ =>
        (restD p w, (0 : Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ))) :=
      (measurable_restD p).prodMk measurable_const
    have hi := (PhysicalFresh.fresh_rest_independent p Finset.univ model).symm.comp hφ
      (measurable_freshA p)
    have e1 : (fun H => (ringD p H, (0 : Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ))) =
        (fun w => (restD p w, (0 : Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ))) ∘
          PhysicalFresh.restCoords p Finset.univ := by
      funext H
      rw [Function.comp_apply, ringD_eq]
    have e2 : ringA p = freshA p ∘ PhysicalFresh.freshCoords p Finset.univ := by
      funext H
      exact ringA_eq_fresh p H
    change IndepFun (fun H => (ringD p H, (0 : Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ)))
      (ringA p) (model.law : Measure p.SiteMatrix)
    rw [e1, e2]
    exact hi

/-- The ring presentation presents the physical law in block coordinates. -/
theorem ringModel_presents (model : p.GaussianRingModel) :
    Presents (ringModel p model) ((model.law : Measure p.SiteMatrix).map (toBlockCoords p)) := by
  apply presents_of_pair _ _ (fun _ => rfl)
  change (model.law : Measure p.SiteMatrix).map (fun H => (ringA p H, ringD p H)) = _
  rw [Measure.map_map (measurable_diagonalBlocks.prodMk measurable_offDiagonalBlocks)
    (measurable_toBlockCoords p)]
  apply Measure.map_congr
  filter_upwards [model.isPhysical.1] with H hH
  have e : (p.physicalHermitianVersion H).1 = H := p.gaussianReconstruction_gaussianExtraction H hH
  simp [ringA, ringD, ringBlockMatrix, e]

end RingBlock

/-- `RingAsBlockModel`. Law: the physical law `model.law` of every admissible `p` and
every realization. The presentation lives on `(p.SiteMatrix, model.law)`; its blocks are the
diagonal blocks of the Hermitian version of the sample in block coordinates, independent with
law `GUE_W(c/W)` (`c = 1 - 2b`, Johansson coordinate normalization), `D` is its bond part,
independent of the blocks, and `Y = 0`; the joint law of (blocks, bonds), hence the law of
`H = D + ⊕_j A_j`, is that of `toBlockCoords p H` under `model.law`. No cited input. -/
theorem ringAsBlockModel_holds : Internal.Contracts.InputsRing.RingAsBlockModel :=
  fun p model => ⟨RingBlock.ringModel p model, RingBlock.ringModel_isIndependent p model,
    RingBlock.ringModel_presents p model⟩

end BlockBand.Wegner
