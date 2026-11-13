module

public import Mathlib
public import BlockBand.Wegner.PhysicalConditionalCountLaw

/-!
# The Peled–Schenker–Shamis–Sodin (PSSS) count conditional on bonds for the physical ring

A proof of `Internal.Contracts.Inputs.PhysicalBlockConditionalCount`: the count deformation and
the conditioning in the proof of the counting theorem.

Law: the physical ring law `model.law` on `p.SiteMatrix`, every admissible `p`, every
set `R` of blocks, every measurable Hermitian deformation `Φ` of the conditioning data
`withoutFreshBlocks p R H` (all bonds and all blocks outside `R`; no norm bound).

Proof. The physical Gaussian coordinates split into those of the `R`-diagonal blocks and
the rest (`fresh_rest_independent`). The normalized fresh blocks `freshNoise` are a function
of the first group and `withoutFreshBlocks p R H` of the second, both everywhere. With
`G = √c · freshNoise` and `D = (H_RR off the blocks) + Φ(rest)`, reindexed to
`Σ j : Fin |R|, Fin W`, the count of `H_RR + Φ(rest)` equals the count of `D + G`
(`subsystemCount_eq`, through `nativeEigenCount_hermitianReindex`), `D` is independent of
`G`, and `c^{-1/2} G` has the canonical PSSS law (`freshNoise_hasLaw`). The
generic adapter `conditionalBlockGUECount_holds` (with `t = c`) concludes. Only
`PSSS.SourceContract.{0}` is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Counting
open BlockBand.Internal.Contracts.Inputs (BlockSites withoutFreshBlocks subsystemCount)
open scoped NNReal

namespace PhysicalFresh

variable (p : Parameters) (R : Finset (ZMod p.n))

/-! ## Fresh and conditioning coordinates -/

/-- The physical Gaussian coordinates inside the diagonal blocks of `R`. -/
def isFresh : p.GaussianCoordinate → Prop
  | .inl x => x.1 ∈ R
  | .inr (x, y, _) => x.1 = y.1 ∧ x.1 ∈ R

instance : DecidablePred (isFresh p R) := by
  intro i
  rcases i with x | ⟨x, y, b⟩ <;> unfold isFresh <;> infer_instance

/-- The fresh coordinates of a sample. -/
def freshCoords (H : p.SiteMatrix) : {i // isFresh p R i} → ℝ :=
  fun i => p.gaussianExtraction H i.1

/-- The remaining (conditioning) coordinates of a sample. -/
def restCoords (H : p.SiteMatrix) : {i // ¬isFresh p R i} → ℝ :=
  fun i => p.gaussianExtraction H i.1

theorem measurable_freshCoords : Measurable (freshCoords p R) :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i.1).comp p.measurable_gaussianExtraction

theorem measurable_restCoords : Measurable (restCoords p R) :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i.1).comp p.measurable_gaussianExtraction

local instance gaussianReal_isProbability'' (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal μ v

/-- Under the physical law the fresh and the remaining coordinates are independent. -/
theorem fresh_rest_independent (model : p.GaussianRingModel) :
    IndepFun (freshCoords p R) (restCoords p R) (model.law : Measure p.SiteMatrix) := by
  have hsplit : HasLaw (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : p.GaussianCoordinate => ℝ)
      (isFresh p R))
      ((Measure.pi (fun i : {i // isFresh p R i} =>
          gaussianReal 0 (p.gaussianCoordinateVariance i.1))).prod
        (Measure.pi (fun i : {i // ¬isFresh p R i} =>
          gaussianReal 0 (p.gaussianCoordinateVariance i.1))))
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) :=
    ⟨(MeasurableEquiv.piEquivPiSubtypeProd _ _).measurable.aemeasurable,
      (measurePreserving_piEquivPiSubtypeProd
        (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) (isFresh p R)).map_eq⟩
  have hj : HasLaw (fun H => (freshCoords p R H, restCoords p R H))
      ((Measure.pi (fun i : {i // isFresh p R i} =>
          gaussianReal 0 (p.gaussianCoordinateVariance i.1))).prod
        (Measure.pi (fun i : {i // ¬isFresh p R i} =>
          gaussianReal 0 (p.gaussianCoordinateVariance i.1))))
      (model.law : Measure p.SiteMatrix) :=
    hsplit.comp ⟨p.measurable_gaussianExtraction.aemeasurable, model.gaussianExtraction_law⟩
  have hd : HasLaw (freshCoords p R)
      (Measure.pi (fun i : {i // isFresh p R i} =>
          gaussianReal 0 (p.gaussianCoordinateVariance i.1)))
      (model.law : Measure p.SiteMatrix) :=
    HasLaw.comp ⟨measurable_fst.aemeasurable, measurePreserving_fst.map_eq⟩ hj
  have he : HasLaw (restCoords p R)
      (Measure.pi (fun i : {i // ¬isFresh p R i} =>
          gaussianReal 0 (p.gaussianCoordinateVariance i.1)))
      (model.law : Measure p.SiteMatrix) :=
    HasLaw.comp ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩ hj
  exact (indepFun_iff_hasLaw_prodMk_prod hd he).mpr hj

/-- Extend fresh coordinates by zero. -/
def freshExt (z : {i // isFresh p R i} → ℝ) (i : p.GaussianCoordinate) : ℝ :=
  if h : isFresh p R i then z ⟨i, h⟩ else 0

/-- Extend the remaining coordinates by zero. -/
def restExt (z : {i // ¬isFresh p R i} → ℝ) (i : p.GaussianCoordinate) : ℝ :=
  if h : isFresh p R i then 0 else z ⟨i, h⟩

theorem measurable_freshExt : Measurable (freshExt p R) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold freshExt
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem measurable_restExt : Measurable (restExt p R) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold restExt
  split_ifs
  · exact measurable_const
  · exact measurable_pi_apply _

/-- The conditioning data depend only on the remaining coordinates (everywhere). -/
theorem reconstruction_rest (H : p.SiteMatrix) :
    withoutFreshBlocks p R (p.gaussianReconstruction (restExt p R (restCoords p R H))) =
      withoutFreshBlocks p R (p.gaussianReconstruction (p.gaussianExtraction H)) := by
  ext x y
  unfold withoutFreshBlocks
  by_cases h : x.1 = y.1 ∧ x.1 ∈ R
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · simp only [h, ↓reduceIte]
    have h1 : ∀ b, ¬isFresh p R (.inr (x, y, b)) := fun _ => h
    have h2 : ∀ b, ¬isFresh p R (.inr (y, x, b)) := fun _ hf =>
      h ⟨hf.1.symm, by rw [← hf.1]; exact hf.2⟩
    unfold Parameters.gaussianReconstruction
    split_ifs with hxy hlt
    · subst hxy
      have h3 : ¬isFresh p R (.inl x) := fun hf => h ⟨rfl, hf⟩
      simp [restExt, restCoords, h3]
    · simp [restExt, restCoords, h1]
    · simp [restExt, restCoords, h2]

/-- Within a block of `R` the reconstruction only uses fresh coordinates. -/
theorem reconstruction_fresh (H : p.SiteMatrix) (s t : p.Site) (hst : s.1 = t.1)
    (hs : s.1 ∈ R) :
    p.gaussianReconstruction (freshExt p R (freshCoords p R H)) s t =
      p.gaussianReconstruction (p.gaussianExtraction H) s t := by
  have h1 : ∀ b, isFresh p R (.inr (s, t, b)) := fun _ => ⟨hst, hs⟩
  have h2 : ∀ b, isFresh p R (.inr (t, s, b)) := fun _ => ⟨hst.symm, by rw [← hst]; exact hs⟩
  have h3 : isFresh p R (.inl s) := hs
  unfold Parameters.gaussianReconstruction
  split_ifs with hxy hlt
  · subst hxy
    simp [freshExt, freshCoords, h3]
  · simp [freshExt, freshCoords, h1]
  · simp [freshExt, freshCoords, h2]

/-- The fresh blocks as a function of the fresh coordinates. -/
def freshFromCoords (z : {i // isFresh p R i} → ℝ) :
    Matrix (Index (sizes p R)) (Index (sizes p R)) ℂ := fun x y =>
  if x.1 = y.1 then
    (Real.sqrt p.c : ℂ)⁻¹ *
      p.gaussianReconstruction (freshExt p R z) (siteEquiv p R x).1 (siteEquiv p R y).1
  else 0

theorem measurable_freshFromCoords : Measurable (freshFromCoords p R) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold freshFromCoords
  split_ifs
  · exact ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (p.measurable_gaussianReconstruction.comp (measurable_freshExt p R)))).const_mul _
  · exact measurable_const

theorem freshNoise_eq (H : p.SiteMatrix) :
    freshNoise p R H = freshFromCoords p R (freshCoords p R H) := by
  ext x y
  simp only [freshNoise, Matrix.submatrix_apply, Parameters.nativeDiagonalMatrix,
    nativeSite_block_iff, nativeSiteEquiv_nativeSite, freshFromCoords,
    Parameters.normalizedMatrix_apply]
  split_ifs with h
  · rw [reconstruction_fresh p R H _ _ ((siteEquiv_block_iff p R x y).mpr h)
      (siteEquiv p R x).2]
  · rfl

/-! ## The deformation and the noise -/

/-- Removing the fresh blocks preserves hermiticity. -/
theorem withoutFreshBlocks_isHermitian {M : p.SiteMatrix} (hM : M.IsHermitian) :
    (withoutFreshBlocks p R M).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, withoutFreshBlocks]
  by_cases h : x.1 = y.1 ∧ x.1 ∈ R
  · have h' : y.1 = x.1 ∧ y.1 ∈ R := ⟨h.1.symm, by rw [← h.1]; exact h.2⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true h), star_zero]
  · have h' : ¬(y.1 = x.1 ∧ y.1 ∈ R) := fun h' => h ⟨h'.1.symm, by rw [← h'.1]; exact h'.2⟩
    simp only [h, h', ↓reduceIte]
    exact hM.apply x y

theorem measurable_withoutFreshBlocks : Measurable (withoutFreshBlocks p R) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold withoutFreshBlocks
  split_ifs
  · exact measurable_const
  · exact (measurable_pi_apply y).comp (measurable_pi_apply x)

/-- The conditioning data: all bonds and every block outside `R`. -/
def background (H : p.SiteMatrix) : p.SiteMatrix :=
  withoutFreshBlocks p R (p.physicalHermitianVersion H).1

theorem measurable_background : Measurable (background p R) :=
  (measurable_withoutFreshBlocks p R).comp
    (measurable_subtype_coe.comp p.measurable_physicalHermitianVersion)

theorem background_isHermitian (H : p.SiteMatrix) : (background p R H).IsHermitian :=
  withoutFreshBlocks_isHermitian p R (p.physicalHermitianVersion H).2

variable {p R} in
/-- `A_RR + Φ(A)`, reindexed to `Σ j : Fin |R|, Fin W`. -/
def deformationOf (Φ : p.SiteMatrix → HermitianMatrix (BlockSites p R))
    (A : HermitianMatrix p.Site) : HermitianMatrix (Index (sizes p R)) :=
  hermitianReindex (siteEquiv p R).symm
    ⟨A.1.submatrix Subtype.val Subtype.val + (Φ A.1).1, (A.2.submatrix _).add (Φ A.1).2⟩

variable {p R} in
theorem measurable_deformationOf (Φ : p.SiteMatrix → HermitianMatrix (BlockSites p R))
    (hΦ : Measurable Φ) : Measurable (deformationOf Φ) := by
  apply (measurable_hermitianReindex _).comp
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  have hA : Measurable (fun A : HermitianMatrix p.Site => A.1 x.1 y.1) :=
    (measurable_pi_apply y.1).comp ((measurable_pi_apply x.1).comp measurable_subtype_coe)
  have hB : Measurable (fun A : HermitianMatrix p.Site => (Φ A.1).1 x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      (measurable_subtype_coe.comp (hΦ.comp measurable_subtype_coe)))
  exact hA.add hB

/-- The deformation `D = (H_RR off the fresh blocks) + Φ(rest)`, a function of the
conditioning data only. -/
def deformation (Φ : p.SiteMatrix → HermitianMatrix (BlockSites p R)) (H : p.SiteMatrix) :
    HermitianMatrix (Index (sizes p R)) :=
  BlockBand.Model.Construction.rawHermitianExtension (deformationOf Φ)
    ⟨0, Matrix.isHermitian_zero⟩ (background p R H)

theorem measurable_deformation (Φ : p.SiteMatrix → HermitianMatrix (BlockSites p R))
    (hΦ : Measurable Φ) : Measurable (deformation p R Φ) :=
  (BlockBand.Model.Construction.measurable_rawHermitianExtension _
    (measurable_deformationOf Φ hΦ) _).comp (measurable_background p R)

/-- The noise `G = √c · freshNoise`: the fresh blocks `H_jj`, `j ∈ R`, reindexed. -/
def noise (H : p.SiteMatrix) : HermitianMatrix (Index (sizes p R)) :=
  hermitianScale (Real.sqrt p.c) ⟨freshNoise p R H, freshNoise_isHermitian p R H⟩

theorem measurable_noise : Measurable (noise p R) :=
  (measurable_hermitianScale _).comp (Measurable.subtype_mk (measurable_freshNoise p R))

/-- Under the physical law the deformation is independent of the noise. -/
theorem deformation_noise_independent (model : p.GaussianRingModel)
    (Φ : p.SiteMatrix → HermitianMatrix (BlockSites p R)) (hΦ : Measurable Φ) :
    IndepFun (deformation p R Φ) (noise p R) (model.law : Measure p.SiteMatrix) := by
  have hφ : Measurable (fun z : {i // ¬isFresh p R i} → ℝ =>
      BlockBand.Model.Construction.rawHermitianExtension (deformationOf Φ)
        ⟨0, Matrix.isHermitian_zero⟩
        (withoutFreshBlocks p R (p.gaussianReconstruction (restExt p R z)))) :=
    (BlockBand.Model.Construction.measurable_rawHermitianExtension _
      (measurable_deformationOf Φ hΦ) _).comp ((measurable_withoutFreshBlocks p R).comp
        (p.measurable_gaussianReconstruction.comp (measurable_restExt p R)))
  have hψ : Measurable (fun z : {i // isFresh p R i} → ℝ =>
      hermitianScale (Real.sqrt p.c)
        (BlockBand.Model.Construction.rawHermitianExtension id ⟨0, Matrix.isHermitian_zero⟩
          (freshFromCoords p R z))) :=
    (measurable_hermitianScale _).comp
      ((BlockBand.Model.Construction.measurable_rawHermitianExtension id measurable_id _).comp
        (measurable_freshFromCoords p R))
  have h := (fresh_rest_independent p R model).symm.comp hφ hψ
  convert h using 1
  · funext H
    change _ = BlockBand.Model.Construction.rawHermitianExtension (deformationOf Φ) _
      (withoutFreshBlocks p R (p.gaussianReconstruction (restExt p R (restCoords p R H))))
    rw [reconstruction_rest]
    rfl
  · funext H
    change _ = hermitianScale (Real.sqrt p.c)
      (BlockBand.Model.Construction.rawHermitianExtension id _
        (freshFromCoords p R (freshCoords p R H)))
    rw [← freshNoise_eq, BlockBand.Model.Construction.rawHermitianExtension_eq id _ _
      (freshNoise_isHermitian p R H)]
    rfl

/-- Deterministic count identity: the count of `H_RR + Φ(rest)` is the count of `D + G`. -/
theorem subsystemCount_eq (Φ : p.SiteMatrix → HermitianMatrix (BlockSites p R)) (J : Set ℝ)
    (H : p.SiteMatrix) :
    subsystemCount p R Φ J H =
      eigenCount ⟨(deformation p R Φ H).1 + (noise p R H).1,
        (deformation p R Φ H).2.add (noise p R H).2⟩ J := by
  have hD : deformation p R Φ H = deformationOf Φ ⟨background p R H, background_isHermitian p R H⟩ :=
    BlockBand.Model.Construction.rawHermitianExtension_eq _ _ _ (background_isHermitian p R H)
  have hc : (Real.sqrt p.c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.c_pos).ne'
  have hM : (⟨(deformation p R Φ H).1 + (noise p R H).1,
      (deformation p R Φ H).2.add (noise p R H).2⟩ : HermitianMatrix (Index (sizes p R))) =
      hermitianReindex (siteEquiv p R).symm
        ⟨(p.physicalHermitianVersion H).1.submatrix Subtype.val Subtype.val +
            (Φ (background p R H)).1,
          ((p.physicalHermitianVersion H).2.submatrix _).add (Φ (background p R H)).2⟩ := by
    apply Subtype.ext
    rw [hD]
    ext x y
    by_cases h : x.1 = y.1
    · have h' : (siteEquiv p R x).1.1 = (siteEquiv p R y).1.1 :=
        (siteEquiv_block_iff p R x y).mpr h
      simp [deformationOf, hermitianReindex, noise, hermitianScale, freshNoise,
        Parameters.nativeDiagonalMatrix, nativeSite_block_iff, nativeSiteEquiv_nativeSite,
        background, withoutFreshBlocks, Parameters.normalizedMatrix_apply,
        Parameters.physicalHermitianVersion, h, h', (siteEquiv p R y).2, hc, add_comm]
    · have h' : ¬(siteEquiv p R x).1.1 = (siteEquiv p R y).1.1 :=
        fun e => h ((siteEquiv_block_iff p R x y).mp e)
      simp [deformationOf, hermitianReindex, noise, hermitianScale, freshNoise,
        Parameters.nativeDiagonalMatrix, nativeSite_block_iff,
        background, withoutFreshBlocks, Parameters.physicalHermitianVersion, h, h']
  unfold subsystemCount
  rw [hM, nativeEigenCount_hermitianReindex]
  rfl

end PhysicalFresh

open PhysicalFresh in

/-- `PhysicalBlockConditionalCount`. Law: the physical ring law `model.law`. The
constant `C` is the one of `conditionalBlockGUECount_holds` (the PSSS constant `source.C`),
chosen before `p`, `model`, `R`, `Φ`, `a ≤ b` and `r ≥ 1`. For every set `R` of blocks (empty
allowed) and every measurable Hermitian deformation `Φ` of the conditioning data (bonds and
blocks outside `R`, no norm bound), the factorial moments of the count of `H_RR + Φ(rest)` on
`[a,b]` are integrable and at most `(C/√c · |R|W · (b-a))^r`. Uses only
`PSSS.SourceContract.{0}`. -/
theorem physicalBlockConditionalCount_holds (source : PSSS.SourceContract.{0}) :
    Internal.Contracts.Inputs.PhysicalBlockConditionalCount := by
  obtain ⟨C, hC, hgen⟩ := conditionalBlockGUECount_holds source
  refine ⟨C, hC, ?_⟩
  intro p model R Φ hΦ a b hab r hr
  have hc : (Real.sqrt p.c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.c_pos).ne'
  have hlaw : HasLaw (fun H => ((Real.sqrt p.c)⁻¹ : ℂ) • (noise p R H).1)
      ((canonicalMatrixMeasure (sizes p R) (sizes_pos p R)).map Subtype.val)
      (model.law : Measure p.SiteMatrix) := by
    have he : (fun H => ((Real.sqrt p.c)⁻¹ : ℂ) • (noise p R H).1) =
        fun H => freshNoise p R H := by
      funext H
      ext x y
      simp only [noise, hermitianScale, Matrix.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [he]
    exact freshNoise_hasLaw p R model
  have key := hgen p.SiteMatrix (model.law : Measure p.SiteMatrix) R.card (sizes p R)
    (sizes_pos p R) p.c p.c_pos (noise p R) (deformation p R Φ) (measurable_noise p R)
    (measurable_deformation p R Φ hΦ) hlaw (deformation_noise_independent p R model Φ hΦ)
    a b hab r hr
  have hcount : subsystemCount p R Φ (Icc a b) = fun H =>
      eigenCount ⟨(deformation p R Φ H).1 + (noise p R H).1,
        (deformation p R Φ H).2.add (noise p R H).2⟩ (Icc a b) :=
    funext (subsystemCount_eq p R Φ (Icc a b))
  have hdim : ((∑ j, sizes p R j : ℕ) : ℝ) = ((R.card * p.W : ℕ) : ℝ) := by
    simp
  rw [hcount]
  rw [hdim] at key
  exact key

end BlockBand.Wegner
