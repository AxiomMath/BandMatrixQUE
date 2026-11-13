module
public import BlockBand.Counting.PhysicalBlockProduct
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product decomposition into diagonal blocks and background

The Gaussian coordinates of the physical ring split into the diagonal-block coordinates and
the exterior coordinates, which are independent.  Consequently the normalized diagonal
GUE blocks are independent of the normalized off-diagonal background, the law of `H + A`
is the pushforward of the product of the background law and the GUE block law, and
physical expectations can be computed by integrating over the GUE blocks at fixed
background.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

/-- Full real labels within one physical diagonal block; all other labels are exterior. -/
def isDiagonalGaussianCoordinate (p : BlockBand.Parameters) : p.GaussianCoordinate → Prop
  | .inl _ => True
  | .inr (x, y, _) => x.1 = y.1

instance (p : BlockBand.Parameters) : DecidablePred p.isDiagonalGaussianCoordinate := by
  intro i
  cases i <;> unfold isDiagonalGaussianCoordinate <;> infer_instance

abbrev DiagonalGaussianCoordinate (p : BlockBand.Parameters) :=
  {i : p.GaussianCoordinate // p.isDiagonalGaussianCoordinate i}
abbrev ExteriorGaussianCoordinate (p : BlockBand.Parameters) :=
  {i : p.GaussianCoordinate // ¬p.isDiagonalGaussianCoordinate i}

def diagonalGaussianCoordinates (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.DiagonalGaussianCoordinate → ℝ := fun i => p.gaussianExtraction H i.1

def exteriorGaussianCoordinates (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.ExteriorGaussianCoordinate → ℝ := fun i => p.gaussianExtraction H i.1

theorem measurable_diagonalGaussianCoordinates (p : BlockBand.Parameters) :
    Measurable p.diagonalGaussianCoordinates :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i.1).comp p.measurable_gaussianExtraction

theorem measurable_exteriorGaussianCoordinates (p : BlockBand.Parameters) :
    Measurable p.exteriorGaussianCoordinates :=
  measurable_pi_iff.mpr fun i => (measurable_pi_apply i.1).comp p.measurable_gaussianExtraction

/-- The coordinate partition has the independent product law. -/
theorem GaussianRingModel.diagonal_exterior_coordinates_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw (fun H => (p.diagonalGaussianCoordinates H, p.exteriorGaussianCoordinates H))
      ((Measure.pi (fun i : p.DiagonalGaussianCoordinate => gaussianReal 0 (p.gaussianCoordinateVariance i.1))).prod
        (Measure.pi (fun i : p.ExteriorGaussianCoordinate => gaussianReal 0 (p.gaussianCoordinateVariance i.1))))
      (model.law : Measure p.SiteMatrix) := by
  have hsplit : HasLaw (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : p.GaussianCoordinate => ℝ)
      p.isDiagonalGaussianCoordinate)
      ((Measure.pi (fun i : p.DiagonalGaussianCoordinate => gaussianReal 0 (p.gaussianCoordinateVariance i.1))).prod
        (Measure.pi (fun i : p.ExteriorGaussianCoordinate => gaussianReal 0 (p.gaussianCoordinateVariance i.1))))
      (p.gaussianCoordinatesLaw : Measure (p.GaussianCoordinate → ℝ)) :=
    ⟨(MeasurableEquiv.piEquivPiSubtypeProd _ _).measurable.aemeasurable,
      (measurePreserving_piEquivPiSubtypeProd
        (fun i => gaussianReal 0 (p.gaussianCoordinateVariance i)) p.isDiagonalGaussianCoordinate).map_eq⟩
  exact hsplit.comp ⟨p.measurable_gaussianExtraction.aemeasurable, model.gaussianExtraction_law⟩

/-- The complete diagonal and complete exterior coordinate groups are independent. -/
theorem GaussianRingModel.diagonal_exterior_coordinates_independent {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    IndepFun p.diagonalGaussianCoordinates p.exteriorGaussianCoordinates (model.law : Measure p.SiteMatrix) := by
  have hd := HasLaw.comp
    ⟨measurable_fst.aemeasurable, measurePreserving_fst.map_eq⟩ model.diagonal_exterior_coordinates_hasLaw
  have he := HasLaw.comp
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩ model.diagonal_exterior_coordinates_hasLaw
  exact (indepFun_iff_hasLaw_prodMk_prod hd he).mpr model.diagonal_exterior_coordinates_hasLaw

/-- Every block-internal label belongs to the complete diagonal group. -/
theorem blockGUECoordinateInclusion_diagonal (p : BlockBand.Parameters) (k : ZMod p.n)
    (i : p.BlockGUECoordinate) : p.isDiagonalGaussianCoordinate (p.blockGUECoordinateInclusion k i) := by
  cases i <;> simp [isDiagonalGaussianCoordinate, blockGUECoordinateInclusion]

/-- Normalized diagonal GUE matrix family reconstructed solely from diagonal labels. -/
def diagonalBlocksFromCoordinates (p : BlockBand.Parameters)
    (z : p.DiagonalGaussianCoordinate → ℝ) : ZMod p.n → p.BlockGUEMatrix :=
  fun k => p.blockGUEReconstruction (fun i => (Real.sqrt p.c)⁻¹ *
    z ⟨p.blockGUECoordinateInclusion k i, p.blockGUECoordinateInclusion_diagonal k i⟩)

theorem measurable_diagonalBlocksFromCoordinates (p : BlockBand.Parameters) :
    Measurable p.diagonalBlocksFromCoordinates := by
  apply measurable_pi_iff.mpr
  intro k
  apply p.measurable_blockGUEReconstruction.comp
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply _).const_mul _

/-- Extend exterior labels by zero on every diagonal-block coordinate. -/
def exteriorCoordinatesExtension (p : BlockBand.Parameters)
    (z : p.ExteriorGaussianCoordinate → ℝ) (i : p.GaussianCoordinate) : ℝ :=
  if h : p.isDiagonalGaussianCoordinate i then 0 else z ⟨i, h⟩

def offDiagonalFromCoordinates (p : BlockBand.Parameters)
    (z : p.ExteriorGaussianCoordinate → ℝ) : p.SiteMatrix :=
  p.normalizedMatrix (p.gaussianReconstruction (p.exteriorCoordinatesExtension z))

theorem measurable_offDiagonalFromCoordinates (p : BlockBand.Parameters) :
    Measurable p.offDiagonalFromCoordinates := by
  unfold offDiagonalFromCoordinates normalizedMatrix
  apply (show Measurable (fun M : p.SiteMatrix => ((Real.sqrt p.c : ℂ)⁻¹) • M) from by fun_prop).comp
  apply p.measurable_gaussianReconstruction.comp
  apply measurable_pi_iff.mpr
  intro i
  unfold exteriorCoordinatesExtension
  split_ifs <;> fun_prop

/-- Normalized matrix background: exactly the cross-block entries. -/
def normalizedOffDiagonalBackground (p : BlockBand.Parameters) (H : p.SiteMatrix) : p.SiteMatrix :=
  fun x y => if x.1 = y.1 then 0 else p.normalizedMatrix H x y

theorem measurable_normalizedOffDiagonalBackground (p : BlockBand.Parameters) :
    Measurable p.normalizedOffDiagonalBackground := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold normalizedOffDiagonalBackground normalizedMatrix
  split_ifs <;> fun_prop

/-- The normalized background is Hermitian on every Hermitian input. -/
theorem normalizedOffDiagonalBackground_isHermitian (p : BlockBand.Parameters)
    (H : p.SiteMatrix) (hH : H.IsHermitian) : (p.normalizedOffDiagonalBackground H).IsHermitian := by
  ext x y
  simp only [Matrix.conjTranspose_apply, normalizedOffDiagonalBackground]
  by_cases h : x.1 = y.1
  · rw [ite_eq_left h.symm, ite_eq_left h]
    simp
  · simp [h, Ne.symm h, normalizedMatrix_apply, hH.apply x y]

/-- Exact exterior reconstruction on the canonical physical coordinate representation. -/
theorem offDiagonalFromCoordinates_extraction (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    p.offDiagonalFromCoordinates (p.exteriorGaussianCoordinates H) =
      p.normalizedOffDiagonalBackground (p.gaussianReconstruction (p.gaussianExtraction H)) := by
  ext x y
  rcases x with ⟨k, a⟩
  rcases y with ⟨l, b⟩
  by_cases hblock : k = l
  · subst l
    simp [offDiagonalFromCoordinates, exteriorCoordinatesExtension,
      normalizedOffDiagonalBackground, normalizedMatrix_apply, gaussianReconstruction,
      isDiagonalGaussianCoordinate]
  · have hyx : l ≠ k := Ne.symm hblock
    have hxy : (k, a) ≠ (l, b) := fun h => hblock (congrArg Prod.fst h)
    simp [offDiagonalFromCoordinates, exteriorCoordinatesExtension, exteriorGaussianCoordinates,
      normalizedOffDiagonalBackground, normalizedMatrix_apply, gaussianReconstruction,
      isDiagonalGaussianCoordinate, hblock, hyx, hxy]

/-- Diagonal reconstruction holds outside the non-Hermitian null set. -/
theorem GaussianRingModel.ae_diagonalBlocksFromCoordinates {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    (fun H => p.diagonalBlocksFromCoordinates (p.diagonalGaussianCoordinates H)) =ᵐ[
      (model.law : Measure p.SiteMatrix)] p.normalizedDiagonalBlocks := by
  exact model.ae_blockGUEReconstruction_normalizedCoordinates

/-- Exterior reconstruction holds outside the non-Hermitian null set. -/
theorem GaussianRingModel.ae_offDiagonalFromCoordinates {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    (fun H => p.offDiagonalFromCoordinates (p.exteriorGaussianCoordinates H)) =ᵐ[
      (model.law : Measure p.SiteMatrix)] p.normalizedOffDiagonalBackground := by
  filter_upwards [model.isPhysical.1] with H hH
  rw [p.offDiagonalFromCoordinates_extraction, p.gaussianReconstruction_gaussianExtraction H hH]

/-- All normalized diagonal GUE blocks are independent of the complete normalized background. -/
theorem GaussianRingModel.diagonalBlocks_background_independent {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    IndepFun p.normalizedDiagonalBlocks p.normalizedOffDiagonalBackground (model.law : Measure p.SiteMatrix) := by
  have h := model.diagonal_exterior_coordinates_independent.comp
    p.measurable_diagonalBlocksFromCoordinates p.measurable_offDiagonalFromCoordinates
  exact h.congr model.ae_diagonalBlocksFromCoordinates model.ae_offDiagonalFromCoordinates

/-- Normalized background marginal law. -/
def GaussianRingModel.normalizedBackgroundLaw {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    Measure p.SiteMatrix := Measure.map p.normalizedOffDiagonalBackground (model.law : Measure p.SiteMatrix)

instance {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    IsProbabilityMeasure model.normalizedBackgroundLaw := by
  unfold GaussianRingModel.normalizedBackgroundLaw
  exact (Measure.isProbabilityMeasure_map_iff p.measurable_normalizedOffDiagonalBackground.aemeasurable).mpr inferInstance

/-- The background law has Hermitian support; a background sample can be fixed as
a Hermitian deformation before a block-GUE estimate is used. -/
theorem GaussianRingModel.normalizedBackgroundLaw_ae_isHermitian {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    ∀ᵐ B ∂model.normalizedBackgroundLaw, B.IsHermitian := by
  unfold GaussianRingModel.normalizedBackgroundLaw
  rw [ae_map_iff p.measurable_normalizedOffDiagonalBackground.aemeasurable]
  · filter_upwards [model.isPhysical.1] with H hH
    exact p.normalizedOffDiagonalBackground_isHermitian H hH
  · exact (isClosed_eq
      (by fun_prop : Continuous (fun B : p.SiteMatrix => B.conjTranspose)) continuous_id).measurableSet

/-- Joint law of the background and the GUE blocks is the product law. -/
theorem GaussianRingModel.background_diagonalBlocks_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw (fun H => (p.normalizedOffDiagonalBackground H, p.normalizedDiagonalBlocks H))
      (model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw)))
      (model.law : Measure p.SiteMatrix) :=
  model.diagonalBlocks_background_independent.symm.hasLaw_prod
    ⟨p.measurable_normalizedOffDiagonalBackground.aemeasurable, rfl⟩ model.normalizedDiagonalBlocks_hasLaw

/-- Embed a family of `W`-dimensional GUE blocks as a block-diagonal physical matrix. -/
def blockDiagonalMatrix (p : BlockBand.Parameters) (G : ZMod p.n → p.BlockGUEMatrix) : p.SiteMatrix :=
  fun x y => if x.1 = y.1 then G x.1 x.2 y.2 else 0

/-- Reconstruction of `H + A` from the background and the blocks, rescaled by `sqrt c`,
for any deterministic deformation `A`. -/
def freshDeformedMatrix (p : BlockBand.Parameters) (A : p.SiteMatrix)
    (z : p.SiteMatrix × (ZMod p.n → p.BlockGUEMatrix)) : p.SiteMatrix :=
  (Real.sqrt p.c : ℂ) • (z.1 + p.blockDiagonalMatrix z.2 + p.normalizedMatrix A)

theorem measurable_freshDeformedMatrix (p : BlockBand.Parameters) (A : p.SiteMatrix) :
    Measurable (p.freshDeformedMatrix A) := by
  unfold freshDeformedMatrix blockDiagonalMatrix
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  change Measurable (fun z : p.SiteMatrix × (ZMod p.n → p.BlockGUEMatrix) =>
    (Real.sqrt p.c : ℂ) * (z.1 x y + (if x.1 = y.1 then z.2 x.1 x.2 y.2 else 0) +
      p.normalizedMatrix A x y))
  split_ifs <;> fun_prop

/-- Deterministic reconstruction of `H + A`, valid for arbitrary `A`. -/
theorem freshDeformedMatrix_actual (p : BlockBand.Parameters) (A H : p.SiteMatrix) :
    p.freshDeformedMatrix A (p.normalizedOffDiagonalBackground H, p.normalizedDiagonalBlocks H) = H + A := by
  have hs : (Real.sqrt p.c : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr p.c_pos).ne'
  ext x y
  rcases x with ⟨k, a⟩
  rcases y with ⟨l, b⟩
  by_cases h : k = l
  · subst l
    simp [freshDeformedMatrix, normalizedOffDiagonalBackground, blockDiagonalMatrix,
      normalizedDiagonalBlocks, normalizedMatrix_apply, mul_add, hs]
  · simp [freshDeformedMatrix, normalizedOffDiagonalBackground, blockDiagonalMatrix,
      normalizedMatrix_apply, h, mul_add, hs]

/-- The law of `H + A` is the pushforward of the product of the background law and the
independent GUE block law. -/
theorem GaussianRingModel.deformedMatrix_freshProduct_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : p.SiteMatrix) :
    HasLaw (fun H => H + A)
      (Measure.map (p.freshDeformedMatrix A)
        (model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))))
      (model.law : Measure p.SiteMatrix) := by
  have h := HasLaw.comp ⟨(p.measurable_freshDeformedMatrix A).aemeasurable, rfl⟩
    model.background_diagonalBlocks_hasLaw
  exact h.congr (Filter.Eventually.of_forall fun H => (p.freshDeformedMatrix_actual A H).symm)

/-- Normalized law of `H + A`, exposing the normalized GUE diagonal blocks
before the `sqrt c` spectral scaling.  `A` may have arbitrary norm. -/
theorem GaussianRingModel.normalizedDeformedMatrix_freshProduct_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : p.SiteMatrix) :
    HasLaw (fun H => p.normalizedMatrix (H + A))
      (Measure.map (fun z : p.SiteMatrix × (ZMod p.n → p.BlockGUEMatrix) =>
        z.1 + p.blockDiagonalMatrix z.2 + p.normalizedMatrix A)
        (model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))))
      (model.law : Measure p.SiteMatrix) := by
  have hm : Measurable (fun z : p.SiteMatrix × (ZMod p.n → p.BlockGUEMatrix) =>
      z.1 + p.blockDiagonalMatrix z.2 + p.normalizedMatrix A) := by
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro y
    unfold blockDiagonalMatrix
    change Measurable (fun z : p.SiteMatrix × (ZMod p.n → p.BlockGUEMatrix) =>
      z.1 x y + (if x.1 = y.1 then z.2 x.1 x.2 y.2 else 0) + p.normalizedMatrix A x y)
    split_ifs <;> fun_prop
  have h := HasLaw.comp ⟨hm.aemeasurable, rfl⟩ model.background_diagonalBlocks_hasLaw
  apply h.congr
  filter_upwards with H
  ext x y
  rcases x with ⟨k, a⟩
  rcases y with ⟨l, b⟩
  by_cases hkl : k = l
  · subst l
    simp [normalizedOffDiagonalBackground, blockDiagonalMatrix,
      normalizedDiagonalBlocks, normalizedMatrix_apply, mul_add]
  · simp [normalizedOffDiagonalBackground, blockDiagonalMatrix,
      normalizedMatrix_apply, hkl, mul_add]

/-- Exact physical expectation as a fresh product integral, for any measurable observable.
No integrability or bound is assumed in this identity. -/
theorem GaussianRingModel.integral_deformedMatrix_freshProduct {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : p.SiteMatrix) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : p.SiteMatrix → E)
    (hf : AEStronglyMeasurable f
      (Measure.map (p.freshDeformedMatrix A)
        (model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))))) :
    (∫ H, f (H + A) ∂(model.law : Measure p.SiteMatrix)) =
      ∫ z, f (p.freshDeformedMatrix A z)
        ∂(model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))) := by
  have h := (model.deformedMatrix_freshProduct_hasLaw A).integral_comp hf
  rw [integral_map (p.measurable_freshDeformedMatrix A).aemeasurable hf] at h
  exact h

/-- Nonnegative physical expectation as a product integral, allowing infinite values.
No integrability assumption is needed. -/
theorem GaussianRingModel.lintegral_deformedMatrix_freshProduct {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : p.SiteMatrix) (f : p.SiteMatrix → ℝ≥0∞)
    (hf : AEMeasurable f
      (Measure.map (p.freshDeformedMatrix A)
        (model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))))) :
    (∫⁻ H, f (H + A) ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ z, f (p.freshDeformedMatrix A z)
        ∂(model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))) := by
  have h := (model.deformedMatrix_freshProduct_hasLaw A).lintegral_comp hf
  rw [lintegral_map' hf (p.measurable_freshDeformedMatrix A).aemeasurable] at h
  exact h

/-- Fixed-background Tonelli representation of the physical nonnegative
expectation.  The inner law is the independent normalized GUE block product.
This is the conditioning identity used before applying the PSSS estimate. -/
theorem GaussianRingModel.lintegral_deformedMatrix_conditionedGUE {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : p.SiteMatrix) (f : p.SiteMatrix → ℝ≥0∞)
    (hf : AEMeasurable f
      (Measure.map (p.freshDeformedMatrix A)
        (model.normalizedBackgroundLaw.prod (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))))) :
    (∫⁻ H, f (H + A) ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ B, ∫⁻ G, f (p.freshDeformedMatrix A (B, G))
        ∂(Measure.pi (fun _ : ZMod p.n => p.blockGUELaw)) ∂model.normalizedBackgroundLaw := by
  rw [model.lintegral_deformedMatrix_freshProduct A f hf]
  exact lintegral_prod _ (hf.comp_aemeasurable' (p.measurable_freshDeformedMatrix A).aemeasurable)

end BlockBand.Parameters
