module
public import BlockBand.Counting.PhysicalBlockCoordinates

/-!
# Normalized GUE matrices and their independent block law

The normalized diagonal blocks `G_k = c^{-1/2} H_{I_k I_k}` of the physical Gaussian ring
are reconstructed from their Gaussian coordinates; their joint law is the product of
independent `GUE_W(1/W)` laws.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open scoped NNReal ComplexConjugate

abbrev BlockGUEMatrix (p : BlockBand.Parameters) := Matrix (Fin p.W) (Fin p.W) ℂ

def blockGUEReconstruction (p : BlockBand.Parameters) (z : p.BlockGUECoordinate → ℝ) :
    p.BlockGUEMatrix := fun a b =>
  if a = b then (z (.inl a) : ℂ)
  else if a.val < b.val then
    (z (.inr (a, b, false)) : ℂ) + Complex.I * (z (.inr (a, b, true)) : ℂ)
  else (z (.inr (b, a, false)) : ℂ) - Complex.I * (z (.inr (b, a, true)) : ℂ)

theorem measurable_blockGUEReconstruction (p : BlockBand.Parameters) :
    Measurable p.blockGUEReconstruction := by
  apply measurable_pi_iff.mpr
  intro a
  apply measurable_pi_iff.mpr
  intro b
  unfold blockGUEReconstruction
  split_ifs <;> fun_prop

/-- Every normalized GUE reconstruction is Hermitian, without an a.e. exception. -/
theorem blockGUEReconstruction_isHermitian (p : BlockBand.Parameters)
    (z : p.BlockGUECoordinate → ℝ) : (p.blockGUEReconstruction z).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, blockGUEReconstruction]
  by_cases hab : a = b
  · subst b
    simp
  · have hba := Ne.symm hab
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    by_cases hlt : a.val < b.val
    · have hnlt : ¬b.val < a.val := by omega
      simp [hab, hba, hlt, hnlt]
    · have hrev : b.val < a.val := by omega
      simp [hab, hba, hlt, hrev, sub_eq_add_neg]

/-- The normalized complex `GUE_W(1/W)` matrix measure. -/
def blockGUELaw (p : BlockBand.Parameters) : Measure p.BlockGUEMatrix :=
  Measure.map p.blockGUEReconstruction p.blockGUECoordinatesLaw

instance (p : BlockBand.Parameters) : IsProbabilityMeasure p.blockGUELaw := by
  unfold blockGUELaw
  exact (Measure.isProbabilityMeasure_map_iff p.measurable_blockGUEReconstruction.aemeasurable).mpr inferInstance

/-- The normalized GUE law is supported on Hermitian matrices. -/
theorem blockGUELaw_ae_isHermitian (p : BlockBand.Parameters) :
    ∀ᵐ G ∂p.blockGUELaw, G.IsHermitian := by
  unfold blockGUELaw
  rw [ae_map_iff p.measurable_blockGUEReconstruction.aemeasurable]
  · exact Filter.Eventually.of_forall p.blockGUEReconstruction_isHermitian
  · exact (isClosed_eq
      (by fun_prop : Continuous (fun G : p.BlockGUEMatrix => G.conjTranspose)) continuous_id).measurableSet

/-- The normalized family of physical principal diagonal blocks. -/
def normalizedDiagonalBlocks (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    ZMod p.n → p.BlockGUEMatrix := fun k a b => p.normalizedMatrix H (k, a) (k, b)

theorem measurable_normalizedDiagonalBlocks (p : BlockBand.Parameters) :
    Measurable p.normalizedDiagonalBlocks := by
  unfold normalizedDiagonalBlocks normalizedMatrix
  fun_prop

/-- Coordinate normalization and Hermitian reconstruction intertwine pointwise. -/
theorem blockGUEReconstruction_normalizedCoordinates (p : BlockBand.Parameters)
    (H : p.SiteMatrix) (k : ZMod p.n) :
    p.blockGUEReconstruction (p.normalizedBlockCoordinates H k) =
      (p.normalizedMatrix (p.gaussianReconstruction (p.gaussianExtraction H))).submatrix
        (fun a : Fin p.W => (k, a)) (fun a : Fin p.W => (k, a)) := by
  ext a b
  simp only [Matrix.submatrix_apply, normalizedMatrix_apply]
  unfold blockGUEReconstruction normalizedBlockCoordinates blockGUECoordinateInclusion
    gaussianReconstruction
  simp only [Prod.mk.injEq, true_and, p.siteIndex_sameBlock_lt]
  split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_inv] <;> ring

/-- Almost surely, the reconstructed normalized coordinates are the physical blocks. -/
theorem GaussianRingModel.ae_blockGUEReconstruction_normalizedCoordinates
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    (fun H k => p.blockGUEReconstruction (p.normalizedBlockCoordinates H k)) =ᵐ[
      (model.law : Measure p.SiteMatrix)] p.normalizedDiagonalBlocks := by
  filter_upwards [model.isPhysical.1] with H hH
  funext k
  rw [p.blockGUEReconstruction_normalizedCoordinates,
    p.gaussianReconstruction_gaussianExtraction H hH]
  rfl

/-- The joint law of the normalized blocks is the independent GUE product. -/
theorem GaussianRingModel.normalizedDiagonalBlocks_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw p.normalizedDiagonalBlocks (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))
      (model.law : Measure p.SiteMatrix) := by
  have hmap : HasLaw (fun z : ZMod p.n → p.BlockGUECoordinate → ℝ =>
      fun k => p.blockGUEReconstruction (z k)) (Measure.pi (fun _ : ZMod p.n => p.blockGUELaw))
      (Measure.pi (fun _ : ZMod p.n => p.blockGUECoordinatesLaw)) := by
    refine ⟨(show Measurable (fun z : ZMod p.n → p.BlockGUECoordinate → ℝ =>
      fun k => p.blockGUEReconstruction (z k)) from by
      apply measurable_pi_iff.mpr
      intro k
      exact p.measurable_blockGUEReconstruction.comp (measurable_pi_apply k)).aemeasurable, ?_⟩
    exact Measure.pi_map_pi (fun _ => p.measurable_blockGUEReconstruction.aemeasurable)
  exact (hmap.comp model.normalizedBlockCoordinates_hasLaw).congr
    model.ae_blockGUEReconstruction_normalizedCoordinates.symm

/-- Every normalized physical block has the `GUE_W(1/W)` marginal. -/
theorem GaussianRingModel.normalizedDiagonalBlock_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (k : ZMod p.n) :
    HasLaw (fun H => p.normalizedDiagonalBlocks H k) p.blockGUELaw
      (model.law : Measure p.SiteMatrix) :=
  HasLaw.comp ⟨(measurable_pi_apply k).aemeasurable,
    (measurePreserving_eval (fun _ : ZMod p.n => p.blockGUELaw) k).map_eq⟩
      model.normalizedDiagonalBlocks_hasLaw

/-- The normalized diagonal blocks are independent. -/
theorem GaussianRingModel.iIndepFun_normalizedDiagonalBlocks {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    iIndepFun (fun k H => p.normalizedDiagonalBlocks H k) (model.law : Measure p.SiteMatrix) :=
  (iIndepFun_iff_hasLaw_pi_pi (fun k => model.normalizedDiagonalBlock_hasLaw k)).mpr
    model.normalizedDiagonalBlocks_hasLaw

end BlockBand.Parameters
