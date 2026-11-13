module
public import BlockBand.Counting.NativePhysicalCoordinates
public import BlockBand.Counting.PhysicalCountTransport
public import BlockBand.Counting.PhysicalBlockReconstruction

/-!
# The block-GUE law of the diagonal blocks of the Gaussian ring

The normalized diagonal blocks of the physical Gaussian ring, reindexed by the block-GUE
index, form a block-GUE law in the PSSS normalization.  Every Gaussian and independence
property is proved from the model law, and the diagonal blocks are independent of the
normalized off-diagonal background.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open BlockBand.External.PSSS
open scoped NNReal

theorem nativeSiteEquiv_apply (p : BlockBand.Parameters) (x : p.NativeIndex) :
    p.nativeSiteEquiv x = ((ZMod.finEquiv p.n) x.1, x.2) := rfl

def nativeDiagonalMatrix (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    Matrix p.NativeIndex p.NativeIndex ℂ := fun x y =>
  if x.1 = y.1 then p.normalizedMatrix (p.gaussianReconstruction (p.gaussianExtraction H))
    (p.nativeSiteEquiv x) (p.nativeSiteEquiv y) else 0

theorem measurable_nativeDiagonalMatrix (p : BlockBand.Parameters) :
    Measurable p.nativeDiagonalMatrix := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold nativeDiagonalMatrix
  split_ifs
  · change Measurable (fun H => (Real.sqrt p.c : ℂ)⁻¹ *
      p.gaussianReconstruction (p.gaussianExtraction H) (p.nativeSiteEquiv x) (p.nativeSiteEquiv y))
    exact ((((measurable_pi_apply (p.nativeSiteEquiv y)).comp
      (measurable_pi_apply (p.nativeSiteEquiv x))).comp p.measurable_gaussianReconstruction).comp
      p.measurable_gaussianExtraction).const_mul _
  · exact measurable_const

theorem nativeDiagonalMatrix_isHermitian (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    (p.nativeDiagonalMatrix H).IsHermitian := by
  have hN := p.normalizedMatrix_hermitian
    (p.gaussianReconstruction_isHermitian (p.gaussianExtraction H))
  ext x y
  simp only [Matrix.conjTranspose_apply, nativeDiagonalMatrix]
  by_cases hxy : x.1 = y.1
  · rw [ite_eq_left hxy, ite_eq_left hxy.symm]
    exact hN.apply (p.nativeSiteEquiv x) (p.nativeSiteEquiv y)
  · simp only [hxy, Ne.symm hxy, ite_false, star_zero]

def nativeUpperEntry (p : BlockBand.Parameters) (q : p.NativeUpperPair) (z : Bool → ℝ) : ℂ :=
  if q.1.1.1 ≠ q.1.2.1 then 0
  else if q.1.1 = q.1.2 then (z false : ℂ)
  else if p.siteIndex (p.nativeSiteEquiv q.1.1) < p.siteIndex (p.nativeSiteEquiv q.1.2)
    then (z false : ℂ) + Complex.I * (z true : ℂ)
    else (z false : ℂ) - Complex.I * (z true : ℂ)

theorem measurable_nativeUpperEntry (p : BlockBand.Parameters) (q : p.NativeUpperPair) :
    Measurable (p.nativeUpperEntry q) := by
  unfold nativeUpperEntry
  split_ifs <;> fun_prop

theorem nativeDiagonalMatrix_upperEntry (p : BlockBand.Parameters) (H : p.SiteMatrix)
    (q : p.NativeUpperPair) :
    p.nativeDiagonalMatrix H q.1.1 q.1.2 =
      p.nativeUpperEntry q (p.nativeNormalizedCoordinates H q) := by
  rcases q with ⟨⟨x,y⟩, hq⟩
  by_cases hb : x.1 = y.1
  · by_cases hd : x = y
    · subst y
      simp [nativeDiagonalMatrix, nativeUpperEntry, nativeNormalizedCoordinates,
        nativeGaussianCoordinate, normalizedMatrix_apply, gaussianReconstruction,
        Complex.ofReal_mul, Complex.ofReal_inv]
    · have he : p.nativeSiteEquiv x ≠ p.nativeSiteEquiv y := fun h => hd (p.nativeSiteEquiv.injective h)
      have hi : p.siteIndex (p.nativeSiteEquiv x) ≠ p.siteIndex (p.nativeSiteEquiv y) :=
        fun h => he (p.siteIndex_injective h)
      by_cases hl : p.siteIndex (p.nativeSiteEquiv x) < p.siteIndex (p.nativeSiteEquiv y)
      · have hle : p.siteIndex (p.nativeSiteEquiv x) ≤ p.siteIndex (p.nativeSiteEquiv y) := hl.le
        simp [nativeDiagonalMatrix, nativeUpperEntry, nativeNormalizedCoordinates,
          nativeGaussianCoordinate, nativeSortedPair, normalizedMatrix_apply,
          gaussianReconstruction, hb, hd, he, hl, hle, Complex.ofReal_mul, Complex.ofReal_inv]
        ring
      · have hle : ¬p.siteIndex (p.nativeSiteEquiv x) ≤ p.siteIndex (p.nativeSiteEquiv y) := by omega
        simp [nativeDiagonalMatrix, nativeUpperEntry, nativeNormalizedCoordinates,
          nativeGaussianCoordinate, nativeSortedPair, normalizedMatrix_apply,
          gaussianReconstruction, hb, hd, he, hl, hle, Complex.ofReal_mul, Complex.ofReal_inv]
        ring
  · simp [nativeDiagonalMatrix, nativeUpperEntry, hb]

theorem GaussianRingModel.nativeNormalized_group_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (q : p.NativeUpperPair) :
    HasLaw (fun H => p.nativeNormalizedCoordinates H q)
      (Measure.pi (fun b : Bool => gaussianReal 0 (p.nativeCoordinateVariance q b)))
      (model.law : Measure p.SiteMatrix) :=
  HasLaw.comp ⟨(measurable_pi_apply q).aemeasurable,
    (measurePreserving_eval (fun q : p.NativeUpperPair =>
      Measure.pi (fun b : Bool => gaussianReal 0 (p.nativeCoordinateVariance q b))) q).map_eq⟩
    model.nativeNormalizedCoordinates_hasLaw

theorem GaussianRingModel.iIndepFun_nativeNormalized_groups {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    iIndepFun (fun q H => p.nativeNormalizedCoordinates H q) (model.law : Measure p.SiteMatrix) :=
  (iIndepFun_iff_hasLaw_pi_pi (fun q => model.nativeNormalized_group_hasLaw q)).mpr
    model.nativeNormalizedCoordinates_hasLaw

theorem GaussianRingModel.iIndepFun_nativeDiagonal_upper {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    iIndepFun (fun q : p.NativeUpperPair => fun H => p.nativeDiagonalMatrix H q.1.1 q.1.2)
      (model.law : Measure p.SiteMatrix) := by
  have h := model.iIndepFun_nativeNormalized_groups.comp (fun q => p.nativeUpperEntry q)
    (fun q => p.measurable_nativeUpperEntry q)
  convert h using 1
  funext q H
  exact p.nativeDiagonalMatrix_upperEntry H q

def nativeDiagonalPair (p : BlockBand.Parameters) (x : p.NativeIndex) : p.NativeUpperPair :=
  ⟨(x,x), by unfold BlockGUE.indexLE; exact le_rfl⟩

theorem nativeCoordinateVariance_diagonal (p : BlockBand.Parameters) (x : p.NativeIndex) :
    p.nativeCoordinateVariance (p.nativeDiagonalPair x) false =
      ⟨BlockGUE.entryVariance p.nativeBlockSizes x x,
        BlockGUE.entryVariance_nonneg (fun _ => p.W_pos) x x⟩ := by
  rcases x with ⟨k,a⟩
  have h := p.blockGUECoordinateVariance_scaling ((ZMod.finEquiv p.n) k) (.inl a)
  simpa [nativeCoordinateVariance, nativeGaussianCoordinate, nativeDiagonalPair,
    nativeSiteEquiv_apply, blockGUECoordinateInclusion, blockGUECoordinateVariance,
    BlockGUE.entryVariance, nativeBlockSizes] using h

theorem nativeCoordinateVariance_offdiag (p : BlockBand.Parameters) (q : p.NativeUpperPair)
    (hb : q.1.1.1 = q.1.2.1) (hd : q.1.1 ≠ q.1.2) (r : Bool) :
    p.nativeCoordinateVariance q r =
      ⟨BlockGUE.entryVariance p.nativeBlockSizes q.1.1 q.1.2 / 2,
        div_nonneg (BlockGUE.entryVariance_nonneg (fun _ => p.W_pos) _ _) (by norm_num)⟩ := by
  rcases q with ⟨⟨⟨k,a⟩,⟨l,b⟩⟩,hq⟩
  change k = l at hb
  subst l
  have hab : a ≠ b := by intro h; subst b; exact hd rfl
  have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
  by_cases hlt : a.val < b.val
  · have h := p.blockGUECoordinateVariance_scaling ((ZMod.finEquiv p.n) k) (.inr (a,b,r))
    simpa [nativeCoordinateVariance, nativeGaussianCoordinate, nativeSortedPair,
      nativeSiteEquiv_apply, siteIndex, blockGUECoordinateInclusion,
      blockGUECoordinateVariance, BlockGUE.entryVariance, nativeBlockSizes, hd, hlt, hlt.le, div_eq_mul_inv] using h
  · have hrev : b.val < a.val := by omega
    have hnotle : ¬a.val ≤ b.val := by omega
    have h := p.blockGUECoordinateVariance_scaling ((ZMod.finEquiv p.n) k) (.inr (b,a,r))
    simpa [nativeCoordinateVariance, nativeGaussianCoordinate, nativeSortedPair,
      nativeSiteEquiv_apply, siteIndex, blockGUECoordinateInclusion,
      blockGUECoordinateVariance, BlockGUE.entryVariance, nativeBlockSizes, hd, hrev, hnotle, div_eq_mul_inv] using h

theorem GaussianRingModel.nativeNormalized_components_independent {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (q : p.NativeUpperPair) :
    IndepFun (fun H => p.nativeNormalizedCoordinates H q false)
      (fun H => p.nativeNormalizedCoordinates H q true) (model.law : Measure p.SiteMatrix) := by
  have hne : p.nativeGaussianCoordinate (q,false) ≠ p.nativeGaussianCoordinate (q,true) := by
    intro h
    have he := congrArg Prod.snd (p.nativeGaussianCoordinate_injective h)
    cases he
  have hi := model.iIndepFun_gaussianExtraction.indepFun hne
  exact hi.comp (by fun_prop) (by fun_prop)

theorem nativeUpperEntry_re (p : BlockBand.Parameters) (q : p.NativeUpperPair)
    (hb : q.1.1.1 = q.1.2.1) (z : Bool → ℝ) :
    (p.nativeUpperEntry q z).re = z false := by
  unfold nativeUpperEntry
  simp only [hb, ne_eq, not_true_eq_false, ite_false]
  split_ifs <;> simp

def nativeImagSign (p : BlockBand.Parameters) (q : p.NativeUpperPair) : ℝ :=
  if p.siteIndex (p.nativeSiteEquiv q.1.1) < p.siteIndex (p.nativeSiteEquiv q.1.2) then 1 else -1

theorem nativeUpperEntry_im (p : BlockBand.Parameters) (q : p.NativeUpperPair)
    (hb : q.1.1.1 = q.1.2.1) (hd : q.1.1 ≠ q.1.2) (z : Bool → ℝ) :
    (p.nativeUpperEntry q z).im = p.nativeImagSign q * z true := by
  unfold nativeUpperEntry nativeImagSign
  simp only [hb, ne_eq, not_true_eq_false, hd, ite_false]
  split_ifs <;> simp

theorem GaussianRingModel.nativeDiagonal_re_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (x : p.NativeIndex) :
    HasLaw (fun H => (p.nativeDiagonalMatrix H x x).re)
      (gaussianReal 0 ⟨BlockGUE.entryVariance p.nativeBlockSizes x x,
        BlockGUE.entryVariance_nonneg (fun _ => p.W_pos) x x⟩) (model.law : Measure p.SiteMatrix) := by
  have h := model.nativeNormalized_coordinate_hasLaw (p.nativeDiagonalPair x) false
  rw [p.nativeCoordinateVariance_diagonal x] at h
  apply h.congr
  filter_upwards with H
  rw [show p.nativeDiagonalMatrix H x x =
    p.nativeUpperEntry (p.nativeDiagonalPair x) (p.nativeNormalizedCoordinates H (p.nativeDiagonalPair x)) from
    p.nativeDiagonalMatrix_upperEntry H (p.nativeDiagonalPair x)]
  exact p.nativeUpperEntry_re _ rfl _

theorem GaussianRingModel.nativeOffdiag_re_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (q : p.NativeUpperPair)
    (hb : q.1.1.1 = q.1.2.1) (hd : q.1.1 ≠ q.1.2) :
    HasLaw (fun H => (p.nativeDiagonalMatrix H q.1.1 q.1.2).re)
      (gaussianReal 0 ⟨BlockGUE.entryVariance p.nativeBlockSizes q.1.1 q.1.2 / 2,
        div_nonneg (BlockGUE.entryVariance_nonneg (fun _ => p.W_pos) _ _) (by norm_num)⟩)
      (model.law : Measure p.SiteMatrix) := by
  have h := model.nativeNormalized_coordinate_hasLaw q false
  rw [p.nativeCoordinateVariance_offdiag q hb hd false] at h
  apply h.congr
  filter_upwards with H
  rw [p.nativeDiagonalMatrix_upperEntry H q]
  exact p.nativeUpperEntry_re q hb _

theorem GaussianRingModel.nativeOffdiag_im_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (q : p.NativeUpperPair)
    (hb : q.1.1.1 = q.1.2.1) (hd : q.1.1 ≠ q.1.2) :
    HasLaw (fun H => (p.nativeDiagonalMatrix H q.1.1 q.1.2).im)
      (gaussianReal 0 ⟨BlockGUE.entryVariance p.nativeBlockSizes q.1.1 q.1.2 / 2,
        div_nonneg (BlockGUE.entryVariance_nonneg (fun _ => p.W_pos) _ _) (by norm_num)⟩)
      (model.law : Measure p.SiteMatrix) := by
  have hbase := model.nativeNormalized_coordinate_hasLaw q true
  have h := gaussianReal_const_mul hbase (p.nativeImagSign q)
  have hs : NNReal.mk ((p.nativeImagSign q) ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.coe_injective
    change (p.nativeImagSign q) ^ 2 = 1
    unfold nativeImagSign
    split_ifs <;> norm_num
  rw [mul_zero, hs, one_mul, p.nativeCoordinateVariance_offdiag q hb hd true] at h
  apply h.congr
  filter_upwards with H
  rw [p.nativeDiagonalMatrix_upperEntry H q]
  exact p.nativeUpperEntry_im q hb hd _

theorem GaussianRingModel.nativeOffdiag_components_independent {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (q : p.NativeUpperPair)
    (hb : q.1.1.1 = q.1.2.1) (hd : q.1.1 ≠ q.1.2) :
    IndepFun (fun H => (p.nativeDiagonalMatrix H q.1.1 q.1.2).re)
      (fun H => (p.nativeDiagonalMatrix H q.1.1 q.1.2).im) (model.law : Measure p.SiteMatrix) := by
  have h : IndepFun (fun H => p.nativeNormalizedCoordinates H q false)
      (fun H => p.nativeImagSign q * p.nativeNormalizedCoordinates H q true)
      (model.law : Measure p.SiteMatrix) :=
    (model.nativeNormalized_components_independent q).comp measurable_id (by fun_prop)
  apply h.congr
  · filter_upwards with H
    rw [p.nativeDiagonalMatrix_upperEntry H q]
    exact (p.nativeUpperEntry_re q hb _).symm
  · filter_upwards with H
    rw [p.nativeDiagonalMatrix_upperEntry H q]
    exact (p.nativeUpperEntry_im q hb hd _).symm

theorem nativeDiagonalMatrix_diagonal_im_zero (p : BlockBand.Parameters)
    (H : p.SiteMatrix) (x : p.NativeIndex) : (p.nativeDiagonalMatrix H x x).im = 0 := by
  change RCLike.im (p.nativeDiagonalMatrix H x x) = 0
  have he := (p.nativeDiagonalMatrix_isHermitian H).coe_re_apply_self x
  have hi := congrArg (RCLike.im : ℂ → ℝ) he
  simpa only [RCLike.ofReal_im] using hi.symm

/-- The block-GUE law of the normalized diagonal blocks, constructed from the physical
model law; every Gaussian and independence field is proved above. -/
def GaussianRingModel.nativeBlockGUELaw {p : BlockBand.Parameters} (model : p.GaussianRingModel) :
    BlockGUE.Law p.nativeBlockSizes (fun _ => p.W_pos) where
  Ω := p.SiteMatrix
  mΩ := inferInstance
  P := (model.law : Measure p.SiteMatrix)
  probability := inferInstance
  G := p.nativeDiagonalMatrix
  hermitian := p.nativeDiagonalMatrix_isHermitian
  measurable_entry := by
    intro x y
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp p.measurable_nativeDiagonalMatrix)
  block_diagonal := by
    intro x y hxy
    filter_upwards with H
    simp only [nativeDiagonalMatrix, hxy, ite_false]
  upper_independent := model.iIndepFun_nativeDiagonal_upper
  diagonal_im_zero := fun x => Filter.Eventually.of_forall (fun H => p.nativeDiagonalMatrix_diagonal_im_zero H x)
  diagonal_re_law := model.nativeDiagonal_re_hasLaw
  offdiag_components_independent := fun x y hxy hne hb =>
    model.nativeOffdiag_components_independent ⟨(x,y),hxy⟩ hb hne
  offdiag_re_law := fun x y hxy hne hb =>
    model.nativeOffdiag_re_hasLaw ⟨(x,y),hxy⟩ hb hne
  offdiag_im_law := fun x y hxy hne hb =>
    model.nativeOffdiag_im_hasLaw ⟨(x,y),hxy⟩ hb hne

theorem GaussianRingModel.nativeBlockGUELaw_probability {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) : IsProbabilityMeasure model.nativeBlockGUELaw.P :=
  model.nativeBlockGUELaw.probability

theorem GaussianRingModel.nativeDiagonalMatrix_ae_actual {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    p.nativeDiagonalMatrix =ᵐ[(model.law : Measure p.SiteMatrix)]
      (fun H x y => if x.1 = y.1 then p.normalizedMatrix H
        (p.nativeSiteEquiv x) (p.nativeSiteEquiv y) else 0) := by
  filter_upwards [model.isPhysical.1] with H hH
  funext x y
  simp only [nativeDiagonalMatrix, p.gaussianReconstruction_gaussianExtraction H hH]

def nativeReindex (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    Matrix p.NativeIndex p.NativeIndex ℂ := H.submatrix p.nativeSiteEquiv p.nativeSiteEquiv

theorem measurable_nativeReindex (p : BlockBand.Parameters) : Measurable p.nativeReindex := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (measurable_pi_apply (p.nativeSiteEquiv y)).comp (measurable_pi_apply (p.nativeSiteEquiv x))

theorem nativeReindex_isHermitian (p : BlockBand.Parameters) {H : p.SiteMatrix}
    (hH : H.IsHermitian) : (p.nativeReindex H).IsHermitian := hH.submatrix _

def nativeBlocksMatrix (p : BlockBand.Parameters) (G : ZMod p.n → p.BlockGUEMatrix) :
    Matrix p.NativeIndex p.NativeIndex ℂ := p.nativeReindex (p.blockDiagonalMatrix G)

theorem measurable_nativeBlocksMatrix (p : BlockBand.Parameters) : Measurable p.nativeBlocksMatrix := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  unfold nativeBlocksMatrix nativeReindex
  change Measurable (fun G : ZMod p.n → p.BlockGUEMatrix => if (p.nativeSiteEquiv x).1 = (p.nativeSiteEquiv y).1
    then G (p.nativeSiteEquiv x).1 (p.nativeSiteEquiv x).2 (p.nativeSiteEquiv y).2 else 0)
  split_ifs <;> fun_prop

theorem nativeSiteEquiv_block_eq (p : BlockBand.Parameters) (x y : p.NativeIndex) :
    (p.nativeSiteEquiv x).1 = (p.nativeSiteEquiv y).1 ↔ x.1 = y.1 := by
  rw [p.nativeSiteEquiv_apply x, p.nativeSiteEquiv_apply y]
  exact (ZMod.finEquiv p.n).injective.eq_iff

theorem GaussianRingModel.nativeDiagonalMatrix_ae_nativeBlocks {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    p.nativeDiagonalMatrix =ᵐ[(model.law : Measure p.SiteMatrix)]
      (fun H => p.nativeBlocksMatrix (p.normalizedDiagonalBlocks H)) := by
  filter_upwards [model.nativeDiagonalMatrix_ae_actual] with H hH
  rw [hH]
  funext x y
  simp only [nativeBlocksMatrix, nativeReindex, Matrix.submatrix_apply,
    blockDiagonalMatrix, normalizedDiagonalBlocks, p.nativeSiteEquiv_block_eq]
  split_ifs with hxy
  · have hey : ((p.nativeSiteEquiv x).1, (p.nativeSiteEquiv y).2) = p.nativeSiteEquiv y :=
      Prod.ext ((p.nativeSiteEquiv_block_eq x y).mpr hxy) rfl
    rw [hey]
  · rfl

theorem GaussianRingModel.nativeDiagonalMatrix_background_independent {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    IndepFun p.nativeDiagonalMatrix p.normalizedOffDiagonalBackground (model.law : Measure p.SiteMatrix) := by
  have h : IndepFun (fun H => p.nativeBlocksMatrix (p.normalizedDiagonalBlocks H))
      p.normalizedOffDiagonalBackground (model.law : Measure p.SiteMatrix) :=
    model.diagonalBlocks_background_independent.comp p.measurable_nativeBlocksMatrix measurable_id
  exact h.congr model.nativeDiagonalMatrix_ae_nativeBlocks.symm (Filter.Eventually.of_forall (fun _ => rfl))

end BlockBand.Parameters
