module
public import BlockBand.Counting.PhysicalBlockCoordinates
public import BlockBand.External.PSSS.SourceStatement

/-!
# Physical coordinates indexed by the block-GUE upper ordering

The sites of the Gaussian ring are identified with the block-GUE index `Σ k, Fin W`, and
the upper-triangular block-GUE pairs with real and imaginary Gaussian coordinates of the
physical matrix.  Under the model law, these coordinates, divided by `sqrt c`, are
independent centered real Gaussians with explicit variances.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open BlockBand.External.PSSS
open scoped NNReal

abbrev nativeBlockSizes (p : BlockBand.Parameters) (_ : Fin p.n) : ℕ := p.W
abbrev NativeIndex (p : BlockBand.Parameters) := BlockGUE.Index p.nativeBlockSizes
abbrev NativeUpperPair (p : BlockBand.Parameters) := BlockGUE.UpperPair p.nativeBlockSizes

instance (p : BlockBand.Parameters) : Fintype p.NativeUpperPair := by
  unfold NativeUpperPair BlockGUE.UpperPair
  infer_instance

def nativeSiteEquiv (p : BlockBand.Parameters) : p.NativeIndex ≃ p.Site :=
  (Equiv.sigmaEquivProd (Fin p.n) (Fin p.W)).trans
    (Equiv.prodCongr (ZMod.finEquiv p.n).toEquiv (Equiv.refl (Fin p.W)))

theorem native_indexLE_antisymm (p : BlockBand.Parameters) (x y : p.NativeIndex)
    (hxy : BlockGUE.indexLE p.nativeBlockSizes x y)
    (hyx : BlockGUE.indexLE p.nativeBlockSizes y x) : x = y := by
  apply (Fintype.equivFin p.NativeIndex).injective
  apply Fin.ext
  exact Nat.le_antisymm hxy hyx

def nativeSortedPair (p : BlockBand.Parameters) (q : p.NativeUpperPair) : p.Site × p.Site :=
  if p.siteIndex (p.nativeSiteEquiv q.1.1) ≤ p.siteIndex (p.nativeSiteEquiv q.1.2)
    then (p.nativeSiteEquiv q.1.1, p.nativeSiteEquiv q.1.2)
    else (p.nativeSiteEquiv q.1.2, p.nativeSiteEquiv q.1.1)

theorem nativeSortedPair_eq_cases (p : BlockBand.Parameters) (q r : p.NativeUpperPair)
    (h : p.nativeSortedPair q = p.nativeSortedPair r) :
    (q.1.1 = r.1.1 ∧ q.1.2 = r.1.2) ∨ (q.1.1 = r.1.2 ∧ q.1.2 = r.1.1) := by
  unfold nativeSortedPair at h
  split_ifs at h with hq hr hr
  · exact Or.inl ⟨p.nativeSiteEquiv.injective (congrArg Prod.fst h),
      p.nativeSiteEquiv.injective (congrArg Prod.snd h)⟩
  · exact Or.inr ⟨p.nativeSiteEquiv.injective (congrArg Prod.fst h),
      p.nativeSiteEquiv.injective (congrArg Prod.snd h)⟩
  · exact Or.inr ⟨p.nativeSiteEquiv.injective (congrArg Prod.snd h),
      p.nativeSiteEquiv.injective (congrArg Prod.fst h)⟩
  · exact Or.inl ⟨p.nativeSiteEquiv.injective (congrArg Prod.snd h),
      p.nativeSiteEquiv.injective (congrArg Prod.fst h)⟩

theorem nativeSortedPair_injective (p : BlockBand.Parameters) :
    Function.Injective p.nativeSortedPair := by
  intro q r h
  rcases p.nativeSortedPair_eq_cases q r h with he | he
  · exact Subtype.ext (Prod.ext he.1 he.2)
  · have hxy : q.1.1 = q.1.2 := p.native_indexLE_antisymm _ _ q.2 (by
      simpa only [he.1, he.2] using r.2)
    exact Subtype.ext (Prod.ext (hxy.trans he.2) (hxy.symm.trans he.1))

def nativeGaussianCoordinate (p : BlockBand.Parameters) (qb : p.NativeUpperPair × Bool) :
    p.GaussianCoordinate :=
  if qb.1.1.1 = qb.1.1.2 ∧ qb.2 = false then .inl (p.nativeSiteEquiv qb.1.1.1)
  else .inr ((p.nativeSortedPair qb.1).1, (p.nativeSortedPair qb.1).2, qb.2)

theorem nativeGaussianCoordinate_injective (p : BlockBand.Parameters) :
    Function.Injective p.nativeGaussianCoordinate := by
  rintro ⟨q, b⟩ ⟨r, c⟩ he
  unfold nativeGaussianCoordinate at he
  split_ifs at he with hq hr hr
  · have hx : q.1.1 = r.1.1 := p.nativeSiteEquiv.injective (Sum.inl.inj he)
    have hqr : q = r := Subtype.ext (Prod.ext hx (hq.1.symm.trans (hx.trans hr.1)))
    exact Prod.ext hqr (hq.2.trans hr.2.symm)
  · have hp := Sum.inr.inj he
    have hpair : p.nativeSortedPair q = p.nativeSortedPair r :=
      Prod.ext (congrArg (fun z : p.Site × p.Site × Bool => z.1) hp) (congrArg (fun z : p.Site × p.Site × Bool => z.2.1) hp)
    exact Prod.ext (p.nativeSortedPair_injective hpair) (congrArg (fun z : p.Site × p.Site × Bool => z.2.2) hp)

def nativeNormalizedCoordinates (p : BlockBand.Parameters) (H : p.SiteMatrix)
    (q : p.NativeUpperPair) (b : Bool) : ℝ :=
  (Real.sqrt p.c)⁻¹ * p.gaussianExtraction H (p.nativeGaussianCoordinate (q, b))

theorem measurable_nativeNormalizedCoordinates (p : BlockBand.Parameters) :
    Measurable p.nativeNormalizedCoordinates := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro b
  unfold nativeNormalizedCoordinates
  exact (((measurable_pi_apply _).comp p.measurable_gaussianExtraction).const_mul _)

def nativeCoordinateVariance (p : BlockBand.Parameters) (q : p.NativeUpperPair) (b : Bool) : ℝ≥0 :=
  NNReal.mk ((Real.sqrt p.c)⁻¹ ^ 2) (sq_nonneg _) *
    p.gaussianCoordinateVariance (p.nativeGaussianCoordinate (q, b))

theorem GaussianRingModel.nativeNormalized_coordinate_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (q : p.NativeUpperPair) (b : Bool) :
    HasLaw (fun H => p.nativeNormalizedCoordinates H q b)
      (gaussianReal 0 (p.nativeCoordinateVariance q b)) (model.law : Measure p.SiteMatrix) := by
  simpa only [nativeNormalizedCoordinates, nativeCoordinateVariance, mul_zero] using
    gaussianReal_const_mul (model.gaussianExtraction_coordinate_hasLaw (p.nativeGaussianCoordinate (q,b)))
      (Real.sqrt p.c)⁻¹

theorem GaussianRingModel.nativeNormalized_flat_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw (fun H (qb : p.NativeUpperPair × Bool) => p.nativeNormalizedCoordinates H qb.1 qb.2)
      (Measure.pi (fun qb : p.NativeUpperPair × Bool => gaussianReal 0 (p.nativeCoordinateVariance qb.1 qb.2)))
      (model.law : Measure p.SiteMatrix) := by
  have hi := model.iIndepFun_gaussianExtraction.precomp p.nativeGaussianCoordinate_injective
  have hs := hi.comp (fun _ (x : ℝ) => (Real.sqrt p.c)⁻¹ * x) (fun _ => by fun_prop)
  exact hs.hasLaw_pi (fun qb => model.nativeNormalized_coordinate_hasLaw qb.1 qb.2)

theorem GaussianRingModel.nativeNormalizedCoordinates_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw p.nativeNormalizedCoordinates
      (Measure.pi (fun q : p.NativeUpperPair => Measure.pi (fun b : Bool => gaussianReal 0 (p.nativeCoordinateVariance q b))))
      (model.law : Measure p.SiteMatrix) := by
  have hc : HasLaw (MeasurableEquiv.curry p.NativeUpperPair Bool ℝ)
      (Measure.pi (fun q : p.NativeUpperPair => Measure.pi (fun b : Bool => gaussianReal 0 (p.nativeCoordinateVariance q b))))
      (Measure.pi (fun qb : p.NativeUpperPair × Bool => gaussianReal 0 (p.nativeCoordinateVariance qb.1 qb.2))) := by
    refine ⟨(MeasurableEquiv.curry _ _ _).measurable.aemeasurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      Measure.infinitePi_map_curry (fun q b => gaussianReal 0 (p.nativeCoordinateVariance q b))
  exact hc.comp model.nativeNormalized_flat_hasLaw

end BlockBand.Parameters
