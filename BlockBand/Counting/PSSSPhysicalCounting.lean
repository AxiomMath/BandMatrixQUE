module
public import BlockBand.Counting.NativePhysicalLaw
public import BlockBand.Counting.NativeCountTransport
public import BlockBand.Model.Construction.SpectralEigenvalues

/-!
# PSSS factorial moments for the physical Gaussian ring

Conditionally on the off-diagonal background, the normalized diagonal blocks of the
physical Gaussian ring form a block-GUE law, so the external PSSS estimate applies with a
deterministic deformation.  Transporting the counts through this identity in law and
integrating out the background with Fubini gives the factorial-moment bound for the
interval counts of `H + A`, with constant `C / sqrt c`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open BlockBand.External.PSSS BlockBand.Counting

def physicalHermitianVersion (p : BlockBand.Parameters) (H : p.SiteMatrix) :
    HermitianMatrix p.Site :=
  ⟨p.gaussianReconstruction (p.gaussianExtraction H), p.gaussianReconstruction_isHermitian _⟩

theorem measurable_physicalHermitianVersion (p : BlockBand.Parameters) :
    Measurable p.physicalHermitianVersion :=
  Measurable.subtype_mk (p.measurable_gaussianReconstruction.comp p.measurable_gaussianExtraction)

def nativeBackgroundDeformation (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (B : p.SiteMatrix) : HermitianMatrix p.NativeIndex :=
  ⟨p.nativeReindex ((p.physicalHermitianVersion B).1 + p.normalizedMatrix A.1),
    p.nativeReindex_isHermitian ((p.physicalHermitianVersion B).2.add
      (p.normalizedMatrix_hermitian A.2))⟩

theorem measurable_nativeBackgroundDeformation (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) : Measurable (p.nativeBackgroundDeformation A) := by
  apply Measurable.subtype_mk
  apply p.measurable_nativeReindex.comp
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
    (measurable_subtype_coe.comp p.measurable_physicalHermitianVersion)).add measurable_const

def GaussianRingModel.nativeFreshCount {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (a b : ℝ)
    (z : p.SiteMatrix × p.SiteMatrix) : ℕ :=
  BlockGUE.intervalCount model.nativeBlockGUELaw (p.nativeBackgroundDeformation A z.1)
    (Set.Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c)) z.2

theorem GaussianRingModel.measurable_nativeFreshCount {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (a b : ℝ) :
    Measurable (model.nativeFreshCount A a b) := by
  apply (measurable_nativeEigenCount _ measurableSet_Icc).comp
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact ((((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
    (measurable_subtype_coe.comp (p.measurable_nativeBackgroundDeformation A))).comp
    measurable_fst).add ((((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
    p.measurable_nativeDiagonalMatrix).comp measurable_snd)

theorem GaussianRingModel.nativeFreshCount_integrable {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (a b : ℝ) (r : ℕ) :
    Integrable (factorialCount (model.nativeFreshCount A a b) r)
      (model.normalizedBackgroundLaw.prod (model.law : Measure p.SiteMatrix)) :=
  integrable_factorialCount _ (model.measurable_nativeFreshCount A a b)
    (fun _ => BlockGUE.intervalCount_le_dimension _ _ _ _) r

/-- The PSSS estimate applied at fixed background, then Fubini. Finite-dimensional integrability is proved
separately, at every order; conditioning costs no constant. -/
theorem GaussianRingModel.nativeFreshCount_factorialBound {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    FactorialMomentBound
      (model.normalizedBackgroundLaw.prod (model.law : Measure p.SiteMatrix))
      (model.nativeFreshCount A a b) (Fintype.card p.NativeIndex) (b - a)
      (source.C / Real.sqrt p.c) r := by
  have hs : 0 < Real.sqrt p.c := Real.sqrt_pos.mpr p.c_pos
  have hbound : ∀ B : p.SiteMatrix,
      (∫ H, factorialCount (model.nativeFreshCount A a b) r (B,H)
        ∂(model.law : Measure p.SiteMatrix)) ≤
      (source.C * (Fintype.card p.NativeIndex : ℝ) *
        (b / Real.sqrt p.c - a / Real.sqrt p.c)) ^ r := by
    intro B
    exact source.factorialBound (fun _ => p.W_pos) model.nativeBlockGUELaw
      (p.nativeBackgroundDeformation A B) _ _ (div_le_div_of_nonneg_right hab hs.le) r hr
  unfold FactorialMomentBound
  rw [integral_prod _ (model.nativeFreshCount_integrable A a b r)]
  have hle := integral_mono
    (model.nativeFreshCount_integrable A a b r).integral_prod_left
    (integrable_const ((source.C * (Fintype.card p.NativeIndex : ℝ) *
      (b / Real.sqrt p.c - a / Real.sqrt p.c)) ^ r)) hbound
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hle
  convert hle using 1
  congr 1
  ring

/-- Globally measurable, bounded physical count; on every Hermitian `H` this is
exactly the multiplicity count of `H + A`, with no simple-spectrum restriction. -/
def physicalIntervalCount (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (a b : ℝ) (H : p.SiteMatrix) : ℕ :=
  eigenCount ⟨(p.physicalHermitianVersion H).1 + A.1,
    (p.physicalHermitianVersion H).2.add A.2⟩ (Set.Icc a b)

theorem measurable_physicalIntervalCount (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (a b : ℝ) : Measurable (p.physicalIntervalCount A a b) := by
  apply (measurable_nativeEigenCount _ measurableSet_Icc).comp
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
    (measurable_subtype_coe.comp p.measurable_physicalHermitianVersion)).add measurable_const

theorem physicalIntervalCount_eq (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (a b : ℝ) (H : p.SiteMatrix) (hH : H.IsHermitian) :
    p.physicalIntervalCount A a b H = orderedEigenvalueCount (hH.add A.2) (Set.Icc a b) := by
  simp only [physicalIntervalCount, physicalHermitianVersion,
    p.gaussianReconstruction_gaussianExtraction H hH]
  rfl

def nativeNoise (p : BlockBand.Parameters) (H : p.SiteMatrix) : HermitianMatrix p.NativeIndex :=
  ⟨p.nativeDiagonalMatrix H, p.nativeDiagonalMatrix_isHermitian H⟩

theorem measurable_nativeNoise (p : BlockBand.Parameters) : Measurable p.nativeNoise :=
  Measurable.subtype_mk p.measurable_nativeDiagonalMatrix

def nativePairCount (p : BlockBand.Parameters) (A : HermitianMatrix p.Site) (a b : ℝ)
    (z : p.SiteMatrix × HermitianMatrix p.NativeIndex) : ℕ :=
  eigenCount ⟨(p.nativeBackgroundDeformation A z.1).1 + z.2.1,
    (p.nativeBackgroundDeformation A z.1).2.add z.2.2⟩
    (Set.Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c))

theorem measurable_nativePairCount (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (a b : ℝ) : Measurable (p.nativePairCount A a b) := by
  apply (measurable_nativeEigenCount _ measurableSet_Icc).comp
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  have hev : Measurable (fun M : Matrix p.NativeIndex p.NativeIndex ℂ => M x y) :=
    (measurable_pi_apply y).comp (measurable_pi_apply x)
  exact ((hev.comp (measurable_subtype_coe.comp (p.measurable_nativeBackgroundDeformation A))).comp
    measurable_fst).add ((hev.comp
      (measurable_subtype_coe : Measurable (Subtype.val : HermitianMatrix p.NativeIndex →
        Matrix p.NativeIndex p.NativeIndex ℂ))).comp measurable_snd)

theorem GaussianRingModel.background_nativeNoise_hasLaw {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    HasLaw (fun H => (p.normalizedOffDiagonalBackground H, p.nativeNoise H))
      (model.normalizedBackgroundLaw.prod
        (Measure.map p.nativeNoise (model.law : Measure p.SiteMatrix)))
      (model.law : Measure p.SiteMatrix) := by
  let retract : Matrix p.NativeIndex p.NativeIndex ℂ → HermitianMatrix p.NativeIndex :=
    BlockBand.Model.Construction.rawHermitianExtension id ⟨0, Matrix.isHermitian_zero⟩
  have hm : Measurable retract :=
    BlockBand.Model.Construction.measurable_rawHermitianExtension id measurable_id _
  have hi : IndepFun p.normalizedOffDiagonalBackground p.nativeNoise
      (model.law : Measure p.SiteMatrix) := by
    have h := model.nativeDiagonalMatrix_background_independent.symm.comp measurable_id hm
    apply h.congr (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards with H
    exact BlockBand.Model.Construction.rawHermitianExtension_eq id _ _
      (p.nativeDiagonalMatrix_isHermitian H)
  exact hi.hasLaw_prod
    ⟨p.measurable_normalizedOffDiagonalBackground.aemeasurable, rfl⟩
    ⟨p.measurable_nativeNoise.aemeasurable, rfl⟩

theorem GaussianRingModel.nativePair_identDistrib {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) :
    IdentDistrib (fun H => (p.normalizedOffDiagonalBackground H, p.nativeNoise H))
      (fun z : p.SiteMatrix × p.SiteMatrix => (z.1, p.nativeNoise z.2))
      (model.law : Measure p.SiteMatrix)
      (model.normalizedBackgroundLaw.prod (model.law : Measure p.SiteMatrix)) := by
  have hm : Measurable (fun z : p.SiteMatrix × p.SiteMatrix => (z.1, p.nativeNoise z.2)) :=
    measurable_fst.prodMk (p.measurable_nativeNoise.comp measurable_snd)
  refine ⟨model.background_nativeNoise_hasLaw.aemeasurable, hm.aemeasurable, ?_⟩
  rw [model.background_nativeNoise_hasLaw.map_eq]
  change model.normalizedBackgroundLaw.prod (Measure.map p.nativeNoise (model.law : Measure p.SiteMatrix)) =
    Measure.map (Prod.map id p.nativeNoise) _
  simpa only [Measure.map_id] using
    Measure.map_prod_map model.normalizedBackgroundLaw (model.law : Measure p.SiteMatrix)
      measurable_id p.measurable_nativeNoise

/-- Deterministic reconstruction of the count on every Hermitian raw input. -/
theorem nativePairCount_actual (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (a b : ℝ) (H : p.SiteMatrix) (hH : H.IsHermitian) :
    p.nativePairCount A a b (p.normalizedOffDiagonalBackground H, p.nativeNoise H) =
      p.physicalIntervalCount A a b H := by
  have hR := p.gaussianReconstruction_gaussianExtraction H hH
  have hB := p.gaussianReconstruction_gaussianExtraction (p.normalizedOffDiagonalBackground H)
    (p.normalizedOffDiagonalBackground_isHermitian H hH)
  let T : HermitianMatrix p.Site :=
    ⟨p.normalizedMatrix (H + A.1), p.normalizedMatrix_hermitian (hH.add A.2)⟩
  have hM : (⟨(p.nativeBackgroundDeformation A (p.normalizedOffDiagonalBackground H)).1 +
      (p.nativeNoise H).1,
      (p.nativeBackgroundDeformation A (p.normalizedOffDiagonalBackground H)).2.add
        (p.nativeNoise H).2⟩ : HermitianMatrix p.NativeIndex) =
      hermitianReindex p.nativeSiteEquiv.symm T := by
    apply Subtype.ext
    ext x y
    change p.nativeReindex
      (p.gaussianReconstruction (p.gaussianExtraction (p.normalizedOffDiagonalBackground H)) +
        p.normalizedMatrix A.1) x y + p.nativeDiagonalMatrix H x y =
      p.normalizedMatrix (H + A.1) (p.nativeSiteEquiv x) (p.nativeSiteEquiv y)
    rw [hB]
    by_cases hxy : x.1 = y.1
    · have he := (p.nativeSiteEquiv_block_eq x y).mpr hxy
      simp [nativeReindex, nativeDiagonalMatrix, hR, hxy, he,
        normalizedOffDiagonalBackground, normalizedMatrix_apply, mul_add, add_comm]
    · have he : (p.nativeSiteEquiv x).1 ≠ (p.nativeSiteEquiv y).1 :=
        fun h => hxy ((p.nativeSiteEquiv_block_eq x y).mp h)
      simp [nativeReindex, nativeDiagonalMatrix, hxy, he,
        normalizedOffDiagonalBackground, normalizedMatrix_apply, mul_add]
  unfold nativePairCount
  rw [hM, nativeEigenCount_hermitianReindex]
  rw [nativeEigenCount_eq_orderedEigenvalueCount]
  exact (p.orderedEigenvalueCount_normalizedMatrix (hH.add A.2) a b).trans
    (p.physicalIntervalCount_eq A a b H hH).symm

theorem GaussianRingModel.physicalIntervalCount_identDistrib {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (a b : ℝ) :
    IdentDistrib (p.physicalIntervalCount A a b) (model.nativeFreshCount A a b)
      (model.law : Measure p.SiteMatrix)
      (model.normalizedBackgroundLaw.prod (model.law : Measure p.SiteMatrix)) := by
  have h := model.nativePair_identDistrib.comp (p.measurable_nativePairCount A a b)
  have hae : (p.nativePairCount A a b ∘
      (fun H => (p.normalizedOffDiagonalBackground H, p.nativeNoise H))) =ᵐ[
        (model.law : Measure p.SiteMatrix)] p.physicalIntervalCount A a b := by
    filter_upwards [model.isPhysical.1] with H hH
    exact p.nativePairCount_actual A a b H hH
  refine ⟨(p.measurable_physicalIntervalCount A a b).aemeasurable,
    (model.measurable_nativeFreshCount A a b).aemeasurable, ?_⟩
  calc
    Measure.map (p.physicalIntervalCount A a b) (model.law : Measure p.SiteMatrix) =
        Measure.map (p.nativePairCount A a b ∘
          (fun H => (p.normalizedOffDiagonalBackground H, p.nativeNoise H)))
          (model.law : Measure p.SiteMatrix) := (Measure.map_congr hae).symm
    _ = _ := h.map_eq

theorem GaussianRingModel.physicalIntervalCount_integrable {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (a b : ℝ) (r : ℕ) :
    Integrable (factorialCount (p.physicalIntervalCount A a b) r)
      (model.law : Measure p.SiteMatrix) :=
  integrable_factorialCount _ (p.measurable_physicalIntervalCount A a b)
    (fun _ => eigenCount_le_dimension _ _) r

/-- Physical factorial bound under the model law, with the exact `C / sqrt c` scaling.
The PSSS theorem is an explicit hypothesis; the law and count transport is proved.
Uniform in the parameters, the deformation `A`, the endpoints and the orders. -/
theorem GaussianRingModel.physicalIntervalCount_factorialBound {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    FactorialMomentBound (model.law : Measure p.SiteMatrix)
      (p.physicalIntervalCount A a b) p.N (b - a) (source.C / Real.sqrt p.c) r := by
  have h := factorialMomentBound_transport (model.physicalIntervalCount_identDistrib A a b)
    (model.nativeFreshCount_factorialBound source A a b hab r hr)
  simpa only [NativeIndex, nativeBlockSizes, BlockGUE.Index, Fintype.card_sigma,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, N] using h

end BlockBand.Parameters
