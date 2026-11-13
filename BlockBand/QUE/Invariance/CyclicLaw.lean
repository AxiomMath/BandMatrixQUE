module

public import BlockBand.QUE.Invariance.CyclicCoordinates

/-!
# Cyclic invariance of the physical Gaussian matrix law

Site permutations preserving the entry variance profile preserve every physical Gaussian law; in
particular cyclic block translations do (`GaussianRingModel.map_cyclicMatrix`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory

/-- A matrix read at the permuted sites. -/
def siteReindexMatrix (p : BlockBand.Parameters) (e : p.Site ≃ p.Site)
    (H : p.SiteMatrix) : p.SiteMatrix := fun x y => H (e x) (e y)

theorem measurable_siteReindexMatrix (p : BlockBand.Parameters) (e : p.Site ≃ p.Site) :
    Measurable (p.siteReindexMatrix e) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (measurable_pi_apply (e y)).comp (measurable_pi_apply (e x))

/-- Variance-preserving site permutations preserve every physical law. -/
theorem GaussianRingModel.map_siteReindexMatrix
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (e : p.Site ≃ p.Site)
    (hvar : ∀ x y, p.entryVariance (e x) (e y) = p.entryVariance x y)
    (hsym : ∀ x y, p.entryVariance y x = p.entryVariance x y) :
    Measure.map (p.siteReindexMatrix e) (model.law : Measure p.SiteMatrix) =
      (model.law : Measure p.SiteMatrix) := by
  rw [model.law_eq_gaussianMatrixLaw]
  change Measure.map (p.siteReindexMatrix e)
      (Measure.map p.gaussianReconstruction (p.gaussianCoordinatesLaw : Measure _)) =
    Measure.map p.gaussianReconstruction (p.gaussianCoordinatesLaw : Measure _)
  let T := p.signedGaussianPermutation (p.orientedGaussianEquiv e) (p.orientedGaussianNegate e)
  have hT : Measurable T := p.measurable_signedGaussianPermutation _ _
  have hTlaw := p.hasLaw_signedGaussianPermutation (p.orientedGaussianEquiv e)
    (p.orientedGaussianNegate e) (p.gaussianCoordinateVariance_orientedGaussianEquiv e hvar hsym)
  have heq : p.siteReindexMatrix e ∘ p.gaussianReconstruction = p.gaussianReconstruction ∘ T := by
    funext z
    exact (p.gaussianReconstruction_oriented e z).symm
  rw [Measure.map_map (p.measurable_siteReindexMatrix e) p.measurable_gaussianReconstruction,
    heq, ← Measure.map_map p.measurable_gaussianReconstruction hT, hTlaw.map_eq]

/-- The variance profile is symmetric, including the sparse zero entries. -/
theorem entryVariance_symm (p : BlockBand.Parameters) (x y : p.Site) :
    p.entryVariance y x = p.entryVariance x y := by
  have hnear : (x.1 = y.1 + 1 ∨ x.1 = y.1 - 1) ↔
      (y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) := by
    constructor
    · rintro (h | h)
      · right; rw [h]; abel
      · left; rw [h]; abel
    · rintro (h | h)
      · right; rw [h]; abel
      · left; rw [h]; abel
  simp only [entryVariance, hnear]
  simp only [eq_comm]

/-- Cyclic block translation; internal block coordinates stay fixed. -/
def cyclicSiteEquiv (p : BlockBand.Parameters) (s : ZMod p.n) : p.Site ≃ p.Site where
  toFun x := (x.1 + s, x.2)
  invFun x := (x.1 - s, x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

/-- Cyclic shifts preserve the full physical entry variance profile. -/
theorem entryVariance_cyclicSiteEquiv (p : BlockBand.Parameters) (s : ZMod p.n)
    (x y : p.Site) :
    p.entryVariance (p.cyclicSiteEquiv s x) (p.cyclicSiteEquiv s y) =
      p.entryVariance x y := by
  have hplus : y.1 + s = (x.1 + s) + 1 ↔ y.1 = x.1 + 1 := by
    rw [show (x.1 + s) + 1 = (x.1 + 1) + s by abel, add_left_inj]
  have hminus : y.1 + s = (x.1 + s) - 1 ↔ y.1 = x.1 - 1 := by
    rw [show (x.1 + s) - 1 = (x.1 - 1) + s by abel, add_left_inj]
  simp [entryVariance, cyclicSiteEquiv, hplus, hminus]

/-- Cyclic invariance of every physical Gaussian matrix law. -/
theorem GaussianRingModel.map_cyclicMatrix
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (s : ZMod p.n) :
    Measure.map (p.siteReindexMatrix (p.cyclicSiteEquiv s))
      (model.law : Measure p.SiteMatrix) = (model.law : Measure p.SiteMatrix) :=
  model.map_siteReindexMatrix (p.cyclicSiteEquiv s)
    (p.entryVariance_cyclicSiteEquiv s) p.entryVariance_symm

end BlockBand.Parameters
