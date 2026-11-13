module
public import BlockBand.Model.Construction.MarkedRotation
public import BlockBand.QUE.Fourier.CyclicTransport

/-!
# Cyclic shifts rotate the mass profiles

The profile grid `k ↦ k/n` is the additive embedding `ZMod n → ℝ/ℤ`; a cyclic shift of the sites
preserves the good locus and rotates every mass profile of a fixed rank by minus its grid angle
(`physicalOrderedProfile_cyclic`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open Matrix MeasureTheory BlockBand.Model.Construction
open BlockBand.QUE.Fourier

/-- The profile grid `k ↦ k/n` is the additive embedding `ZMod n → ℝ/ℤ`. -/
theorem physicalProfileGrid_eq_toAddCircle (p : Parameters) (k : ZMod p.n) :
    physicalProfileGrid p k = ZMod.toAddCircle k := by
  exact (ZMod.toAddCircle_apply k).symm

theorem physicalProfileGrid_add (p : Parameters) (k s : ZMod p.n) :
    physicalProfileGrid p (k+s) = physicalProfileGrid p k + physicalProfileGrid p s := by
  simp only [physicalProfileGrid_eq_toAddCircle, map_add]

theorem physicalProfileGrid_neg (p : Parameters) (k : ZMod p.n) :
    physicalProfileGrid p (-k) = -physicalProfileGrid p k := by
  simp only [physicalProfileGrid_eq_toAddCircle, map_neg]

theorem physicalProfileGrid_zero (p : Parameters) : physicalProfileGrid p 0 = 0 := by
  simp only [physicalProfileGrid_eq_toAddCircle, map_zero]

/-- Reindexing preserves the Hermitian and separable good locus. -/
theorem physicalProfileGood_cyclic (p : Parameters) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (s : ZMod p.n) :
    physicalProfileGood p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) := by
  rw [← sitePermutation_conjugation]
  refine ⟨Matrix.isHermitian_mul_mul_conjTranspose _ h.1, ?_⟩
  have hc := BlockBand.QUE.Haar.charpoly_unitaryConjugate
    (sitePermutationUnitary p (p.cyclicSiteEquiv s)) ⟨H,h.1⟩
  change ((sitePermutationUnitary p (p.cyclicSiteEquiv s) : p.SiteMatrix) * H *
    (sitePermutationUnitary p (p.cyclicSiteEquiv s) : p.SiteMatrix)ᴴ).charpoly.Separable
  change ((sitePermutationUnitary p (p.cyclicSiteEquiv s) : p.SiteMatrix) * H *
    (sitePermutationUnitary p (p.cyclicSiteEquiv s) : p.SiteMatrix)ᴴ).charpoly = H.charpoly at hc
  rw [hc]
  exact h.2

/-- On the good locus, a positive cyclic shift rotates every probability profile of a fixed rank
by minus its grid angle. -/
theorem physicalOrderedProfile_cyclic (p : Parameters) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (α : Fin p.N) (s : ZMod p.n) :
    physicalOrderedProfile p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) α =
      massProfileRotation (-physicalProfileGrid p s) (physicalOrderedProfile p H α) := by
  have hg := physicalProfileGood_cyclic p H h s
  apply ProbabilityMeasure.toMeasure_injective
  change (physicalOrderedProfile p (p.siteReindexMatrix (p.cyclicSiteEquiv s) H) α : Measure Torus) =
    Measure.map (Homeomorph.addLeft (-physicalProfileGrid p s))
      (physicalOrderedProfile p H α : Measure Torus)
  rw [physicalOrderedProfile_eq p _ hg.1 hg.2 α, physicalOrderedProfile_eq p H h.1 h.2 α]
  unfold physicalOrderedProfileMeasure
  rw [Measure.map_finset_sum' (Homeomorph.addLeft _).continuous.measurable.aemeasurable]
  simp_rw [Measure.map_smul _ (Homeomorph.addLeft _).continuous.measurable.aemeasurable,
    Measure.map_dirac' (Homeomorph.addLeft _).continuous.measurable]
  apply Fintype.sum_equiv (Equiv.addRight s)
  intro k
  rw [physical_blockMass_cyclic p H h.1 h.2 α s k]
  congr 2
  change physicalProfileGrid p k = -physicalProfileGrid p s + physicalProfileGrid p (k+s)
  rw [physicalProfileGrid_add]
  abel
end BlockBand.QUE.Invariance
