module

public import BlockBand.Model.Construction.SpectralProfiles

/-!
# Finite-dimensional profile simplex factorization

The torus profile of each rank factors through the finite probability simplex of block weights,
via a continuous embedding of the simplex into the torus mass profiles; this gives measurability
of the profiles.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Model.Construction

open MeasureTheory
open scoped ENNReal

/-- The finite real block-weight probability simplex. -/
abbrev PhysicalMassSimplex (p : Parameters) :=
  {w : ZMod p.n → ℝ // (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1}

/-- The block-zero default point of the simplex. -/
def physicalMassSimplexDefault (p : Parameters) : PhysicalMassSimplex p := by
  classical
  refine ⟨fun k => if k = 0 then 1 else 0, ?_, ?_⟩
  · intro k
    dsimp only
    split_ifs <;> norm_num
  · simp

/-- Finite weighted Dirac measure attached to a simplex point. -/
def physicalSimplexMeasure (p : Parameters) (w : PhysicalMassSimplex p) : Measure Torus :=
  ∑ k : ZMod p.n, ENNReal.ofReal (w.1 k) • Measure.dirac (physicalProfileGrid p k)

/-- Exact mass-one identity of the finite simplex measure. -/
theorem physicalSimplexMeasure_univ (p : Parameters) (w : PhysicalMassSimplex p) :
    physicalSimplexMeasure p w Set.univ = 1 := by
  simp only [physicalSimplexMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => w.2.1 k), w.2.2]
  norm_num

/-- The torus probability profile of a finite simplex point. -/
def physicalSimplexProfile (p : Parameters) (w : PhysicalMassSimplex p) : MassProfile :=
  ⟨physicalSimplexMeasure p w,
    isProbabilityMeasure_iff.mpr (physicalSimplexMeasure_univ p w)⟩

/-- Finite simplex profile integration, preserving exact block weights. -/
theorem physicalSimplexProfile_integral (p : Parameters) (w : PhysicalMassSimplex p)
    (φ : ContinuousMap Torus ℝ) :
    (∫ r, φ r ∂(physicalSimplexProfile p w : Measure Torus)) =
      ∑ k : ZMod p.n, w.1 k * φ (physicalProfileGrid p k) := by
  change (∫ r, φ r ∂physicalSimplexMeasure p w) = _
  unfold physicalSimplexMeasure
  rw [integral_finsetSum_measure (fun k _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (w.2.1 _), smul_eq_mul]

/-- The simplex-to-profile map is continuous in the weak topology. -/
theorem continuous_physicalSimplexProfile (p : Parameters) :
    Continuous (physicalSimplexProfile p) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro φ
  simp_rw [physicalSimplexProfile_integral]
  apply continuous_finsetSum
  intro k _
  exact ((continuous_apply k).comp continuous_subtype_val).mul continuous_const

/-- The physical block weights as a finite simplex point. -/
def physicalMassSimplex (p : Parameters) (H : p.SiteMatrix) (α : Fin p.N) :
    PhysicalMassSimplex p := by
  classical
  exact if h : physicalProfileGood p H then
    ⟨physicalOrderedBlockMass p H α,
      physicalOrderedBlockMass_nonneg p H α, physicalOrderedBlockMass_sum p H h.1 h.2 α⟩
  else physicalMassSimplexDefault p

/-- Each finite-dimensional physical simplex coordinate is measurable. -/
theorem measurable_physicalMassSimplex (p : Parameters) (α : Fin p.N) :
    Measurable (fun H => physicalMassSimplex p H α) := by
  classical
  have hm : Measurable (fun H : p.SiteMatrix => (physicalMassSimplex p H α).val) := by
    apply measurable_pi_iff.mpr
    intro k
    have he : (fun H : p.SiteMatrix => (physicalMassSimplex p H α).val k) =
        (fun H => if physicalProfileGood p H then physicalOrderedBlockMass p H α k
          else (physicalMassSimplexDefault p).val k) := by
      funext H
      by_cases h : physicalProfileGood p H <;> simp [physicalMassSimplex, h]
    rw [he]
    exact (measurable_physicalOrderedBlockMass p α k).piecewise
      (measurableSet_physicalProfileGood p) measurable_const
  exact hm.subtype_mk

/-- On the good locus the finite simplex coordinates are the physical block masses. -/
theorem physicalMassSimplex_val_eq (p : Parameters) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (α : Fin p.N) :
    (physicalMassSimplex p H α).val = physicalOrderedBlockMass p H α := by
  simp [physicalMassSimplex, h]

/-- On the good locus, the probability profile is the continuous simplex embedding. -/
theorem physicalSimplexProfile_physicalMassSimplex (p : Parameters) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (α : Fin p.N) :
    physicalSimplexProfile p (physicalMassSimplex p H α) = physicalOrderedProfile p H α := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [physicalOrderedProfile_eq p H h.1 h.2 α]
  change physicalSimplexMeasure p (physicalMassSimplex p H α) = physicalOrderedProfileMeasure p H α
  simp only [physicalSimplexMeasure, physicalOrderedProfileMeasure, physicalMassSimplex_val_eq p H h α]

end BlockBand.Model.Construction
