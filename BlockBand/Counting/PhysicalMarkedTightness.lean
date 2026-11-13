module
public import BlockBand.Counting.PhysicalMarkedTightnessTails
public import BlockBand.Counting.PhysicalSpectralIntensity
public import BlockBand.Model.Construction.PhysicalCanonicalLaw
public import BlockBand.Model.Construction.PhysicalSpectralStationarity

/-!
# Tightness of the physical marked spectral laws

The laws of the unfolded marked spectral configurations of the physical Gaussian ring at a
fixed bulk energy form a tight family in the vague topology, for any family of parameters
with a common diagonal weight `c`, in particular along every critical sequence.  The
local counts are controlled by the unfolded first-moment bound.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set
open BlockBand.Model.Construction BlockBand.External.PSSS
open scoped Topology ENNReal NNReal

def physicalCanonicalMarkedLocations (p : Parameters) (E : ℝ) (H : p.SiteMatrix) :
    Fin p.N → MarkedSpectralSpace := physicalSpectralDataLocations p E (physicalSpectralData p H)

def physicalCanonicalLocalCount (p : Parameters) (E R : ℝ) : p.SiteMatrix → ℕ :=
  finiteSpectralCount (fun H α => (physicalCanonicalMarkedLocations p E H α).1) (Icc (-R) R)

theorem measurable_physicalCanonicalLocalCount (p : Parameters) (E R : ℝ) :
    Measurable (physicalCanonicalLocalCount p E R) := by
  apply measurable_finiteSpectralCount _ _ _ measurableSet_Icc
  intro α
  exact ((measurable_physicalOrderedEigenvalue p α).sub_const E).const_mul _

theorem physicalCanonicalLocalCount_eq_physical_ae (p : Parameters)
    (model : p.GaussianRingModel) (E R : ℝ) :
    physicalCanonicalLocalCount p E R =ᵐ[(model.law : Measure p.SiteMatrix)]
      p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
        (Parameters.semicircleDensity E) (-R) R := by
  classical
  filter_upwards [model.isPhysical.1] with H hH
  have he (α : Fin p.N) : (physicalCanonicalMarkedLocations p E H α).1 =
      p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E
        (Parameters.semicircleDensity E) H (physicalSpectralRank p α) := by
    dsimp [physicalCanonicalMarkedLocations, physicalSpectralDataLocations, physicalSpectralData]
    unfold physicalOrderedEigenvalue
    rw [rawIncreasingEigenvalue_eq _ H hH,
      p.physicalUnfoldedEigenvalue_eq ⟨0, Matrix.isHermitian_zero⟩ E
        (Parameters.semicircleDensity E) H hH]
    simp
  have hc1 : physicalCanonicalLocalCount p E R H =
      ∑ α : Fin p.N, if (physicalCanonicalMarkedLocations p E H α).1 ∈ Icc (-R) R then 1 else 0 := by
    simp [physicalCanonicalLocalCount, finiteSpectralCount, Finset.sum_boole]
  have hc2 : p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
      (Parameters.semicircleDensity E) (-R) R H =
      ∑ α : Fin (Fintype.card p.Site), if p.physicalUnfoldedEigenvalue
        ⟨0, Matrix.isHermitian_zero⟩ E (Parameters.semicircleDensity E) H α ∈ Icc (-R) R then 1 else 0 := by
    simp [Parameters.physicalUnfoldedIntervalCount, eigenvalueCount, Finset.sum_boole]
  rw [hc1, hc2]
  simp_rw [he]
  let e : Fin p.N ≃ Fin (Fintype.card p.Site) :=
    { toFun := physicalSpectralRank p
      invFun := Fin.cast (physicalSite_card p)
      left_inv := by intro i; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  exact Equiv.sum_comp e (fun i => if p.physicalUnfoldedEigenvalue
    ⟨0, Matrix.isHermitian_zero⟩ E (Parameters.semicircleDensity E) H i ∈ Icc (-R) R then 1 else 0)

theorem physicalCanonicalLocalCount_firstMoment_le (p : Parameters)
    (model : p.GaussianRingModel) (source : SourceContract.{0}) (E R : ℝ)
    (hrho : 0 < Parameters.semicircleDensity E) (_hR : 0 ≤ R) :
    (∫⁻ H, (physicalCanonicalLocalCount p E R H : ℝ≥0∞) ∂(model.law : Measure p.SiteMatrix)) ≤
      ENNReal.ofReal (p.physicalUnfoldedConstant source (Parameters.semicircleDensity E) * (2*R)) := by
  have he := physicalCanonicalLocalCount_eq_physical_ae p model E R
  rw [lintegral_congr_ae (he.mono fun H h => congrArg (fun n : ℕ => (n : ℝ≥0∞)) h)]
  have h := model.physicalSpectralIntensity_le_volume source ⟨0, Matrix.isHermitian_zero⟩
    E (Parameters.semicircleDensity E) hrho
  have hA := h (Icc (-R) R)
  rw [Parameters.GaussianRingModel.physicalSpectralIntensity,
    finiteSpectralIntensity_apply _ _
      (p.measurable_physicalUnfoldedEigenvalue _ _ _) _ measurableSet_Icc] at hA
  convert hA using 1 <;>
    simp [finiteSpectralCount, Parameters.physicalUnfoldedIntervalCount, eigenvalueCount,
      Measure.smul_apply, Real.volume_Icc, Parameters.physicalUnfoldedConstant,
      sub_neg_eq_add, two_mul]
  exact ENNReal.ofReal_mul (p.physicalUnfoldedConstant_pos source hrho).le

/-- Every shell label is controlled by the count on its visible symmetric interval. -/
theorem physicalCanonicalMarkedLocations_shell_control (p : Parameters) (E : ℝ)
    (H : p.SiteMatrix) (j : ℕ) :
    (finiteMarkedShellLabels (physicalCanonicalMarkedLocations p E H) j).card ≤
      physicalCanonicalLocalCount p E (j+1) H := by
  classical
  unfold physicalCanonicalLocalCount finiteSpectralCount
  apply Finset.card_le_card
  intro α hα
  have hj := (mem_finiteMarkedShellLabels _ j α).mp hα
  have hz := markedAtom_mem_assignedShell (physicalCanonicalMarkedLocations p E H α)
  rw [hj] at hz
  have ha := abs_le.mp hz.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Icc]
  exact ha

/-- Tightness of the canonical marked laws of a family of Gaussian ring models,
with one common positive diagonal weight `c` and fixed bulk energy `E`. -/
theorem physicalCanonicalMarkedLaws_isTight (source : SourceContract.{0})
    (p : ℕ → Parameters) (models : ∀ i, (p i).GaussianRingModel)
    (hc : ∀ i, (p i).c = (p 0).c) (E : ℝ)
    (hrho : 0 < Parameters.semicircleDensity E) :
    IsTightMeasureSet (Set.range (fun i =>
      (models i |>.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure))) := by
  let μ := fun i => (models i).law.toMeasure
  let locations := fun i => physicalCanonicalMarkedLocations (p i) E
  let sample := fun i => physicalOrderedMarkedConfig (p i) E
  let count := fun i (j : ℕ) => physicalCanonicalLocalCount (p i) E (j+1)
  let L := fun j : ℕ => ENNReal.ofReal
    ((p 0).physicalUnfoldedConstant source (Parameters.semicircleDensity E) * (2*(j+1)))
  change IsTightMeasureSet (Set.range (fun i => Measure.map (sample i) (μ i)))
  apply finiteMarkedFamily_isTight μ (fun i => (p i).N) locations sample
    (fun i => measurable_physicalOrderedMarkedConfig (p i) E)
    (fun i H => rfl) count (fun i j => measurable_physicalCanonicalLocalCount (p i) E (j+1))
    (fun i H j => physicalCanonicalMarkedLocations_shell_control (p i) E H j) L
    (fun _ => ENNReal.ofReal_ne_top)
  intro i j
  have h := physicalCanonicalLocalCount_firstMoment_le (p i) (models i) source E (j+1)
    hrho (by positivity)
  simpa only [L, Parameters.physicalUnfoldedConstant, hc i] using h

/-- The marked laws of any family of finite realizations are tight in the vague
topology; the dimensions are arbitrary and share the fixed diagonal weight `c`. -/
theorem finiteRealization_markedLaws_isTight (source : SourceContract.{0})
    (p : ℕ → Parameters) (R : ∀ i, FiniteRealization (p i))
    (hc : ∀ i, (p i).c = (p 0).c) (E : ℝ)
    (hrho : 0 < Parameters.semicircleDensity E) :
    IsTightMeasureSet (Set.range (fun i => (R i |>.markedLaw E : Measure MarkedPointMeasure))) := by
  simpa only [finiteRealization_markedLaw_eq_canonical] using
    physicalCanonicalMarkedLaws_isTight source p (fun i => (R i).model) hc E hrho

/-- Marked tightness of the counting theorem at fixed `b`, `E` along every critical
sequence, for every family of physical realizations.  No hypothesis on
limits, atom reconstruction, gluing or Polish completeness is assumed. -/
theorem criticalSequence_markedLaws_isTight (source : SourceContract.{0}) {τ : ℝ}
    (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1/2)
    (hrho : 0 < Parameters.semicircleDensity E)
    (R : ∀ i, FiniteRealization (s.parameters b hb hb' i)) :
    IsTightMeasureSet (Set.range (fun i => (R i |>.markedLaw E : Measure MarkedPointMeasure))) := by
  apply finiteRealization_markedLaws_isTight source (s.parameters b hb hb') R _ E hrho
  intro i
  rfl

/-- Tightness for the canonical constructed physical laws along a critical sequence. -/
theorem criticalPhysicalMarkedLaws_isTight (source : SourceContract.{0}) {τ : ℝ}
    (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1/2)
    (hrho : 0 < Parameters.semicircleDensity E) :
    IsTightMeasureSet (Set.range (fun i =>
      (criticalPhysicalMarkedLaws s b E hb hb' i : Measure MarkedPointMeasure))) :=
  criticalSequence_markedLaws_isTight source s b E hb hb' hrho
    (fun i => constructFiniteRealization (s.parameters b hb hb' i))

end BlockBand.Counting
