module

public import BlockBand.Internal.Contracts.RingSymmetry
public import BlockBand.Model.Construction.SpectralMarkedData
public import BlockBand.Model.Construction.SpectralMarkSingleton
public import BlockBand.Model.Construction.GaussianTranslationPhysical
public import BlockBand.QUE.Invariance.PhysicalRotationGrid

/-!
# The finite-`W` block-atom functional as a marked test functional

The block-atom functional `Σ_α |w(u_α)| Σ_k p_{αk}²` of the physical ordered marked configuration
is bounded by the marked atom test `∫ |w(u)| G(ν) dξ(u, ν)` for every mark functional `G`
dominating `Σ_k q_k²` on grid profiles, pointwise on the good locus and in expectation under the
physical law and the canonical physical marked law.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.PointProcess.BlockAtom

open MeasureTheory
open BlockBand.Model.Construction BlockBand.Internal.Contracts
open scoped ENNReal

/-- The marked atom test `∫ |w(u)| G(ν) dξ(u, ν)` over the marked measure of a marked
configuration `ξ` (Bochner integral). No assumption on `w` or `G`. -/
def markedAtomTest (w : ℝ → ℝ) (G : MassProfile → ℝ) (ξ : MarkedPointMeasure) : ℝ :=
  ∫ x, |w x.1| * G x.2 ∂ξ.marked.measure

/-- On a finite atomic marked configuration (`finiteAtomicMarkedPointMeasure`, counting
pushforward, multiplicities retained) the marked atom test is the finite sum over the indexed
atoms. -/
theorem markedAtomTest_finiteAtomic {d : ℕ} (w : ℝ → ℝ) (G : MassProfile → ℝ)
    (loc : Fin d → MarkedSpectralSpace) :
    markedAtomTest w G (finiteAtomicMarkedPointMeasure loc) =
      ∑ i, |w (loc i).1| * G (loc i).2 := by
  have : MeasurableSingletonClass MassProfile := massProfile_measurableSingletonClass
  unfold markedAtomTest
  rw [finiteAtomicMarkedPointMeasure_marked, finiteAtomicMeasure_eq_sum_dirac,
    integral_finsetSum_measure (fun _ _ => integrable_dirac enorm_lt_top)]
  simp only [integral_dirac]

/-- On the good locus (`H` Hermitian with separable characteristic polynomial) the selected mass
profile of rank `α` is the finite atomic measure `Σ_k p_{α k} δ_{k/n}` on the unit torus, with the
block masses `physicalOrderedBlockMass`. -/
theorem physicalOrderedProfile_eq_sum (p : Parameters) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) (α : Fin p.N) :
    (physicalOrderedProfile p H α : Measure Torus) =
      ∑ k : ZMod p.n, ENNReal.ofReal (physicalOrderedBlockMass p H α k) •
        Measure.dirac (physicalProfileGrid p k) :=
  physicalOrderedProfile_eq p H h.1 h.2 α

/-- The mass grid `k ↦ k/n ∈ ℝ/ℤ` is injective on `ZMod n`, so the grid atoms are distinct. -/
theorem physicalProfileGrid_injective (p : Parameters) :
    Function.Injective (physicalProfileGrid p) := by
  intro a b hab
  rw [QUE.Invariance.physicalProfileGrid_eq_toAddCircle,
    QUE.Invariance.physicalProfileGrid_eq_toAddCircle] at hab
  exact ZMod.toAddCircle_injective p.n hab

/-- On every matrix the marked atom test of the physical ordered marked configuration is the
finite sum over its `N` indexed atoms `physicalSpectralDataLocations`. -/
theorem markedAtomTest_physicalOrderedMarkedConfig (p : Parameters) (E : ℝ) (w : ℝ → ℝ)
    (G : MassProfile → ℝ) (H : p.SiteMatrix) :
    markedAtomTest w G (physicalOrderedMarkedConfig p E H) =
      ∑ α, |w (physicalSpectralDataLocations p E (physicalSpectralData p H) α).1| *
        G (physicalSpectralDataLocations p E (physicalSpectralData p H) α).2 :=
  markedAtomTest_finiteAtomic w G _

/-- On the good locus the marked atom test of the physical ordered marked configuration is
`Σ_α |w(u_α)| G(ν_α)`, `u_α = Nρ(E)(λ_α - E)` (`Clocks.microCoord`), `ν_α` the mass profile. -/
theorem markedAtomTest_physicalOrderedMarkedConfig_of_good (p : Parameters) (E : ℝ)
    (w : ℝ → ℝ) (G : MassProfile → ℝ) (H : p.SiteMatrix) (h : physicalProfileGood p H) :
    markedAtomTest w G (physicalOrderedMarkedConfig p E H) =
      ∑ α, |w (Clocks.microCoord p E (physicalOrderedEigenvalue p H α))| *
        G (physicalOrderedProfile p H α) := by
  rw [markedAtomTest_physicalOrderedMarkedConfig]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [physicalSpectralDataLocations_eq p E H h α]
  rfl

/-- **Pointwise comparison.** For every mark functional `G` with `Σ_k q_k² ≤ G(ν)` whenever
`ν = Σ_k q_k δ_{k/n}` with `q ≥ 0`: on the good locus,
`Σ_α |w(u_α)| Σ_k p_{α k}² ≤ ∫ |w(u)| G(ν) dξ` for `ξ = physicalOrderedMarkedConfig p E H`. -/
theorem blockAtomFunctional_le_markedAtomTest (p : Parameters) (E : ℝ) (w : ℝ → ℝ)
    (G : MassProfile → ℝ)
    (hG : ∀ (ν : MassProfile) (q : ZMod p.n → ℝ), (∀ k, 0 ≤ q k) →
      (ν : Measure Torus) = ∑ k, ENNReal.ofReal (q k) • Measure.dirac (physicalProfileGrid p k) →
      ∑ k, q k ^ 2 ≤ G ν)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) :
    RingSymmetry.blockAtomFunctional p E w H ≤
      markedAtomTest w G (physicalOrderedMarkedConfig p E H) := by
  rw [markedAtomTest_physicalOrderedMarkedConfig_of_good p E w G H h]
  unfold RingSymmetry.blockAtomFunctional
  refine Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact hG _ _ (physicalOrderedBlockMass_nonneg p H α) (physicalOrderedProfile_eq_sum p H h α)

/-- The block-atom functional is nonnegative on every matrix. -/
theorem blockAtomFunctional_nonneg (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (H : p.SiteMatrix) :
    0 ≤ RingSymmetry.blockAtomFunctional p E w H :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Under every exact physical law the composed marked atom test
`H ↦ ∫ |w(u)| G(ν) d(physicalOrderedMarkedConfig p E H)` is integrable, for continuous compactly
supported `w` and measurable `0 ≤ G ≤ 1`. It is a.s. equal to the bounded measurable
`Σ_α |w(u_α)| G(ν_α)`, bounded by `N sup|w|`. -/
theorem integrable_markedAtomTest_physicalOrderedMarkedConfig (p : Parameters)
    (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (G : MassProfile → ℝ) (hGm : Measurable G)
    (hG0 : ∀ ν, 0 ≤ G ν) (hG1 : ∀ ν, G ν ≤ 1) :
    Integrable (fun H => markedAtomTest w G (physicalOrderedMarkedConfig p E H))
      (model.law : Measure p.SiteMatrix) := by
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hwc
  let F : p.SiteMatrix → ℝ := fun H =>
    ∑ α, |w (Clocks.microCoord p E (physicalOrderedEigenvalue p H α))| *
      G (physicalOrderedProfile p H α)
  have hFm : Measurable F := by
    refine Finset.measurable_sum _ fun α _ => ?_
    exact (continuous_abs.measurable.comp (hw.measurable.comp
      (((measurable_physicalOrderedEigenvalue p α).sub_const E).const_mul _))).mul
      (hGm.comp (measurable_physicalOrderedProfile p α))
  have hFb : ∀ H, ‖F H‖ ≤ (p.N : ℝ) * C := by
    intro H
    calc ‖F H‖ ≤ ∑ α : Fin p.N, ‖|w (Clocks.microCoord p E (physicalOrderedEigenvalue p H α))| *
          G (physicalOrderedProfile p H α)‖ := norm_sum_le _ _
      _ ≤ ∑ _α : Fin p.N, C := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [norm_mul, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs, abs_of_nonneg (hG0 _)]
          calc |w _| * G _ ≤ |w _| * 1 := mul_le_mul_of_nonneg_left (hG1 _) (abs_nonneg _)
            _ = ‖w _‖ := by rw [mul_one, Real.norm_eq_abs]
            _ ≤ C := hC _
      _ = (p.N : ℝ) * C := by simp
  have hFi : Integrable F (model.law : Measure p.SiteMatrix) :=
    Integrable.of_bound hFm.aestronglyMeasurable ((p.N : ℝ) * C) (Filter.Eventually.of_forall hFb)
  refine hFi.congr ?_
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact (markedAtomTest_physicalOrderedMarkedConfig_of_good p E w G H ⟨hH, hsep⟩).symm

/-- **Integrated comparison, composed form.** For continuous compactly supported `w` and
measurable `0 ≤ G ≤ 1` dominating `Σ_k q_k²` on grid profiles:
`E Σ_α |w(u_α)| Σ_k p_{α k}² ≤ E ∫ |w(u)| G(ν) d(physicalOrderedMarkedConfig p E H)`, both
expectations under `model.law`. -/
theorem integral_blockAtomFunctional_le_comp (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) (G : MassProfile → ℝ)
    (hGm : Measurable G) (hG0 : ∀ ν, 0 ≤ G ν) (hG1 : ∀ ν, G ν ≤ 1)
    (hG : ∀ (ν : MassProfile) (q : ZMod p.n → ℝ), (∀ k, 0 ≤ q k) →
      (ν : Measure Torus) = ∑ k, ENNReal.ofReal (q k) • Measure.dirac (physicalProfileGrid p k) →
      ∑ k, q k ^ 2 ≤ G ν) :
    ∫ H, RingSymmetry.blockAtomFunctional p E w H ∂(model.law : Measure p.SiteMatrix) ≤
      ∫ H, markedAtomTest w G (physicalOrderedMarkedConfig p E H)
        ∂(model.law : Measure p.SiteMatrix) := by
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall
    (blockAtomFunctional_nonneg p E w))
    (integrable_markedAtomTest_physicalOrderedMarkedConfig p model E w hw hwc G hGm hG0 hG1) ?_
  filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H hH hsep
  exact blockAtomFunctional_le_markedAtomTest p E w G hG H ⟨hH, hsep⟩

/-- Change of variables to the canonical physical marked law
`model.canonicalPhysicalMarkedLaw E = model.law ∘ (physicalOrderedMarkedConfig p E)⁻¹`, for any `w`,
`G` whose marked atom test is a.e. strongly measurable for that law. -/
theorem integral_markedAtomTest_canonicalPhysicalMarkedLaw (p : Parameters)
    (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ) (G : MassProfile → ℝ)
    (hT : AEStronglyMeasurable (markedAtomTest w G)
      (model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure)) :
    ∫ ξ, markedAtomTest w G ξ
        ∂(model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure) =
      ∫ H, markedAtomTest w G (physicalOrderedMarkedConfig p E H)
        ∂(model.law : Measure p.SiteMatrix) := by
  have hlaw : (model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure) =
      Measure.map (physicalOrderedMarkedConfig p E) (model.law : Measure p.SiteMatrix) := rfl
  rw [hlaw] at hT ⊢
  exact integral_map (measurable_physicalOrderedMarkedConfig p E).aemeasurable hT

/-- **Integrated comparison under the canonical physical marked law.** As
`integral_blockAtomFunctional_le_comp`, with the right side the expectation of the marked atom
test under `model.canonicalPhysicalMarkedLaw E`; the hypothesis `hT` (a.e. strong measurability
of `markedAtomTest w G` for that law) is needed because the configuration space carries the vague
Borel σ-algebra. -/
theorem integral_blockAtomFunctional_le (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) (G : MassProfile → ℝ)
    (hGm : Measurable G) (hG0 : ∀ ν, 0 ≤ G ν) (hG1 : ∀ ν, G ν ≤ 1)
    (hG : ∀ (ν : MassProfile) (q : ZMod p.n → ℝ), (∀ k, 0 ≤ q k) →
      (ν : Measure Torus) = ∑ k, ENNReal.ofReal (q k) • Measure.dirac (physicalProfileGrid p k) →
      ∑ k, q k ^ 2 ≤ G ν)
    (hT : AEStronglyMeasurable (markedAtomTest w G)
      (model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure)) :
    ∫ H, RingSymmetry.blockAtomFunctional p E w H ∂(model.law : Measure p.SiteMatrix) ≤
      ∫ ξ, markedAtomTest w G ξ
        ∂(model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure) := by
  rw [integral_markedAtomTest_canonicalPhysicalMarkedLaw p model E w G hT]
  exact integral_blockAtomFunctional_le_comp p model E w hw hwc G hGm hG0 hG1 hG

end BlockBand.PointProcess.BlockAtom
