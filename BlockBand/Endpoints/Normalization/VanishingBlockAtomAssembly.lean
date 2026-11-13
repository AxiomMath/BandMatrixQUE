module

public import BlockBand.Endpoints.Normalization.VanishingBlockAtomLimit
public import BlockBand.Internal.Contracts.WindowAngular
public import BlockBand.External.NativeInputs
public import BlockBand.Model.Construction.MarkedStateTopologyConsequences

/-!
# The vanishing block-atom bound

We prove `VanishingBlockAtom`, a step of the proof of the physical lead-profile theorem.

**Theorems.** `vanishingBlockAtom_of_psss source hsmall : VanishingBlockAtom` and its wrapper
`vanishingBlockAtom_of inputs hsmall := vanishingBlockAtom_of_psss inputs.psss hsmall`.

The hypotheses are:
* `inputs : BlockBand.External.NativeInputs.{0}`; only its PSSS field `inputs.psss` is used,
  through the consequences of the counting theorem (marked tightness
  `criticalSequence_markedLaws_isTight` and the exponential count bound);
* `hsmall : BlockBand.Internal.Contracts.WindowAngular.SmallCriticalContract` (the small-critical
  theorem); only its `diffuse` field is used.

Proof. Measure: the exact physical law `(R j).model.law`; marks are the canonical
profiles. Let `S_j` be the statistic. (i) `S_j ≤ E_j ∫ g_m dξ` for every `m`, where
`g_m(u,ν) = |w(u)| Q_m(ν)` and `Q_m` is the continuous pair energy (`Σ_k p_k² ≤ Q_m(ν)`).
(ii) Count moments: `E_j (∫ g_m dξ)² ≤ ‖w‖²_∞ · 2 exp(2 L K (e-1))`, uniformly in `j` and `m`.
(iii) If `S_j ↛ 0`, a subsequence has `S_j ≥ ε`; by tightness (Prokhorov on the metrizable
marked space) a further subsequence of marked laws converges to some `P`, which is a
critical marked limit, so (`diffuse`) `P`-a.s. every atom has a nonatomic mark; hence
`E_P ∫ g_m dξ → 0` as `m → ∞`, and by (ii) `limsup_j E_j ∫ g_m dξ ≤ E_P ∫ g_m dξ`, a
contradiction. The full-sequence statement follows with no rate and no identification of `P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology Set TopologicalSpace
open BlockBand.Model.Construction BlockBand.Counting BlockBand.External.PSSS
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal

section FiniteLevel

variable {p : Parameters}

/-- Expectations under the physical marked law are expectations of the canonical configuration. -/
theorem integral_markedLaw_eq (R : FiniteRealization p) (E : ℝ)
    (F : MarkedPointMeasure → ℝ) (hF : Measurable F) :
    (∫ ξ, F ξ ∂((R.markedLaw E : ProbabilityMeasure MarkedPointMeasure) :
        Measure MarkedPointMeasure)) =
      ∫ H, F (physicalOrderedMarkedConfig p E H) ∂(R.model.law : Measure p.SiteMatrix) := by
  rw [finiteRealization_markedLaw_eq_canonical, Parameters.GaussianRingModel.canonicalPhysicalMarkedLaw,
    ProbabilityMeasure.toMeasure_map]
  exact integral_map (measurable_physicalOrderedMarkedConfig p E).aemeasurable
    hF.aestronglyMeasurable

theorem integrable_markedLaw_iff (R : FiniteRealization p) (E : ℝ)
    (F : MarkedPointMeasure → ℝ) (hF : Measurable F) :
    Integrable F ((R.markedLaw E : ProbabilityMeasure MarkedPointMeasure) :
        Measure MarkedPointMeasure) ↔
      Integrable (fun H => F (physicalOrderedMarkedConfig p E H))
        (R.model.law : Measure p.SiteMatrix) := by
  rw [finiteRealization_markedLaw_eq_canonical, Parameters.GaussianRingModel.canonicalPhysicalMarkedLaw,
    ProbabilityMeasure.toMeasure_map]
  exact integrable_map_measure hF.aestronglyMeasurable
    (measurable_physicalOrderedMarkedConfig p E).aemeasurable

/-- Bounded mark tests give bounded configuration functionals (`≤ C N`). -/
theorem abs_markedFunctional_config_le
    (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (C : ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hgC : ∀ x, g x ≤ C) (E : ℝ) (H : p.SiteMatrix) :
    |markedFunctional g (physicalOrderedMarkedConfig p E H)| ≤ p.N * C := by
  rw [markedFunctional_config, abs_of_nonneg (Finset.sum_nonneg fun α _ => hg0 _)]
  calc (∑ α : Fin p.N, g (physicalCanonicalMarkedLocations p E H α))
      ≤ ∑ _α : Fin p.N, C := Finset.sum_le_sum fun α _ => hgC _
    _ = p.N * C := by simp

/-- **Count-moment bound for mark functionals.** If `0 ≤ g ≤ C` and `g = 0` off `|u| ≤ L`,
then `E (∫ g dξ)² ≤ C² · 2 exp(2 L K (e-1))` under the physical marked law at a bulk energy. -/
theorem integral_sq_markedFunctional_le (R : FiniteRealization p) (source : SourceContract.{0})
    (E : ℝ) (hE : -2 < E ∧ E < 2)
    (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) (C L : ℝ) (hL : 0 ≤ L)
    (hg0 : ∀ x, 0 ≤ g x) (hgC : ∀ x, g x ≤ C)
    (hgL : ∀ x : MarkedSpectralSpace, L < |x.1| → g x = 0) :
    Integrable (fun ξ => markedFunctional g ξ ^ 2)
        ((R.markedLaw E : ProbabilityMeasure MarkedPointMeasure) : Measure MarkedPointMeasure) ∧
      (∫ ξ, markedFunctional g ξ ^ 2
          ∂((R.markedLaw E : ProbabilityMeasure MarkedPointMeasure) :
            Measure MarkedPointMeasure)) ≤
        C ^ 2 * (2 * Real.exp (2 * L *
          p.physicalUnfoldedConstant source (Parameters.semicircleDensity E) * (Real.exp 1 - 1))) := by
  have hmeas : Measurable (fun ξ => markedFunctional g ξ ^ 2) :=
    (measurable_markedFunctional g).pow_const 2
  have hint : Integrable (fun H => markedFunctional g (physicalOrderedMarkedConfig p E H) ^ 2)
      (R.model.law : Measure p.SiteMatrix) := by
    apply Integrable.of_bound
      ((hmeas.comp (measurable_physicalOrderedMarkedConfig p E)).aestronglyMeasurable)
      (((p.N : ℝ) * C) ^ 2)
    filter_upwards with H
    have h := abs_markedFunctional_config_le g C hg0 hgC E H
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  refine ⟨(integrable_markedLaw_iff R E _ hmeas).mpr hint, ?_⟩
  rw [integral_markedLaw_eq R E _ hmeas]
  have hcount := integral_localCount_sq_le p R.model source E L hE hL
  have hcount_int : Integrable (fun H => (physicalCanonicalLocalCount p E L H : ℝ) ^ 2)
      (R.model.law : Measure p.SiteMatrix) := by
    apply Integrable.of_bound
      ((((measurable_from_nat.comp (measurable_physicalCanonicalLocalCount p E L)).pow_const 2)
        ).aestronglyMeasurable) ((p.N : ℝ) ^ 2)
    filter_upwards with H
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : physicalCanonicalLocalCount p E L H ≤ p.N := by
      unfold physicalCanonicalLocalCount finiteSpectralCount
      exact (Finset.card_le_univ _).trans (by simp)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by simp only [Function.comp_apply]; exact_mod_cast this) 2
  calc (∫ H, markedFunctional g (physicalOrderedMarkedConfig p E H) ^ 2
        ∂(R.model.law : Measure p.SiteMatrix))
      ≤ ∫ H, C ^ 2 * (physicalCanonicalLocalCount p E L H : ℝ) ^ 2
          ∂(R.model.law : Measure p.SiteMatrix) := by
        apply integral_mono hint (hcount_int.const_mul _)
        intro H
        have h0 : 0 ≤ markedFunctional g (physicalOrderedMarkedConfig p E H) := by
          rw [markedFunctional_config]
          exact Finset.sum_nonneg fun α _ => hg0 _
        have h1 := markedFunctional_config_le_count g C L hgC hgL p E H
        show markedFunctional g (physicalOrderedMarkedConfig p E H) ^ 2 ≤
          C ^ 2 * (physicalCanonicalLocalCount p E L H : ℝ) ^ 2
        rw [← mul_pow]
        exact pow_le_pow_left₀ h0 h1 2
    _ = C ^ 2 * ∫ H, (physicalCanonicalLocalCount p E L H : ℝ) ^ 2
          ∂(R.model.law : Measure p.SiteMatrix) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount (sq_nonneg C)

/-- **Domination by the pair energy:** `blockAtomStatistic ≤ E ∫ g_m dξ` under the exact physical law. -/
theorem blockAtomStatistic_le_integral (R : FiniteRealization p) (E : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (hws : HasCompactSupport w) (C : ℝ) (hC : ∀ u, |w u| ≤ C) (m : ℕ) :
    blockAtomStatistic R E w ≤
      ∫ ξ, markedFunctional (atomMarkTest hw hws m) ξ
        ∂((R.markedLaw E : ProbabilityMeasure MarkedPointMeasure) : Measure MarkedPointMeasure) := by
  rw [integral_markedLaw_eq R E _ (measurable_markedFunctional _)]
  unfold blockAtomStatistic
  apply integral_mono_of_nonneg
  · filter_upwards with H
    exact Finset.sum_nonneg fun α _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  · apply Integrable.of_bound (((measurable_markedFunctional _).comp
      (measurable_physicalOrderedMarkedConfig p E)).aestronglyMeasurable) (p.N * C)
    filter_upwards with H
    rw [Real.norm_eq_abs]
    exact abs_markedFunctional_config_le _ C (atomMarkTest_nonneg hw hws m)
      (fun x => (mul_le_of_le_one_right (abs_nonneg _) (pairEnergy_le_one m _)).trans (hC _))
      E H
  · filter_upwards [R.model.isPhysical.1, R.model.ae_charpoly_separable] with H hH hsep
    exact blockAtomSum_le_markedFunctional hw hws m p E H hH hsep

end FiniteLevel

/-- **Vanishing block atom** (`VanishingBlockAtom`), from the PSSS source statement (through the
consequences of the counting theorem) and `SmallCriticalContract` (`diffuse` field). -/
theorem vanishingBlockAtom_of_psss (source : SourceContract.{0})
    (hsmall : SmallCriticalContract) : VanishingBlockAtom := by
  intro b hb hb' E hE1 hE2 w hwsmooth hws τ hτ s R
  have hw : Continuous w := hwsmooth.continuous
  have hE : -2 < E ∧ E < 2 := ⟨hE1, hE2⟩
  have hE2' : E ^ 2 < 4 := by nlinarith
  have hrho := Parameters.semicircleDensity_pos hE
  -- the weight bound and support radius
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hws
  have hC' : ∀ u, |w u| ≤ C := fun u => by simpa [Real.norm_eq_abs] using hC u
  obtain ⟨r, hr⟩ := hws.isCompact.isBounded.subset_closedBall 0
  set L := max r 0 with hLdef
  have hL : 0 ≤ L := le_max_right _ _
  have hwL : ∀ u : ℝ, L < |u| → w u = 0 := by
    intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hr hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    have : r < |u| := lt_of_le_of_lt (le_max_left r 0) hu
    linarith
  -- count-moment constant, uniform along the sequence (fixed `b`, hence fixed `c`)
  set p := fun j => s.parameters b hb hb' j with hp
  set B := C ^ 2 * (2 * Real.exp (2 * L *
    (p 0).physicalUnfoldedConstant source (Parameters.semicircleDensity E) * (Real.exp 1 - 1)))
  have hK : ∀ j, (p j).physicalUnfoldedConstant source (Parameters.semicircleDensity E) =
      (p 0).physicalUnfoldedConstant source (Parameters.semicircleDensity E) := by
    intro j
    have hc : (p j).c = (p 0).c := rfl
    simp only [Parameters.physicalUnfoldedConstant, hc]
  have hmom : ∀ (g : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ),
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ C) → (∀ x : MarkedSpectralSpace, L < |x.1| → g x = 0) →
      ∀ j, Integrable (fun ξ => markedFunctional g ξ ^ 2)
          (((R j).markedLaw E : ProbabilityMeasure MarkedPointMeasure) :
            Measure MarkedPointMeasure) ∧
        (∫ ξ, markedFunctional g ξ ^ 2 ∂(((R j).markedLaw E :
          ProbabilityMeasure MarkedPointMeasure) : Measure MarkedPointMeasure)) ≤ B := by
    intro g hg0 hgC hgL j
    have h := integral_sq_markedFunctional_le (R j) source E hE g C L hL hg0 hgC hgL
    rw [hK j] at h
    exact h
  have hatom0 := atomMarkTest_nonneg hw hws
  have hatomC : ∀ m x, atomMarkTest hw hws m x ≤ C := fun m x =>
    (mul_le_of_le_one_right (abs_nonneg _) (pairEnergy_le_one m _)).trans (hC' _)
  have hatomL : ∀ m (x : MarkedSpectralSpace), L < |x.1| → atomMarkTest hw hws m x = 0 := by
    intro m x hx
    rw [atomMarkTest_apply, hwL _ hx]
    simp
  have hweight0 : ∀ x, 0 ≤ weightMarkTest hw hws x := fun x => abs_nonneg _
  have hweightC : ∀ x, weightMarkTest hw hws x ≤ C := fun x => hC' _
  have hweightL : ∀ (x : MarkedSpectralSpace), L < |x.1| → weightMarkTest hw hws x = 0 := by
    intro x hx
    rw [weightMarkTest_apply, hwL _ hx]
    simp
  -- the statistic is nonnegative and dominated by the mark functionals
  have hS0 : ∀ j, 0 ≤ blockAtomStatistic (R j) E w := by
    intro j
    exact integral_nonneg fun H => Finset.sum_nonneg fun α _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hSle := fun j m => blockAtomStatistic_le_integral (R j) E hw hws C hC' m
  -- topology of the marked space
  have : T2Space MarkedPointMeasure := markedPointMeasure_t2Space
  have : PseudoMetrizableSpace MarkedPointMeasure := markedPointMeasure_pseudoMetrizableSpace
  have : SecondCountableTopology MarkedPointMeasure := markedPointMeasure_secondCountableTopology
  have htight := criticalSequence_markedLaws_isTight source s b E hb hb' hrho R
  have hcomp : IsCompact (closure (Set.range (fun j => (R j).markedLaw E))) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext ν
    constructor
    · rintro ⟨μ, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(R i).markedLaw E, ⟨i, rfl⟩, rfl⟩
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun j => lt_of_lt_of_le ha (hS0 j), ?_⟩
  intro ε hε
  by_contra hne
  rw [Filter.not_eventually] at hne
  obtain ⟨φ, hφ, hφS⟩ := Filter.extraction_of_frequently_atTop hne
  obtain ⟨P, -, ψ, hψ, hlim⟩ := hcomp.tendsto_subseq
    (x := fun j => (R (φ j)).markedLaw E) (fun j => subset_closure ⟨φ j, rfl⟩)
  have hcrit : IsCriticalMarkedLimit τ b E hb hb' P := ⟨s, R, φ ∘ ψ, hφ.comp hψ, hlim⟩
  have hdiff := hsmall.diffuse b hb hb' E hE2' τ hτ P hcrit
  have hdiff' : ∀ᵐ ξ ∂(P : Measure MarkedPointMeasure), ∀ x : MarkedSpectralSpace,
      ξ.marked.measure {x} ≠ 0 → ∀ r : Torus, (x.2 : Measure Torus) {r} = 0 := by
    filter_upwards [hdiff] with ξ hξ x hx
    exact (hξ x hx).2
  -- integrability of the weight functional at `P`
  have hweight := integrable_and_eventually_integral_le_of_tendsto hlim
    (markedFunctional (weightMarkTest hw hws)) (continuous_markedFunctional _)
    (fun ξ => integral_nonneg hweight0) B
    (fun j => (hmom _ hweight0 hweightC hweightL (φ (ψ j))).1)
    (fun j => (hmom _ hweight0 hweightC hweightL (φ (ψ j))).2)
  -- choose `m` with `E_P ∫ g_m dξ < ε/2`
  have hzero := tendsto_integral_atomFunctional_of_diffuse hw hws P hweight.1 hdiff'
  obtain ⟨m, hm⟩ := (hzero.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).exists
  have hatom := integrable_and_eventually_integral_le_of_tendsto hlim
    (markedFunctional (atomMarkTest hw hws m)) (continuous_markedFunctional _)
    (fun ξ => integral_nonneg (hatom0 m)) B
    (fun j => (hmom _ (hatom0 m) (hatomC m) (hatomL m) (φ (ψ j))).1)
    (fun j => (hmom _ (hatom0 m) (hatomC m) (hatomL m) (φ (ψ j))).2)
  obtain ⟨j, hj⟩ := (hatom.2 (ε / 2) (by linarith)).exists
  have h1 := hSle (φ (ψ j)) m
  have h2 := hφS (ψ j)
  simp only [Function.comp_apply] at hj
  exact h2 (by linarith)

/-- **Vanishing block atom** from the cited inputs `NativeInputs` (only `inputs.psss` is used) and
`SmallCriticalContract`. -/
theorem vanishingBlockAtom_of (inputs : BlockBand.External.NativeInputs.{0})
    (hsmall : SmallCriticalContract) : VanishingBlockAtom :=
  vanishingBlockAtom_of_psss inputs.psss hsmall

end BlockBand.Endpoints.Normalization
