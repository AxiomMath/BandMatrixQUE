module

public import BlockBand.PointProcess.BlockAtom.Kernel
public import BlockBand.PointProcess.BlockAtom.Atomic
public import BlockBand.PointProcess.BlockAtom.Link
public import BlockBand.PointProcess.BlockAtom.Moments
public import BlockBand.PointProcess.BlockAtom.Limit
public import BlockBand.Internal.Contracts.WindowAngular
public import BlockBand.Counting.PhysicalMarkedTightness
public import BlockBand.Model.Construction.MarkedStateTopologyConsequences
public import BlockBand.Model.Construction.PhysicalCanonicalLaw
public import BlockBand.Native.PSSS.SourceContract
public import BlockBand.Model.Construction.MarkedStateTopology

/-!
# Vanishing of the block-atom functional (`VanishingBlockAtom`)

The block-atom functional `E Σ_α |w(u_α)| Σ_k p_{αk}²` vanishes along the critical sequence
(`vanishingBlockAtom_holds`).

Proof: every critical marked subsequential limit has nonatomic marks; compactness and the count
moment bound then give the vanishing along the full sequence.
* the marks enter through the continuous functional `G_M(ν) = ∬ h_M(r - r') dν dν`
  (`Kernel`), which dominates `Σ_k p_k²` on the finite profiles; hence
  `E Σ_α |w(u_α)| Σ_k p_{αk}² ≤ E_{P_j} Ψ_M`, `Ψ_M(ξ) = ∫ |w(u)| G_M(ν) dξ` (`Link`), and `Ψ_M`
  is a vague coordinate of a compactly supported continuous test, so it is continuous;
* the physical marked laws `P_j` are tight (`criticalSequence_markedLaws_isTight`), and
  the marked configuration space is metrizable and second countable, so every subsequence has a
  further subsequence converging to a critical marked limit Q (Prokhorov);
* uniform second moments of the window count (`Moments`) give
  `limsup E_{P_j} Ψ_M ≤ E_Q Ψ_M` (`Limit`);
* Q-almost surely every atom of the limit configuration has a nonatomic mark (`diffuse`), and the
  configuration is carried by its atoms (`Atomic`), so `Ψ_M(ξ) → ∫ |w| Σ(atoms of ν)² dξ = 0`
  and, dominated by `∫ |w| dξ`, `E_Q Ψ_M → 0` as `M → ∞`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.PointProcess.BlockAtom

open MeasureTheory Filter Topology Set
open BlockBand.Model.Construction BlockBand.Internal.Contracts
open scoped ENNReal NNReal

attribute [local instance] markedSpectralSpace_borelSpace massProfile_borelSpace

/-- The marked test `x ↦ |w(x.1)| G(x.2)` as a compactly supported continuous function on
`ℝ × P(𝕋)` (the mark space is compact). -/
def markedTestFunction (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (G : MassProfile → ℝ) (hG : Continuous G) :
    CompactlySupportedContinuousMap MarkedSpectralSpace ℝ where
  toFun x := |w x.1| * G x.2
  continuous_toFun := (continuous_abs.comp (hw.comp continuous_fst)).mul (hG.comp continuous_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (hwc.isCompact.prod isCompact_univ)
    intro x hx
    have h1 : x.1 ∉ tsupport w := fun h => hx ⟨h, Set.mem_univ _⟩
    simp [image_eq_zero_of_notMem_tsupport h1]

/-- `markedAtomTest` is the vague coordinate of `markedTestFunction`. -/
theorem markedAtomTest_eq_coordinate (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (G : MassProfile → ℝ) (hG : Continuous G) (ξ : MarkedPointMeasure) :
    markedAtomTest w G ξ = ξ.marked.coordinate (markedTestFunction w hw hwc G hG) := rfl

/-- `ξ ↦ ∫ |w(u)| G(ν) dξ` is continuous in the vague topology. -/
theorem continuous_markedAtomTest (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (G : MassProfile → ℝ) (hG : Continuous G) : Continuous (markedAtomTest w G) := by
  have h1 : Continuous (fun ξ : MarkedPointMeasure => ξ.marked) := continuous_induced_dom
  have h2 : Continuous (fun η : VaguePointMeasure MarkedSpectralSpace =>
      fun f : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ => η.coordinate f) :=
    continuous_induced_dom
  exact ((continuous_apply (markedTestFunction w hw hwc G hG)).comp h2).comp h1

/-- The marked test is integrable against every locally finite marked point measure. -/
theorem integrable_markedTest (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (G : MassProfile → ℝ) (hG : Continuous G) (ξ : MarkedPointMeasure) :
    Integrable (fun x : MarkedSpectralSpace => |w x.1| * G x.2) ξ.marked.measure :=
  (markedTestFunction w hw hwc G hG).continuous.integrable_of_hasCompactSupport
    (markedTestFunction w hw hwc G hG).hasCompactSupport

theorem markedAtomTest_nonneg (w : ℝ → ℝ) (G : MassProfile → ℝ) (hG0 : ∀ ν, 0 ≤ G ν)
    (ξ : MarkedPointMeasure) : 0 ≤ markedAtomTest w G ξ :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (hG0 _)

/-- Window bound: `Ψ(ξ) ≤ B · ξ([-L, L] × P(𝕋))` when `|w| ≤ B`, `tsupport w ⊆ [-L, L]` and
`0 ≤ G ≤ 1`. -/
theorem ofReal_markedAtomTest_le (w : ℝ → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (G : MassProfile → ℝ) (hG : Continuous G) (hG0 : ∀ ν, 0 ≤ G ν) (hG1 : ∀ ν, G ν ≤ 1)
    {B L : ℝ} (hB : ∀ x, ‖w x‖ ≤ B) (hL : tsupport w ⊆ Icc (-L) L) (ξ : MarkedPointMeasure) :
    ENNReal.ofReal (markedAtomTest w G ξ) ≤ ENNReal.ofReal B * markedWindowCount L ξ := by
  unfold markedAtomTest
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_markedTest w hw hwc G hG ξ)
    (Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (hG0 _))]
  have hwin : MeasurableSet (Icc (-L) L ×ˢ (univ : Set MassProfile)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  calc ∫⁻ x, ENNReal.ofReal (|w x.1| * G x.2) ∂ξ.marked.measure
      ≤ ∫⁻ x, (Icc (-L) L ×ˢ (univ : Set MassProfile)).indicator
          (fun _ => ENNReal.ofReal B) x ∂ξ.marked.measure := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ Icc (-L) L ×ˢ (univ : Set MassProfile)
        · rw [indicator_of_mem hx]
          apply ENNReal.ofReal_le_ofReal
          calc |w x.1| * G x.2 ≤ B * 1 :=
                mul_le_mul (by simpa [Real.norm_eq_abs] using hB x.1) (hG1 _) (hG0 _)
                  ((norm_nonneg _).trans (hB x.1))
            _ = B := mul_one B
        · rw [indicator_of_notMem hx]
          have h1 : x.1 ∉ tsupport w := fun h => hx ⟨hL h, Set.mem_univ _⟩
          simp [image_eq_zero_of_notMem_tsupport h1]
    _ = ENNReal.ofReal B * markedWindowCount L ξ := by
        rw [lintegral_indicator_const hwin]
        rfl

/-- `x ≤ 1 + x²` in `ℝ≥0∞`. -/
theorem le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  by_cases hx : x ≤ 1
  · exact hx.trans le_self_add
  · rw [not_le] at hx
    refine le_add_left ?_
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm

/-- **Vanishing block atom**, from the `diffuse` clause of `SmallCriticalContract` and the window
count moments. -/
theorem vanishingBlockAtom_holds (hS : WindowAngular.SmallCriticalContract) :
    RingSymmetry.VanishingBlockAtom := by
  intro b hb hb' E hE hE' w hw hwc τ hτ s R
  have hE2 : E ^ 2 < 4 := by nlinarith
  have hrho := Parameters.semicircleDensity_pos_of_sq_lt_four E hE2
  obtain ⟨B, hB⟩ := hw.bounded_above_of_compact_support hwc
  obtain ⟨L, hL0, hLsupp⟩ : ∃ L : ℝ, 0 ≤ L ∧ tsupport w ⊆ Icc (-L) L := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hwc.isCompact.isBounded
    refine ⟨max r 0, le_max_right _ _, hr.trans ?_⟩
    rw [Real.closedBall_eq_Icc, zero_sub, zero_add]
    exact Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _)
  obtain ⟨C, hCtop, hC⟩ := lintegral_markedWindowCount_sq_le b hb hb' E hE hE' L hL0
  let p : ℕ → Parameters := s.parameters b hb hb'
  let P : ℕ → ProbabilityMeasure MarkedPointMeasure := fun j => (R j).canonicalPhysicalMarkedLaw E
  let X : ℕ → ℝ := fun j => ∫ H, RingSymmetry.blockAtomFunctional (p j) E w H
    ∂((R j).law : Measure (p j).SiteMatrix)
  show Tendsto X atTop (𝓝 0)
  let Ψ : ℕ → MarkedPointMeasure → ℝ := fun M => markedAtomTest w (markPairKernel M)
  have hΨc : ∀ M, Continuous (Ψ M) := fun M =>
    continuous_markedAtomTest w hw hwc _ (continuous_markPairKernel M)
  have hΨ0 : ∀ M ξ, 0 ≤ Ψ M ξ := fun M ξ =>
    markedAtomTest_nonneg w _ (markPairKernel_nonneg M) ξ
  -- the finite-W comparison
  have hXΨ : ∀ M j, X j ≤ ∫ ξ, Ψ M ξ ∂(P j : Measure MarkedPointMeasure) := by
    intro M j
    exact integral_blockAtomFunctional_le (p j) (R j) E w hw hwc (markPairKernel M)
      (continuous_markPairKernel M).measurable (markPairKernel_nonneg M) (markPairKernel_le_one M)
      (fun ν q hq hν => sum_sq_le_markPairKernel M ν q (physicalProfileGrid (p j)) hq
        (physicalProfileGrid_injective (p j)) hν)
      (hΨc M).aestronglyMeasurable
  have hX0 : ∀ j, 0 ≤ X j := fun j =>
    integral_nonneg fun H => blockAtomFunctional_nonneg (p j) E w H
  -- moment bounds
  have hwinB : ∀ M ξ, ENNReal.ofReal (Ψ M ξ) ≤ ENNReal.ofReal B * markedWindowCount L ξ :=
    fun M ξ => ofReal_markedAtomTest_le w hw hwc _ (continuous_markPairKernel M)
      (markPairKernel_nonneg M) (markPairKernel_le_one M) hB hLsupp ξ
  have h2 : ∀ M j, ∫⁻ ξ, ENNReal.ofReal (Ψ M ξ) ^ 2 ∂(P j : Measure MarkedPointMeasure) ≤
      ENNReal.ofReal B ^ 2 * C := by
    intro M j
    calc ∫⁻ ξ, ENNReal.ofReal (Ψ M ξ) ^ 2 ∂(P j : Measure MarkedPointMeasure)
        ≤ ∫⁻ ξ, ENNReal.ofReal B ^ 2 * markedWindowCount L ξ ^ 2
            ∂(P j : Measure MarkedPointMeasure) := by
          apply lintegral_mono
          intro ξ
          calc ENNReal.ofReal (Ψ M ξ) ^ 2
              ≤ (ENNReal.ofReal B * markedWindowCount L ξ) ^ 2 :=
                pow_le_pow_left₀ zero_le (hwinB M ξ) 2
            _ = ENNReal.ofReal B ^ 2 * markedWindowCount L ξ ^ 2 := mul_pow _ _ _
      _ = ENNReal.ofReal B ^ 2 * ∫⁻ ξ, markedWindowCount L ξ ^ 2
            ∂(P j : Measure MarkedPointMeasure) :=
          lintegral_const_mul _ ((measurable_markedWindowCount L).pow_const 2)
      _ ≤ ENNReal.ofReal B ^ 2 * C := by
          gcongr
          exact hC (p j) rfl (R j)
  -- the dominating functional `D = Ψ` with `G = 1`
  let D : MarkedPointMeasure → ℝ := markedAtomTest w (fun _ => 1)
  have hDc : Continuous D := continuous_markedAtomTest w hw hwc _ continuous_const
  have hD1 : ∀ j, ∫⁻ ξ, ENNReal.ofReal (D ξ) ∂(P j : Measure MarkedPointMeasure) ≤
      ENNReal.ofReal B * (1 + C) := by
    intro j
    calc ∫⁻ ξ, ENNReal.ofReal (D ξ) ∂(P j : Measure MarkedPointMeasure)
        ≤ ∫⁻ ξ, ENNReal.ofReal B * (1 + markedWindowCount L ξ ^ 2)
            ∂(P j : Measure MarkedPointMeasure) := by
          apply lintegral_mono
          intro ξ
          refine (ofReal_markedAtomTest_le w hw hwc _ continuous_const (fun _ => zero_le_one)
            (fun _ => le_rfl) hB hLsupp ξ).trans ?_
          exact mul_le_mul_of_nonneg_left (le_one_add_sq _) zero_le
      _ = ENNReal.ofReal B * (1 + ∫⁻ ξ, markedWindowCount L ξ ^ 2
            ∂(P j : Measure MarkedPointMeasure)) := by
          rw [lintegral_const_mul (ENNReal.ofReal B) (f := fun ξ => 1 + markedWindowCount L ξ ^ 2)
            (measurable_const.add ((measurable_markedWindowCount L).pow_const 2)),
            lintegral_add_left measurable_const]
          simp
      _ ≤ ENNReal.ofReal B * (1 + C) := by
          gcongr
          exact hC (p j) rfl (R j)
  have hΨD : ∀ M ξ, Ψ M ξ ≤ D ξ := by
    intro M ξ
    apply integral_mono (integrable_markedTest w hw hwc _ (continuous_markPairKernel M) ξ)
      (integrable_markedTest w hw hwc _ continuous_const ξ)
    intro x
    exact mul_le_mul_of_nonneg_left (markPairKernel_le_one M x.2) (abs_nonneg _)
  -- topology of the law space
  have : TopologicalSpace.PseudoMetrizableSpace MarkedPointMeasure :=
    markedPointMeasure_pseudoMetrizableSpace
  have : SecondCountableTopology MarkedPointMeasure := markedPointMeasure_secondCountableTopology
  have : T2Space MarkedPointMeasure := markedPointMeasure_t2Space
  -- realizations, tightness and compactness
  let R' : ∀ j, FiniteRealization (p j) := fun j =>
    ⟨R j, constructSpectralRealization (p j) (R j)⟩
  have hR' : ∀ j, (R' j).markedLaw E = P j := fun j =>
    finiteRealization_markedLaw_eq_canonical (R' j) E
  have htight := BlockBand.Counting.criticalSequence_markedLaws_isTight
    BlockBand.Native.PSSS.sourceContract_holds_zero s b E hb hb' hrho R'
  have hcpt : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have heq : {ν : Measure MarkedPointMeasure | ∃ μ ∈ Set.range P, (μ : Measure _) = ν} =
        Set.range (fun i => ((R' i).markedLaw E : Measure MarkedPointMeasure)) := by
      ext ν
      constructor
      · rintro ⟨μ, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by dsimp only; rw [hR']⟩
      · rintro ⟨i, rfl⟩
        exact ⟨P i, ⟨i, rfl⟩, by dsimp only; rw [hR']⟩
    rw [heq]
    exact htight
  -- conclusion
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun j => ha.trans_le (hX0 j), fun ε hε => ?_⟩
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨φ, hφ, hφX⟩ := extraction_of_frequently_atTop hne
  obtain ⟨Q, -, ψ, hψ, hlim⟩ := hcpt.tendsto_subseq (x := fun n => P (φ n))
    (fun n => subset_closure ⟨φ n, rfl⟩)
  have hcrit : WindowAngular.IsCriticalMarkedLimit τ b E hb hb' Q :=
    ⟨s, R', φ ∘ ψ, hφ.comp hψ, by simpa [Function.comp_def, hR'] using hlim⟩
  have hdiff := hS.diffuse b hb hb' E hE2 τ hτ Q hcrit
  -- `E_Q Ψ_M → 0`
  have hQD : ∫⁻ ξ, ENNReal.ofReal (D ξ) ∂(Q : Measure MarkedPointMeasure) ≤
      ENNReal.ofReal B * (1 + C) :=
    lintegral_le_of_tendsto hlim D hDc _ fun n => hD1 _
  have hQDfin : ∫⁻ ξ, ENNReal.ofReal (D ξ) ∂(Q : Measure MarkedPointMeasure) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hCtop⟩)) hQD
  have hQlim : Tendsto (fun M => ∫⁻ ξ, ENNReal.ofReal (Ψ M ξ) ∂(Q : Measure MarkedPointMeasure))
      atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := (Q : Measure MarkedPointMeasure))
      (F := fun M ξ => ENNReal.ofReal (Ψ M ξ)) (f := fun _ => 0) (fun ξ => ENNReal.ofReal (D ξ))
      (fun M => ENNReal.measurable_ofReal.comp (hΨc M).measurable)
      (fun M => Eventually.of_forall fun ξ => ENNReal.ofReal_le_ofReal (hΨD M ξ)) hQDfin
      (by
        filter_upwards [hdiff] with ξ hξ
        have hint : ∫ x, |w x.1| * markAtomSq x.2 ∂ξ.marked.measure = 0 := by
          apply integral_eq_zero_of_atoms ξ.marked
          intro x hx
          rw [markAtomSq_eq_zero_of_noAtoms x.2 (hξ x hx).2, mul_zero]
        have hconv : Tendsto (fun M => Ψ M ξ) atTop
            (𝓝 (∫ x, |w x.1| * markAtomSq x.2 ∂ξ.marked.measure)) := by
          apply tendsto_integral_of_dominated_convergence (fun x => |w x.1|)
          · intro M
            exact (markedTestFunction w hw hwc _ (continuous_markPairKernel M)).continuous
              |>.aestronglyMeasurable
          · simpa using integrable_markedTest w hw hwc (fun _ => (1 : ℝ)) continuous_const ξ
          · intro M
            refine Eventually.of_forall fun x => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
              (markPairKernel_nonneg M x.2))]
            exact mul_le_of_le_one_right (abs_nonneg _) (markPairKernel_le_one M x.2)
          · exact Eventually.of_forall fun x => (tendsto_markPairKernel x.2).const_mul _
        rw [hint] at hconv
        simpa using ENNReal.tendsto_ofReal hconv)
    simpa using this
  -- choose `M`, then pass to the limit along the subsequence
  have hε4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨M, hM⟩ := (hQlim.eventually (gt_mem_nhds hε4)).exists
  have hev := eventually_lintegral_le_add hlim (Ψ M) (hΨc M) (ENNReal.ofReal B ^ 2 * C)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hCtop)
    (fun n => h2 M _) (ENNReal.ofReal (ε / 4)) hε4
  obtain ⟨n, hn⟩ := hev.exists
  have hle : ∫⁻ ξ, ENNReal.ofReal (Ψ M ξ) ∂(P (φ (ψ n)) : Measure MarkedPointMeasure) ≤
      ENNReal.ofReal (ε / 2) := by
    refine hn.trans ?_
    calc ∫⁻ ξ, ENNReal.ofReal (Ψ M ξ) ∂(Q : Measure MarkedPointMeasure) + ENNReal.ofReal (ε / 4)
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := add_le_add hM.le le_rfl
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  have hXle : X (φ (ψ n)) ≤ ε / 2 := by
    refine (hXΨ M (φ (ψ n))).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hΨ0 M))
      (hΨc M).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) hle
  have := hφX (ψ n)
  simp only [not_lt] at this
  linarith

end BlockBand.PointProcess.BlockAtom
