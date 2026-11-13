module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2EntrLim
public import BlockBand.SourceProcess.PhysApprox.B3Ident2Main2

/-!
# The entrance identification `CapIdentEntranceFdd` and `CapIdentEntrance`

Measure: the candidate's `Q`, the conditioned entrance `μ(s)[|capSet K h]`; at width `W` the
closed law conditioned on the physical cap event. Input: `TransmissionLawContract` (through
`tendsto_capTseq`, `tendsto_capProb`).

* `condObsTestAll_tseq_eq`: the conditioned test of the entrance coordinates is
  `E_W[1_{cap} f(physTseq_J)] / P_W(cap)` (closed-law marginal, Borel cap event a.e.).
* **`capIdentEntranceFdd_holds : CapIdentEntranceFdd`**: both laws of `(t_k)_{k ∈ J}` give
  `E[1{μ(s) ∈ cap} f(t_J(μ(s)))] / P(μ(s) ∈ cap)` for every bounded continuous `f`
  (`ext_of_forall_integral_eq_of_IsFiniteMeasure`).
* **`capIdentEntrance_holds : CapIdentEntrance`** (with `capIdentEntrance_of_fdd`).
* `targetCapCond'_of_gramPins`: `CapIdentGram → CapIdentKDouble → TargetCapCond'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

/-- The test of the `J` entrance coordinates. -/
def tseqTest {J : Finset ℕ} (f : BoundedContinuousFunction (J → ℝ) ℝ) :
    BoundedContinuousFunction (J → ℂ) ℝ :=
  f.compContinuous ⟨fun z k => (z k).re,
    continuous_pi fun k => Complex.continuous_re.comp (continuous_apply k)⟩

/-- The labels of the `J` entrance coordinates. -/
def tseqIdx {K np : ℕ} (J : Finset ℕ) : J → LIdx K np := fun k => Sum.inr (Sum.inl k.val)

theorem condObsTestAll_tseq_eq {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {J : Finset ℕ}
    (f : BoundedContinuousFunction (J → ℝ) ℝ) :
    condObsTestAll b E s h τ m W V (tseqIdx (K := K) (np := np) J) (fun _ => 0) (tseqTest f) =
      (∫ ω, (ClosedIdent.physCapEventM b E s h K W).indicator
          (fun ω => f (J.restrict (physTseq b E s W ω))) ω ∂growthPathLaw W b) /
        (growthPathLaw W b (physCapEventC b E s h K W)).toReal := by
  have e : ∫ y, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
      tseqTest f (fun l => b3ObsAll b E s h τ m W V (tseqIdx J l) 0 y) ∂closedLaw b W np =
      ∫ ω, (ClosedIdent.physCapEventM b E s h K W).indicator
          (fun ω => f (J.restrict (physTseq b E s W ω))) ω ∂growthPathLaw W b := by
    calc _ = ∫ y, (fun ω => (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) ω *
          f (J.restrict (physTseq b E s W ω))) y.1.1 ∂closedLaw b W np :=
          integral_congr_ae (Eventually.of_forall fun y => rfl)
      _ = ∫ ω, (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) ω *
          f (J.restrict (physTseq b E s W ω)) ∂growthPathLaw W b :=
          integral_closedLaw_fst (b := b) (np := np) (fun ω =>
            (physCapEventC b E s h K W).indicator (fun _ => (1 : ℝ)) ω *
              f (J.restrict (physTseq b E s W ω)))
      _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [ClosedIdent.physCapEvent_ae_eq hb hE1 hE2 s h K] with ω hω
        have hω' : (ω ∈ physCapEventC b E s h K W) = (ω ∈ ClosedIdent.physCapEventM b E s h K W) :=
          hω
        by_cases hc : ω ∈ ClosedIdent.physCapEventM b E s h K W
        · have hc' : ω ∈ physCapEventC b E s h K W := hω' ▸ hc
          rw [Set.indicator_of_mem hc', Set.indicator_of_mem hc, one_mul]
        · have hc' : ω ∉ physCapEventC b E s h K W := hω' ▸ hc
          rw [Set.indicator_of_notMem hc', Set.indicator_of_notMem hc, zero_mul]
  unfold condObsTestAll
  rw [e]

/-- **`CapIdentEntranceFdd` holds.** -/
theorem capIdentEntranceFdd_holds : CapIdentEntranceFdd := by
  intro hTL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP J
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, -, -, -, -⟩, hfdd⟩ := hP
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, hs, hτ, hh0, -, -⟩ := hD
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  have hb1 : b < 1 := by linarith
  set Mf : Ω → Measure unitInterval := fun ω => (μ s ω : Measure unitInterval)
  have hMf : Measurable Mf := measurable_subtype_coe.comp (hlim.measurable s hs)
  set A := capSet K h
  have hAm : MeasurableSet A := measurableSet_capSet K h
  have hρc : (entranceLaw P μ s)[|A] = (P[|Mf ⁻¹' A]).map Mf := map_cond P hMf hAm
  have hPA : P (Mf ⁻¹' A) = entranceLaw P μ s A := (Measure.map_apply hMf hAm).symm
  have hne' : P (Mf ⁻¹' A) ≠ 0 := by rwa [hPA]
  have : IsProbabilityMeasure (P[|Mf ⁻¹' A]) := cond_isProbabilityMeasure hne'
  set p := (entranceLaw P μ s A).toReal
  have hp : p ≠ 0 := (ENNReal.toReal_pos hne (measure_ne_top _ _)).ne'
  have hres : Measurable (fun t : ℕ → ℝ => J.restrict t) := Finset.measurable_restrict J
  rw [hρc, Measure.map_map (show Measurable fun ν => J.restrict (seqExtract ν) from
    hres.comp measurable_seqExtract) hMf]
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map (show AEMeasurable (fun ω => J.restrict (tseq ω)) Q from
      (hres.comp htm).aemeasurable) f.continuous.aestronglyMeasurable,
    integral_map (show AEMeasurable ((fun ν => J.restrict (seqExtract ν)) ∘ Mf) (P[|Mf ⁻¹' A])
      from ((hres.comp measurable_seqExtract).comp hMf).aemeasurable)
      f.continuous.aestronglyMeasurable]
  set Ninf := ∫ ω, {ω | (μ s ω : Measure unitInterval) ∈ capSet K h}.indicator
    (fun ω => f (J.restrict (seqExtract (μ s ω : Measure unitInterval)))) ω ∂P
  have hR : ∫ ω, f (J.restrict (seqExtract (Mf ω))) ∂(P[|Mf ⁻¹' A]) = Ninf / p := by
    rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator (hMf hAm), hPA,
      ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]
    rfl
  have hu : ∀ (l : J) (j : Fin np), s + (((fun _ : J => (0 : ℝ≥0)) l : ℝ≥0) : ℝ) ≠ τ j :=
    fun _ j => by simp only [NNReal.coe_zero, add_zero]; exact (hτ j).ne
  have h1 := hfdd J (tseqIdx J) (fun _ => 0) hu (tseqTest f)
  have hL : ∫ ω, tseqTest f (fun l => complexObs tseq G Kc (tseqIdx J l)
      ((fun _ : J => (0 : ℝ≥0)) l) ω) ∂Q = ∫ ω, f (J.restrict (tseq ω)) ∂Q :=
    integral_congr_ae (Eventually.of_forall fun ω => rfl)
  rw [hL] at h1
  have h2 : Tendsto (fun n => condObsTestAll b E s h τ m (φ n) (Vs (φ n)) (tseqIdx J)
      (fun _ => 0) (tseqTest f)) atTop (𝓝 (Ninf / p)) := by
    have hnum := (tendsto_capTseq hTL hb0 hb hE1 hE2 hlim hs hh0 hA K J f).comp hφ
    have hden := (CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh0 K (hA K)).comp hφ
    refine (hnum.div hden hp).congr fun n => ?_
    exact (condObsTestAll_tseq_eq hb1 hE1 hE2 (φ n) (Vs (φ n)) f).symm
  show ∫ ω, f (J.restrict (tseq ω)) ∂Q = ∫ ω, f (J.restrict (seqExtract (Mf ω))) ∂(P[|Mf ⁻¹' A])
  rw [hR]
  exact tendsto_nhds_unique h1 h2

/-- **`CapIdentEntrance` holds.** -/
theorem capIdentEntrance_holds : CapIdentEntrance :=
  capIdentEntrance_of_fdd capIdentEntranceFdd_holds

/-- **`TargetCapCond'` from `CapIdentGram` and `CapIdentKDouble`.** -/
theorem targetCapCond'_of_gramPins (hGr : CapIdentGram) (hKD : CapIdentKDouble) :
    TargetCapCond' :=
  targetCapCond'_of_three capIdentEntrance_holds hGr hKD

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
