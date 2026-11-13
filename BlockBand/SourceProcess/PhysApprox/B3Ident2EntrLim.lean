module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2EntrT
public import BlockBand.SourceProcess.PhysApprox.B3Ident2Entr

/-!
# The finite-dimensional entrance laws `CapIdentEntranceFdd`

Measure: at width `W` the path law `growthPathLaw W b` (and the closed law, through its
marginal); the limit `P`; the candidate's `Q`. Input: `TransmissionLawContract` only.

* `exists_TK_approx`: for a bounded continuous `f` on `ℝ^J` and `ε > 0` there are `δ, M` with
  `|f(t_J) − f(T^δ_J(ν))| ≤ ε` on every trace measure `ν = Σ t_i δ_{t_i}` (uniform continuity of
  `f` on `[0,1]^J`, `abs_TK_sub_le`).
* **`tendsto_capTseq`**: `E_W[1_{cap} f(physTseq_J)] → E[1{μ(s) ∈ cap} f(t_J(μ(s)))]`, for
  non-atomic `h` (`tendsto_capWeighted` applied to `f ∘ T^δ_J + ‖f‖` and `‖f‖`;
  `ae_transmissionProcess_seq` at width `W`, `entranceAtomic_of` in the limit).
* `integral_closedLaw_fst`: the closed law has the path law as marginal.
* **`capIdentEntranceFdd_holds : CapIdentEntranceFdd`** (bounded continuous tests of the `J`
  coordinates determine the laws, `ext_of_forall_integral_eq_of_IsFiniteMeasure`), and
  **`capIdentEntrance_holds : CapIdentEntrance`**.
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

/-- **Uniform approximation of `f(t_J)` by a continuous functional of `ν`.** -/
theorem exists_TK_approx {J : Finset ℕ} (f : BoundedContinuousFunction (J → ℝ) ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℕ, ∀ (ν : FiniteMeasure unitInterval) (t : ℕ → ℝ),
      (ν : Measure unitInterval) = seqTraceMeasure t → IsTransmissionSequence t →
        |f (J.restrict t) - f (fun k : J => TK δ M k ν)| ≤ ε := by
  set S : Set (J → ℝ) := Set.pi Set.univ fun _ => Set.Icc 0 1
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨δ', hδ', hu⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous f.continuous.continuousOn) ε hε
  refine ⟨δ' / 4, by positivity, ⌈1 / (δ' / 4)⌉₊, fun ν t hν ht => ?_⟩
  have hδ : 0 < δ' / 4 := by positivity
  have hM : 1 ≤ (⌈1 / (δ' / 4)⌉₊ : ℝ) * (δ' / 4) := by
    have := Nat.le_ceil (1 / (δ' / 4))
    rwa [div_le_iff₀ hδ] at this
  have hx : J.restrict t ∈ S := fun k _ => ⟨(ht.2.1 k).1, (ht.2.1 k).2⟩
  have hy : (fun k : J => TK (δ' / 4) ⌈1 / (δ' / 4)⌉₊ k ν) ∈ S := fun k _ =>
    ⟨(TK_mem hδ hν ht k).1, (TK_mem hδ hν ht k).2⟩
  have hd : dist (J.restrict t) (fun k : J => TK (δ' / 4) ⌈1 / (δ' / 4)⌉₊ k ν) < δ' := by
    rw [dist_pi_lt_iff hδ']
    intro k
    rw [Real.dist_eq, abs_sub_comm]
    have := abs_TK_sub_le hδ hM hν ht k
    show |TK (δ' / 4) ⌈1 / (δ' / 4)⌉₊ k ν - t k| < δ'
    linarith
  have := hu _ hx _ hy hd
  rw [Real.dist_eq] at this
  exact this.le

/-- The approximating test on `FiniteMeasure [0,1]`. -/
def fTK {J : Finset ℕ} (f : BoundedContinuousFunction (J → ℝ) ℝ) {δ : ℝ} (hδ : 0 < δ) (M : ℕ) :
    BoundedContinuousFunction (FiniteMeasure unitInterval) ℝ :=
  f.compContinuous ⟨fun ν k => TK δ M k ν, continuous_pi fun k => continuous_TK hδ M k⟩

theorem integral_closedLaw_fst {b : ℝ} {W np : ℕ} (F : GrowthPath W → ℝ) :
    ∫ y, F y.1.1 ∂closedLaw b W np = ∫ ω, F ω ∂growthPathLaw W b := by
  have := BlockBand.Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  rw [closedLaw, integral_fun_fst (f := fun x : ProbedPath W np => F x.1), probedPathLaw,
    integral_fun_fst]
  simp

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {b E s h : ℝ}

/-- **The entrance coordinates on the cap event converge.** -/
theorem tendsto_capTseq (hTL : TransmissionLawContract) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hlim : IsTransmissionLimit b E (fun _ => 0) P μ) (hs : 0 < s)
    (hh : 0 < h) (hA : CapCond.NoAtom (entranceLaw P μ s) h) (K : ℕ) (J : Finset ℕ)
    (f : BoundedContinuousFunction (J → ℝ) ℝ) :
    Tendsto (fun W => ∫ ω, (ClosedIdent.physCapEventM b E s h K W).indicator
        (fun ω => f (J.restrict (physTseq b E s W ω))) ω ∂growthPathLaw W b) atTop
      (𝓝 (∫ ω, {ω | (μ s ω : Measure unitInterval) ∈ capSet K h}.indicator
        (fun ω => f (J.restrict (seqExtract (μ s ω : Measure unitInterval)))) ω ∂P)) := by
  have := hlim.prob
  have hμ := hlim.measurable s hs
  have hMf : Measurable fun ω => (μ s ω : Measure unitInterval) := measurable_subtype_coe.comp hμ
  have hcapM : MeasurableSet {ω | (μ s ω : Measure unitInterval) ∈ capSet K h} :=
    hMf (measurableSet_capSet K h)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, M, happ⟩ := exists_TK_approx f (show 0 < ε / 4 by positivity)
  set w0 := fTK f hδ M
  set c := ‖f‖
  set w1 := w0 + BoundedContinuousFunction.const (FiniteMeasure unitInterval) c
  set w2 := BoundedContinuousFunction.const (FiniteMeasure unitInterval) c
  have hw1 : ∀ ν, 0 ≤ w1 ν := fun ν => by
    have := f.norm_coe_le_norm (fun k : J => TK δ M k ν)
    rw [Real.norm_eq_abs] at this
    show 0 ≤ f (fun k : J => TK δ M k ν) + c
    linarith [neg_abs_le (f (fun k : J => TK δ M k ν))]
  have hw2 : ∀ ν, 0 ≤ w2 ν := fun ν => norm_nonneg f
  have t1 := CapCond.tendsto_capWeighted (w := w1) hTL hb0 hb hE1 hE2 hlim hs hh K (hA K) hw1
  have t2 := CapCond.tendsto_capWeighted (w := w2) hTL hb0 hb hE1 hE2 hlim hs hh K (hA K) hw2
  have hfin : ∀ W, CapCond.finInt b E s h K W w1 - CapCond.finInt b E s h K W w2 =
      CapCond.finInt b E s h K W w0 := fun W => by
    unfold CapCond.finInt
    rw [← integral_sub (CapCond.integrable_finInd hb hE1 hE2 s h K)
      (CapCond.integrable_finInd hb hE1 hE2 s h K)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ ClosedIdent.physCapEventM b E s h K W
    · simp only [Set.indicator_of_mem hω, w1, w2, BoundedContinuousFunction.coe_add,
        Pi.add_apply, BoundedContinuousFunction.const_apply]
      ring
    · simp only [Set.indicator_of_notMem hω, sub_zero]
  have hlimI : CapCond.limInt P μ s w1 (capSet K h) - CapCond.limInt P μ s w2 (capSet K h) =
      CapCond.limInt P μ s w0 (capSet K h) := by
    unfold CapCond.limInt
    rw [← integral_sub (CapCond.integrable_limInd hμ (measurableSet_capSet K h))
      (CapCond.integrable_limInd hμ (measurableSet_capSet K h))]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ {ω | (μ s ω : Measure unitInterval) ∈ capSet K h}
    · simp only [Set.indicator_of_mem hω, w1, w2, BoundedContinuousFunction.coe_add,
        Pi.add_apply, BoundedContinuousFunction.const_apply]
      ring
    · simp only [Set.indicator_of_notMem hω, sub_zero]
  have t0 : Tendsto (fun W => CapCond.finInt b E s h K W w0) atTop
      (𝓝 (CapCond.limInt P μ s w0 (capSet K h))) := by
    rw [← hlimI]; exact (t1.sub t2).congr hfin
  obtain ⟨W₀, hW₀⟩ := Metric.tendsto_atTop.1 t0 (ε / 4) (by positivity)
  -- the limit error
  have hlimErr : |CapCond.limInt P μ s w0 (capSet K h) - ∫ ω, {ω | (μ s ω : Measure unitInterval)
      ∈ capSet K h}.indicator (fun ω => f (J.restrict (seqExtract (μ s ω : Measure
        unitInterval)))) ω ∂P| ≤ ε / 4 := by
    have hat := SourcePins.entranceAtomic_of hTL b hb0 hb E hE1 hE2 Ω _ P μ hlim s hs
    have hm2 : Measurable fun ω => f (J.restrict (seqExtract (μ s ω : Measure unitInterval))) :=
      f.continuous.measurable.comp ((Finset.measurable_restrict J).comp
        (measurable_seqExtract.comp hMf))
    unfold CapCond.limInt
    rw [← integral_sub (CapCond.integrable_limInd hμ (measurableSet_capSet K h))
      ((Integrable.of_bound hm2.aestronglyMeasurable ‖f‖ (Eventually.of_forall fun _ =>
        f.norm_coe_le_norm _)).indicator hcapM), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 4) ?_).trans (by simp)
    filter_upwards [hat] with ω hω'
    obtain ⟨t, ht, he⟩ := hω'
    by_cases hω : ω ∈ {ω | (μ s ω : Measure unitInterval) ∈ capSet K h}
    · simp only [Set.indicator_of_mem hω]
      rw [he, seqExtract_seqTraceMeasure ht, Real.norm_eq_abs, abs_sub_comm]
      exact happ _ t he ht
    · simp only [Set.indicator_of_notMem hω, sub_zero, norm_zero]; positivity
  -- the finite-width error
  refine ⟨max W₀ 1, fun W hW => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have := BlockBand.Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
  have hm1 : Measurable fun ω : GrowthPath W => f (J.restrict (physTseq b E s W ω)) :=
    f.continuous.measurable.comp (Measurable.of_eval fun k => CapLaw.measurable_physTseq b E s W k)
  have hfinErr : |(∫ ω, (ClosedIdent.physCapEventM b E s h K W).indicator
      (fun ω => f (J.restrict (physTseq b E s W ω))) ω ∂growthPathLaw W b) -
        CapCond.finInt b E s h K W w0| ≤ ε / 4 := by
    unfold CapCond.finInt
    rw [← integral_sub ((Integrable.of_bound hm1.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun _ => f.norm_coe_le_norm _)).indicator
        (ClosedIdent.measurableSet_physCapEventM b E s h K W))
      (CapCond.integrable_finInd hb hE1 hE2 s h K), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 4) ?_).trans (by simp)
    filter_upwards [CapCond.ae_transmissionProcess_seq hb hE1 hE2 hW1 s] with ω hω'
    obtain ⟨ht, he⟩ := hω'
    by_cases hω : ω ∈ ClosedIdent.physCapEventM b E s h K W
    · simp only [Set.indicator_of_mem hω, Real.norm_eq_abs]
      exact happ _ _ he ht
    · simp only [Set.indicator_of_notMem hω, sub_zero, norm_zero]; positivity
  have h0 := hW₀ W (le_of_max_le_left hW)
  rw [Real.dist_eq] at h0 ⊢
  have key : ∀ a b c d : ℝ, |a - b| ≤ ε / 4 → |b - c| < ε / 4 → |c - d| ≤ ε / 4 →
      |a - d| < ε := fun a b c d h1 h2 h3 => by
    have := (abs_sub_le a b d).trans (add_le_add_right (abs_sub_le b c d) _)
    linarith
  exact key _ _ _ _ hfinErr h0 hlimErr

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
