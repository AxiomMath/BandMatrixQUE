module

public import BlockBand.Transmission.DualAtomless.Kernel
public import BlockBand.Transmission.Dual.GB1RCorner

/-!
# Atomlessness of the level-one lifetime from a random start, conditionally on the old state

For the level-1 random-start family `F : B1R D₀ 1 μ ξ` on `ΩR S 1 = S × (driver)` and every
measurable `c : S → ℝ≥0`: **`ae_zeta_ne`**: a.s. `ζ(x) ≠ c(x.1)`, i.e. the chart explosion time
has no atom at any `𝓖₀`-measurable random time that is a function of the old state.

Proof: condition on `η = (ξ, c) ∘ fst` (`ae_isMPSolutionOn_kernelC`). For a.e. `e = (z, u)` the
kernel solves the flat level-1 dual problem from `z` in every box of `boxExh 1 n₀`, so its
truncated stop sequence has the law of a `B1Family` from `z` (`map_eq_of_isMPSolutionOn`), for
which the atomlessness on the sequence space (`a3Seq_holds`) gives `P(ρ_∞ ∧ t₀ = u) = 0` for
`u < t₀`. Integrate (`ae_of_ae_condKernel`) and use `ρ_∞ ∧ t₀ = ζ ∧ t₀` on consistent paths
(`coe_sinf_stopSeq`); take the union over `n₀, t₀ ∈ ℕ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualAtomless

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.Transmission.Dual
open BlockBand.Transmission.Dual.G
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {D0 : ℝ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin (1 + 1) → ℝ}

/-- The kernel half: for a.e. conditioning value `(z, u)` with `z` in the base box and
`u < t₀`, the truncated stop sequence of the kernel avoids `ρ_∞ ∧ t₀ = u`. -/
theorem ae_sinf_ne_box (hD0 : 0 < D0) (hξ : Measurable ξ) (F : B1R D0 1 μ ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber 1) {c : S → ℝ≥0} (hc : Measurable c) {n₀ : ℕ}
    {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, boxExh 1 n₀ n ⊆ chartQ 1 '' Metric.ball 0 (r n)) (t₀ : ℝ≥0) :
    ∀ᵐ x ∂PR μ 1, ξ x.1 ∈ flatBox 1 n₀ → c x.1 < t₀ →
      sinf (boxExh 1 n₀) t₀ (F.stopSeq (boxExh 1 n₀) t₀ r x) ≠ c x.1 := by
  set W := boxExh 1 n₀
  have hE := isExh_boxExh 1 n₀
  have hW : ∀ n, IsOpen (W n) := hE.isOpen
  set Z : ℕ → ΩR S 1 → CPath (1 + 1) := fun n => F.cpath (r n)
  set η : ΩR S 1 → (Fin (1 + 1) → ℝ) × ℝ≥0 := fun x => (ξ x.1, c x.1)
  have hη : Measurable[𝓖R μ 1 0] η := measurable_fst_zero μ (hξ.prodMk hc)
  have hZ : ∀ n, IsMPSolutionOn (PR μ 1) (𝓖R μ 1) (flatDrift D0 1) (flatDiff D0 1) (W n)
      (zproc Z n) := fun n => isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 (r n)) (hball n)
  have hZa : ∀ n t, StronglyMeasurable[𝓖R μ 1 t] (zproc Z n t) := fun n t => (hZ n).adapted t
  have hZ0 : ∀ n x, (Z n x).1 0 = Prod.fst (η x) := fun _ x => F.Yf_zero hξc _ x
  have hb : ∀ n, ContinuousOn (flatDrift D0 1) (W n) := fun n =>
    (continuousOn_flatDrift D0).mono (subset_closure.trans (hE.dom n).2.2)
  have ha : ∀ n, ContinuousOn (flatDiff D0 1) (W n) := fun n =>
    (contDiff_flatDiff D0).continuous.continuousOn
  have hst := F.isStopSeq_stopSeq (t₀ := t₀) hD0 hW hE.mono hr hball
  have hηΦ : Measurable fun x => (η x, useq W Z x) :=
    (hη.mono ((𝓖R μ 1).le 0) le_rfl).prodMk (measurable_useq hW hZa)
  have hbox : MeasurableSet (flatBox 1 n₀) := (isInteriorDomain_flatBox _ _).1.measurableSet
  set A := {p : ((Fin (1 + 1) → ℝ) × ℝ≥0) × CSeq (1 + 1) |
    p.1.1 ∈ flatBox 1 n₀ → p.1.2 < t₀ → sinf W t₀ (ctr W t₀ p.2) ≠ p.1.2}
  have hsinf : Measurable fun p : ((Fin (1 + 1) → ℝ) × ℝ≥0) × CSeq (1 + 1) =>
      sinf W t₀ (ctr W t₀ p.2) :=
    (measurable_sinf hW).comp ((measurable_ctr hW t₀).comp measurable_snd)
  have hA : MeasurableSet A := by
    have e : A = (Prod.fst ⁻¹' (Prod.fst ⁻¹' flatBox 1 n₀))ᶜ ∪
        ({p : ((Fin (1 + 1) → ℝ) × ℝ≥0) × CSeq (1 + 1) | p.1.2 < t₀}ᶜ ∪
          {p | sinf W t₀ (ctr W t₀ p.2) = p.1.2}ᶜ) := by
      ext p; simp only [A, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
    rw [e]
    refine ((measurable_fst.fst hbox).compl).union ((?_ : MeasurableSet _).compl.union
      (measurableSet_eq_fun hsinf measurable_fst.snd).compl)
    exact measurableSet_lt measurable_fst.snd measurable_const
  have hK : ∀ᵐ e ∂(jlaw (PR μ 1) η (useq W Z)).fst,
      ∀ᵐ ŵ ∂(jlaw (PR μ 1) η (useq W Z)).condKernel e, (e, ŵ) ∈ A := by
    filter_upwards [ae_isMPSolutionOn_kernelC hW hZ hZ0 measurable_fst hη hb ha,
      ae_isStopSeq_kernelC hW hZa hη t₀ hst] with e hz hzs
    by_cases hzb : e.1 ∈ flatBox 1 n₀
    · by_cases hlt : e.2 < t₀
      · obtain ⟨F'⟩ := nonempty_b1Family hD0 e.1
        obtain ⟨B, hB⟩ := exists_boxRad 1 n₀
        have hr' := monotone_majorant B
        have hball' : ∀ n, W n ⊆ chartQ 1 '' Metric.ball 0 (majorant B n) := fun n =>
          (hB n).trans (chartQ_ball_mono (le_majorant B n))
        have hz0 : e.1 ∈ W 0 := hzb
        have hz' : e.1 ∈ flatChamber 1 := (hE.dom 0).2.2 (subset_closure hz0)
        have hmap : ((jlaw (PR μ 1) η (useq W Z)).condKernel e).map (ctr W t₀) =
            (Pq 1).map (F'.stopSeq W t₀ (majorant B)) :=
          map_eq_of_isMPSolutionOn hD0 hE.dom (measurable_ctr hW t₀)
            (F'.measurable_stopSeq hW _) hzs (F'.isStopSeq_stopSeq hD0 hW hE.mono hr' hball')
            (fun n => isDualStopAt_cY (hz n).1 (hz n).2) (F'.isDualStopAt hD0 hz' hball')
        have h3 := a3Seq_holds hD0 e.1 n₀ hzb F' (majorant B) hr' hball' t₀ e.2 hlt
        have hmeas : MeasurableSet {w : ℕ → CPath (1 + 1) | sinf W t₀ w = e.2} :=
          measurableSet_eq_fun (measurable_sinf hW) measurable_const
        have h4 : (jlaw (PR μ 1) η (useq W Z)).condKernel e
            (ctr W t₀ ⁻¹' {w | sinf W t₀ w = e.2}) = 0 := by
          rw [← Measure.map_apply (measurable_ctr hW t₀) hmeas, hmap,
            Measure.map_apply (F'.measurable_stopSeq hW _) hmeas]
          exact h3
        rw [ae_iff]
        refine measure_mono_null (fun ŵ hŵ => ?_) h4
        simp only [mem_ofPred_eq, A, not_forall, not_not] at hŵ
        exact hŵ.2.2
      · exact ae_of_all _ fun ŵ _ h => absurd h hlt
    · exact ae_of_all _ fun ŵ h => absurd h hzb
  filter_upwards [ae_of_ae_condKernel hηΦ hA hK] with x hx hξx hcx
  have := hx hξx hcx
  rwa [ctr_useq hW t₀ x] at this

/-- **The level-one lifetime from a random start has no atom at a function of the old
state.** -/
theorem ae_zeta_ne (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber 1)
    (F : B1R D0 1 μ ξ) {c : S → ℝ≥0} (hc : Measurable c) :
    ∀ᵐ x ∂PR μ 1, F.zeta x ≠ (c x.1 : WithTop ℝ≥0) := by
  choose B hB using fun n₀ => exists_boxRad 1 n₀
  set r : ℕ → ℕ → ℕ := fun n₀ n => max (majorant (B n₀) n) n
  have hr : ∀ n₀, Monotone (r n₀) := fun n₀ => (monotone_majorant _).max monotone_id
  have hrn : ∀ n₀ n, n ≤ r n₀ n := fun _ _ => le_max_right _ _
  have hball : ∀ n₀ n, boxExh 1 n₀ n ⊆ chartQ 1 '' Metric.ball 0 (r n₀ n) :=
    fun n₀ n => (hB n₀ n).trans (chartQ_ball_mono ((le_majorant _ n).trans (le_max_left _ _)))
  have h1 := ae_all_iff.2 fun n₀ => ae_all_iff.2 fun t₀ : ℕ =>
    ae_sinf_ne_box hD0 hξ F hξc hc (hr n₀) (hball n₀) (t₀ : ℝ≥0)
  filter_upwards [h1, F.ae_consistent hD0] with x hx hcons heq
  obtain ⟨n₀, hn₀⟩ := (isExh_boxExh 1 0).cover _ (hξc x.1)
  rw [boxExh, zero_add] at hn₀
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt (c x.1)
  have hs := F.coe_sinf_stopSeq (isExh_boxExh 1 n₀) (hrn n₀) (hball n₀) hcons (t₀ : ℝ≥0)
  rw [heq, min_eq_left (WithTop.coe_le_coe.2 ht₀.le)] at hs
  exact hx n₀ t₀ hn₀ ht₀ (WithTop.coe_inj.1 hs)

end BlockBand.Transmission.DualAtomless
