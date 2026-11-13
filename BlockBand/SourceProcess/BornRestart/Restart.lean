module

public import BlockBand.SourceProcess.BornRestart.Lim

/-!
# Optional sampling at a `𝓖₀`-measurable time: the restart lemma

* `setIntegral_dyShift_eq`: for a `𝓖`-martingale `M` and `B ∈ 𝓗_s`,
  `∫_B M(a_k + t) = ∫_B M(a_k + s)` with `a_k = dyU k a`. This is discrete optional sampling on the
  `𝓖₀`-events `{a_k = i/2ᵏ}`.
* `exists_martingale_restart`: if `M` is a `𝓖`-martingale modification of a process `X` with
  a.s. continuous paths, bounded on every window `[a, a + u + 1]`, then `u ↦ X(a + u)` has an
  `𝓗`-martingale modification, `𝓗 = shiftFiltration 𝓖 a`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 m} {a : Ω → ℝ≥0} {ha : Measurable[𝓖 0] a}

omit [IsProbabilityMeasure Q] in
theorem measurable_dyIdx_comp (ha : Measurable[𝓖 0] a) (k : ℕ) :
    Measurable[𝓖 0] fun ω => dyIdx k (a ω) :=
  (measurable_from_nat (f := fun n : ℕ => n + 1)).comp
    (Nat.measurable_floor.comp (ha.mul_const _))

omit [IsProbabilityMeasure Q] in
theorem stronglyMeasurable_dyAt (ha : Measurable[𝓖 0] a) {M : ℝ≥0 → Ω → ℂ}
    (hM : ∀ t, StronglyMeasurable[m] (M t)) (k : ℕ) (u : ℝ≥0) :
    StronglyMeasurable[m] fun ω => M (dyU k (a ω) + u) ω :=
  stronglyMeasurable_comp_nat (h := fun i => M ((i : ℝ≥0) / 2 ^ k + u))
    ((measurable_dyIdx_comp ha k).mono (𝓖.le 0) le_rfl) fun _ => hM _

/-- **Discrete optional sampling on the events `{a_k = i/2ᵏ}`.** -/
theorem setIntegral_dyShift_eq {M : ℝ≥0 → Ω → ℂ} (hM : Martingale M 𝓖 Q) (k : ℕ) {s t : ℝ≥0}
    (hst : s ≤ t) {B : Set Ω} (hB : MeasurableSet[shiftFiltration 𝓖 a ha s] B)
    (hint : ∀ u, Integrable (fun ω => M (dyU k (a ω) + u) ω) Q) :
    ∫ ω in B, M (dyU k (a ω) + t) ω ∂Q = ∫ ω in B, M (dyU k (a ω) + s) ω ∂Q := by
  set P : ℕ → Set Ω := fun i => B ∩ {ω | dyIdx k (a ω) = i}
  have hE : ∀ i, MeasurableSet[𝓖 0] {ω | dyIdx k (a ω) = i} := fun i =>
    measurable_dyIdx_comp ha k (measurableSet_singleton i)
  have hPm : ∀ i, MeasurableSet (P i) := fun i =>
    ((shiftFiltration 𝓖 a ha).le s _ hB).inter (𝓖.le 0 _ (hE i))
  have hPd : Pairwise (Function.onFun Disjoint P) := fun i i' hii' => by
    refine Set.disjoint_left.2 fun ω h1 h2 => hii' ?_
    exact h1.2.symm.trans h2.2
  have hBU : B = ⋃ i, P i := by
    ext ω
    simp only [P, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hpiece : ∀ (i : ℕ) (u : ℝ≥0), ∫ ω in P i, M (dyU k (a ω) + u) ω ∂Q =
      ∫ ω in P i, M ((i : ℝ≥0) / 2 ^ k + u) ω ∂Q := fun i u => by
    refine setIntegral_congr_fun (hPm i) fun ω hω => ?_
    have h2 : dyIdx k (a ω) = i := hω.2
    simp only [dyU, h2]
  have hPs : ∀ i : ℕ, MeasurableSet[𝓖 ((i : ℝ≥0) / 2 ^ k + s)] (P i) := fun i => by
    have e : P i = (B ∩ {ω | a ω + s < (i : ℝ≥0) / 2 ^ k + s}) ∩ {ω | dyIdx k (a ω) = i} := by
      ext ω
      simp only [P, mem_inter_iff, mem_ofPred_eq]
      refine ⟨fun h => ⟨⟨h.1, ?_⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      have := lt_dyU k (a ω)
      rw [dyU, h.2] at this
      exact add_lt_add_of_lt_of_le this le_rfl
    rw [e]
    exact (hB _).inter (𝓖.mono zero_le _ (hE i))
  rw [hBU, integral_iUnion hPm hPd (hint t).integrableOn,
    integral_iUnion hPm hPd (hint s).integrableOn]
  refine tsum_congr fun i => ?_
  rw [hpiece, hpiece]
  exact (hM.setIntegral_eq (add_le_add le_rfl hst) (hPs i)).symm

/-- **The restart lemma.** -/
theorem exists_martingale_restart {M X : ℝ≥0 → Ω → ℂ} (hM : Martingale M 𝓖 Q)
    (hMX : ∀ t, M t =ᵐ[Q] X t) (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (hbd : ∀ u, ∃ C, ∀ᵐ ω ∂Q, ∀ v ≤ u + 1, ‖X (a ω + v) ω‖ ≤ C) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (shiftFiltration 𝓖 a ha) Q ∧
      ∀ u, N u =ᵐ[Q] fun ω => X (a ω + u) ω := by
  have key : ∀ u, ∀ᵐ ω ∂Q, ∀ k, M (dyU k (a ω) + u) ω = X (dyU k (a ω) + u) ω := fun u => by
    have h := ae_all_iff.2 fun p : ℕ × ℕ => hMX ((p.2 : ℝ≥0) / 2 ^ p.1 + u)
    filter_upwards [h] with ω hω k
    exact hω (k, dyIdx k (a ω))
  have hYm : ∀ k u, StronglyMeasurable[m] fun ω => M (dyU k (a ω) + u) ω := fun k u =>
    stronglyMeasurable_dyAt ha (fun t => (hM.1 t).mono (𝓖.le t)) k u
  have hwin : ∀ k (ω : Ω) (u : ℝ≥0), ∃ v ≤ u + 1, dyU k (a ω) + u = a ω + v := fun k ω u =>
    ⟨dyU k (a ω) - a ω + u, by
      rw [add_comm u 1]
      exact add_le_add (tsub_le_iff_left.2 (dyU_le_add_one k (a ω))) le_rfl, by
      rw [← add_assoc, add_tsub_cancel_of_le (lt_dyU k (a ω)).le]⟩
  have hYbd : ∀ u, ∃ C, ∀ k, ∀ᵐ ω ∂Q, ‖M (dyU k (a ω) + u) ω‖ ≤ C := fun u => by
    obtain ⟨C, hC⟩ := hbd u
    refine ⟨C, fun k => ?_⟩
    filter_upwards [key u, hC] with ω h1 h2
    obtain ⟨v, hv, e⟩ := hwin k ω u
    rw [h1 k, e]
    exact h2 v hv
  have hint : ∀ k u, Integrable (fun ω => M (dyU k (a ω) + u) ω) Q := fun k u => by
    obtain ⟨C, hC⟩ := hYbd u
    exact Integrable.of_bound (hYm k u).aestronglyMeasurable C (hC k)
  refine exists_martingale_of_tendsto (Y := fun k u ω => M (dyU k (a ω) + u) ω)
    (stronglyMeasurable_limUnder_shift (Y := fun _ => M) (fun _ t => hM.1 t))
    (fun k u => (hYm k u).aestronglyMeasurable) (fun u => ?_) hYbd
    (fun k s t hst B hB => setIntegral_dyShift_eq hM k hst hB (hint k))
  filter_upwards [key u, hc] with ω h1 h2
  simp only [h1]
  exact ((h2.tendsto _).comp ((tendsto_dyU (a ω)).add_const u))

end BlockBand.SourceProcess.BornRestart
