module

public import BlockBand.Palm.MomentFlow.PropMeas

/-!
# Time-integrated excess on an increasing family of good sets

Abstract form of the monotone-union argument of `tail6_core` (Tonelli and Markov in time).

* **`excess_core`**: `G n` increasing `m`-measurable sets; `Y n v ω` `m`-measurable in `ω`,
  continuous in `v`, in `[0, K]` on `G n`, independent of `n` on `G n`; per deterministic time
  `μ{ω ∈ G n, δ < Y n v ω} ≤ p`. Then **one** `m`-measurable `B` with
  `μ(B) ≤ (b-a)(δ + Kp)/t + p` such that off `B`, for every `n` with `ω ∈ G n`,
  `∫_a^b Y n ≤ t` and `Y n b ≤ δ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set MeasureTheory

theorem excess_core {Ω : Type*} (m : MeasurableSpace Ω) {m0 : MeasurableSpace Ω}
    (hm : m ≤ m0) (μ : Measure Ω) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b)
    (G : ℕ → Set Ω) (hGm : ∀ n, MeasurableSet[m] (G n)) (hGmono : ∀ n, G n ⊆ G (n + 1))
    (Y : ℕ → ℝ → Ω → ℝ) (hYm : ∀ n, ∀ v ∈ Icc a b, Measurable[m] (Y n v))
    (hYc : ∀ n ω, ContinuousOn (fun v => Y n v ω) (Icc a b))
    {K δ p t : ℝ} (hY0 : ∀ n, ∀ ω ∈ G n, ∀ v ∈ Icc a b, 0 ≤ Y n v ω)
    (hYK : ∀ n, ∀ ω ∈ G n, ∀ v ∈ Icc a b, Y n v ω ≤ K) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hp : 0 ≤ p) (ht : 0 < t)
    (hcons : ∀ n, ∀ ω ∈ G n, ∀ v ∈ Icc a b, Y (n + 1) v ω = Y n v ω)
    (hbad : ∀ n, ∀ v ∈ Icc a b, μ {ω | ω ∈ G n ∧ δ < Y n v ω} ≤ ENNReal.ofReal p) :
    ∃ B : Set Ω, MeasurableSet[m] B ∧
      μ B ≤ ENNReal.ofReal ((b - a) * (δ + K * p) / t + p) ∧
      ∀ ω, ω ∉ B → ∀ n, ω ∈ G n → (∫ v in a..b, Y n v ω) ≤ t ∧ Y n b ω ≤ δ := by
  classical
  set X : ℕ → ℝ → Ω → ℝ := fun n v ω => (G n).indicator (fun ω => Y n v ω) ω with hXdef
  have hXeq : ∀ n, ∀ ω ∈ G n, ∀ v, X n v ω = Y n v ω := fun n ω hω v => by
    simp only [hXdef, indicator_of_mem hω]
  have hXout : ∀ n, ∀ ω, ω ∉ G n → ∀ v, X n v ω = 0 := fun n ω hω v => by
    simp only [hXdef, indicator_of_notMem hω]
  have hXm : ∀ n, ∀ v ∈ Icc a b, Measurable[m] (X n v) := fun n v hv =>
    (hYm n v hv).indicator (hGm n)
  have hXc : ∀ n ω, ContinuousOn (fun v => X n v ω) (Icc a b) := by
    intro n ω
    by_cases hω : ω ∈ G n
    · exact (hYc n ω).congr fun v _ => hXeq n ω hω v
    · exact continuousOn_const.congr fun v _ => hXout n ω hω v
  have hX0 : ∀ n, ∀ v ∈ Icc a b, ∀ ω, 0 ≤ X n v ω := by
    intro n v hv ω
    by_cases hω : ω ∈ G n
    · rw [hXeq n ω hω v]; exact hY0 n ω hω v hv
    · rw [hXout n ω hω v]
  have hXK : ∀ n, ∀ v ∈ Icc a b, ∀ ω, X n v ω ≤ K := by
    intro n v hv ω
    by_cases hω : ω ∈ G n
    · rw [hXeq n ω hω v]; exact hYK n ω hω v hv
    · rw [hXout n ω hω v]; exact hK
  have hXbad : ∀ n, ∀ v ∈ Icc a b, {ω | δ < X n v ω} ⊆ {ω | ω ∈ G n ∧ δ < Y n v ω} := by
    intro n v _ ω hω
    have hω' : δ < X n v ω := hω
    by_cases hG : ω ∈ G n
    · exact ⟨hG, by rwa [hXeq n ω hG v] at hω'⟩
    · rw [hXout n ω hG v] at hω'; exact absurd hω' (not_lt.2 hδ)
  have hXmono : ∀ n, ∀ v ∈ Icc a b, ∀ ω, X n v ω ≤ X (n + 1) v ω := by
    intro n v hv ω
    by_cases hω : ω ∈ G n
    · rw [hXeq n ω hω v, hXeq (n + 1) ω (hGmono n hω) v, hcons n ω hω v hv]
    · rw [hXout n ω hω v]; exact hX0 (n + 1) v hv ω
  set B1 : ℕ → Set Ω := fun n => {ω | t < ∫ v in a..b, X n v ω} with hB1def
  set B2 : ℕ → Set Ω := fun n => {ω | δ < X n b ω} with hB2def
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hTM : ∀ n, MeasurableSet[m] (B1 n) ∧
      μ (B1 n) ≤ ENNReal.ofReal ((b - a) * (δ + K * p) / t) := fun n =>
    tonelli_markov m hm μ hab (hXm n) (hXc n) (hX0 n) (hXK n) hK hδ hp ht
      fun v hv => (measure_mono (hXbad n v hv)).trans (hbad n v hv)
  have hB1mono : Monotone B1 := by
    refine monotone_nat_of_le_succ fun n ω hω => ?_
    have hω' : t < ∫ v in a..b, X n v ω := hω
    show t < ∫ v in a..b, X (n + 1) v ω
    exact hω'.trans_le (intervalIntegral.integral_mono_on hab
      ((hXc n ω).intervalIntegrable_of_Icc hab) ((hXc (n + 1) ω).intervalIntegrable_of_Icc hab)
      fun v hv => hXmono n v hv ω)
  have hB2mono : Monotone B2 := by
    refine monotone_nat_of_le_succ fun n ω hω => ?_
    have hω' : δ < X n b ω := hω
    show δ < X (n + 1) b ω
    exact hω'.trans_le (hXmono n b hbI ω)
  refine ⟨(⋃ n, B1 n) ∪ ⋃ n, B2 n, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun n => (hTM n).1).union
      (MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (hXm n b hbI))
  · refine (measure_union_le _ _).trans ?_
    rw [hB1mono.measure_iUnion, hB2mono.measure_iUnion]
    have h1 : (⨆ n, μ (B1 n)) ≤ ENNReal.ofReal ((b - a) * (δ + K * p) / t) :=
      iSup_le fun n => (hTM n).2
    have h2 : (⨆ n, μ (B2 n)) ≤ ENNReal.ofReal p :=
      iSup_le fun n => (measure_mono (hXbad n b hbI)).trans (hbad n b hbI)
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    have hba : 0 ≤ b - a := by linarith
    rw [ENNReal.ofReal_add (by positivity) hp]
  · intro ω hωB n hG
    have hnB1 : ω ∉ B1 n := fun h => hωB (Or.inl (mem_iUnion.2 ⟨n, h⟩))
    have hnB2 : ω ∉ B2 n := fun h => hωB (Or.inr (mem_iUnion.2 ⟨n, h⟩))
    refine ⟨?_, ?_⟩
    · have hle : (∫ v in a..b, X n v ω) ≤ t := not_lt.1 hnB1
      have e : (∫ v in a..b, Y n v ω) = ∫ v in a..b, X n v ω :=
        intervalIntegral.integral_congr fun v _ => (hXeq n ω hG v).symm
      rw [e]; exact hle
    · have hle : X n b ω ≤ δ := not_lt.1 hnB2
      rwa [hXeq n ω hG b] at hle

end BlockBand.Palm.MomentFlow
