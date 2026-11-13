module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Data.Rat.Cast.Order

/-!
# Relative localization: raw-filtration hitting times of closed sets

For a process `X : ℝ≥0 → Ω → E` in a pseudo-metric space with Borel-measurable open sets,
adapted to an arbitrary filtration `𝓖` (no usual conditions) and continuous for **every**
sample, and a closed set `K`, the first entrance time
`hitTime X K ω = ⨅ {t | X t ω ∈ K}` (`⊤` if never) is a `𝓖`-stopping time
(`isStoppingTime_hitTime`). The proof writes `{τ ≤ t}` as
`⋂ₙ ⋃_{q ∈ (ℚ ∩ [0,t]) ∪ {t}} {infDist(X_q, K) < 1/(n+1)}` (compactness of `[0,t]`).
Also: `hitTime_le_iff` (the infimum is attained) and `notMem_of_lt_hitTime` (before the hitting time
the process stays outside `K`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory Set Metric Filter Topology
open scoped NNReal

variable {Ω E : Type*}

/-- First entrance time of `K` (`⊤` if `K` is never reached). -/
def hitTime (X : ℝ≥0 → Ω → E) (K : Set E) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : X t ω ∈ K), (t : WithTop ℝ≥0)

theorem hitTime_le_of_mem {X : ℝ≥0 → Ω → E} {K : Set E} {ω : Ω} {r : ℝ≥0} (hr : X r ω ∈ K) :
    hitTime X K ω ≤ r :=
  iInf₂_le (f := fun (t : ℝ≥0) (_ : X t ω ∈ K) => (t : WithTop ℝ≥0)) r hr

/-- The infimum is attained: `τ ≤ t ↔ ∃ r ≤ t, X_r ∈ K`. -/
theorem hitTime_le_iff [PseudoMetricSpace E] {X : ℝ≥0 → Ω → E} {K : Set E} {ω : Ω}
    (hc : Continuous fun t => X t ω) (hK : IsClosed K) (t : ℝ≥0) :
    hitTime X K ω ≤ t ↔ ∃ r ≤ t, X r ω ∈ K := by
  constructor
  · intro h
    set H : Set ℝ≥0 := {r | X r ω ∈ K} with hH
    rcases H.eq_empty_or_nonempty with he | hne
    · exfalso
      have : hitTime X K ω = ⊤ := by
        unfold hitTime
        refine iInf₂_eq_top.mpr fun r hr => ?_
        exact absurd (show r ∈ H from hr) (by rw [he]; exact Set.notMem_empty r)
      rw [this] at h
      exact absurd h (not_le.mpr (WithTop.coe_lt_top t))
    · have hHc : IsClosed H := hK.preimage hc
      have hbdd : BddBelow H := ⟨0, fun x _ => zero_le (a := x)⟩
      have heq : hitTime X K ω = ((sInf H : ℝ≥0) : WithTop ℝ≥0) := by
        rw [WithTop.coe_sInf' hne hbdd, sInf_image]
        rfl
      rw [heq, WithTop.coe_le_coe] at h
      exact ⟨sInf H, h, hHc.csInf_mem hne hbdd⟩
  · rintro ⟨r, hrt, hr⟩
    exact (hitTime_le_of_mem hr).trans (WithTop.coe_le_coe.mpr hrt)

/-- Strictly before the hitting time the process is outside `K`. -/
theorem notMem_of_lt_hitTime {X : ℝ≥0 → Ω → E} {K : Set E} {ω : Ω} {r : ℝ≥0}
    (hr : (r : WithTop ℝ≥0) < hitTime X K ω) : X r ω ∉ K := fun h =>
  absurd (hitTime_le_of_mem h) (not_le.mpr hr)

/-- Pointwise countable description of `{τ ≤ t}` for nonempty closed `K`. -/
theorem hitTime_le_iff_countable [PseudoMetricSpace E] {X : ℝ≥0 → Ω → E} {K : Set E} {ω : Ω}
    (hc : Continuous fun t => X t ω) (hK : IsClosed K) (hKne : K.Nonempty) (t : ℝ≥0) :
    hitTime X K ω ≤ t ↔ ∀ n : ℕ, (infDist (X t ω) K < 1 / ((n : ℝ) + 1) ∨
      ∃ q : ℚ, (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t ∧
        infDist (X (Real.toNNReal q) ω) K < 1 / ((n : ℝ) + 1)) := by
  rw [hitTime_le_iff hc hK]
  set f : ℝ≥0 → ℝ := fun s => infDist (X s ω) K with hf
  have hfc : Continuous f := (continuous_infDist_pt K).comp hc
  constructor
  · rintro ⟨r, hrt, hr⟩ n
    have hfr : f r = 0 := infDist_zero_of_mem hr
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rcases hrt.lt_or_eq with hlt | heq
    · right
      obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.mp hfc r _ hε
      have hlt' : (r : ℝ) < min ((r : ℝ) + δ) (t : ℝ) := lt_min (by linarith) (by exact_mod_cast hlt)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
      have hq0 : (0 : ℝ) ≤ q := le_trans r.2 hq1.le
      refine ⟨q, hq0, (hq2.trans_le (min_le_right _ _)).le, ?_⟩
      have hd : dist (Real.toNNReal q) r < δ := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_of_pos (by linarith)]
        linarith [min_le_left ((r : ℝ) + δ) (t : ℝ)]
      have := hδf _ hd
      rw [Real.dist_eq, hfr, sub_zero, abs_of_nonneg infDist_nonneg] at this
      exact this
    · left
      rw [← heq]
      change f r < _
      rw [hfr]; exact hε
  · intro h
    obtain ⟨r, hr, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_isMinOn
      ⟨0, ⟨le_rfl, zero_le (a := t)⟩⟩ hfc.continuousOn
    refine ⟨r, hr.2, ?_⟩
    have hle : ∀ n : ℕ, f r < 1 / ((n : ℝ) + 1) := by
      intro n
      rcases h n with h1 | ⟨q, hq0, hqt, hq⟩
      · exact lt_of_le_of_lt (hmin ⟨zero_le (a := t), le_rfl⟩) h1
      · refine lt_of_le_of_lt (hmin ⟨zero_le (a := Real.toNNReal q), ?_⟩) hq
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hqt
    have hf0 : f r = 0 := by
      refine le_antisymm ?_ infDist_nonneg
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [hle n]
    exact (hK.mem_iff_infDist_zero hKne).mpr hf0

/-- The first entrance time of a closed set by a process continuous for every
sample and adapted to an arbitrary (raw) filtration is a stopping time. -/
theorem isStoppingTime_hitTime [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (X : ℝ≥0 → Ω → E)
    (hX : ∀ t, Measurable[𝓖 t] (X t)) (hc : ∀ ω, Continuous fun t => X t ω)
    {K : Set E} (hK : IsClosed K) : IsStoppingTime 𝓖 (hitTime X K) := by
  intro t
  rcases K.eq_empty_or_nonempty with he | hKne
  · have : {ω | hitTime X K ω ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hitTime_le_iff (hc ω) hK]
      rintro ⟨r, _, hr⟩
      rw [he] at hr; exact hr
    rw [this]; exact @MeasurableSet.empty _ (𝓖 t)
  · have hset : {ω | hitTime X K ω ≤ (t : WithTop ℝ≥0)} =
        ⋂ n : ℕ, ({ω | infDist (X t ω) K < 1 / ((n : ℝ) + 1)} ∪
          ⋃ q : ℚ, {ω | (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t ∧
            infDist (X (Real.toNNReal q) ω) K < 1 / ((n : ℝ) + 1)}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_iUnion]
      exact hitTime_le_iff_countable (hc ω) hK hKne t
    rw [hset]
    refine MeasurableSet.iInter fun n => (MeasurableSet.union ?_ (MeasurableSet.iUnion fun q => ?_))
    · exact ((continuous_infDist_pt K).measurable.comp (hX t)) measurableSet_Iio
    · by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t
      · have hle : Real.toNNReal q ≤ t := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq.1]; exact hq.2
        have hm : Measurable[𝓖 t] (X (Real.toNNReal q)) :=
          (hX (Real.toNNReal q)).mono (𝓖.mono hle) le_rfl
        have : {ω | (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t ∧
            infDist (X (Real.toNNReal q) ω) K < 1 / ((n : ℝ) + 1)} =
            {ω | infDist (X (Real.toNNReal q) ω) K < 1 / ((n : ℝ) + 1)} := by
          ext ω; simp [hq.1, hq.2]
        rw [this]
        exact ((continuous_infDist_pt K).measurable.comp hm) measurableSet_Iio
      · have : {ω | (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t ∧
            infDist (X (Real.toNNReal q) ω) K < 1 / ((n : ℝ) + 1)} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hq ⟨h.1, h.2.1⟩
        rw [this]; exact @MeasurableSet.empty _ (𝓖 t)

end BlockBand.Palm.RelativeLocalization
