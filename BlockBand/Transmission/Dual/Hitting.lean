module

public import BlockBand.Transmission.Dual.Statement
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Hitting times of right-continuous, lower semicontinuous processes

* `ceilDyad m t = ⌈t 2^m⌉/2^m ↓ t`, and `measurable_of_tendsto_nhdsGE`: a right-continuous
  `ℝ≥0 → ℝ` function is measurable;
* `continuous_setIntegral_Ioc`: `t ↦ ∫_{(0,t]} G(u) du` is continuous for bounded
  right-continuous `G`;
* `hitLe V c` (first time `V ≤ c`): `lt_hitLe` (before it `V > c`), `hitLe_attained`
  (`V ≤ c` at it, by right-continuity), and `isStoppingTime_hitLe` when every path is
  right-continuous and lower semicontinuous (only downward jumps).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

/-!
## Dyadic approximation from the right
-/

/-- `⌈t 2^m⌉ / 2^m`. -/
def ceilDyad (m : ℕ) (t : ℝ≥0) : ℝ≥0 := (⌈t * 2 ^ m⌉₊ : ℝ≥0) / 2 ^ m

theorem le_ceilDyad (m : ℕ) (t : ℝ≥0) : t ≤ ceilDyad m t := by
  rw [ceilDyad, le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem ceilDyad_lt (m : ℕ) (t : ℝ≥0) : ceilDyad m t < t + (1 / 2) ^ m := by
  rw [ceilDyad, div_lt_iff₀ (by positivity), add_mul, one_div, inv_pow,
    inv_mul_cancel₀ (by positivity)]
  exact Nat.ceil_lt_add_one (zero_le)

theorem tendsto_ceilDyad (t : ℝ≥0) : Tendsto (fun m => ceilDyad m t) atTop (𝓝[≥] t) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => le_ceilDyad m t⟩
  have h0 : Tendsto (fun m : ℕ => t + (1 / 2 : ℝ≥0) ^ m) atTop (𝓝 (t + 0)) :=
    tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [add_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun m => le_ceilDyad m t) (fun m => (ceilDyad_lt m t).le)

/-- A right-continuous function `ℝ≥0 → ℝ` is measurable. -/
theorem measurable_of_tendsto_nhdsGE {G : ℝ≥0 → ℝ} (hG : ∀ t, Tendsto G (𝓝[≥] t) (𝓝 (G t))) :
    Measurable G := by
  refine measurable_of_tendsto_metrizable (f := fun m t => G (ceilDyad m t)) (fun m => ?_)
    (tendsto_pi_nhds.2 fun t => (hG t).comp (tendsto_ceilDyad t))
  have : (fun t => G (ceilDyad m t)) =
      (fun k : ℕ => G ((k : ℝ≥0) / 2 ^ m)) ∘ fun t : ℝ≥0 => ⌈t * 2 ^ m⌉₊ := rfl
  rw [this]
  exact measurable_from_nat.comp (Nat.measurable_ceil.comp (measurable_id.mul_const _))

/-- `t ↦ ∫_{(0,t]} G(u) du` is continuous for a bounded right-continuous `G`. -/
theorem continuous_setIntegral_Ioc {G : ℝ≥0 → ℝ} (hG : ∀ t, Tendsto G (𝓝[≥] t) (𝓝 (G t)))
    {C : ℝ} (hC : ∀ t, ‖G t‖ ≤ C) :
    Continuous fun t : ℝ≥0 => ∫ u in Ioc (0 : ℝ) t, G u.toNNReal := by
  have hm : Measurable fun u : ℝ => G u.toNNReal :=
    (measurable_of_tendsto_nhdsGE hG).comp measurable_real_toNNReal
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => G u.toNNReal) volume a b := by
    intro a b
    refine ⟨?_, ?_⟩ <;>
    · refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
      exact Eventually.of_forall fun u => hC _
  have hc := intervalIntegral.continuous_primitive hint 0
  have : (fun t : ℝ≥0 => ∫ u in Ioc (0 : ℝ) t, G u.toNNReal) =
      (fun b : ℝ => ∫ u in (0 : ℝ)..b, G u.toNNReal) ∘ (fun t : ℝ≥0 => (t : ℝ)) := by
    funext t
    simp [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  rw [this]
  exact hc.comp NNReal.continuous_coe

/-!
## Hitting times
-/

variable {Ω : Type*}

/-- First time `V ≤ c` (`⊤` if never). -/
def hitLe (V : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : V t ω ≤ c), (t : WithTop ℝ≥0)

theorem lt_hitLe {V : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω} {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) < hitLe V c ω) : c < V u ω := by
  by_contra h
  have h2 : hitLe V c ω ≤ u := by
    unfold hitLe; exact iInf₂_le (f := fun t (_ : V t ω ≤ c) => (t : WithTop ℝ≥0)) u
      (not_lt.1 h)
  exact absurd h2 (not_le.2 hu)

theorem hitLe_attained {V : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω}
    (hR : ∀ t, Tendsto (fun u => V u ω) (𝓝[≥] t) (𝓝 (V t ω))) {s : ℝ≥0}
    (hs : hitLe V c ω = s) : V s ω ≤ c := by
  by_contra h'
  have h : c < V s ω := not_le.1 h'
  have hev : ∀ᶠ u in 𝓝[≥] s, c < V u ω := (hR s).eventually (lt_mem_nhds h)
  obtain ⟨b, hb, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  have hb' : (b : WithTop ℝ≥0) ≤ hitLe V c ω := by
    refine le_iInf₂ fun u hu => ?_
    rw [WithTop.coe_le_coe]
    by_contra hub'
    have hub : u < b := not_le.1 hub'
    rcases lt_or_ge u s with hus | hsu
    · have h1 : (u : WithTop ℝ≥0) < hitLe V c ω := by
        rw [hs]; exact WithTop.coe_lt_coe.2 hus
      have := lt_hitLe h1
      linarith
    · have h2 : c < V u ω := hsub ⟨hsu, hub⟩
      linarith
  rw [hs] at hb'
  exact absurd (WithTop.coe_le_coe.1 hb') (not_le.2 hb)

theorem hitLe_le_iff {V : ℝ≥0 → Ω → ℝ} {c : ℝ} {ω : Ω}
    (hR : ∀ t, Tendsto (fun u => V u ω) (𝓝[≥] t) (𝓝 (V t ω))) (t : ℝ≥0) :
    hitLe V c ω ≤ t ↔ ∃ u ≤ t, V u ω ≤ c := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top h)
    exact ⟨s, WithTop.coe_le_coe.1 (hs ▸ h), hitLe_attained hR hs.symm⟩
  · rintro ⟨u, hut, hu⟩
    have h2 : hitLe V c ω ≤ u := by unfold hitLe; exact iInf₂_le u hu
    exact h2.trans (WithTop.coe_le_coe.2 hut)

/-- **Hitting times of `{V ≤ c}` are stopping times** when every path is right-continuous and
lower semicontinuous (a raw filtration suffices). -/
theorem isStoppingTime_hitLe [m : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 m}
    {V : ℝ≥0 → Ω → ℝ} (hV : ∀ t, Measurable[𝓕 t] (V t))
    (hR : ∀ ω t, Tendsto (fun u => V u ω) (𝓝[≥] t) (𝓝 (V t ω)))
    (hL : ∀ ω, LowerSemicontinuous fun u => V u ω) (c : ℝ) :
    IsStoppingTime 𝓕 (hitLe V c) := by
  intro t
  have hset : {ω | hitLe V c ω ≤ t} = ⋂ k : ℕ, ({ω | V t ω < c + 1 / (k + 1)} ∪
      ⋃ (j : ℕ) (m : ℕ) (_ : (j : ℝ≥0) / 2 ^ m ≤ t),
        {ω | V ((j : ℝ≥0) / 2 ^ m) ω < c + 1 / (k + 1)}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_iInter, mem_union, mem_iUnion, exists_prop]
    rw [hitLe_le_iff (hR ω)]
    constructor
    · rintro ⟨u, hut, hu⟩ k
      have hε : c < c + 1 / ((k : ℝ) + 1) := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      rcases eq_or_lt_of_le hut with h | h
      · left; rw [← h]; linarith
      · right
        have hev := (tendsto_ceilDyad u).eventually ((hR ω u).eventually (gt_mem_nhds
          (lt_of_le_of_lt hu hε)))
        have hev2 : ∀ᶠ m in atTop, ceilDyad m u ≤ t :=
          ((tendsto_ceilDyad u).mono_right nhdsWithin_le_nhds).eventually
            (eventually_le_nhds h)
        obtain ⟨m, hm1, hm2⟩ := (hev.and hev2).exists
        exact ⟨⌈u * 2 ^ m⌉₊, m, hm2, hm1⟩
    · intro h
      by_contra hne
      push Not at hne
      have hlsc : LowerSemicontinuousOn (fun u => V u ω) (Icc 0 t) := (hL ω).lowerSemicontinuousOn _
      obtain ⟨a, ha, hmin⟩ := hlsc.exists_isMinOn
        (⟨0, ⟨le_rfl, zero_le⟩⟩ : (Icc (0 : ℝ≥0) t).Nonempty) isCompact_Icc
      have hca : c < V a ω := hne a ha.2
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hca)
      rcases h k with h1 | ⟨j, m, hjm, h2⟩
      · have := isMinOn_iff.1 hmin t ⟨zero_le, le_rfl⟩
        linarith
      · have := isMinOn_iff.1 hmin _ ⟨zero_le, hjm⟩
        linarith
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.union ?_ ?_
  · exact measurableSet_lt (hV t) measurable_const
  · refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun m => MeasurableSet.iUnion
      fun hjm => ?_
    exact 𝓕.mono hjm _ (measurableSet_lt (hV _) measurable_const)

/-- Lower semicontinuity from one-sided limits: right-continuous, and the left limit (if any)
dominates the value. -/
theorem lowerSemicontinuousAt_of_one_sided {G : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hR : Tendsto G (𝓝[≥] t) (𝓝 (G t))) {L : ℝ} (hL : Tendsto G (𝓝[<] t) (𝓝 L))
    (hLt : G t ≤ L) : LowerSemicontinuousAt G t := by
  intro y hy
  rw [← nhdsLT_sup_nhdsGE, eventually_sup]
  exact ⟨hL.eventually (lt_mem_nhds (lt_of_lt_of_le hy hLt)), hR.eventually (lt_mem_nhds hy)⟩

end BlockBand.Transmission.Dual
