module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The restarted filtration `𝓖_{(a+u)+}` and dyadic times above `a`

* `dyU k x = (⌊2ᵏ x⌋ + 1)/2ᵏ`: dyadic times strictly above `x`, at most `x + 2⁻ᵏ`.
* `shiftFiltration 𝓖 a ha`: `A ∈ 𝓗_u` iff `A ∩ {a + u < t} ∈ 𝓖_t` for every `t`. It is a
  right-continuous filtration and contains `𝓖₀`.
* `stronglyMeasurable_limUnder_shift`: for `𝓖`-adapted `Y k`, the limit (`limUnder`) of
  `Y k (dyU k a + u)` is `𝓗_u`-measurable. No path regularity is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

/-!
### Dyadic times above `x`
-/

/-- The index `⌊2ᵏ x⌋ + 1`. -/
def dyIdx (k : ℕ) (x : ℝ≥0) : ℕ := ⌊x * 2 ^ k⌋₊ + 1

/-- The dyadic time `(⌊2ᵏ x⌋ + 1)/2ᵏ`. -/
def dyU (k : ℕ) (x : ℝ≥0) : ℝ≥0 := (dyIdx k x : ℝ≥0) / 2 ^ k

theorem dyU_eq (k : ℕ) (x : ℝ≥0) : dyU k x = (dyIdx k x : ℝ≥0) / 2 ^ k := rfl

theorem lt_dyU (k : ℕ) (x : ℝ≥0) : x < dyU k x := by
  rw [dyU, lt_div_iff₀ (pow_pos two_pos k), dyIdx, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

theorem dyU_le (k : ℕ) (x : ℝ≥0) : dyU k x ≤ x + (1 / 2) ^ k := by
  have h2 : (0 : ℝ≥0) < 2 ^ k := pow_pos two_pos k
  rw [dyU, div_le_iff₀ h2, dyIdx, Nat.cast_add, Nat.cast_one, add_mul, one_div, inv_pow,
    inv_mul_cancel₀ h2.ne']
  exact add_le_add (Nat.floor_le zero_le) le_rfl

theorem dyU_le_add_one (k : ℕ) (x : ℝ≥0) : dyU k x ≤ x + 1 :=
  (dyU_le k x).trans (add_le_add le_rfl (pow_le_one₀ zero_le (by norm_num)))

theorem tendsto_dyU (x : ℝ≥0) : Tendsto (fun k => dyU k x) atTop (𝓝 x) := by
  have h : Tendsto (fun k : ℕ => x + (1 / 2 : ℝ≥0) ^ k) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 / 2) (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun k => (lt_dyU k x).le) (fun k => dyU_le k x)

/-!
### The restarted filtration
-/

variable {Ω : Type*} {m : MeasurableSpace Ω} (𝓖 : Filtration ℝ≥0 m) (a : Ω → ℝ≥0)

theorem measurableSet_shiftSet {ha : Measurable[𝓖 0] a} (u t : ℝ≥0) :
    MeasurableSet[𝓖 t] {ω | a ω + u < t} :=
  𝓖.mono zero_le _ (measurableSet_lt (ha.add_const u) measurable_const)

/-- The σ-algebra `𝓖_{(a+u)+}`. -/
@[instance_reducible] def shiftSigma (ha : Measurable[𝓖 0] a) (u : ℝ≥0) : MeasurableSpace Ω where
  MeasurableSet' A := ∀ t, MeasurableSet[𝓖 t] (A ∩ {ω | a ω + u < t})
  measurableSet_empty t := by simp
  measurableSet_compl A hA t := by
    have e : Aᶜ ∩ {ω | a ω + u < t} = {ω | a ω + u < t} \ (A ∩ {ω | a ω + u < t}) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq]; tauto
    rw [e]
    exact (measurableSet_shiftSet 𝓖 a (ha := ha) u t).diff (hA t)
  measurableSet_iUnion f hf t := by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => hf i t

/-- **The restarted filtration** `𝓗_u = 𝓖_{(a+u)+}`. -/
def shiftFiltration (ha : Measurable[𝓖 0] a) : Filtration ℝ≥0 m where
  seq u := shiftSigma 𝓖 a ha u
  mono' u v huv A hA t := by
    have e : A ∩ {ω | a ω + v < t} = (A ∩ {ω | a ω + u < t}) ∩ {ω | a ω + v < t} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨⟨h.1, lt_of_le_of_lt (add_le_add le_rfl huv) h.2⟩, h.2⟩,
        fun h => ⟨h.1.1, h.2⟩⟩
    show MeasurableSet[𝓖 t] _
    rw [e]
    exact (hA t).inter (measurableSet_shiftSet 𝓖 a (ha := ha) v t)
  le' u A hA := by
    have e : A = ⋃ n : ℕ, A ∩ {ω | a ω + u < n} := by
      ext ω
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨_, h, (exists_nat_gt (a ω + u)).choose_spec⟩, fun ⟨_, h, _⟩ => h⟩
    rw [e]
    exact MeasurableSet.iUnion fun n => 𝓖.le n _ (hA n)

variable {𝓖 a} {ha : Measurable[𝓖 0] a}

theorem measurableSet_shift_iff {u : ℝ≥0} {A : Set Ω} :
    MeasurableSet[shiftFiltration 𝓖 a ha u] A ↔
      ∀ t, MeasurableSet[𝓖 t] (A ∩ {ω | a ω + u < t}) := Iff.rfl

theorem zero_le_shift (u : ℝ≥0) : 𝓖 0 ≤ shiftFiltration 𝓖 a ha u := fun _ hA t =>
  (𝓖.mono zero_le _ hA).inter (measurableSet_shiftSet 𝓖 a (ha := ha) u t)

instance : (shiftFiltration 𝓖 a ha).IsRightContinuous := by
  refine ⟨fun u A hA => ?_⟩
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf] at hA
  intro t
  have e : A ∩ {ω | a ω + u < t} =
      ⋃ n : ℕ, A ∩ {ω | a ω + (u + 1 / ((n : ℝ≥0) + 1)) < t} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hA', h⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt h)
      refine ⟨n, hA', ?_⟩
      rw [← add_assoc]
      exact lt_tsub_iff_left.1 hn
    · rintro ⟨n, hA', h⟩
      exact ⟨hA', lt_of_le_of_lt (by rw [← add_assoc]; exact le_self_add) h⟩
  rw [e]
  refine MeasurableSet.iUnion fun n => ?_
  have h := (MeasurableSpace.measurableSet_iInf.1 (hA (u + 1 / ((n : ℝ≥0) + 1))))
    (lt_add_of_pos_right u (by positivity))
  exact h t

/-!
### Limits along the dyadic times are `𝓗_u`-measurable
-/

section Lim

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A function of a countable `m'`-measurable index is `m'`-measurable. -/
theorem stronglyMeasurable_comp_nat {m' : MeasurableSpace Ω} {n : Ω → ℕ} (hn : Measurable[m'] n)
    {h : ℕ → Ω → E} (hh : ∀ i, StronglyMeasurable[m'] (h i)) :
    StronglyMeasurable[m'] fun ω => h (n ω) ω := by
  have hm : Measurable fun p : Ω × ℕ => h p.2 p.1 :=
    measurable_from_prod_countable_left (fun i => (hh i).measurable)
  exact (hm.comp (measurable_id.prodMk hn)).stronglyMeasurable

omit [CompleteSpace E] in
theorem stronglyMeasurable_dyShift {m' : MeasurableSpace Ω} (ha' : Measurable[m'] a)
    {Y : ℝ≥0 → Ω → E} (k : ℕ) (u t : ℝ≥0)
    (hY : ∀ s, s ≤ t → StronglyMeasurable[m'] (Y s)) :
    StronglyMeasurable[m'] fun ω => if dyU k (a ω) + u ≤ t then Y (dyU k (a ω) + u) ω else 0 := by
  have hn : Measurable[m'] fun ω => dyIdx k (a ω) := by
    exact ((((measurable_id.mul_const _).nat_floor).add_const 1)).comp ha'
  refine stronglyMeasurable_comp_nat (h := fun i ω =>
    if (i : ℝ≥0) / 2 ^ k + u ≤ t then Y ((i : ℝ≥0) / 2 ^ k + u) ω else 0) hn fun i => ?_
  by_cases hi : (i : ℝ≥0) / 2 ^ k + u ≤ t
  · simp only [hi, ↓reduceIte]
    exact hY _ hi
  · simp only [hi, ↓reduceIte]
    exact stronglyMeasurable_const

/-- **The dyadic limit is `𝓗_u`-measurable.** -/
theorem stronglyMeasurable_limUnder_shift {Y : ℕ → ℝ≥0 → Ω → E}
    (hY : ∀ k t, StronglyMeasurable[𝓖 t] (Y k t)) (u : ℝ≥0) :
    StronglyMeasurable[shiftFiltration 𝓖 a ha u]
      (fun ω => limUnder atTop fun k => Y k (dyU k (a ω) + u) ω) := by
  refine (measurable_iff_comap_le.2 fun A hA => ?_).stronglyMeasurable
  obtain ⟨B, hB, rfl⟩ := hA
  intro t
  set g : ℕ → Ω → E := fun k ω =>
    if dyU k (a ω) + u ≤ t then Y k (dyU k (a ω) + u) ω else 0
  have hg : ∀ k, StronglyMeasurable[𝓖 t] (g k) := fun k =>
    stronglyMeasurable_dyShift ((ha.mono (𝓖.mono zero_le) le_rfl)) k u t
      fun s hs => (hY k s).mono (𝓖.mono hs)
  have hlim : StronglyMeasurable[𝓖 t] fun ω => limUnder atTop fun k => g k ω :=
    @StronglyMeasurable.limUnder ℕ Ω E (𝓖 t) _ _ atTop _ g _ _ hg
  have e : (fun ω => limUnder atTop fun k => Y k (dyU k (a ω) + u) ω) ⁻¹' B ∩
      {ω | a ω + u < t} = (fun ω => limUnder atTop fun k => g k ω) ⁻¹' B ∩
      {ω | a ω + u < t} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    refine and_congr_left fun hω => ?_
    have hev : (fun k => g k ω) =ᶠ[atTop] fun k => Y k (dyU k (a ω) + u) ω := by
      have h1 : Tendsto (fun k => dyU k (a ω) + u) atTop (𝓝 (a ω + u)) :=
        (tendsto_dyU (a ω)).add_const u
      filter_upwards [h1.eventually (eventually_le_nhds hω)] with k hk
      simp only [g, hk, ↓reduceIte]
    rw [limUnder, limUnder, Filter.map_congr hev]
  rw [e]
  exact (hlim.measurable hB).inter (measurableSet_shiftSet 𝓖 a (ha := ha) u t)

end Lim

end BlockBand.SourceProcess.BornRestart
