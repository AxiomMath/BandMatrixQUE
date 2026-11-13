module

public import BlockBand.SourceProcess.BornUnique.SegmentProof
public import BlockBand.SourceProcess.BornUnique.Concat
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankStepBounds

/-!
# Deterministic facts about born Gram paths

* `toGramReal_add`, `toGramReal_sub`, `toGramReal_zero`: the real coordinates are additive;
  `norm_toGramReal_birthSum_le`: `‖toGramReal (birthSum j b t)‖ ≤ jumpBound j`.
* `birthSum_eventually_eq`, `birthSum_eq_of_no_birth`: the jump sum is right-continuous and
  constant on birth-free intervals.
* `integrableOn_path`: `s ↦ φ (g s₊)` is integrable on every bounded interval (`φ` continuous).
* `exists_bound_of_continuous`: continuous functions are bounded on real-coordinate balls.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F]

omit [DecidableEq c] in
theorem toGramReal_add (x y : GramState c) : toGramReal (x + y) = toGramReal x + toGramReal y := by
  funext i
  simp only [toGramReal, Pi.add_apply, gramEntry, reIm]
  split_ifs <;> simp

omit [DecidableEq c] in
theorem toGramReal_zero : toGramReal (0 : GramState c) = 0 := by
  funext i
  simp only [toGramReal, Pi.zero_apply, gramEntry, reIm]
  split_ifs <;> simp

omit [DecidableEq c] in
theorem toGramReal_sub (x y : GramState c) : toGramReal (x - y) = toGramReal x - toGramReal y := by
  have h := toGramReal_add (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- A bound for all jump sums. -/
def jumpBound (j : F → GramState c) : ℝ := ∑ f, ‖toGramReal (j f)‖

omit [DecidableEq c] in
theorem norm_toGramReal_birthSum_le (j : F → GramState c) (b : F → ℝ) (t : ℝ) :
    ‖toGramReal (birthSum j b t)‖ ≤ jumpBound j := by
  unfold birthSum jumpBound
  have hadd : ∀ s : Finset F, toGramReal (∑ f ∈ s, if b f ≤ t then j f else 0) =
      ∑ f ∈ s, toGramReal (if b f ≤ t then j f else 0) := fun s => by
    induction s using Finset.cons_induction with
    | empty => simp [toGramReal_zero]
    | cons f s hf ih => rw [Finset.sum_cons, Finset.sum_cons, toGramReal_add, ih]
  rw [hadd]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  split_ifs
  · exact le_rfl
  · simp [toGramReal_zero]

omit [DecidableEq c] in
theorem jumpBound_nonneg (j : F → GramState c) : 0 ≤ jumpBound j :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-!
### Jump sums in time
-/

omit [Fintype c] [DecidableEq c] in
/-- `birthSum` is right-continuous: eventually constant to the right. -/
theorem birthSum_eventually_eq (j : F → GramState c) (b : F → ℝ) (t : ℝ) :
    ∀ᶠ t' in 𝓝[≥] t, birthSum j b t' = birthSum j b t := by
  have h : ∀ f, ∀ᶠ t' in 𝓝[≥] t, (b f ≤ t' ↔ b f ≤ t) := fun f => by
    by_cases hf : b f ≤ t
    · filter_upwards [self_mem_nhdsWithin] with t' ht'
      exact ⟨fun _ => hf, fun _ => hf.trans ht'⟩
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (not_le.1 hf))] with t' ht'
      exact ⟨fun h => absurd h (not_le.2 ht'), fun h => absurd h hf⟩
  filter_upwards [eventually_all.2 h] with t' ht'
  unfold birthSum
  exact Finset.sum_congr rfl fun f _ => if_congr (ht' f) rfl rfl

omit [Fintype c] [DecidableEq c] in
/-- `birthSum` is constant on a birth-free interval. -/
theorem birthSum_eq_of_no_birth (j : F → GramState c) (b : F → ℝ) {s t : ℝ} (hst : s ≤ t)
    (h : ∀ f, b f ≤ s ∨ t < b f) : birthSum j b t = birthSum j b s := by
  unfold birthSum
  refine Finset.sum_congr rfl fun f _ => if_congr ?_ rfl rfl
  rcases h f with h1 | h1
  · exact ⟨fun _ => h1, fun _ => h1.trans hst⟩
  · exact ⟨fun h2 => absurd h2 (not_le.2 h1), fun h2 => absurd (h2.trans hst) (not_le.2 h1)⟩

omit [DecidableEq c] in
theorem measurable_birthSum_time (j : F → GramState c) (b : F → ℝ) :
    Measurable fun s : ℝ => birthSum j b (s.toNNReal : ℝ) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  unfold birthSum
  refine Finset.measurable_sum _ fun f _ => ?_
  exact Measurable.ite (measurableSet_le measurable_const
    (measurable_coe_nnreal_real.comp measurable_real_toNNReal)) measurable_const measurable_const

/-!
### Bounds and integrability along born paths
-/

/-- Continuous functions of the Gram state are bounded on real-coordinate balls. -/
theorem exists_bound_of_continuous {E : Type*} [SeminormedAddCommGroup E]
    {φ : GramState c → E} (hφ : Continuous φ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x : GramState c, ‖toGramReal x‖ ≤ R → ‖φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin (gramDim c) → ℝ) R).exists_bound_of_continuousOn
    (hφ.comp continuous_fromGramReal').continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC (toGramReal x) (mem_closedBall_zero_iff.2 hx)
  rw [Function.comp_apply, fromGramReal_toGramReal] at this
  exact this.trans (le_max_left _ _)

omit [DecidableEq c] in
/-- A born path is bounded on `[0, T]`. -/
theorem exists_path_bound {j : F → GramState c} {g : ℝ≥0 → GramState c} {b : F → ℝ}
    (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) (T : ℝ≥0) :
    ∃ R, ∀ s ≤ T, ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    (continuous_toGramReal.comp hc).continuousOn
  exact ⟨R, fun s hs => hR s ⟨zero_le, hs⟩⟩

omit [DecidableEq c] in
theorem norm_toGramReal_path_le {j : F → GramState c} {g : ℝ≥0 → GramState c} {b : F → ℝ}
    {s : ℝ≥0} {R : ℝ} (h : ‖toGramReal (g s - birthSum j b (s : ℝ))‖ ≤ R) :
    ‖toGramReal (g s)‖ ≤ R + jumpBound j := by
  have e : g s = (g s - birthSum j b (s : ℝ)) + birthSum j b (s : ℝ) := by abel
  rw [e, toGramReal_add]
  exact (norm_add_le _ _).trans (add_le_add h (norm_toGramReal_birthSum_le j b _))

/-- **Integrability along a born path** on every bounded interval. -/
theorem integrableOn_path {j : F → GramState c} {g : ℝ≥0 → GramState c} {b : F → ℝ}
    (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) {φ : GramState c → ℂ}
    (hφ : Continuous φ) (A B : ℝ) : IntegrableOn (fun s : ℝ => φ (g s.toNNReal)) (Icc A B) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  have : MeasurableAdd₂ (GramState c) := ContinuousAdd.measurableMul₂
  obtain ⟨R, hR⟩ := exists_path_bound hc B.toNNReal
  obtain ⟨C, -, hC⟩ := exists_bound_of_continuous hφ (R + jumpBound j)
  have hm : Measurable fun s : ℝ => g s.toNNReal := by
    have e : (fun s : ℝ => g s.toNNReal) = fun s : ℝ =>
        (g s.toNNReal - birthSum j b (s.toNNReal : ℝ)) + birthSum j b (s.toNNReal : ℝ) := by
      funext s; abel
    rw [e]
    exact ((hc.comp continuous_real_toNNReal).measurable).add (measurable_birthSum_time j b)
  refine Measure.integrableOn_of_bounded (M := C) (by simp [Real.volume_Icc])
    (hφ.measurable.comp hm).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => hC _ ?_)
  exact norm_toGramReal_path_le (hR _ (Real.toNNReal_le_toNNReal hs.2))

theorem intervalIntegrable_path {j : F → GramState c} {g : ℝ≥0 → GramState c} {b : F → ℝ}
    (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) {φ : GramState c → ℂ}
    (hφ : Continuous φ) (A B : ℝ) :
    IntervalIntegrable (fun s : ℝ => φ (g s.toNNReal)) volume A B :=
  (integrableOn_path hc hφ (min A B) (max A B)).intervalIntegrable

/-- The primitive `u ↦ ∫_{(0,u]} φ (g s)` is continuous. -/
theorem continuous_pathIntegral {j : F → GramState c} {g : ℝ≥0 → GramState c} {b : F → ℝ}
    (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) {φ : GramState c → ℂ}
    (hφ : Continuous φ) :
    Continuous fun u : ℝ≥0 => ∫ s in Ioc (0 : ℝ) u, φ (g s.toNNReal) := by
  have := (intervalIntegral.continuous_primitive (intervalIntegrable_path hc hφ) 0).comp
    NNReal.continuous_coe
  refine this.congr fun u => ?_
  simp only [Function.comp]
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg u)]

/-- `∫_{(0,u]} φ(g(a+s)) = ∫_{(0,a+u]} φ(g) - ∫_{(0,a]} φ(g)`. -/
theorem pathIntegral_shift {j : F → GramState c} {g : ℝ≥0 → GramState c} {b : F → ℝ}
    (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) {φ : GramState c → ℂ}
    (hφ : Continuous φ) (a u : ℝ≥0) :
    ∫ s in Ioc (0 : ℝ) u, φ (g (a + s.toNNReal)) =
      (∫ s in Ioc (0 : ℝ) (a + u : ℝ≥0), φ (g s.toNNReal)) -
        ∫ s in Ioc (0 : ℝ) a, φ (g s.toNNReal) := by
  have hi := intervalIntegrable_path hc hφ
  rw [← intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
    ← intervalIntegral.integral_of_le (NNReal.coe_nonneg _)]
  have e : ∫ s in (0 : ℝ)..u, φ (g (a + s.toNNReal)) =
      ∫ s in (0 : ℝ)..u, φ (g ((a : ℝ) + s).toNNReal) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIcc_of_le (NNReal.coe_nonneg u)] at hs; exact hs.1
    congr 2
    rw [Real.toNNReal_add a.coe_nonneg hs0, Real.toNNReal_coe]
  rw [e, intervalIntegral.integral_comp_add_left (fun r => φ (g r.toNNReal)) (a : ℝ), add_zero,
    NNReal.coe_add]
  exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals (hi _ _) (hi _ _))

end BlockBand.SourceProcess.BornRestart
