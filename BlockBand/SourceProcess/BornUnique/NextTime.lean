module

public import BlockBand.SourceProcess.BornUnique.Segment

/-!
# The next birth time before a horizon

`nextTime t α x` is the first birth `x_f` after `α(x)`, capped at `t`, and `midCount t α x` counts
the births strictly between `α(x)` and `t`. Passing from `α` to `nextTime t α` either removes a
birth from `(α(x), t)` or leaves none there, which drives an induction on the number of births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory
open scoped NNReal

variable {F : Type*}

/-- The next birth after `α(x)`, capped at `t`: `min(t, min{x_f : α(x) < x_f})`. -/
def nextTime (t : ℝ≥0) (α : (F → ℝ) → ℝ≥0) (x : F → ℝ) : ℝ≥0 :=
  ⨅ i : Option F, Option.elim i t fun f => if (α x : ℝ) < x f then (x f).toNNReal else t

/-- The number of births strictly between `α(x)` and `t`. -/
def midCount [Fintype F] (t : ℝ≥0) (α : (F → ℝ) → ℝ≥0) (x : F → ℝ) : ℕ :=
  (Finset.univ.filter fun f => (α x : ℝ) < x f ∧ x f < t).card

theorem measurable_nextTime [Fintype F] (t : ℝ≥0) {α : (F → ℝ) → ℝ≥0} (hα : Measurable α) :
    Measurable (nextTime t α) := by
  refine Measurable.iInf fun i => ?_
  rcases i with _ | f
  · exact measurable_const
  · refine Measurable.ite (measurableSet_lt (measurable_coe_nnreal_real.comp hα)
      (measurable_pi_apply f)) ?_ measurable_const
    exact measurable_real_toNNReal.comp (measurable_pi_apply f)

theorem bdd_nextTime (t : ℝ≥0) (α : (F → ℝ) → ℝ≥0) (x : F → ℝ) :
    BddBelow (Set.range fun i : Option F =>
      Option.elim i t fun f => if (α x : ℝ) < x f then (x f).toNNReal else t) :=
  ⟨0, fun y _ => by positivity⟩

theorem nextTime_le (t : ℝ≥0) (α : (F → ℝ) → ℝ≥0) (x : F → ℝ) : nextTime t α x ≤ t :=
  ciInf_le (bdd_nextTime t α x) none

theorem le_nextTime {t : ℝ≥0} {α : (F → ℝ) → ℝ≥0} {x : F → ℝ} (hα : α x ≤ t) :
    α x ≤ nextTime t α x := by
  refine le_ciInf fun i => ?_
  rcases i with _ | f
  · exact hα
  · simp only [Option.elim]
    split_ifs with h
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((α x).2.trans h.le)]
      exact h.le
    · exact hα

theorem nextTime_le_of_lt {t : ℝ≥0} {α : (F → ℝ) → ℝ≥0} {x : F → ℝ} {f : F}
    (h : (α x : ℝ) < x f) : (nextTime t α x : ℝ) ≤ x f := by
  have h1 := ciInf_le (bdd_nextTime t α x) (some f)
  simp only [Option.elim, h, ↓reduceIte] at h1
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ ((α x).2.trans h.le)] at h2

/-- No birth lies strictly between `α(x)` and `nextTime t α x`. -/
theorem no_birth_between (t : ℝ≥0) (α : (F → ℝ) → ℝ≥0) (x : F → ℝ) (f : F) :
    x f ≤ α x ∨ (nextTime t α x : ℝ) ≤ x f := by
  by_cases h : (α x : ℝ) < x f
  · exact Or.inr (nextTime_le_of_lt h)
  · exact Or.inl (not_lt.1 h)

/-- The value of `nextTime` is `t` or a birth time after `α(x)`. -/
theorem nextTime_cases [Finite F] (t : ℝ≥0) (α : (F → ℝ) → ℝ≥0) (x : F → ℝ) :
    nextTime t α x = t ∨ ∃ f, (α x : ℝ) < x f ∧ (nextTime t α x : ℝ) = x f := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i : Option F =>
    Option.elim i t fun f => if (α x : ℝ) < x f then (x f).toNNReal else t)
  rw [← nextTime] at hi
  rcases i with _ | f
  · exact Or.inl hi.symm
  · simp only [Option.elim] at hi
    split_ifs at hi with h
    · refine Or.inr ⟨f, h, ?_⟩
      rw [← hi, Real.coe_toNNReal _ ((α x).2.trans h.le)]
    · exact Or.inl hi.symm

/-- `nextTime` removes at least one birth from `(α(x), t)`, or leaves none there. -/
theorem midCount_nextTime_le [Fintype F] {t : ℝ≥0} {α : (F → ℝ) → ℝ≥0} {x : F → ℝ} (hα : α x ≤ t)
    {n : ℕ} (hn : midCount t α x ≤ n + 1) : midCount t (nextTime t α) x ≤ n := by
  rcases nextTime_cases t α x with h | ⟨f₀, hf₀, he⟩
  · have : midCount t (nextTime t α) x = 0 := by
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun f _ hf => ?_)
      rw [h] at hf
      exact lt_asymm hf.1 hf.2
    omega
  · by_cases ht : (nextTime t α x : ℝ) < t
    · have hsub : (Finset.univ.filter fun f => (nextTime t α x : ℝ) < x f ∧ x f < t) ⊂
          Finset.univ.filter fun f => (α x : ℝ) < x f ∧ x f < t := by
        refine Finset.ssubset_iff_of_subset (fun f hf => ?_) |>.2 ⟨f₀, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
          exact ⟨lt_of_le_of_lt (NNReal.coe_le_coe.2 (le_nextTime hα)) hf.1, hf.2⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hf₀, he ▸ ht⟩
        · simp [he]
      have := Finset.card_lt_card hsub
      unfold midCount at hn ⊢
      omega
    · have : midCount t (nextTime t α) x = 0 := by
        refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun f _ hf => ?_)
        exact ht (hf.1.trans hf.2)
      omega

end BlockBand.SourceProcess.BornUnique
