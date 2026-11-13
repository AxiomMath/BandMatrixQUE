module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# The entrance at non-atom cutoffs `h`

The retention `{t_k > h²}` of `initialGram` is discontinuous at `t_k = h²`, so the limit passage
of (b3) identifies the entrance only at cutoffs `h` where no coordinate of the entrance sequence
has an atom at `h²`. For a finite measure `ρ` on sequences these cutoffs are all but countably
many (`countable_atomCutoffs`), so they are frequent as `h ↓ 0` together with any eventual
property (`frequently_nonAtom`). This is what the frequent-`h` form of the target buys.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Set

/-- Cutoffs `h` at which some coordinate of the sequence law `ρ` has an atom at `h²`. -/
def atomCutoffs (ρ : Measure (ℕ → ℝ)) : Set ℝ := {h | ∃ k, ρ {t | t k = h ^ 2} ≠ 0}

/-- **Atom cutoffs are countable.** -/
theorem countable_atomCutoffs (ρ : Measure (ℕ → ℝ)) [IsFiniteMeasure ρ] :
    (atomCutoffs ρ).Countable := by
  have hA : ∀ k : ℕ, {x : ℝ | 0 < ρ {t | t k = x}}.Countable := fun k =>
    Measure.countable_meas_level_set_pos (measurable_pi_apply k)
  have hsub : atomCutoffs ρ ⊆ ⋃ k : ℕ, ((fun x => Real.sqrt x) '' {x | 0 < ρ {t | t k = x}} ∪
      (fun x => -Real.sqrt x) '' {x | 0 < ρ {t | t k = x}}) := by
    rintro h ⟨k, hk⟩
    refine mem_iUnion.2 ⟨k, ?_⟩
    have hpos : 0 < ρ {t | t k = h ^ 2} := pos_iff_ne_zero.2 hk
    rcases le_total 0 h with h0 | h0
    · exact Or.inl ⟨h ^ 2, hpos, Real.sqrt_sq h0⟩
    · refine Or.inr ⟨h ^ 2, hpos, ?_⟩
      have : Real.sqrt (h ^ 2) = -h := by
        rw [← neg_sq]; exact Real.sqrt_sq (neg_nonneg.2 h0)
      simp only [this, neg_neg]
  exact (countable_iUnion fun k => ((hA k).image _).union ((hA k).image _)).mono hsub

/-- **Non-atom cutoffs are frequent as `h ↓ 0`**, jointly with any property that holds eventually
as `h ↓ 0`. -/
theorem frequently_nonAtom (ρ : Measure (ℕ → ℝ)) [IsFiniteMeasure ρ] {P : ℝ → Prop}
    (hP : ∀ᶠ h in 𝓝[>] (0 : ℝ), P h) :
    ∃ᶠ h in 𝓝[>] (0 : ℝ), P h ∧ ∀ k, ρ {t | t k = h ^ 2} = 0 := by
  intro hne
  have hS : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ atomCutoffs ρ := by
    filter_upwards [hne, hP] with h h1 h2
    by_contra hc
    exact h1 ⟨h2, fun k => by
      by_contra hk
      exact hc ⟨k, hk⟩⟩
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hS
  have h0 : volume (Ioo (0 : ℝ) ε) = 0 :=
    ((countable_atomCutoffs ρ).mono hsub).measure_zero volume
  rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h0
  exact absurd h0 (not_le.2 hε)

end BlockBand.SourceProcess.PhysApprox.B3
