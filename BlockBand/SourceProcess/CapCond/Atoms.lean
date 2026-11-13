module

public import BlockBand.SourceProcess.CapCond.Limit

/-!
# Frequent cutoffs without entrance atoms

For a finite measure `ρ` on trace measures, the set of `h > 0` such that some `t_k = seqExtract · k`
has an atom at `h²` is countable. Hence `∃ᶠ h in 𝓝[>] 0`, `h < 1` and no `t_k` has an atom at `h²`
(`frequently_noAtom`), and a frequent property on such `h` is frequent (`frequently_of_noAtom`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapCond

open MeasureTheory Filter Topology
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal

/-- No `t_k` has an atom at `h²`. -/
def NoAtom (ρ : Measure (Measure unitInterval)) (h : ℝ) : Prop :=
  ∀ k : ℕ, ρ {ν | seqExtract ν k = h ^ 2} = 0

theorem countable_atoms (ρ : Measure (Measure unitInterval)) [IsFiniteMeasure ρ] :
    {h : ℝ | 0 < h ∧ ¬ NoAtom ρ h}.Countable := by
  have hC : ∀ k : ℕ, {x : ℝ | 0 < ρ {ν | seqExtract ν k = x}}.Countable := fun k =>
    Measure.countable_meas_level_set_pos ((measurable_pi_apply k).comp measurable_seqExtract)
  refine (Set.countable_iUnion fun k => (hC k).image Real.sqrt).mono ?_
  rintro h ⟨hh, hn⟩
  simp only [NoAtom, not_forall] at hn
  obtain ⟨k, hk⟩ := hn
  refine Set.mem_iUnion.2 ⟨k, h ^ 2, pos_iff_ne_zero.2 hk, Real.sqrt_sq hh.le⟩

/-- **Frequently, `0 < h < 1` and `h²` is not an atom of any `t_k`.** -/
theorem frequently_noAtom (ρ : Measure (Measure unitInterval)) [IsFiniteMeasure ρ] :
    ∃ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < 1 ∧ NoAtom ρ h := by
  rw [frequently_iff]
  intro U hU
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  have hu0 : (0 : ℝ) < min u 1 := lt_min hu one_pos
  by_contra hne
  push Not at hne
  have hsub' : Set.Ioo (0 : ℝ) (min u 1) ⊆ {h : ℝ | 0 < h ∧ ¬ NoAtom ρ h} := by
    intro h hh
    have hU' : h ∈ U := hsub ⟨hh.1, hh.2.trans_le (min_le_left _ _)⟩
    exact ⟨hh.1, fun hA => hne h hU' hh.1 (hh.2.trans_le (min_le_right _ _)) hA⟩
  have h0 := ((countable_atoms ρ).mono hsub').measure_zero volume
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- A property holding on all small non-atomic `h` holds frequently. -/
theorem frequently_of_noAtom (ρ : Measure (Measure unitInterval)) [IsFiniteMeasure ρ]
    {Pr : ℝ → Prop} (hP : ∀ h, 0 < h → h < 1 → NoAtom ρ h → Pr h) :
    ∃ᶠ h in 𝓝[>] (0 : ℝ), Pr h :=
  (frequently_noAtom ρ).mono fun h ⟨h0, h1, hA⟩ => hP h h0 h1 hA

end BlockBand.SourceProcess.CapCond
