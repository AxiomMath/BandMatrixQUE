module

public import BlockBand.SourceProcess.BornUnique.NextTime
public import BlockBand.SourceProcess.SourceProcessLaw.ModelValue

/-!
# Concatenation over births: `BornGramLawUnique` from `BornSegmentStep`

Iterating the segment step `BornSegmentStep` over the finitely many births in a time interval
shows that two born Gram solutions with the same law of birth times and initial state have the
same one-time laws (`bornGramLawUnique_of_segmentStep`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

section Meas

variable {c F : Type} [Fintype c] [Fintype F]

theorem gramState_secondCountable : SecondCountableTopology (GramState c) := by
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  infer_instance

theorem measurable_birthSum (j : F → GramState c) (t : ℝ) :
    Measurable fun x : F → ℝ => birthSum j x t := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  unfold birthSum
  refine Finset.measurable_sum _ fun f _ => ?_
  exact Measurable.ite (measurableSet_le (measurable_pi_apply f) measurable_const)
    measurable_const measurable_const

/-- The map `(x, g) ↦ (x, g - J_x(t))` is measurable. -/
theorem measurable_subJump (j : F → GramState c) (t : ℝ) :
    Measurable fun p : (F → ℝ) × GramState c => (p.1, p.2 - birthSum j p.1 t) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  exact measurable_fst.prodMk (measurable_snd.sub ((measurable_birthSum j t).comp measurable_fst))

/-- The map `(x, g) ↦ g + J_x(t)` is measurable. -/
theorem measurable_addJump (j : F → GramState c) (t : ℝ) :
    Measurable fun p : (F → ℝ) × GramState c => p.2 + birthSum j p.1 t := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  exact measurable_snd.add ((measurable_birthSum j t).comp measurable_fst)

end Meas

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ}
  {j : F → GramState c}
  {Ω : Type} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω}
  {β : Ω → F → ℝ} {G : ℝ≥0 → Ω → GramState c}
  {Ω' : Type} {m' : MeasurableSpace Ω'} {𝓖' : Filtration ℝ≥0 m'} {Q' : Measure Ω'}
  {β' : Ω' → F → ℝ} {G' : ℝ≥0 → Ω' → GramState c}

/-- **Iterated segment steps** from any `α ≤ t` with at most `n` births in `(α, t)` up to `t`. -/
theorem segment_iter (hS : BornSegmentStep) (hD0 : 0 < D0) (hD : IsSignature D)
    (hQ : IsProbabilityMeasure Q) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    (hQ' : IsProbabilityMeasure Q') (hβ' : Measurable[𝓖' 0] β')
    (hG' : IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (β' ω) (t : ℝ)) G')
    (t : ℝ≥0) (n : ℕ) : ∀ α : (F → ℝ) → ℝ≥0, Measurable α → (∀ x, α x ≤ t) →
      (∀ x, midCount t α x ≤ n) →
      Q.map (fun ω => (β ω, bornCont j β G (α (β ω)) ω)) =
        Q'.map (fun ω => (β' ω, bornCont j β' G' (α (β' ω)) ω)) →
      Q.map (fun ω => (β ω, bornCont j β G t ω)) =
        Q'.map (fun ω => (β' ω, bornCont j β' G' t ω)) := by
  induction n with
  | zero =>
    intro α hα hle hc h0
    refine hS c F D0 D hD0 hD j α (fun _ => t) hα measurable_const hle (fun x f => ?_)
      Ω m 𝓖 Q β G hQ hβ hG Ω' m' 𝓖' Q' β' G' hQ' hβ' hG' h0
    rcases le_or_gt (x f) (α x) with h | h
    · exact Or.inl h
    · refine Or.inr (not_lt.1 fun h' => ?_)
      have hpos : 0 < midCount t α x :=
        Finset.card_pos.2 ⟨f, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h, h'⟩⟩
      have := hc x
      omega
  | succ n ih =>
    intro α hα hle hc h0
    have h1 := hS c F D0 D hD0 hD j α (nextTime t α) hα (measurable_nextTime t hα)
      (fun x => le_nextTime (hle x)) (no_birth_between t α) Ω m 𝓖 Q β G hQ hβ hG
      Ω' m' 𝓖' Q' β' G' hQ' hβ' hG' h0
    exact ih (nextTime t α) (measurable_nextTime t hα) (nextTime_le t α)
      (fun x => midCount_nextTime_le (hle x) (hc x)) h1

theorem measurable_G {G : ℝ≥0 → Ω → GramState c} {J : ℝ≥0 → Ω → GramState c}
    (hG : IsBornGramSolution Q 𝓖 D0 D J G) (t : ℝ≥0) : Measurable (G t) :=
  measurable_of_stronglyMeasurable_gram (𝓖.le t) (hG.adapted t)

/-- **`BornGramLawUnique` from `BornSegmentStep`.** -/
theorem bornGramLawUnique_of_segmentStep (hS : BornSegmentStep) : BornGramLawUnique := by
  intro c F _ _ _ D0 D hD0 hD j Ω m 𝓖 Q β G hQ hβ hG Ω' m' 𝓖' Q' β' G' hQ' hβ' hG' h0 t
  have hb : Measurable β := hβ.mono (𝓖.le 0) le_rfl
  have hb' : Measurable β' := hβ'.mono (𝓖'.le 0) le_rfl
  have hstart : Q.map (fun ω => (β ω, bornCont j β G ((fun _ => (0 : ℝ≥0)) (β ω)) ω)) =
      Q'.map (fun ω => (β' ω, bornCont j β' G' ((fun _ => (0 : ℝ≥0)) (β' ω)) ω)) := by
    have e : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (β₁ : Ω₁ → F → ℝ) (G₁ : ℝ≥0 → Ω₁ → GramState c),
        (fun ω => (β₁ ω, bornCont j β₁ G₁ ((fun _ => (0 : ℝ≥0)) (β₁ ω)) ω)) =
          (fun p : (F → ℝ) × GramState c => (p.1, p.2 - birthSum j p.1 ((0 : ℝ≥0) : ℝ))) ∘
            fun ω => (β₁ ω, G₁ 0 ω) := fun _ _ => rfl
    rw [e, e, ← Measure.map_map (measurable_subJump j _) (hb.prodMk (measurable_G hG 0)),
      ← Measure.map_map (measurable_subJump j _) (hb'.prodMk (measurable_G hG' 0)), h0]
  have hend := segment_iter hS hD0 hD hQ hβ hG hQ' hβ' hG' t (Fintype.card F) (fun _ => 0)
    measurable_const (fun x => by positivity) (fun _ => Finset.card_le_univ _) hstart
  have e : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (β₁ : Ω₁ → F → ℝ) (G₁ : ℝ≥0 → Ω₁ → GramState c),
      G₁ t = (fun p : (F → ℝ) × GramState c => p.2 + birthSum j p.1 (t : ℝ)) ∘
        fun ω => (β₁ ω, bornCont j β₁ G₁ t ω) := by
    intro _ _ β₁ G₁
    funext ω
    simp [bornCont]
  have hc : ∀ {Ω₁ : Type} [MeasurableSpace Ω₁] (β₁ : Ω₁ → F → ℝ) (G₁ : ℝ≥0 → Ω₁ → GramState c),
      Measurable β₁ → Measurable (G₁ t) → Measurable fun ω => (β₁ ω, bornCont j β₁ G₁ t ω) := by
    intro _ _ β₁ G₁ h1 h2
    have := (measurable_subJump j (t : ℝ)).comp (h1.prodMk h2)
    exact this
  rw [e β G, e β' G', ← Measure.map_map (measurable_addJump j _) (hc β G hb (measurable_G hG t)),
    ← Measure.map_map (measurable_addJump j _) (hc β' G' hb' (measurable_G hG' t)), hend]

end BlockBand.SourceProcess.BornUnique
