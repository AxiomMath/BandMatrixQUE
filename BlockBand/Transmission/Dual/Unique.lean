module

public import BlockBand.Transmission.Dual.UniqueGlue
public import BlockBand.Transmission.Dual.Conservative

/-!
# Uniqueness in law of the dual deletion process

Proof of the `unique` field of `DualBoundaryLawStatement`, for the class
`IsDualDeletionProcess`: any two realizations, on any filtered probability spaces in `Type`,
from the same ordered interior start, have the same law of the truncated state path `dualState`
(product σ-algebra on `ℝ≥0 → ℕ × (ℕ → ℝ) × (ℕ → ℝ)`; `D₀ > 0`, every finite `p`).

* `map_dualState_step`: `DualUniqueAt D₀ (p − 1) → DualUniqueAt D₀ p` for `p ≥ 1`.
* `dualUniqueAt_zero`, `dualUniqueAt`: induction over the level from a random start.
* `unique_holds`: normalization (`exists_normalized`) turns each realization into an
  `IsDualFrom` realization with a deterministic start, without changing the law of `dualState`.
* `dualBoundaryLaw_of_exists`: the whole `DualBoundaryLawStatement` follows from its `exists_`
  field (`unique_holds`, `conservative_holds`).

Main inputs: uniqueness for stopped martingale problems
(`stoppedMartingaleProblemUniquenessPosDef_holds`) and the martingale-problem converse
`isMPSolutionOn_of_test`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

variable {D0 : ℝ} {p : ℕ}

/-- The padded state as a function of the truncated state. -/
def padS (p : ℕ) (s : DualState) : Fin (p + p) → ℝ := padState p s.1 s.2.1 s.2.2

theorem measurable_padS : Measurable (padS p) :=
  measurable_padState_uncurry.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk
    measurable_fst))

theorem IsDualFrom.measurable_dualState {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℝ≥0 → Ω → ℕ}
    {X Y : ℝ≥0 → Ω → ℕ → ℝ} (h : IsDualFrom P 𝓖 D0 p N X Y) : Measurable (dualState N X Y) :=
  Dual.measurable_dualState (fun t => (h.adapted t).1.mono (𝓖.le t) le_rfl)
    (fun t => (h.adapted t).2.1.mono (𝓖.le t) le_rfl)
    (fun t => (h.adapted t).2.2.mono (𝓖.le t) le_rfl)

theorem padPath_zero_eq {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    padPath p N X Y 0 = padS p ∘ fun ω => dualState N X Y ω 0 := by
  funext ω; simp [padPath, padS, dualState, padState_trunc]

/-- **The level step**: uniqueness at level `p − 1` gives uniqueness at level `p`. -/
theorem map_dualState_step (hD0 : 0 < D0) (hp : 1 ≤ p) (IH : DualUniqueAt D0 (p - 1)) :
    DualUniqueAt D0 p := by
  intro Ω₁ _ P₁ 𝓖₁ N₁ X₁ Y₁ Ω₂ _ P₂ 𝓖₂ N₂ X₂ Y₂ h₁ h₂ h0
  have := h₁.prob
  have := h₂.prob
  have hS₁ := h₁.measurable_dualState
  have hS₂ := h₂.measurable_dualState
  have hV0 : P₁.map (padPath p N₁ X₁ Y₁ 0) = P₂.map (padPath p N₂ X₂ Y₂ 0) := by
    rw [padPath_zero_eq, padPath_zero_eq,
      ← Measure.map_map measurable_padS (show Measurable fun ω => dualState N₁ X₁ Y₁ ω 0 from
        (measurable_pi_apply 0).comp hS₁),
      ← Measure.map_map measurable_padS (show Measurable fun ω => dualState N₂ X₂ Y₂ ω 0 from
        (measurable_pi_apply 0).comp hS₂), h0]
  have hstop := map_stopped_padPath_eq hD0 hp h₁ h₂ hV0
  have hpre : ∀ T, P₁.map (preP p N₁ X₁ Y₁ T) = P₂.map (preP p N₂ X₂ Y₂ T) := by
    intro T
    have hΦ : Measurable fun (v : ℝ≥0 → Fin (p + p) → ℝ) (t : ℝ≥0) => v (min t T) :=
      Measurable.of_eval fun t => measurable_pi_apply _
    have e₁ : preP p N₁ X₁ Y₁ T = (fun (v : ℝ≥0 → Fin (p + p) → ℝ) (t : ℝ≥0) => v (min t T)) ∘
        fun ω t => stoppedProcess (padPath p N₁ X₁ Y₁)
          (exitTimeFrom (flatChamber p) (padPath p N₁ X₁ Y₁)) t ω := by
      funext ω t; exact h₁.preP_eq hp T ω t
    have e₂ : preP p N₂ X₂ Y₂ T = (fun (v : ℝ≥0 → Fin (p + p) → ℝ) (t : ℝ≥0) => v (min t T)) ∘
        fun ω t => stoppedProcess (padPath p N₂ X₂ Y₂)
          (exitTimeFrom (flatChamber p) (padPath p N₂ X₂ Y₂)) t ω := by
      funext ω t; exact h₂.preP_eq hp T ω t
    rw [e₁, e₂, ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable
      (aemeasurable_stopped h₁.measurable_padPath (Eventually.of_forall h₁.continuous_padPath)
        (isOpen_flatChamber p)),
      ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable
      (aemeasurable_stopped h₂.measurable_padPath (Eventually.of_forall h₂.continuous_padPath)
        (isOpen_flatChamber p)), hstop]
  refine map_eq_of_fdd_eq₂' hS₁.aemeasurable hS₂.aemeasurable fun I => ?_
  set T : ℝ≥0 := I.sup id
  have hjoint := map_pre_post_eq hp IH h₁ h₂ T (hpre T)
  have hΓ : ∀ m, Measurable fun z : (ℝ≥0 → Fin (p + p) → ℝ) × (ℝ≥0 → DualState) =>
      I.restrict fun t => glueApprox p T m z t := fun m =>
    Measurable.of_eval fun t => measurable_glueApprox T m t
  have hZW₁ : Measurable fun ω => (preP p N₁ X₁ Y₁ T ω, postS p N₁ X₁ Y₁ T ω) :=
    (h₁.measurable_preP' T).prodMk (h₁.measurable_postS T)
  have hZW₂ : Measurable fun ω => (preP p N₂ X₂ Y₂ T ω, postS p N₂ X₂ Y₂ T ω) :=
    (h₂.measurable_preP' T).prodMk (h₂.measurable_postS T)
  refine map_eq_of_tendsto_ae
    (f₁ := fun m ω => I.restrict fun t => glueApprox p T m (preP p N₁ X₁ Y₁ T ω,
      postS p N₁ X₁ Y₁ T ω) t)
    (f₂ := fun m ω => I.restrict fun t => glueApprox p T m (preP p N₂ X₂ Y₂ T ω,
      postS p N₂ X₂ Y₂ T ω) t)
    (fun m => ((hΓ m).comp hZW₁).aemeasurable) (fun m => ((hΓ m).comp hZW₂).aemeasurable)
    ?_ ?_ fun m => ?_
  · exact Eventually.of_forall fun ω => tendsto_pi_nhds.2 fun t =>
      h₁.tendsto_glueApprox hp ω (Finset.le_sup (f := id) t.2)
  · exact Eventually.of_forall fun ω => tendsto_pi_nhds.2 fun t =>
      h₂.tendsto_glueApprox hp ω (Finset.le_sup (f := id) t.2)
  · have e₁ : (fun ω => I.restrict fun t => glueApprox p T m (preP p N₁ X₁ Y₁ T ω,
        postS p N₁ X₁ Y₁ T ω) t) = (fun z => I.restrict fun t => glueApprox p T m z t) ∘
          fun ω => (preP p N₁ X₁ Y₁ T ω, postS p N₁ X₁ Y₁ T ω) := rfl
    have e₂ : (fun ω => I.restrict fun t => glueApprox p T m (preP p N₂ X₂ Y₂ T ω,
        postS p N₂ X₂ Y₂ T ω) t) = (fun z => I.restrict fun t => glueApprox p T m z t) ∘
          fun ω => (preP p N₂ X₂ Y₂ T ω, postS p N₂ X₂ Y₂ T ω) := rfl
    rw [e₁, e₂, ← Measure.map_map (hΓ m) hZW₁, ← Measure.map_map (hΓ m) hZW₂, hjoint]

/-- The base case: at level `0` the truncated state is the empty state. -/
theorem dualUniqueAt_zero (D0 : ℝ) : DualUniqueAt D0 0 := by
  intro Ω₁ _ P₁ 𝓖₁ N₁ X₁ Y₁ Ω₂ _ P₂ 𝓖₂ N₂ X₂ Y₂ h₁ h₂ _
  have := h₁.prob
  have := h₂.prob
  have hc : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℝ≥0 → Ω → ℕ}
      {X Y : ℝ≥0 → Ω → ℕ → ℝ}, IsDualFrom P 𝓖 D0 0 N X Y →
      dualState N X Y = fun _ _ => ((0, 0, 0) : DualState) := by
    intro Ω _ P 𝓖 N X Y h
    funext ω t
    have hN : N t ω = 0 := Nat.le_zero.1 (h.level_le t ω)
    simp [dualState, hN, truncCoord_zero]
  rw [hc h₁, hc h₂, Measure.map_const, Measure.map_const, measure_univ, measure_univ]

/-- **Uniqueness in law from a random start, at every level.** -/
theorem dualUniqueAt (hD0 : 0 < D0) : ∀ p, DualUniqueAt D0 p
  | 0 => dualUniqueAt_zero D0
  | p + 1 => map_dualState_step hD0 (by omega) (by simpa using dualUniqueAt hD0 p)

/-- **The `unique` field of `DualBoundaryLawStatement`**, with exactly the field type. -/
theorem unique_holds : ∀ D0 : ℝ, 0 < D0 → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
    ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (P₁ : Measure Ω₁)
      (N₁ : ℝ≥0 → Ω₁ → ℕ) (X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ)
      (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (P₂ : Measure Ω₂)
      (N₂ : ℝ≥0 → Ω₂ → ℕ) (X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ),
      IsDualDeletionProcess P₁ 𝓖₁ D0 x y N₁ X₁ Y₁ →
      IsDualDeletionProcess P₂ 𝓖₂ D0 x y N₂ X₂ Y₂ →
      P₁.map (dualState N₁ X₁ Y₁) = P₂.map (dualState N₂ X₂ Y₂) := by
  intro D0 hD0 p x y hxy Ω₁ m₁ 𝓖₁ P₁ N₁ X₁ Y₁ Ω₂ m₂ 𝓖₂ P₂ N₂ X₂ Y₂ h₁ h₂
  obtain ⟨N₁', X₁', Y₁', hc₁, hpath₁, hst₁, hae₁⟩ := exists_normalized hxy h₁
  obtain ⟨N₂', X₂', Y₂', hc₂, hpath₂, hst₂, hae₂⟩ := exists_normalized hxy h₂
  have hfrom : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℝ≥0 → Ω → ℕ}
      {X Y : ℝ≥0 → Ω → ℕ → ℝ}, IsDualDeletionProcess P 𝓖 D0 x y N X Y →
      (∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) →
      (∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) →
      IsDualFrom P 𝓖 D0 p N X Y := fun hc hpath hst =>
    { prob := hc.prob
      adapted := hc.adapted
      start := Eventually.of_forall fun ω => (hst ω).1
      bound := fun ω => (hst ω).1.le
      paths := hpath
      martingale := hc.martingale }
  have h0 : ∀ {Ω : Type} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ},
      (∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) →
      (fun ω => dualState N X Y ω 0) =
        fun _ => ((p, truncCoord p (extendFin x), truncCoord p (extendFin y)) : DualState) := by
    intro Ω N X Y hst
    funext ω
    simp only [dualState, (hst ω).1]
    congr 2 <;> funext i <;> unfold truncCoord <;> split_ifs with hi
    · rw [(hst ω).2 ⟨i, hi⟩ |>.1]; simp [extendFin, hi]
    · rfl
    · rw [(hst ω).2 ⟨i, hi⟩ |>.2]; simp [extendFin, hi]
    · rfl
  have := hc₁.prob
  have := hc₂.prob
  rw [← map_dualState_congr hae₁, ← map_dualState_congr hae₂]
  exact dualUniqueAt hD0 p Ω₁ P₁ _ N₁' X₁' Y₁' Ω₂ P₂ _ N₂' X₂' Y₂' (hfrom hc₁ hpath₁ hst₁)
    (hfrom hc₂ hpath₂ hst₂) (by rw [h0 hst₁, h0 hst₂, Measure.map_const, Measure.map_const,
      measure_univ, measure_univ])

/-- **Reduction to existence**: `unique` and `conservative` are proved, so
`DualBoundaryLawStatement` follows from its `exists_` field. -/
theorem dualBoundaryLaw_of_exists
    (hex : ∀ D0 : ℝ, 0 < D0 → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
      HasDualDeletionProcess D0 x y) : DualBoundaryLawStatement :=
  ⟨hex, unique_holds, conservative_holds⟩

example (S : DualBoundaryLawStatement) : DualBoundaryLawStatement :=
  ⟨S.exists_, unique_holds, conservative_holds⟩

end BlockBand.Transmission.Dual
