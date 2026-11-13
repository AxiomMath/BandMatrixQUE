module

public import BlockBand.Transmission.Dual.UniqueGluePre

/-!
# Uniqueness in law: gluing across the first deletion

* `DualUniqueAt D₀ p`: any two `IsDualFrom` realizations at level `p` (spaces in `Type`) with
  the same law of the initial truncated state have the same law of the truncated state path.
* `map_pre_post_eq`: assuming `DualUniqueAt D₀ (p − 1)`, the joint law of
  `(preP, postS)` (pre-deletion stopped padded path, post-deletion truncated path) is determined
  by the law of `preP`. Rectangles `C × D` are split along `E = {σ ≤ T}`; on `E` one conditions
  on `A = {preP ∈ C, σ ≤ T} ∈ 𝓖_{σ ∧ T}` and applies the induction hypothesis to the shifted
  realization `IsDualFrom.shift`, whose initial law `L(unpad(preP_T) | A)` is a function of the
  law of `preP`; off `E` the post path is the constant empty path. Then π–λ
  (`ext_of_generate_finite`).

This is the main input of the induction step, proved in the sibling module:
`map_dualState_step`: `DualUniqueAt D₀ (p − 1) → DualUniqueAt D₀ p` for `p ≥ 1`. The law of
`preP` comes from `map_stopped_padPath_eq`; the finite-dimensional laws of the truncated
state are a.s. limits of measurable functionals of `(preP, postS)` (`tendsto_glueApprox`,
`map_eq_of_tendsto_ae`); then `map_eq_of_fdd_eq₂'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

/-- Uniqueness in law of the truncated state path at level `p`, from a random start. -/
def DualUniqueAt (D0 : ℝ) (p : ℕ) : Prop :=
  ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (P₁ : Measure Ω₁)
    (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)) (N₁ : ℝ≥0 → Ω₁ → ℕ)
    (X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ)
    (Ω₂ : Type) [MeasurableSpace Ω₂] (P₂ : Measure Ω₂)
    (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)) (N₂ : ℝ≥0 → Ω₂ → ℕ)
    (X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ),
    IsDualFrom P₁ 𝓖₁ D0 p N₁ X₁ Y₁ → IsDualFrom P₂ 𝓖₂ D0 p N₂ X₂ Y₂ →
    P₁.map (fun ω => dualState N₁ X₁ Y₁ ω 0) = P₂.map (fun ω => dualState N₂ X₂ Y₂ ω 0) →
    P₁.map (dualState N₁ X₁ Y₁) = P₂.map (dualState N₂ X₂ Y₂)

/-- Conditional laws of functions of `Z` given `{Z ∈ C}` are determined by the law of `Z`. -/
theorem map_cond_comp_eq {Ω₁ Ω₂ α β : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace α] [MeasurableSpace β] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {Z₁ : Ω₁ → α} {Z₂ : Ω₂ → α} (hZ₁ : Measurable Z₁) (hZ₂ : Measurable Z₂)
    (hlaw : P₁.map Z₁ = P₂.map Z₂) {C : Set α} (hC : MeasurableSet C) {g : α → β}
    (hg : Measurable g) : (P₁[|Z₁ ⁻¹' C]).map (g ∘ Z₁) = (P₂[|Z₂ ⁻¹' C]).map (g ∘ Z₂) := by
  ext B hB
  rw [Measure.map_apply (hg.comp hZ₁) hB, Measure.map_apply (hg.comp hZ₂) hB,
    cond_apply (hZ₁ hC), cond_apply (hZ₂ hC),
    show Z₁ ⁻¹' C ∩ (g ∘ Z₁) ⁻¹' B = Z₁ ⁻¹' (C ∩ g ⁻¹' B) from rfl,
    show Z₂ ⁻¹' C ∩ (g ∘ Z₂) ⁻¹' B = Z₂ ⁻¹' (C ∩ g ⁻¹' B) from rfl, ← Measure.map_apply hZ₁ hC,
    ← Measure.map_apply hZ₂ hC, ← Measure.map_apply hZ₁ (hC.inter (hg hB)),
    ← Measure.map_apply hZ₂ (hC.inter (hg hB)), hlaw]

variable {D0 : ℝ} {p : ℕ}

section OneSide

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℝ≥0 → Ω → ℕ}
  {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- Paths that have left the chamber by time `T`. -/
def offSet (p : ℕ) (T : ℝ≥0) : Set (ℝ≥0 → Fin (p + p) → ℝ) := {v | v T ∉ flatChamber p}

theorem measurableSet_offSet (T : ℝ≥0) : MeasurableSet (offSet p T) :=
  (isOpen_flatChamber p).measurableSet.compl.preimage (measurable_pi_apply T)

theorem IsDualFrom.measurable_preP' (h : IsDualFrom P 𝓖 D0 p N X Y) (T : ℝ≥0) :
    Measurable (preP p N X Y T) :=
  (h.measurable_preP T).mono ((postFil h T).le 0) le_rfl

theorem IsDualFrom.measurable_postS (h : IsDualFrom P 𝓖 D0 p N X Y) (T : ℝ≥0) :
    Measurable (postS p N X Y T) :=
  measurable_dualState (fun s => (h.post_adapted T s).1.mono ((postFil h T).le s) le_rfl)
    (fun s => (h.post_adapted T s).2.1.mono ((postFil h T).le s) le_rfl)
    (fun s => (h.post_adapted T s).2.2.mono ((postFil h T).le s) le_rfl)

/-- Splitting a rectangle along `E = {σ ≤ T}`. -/
theorem IsDualFrom.measure_rect (h : IsDualFrom P 𝓖 D0 p N X Y) (hp : 1 ≤ p) (T : ℝ≥0)
    {C : Set (ℝ≥0 → Fin (p + p) → ℝ)} (hC : MeasurableSet C) {D : Set (ℝ≥0 → DualState)}
    (hD : MeasurableSet D) :
    P (preP p N X Y T ⁻¹' C ∩ postS p N X Y T ⁻¹' D) =
      P (preP p N X Y T ⁻¹' (C ∩ offSet p T) ∩ postS p N X Y T ⁻¹' D) +
        D.indicator (fun _ => P (preP p N X Y T ⁻¹' (C \ offSet p T)))
          (fun _ => ((0, 0, 0) : DualState)) := by
  classical
  have hZ := h.measurable_preP' T
  have hW := h.measurable_postS T
  have hoff : ∀ ω, preP p N X Y T ω ∉ offSet p T → postS p N X Y T ω = fun _ => (0, 0, 0) :=
    fun ω hω => postS_of_notMem fun hE => hω ((h.mem_E_iff hp T ω).1 hE)
  have e2 : preP p N X Y T ⁻¹' (C \ offSet p T) ∩ postS p N X Y T ⁻¹' D =
      if (fun _ => ((0, 0, 0) : DualState)) ∈ D then preP p N X Y T ⁻¹' (C \ offSet p T)
      else ∅ := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff]
    split_ifs with hs
    · exact ⟨fun h' => h'.1, fun h' => ⟨h', by rw [hoff ω h'.2]; exact hs⟩⟩
    · simp only [mem_empty_iff_false, iff_false, not_and]
      intro h'; rw [hoff ω h'.2]; exact hs
  have hu : preP p N X Y T ⁻¹' C ∩ postS p N X Y T ⁻¹' D =
      (preP p N X Y T ⁻¹' (C ∩ offSet p T) ∩ postS p N X Y T ⁻¹' D) ∪
        (preP p N X Y T ⁻¹' (C \ offSet p T) ∩ postS p N X Y T ⁻¹' D) := by
    rw [← union_inter_distrib_right, ← preimage_union, inter_union_sdiff]
  rw [hu, measure_union (disjoint_left.2 fun ω h1 h2 => h2.1.2 h1.1.2)
    ((hZ (hC.diff (measurableSet_offSet T))).inter (hW hD)), e2]
  by_cases hs : (fun _ => ((0, 0, 0) : DualState)) ∈ D
  · simp [hs]
  · simp [hs]

end OneSide

/-- **The joint law of the pre- and post-deletion paths** is determined by the law of the
pre-deletion path, given uniqueness at level `p − 1`. -/
theorem map_pre_post_eq (hp : 1 ≤ p) (IH : DualUniqueAt D0 (p - 1))
    {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {N₁ : ℝ≥0 → Ω₁ → ℕ}
    {X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ}
    {Ω₂ : Type} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {N₂ : ℝ≥0 → Ω₂ → ℕ}
    {X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ}
    (h₁ : IsDualFrom P₁ 𝓖₁ D0 p N₁ X₁ Y₁) (h₂ : IsDualFrom P₂ 𝓖₂ D0 p N₂ X₂ Y₂) (T : ℝ≥0)
    (hpre : P₁.map (preP p N₁ X₁ Y₁ T) = P₂.map (preP p N₂ X₂ Y₂ T)) :
    P₁.map (fun ω => (preP p N₁ X₁ Y₁ T ω, postS p N₁ X₁ Y₁ T ω)) =
      P₂.map (fun ω => (preP p N₂ X₂ Y₂ T ω, postS p N₂ X₂ Y₂ T ω)) := by
  have := h₁.prob
  have := h₂.prob
  have hZ₁ := h₁.measurable_preP' T
  have hZ₂ := h₂.measurable_preP' T
  have hW₁ := h₁.measurable_postS T
  have hW₂ := h₂.measurable_postS T
  have hlaw : ∀ {C}, MeasurableSet C → P₁ (preP p N₁ X₁ Y₁ T ⁻¹' C) = P₂ (preP p N₂ X₂ Y₂ T ⁻¹' C) :=
    fun hC => by rw [← Measure.map_apply hZ₁ hC, ← Measure.map_apply hZ₂ hC, hpre]
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by
    rw [Measure.map_apply (hZ₁.prodMk hW₁) MeasurableSet.univ,
      Measure.map_apply (hZ₂.prodMk hW₂) MeasurableSet.univ]; simp)
  rintro _ ⟨C, hC, D, hD, rfl⟩
  simp only [mem_ofPred_eq] at hC hD
  show _ = Measure.map _ P₂ (C ×ˢ D)
  rw [Measure.map_apply (hZ₁.prodMk hW₁) (hC.prod hD), Measure.map_apply (hZ₂.prodMk hW₂)
    (hC.prod hD), mk_preimage_prod, mk_preimage_prod, h₁.measure_rect hp T hC hD,
    h₂.measure_rect hp T hC hD]
  have hCD := hC.diff (measurableSet_offSet (p := p) T)
  simp only [indicator, hlaw hCD]
  congr 1
  -- the part on `E`: condition on `A = {preP ∈ C ∩ offSet}`
  set C' := C ∩ offSet p T
  have hC' : MeasurableSet C' := hC.inter (measurableSet_offSet T)
  set A₁ := preP p N₁ X₁ Y₁ T ⁻¹' C'
  set A₂ := preP p N₂ X₂ Y₂ T ⁻¹' C'
  have hA₁m : MeasurableSet A₁ := hZ₁ hC'
  have hA₂m : MeasurableSet A₂ := hZ₂ hC'
  by_cases hA0 : P₁ A₁ = 0
  · have hA0' : P₂ A₂ = 0 := (hlaw hC').symm.trans hA0
    rw [measure_mono_null inter_subset_left hA0, measure_mono_null inter_subset_left hA0']
  have hA0' : P₂ A₂ ≠ 0 := (hlaw hC') ▸ hA0
  have hAE₁ : A₁ ⊆ {ω | firstDel p N₁ ω ≤ T} := fun ω hω => (h₁.mem_E_iff hp T ω).2 hω.2
  have hAE₂ : A₂ ⊆ {ω | firstDel p N₂ ω ≤ T} := fun ω hω => (h₂.mem_E_iff hp T ω).2 hω.2
  have hs₁ := h₁.shift hp T (h₁.measurable_preP T hC') hAE₁ hA0
  have hs₂ := h₂.shift hp T (h₂.measurable_preP T hC') hAE₂ hA0'
  have hg : Measurable fun v : ℝ≥0 → Fin (p + p) → ℝ => unpad p (v T) :=
    measurable_unpad.comp (measurable_pi_apply T)
  have hinit : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
      {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℝ≥0 → Ω → ℕ}
      {X Y : ℝ≥0 → Ω → ℕ → ℝ}, IsDualFrom P 𝓖 D0 p N X Y →
      (P[|preP p N X Y T ⁻¹' C']).map (fun ω => postS p N X Y T ω 0) =
        (P[|preP p N X Y T ⁻¹' C']).map ((fun v => unpad p (v T)) ∘ preP p N X Y T) := by
    intro Ω _ P 𝓖 N X Y h
    refine Measure.map_congr ?_
    filter_upwards [ae_cond_mem ((h.measurable_preP' T) hC')] with ω hω
    exact h.postS_zero ((h.mem_E_iff hp T ω).2 hω.2)
  have hpost := IH Ω₁ (P₁[|A₁]) (postFil h₁ T) _ _ _ Ω₂ (P₂[|A₂]) (postFil h₂ T) _ _ _ hs₁ hs₂
    (by
      have e1 := hinit h₁
      have e2 := hinit h₂
      simp only [postS] at e1 e2
      rw [e1, e2]
      exact map_cond_comp_eq hZ₁ hZ₂ hpre hC' hg)
  have hD₁ : P₁[|A₁] (postS p N₁ X₁ Y₁ T ⁻¹' D) = P₂[|A₂] (postS p N₂ X₂ Y₂ T ⁻¹' D) := by
    have := congrArg (fun μ : Measure (ℝ≥0 → DualState) => μ D) hpost
    rwa [Measure.map_apply (show Measurable (dualState (postN p N₁ T) (postC p N₁ T X₁)
      (postC p N₁ T Y₁)) from hW₁) hD, Measure.map_apply (show Measurable (dualState
      (postN p N₂ T) (postC p N₂ T X₂) (postC p N₂ T Y₂)) from hW₂) hD] at this
  rw [← cond_mul_eq_inter hA₁m, ← cond_mul_eq_inter hA₂m, hD₁, hlaw hC']

end BlockBand.Transmission.Dual
