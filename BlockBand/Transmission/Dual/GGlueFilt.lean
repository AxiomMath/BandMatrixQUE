module

public import BlockBand.Transmission.Dual.GShift

/-!
# The glued filtration and its martingales

Generic setting for the restart on the restart space `(Ω, 𝓖, P)` (the space of `DelFrom (q−1)`):
a filtration `𝓕` with `𝓕 t ≤ 𝓖 0` for all `t` (the stage-1 filtration pulled back by `π'`,
which is `𝓖₀`-measurable), an `𝓕`-stopping time `ρ` (the first deletion, `⊤` if none) and a
`𝓖₀`-measurable `θ : Ω → ℝ≥0` equal to `ρ` where `ρ < ⊤`.
* **`glueFilt`**: `𝓗 t = {A | A ∩ {t < ρ} ∈ 𝓕 t ∧ A ∩ {ρ ≤ t} ∈ 𝓖_{(t−θ)⁺}}`, a filtration,
  with `le_glueFilt : 𝓕 t ≤ 𝓗 t` and
  **`measurable_glueFilt_ite`** (adaptedness of a process defined by stage 1 before `ρ` and by a
  `𝓖_{(t−θ)⁺}`-measurable variable from `ρ` on).
* **`martingale_glue_pre`**: an `𝓕`-martingale stopped at `ρ` is an `𝓗`-martingale.
* **`martingale_glue_post`**: for a right-continuous bounded `𝓖`-martingale `M'` with `M'_0 = 0`,
  `t ↦ 1{ρ < ⊤} M'_{(t−θ)⁺}` is an `𝓗`-martingale (`martingale_shift` on `{ρ ≤ s}`; on
  `{s < ρ}`, a `𝓖₀` set, both sides vanish because `M'_0 = 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {𝓖 𝓕 : Filtration ℝ≥0 m}
  {ρ : Ω → WithTop ℝ≥0} {θ : Ω → ℝ≥0}

theorem le_shiftFilt (hθ : Measurable[𝓖 0] θ) (t : ℝ≥0) : 𝓖 0 ≤ shiftFilt hθ t := fun A hA =>
  ⟨le_iSup (fun t => (𝓖 t : MeasurableSpace Ω)) 0 A hA, fun i =>
    (𝓖.mono zero_le A hA).inter ((isStoppingTime_shiftTime hθ t).measurableSet_le i)⟩

/-- Sets of the glued filtration at time `t`. -/
def GlueSet (𝓕 : Filtration ℝ≥0 m) (ρ : Ω → WithTop ℝ≥0) (hθ : Measurable[𝓖 0] θ) (t : ℝ≥0)
    (A : Set Ω) : Prop :=
  MeasurableSet[𝓕 t] (A ∩ {ω | (t : WithTop ℝ≥0) < ρ ω}) ∧
    MeasurableSet[shiftFilt hθ t] (A ∩ {ω | ρ ω ≤ t})

variable (h𝓕 : ∀ t, 𝓕 t ≤ 𝓖 0) (hρ : IsStoppingTime 𝓕 ρ) (hθ : Measurable[𝓖 0] θ)

include h𝓕 hρ in
theorem measurableSet_le_shiftFilt (t u : ℝ≥0) :
    MeasurableSet[shiftFilt hθ u] {ω | ρ ω ≤ t} :=
  le_shiftFilt hθ u _ (h𝓕 t _ (hρ.measurableSet_le t))

set_option warn.classDefReducibility false in
/-- The σ-algebra of the glued filtration at time `t`. -/
def glueSigma (t : ℝ≥0) : MeasurableSpace Ω where
  MeasurableSet' := GlueSet 𝓕 ρ hθ t
  measurableSet_empty := by simp [GlueSet]
  measurableSet_compl A hA := by
    refine ⟨?_, ?_⟩
    · have e : Aᶜ ∩ {ω | (t : WithTop ℝ≥0) < ρ ω} =
          {ω | (t : WithTop ℝ≥0) < ρ ω} ∩ (A ∩ {ω | (t : WithTop ℝ≥0) < ρ ω})ᶜ := by
        ext; simp; tauto
      rw [e]; exact (hρ.measurableSet_gt t).inter hA.1.compl
    · have e : Aᶜ ∩ {ω | ρ ω ≤ t} = {ω | ρ ω ≤ t} ∩ (A ∩ {ω | ρ ω ≤ t})ᶜ := by
        ext; simp; tauto
      rw [e]; exact (measurableSet_le_shiftFilt h𝓕 hρ hθ t t).inter hA.2.compl
  measurableSet_iUnion A hA := by
    refine ⟨?_, ?_⟩
    · rw [iUnion_inter]; exact MeasurableSet.iUnion fun i => (hA i).1
    · rw [iUnion_inter]; exact MeasurableSet.iUnion fun i => (hA i).2

/-- **The glued filtration.** -/
def glueFilt : Filtration ℝ≥0 m where
  seq := glueSigma h𝓕 hρ hθ
  mono' s t hst A hA := by
    refine ⟨?_, ?_⟩
    · have e : A ∩ {ω | (t : WithTop ℝ≥0) < ρ ω} =
          (A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}) ∩ {ω | (t : WithTop ℝ≥0) < ρ ω} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun h => ⟨⟨h.1, (WithTop.coe_le_coe.2 hst).trans_lt h.2⟩, h.2⟩,
          fun h => ⟨h.1.1, h.2⟩⟩
      rw [e]; exact (𝓕.mono hst _ hA.1).inter (hρ.measurableSet_gt t)
    · have e : A ∩ {ω | ρ ω ≤ t} = (A ∩ {ω | ρ ω ≤ s}) ∪
          ((A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}) ∩ {ω | ρ ω ≤ t}) := by
        ext ω; simp only [mem_inter_iff, mem_union, mem_ofPred_eq]
        constructor
        · rintro ⟨hA, ht⟩
          rcases le_or_gt (ρ ω) s with h | h
          · exact Or.inl ⟨hA, h⟩
          · exact Or.inr ⟨⟨hA, h⟩, ht⟩
        · rintro (⟨hA, h⟩ | ⟨⟨hA, -⟩, h⟩)
          · exact ⟨hA, h.trans (WithTop.coe_le_coe.2 hst)⟩
          · exact ⟨hA, h⟩
      rw [e]
      exact ((shiftFilt hθ).mono hst _ hA.2).union ((le_shiftFilt hθ t _ (h𝓕 s _ hA.1)).inter
        (measurableSet_le_shiftFilt h𝓕 hρ hθ t t))
  le' t A hA := by
    have e : A = (A ∩ {ω | (t : WithTop ℝ≥0) < ρ ω}) ∪ (A ∩ {ω | ρ ω ≤ t}) := by
      ext ω; simp only [mem_inter_iff, mem_union, mem_ofPred_eq]
      constructor
      · intro h; rcases lt_or_ge (t : WithTop ℝ≥0) (ρ ω) with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
      · rintro (h | h) <;> exact h.1
    rw [e]; exact (𝓕.le t _ hA.1).union ((shiftFilt hθ).le t _ hA.2)

theorem measurableSet_glueFilt_iff {t : ℝ≥0} {A : Set Ω} :
    MeasurableSet[glueFilt h𝓕 hρ hθ t] A ↔ GlueSet 𝓕 ρ hθ t A := Iff.rfl

theorem le_glueFilt (t : ℝ≥0) : 𝓕 t ≤ glueFilt h𝓕 hρ hθ t := fun _ hA =>
  ⟨@MeasurableSet.inter Ω (𝓕 t) _ _ hA (hρ.measurableSet_gt t),
    (le_shiftFilt hθ t _ (h𝓕 t _ hA)).inter (measurableSet_le_shiftFilt h𝓕 hρ hθ t t)⟩

theorem shiftSet_glueFilt {t : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[shiftFilt hθ t] A) :
    MeasurableSet[glueFilt h𝓕 hρ hθ t] (A ∩ {ω | ρ ω ≤ t}) := by
  refine ⟨?_, ?_⟩
  · have e : A ∩ {ω | ρ ω ≤ t} ∩ {ω | (t : WithTop ℝ≥0) < ρ ω} = ∅ := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => absurd h.1.2 (not_le.2 h.2)
    rw [e]; exact @MeasurableSet.empty Ω (𝓕 t)
  · rw [inter_assoc, inter_self]
    exact hA.inter (measurableSet_le_shiftFilt h𝓕 hρ hθ t t)

open scoped Classical in
/-- **Adaptedness of a glued variable.** -/
theorem measurable_glueFilt_ite {β : Type*} [MeasurableSpace β] {t : ℝ≥0} {g₁ g₂ : Ω → β}
    (h₁ : Measurable[𝓕 t] g₁) (h₂ : Measurable[shiftFilt hθ t] g₂) :
    Measurable[glueFilt h𝓕 hρ hθ t]
      (fun ω => if (t : WithTop ℝ≥0) < ρ ω then g₁ ω else g₂ ω) := by
  intro B hB
  refine ⟨?_, ?_⟩
  · have e : (fun ω => if (t : WithTop ℝ≥0) < ρ ω then g₁ ω else g₂ ω) ⁻¹' B ∩
        {ω | (t : WithTop ℝ≥0) < ρ ω} = g₁ ⁻¹' B ∩ {ω | (t : WithTop ℝ≥0) < ρ ω} := by
      ext ω; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨h, h'⟩; simp only [h', ↓reduceIte] at h; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; simp only [h', ↓reduceIte, and_true]; exact h
    rw [e]; exact (h₁ hB).inter (hρ.measurableSet_gt t)
  · have e : (fun ω => if (t : WithTop ℝ≥0) < ρ ω then g₁ ω else g₂ ω) ⁻¹' B ∩
        {ω | ρ ω ≤ t} = g₂ ⁻¹' B ∩ {ω | ρ ω ≤ t} := by
      ext ω; simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨h, h'⟩; simp only [not_lt.2 h', ↓reduceIte] at h; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; simp only [not_lt.2 h', ↓reduceIte]; exact ⟨h, h'⟩
    rw [e]; exact (h₂ hB).inter (measurableSet_le_shiftFilt h𝓕 hρ hθ t t)

/-! ## Martingales of the glued filtration -/

omit h𝓕 hρ hθ in
theorem martingale_of_setIntegral {𝓗 : Filtration ℝ≥0 m} {P : Measure Ω} [IsFiniteMeasure P]
    {M : ℝ≥0 → Ω → ℝ} (hadapt : StronglyAdapted 𝓗 M) (hint : ∀ t, Integrable (M t) P)
    (h : ∀ s t, s ≤ t → ∀ A, MeasurableSet[𝓗 s] A →
      ∫ ω in A, M t ω ∂P = ∫ ω in A, M s ω ∂P) : Martingale M 𝓗 P :=
  ⟨hadapt, fun s t hst => (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => (h s t hst A hA).symm)
    (hadapt s).aestronglyMeasurable).symm⟩

variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
include h𝓕 hρ hθ in
theorem setIntegral_split {s : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[glueFilt h𝓕 hρ hθ s] A)
    {g : Ω → ℝ} (hg : Integrable g P) :
    ∫ ω in A, g ω ∂P = ∫ ω in A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}, g ω ∂P +
      ∫ ω in A ∩ {ω | ρ ω ≤ s}, g ω ∂P := by
  have e : A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω} ∪ A ∩ {ω | ρ ω ≤ s} = A := by
    ext ω; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases lt_or_ge (s : WithTop ℝ≥0) (ρ ω) with h' | h'
      exacts [Or.inl ⟨h, h'⟩, Or.inr ⟨h, h'⟩]
  conv_lhs => rw [← e]
  exact setIntegral_union (Set.disjoint_left.2 fun ω h1 h2 => (not_le.2 (show (s : WithTop ℝ≥0) < ρ ω from h1.2))
      (show ρ ω ≤ s from h2.2))
    ((shiftFilt hθ).le s _ hA.2) hg.integrableOn hg.integrableOn

/-- **Stage 1**: an `𝓕`-martingale stopped at `ρ` is a martingale of the glued filtration. -/
theorem martingale_glue_pre {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (hstop : ∀ (s t : ℝ≥0) ω, s ≤ t → ρ ω ≤ s → M t ω = M s ω) :
    Martingale M (glueFilt h𝓕 hρ hθ) P := by
  refine martingale_of_setIntegral (fun t => (hM.1 t).mono (le_glueFilt h𝓕 hρ hθ t))
    hM.integrable fun s t hst A hA => ?_
  rw [setIntegral_split h𝓕 hρ hθ hA (hM.integrable t),
    setIntegral_split h𝓕 hρ hθ hA (hM.integrable s), ← hM.setIntegral_eq hst hA.1]
  congr 1
  exact setIntegral_congr_fun ((shiftFilt hθ).le s _ hA.2) fun ω hω => hstop s t ω hst hω.2

open scoped Classical in
/-- **After the restart**: for a right-continuous bounded `𝓖`-martingale `M` with `M_0 = 0`,
`t ↦ 1{ρ ≤ t} M_{(t−θ)⁺}` is a martingale of the glued filtration. -/
theorem martingale_glue_post {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P)
    (hrc : ∀ ω t, Tendsto (fun s => M s ω) (𝓝[≥] t) (𝓝 (M t ω)))
    (hb : ∀ T : ℝ≥0, ∃ C, ∀ t ≤ T, ∀ ω, |M t ω| ≤ C) (h0 : ∀ ω, M 0 ω = 0) :
    Martingale (fun (t : ℝ≥0) ω => if (t : WithTop ℝ≥0) < ρ ω then 0 else M (t - θ ω) ω)
      (glueFilt h𝓕 hρ hθ) P := by
  have hMs := martingale_shift hM hθ hrc hb
  set G : ℝ≥0 → Ω → ℝ := fun (t : ℝ≥0) ω => if (t : WithTop ℝ≥0) < ρ ω then 0 else M (t - θ ω) ω
  have hGi : ∀ t, G t = {ω | ρ ω ≤ t}.indicator fun ω => M (t - θ ω) ω := fun t => funext fun ω => by
    by_cases h : (t : WithTop ℝ≥0) < ρ ω
    · rw [indicator_of_notMem (show ω ∉ {ω | ρ ω ≤ t} from not_le.2 h)]; simp only [G, h, ↓reduceIte]
    · rw [indicator_of_mem (show ω ∈ {ω | ρ ω ≤ t} from not_lt.1 h)]; simp only [G, h, ↓reduceIte]
  have hGm : ∀ t, Measurable[glueFilt h𝓕 hρ hθ t] (G t) := fun t =>
    measurable_glueFilt_ite h𝓕 hρ hθ measurable_const (hMs.1 t).measurable
  have hGint : ∀ t, Integrable (G t) P := fun t => by
    obtain ⟨C, hC⟩ := hb t
    refine integrable_of_abs_le' (C := C) ((hGm t).mono ((glueFilt h𝓕 hρ hθ).le t) le_rfl)
      fun ω => ?_
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 zero_le ω)
    simp only [G]; split_ifs
    · simpa using hC0
    · exact hC _ tsub_le_self ω
  have hzero : ∀ (u : ℝ≥0) (B : Set Ω), MeasurableSet[𝓖 0] B → ∫ ω in B, M (u - θ ω) ω ∂P = 0 := by
    intro u B hB
    rw [← hMs.setIntegral_eq zero_le (le_shiftFilt hθ 0 _ hB)]
    simp [zero_tsub, h0]
  refine martingale_of_setIntegral (fun t => (hGm t).stronglyMeasurable) hGint
    fun s t hst A hA => ?_
  rw [setIntegral_split h𝓕 hρ hθ hA (hGint t), setIntegral_split h𝓕 hρ hθ hA (hGint s)]
  have hB0 : MeasurableSet[𝓖 0] (A ∩ {ω | (s : WithTop ℝ≥0) < ρ ω}) := h𝓕 s _ hA.1
  have hBm := (𝓖.le 0) _ hB0
  have hle : ∀ u : ℝ≥0, MeasurableSet {ω | ρ ω ≤ u} := fun u =>
    (𝓖.le 0) _ (h𝓕 u _ (hρ.measurableSet_le u))
  congr 1
  · rw [hGi t, hGi s, setIntegral_indicator (hle t), setIntegral_indicator (hle s),
      hzero t _ (hB0.inter (h𝓕 t _ (hρ.measurableSet_le t))),
      hzero s _ (hB0.inter (h𝓕 s _ (hρ.measurableSet_le s)))]
  · have e : ∀ u : ℝ≥0, s ≤ u → EqOn (G u) (fun ω => M (u - θ ω) ω) (A ∩ {ω | ρ ω ≤ s}) :=
      fun u hu ω hω => by
        simp only [G, not_lt.2 (hω.2.trans (WithTop.coe_le_coe.2 hu)), ↓reduceIte]
    have hAm := (shiftFilt hθ).le s _ hA.2
    rw [setIntegral_congr_fun hAm (e t hst), setIntegral_congr_fun hAm (e s le_rfl),
      hMs.setIntegral_eq hst hA.2]

end BlockBand.Transmission.Dual.G
