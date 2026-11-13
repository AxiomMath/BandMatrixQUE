module

public import BlockBand.SourceProcess.CapLimit.RestrictSol
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction
public import BlockBand.SourceProcess.SourceProcessLaw.Entrance

/-!
# Conditioning a finite source model on an entrance event

Conditioning a model on `A = {seqTraceMeasure tseq ∈ S} ∈ σ(tseq) ⊆ 𝓖₀`
keeps the entrance clauses with the conditioned entrance `entrance[|S]`, keeps `tseq ⫫ τ` and the
law of `τ` (because `A ∈ σ(tseq)`), and keeps every martingale clause (because `A ∈ 𝓖₀`).

* `map_cond_preimage`: `(Q[|F⁻¹S]).map F = (Q.map F)[|S]`;
* `cond_preimage_map`, `indepFun_cond_preimage`: conditioning on a `σ(X)`-event keeps the law
  of an independent `Y` and the independence;
* `isBornGramSolution_cond`: a born solution conditioned on an `𝓖₀`-event;
* `model_cond_of`: the model clauses not involving `G` survive; `G` is supplied separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLimit

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

theorem map_cond_preimage {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (Q : Measure Ω)
    {F : Ω → α} (hF : Measurable F) {S : Set α} (hS : MeasurableSet S) :
    (Q[|F ⁻¹' S]).map F = (Q.map F)[|S] := by
  ext U hU
  rw [Measure.map_apply hF hU, cond_apply (hF hS), cond_apply hS, Measure.map_apply hF hS,
    Measure.map_apply hF (hS.inter hU), Set.preimage_inter]

section Indep

variable {Ω β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
  {Q : Measure Ω} [IsFiniteMeasure Q] {X : Ω → β} {Y : Ω → γ}

theorem cond_preimage_apply (hX : Measurable X) (hXY : IndepFun X Y Q) {T : Set β}
    (hT : MeasurableSet T) (hQ : Q (X ⁻¹' T) ≠ 0) {U : Set γ} (hU : MeasurableSet U) :
    Q[Y ⁻¹' U|X ⁻¹' T] = Q (Y ⁻¹' U) := by
  rw [cond_apply (hX hT), (indepFun_iff_measure_inter_preimage_eq_mul.1 hXY) T U hT hU,
    ← mul_assoc, ENNReal.inv_mul_cancel hQ (measure_ne_top _ _), one_mul]

theorem cond_preimage_map (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y Q)
    {T : Set β} (hT : MeasurableSet T) (hQ : Q (X ⁻¹' T) ≠ 0) :
    (Q[|X ⁻¹' T]).map Y = Q.map Y := by
  ext U hU
  rw [Measure.map_apply hY hU, Measure.map_apply hY hU, cond_preimage_apply hX hXY hT hQ hU]

theorem indepFun_cond_preimage (hX : Measurable X) (hXY : IndepFun X Y Q) {T : Set β}
    (hT : MeasurableSet T) (hQ : Q (X ⁻¹' T) ≠ 0) : IndepFun X Y (Q[|X ⁻¹' T]) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  rw [cond_preimage_apply hX hXY hT hQ ht, cond_apply (hX hT), cond_apply (hX hT),
    ← Set.inter_assoc, ← Set.preimage_inter,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 hXY) _ _ (hT.inter hs) ht, mul_assoc]

end Indep

section Born

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {c : Type*} [Fintype c]
  [DecidableEq c] {D0 : ℝ} {D : Matrix c c ℂ} {J G : ℝ≥0 → Ω → GramState c}

theorem isBornGramSolution_cond (hG : IsBornGramSolution Q 𝓖 D0 D J G) {A : Set Ω}
    (hA : MeasurableSet[𝓖 0] A) (hA0 : Q A ≠ 0) : IsBornGramSolution (Q[|A]) 𝓖 D0 D J G where
  adapted := hG.adapted
  jump := hG.jump
  continuous := ae_cond_of_ae hG.continuous A
  feasible := ae_cond_of_ae hG.feasible A
  drift L e := by
    obtain ⟨N, hN, hNX⟩ := hG.drift L e
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩
  bracket L e e' := by
    obtain ⟨N, hN, hNX⟩ := hG.bracket L e e'
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩

end Born

/-! ### Models -/

/-- The entrance event `{seqTraceMeasure tseq ∈ S}`. -/
def entEvent {Ω : Type*} (tseq : Ω → ℕ → ℝ) (S : Set (Measure unitInterval)) : Set Ω :=
  (fun ω => seqTraceMeasure (tseq ω)) ⁻¹' S

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h : ℝ} {K K' M : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type*} [MeasurableSpace Ω]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Q : Measure Ω}
  {tseq : Ω → ℕ → ℝ} {τ : Ω → Fin p × Fin M → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin p × Fin M))}

theorem measurableSet_entEvent (hM : IsFiniteSourceModel b E s T q h K' M entrance 𝓖 Q tseq τ G)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    MeasurableSet[𝓖 0] (entEvent tseq S) :=
  (measurable_seqTraceMeasure.comp hM.entrance_measurable) hS

theorem measure_entEvent (hM : IsFiniteSourceModel b E s T q h K' M entrance 𝓖 Q tseq τ G)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    Q (entEvent tseq S) = entrance S := by
  have hF : Measurable fun ω => seqTraceMeasure (tseq ω) :=
    measurable_seqTraceMeasure.comp (hM.entrance_measurable.mono (𝓖.le 0) le_rfl)
  rw [← hM.entrance_law, Measure.map_apply hF hS]
  rfl

/-- **Conditioning keeps the model clauses that do not involve `G`.** -/
theorem model_cond_of (hM : IsFiniteSourceModel b E s T q h K' M entrance 𝓖 Q tseq τ G)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) (hS0 : entrance S ≠ 0)
    {G₁ : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))}
    (hinit : ∀ᵐ ω ∂Q, G₁ 0 ω = initialGram K (Fin p × Fin M) (tseq ω) h)
    (hsol : IsBornGramSolution (Q[|entEvent tseq S]) 𝓖 (transportD0 b E)
      (srcSignature K (Fin p × Fin M))
      (fun t ω => birthJump (fun i => τ ω i - s) (fun i => dStar b * sourceMass s T (q i.1) / M)
        (t : ℝ)) G₁) :
    IsFiniteSourceModel b E s T q h K M (entrance[|S]) 𝓖 (Q[|entEvent tseq S]) tseq τ G₁ := by
  have := hM.prob
  have hQA : Q (entEvent tseq S) ≠ 0 := by rwa [measure_entEvent hM hS]
  have ht : Measurable tseq := hM.entrance_measurable.mono (𝓖.le 0) le_rfl
  have hτ : Measurable τ := hM.births_measurable.mono (𝓖.le 0) le_rfl
  have hT : MeasurableSet (seqTraceMeasure ⁻¹' S) := measurable_seqTraceMeasure hS
  have hA : entEvent tseq S = tseq ⁻¹' (seqTraceMeasure ⁻¹' S) := rfl
  exact {
    prob := cond_isProbabilityMeasure hQA
    entrance_measurable := hM.entrance_measurable
    entrance_sequence := ae_cond_of_ae hM.entrance_sequence _
    entrance_law := by
      have hF : Measurable fun ω => seqTraceMeasure (tseq ω) :=
        measurable_seqTraceMeasure.comp ht
      rw [entEvent, map_cond_preimage Q hF hS, hM.entrance_law]
    births_measurable := hM.births_measurable
    births_law := by
      rw [hA, cond_preimage_map ht hτ hM.independent hT (by rwa [← hA]), hM.births_law]
    independent := by
      rw [hA]
      exact indepFun_cond_preimage ht hM.independent hT (by rwa [← hA])
    initial := ae_cond_of_ae hinit _
    solution := hsol }

end BlockBand.SourceProcess.CapLimit
