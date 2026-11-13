module

public import BlockBand.SourceProcess.CapLimit.Model

/-!
# Conditioning a complex finite source model on an entrance event

Conditioning on a `𝓖₀`-event keeps the `𝒦` extension (`isComplexSourceExtension_cond`) and the
clauses of a complex finite source model, so a complex model conditioned on an entrance event is a
complex model with the conditioned entrance (`ccondModel`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCapLimit

open MeasureTheory ProbabilityTheory Function
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

section Ext

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {b E : ℝ} {K : ℕ} {π : Type*}
  [Fintype π] [DecidableEq π] {D : Matrix (SrcCol K π) (SrcCol K π) ℂ}
  {J G : ℝ≥0 → Ω → GramState (SrcCol K π)} {JK Kc : ℝ≥0 → Ω → Matrix π π ℂ}

/-- The `𝒦` extension conditioned on an `𝓖₀`-event. -/
theorem isComplexSourceExtension_cond (hC : IsComplexSourceExtension Q 𝓖 b E D J G JK Kc)
    {A : Set Ω} (hA : MeasurableSet[𝓖 0] A) (hA0 : Q A ≠ 0) :
    IsComplexSourceExtension (Q[|A]) 𝓖 b E D J G JK Kc where
  adapted := hC.adapted
  jump := hC.jump
  continuous := ae_cond_of_ae hC.continuous A
  martingale L i j := by
    obtain ⟨N, hN, hNX⟩ := hC.martingale L i j
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩
  holomorphic L i j k l := by
    obtain ⟨N, hN, hNX⟩ := hC.holomorphic L i j k l
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩
  antiholomorphic L i j k l := by
    obtain ⟨N, hN, hNX⟩ := hC.antiholomorphic L i j k l
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩
  crossM L i j k l := by
    obtain ⟨N, hN, hNX⟩ := hC.crossM L i j k l
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩
  crossB L i j k l := by
    obtain ⟨N, hN, hNX⟩ := hC.crossB L i j k l
    exact ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae (hNX t) A⟩

end Ext

variable {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h : ℝ} {K K' : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type*} [MeasurableSpace Ω]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Q : Measure Ω}
  {tseq : Ω → ℕ → ℝ}

theorem cmeasurableSet_entEvent {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    MeasurableSet[𝓖 0] (entEvent tseq S) :=
  (measurable_seqTraceMeasure.comp hM.entrance_measurable) hS

theorem cmeasure_entEvent {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) :
    Q (entEvent tseq S) = entrance S := by
  have hF : Measurable fun ω => seqTraceMeasure (tseq ω) :=
    measurable_seqTraceMeasure.comp (hM.entrance_measurable.mono (𝓖.le 0) le_rfl)
  rw [← hM.entrance_law, Measure.map_apply hF hS]
  rfl

/-- **Conditioning keeps the complex model clauses not involving `(G, 𝒦)`.** -/
theorem cmodel_cond_of {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin np))}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K' entrance 𝓖 Q tseq G Kc)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) (hS0 : entrance S ≠ 0)
    {G₁ : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
    (hinit : ∀ᵐ ω ∂Q, G₁ 0 ω = initialGram K (Fin np) (tseq ω) h ∧ Kc 0 ω = 0)
    (hsol : IsBornGramSolution (Q[|entEvent tseq S]) 𝓖 (transportD0 b E)
      (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G₁)
    (hcx : IsComplexSourceExtension (Q[|entEvent tseq S]) 𝓖 b E (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G₁
      (fun t _ => kBirthJump E (fun j => τ j - s) m (t : ℝ)) Kc) :
    IsFiniteComplexSourceModel b E s τ m h K (entrance[|S]) 𝓖 (Q[|entEvent tseq S]) tseq G₁
      Kc := by
  have := hM.prob
  have hQA : Q (entEvent tseq S) ≠ 0 := by rwa [cmeasure_entEvent hM hS]
  have ht : Measurable tseq := hM.entrance_measurable.mono (𝓖.le 0) le_rfl
  exact {
    prob := cond_isProbabilityMeasure hQA
    entrance_measurable := hM.entrance_measurable
    entrance_sequence := ae_cond_of_ae hM.entrance_sequence _
    entrance_law := by
      have hF : Measurable fun ω => seqTraceMeasure (tseq ω) :=
        measurable_seqTraceMeasure.comp ht
      rw [entEvent, map_cond_preimage Q hF hS, hM.entrance_law]
    initial := ae_cond_of_ae hinit _
    solution := hsol
    complex := hcx }

/-- **Same cap**: conditioning a complex model on an entrance event gives a complex model. -/
theorem ccondModel {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}
    (hM : IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc)
    {S : Set (Measure unitInterval)} (hS : MeasurableSet S) (hS0 : entrance S ≠ 0) :
    IsFiniteComplexSourceModel b E s τ m h K (entrance[|S]) 𝓖 (Q[|entEvent tseq S]) tseq G Kc := by
  have := hM.prob
  have hA := cmeasurableSet_entEvent hM hS
  have hQA : Q (entEvent tseq S) ≠ 0 := by rwa [cmeasure_entEvent hM hS]
  exact cmodel_cond_of hM hS hS0 hM.initial (isBornGramSolution_cond hM.solution hA hQA)
    (isComplexSourceExtension_cond hM.complex hA hQA)

end BlockBand.SourceProcess.ComplexCapLimit
