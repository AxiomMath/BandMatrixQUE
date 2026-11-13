module

public import BlockBand.SourceProcess.ComplexSourceLaw.Interface

/-!
# Splitting `ComplexFiniteUniqueness` into a segment law and a birth concatenation

`JointSegmentLaw`: for two born Gram solutions with complex source extensions (deterministic
births at `τ_j - s`), on an interval `[a, t]` containing no birth, equal joint laws of `(G, 𝒦)` at
time `a` give equal joint laws at time `t`. `SplitTarget` is the implication
`JointSegmentLaw → ComplexFiniteUniqueness`, obtained by concatenation over the births.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSplit

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal

/-- **The joint segment law.** On the domain of `ComplexFiniteUniqueness`, let two probability
spaces carry Gram processes solving the born Gram problem (`IsBornGramSolution`) and `𝒦` processes
solving the complex source extension (`IsComplexSourceExtension`), both with the model's
deterministic birth jumps (`birthJump` at `τ_j − s` of size `d_* m_j`, `kBirthJump` of size
`a m_j`). For a deterministic `a` and every `t ≥ a` with no birth in `(a, t]`, equal joint laws of
`(G(a), 𝒦(a))` give equal joint laws of `(G(t), 𝒦(t))`. Proved as
`ComplexUnique.jointSegmentLaw_holds`.
-/
def JointSegmentLaw : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ K : ℕ,
  ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (Q₁ : Measure Ω₁)
    (G₁ : ℝ≥0 → Ω₁ → GramState (SrcCol K (Fin np))) (K₁ : ℝ≥0 → Ω₁ → Matrix (Fin np) (Fin np) ℂ),
    IsProbabilityMeasure Q₁ →
    IsBornGramSolution Q₁ 𝓖₁ (transportD0 b E) (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G₁ →
    IsComplexSourceExtension Q₁ 𝓖₁ b E (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G₁
      (fun t _ => kBirthJump E (fun j => τ j - s) m (t : ℝ)) K₁ →
  ∀ (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (Q₂ : Measure Ω₂)
    (G₂ : ℝ≥0 → Ω₂ → GramState (SrcCol K (Fin np))) (K₂ : ℝ≥0 → Ω₂ → Matrix (Fin np) (Fin np) ℂ),
    IsProbabilityMeasure Q₂ →
    IsBornGramSolution Q₂ 𝓖₂ (transportD0 b E) (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G₂ →
    IsComplexSourceExtension Q₂ 𝓖₂ b E (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G₂
      (fun t _ => kBirthJump E (fun j => τ j - s) m (t : ℝ)) K₂ →
  ∀ a t : ℝ≥0, a ≤ t → (∀ j, ¬ ((a : ℝ) < τ j - s ∧ τ j - s ≤ (t : ℝ))) →
    Q₁.map (fun ω => (G₁ a ω, K₁ a ω)) = Q₂.map (fun ω => (G₂ a ω, K₂ a ω)) →
      Q₁.map (fun ω => (G₁ t ω, K₁ t ω)) = Q₂.map (fun ω => (G₂ t ω, K₂ t ω))

/-- The implication `JointSegmentLaw → ComplexFiniteUniqueness`, proved as
`ComplexUniqueSegment.splitTarget_holds` (through `complexFiniteUniqueness_of_segment`).
-/
def SplitTarget : Prop := JointSegmentLaw → ComplexFiniteUniqueness

end BlockBand.SourceProcess.ComplexSplit
