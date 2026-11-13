module

public import BlockBand.SourceProcess.SourceProcessLaw.Interface

/-!
# Uniqueness of the born Gram law

`BornGramLawUnique` is uniqueness in law for the Gram martingale problem with finitely many births
at `𝓖₀`-measurable times and deterministic jump matrices: two born solutions whose birth times and
initial Gram state have the same joint law have the same one-time Gram laws. It contains no
model data (no entrance, no sampling law); `modelUnique_of_bornGramLawUnique` derives
`ModelUnique` from it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornUnique

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

/-- Jump process of finitely many births: `J(t) = Σ_f 1{β_f ≤ t} j_f`. -/
def birthSum {c F : Type*} [Fintype F] (j : F → GramState c) (β : F → ℝ) (t : ℝ) :
    GramState c :=
  ∑ f, if β f ≤ t then j f else 0

/-- **Uniqueness of the born Gram law**, the uniqueness part of the finite Gram law proposition,
with births at `𝓖₀`-measurable times. For `D₀ > 0`, a signature `𝖣`, finitely many
births `f ∈ F` with deterministic Gram jumps `j_f`, and two born Gram solutions
(`IsBornGramSolution`, jump process `birthSum j β`) on arbitrary filtered probability spaces,
with `𝓖₀`-measurable birth times `β`: if `(β, G₀)` has the same law in both, then `G_t` has the
same law in both, for every `t`. -/
def BornGramLawUnique : Prop :=
  ∀ (c F : Type) [Fintype c] [DecidableEq c] [Fintype F] (D0 : ℝ) (D : Matrix c c ℂ),
    0 < D0 → IsSignature D → ∀ j : F → GramState c,
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (β : Ω → F → ℝ) (G : ℝ≥0 → Ω → GramState c),
    IsProbabilityMeasure Q → Measurable[𝓖 0] β →
    IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G →
  ∀ (Ω' : Type) (m' : MeasurableSpace Ω') (𝓖' : Filtration ℝ≥0 m') (Q' : Measure Ω')
    (β' : Ω' → F → ℝ) (G' : ℝ≥0 → Ω' → GramState c),
    IsProbabilityMeasure Q' → Measurable[𝓖' 0] β' →
    IsBornGramSolution Q' 𝓖' D0 D (fun t ω => birthSum j (β' ω) (t : ℝ)) G' →
    Q.map (fun ω => (β ω, G 0 ω)) = Q'.map (fun ω => (β' ω, G' 0 ω)) →
  ∀ t : ℝ≥0, Q.map (G t) = Q'.map (G' t)

end BlockBand.SourceProcess.BornUnique
