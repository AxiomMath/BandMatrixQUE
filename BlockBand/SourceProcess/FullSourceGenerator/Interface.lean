module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The full-source generator theorem: the generator and tightness clauses

The `generator` and `tight` fields of `FullSourceGeneratorContract` as separate statements, the
summed generator errors with early tags `EarlySummed`, and `WordLimitExists`: by Prokhorov over
the countably many ordinary words, joint critical limits exist along subsequences.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

/-- **The `generator` field** of `FullSourceGeneratorContract`. -/
def GeneratorClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ t₀ : ℝ, 0 < t₀ →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), (∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) →
    ∀ k : ℕ → Fin nT → ℕ, (∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : TraceWord nT nI → ℝ → Ω → ℂ),
      IsWordLimit b E k q t₀ P Z → ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ →
      let obs : {w : TraceWord nT nI // IsOrdinaryWord w} → ℝ → Ω → ℂ := fun w => Z w.1
      let M : ℝ → ℝ → Ω → ℂ := fun s t ω =>
        MvPolynomial.eval (fun w => Z w t ω) Φ - MvPolynomial.eval (fun w => Z w s ω) Φ -
          ∫ u in s..t, MvPolynomial.eval (fun w => Z w u ω) (wordGenerator b E q u Φ)
      IsMartingaleIncrements P obs (Set.Ici t₀) M ∧
      IsMartingaleIncrements P obs (Set.Ici t₀) fun s t ω =>
        M s t ω ^ 2 - ∫ u in s..t, MvPolynomial.eval (fun w => Z w u ω) (wordCarre b E Φ)

/-- **The `tight` field** of `FullSourceGeneratorContract`. -/
def TightClause : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ t₀ : ℝ, 0 < t₀ →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), (∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) →
    ∀ k : ℕ → Fin nT → ℕ, (∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) →
    ∀ w : TraceWord nT nI, IsOrdinaryWord w → ∀ t₁ T : ℝ, t₀ ≤ t₁ → t₁ < T →
      (∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | M < ‖wordValue b E (k W) q W ⌊(W : ℝ) * t₁⌋₊ ω w‖} ≤
          ENNReal.ofReal θ) ∧
      (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧
          η < ‖wordValue b E (k W) q W ⌊(W : ℝ) * t⌋₊ ω w -
            wordValue b E (k W) q W ⌊(W : ℝ) * t'⌋₊ ω w‖} ≤ ENNReal.ofReal θ)

/-- **The summed generator errors with early tags.** Fixed `b`, bulk `E`, a source family (`nT` tags
normalized by `W`, `nI` interval sources with tests `q`), an ordinary trace polynomial `Φ`,
`0 < ε < T`, the stop level `K`; then `C = C_{K,ε,T}` and `W₀`. For `W ≥ W₀`, *all* tag birth
indices `k` and every window start `j₀ ≥ εW` after all tag births (`k_a < j₀`), the expected
absolute errors of the two conditional increment formulas before the trace stop,
`E|1{j<σ_K}(E_j[ΔΦ_j] - W⁻¹𝒜_{(j+1)/W}Φ)|` and `E|1{j<σ_K}(E_j[(ΔΦ_j)²] - W⁻¹Γ(Φ))|`, summed over
the steps `j₀ ≤ j < ⌊TW⌋`, are at most `C(W^{-1/2} + W⁻¹)`. The stop `σ_K` is `traceStop` (from
`εW`); the conditional expectations are those of `ContractingWordsContract.summed`. -/
def EarlySummed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T K : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ k : Fin nT → ℕ, ∀ j₀ : ℕ, ε * W ≤ j₀ →
      (∀ a, k a < j₀) →
      let μ := growthPathLaw W b
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      let F : ℕ → GrowthPath W → ℂ := fun j ω => polyValue b E k q W j ω Φ
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => j₀ ≤ j
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => F (j + 1) ω - F j ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω
              (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W)) ∧
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => (F (j + 1) ω - F j ω) ^ 2) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W))

/-- **Existence of joint critical limits** (Prokhorov over the countably many ordinary words).
For the data of
`generator`, some probability space carries a joint critical limit. -/
def WordLimitExists : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ t₀ : ℝ, 0 < t₀ →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), (∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) →
    ∀ k : ℕ → Fin nT → ℕ, (∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : TraceWord nT nI → ℝ → Ω → ℂ),
      IsWordLimit b E k q t₀ P Z

end BlockBand.SourceProcess.FullSourceGenerator
