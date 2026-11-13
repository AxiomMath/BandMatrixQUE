module

public import BlockBand.SourceProcess.CompleteSourceGap.Interface

/-!
# The bulk-uniform contracting-separator inputs of the word step

The two statements below are the two fields of `CompleteSourceGapStatement` with the energy
quantifier moved **inside** the constants: `∀ κ > 0, ∃ C W₀, ∀ W ≥ W₀, ∀ E ∈ bulkInterval κ`
instead of `∀ E ∈ (-2,2), ∃ C W₀`. The word step needs constants uniform on `bulkInterval κI`
because `WordStepMean`/`WordStepFluct` quantify `E` after `C, W₀`. The existence clause
`∃ s, IsStationaryJet b E s` of `mean` is dropped (the word step is stated at a given jet).

Setting: one fresh one-port layer `ω ~ freshLaw W b` at a deterministic Hermitian old
two-port Schur matrix `𝕏`, `X = nearSchur z 𝕏`, `N = freshTransport b E 𝕏 ω`,
`transportedSep b E 𝕏 σ ω = N · sepOf b E 𝕏₊ σ · N*` with `𝕏₊ = freshTwoPortSchur E 𝕏 ω`,
`g = Tr T(X)`, operator norm; `σ.unconj + σ.conj = 1` selects `P𝕊, 𝕊*P, P𝕊P, P𝕊*P`.

A bulk-uniform `CompleteSourceGapStatement` (each field with `∀ κ, 0 < κ →` before `∃ C W₀` and
`∀ E ∈ bulkInterval κ` after `∀ W ≥ W₀`) gives both statements by projection.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open scoped ENNReal ComplexConjugate Matrix.Norms.L2Operator

/-- **Bulk-uniform conditional means of the contracting separators.**
`CompleteSourceGapStatement.mean` with constants uniform on `bulkInterval κ`: for `W ≥ W₀`, every
`E ∈ bulkInterval κ`, every stationary jet `s`, every Hermitian `𝕏` and every contracting `σ`,
`‖E[N sepOf(𝕏₊) σ N*] - θ_*^{r(σ)}θ̄_*^{r̄(σ)} sepOf(𝕏) σ‖ ≤ C(δ₀ + δ₁ + g/W + W⁻²)`. -/
def SeparatorMeanUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, σ.unconj + σ.conj = 1 →
        let X := nearSchur (boundaryZ b E) XX
        ‖matrixExpect (freshLaw W b) (transportedSep b E XX σ) -
            gapFactor b E s σ • sepOf b E XX σ‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X +
            conductanceOf (passiveTransmission b E X) / W + ((W : ℝ)⁻¹) ^ 2)

/-- **Bulk-uniform centered bilinear bounds of the contracting separators.**
`CompleteSourceGapStatement.fluctuation` with constants uniform on `bulkInterval κ`:
`‖u*(T_σ - ET_σ)v‖_{L^p} ≤ C_pW^{-1/2}‖u‖‖v‖`, `T_σ = N sepOf(𝕏₊) σ N*`. -/
def SeparatorFluctUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ : Separator, σ.unconj + σ.conj = 1 → ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (transportedSep b E XX σ ω -
            matrixExpect (freshLaw W b) (transportedSep b E XX σ)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

end BlockBand.SourceProcess.ContractingWords
