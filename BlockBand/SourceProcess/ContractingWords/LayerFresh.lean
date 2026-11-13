module

public import BlockBand.SourceProcess.ContractingWords.LayerWord
public import BlockBand.Transmission.Bridge.NewRow

/-!
# The one-layer word step at a deterministic old state (statement)

`LayerFreshBound`: `b`, the bulk margin `κ`, the degree `d`, the exponent `r ≥ 1`, the letter bound
`K` and the injection bound `c₀`, then `C, W₀`; for `W ≥ W₀`, every `E ∈ bulkInterval κ`, every
stationary jet `s`, every Hermitian old two-port `𝕏` (`X = nearSchur z 𝕏`), all Hermitian old
letters with `Tr|A_ℓ| ≤ K`, injections `|c_ℓ| ≤ c₀/W²` and every admitted product of degree
`≤ d`, the new value `Z(ω) = newProd A c N D (sepOf 𝕏₊) Zs` of one fresh layer satisfies
* `|EZ - θ_*^rθ̄_*^{r̄} Z_old| ≤ C(δ₀ + δ₁ + g/W + W⁻¹)`, `Z_old = coreProd A (sepOf 𝕏) Zs`;
* `‖Z - EZ‖_r ≤ C(W^{-1/2} + δ₀)`.
The `δ₀` in the second bound pays the fluctuation of `NN*` off the scalar domain of
`FullSourceEstimates.fluct` (crude moment bound there); along the path `‖δ₀‖_p ≤ C/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge
open scoped ENNReal

/-- **The one-layer word step** (at one fresh layer, bulk-uniform). -/
def LayerFreshBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (d : ℕ) (r K c₀ : ℝ), 1 ≤ r → 0 ≤ K → 0 ≤ c₀ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (c : TraceLetter nT nI → ℝ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        (∀ ℓ, |c ℓ| ≤ c₀ / (W : ℝ) ^ 2) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        let X := nearSchur (boundaryZ b E) XX
        let Z : LayerSample W .oneBlockOnePort → ℂ := fun y =>
          newProd A c (freshTransport b E XX y) (freshD b E XX y)
            (sepOf b E (freshTwoPortSchur E XX y)) Zs
        Integrable Z (freshLaw W b) ∧
        ‖∫ y, Z y ∂freshLaw W b - meanFactor b E s Zs * coreProd A (sepOf b E XX) Zs‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X +
            conductanceOf (passiveTransmission b E X) / W + (W : ℝ)⁻¹) ∧
        eLpNorm (fun y => Z y - ∫ y', Z y' ∂freshLaw W b) (ENNReal.ofReal r) (freshLaw W b) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + jetDistance0 b E X))

end BlockBand.SourceProcess.ContractingWords
