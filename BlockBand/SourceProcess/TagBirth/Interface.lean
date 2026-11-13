module

public import BlockBand.Internal.Contracts.TransmissionUniform2
public import BlockBand.Transmission.PathScalar.MeanEqPort

/-!
# Tag-birth values

## Method (departure from the paper's ladder)

The paper solves the advanced–retarded ladder for the near trace `t₂ = W⁻¹E Tr 𝒢₁₂*𝒢₁₂` and
bounds the far part of `C₊` by the conductance `g`. Lean uses instead the exact **Ward identity
of the fresh layer**: for `k ≥ 1`, almost surely `Y_{k+1;k} = D₊*D₊`, `D₊ = [𝒢₁₂, 𝒢₁₁Kℝ₁₂]`,
and (far absorption `R Y R* = ηℝ₁₂ℝ₁₂*`, `Im 𝒢₁₁ = -(𝒢₁₁Y𝒢₁₁* + η𝒢₁₂𝒢₁₂*)`)
`η Tr D₊D₊* = -Im Tr 𝒢₁₁`. With `z + E = -(1-b)a`, `η = -(1-b) Im a`, hence `d_* = -Im a/η` and
`W⁻¹Tr Y_{k+1;k} - d_* = -η⁻¹ Im(⟨𝒢₁₁⟩ - a)`. Near and far parts are handled together; the
conductance is not needed.

The fresh-layer input is stated below as `FreshPhysTraceLp`: `⟨𝒢₁₁⟩` is close to `a` in
`L^p(freshLaw)`, linearly in `δ₀(X)`, up to `W^{-1/2}`, uniformly on `bulkInterval κ` and in the
passive input `X`. It follows from `𝒢₁₁ = R + RΔR` (`Δ = K𝒢₁₁K - K`), the bounds `DeltaMean`
and `DeltaFluctuation`, and the layer moments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.TagBirth

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PathScalar
open scoped ENNReal ComplexOrder

/-- **Fresh-layer input.** `b, κ, p ≥ 1`, then `A, B ≥ 0` and `W₀`. For `W ≥ W₀`, every
`E ∈ bulkInterval κ` and every passive `X` (`-Im X ⪰ 0`):
`‖⟨𝒢₁₁⟩ - a‖_{L^p(freshLaw)} ≤ A δ₀(X) + B W^{-1/2}`. -/
def FreshPhysTraceLp : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (A B : ℝ) (W₀ : ℕ), 0 ≤ A ∧ 0 ≤ B ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => physTr b E X ω - matchedA E) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (A * jetDistance0 b E X + B / Real.sqrt W)

end BlockBand.SourceProcess.TagBirth
