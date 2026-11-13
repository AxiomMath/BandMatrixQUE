module

public import BlockBand.Transmission.Bridge.Complete

/-!
# The one-layer inputs of the full-source moments

The statement `FullSourceEstimates`: at one fresh layer, on the scalar domain,
`‖E𝓔‖ ≤ C(δ₀ + W⁻²)` and `‖u*(𝓔 - E𝓔)v‖_{L^p} ≤ C_pW^{-1/2}‖u‖‖v‖`, and unconditionally
`‖N‖_{L^p} + ‖C₊‖_{L^p} ≤ C_p`.

* **Measure.** `freshLaw W b` (one fresh one-port layer); the old two-port Schur matrix `𝕏` is
  deterministic (conditional statement; the path is integrated out by Fubini). `𝕏` Hermitian,
  as `pathSchur` of a Hermitian path (`Bridge.pathSchur_isHermitian`).
* **Objects.** `N = freshTransport b E 𝕏`, `𝓔 = wardNoise b E 𝕏 = NN* - I`,
  `D₊ = Bridge.freshD b E 𝕏` (`C₊ = D₊*D₊`, so `‖C₊‖ = ‖D₊‖²`), `δ₀ = jetDistance0 b E X`,
  `X = nearSchur z 𝕏`.
* **Domain.** `mean` is stated for every Hermitian `𝕏`. On the scalar domain `δ₀ ≤ d₀` this is
  the bound above; off it, `‖E𝓔‖ ≤ E‖N‖² + 1 ≤ C ≤ (C/d₀)δ₀` by `moments`, so the two forms are
  equivalent. `fluct` is stated only on a scalar domain `δ₀ ≤ d₀` (some `d₀ > 0` depending on
  `b, κ`); this is all the moments proof uses. `moments` holds for every Hermitian `𝕏`.
* **Uniformity.** Constants depend on `b, κ` (and `p`); uniform in `W ≥ W₀`,
  `E ∈ bulkInterval κ`, `𝕏`, `u`, `v`.
* **Norms.** Operator norm (`Matrix.Norms.L2Operator`), `vecNorm`, `eLpNorm`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

/-- **The full-source estimates** with the unconditional moments, at a
deterministic Hermitian old two-port Schur matrix `𝕏` and one fresh layer.
* `mean`: `‖E𝓔‖ ≤ C(δ₀(X) + W⁻²)`;
* `fluct`: on the scalar domain `δ₀(X) ≤ d₀`, `‖u*(𝓔 - E𝓔)v‖_p ≤ C_p W^{-1/2}‖u‖‖v‖`;
* `moments`: `‖‖N‖‖_p ≤ C_p` and `‖‖D₊‖‖_p ≤ C_p`. -/
structure FullSourceEstimates : Prop where
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤
          C * (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + ((W : ℝ)⁻¹) ^ 2)
  fluct : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      jetDistance0 b E (nearSchur (boundaryZ b E) XX) ≤ d₀ → ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
            matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)
  moments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal C ∧
          eLpNorm (fun ω => ‖freshD b E XX ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal C

end BlockBand.SourceProcess.FullSource
