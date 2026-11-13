module

public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# The passive bounds lemma: statement

## The statement in the paper

For independent fresh blocks `A ~ GUE_W(c/W)`, `B ~ Gin(b/W)` (`c = 1-2b`) and an independent
passive input `X` (`Y = -Im X ⪰ 0`), with
`𝒢 = [[A - E - X, B], [B*, zI]]⁻¹`, `K = z - X`, `L = K𝒢₁₂`, `X₊ = B*(A - E - X)⁻¹B`,
`R₊ = (z - X₊)⁻¹`, `η = Im z`:
1. all fixed operator moments of `𝒢`, `K𝒢₁₁` and `L` are bounded uniformly in `W ≥ W₀(p)`
   and `X`;
2. normalized trace–matrix covariances of their fixed inverse words are `O(W⁻²)`;
3. centered bilinear entries of `LL*` and `L(R₊ - (2iη)⁻¹I)L*` have conditional `L^p` norm
   `≤ C_p W^{-1/2}‖u‖‖v‖`.

## Lean reading

* **Measure.** `freshLaw W b = layerLaw W b .oneBlockOnePort` (the fresh layer only). The old
  input `X` is deterministic; this is the conditional statement (Fubini), as in `Layers`.
* **Domain.** `0 < b < 1/2`; `E ∈ bulkInterval κ` for a fixed `κ > 0`, uniformly; the port
  parameter `w` ranges over the closed disk `paramDisk b E` of radius `η/2` about `z = z_∂(E)`,
  uniformly (the argument also applies on a fixed parameter disk). At `w = z` every clause is
  the clause of the paper; `K = w - X` and `R₊ = (w - X₊)⁻¹` on the disk, so that
  `K𝒢₁₁ = I + [(w+E)I - A + w⁻¹BB*]𝒢₁₁`.
  Every passive `X : Matrix (Fin W) (Fin W) ℂ` (`(passiveY X).PosSemidef`, no norm bound).
* **Norms.** Euclidean operator norm (`Matrix.Norms.L2Operator`) for matrices, `vecNorm` for
  vectors, `eLpNorm` for `L^p` norms. The `W⁻²` covariance is in operator norm.
* **Uniformity.** Constants depend on `b, κ` and the fixed orders/lengths/insertion bound
  only: `moments` and `bilinear` on `p`, `traceMatrix` on the maximal word length and the
  bound `Kd` on the deterministic insertions.
* **Words.** A "fixed inverse word" is `D₀ ℓ₁ D₁ ⋯ ℓ_m D_m` with letters
  `ℓ_j ∈ {𝒢₁₁, 𝒢₁₂, 𝒢₂₁, 𝒢₂₂, K𝒢₁₁, L}` or their adjoints (`passiveLetter`) and
  deterministic `W × W` insertions `‖D_j‖ ≤ Kd`, the passive analogue of `Layers.wordEval`.
  Weighted inverses occur only in the displayed order `K𝒢₁₁`, `K𝒢₁₂`.
* **Integrability.** `traceMatrix` asserts integrability of `f`, `U`, `fU` (as
  `Layers.TraceMatrixContract`), so no Bochner-junk value enters its left side. In `bilinear`
  a finite `L^p` bound already forces `U` to be integrable.

The `oneStepFluctuation` field of `PassiveSourceMixingContract` is the `w = z` case of `bilinear`
(`oneStepFluctuation_of_passiveBounds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## Vocabulary
-/

/-- The one-block lift of a `W × W` input to `PhysSite W .oneBlockOnePort = Fin 1 × Fin W`. -/
def liftX (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
  Matrix.of fun u v => X u.2 v.2

/-- The fixed parameter disk: the closed disk of radius `η/2` about `z = z_∂(E)`,
`η = Im z_∂(E)` (so `Im w ≥ η/2` on it). -/
def paramDisk (b E : ℝ) : Set ℂ := Metric.closedBall (boundaryZ b E) (etaZ b E / 2)

/-- The fresh one-port layer `𝒢 = [[A - E - X, B], [B*, wI]]⁻¹` at port parameter `w`. -/
def layerAt (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerResolvent .oneBlockOnePort E w (liftX X) ω

/-- `𝒢₁₁` (physical × physical). -/
def g11 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => layerAt E w X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y))

/-- `𝒢₁₂` (physical × port). -/
def g12 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => layerAt E w X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- `𝒢₂₁` (port × physical). -/
def g21 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => layerAt E w X ω (Sum.inr ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y))

/-- `𝒢₂₂` (port × port); it equals `R₊ = (w - X₊)⁻¹` off a null set. -/
def g22 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => layerAt E w X ω (Sum.inr ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- The weighted inverse `K𝒢₁₁`, `K = w - X`. -/
def kG11 (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * g11 E w X ω

/-- `L = K𝒢₁₂`, `K = w - X`. At `w = z_∂` this is `TransmissionPath.freshL`. -/
def lAt (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * g12 E w X ω

/-- The six letters `𝒢₁₁, 𝒢₁₂, 𝒢₂₁, 𝒢₂₂, K𝒢₁₁, L`. -/
def passiveLetter (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Fin 6 → Matrix (Fin W) (Fin W) ℂ :=
  ![g11 E w X ω, g12 E w X ω, g21 E w X ω, g22 E w X ω, kG11 E w X ω, lAt E w X ω]

/-- A fixed inverse word `D₀ ℓ₁ D₁ ⋯ ℓ_m D_m`: letter `j` is `passiveLetter (wd j).1`, its
adjoint when `(wd j).2 = true`; `D` are the deterministic insertions. -/
def passiveWord (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  D 0 * (List.ofFn fun j : Fin ℓ =>
    (if (wd j).2 then (passiveLetter E w X ω (wd j).1)ᴴ else passiveLetter E w X ω (wd j).1) *
      D j.succ).prod

/-- `LL*` at port parameter `w`. -/
def uAt (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  lAt E w X ω * (lAt E w X ω)ᴴ

/-- `L(R₊ - c₀I)L*`, `R₊ = (w - X₊)⁻¹`, `c₀ = (2iη)⁻¹`. -/
def transportedFAt (b E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  lAt E w X ω * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur E X ω)⁻¹ -
    cZero b E • (1 : Matrix (Fin W) (Fin W) ℂ)) * (lAt E w X ω)ᴴ

/-!
## The statement
-/

/-- **The passive bounds lemma**, on the parameter disk. Law `freshLaw W b`; deterministic passive
`X`; `E ∈ bulkInterval κ`,
`w ∈ paramDisk b E`; operator norms.
* `moments`: for every `p ≥ 1` there are `C, W₀` such that for `W ≥ W₀` the layer matrix is
  a.s. invertible and `‖𝒢‖`, `‖K𝒢₁₁‖`, `‖L‖` have `L^p` norm `≤ C`.
* `traceMatrix`: for each maximal word length `Lw` and insertion bound `Kd` there are `C, W₀`
  such that for `W ≥ W₀`, `f = W⁻¹ Tr w_f`, `U = w_U` (fixed inverse words), `f, U, fU` are
  integrable and `‖E(fU) - (Ef)(EU)‖ ≤ C W⁻²`.
* `bilinear`: for every `p ≥ 1` there are `C, W₀` such that for `W ≥ W₀` and all vectors
  `u, v`, `‖u*(U - EU)v‖_p ≤ C W^{-1/2}‖u‖‖v‖` for `U = LL*` and `U = L(R₊ - c₀I)L*`. -/
structure PassiveBoundsStatement : Prop where
  moments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        (∀ᵐ ω ∂freshLaw W b, IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω).det) ∧
        eLpNorm (fun ω => ‖layerAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal C ∧
        eLpNorm (fun ω => ‖kG11 E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal C ∧
        eLpNorm (fun ω => ‖lAt E w X ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal C
  traceMatrix : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (Lw : ℕ) (Kd : ℝ),
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ (ℓf ℓU : ℕ), ℓf ≤ Lw → ℓU ≤ Lw →
      ∀ (wf : Fin ℓf → Fin 6 × Bool) (Df : Fin (ℓf + 1) → Matrix (Fin W) (Fin W) ℂ)
        (wU : Fin ℓU → Fin 6 × Bool) (DU : Fin (ℓU + 1) → Matrix (Fin W) (Fin W) ℂ),
        (∀ j, ‖Df j‖ ≤ Kd) → (∀ j, ‖DU j‖ ≤ Kd) →
        let μ := freshLaw W b
        let f : LayerSample W .oneBlockOnePort → ℂ := fun ω =>
          (W : ℂ)⁻¹ * (passiveWord E w X wf Df ω).trace
        let U : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
          passiveWord E w X wU DU
        Integrable f μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
          (∀ x y, Integrable (fun ω => f ω * U ω x y) μ) ∧
          ‖matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U‖ ≤
            C / (W : ℝ) ^ 2
  bilinear : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ w ∈ paramDisk b E,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (uAt E w X ω - matrixExpect (freshLaw W b) (uAt E w X)) v)
            (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (transportedFAt b E w X ω -
            matrixExpect (freshLaw W b) (transportedFAt b E w X)) v)
            (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

end BlockBand.Transmission.PassiveLayer
