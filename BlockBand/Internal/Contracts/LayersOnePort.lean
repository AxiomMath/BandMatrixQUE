module

public import BlockBand.Internal.Contracts.Layers

/-!
# One-port Hermitian and passive layer estimates

Statements on the fresh one-block, one-port layer: the weighted trace–matrix covariance, the
mean of `LL*` for a passive old self-energy, and operator moments of the one-port transfer `L`.

## Conventions

* **Conditioning.** As in `Internal.Contracts.Layers`: every statement quantifies over
  deterministic `X` and
  integrates against the fresh layer law only (Fubini gives the conditional form `E_j`, `E(·|X)`).
* **Covariances.** `Cov(f, U) = E(fU) - (Ef)(EU)` entrywise through `matrixExpect`; norms are the
  Euclidean operator norm (`Matrix.Norms.L2Operator`); the Loewner bound `M ⪯ λI` is
  `(λI - M).PosSemidef`. Integrability of the integrands is part of each conclusion (no
  Bochner-integral loophole).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.LayersOnePort

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 0. One-port vocabulary
-/

/-- The old one-port self-energy `X` (`W × W`) on the physical sites `Fin 1 × Fin W` of the
one-block layer.
-/
def onePortLift {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  Matrix.of fun u v => X u.2 v.2

/-- The fresh one-port layer resolvent `𝒢 = [[A - E - X, B], [B*, zI]]⁻¹`, `z = z_∂(E)`. -/
def onePortResolvent {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerResolvent .oneBlockOnePort E (boundaryZ b E) (onePortLift X) ω

/-- `𝒢₁₂`: physical-row, port-column block of the one-port layer resolvent. -/
def onePortG12 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => onePortResolvent b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- The one-port transfer `L = K𝒢₁₂`, `K = z - X`; equal by `rfl` to
`TransmissionPath.freshL b E X ω`. -/
def onePortL {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  (boundaryZ b E • 1 - X) * onePortG12 b E X ω

/-- The weight `𝒦 = diag(z - X, 0)` on the layer sites, so that
`Q 𝒢 𝒦*` has the physical (top) column block `(Q𝒢)_{·,top} K*` and zero port columns.
-/
def onePortWeight {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  Matrix.fromBlocks (boundaryZ b E • 1 - onePortLift X) 0 0 0

/-- Projection `P_phys` onto the physical block (`W⁻¹ Tr P_phys 𝒢 = W⁻¹ Tr 𝒢₁₁`). -/
def onePortPhysProj {W : ℕ} :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  Matrix.fromBlocks 1 0 0 0

/-- Projection `P_port` onto the port block (`W⁻¹ Tr P_port 𝒢 = W⁻¹ Tr 𝒢₂₂`). -/
def onePortPortProj {W : ℕ} :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  Matrix.fromBlocks 0 0 0 1

/-- The dissipation `-Im X = (i/2)(X - X*)` (equal to `passiveY X`). -/
def onePortDissipation {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (Complex.I / 2) • (X - Xᴴ)

/-- `X` is a passive old self-energy: `-Im X ⪰ 0`. Every
Hermitian `X` is passive. -/
def IsPassiveInput {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : Prop :=
  (onePortDissipation X).PosSemidef

/-- The one-port scalar distance `δ₀ = |W⁻¹ Tr (z - X)⁻¹ - a|`, `z = z_∂(E)`; equal by `rfl` to
`jetDistance0 b E X`. -/
def onePortDistance (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖(W : ℂ)⁻¹ * ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace - matchedA E‖

/-!
## 1. The weighted trace–matrix covariance
-/

/-- The weighted trace–matrix covariance.
* Law: `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`, deterministic Hermitian `X` (`W × W`;
  the independent past), `K = z - X` (unbounded: no bound on `‖X‖`), `𝒦 = diag(K, 0)`.
* Domain/quantifiers: `b ∈ (0,1/2)`, `κ > 0`; then `C, W₀`; then uniformly in `W ≥ W₀`, every
  Hermitian `X`, every `E ∈ bulkInterval κ` and all deterministic `P, Q` on the layer sites with
  `‖P‖, ‖Q‖ ≤ 1`.
* Conclusion: with `g = W⁻¹ Tr(P𝒢)` and `U = Q𝒢𝒦*`: `g`, the entries of `U` and of `gU` are
  integrable and `‖E(gU) - (Eg)(EU)‖_op ≤ C W⁻²`.
* Uniformity in `X`: the weight never multiplies an unweighted error. For Hermitian `X`,
  `𝒢₁₁K* = I + 𝒢₁₁[(z̄+E)I - A + z⁻¹BB*]`, so the weighted word is a word in `𝒢`
  and the Gaussian letters `A, B`, whose moments (`GaussianAbsorptionContract`) are uniform in
  Hermitian `X`; the Cauchy-type tails of `X₊` at real energy do not enter. -/
def OnePortWeightedCovarianceContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
    ∀ P Q : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ,
      ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
      let μ := layerLaw W b .oneBlockOnePort
      let g : LayerSample W .oneBlockOnePort → ℂ := fun ω =>
        (W : ℂ)⁻¹ * (P * onePortResolvent b E X ω).trace
      let U : LayerSample W .oneBlockOnePort →
          Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ := fun ω =>
        Q * onePortResolvent b E X ω * (onePortWeight b E X)ᴴ
      Integrable g μ ∧ (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
        (∀ x y, Integrable (fun ω => g ω * U ω x y) μ) ∧
        ‖matrixExpect μ (fun ω => g ω • U ω) - (∫ ω, g ω ∂μ) • matrixExpect μ U‖ ≤
          C / (W : ℝ) ^ 2

/-!
## 2. The one-port passive mean
-/

/-- The one-port passive mean.
* Law: `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`; deterministic passive `X`
  (`-Im X ⪰ 0`; the near-end Schur matrix of the old path), `L = K𝒢₁₂`, `K = z - X`,
  `δ₀ = onePortDistance b E X`.
* Quantifiers: `b ∈ (0,1/2)`, `κ > 0`; then `C ≥ 0`, `W₀`; then uniformly in `W ≥ W₀`, every
  passive `X` and `E ∈ bulkInterval κ` (no scalar-domain restriction).
* Conclusion: the entries of `LL*` are integrable and `E LL* ⪯ (1 + Cδ₀ + CW⁻²) I`.
* Why no domain restriction: on `δ₀ ≤ d` the bound is the cancelled passive mean
  (`(I + Ωf + Ω̄f*)/(1 + αq/W)` with `|Ω| ≤ Cδ₀`, `‖f‖ ≤ 3/(2η)` since `‖R‖ ≤ η⁻¹` for passive
  `X`, `1 + αq/W ≥ 1`, and errors `δ₀² + δ₀q/W + W⁻² ≤ C(δ₀ + W⁻²)` since `q/W ≤ 1/(4η)`); on
  `δ₀ > d` it follows from `‖E LL*‖ ≤ E‖L‖²` (`OnePortOperatorMomentsContract`) after enlarging
  `C`. -/
def OnePortPassiveMeanContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, IsPassiveInput X → ∀ E ∈ bulkInterval κ,
      let μ := layerLaw W b .oneBlockOnePort
      let U : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ := fun ω =>
        onePortL b E X ω * (onePortL b E X ω)ᴴ
      (∀ x y, Integrable (fun ω => U ω x y) μ) ∧
        ((((1 + C * onePortDistance b E X + C / (W : ℝ) ^ 2 : ℝ) : ℂ) •
            (1 : Matrix (Fin W) (Fin W) ℂ)) - matrixExpect μ U).PosSemidef

/-!
## 3. Operator moments of the one-port transfer
-/

/-- Operator moments of the one-port transfer.
* `measurable`: `ω ↦ L` is Borel for every `W, b, E, X` (Lean's totalized inverse).
* `moments`: law `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`; `b ∈ (0,1/2)`, `κ > 0` and
  every fixed `p ≥ 1` first; then `C_p, W₀`; then uniformly in `W ≥ W₀`, every passive `X`
  (`-Im X ⪰ 0`, in particular every Hermitian `X`) and `E ∈ bulkInterval κ`:
  `‖ ‖L‖_op ‖_{L^p} ≤ C_p`. (`W₀` depends on `p`: the absorption moments hold for
  `p ≤ ε₁ W`.) Moments of order `0 < p < 1` follow on the probability space.
* Uniformity in `X` with `K` unbounded: `L = -z⁻¹ (K𝒢₁₁) B` and
  `K𝒢₁₁ = I + [(z+E)I - A + z⁻¹BB*] 𝒢₁₁` (valid for every `X`), so only moments of
  `𝒢` and of the Gaussian letters enter; for Hermitian `X` these are
  `GaussianAbsorptionContract`, for passive `X` the Poisson-subharmonic extension of the
  passive bounds. -/
structure OnePortOperatorMomentsContract : Prop where
  measurable : ∀ (W : ℕ) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ), Measurable (onePortL b E X)
  moments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, IsPassiveInput X → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => ‖onePortL b E X ω‖) (ENNReal.ofReal p) (layerLaw W b .oneBlockOnePort) ≤
        ENNReal.ofReal Cp

end BlockBand.Internal.Contracts.LayersOnePort
