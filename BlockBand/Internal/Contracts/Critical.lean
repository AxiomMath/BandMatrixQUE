module

public import BlockBand.Internal.Contracts.Layers

/-!
# Common-port mean, point density, collar kernel and exact boundary mean

This file states, as propositions, the common-port mean lemma, the point-density lemma for a
fresh Gaussian block, the bounds on the expected collar boundary kernel, and the exact boundary
mean of the collar.

## Conventions

* **Energies.** "A compact bulk energy range" is `bulkInterval κ` for a fixed `κ > 0`
  (every compact subset of `(-2,2)` lies in one of these).
* **Asymptotic notation.** `O_op(δ + W⁻²)` is an operator-norm bound `C(δ + W⁻²)` with `C`
  fixed with the model constants (`b`, `κ`). The statement is asymptotic in `W` and uses
  moments of the fresh resolvent, which the Gaussian absorption lemma supplies only for
  `p ≤ ε₁ W`; each clause therefore holds for `W ≥ W₀`, `W₀` chosen with the constants.
  "Every fixed finite `p`" is `∀ p, ∃ C_p, W₀(p)`, `p` chosen after `b, κ` and before `W` and
  all deterministic data.
* **Norms.** Matrix norms are the Euclidean operator norm (`Matrix.Norms.L2Operator`);
  vector norms are `CoareaPalm.l2Norm`; matrix expectations are entrywise (`matrixExpect`).
  Conditional `L^p` norms are `eLpNorm` over the fresh law.
* **Boundary expectations**. For `Y ≻ 0`, `Ur` is a
  strict contraction and `E 𝒫(Ur)` is an ordinary expectation; the statement gives the bound
  for it. For `Y ⪰ 0` ("at unitary boundary points … bounds for the limiting expected kernel
  under a radial regulator"), the statement gives the bound for the radially regulated
  expectations `E 𝒫(tUr)` as `t ↑ 1`, in the form "for every `ε > 0` the bound plus `ε` holds for
  all `t` close to one". This is the bound for the limiting expected kernel without asserting
  that the limit exists, and never replaces it by the unregularized (possibly a.s. zero) kernel.
* **Height and shift**. "Every physical collar diagonal has a
  common positive height `ν ≤ ν₀` and a sufficiently small common real shift" is the collar
  with diagonals `A_j - (e + s) + iν`, `G - (e + s) + iν` (the sign that keeps `Y ⪰ 0`-type
  dissipation, so `U` stays a contraction), for `|s| ≤ s₀`, `0 ≤ ν ≤ ν₀`, `s₀, ν₀ > 0` fixed
  with the constants; `s = ν = 0` is the theorem's main case. `a, z_b` stay at energy `e`.
* **Loewner order.** `M ⪯ cI` is `(c I - M).PosSemidef` (complex matrices); `o_op`, `O_op`
  bounds are operator-norm bounds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.Critical

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The common-port mean lemma
-/

/-- `γ = (1-b)/c`, `c = 1-2b`. -/
def commonPortGamma (b : ℝ) : ℝ := (1 - b) / (1 - 2 * b)

/-- `K = z_b I - X`, `z_b = a⁻¹ + b a`. -/
def matchedLeadK (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X

/-- The common-port resolvent `𝒢 = [[A - e - X, B], [B*, z₀ I]]⁻¹`. -/
def commonPortResolvent (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
  layerResolvent .common e (commonZ b e) X ω

/-- `L = K 𝒢₁₂`, rectangular from the `W`-dimensional common port to the two
`W`-dimensional old ports. -/
def commonPortL (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ :=
  matchedLeadK b e X * (commonPortResolvent b e X ω).toBlocks₁₂

/-- `H = 𝒢₂₂`. -/
def commonPortH (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
  (commonPortResolvent b e X ω).toBlocks₂₂

/-- `LL*` (`2W × 2W`). -/
def commonPortLL (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  commonPortL b e X ω * (commonPortL b e X ω)ᴴ

/-- The common-port mean lemma.
* `mean`: there are `δ₀ > 0` (the fixed small regularity domain `δ ≤ δ₀`), `C` and `W₀`; for
  `W ≥ W₀`, every Hermitian `X` and `e ∈ bulkInterval κ` with `δ = matchedDistance b e X ≤ δ₀`,
  the entries of `LL*` are integrable and `‖E(LL* | X) - γ I_{2W}‖ ≤ C(δ + W⁻²)`.
* `fluctuation`: for every fixed `p ≥ 2` there are `C_p, W₀`; for `W ≥ W₀`, every Hermitian `X`,
  `e ∈ bulkInterval κ` and arbitrary old vectors `u, v ∈ ℂ^{2W}`:
  `‖u*{LL* - E(LL* | X)}v‖_{p|X} ≤ C_p W^{-1/2} ‖u‖ ‖v‖`.
* `moments`: for every fixed `p ≥ 1` there are `C_p, W₀`; for `W ≥ W₀`, every Hermitian `X`
  (uniformly in the old deformation) and `e ∈ bulkInterval κ`: `‖ ‖L‖ ‖_{p|X} ≤ C_p` and
  `‖ ‖H‖ ‖_{p|X} ≤ C_p` (operator norms).
The paper restricts only the mean display to the regularity domain. The fluctuation and moment
bounds hold uniformly in the Hermitian deformation (`L = -K𝒢₁₁B z₀⁻¹` and
`K𝒢₁₁ = I + [z_b + e - A + z₀⁻¹BB*]𝒢₁₁` involve no `X` outside `𝒢₁₁`), so they are stated for
every Hermitian `X`. -/
structure CommonPortMeanContract : Prop where
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (δ₀ C : ℝ) (W₀ : ℕ), 0 < δ₀ ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        X.IsHermitian → ∀ e ∈ bulkInterval κ, matchedDistance b e X ≤ δ₀ →
          (∀ x y, Integrable (fun ω => commonPortLL b e X ω x y) (layerLaw W b .common)) ∧
          ‖matrixExpect (layerLaw W b .common) (commonPortLL b e X) -
              ((commonPortGamma b : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤
            C * (matchedDistance b e X + 1 / (W : ℝ) ^ 2)
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 2 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ, ∀ u v : Fin 2 × Fin W → ℂ,
        eLpNorm (fun ω => star u ⬝ᵥ
            ((commonPortLL b e X ω - matrixExpect (layerLaw W b .common) (commonPortLL b e X)) *ᵥ v))
          (ENNReal.ofReal p) (layerLaw W b .common) ≤
        ENNReal.ofReal (C * (W : ℝ) ^ (-(1 : ℝ) / 2) * l2Norm u * l2Norm v)
  moments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ e ∈ bulkInterval κ,
        eLpNorm (fun ω => ‖commonPortL b e X ω‖) (ENNReal.ofReal p) (layerLaw W b .common) ≤
            ENNReal.ofReal C ∧
          eLpNorm (fun ω => ‖commonPortH b e X ω‖) (ENNReal.ofReal p) (layerLaw W b .common) ≤
            ENNReal.ofReal C

/-!
## 2. The point-density lemma
-/

/-- The normalized expected eigenvalue measure `N⁻¹ Σ_ℓ Law(λ_ℓ(F + G_c))` of `F + G_c`,
`G_c ~ GUE_N(c/N)` (multiplicity counted, increasing eigenvalues). -/
def freshMeanEigenvalueMeasure (N : ℕ) (c : ℝ) (F : Matrix (Fin N) (Fin N) ℂ) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ ℓ : Fin N,
    (gueMeasure (Fin N) (Real.toNNReal (c / N))).map (fun G => freshEigenvalue (F + G) ℓ)

/-- **The point-density lemma** (in the setting of the fresh regularity condition centred at
`x`). Fixed first: the norm exponent `A` and the constants `0 < c < 1`, `r₀, s₀, v₀ > 0`,
`s₀ < c/2` (`FreshConstants`).
Then a deterministic sequence `ε_N → 0` depending only on
these.
Uniformly in `N ≥ 1`, Hermitian `F` with `‖F‖ ≤ N^A` and real `x` such that `F` is regular
at `(c, x)` (`v₀ ≤ Im m_s(y+iη) ≤ v₀⁻¹` for `s ∈ [c-s₀,c]`, `|y-x| ≤ r₀`, `0 ≤ η ≤ 1`): the
normalized expected eigenvalue measure of `F + G_c`, `G_c ~ GUE_N(c/N)`, has a continuous density,
and every continuous density `ρ_{F,c}` satisfies `|ρ_{F,c}(x) - r_{F,c}(x)| ≤ ε_N`,
`r_{F,c}(x) = π⁻¹ Im m_{F,c}(x)` (boundary value of the scalar Dyson equation).
Polynomially
unbounded `F` is allowed; no limiting deformation measure is assumed.
The lemma's setting fixes `s₀ > 0`;
`FreshConstants` also asks `s₀ < c/2` (from the fresh regularity condition).
This adds no hypothesis: regularity with `s₀` implies regularity
with `min(s₀, c/4)`, and the conclusion does not involve `s₀`.
-/
def PointDensityContract : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (x : ℝ), FreshClass F A c x r₀ s₀ v₀ →
        (∃ ρ : ℝ → ℝ, Continuous ρ ∧
          freshMeanEigenvalueMeasure N c F = volume.withDensity (fun y => ENNReal.ofReal (ρ y))) ∧
        ∀ ρ : ℝ → ℝ, Continuous ρ →
          freshMeanEigenvalueMeasure N c F = volume.withDensity (fun y => ENNReal.ofReal (ρ y)) →
            |ρ x - (freshDyson F c x).im / Real.pi| ≤ ε N

/-!
## 3. The collar and its boundary kernel
-/

/-- Fresh variables of the three-block collar: the common-port layer (end diagonals `A₁, A₂`
and bonds `B₁, B₂`) and the middle diagonal `G` on the port index. -/
abbrev CollarSample (W : ℕ) := LayerSample W .common × Matrix (PortSite W .common) (PortSite W .common) ℂ

/-- Law of the collar: `A_j, G ~ GUE_W(c/W)`, bonds of variance `b/W`, all independent. -/
def collarLaw (W : ℕ) (b : ℝ) : Measure (CollarSample W) :=
  (layerLaw W b .common).prod (gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)))

/-- The collar's diagonal spectral parameter `e + s - iν` (diagonals `A_j - (e+s) + iν`,
`G - (e+s) + iν`; `s = ν = 0` is the theorem's main case, the unshifted collar at zero height).
The sign `+iν` is the dissipation convention of the old responses (`Y ⪰ 0`): consumers insert
sources and heights as `+iκ P_C/W²` in the old interior matrix, so that
`Im K_c ⪰ ν I` and `U` stays a contraction. -/
def collarShift (e s ν : ℝ) : ℂ := ((e + s : ℝ) : ℂ) - (ν : ℂ) * Complex.I

/-- Terminating reaction `K_c = A - e - ξ - B(G - e)⁻¹B*` on the two outer ports, `ξ = Re z_b`, with the common height and shift. -/
def collarReaction (b e s ν : ℝ) {W : ℕ} (ω : CollarSample W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  blockDiag ω.1.1 - (collarShift e s ν + ((boundaryZ b e).re : ℂ)) • 1 -
    bondMatrix .common ω.1.2 * (ω.2 - collarShift e s ν • 1)⁻¹ * (bondMatrix .common ω.1.2)ᴴ

/-- Collar scattering matrix `U = I - 2iη(K_c + iη)⁻¹`, `η = Im z_b`. -/
def collarScattering (b e s ν : ℝ) {W : ℕ} (ω : CollarSample W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - (2 * ((boundaryZ b e).im : ℂ) * Complex.I) •
    (collarReaction b e s ν ω + (((boundaryZ b e).im : ℂ) * Complex.I) • 1)⁻¹

/-- Old scattering matrix `r = I - 2iη(z_b - X)⁻¹`. -/
def oldScattering (b e : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - (2 * ((boundaryZ b e).im : ℂ) * Complex.I) • (boundaryZ b e • 1 - X)⁻¹

/-- Conductance `g = Tr(I - r*r)` (real for every `r`; nonnegative for contractions). -/
def conductance {ι : Type*} [Fintype ι] [DecidableEq ι] (r : Matrix ι ι ℂ) : ℝ :=
  (1 - rᴴ * r).trace.re

/-- Imaginary part `Im K = (K - K*)/(2i)`. -/
def imPart {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 * Complex.I)⁻¹ • (K - Kᴴ)

/-- Positive Poisson kernel `𝒫(V) = (I - V)⁻¹ + (I - V*)⁻¹ - I`. -/
def poissonKernel {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 - V)⁻¹ + (1 - Vᴴ)⁻¹ - 1

/-- The expected collar kernel `E_collar 𝒫(t U r)` at radial regulator `t` (`t = 1`: no
regulator). -/
def expectedCollarKernel (b e s ν t : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  matrixExpect (collarLaw W b)
    (fun ω => poissonKernel ((t : ℂ) • (collarScattering b e s ν ω * oldScattering b e X)))

/-- The entries of `𝒫(tUr)` are integrable over the collar. -/
def CollarKernelIntegrable (b e s ν t : ℝ) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Prop :=
  ∀ x y, Integrable (fun ω => poissonKernel ((t : ℂ) •
    (collarScattering b e s ν ω * oldScattering b e X)) x y) (collarLaw W b)

/-- The bounds of the collar-kernel theorem with explicit constants `d_*, C, s₀, ν₀, W₀`:
for `W ≥ W₀`, `e ∈ bulkInterval κ`, `|s| ≤ s₀`, `0 ≤ ν ≤ ν₀`:
* `strict`: for `Y = -Im X ≻ 0`: the kernel entries are integrable, `E 𝒫(Ur) ⪯ C√W I`, and
  `E 𝒫(Ur) ⪯ C(1+g)I` when `d(X) ≤ d_*/2`;
* `boundary`: for `Y ⪰ 0` and every `ε > 0`, for all radial regulators `t < 1` close to one the
  same two bounds hold for `E 𝒫(tUr)` up to `+ε`. -/
structure CollarKernelBounds (b κ dstar C s₀ ν₀ : ℝ) (W₀ : ℕ) : Prop where
  strict : ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
    ∀ ν ∈ Set.Icc 0 ν₀, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-imPart X).PosDef →
      CollarKernelIntegrable b e s ν 1 X ∧
      (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          expectedCollarKernel b e s ν 1 X).PosSemidef ∧
      (matchedDistance b e X ≤ dstar / 2 →
        (((C * (1 + conductance (oldScattering b e X)) : ℝ) : ℂ) •
            (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          expectedCollarKernel b e s ν 1 X).PosSemidef)
  boundary : ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
    ∀ ν ∈ Set.Icc 0 ν₀, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-imPart X).PosSemidef →
      ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℝ, t₀ < 1 ∧ ∀ t ∈ Set.Ioo t₀ 1,
        CollarKernelIntegrable b e s ν t X ∧
        (((C * Real.sqrt W + ε : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            expectedCollarKernel b e s ν t X).PosSemidef ∧
        (matchedDistance b e X ≤ dstar / 2 →
          (((C * (1 + conductance (oldScattering b e X)) + ε : ℝ) : ℂ) •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            expectedCollarKernel b e s ν t X).PosSemidef)

/-- **The collar kernel theorem** (`d_*` is the constant of the collar regularity condition).
Law: the finite Gaussian collar `collarLaw W b`, independent of the deterministic old
response `X = X_h - iY`, `Y ⪰ 0` (an independent `X` by Fubini).
`b ∈ (0,1/2)` and the bulk
range `bulkInterval κ` first; then `d_*, s₀, ν₀ > 0`, a constant `C` and `W₀`; uniformly in `W ≥ W₀`,
`e ∈ bulkInterval κ`, every such `X`, the common height `0 ≤ ν ≤ ν₀` and shift `|s| ≤ s₀`:
`E_collar 𝒫(Ur) ⪯ C(1+g)I` when `d(X) ≤ d_*/2`, and `E_collar 𝒫(Ur) ⪯ C√W I` always, with the
boundary interpretation (radial regulator) for `Y ⪰ 0` (`CollarKernelBounds`).
No norm bound
on `X` is assumed.
The threshold `W₀` follows the asymptotic convention of the layer
contracts (the universal bound itself holds for every `W`).
Where `I - Ur` is a.s. invertible
(e.g.
`ν > 0`), Fatou turns the boundary clause into the ordinary-expectation bound.
A use
needing a uniform radial bound applies `strict` at the Cayley inverse `z_b - 2iη(1 - tr)⁻¹` of
`tr`, using `g(tr) ≤ g(r) + 2W(1-t²)`.
-/
def CollarKernelContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C s₀ ν₀ : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 < s₀ ∧ 0 < ν₀ ∧
      CollarKernelBounds b κ dstar C s₀ ν₀ W₀

/-- **The exact boundary mean theorem.** Setting and law of
`CollarKernelContract` at zero height and shift.
`b ∈ (0,1/2)` and `bulkInterval κ` first; then
a deterministic sequence `ε_W → 0` (depending only on these ranges and the fixed fresh cutoffs),
constants `C`, `d₁ > 0` (the scalar regime "`d(X) → 0`") and `W₀`; uniformly for `W ≥ W₀`,
`e ∈ bulkInterval κ` and deterministic old responses with `d(X) ≤ d₁`:
`‖E_collar 𝒫(Ur) - I‖ ≤ C{d(X) + ε_W + W^{-1/8} + g W^{-1/4}}` (operator norm).
For `Y ≻ 0` this is
the ordinary expectation; for `Y ⪰ 0` the bound plus any `δ > 0` holds for `E 𝒫(tUr)` for all
radial regulators `t < 1` close to one (the boundary interpretation of the collar kernel
theorem).
The explicit error is asserted for every `g`;
`g = O(1)` is needed only for the `o(1)` form: with
`d(X) → 0` and `g = O(1)` this is `E 𝒫(Ur) = I + o_op(1)`.
-/
def ExactBoundaryMeanContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (ε : ℕ → ℝ) (C d₁ : ℝ) (W₀ : ℕ), Tendsto ε atTop (𝓝 0) ∧ 0 < d₁ ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, matchedDistance b e X ≤ d₁ →
        let err : ℝ := C * (matchedDistance b e X + ε W + (W : ℝ) ^ (-(1 : ℝ) / 8) +
          conductance (oldScattering b e X) * (W : ℝ) ^ (-(1 : ℝ) / 4))
        ((-imPart X).PosDef →
          CollarKernelIntegrable b e 0 0 1 X ∧ ‖expectedCollarKernel b e 0 0 1 X - 1‖ ≤ err) ∧
        ((-imPart X).PosSemidef → ∀ δ : ℝ, 0 < δ → ∃ t₀ : ℝ, t₀ < 1 ∧ ∀ t ∈ Set.Ioo t₀ 1,
          CollarKernelIntegrable b e 0 0 t X ∧ ‖expectedCollarKernel b e 0 0 t X - 1‖ ≤ err + δ)

end BlockBand.Internal.Contracts.Critical
