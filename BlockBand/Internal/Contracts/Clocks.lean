module

public import BlockBand.Internal.Contracts.TransmissionStatements
public import BlockBand.Statements

/-!
# Statements on physical normalization, Gaussian ratios, matched leads and clocks

This file states, as propositions, the exact Palm formulas for pair and one-block angular
measures, the normalizer comparison with the window prior, the fresh Gaussian ratio and clock
statements, the matched-lead one-mark comparison, the stability of Gaussian clocks under a
change of covariance, and the lower tails of the full clock.

## Conventions

* **Model, ranks, marks.** The exact physical law `model.law`; ranks are zero-based
  (`α : Fin p.N`, the paper's rank is `α.val + 1`); eigenvalues `physicalOrderedEigenvalue`, block masses
  `p_{αk} = physicalOrderedBlockMass`, pair masses `q_{αS} = CoareaPalm.pairMass`. In the one-mark
  statement the marks are those of an arbitrary `FiniteRealization` (its marked configuration
  is a.s. `Σ_α δ_{(u_α, ν_α)}`, so the left side is `E Σ_α w(u_α)Φ(ν_α)` exactly).
* **The reconstructed profile** `p_k(v,e) = ‖P_kLv‖²/(v*Dv)` (`reconBlockMass`) and the clock
  `v*Dv = CoareaPalm.clockSpeed`.
* **The one-block law**: block `k` of dimension `W` is entirely fresh,
  `GUE_W(c/W)`, so the exterior is `(H_R, C)` with `R` the other blocks (`IsBlockSplitting`); the
  angular measure has constant `coareaConstant W (c/W)` and deformation `-C*(H_R - e)⁻¹C`.
* **Windows.** `ρ = semicircleDensity`, `e(u) = E + u/(Nρ(E))`, `w_W(e) = w(Nρ(E)(e - E))`. The
  exact exterior window measure `d𝔪_W = (n/2) w_W(e) Z(e) de dP_ext` (pair) and
  `n w_W(e) Z₀(e) de dP_ext` (one block) live on `ℝ × exterior`; the comparison probability is
  `d𝔭_W = w(u) du dP_ext`. Bounded observables are measurable `F(u, ω)`, `|F| ≤ 1`.
* **Smoothness.** `C^∞` is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (the class `∞` of
  `SpectralWeight`, not the analytic class `ω`).
* **Tests.** "Continuous `Φ : [-1,1]^k → ℝ`" is a continuous function on the cube
  `Fin k → Icc (-1) 1`, evaluated at the coordinatewise clamp of the ratio vector (the ratios lie
  in the cube, so the clamp changes nothing); "`Φ ∈ C_b([0,∞))`" is `Ici 0 →ᵇ ℝ` at the clamp
  `projIci 0`; bounded continuous tests of a pair of clocks are `(Ici 0 × Ici 0) →ᵇ ℝ`.
  "Zero denominators can be assigned arbitrary values" is an arbitrary measurable default.
* **Uniformity.** "`→ 0` uniformly over a class" is `∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀` members,
  `|difference| ≤ ε`, the fixed data (constants, `k`, `K`, test) chosen before `ε`.
* **Critical limits of clocks.** Along a `ClockSequence τ E` (path lengths `n_j`, widths
  `W_j → ∞`, `n_j/W_j → τ`, energies `E_j → E`, no lower bound on `n_j`) the law of a scalar
  clock is a measure on `ℝ`; a *subsequential limit* is a probability measure `μ` on `ℝ` with
  `∫ f dLaw_{φ(j)} → ∫ f dμ` for every bounded continuous `f` along a strictly increasing `φ`;
  "tight" is `∀ ε > 0, ∃ R, ∀ j, Law_j{|x| > R} ≤ ε`. Uniformity on compact `b, E` sets is
  `b ∈ [β, 1/2 - β]`, `E ∈ bulkInterval κ`.
* **Matched leads** (the physical lead-profile theorem): the path of `r = n - 3` blocks with two
  auxiliary ports of diagonal `z_b = boundaryZ b e`; `G_lead = fullInverse b e W r` and
  `U = G_lead V` (`leadResponse`: the port columns of `G_lead`), positions `Fin r ⊕ Fin 2`. Ring
  positions: path position `i` sits at block `i + 2`, port `0` (near, next to position `0`) at
  block `1`, port `1` (far, next to position `r - 1`) at block `n - 1 = r + 2`, block `0` carries
  no mass. (The opposite orientation has the same law: the path law is invariant under reversal.)
  `ν^lead(q) = h*Y(q)h / h*Yh`; on the null event `h*Yh = 0` the profile is `δ_0`. `ℛ_J` with `J`
  uniform on `ZMod n` (the average `n⁻¹ Σ_J`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.Clocks

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix BoundedContinuousFunction

/-!
## 0. Scalars
-/

/-- The fresh pair variance parameter `s = min(b, 1-2b)`. -/
def pairS (p : Parameters) : ℝ := min p.b p.c

/-- The microscopic energy `e(u) = E + u/(Nρ(E))`. -/
def microEnergy (p : Parameters) (E u : ℝ) : ℝ :=
  E + u / ((p.N : ℝ) * Parameters.semicircleDensity E)

/-- The unfolding `u(e) = Nρ(E)(e - E)` (inverse of `microEnergy`). -/
def microCoord (p : Parameters) (E e : ℝ) : ℝ :=
  (p.N : ℝ) * Parameters.semicircleDensity E * (e - E)

/-!
## 1. The pair angular measure and the exact Palm formula
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- The angular sector measure `𝒜_{ℓ,e}[g]` for `g ≥ 0`: `∫dν_𝒩(v) ∫dGUE_{𝒩-1}(t)(G')
c_{𝒩,t} 𝓡(e,v,F(e)) det(U_v*K(e)U_v + G')² 1{N_-(U_v*K(e)U_v + G') = ℓ} g(v)`. -/
def pairSectorFiber (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (e : ℝ) (ℓ : ℕ) (g : (PairSite p i → ℂ) → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
        regressionFactor (pairTime p (pairS p)) e v (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
        Complex.normSq (frameM p i U ω e v G').det) *
      (if negativeCount (frameM p i U ω e v G') = ℓ then 1 else 0) * g v
    ∂(gueMeasure (FrameIndex p) (pairTime p (pairS p))) ∂(projectiveHaar (PairSite p i))

/-- `𝒜_{ℓ,e}[g]` for a real `g` (Bochner integrals). -/
def pairSectorFiberReal (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (e : ℝ) (ℓ : ℕ) (g : (PairSite p i → ℂ) → ℝ) : ℝ := by
  classical
  exact ∫ v, ∫ G',
    coareaConstant (2 * p.W) (pairTime p (pairS p)) *
        regressionFactor (pairTime p (pairS p)) e v (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
        Complex.normSq (frameM p i U ω e v G').det *
      (if negativeCount (frameM p i U ω e v G') = ℓ then 1 else 0) * g v
    ∂(gueMeasure (FrameIndex p) (pairTime p (pairS p))) ∂(projectiveHaar (PairSite p i))

/-- The full unranked mass `Z(e) = 𝒜_e(1) = Σ_ℓ 𝒜_{ℓ,e}(1)` (the sector indicators sum to one). -/
def pairNormalizer (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (e : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p (pairS p)) *
        regressionFactor (pairTime p (pairS p)) e v (physicalCoareaF ω.1 ω.2.1 ω.2.2 e) *
        Complex.normSq (frameM p i U ω e v G').det)
    ∂(gueMeasure (FrameIndex p) (pairTime p (pairS p))) ∂(projectiveHaar (PairSite p i))

/-- The reconstructed block masses `p_k(v,e) = ‖P_k L v‖²/(v*Dv)`. -/
def reconBlockMass (ω : SplitState p i) (e : ℝ) (v : PairSite p i → ℂ) (k : ZMod p.n) : ℝ :=
  (∑ a : Fin p.W, ‖schurLift p i ω.1 ω.2.1 e v (k, a)‖ ^ 2) / clockSpeed p i ω e v

/-- The physical block-mass vector `(p_{αk})_k`. -/
def blockMassVector (H : p.SiteMatrix) (α : Fin p.N) : ZMod p.n → ℝ :=
  fun k => physicalOrderedBlockMass p H α k

/-- The exterior is Hermitian: `H_R` and `V` Hermitian (every exterior realization). -/
def IsHermitianExterior (ω : SplitState p i) : Prop := ω.1.IsHermitian ∧ ω.2.2.IsHermitian

end Pair

/-- An observable `f(e, p)` with compact energy support, bounded by `M`. -/
def IsBoundedCompactEnergy {ι : Type*} (f : ℝ → (ι → ℝ) → ℝ) : Prop :=
  (∃ M : ℝ, ∀ e x, |f e x| ≤ M) ∧ ∃ R : ℝ, ∀ e x, R < |e| → f e x = 0

/-- The exact pair Palm formula.
* `mass`, for measurable `f ≥ 0` of `(e, p)`:
  `E Σ_α q_{αS} f(λ_α, p_α) = E_ext ∫ 𝒜_e[f(e, p(v,e))] de`.
* `massReal`: the same for every bounded measurable real `f` with compact energy support,
  Bochner integrals.
* `index`, for measurable `f ≥ 0` and every rank `α`:
  `E f(λ_α, p_α) = E_ext ∫ 𝒜_{α-1-N_-(H_RR-e), e}[(v*Dv) f(e, p(v,e))] de` (an unattainable
  sector contributes zero).
* `indexReal`: the same for bounded measurable real `f` with compact energy support.
* `upper`: `b` first, then `C_b`; for every `p` with that `b`, every pair,
  frame, Hermitian exterior and *every* real `e` (the explicit formula is the continuous version
  of the density), `0 ≤ Z(e) ≤ C_b 𝒩`, `𝒩 = 2W` (`0 ≤` is automatic for `ℝ≥0∞`). -/
structure ExactPalmContract : Prop where
  mass : ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞, Measurable (Function.uncurry f) →
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (pairMass p i α H) *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          pairSectorFiber p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) ∂volume ∂Pω
  massReal : ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ, Measurable (Function.uncurry f) →
      IsBoundedCompactEnergy f →
      (∫ H, ∑ α : Fin p.N, pairMass p i α H *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          pairSectorFiberReal p i U ω e ℓ (fun v => f e (reconBlockMass p i ω e v)) ∂volume ∂Pω
  index : ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞),
      Measurable (Function.uncurry f) →
      (∫⁻ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiber p i U ω e ℓ
            (fun v => ENNReal.ofReal (clockSpeed p i ω e v) * f e (reconBlockMass p i ω e v))
        ∂volume ∂Pω
  indexReal : ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n)
    (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
    ∀ U, IsPairFrame p i U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ),
      Measurable (Function.uncurry f) → IsBoundedCompactEnergy f →
      (∫ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range (2 * p.W),
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          pairSectorFiberReal p i U ω e ℓ
            (fun v => clockSpeed p i ω e v * f e (reconBlockMass p i ω e v))
        ∂volume ∂Pω
  upper : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
    ∀ (i : ZMod p.n) (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
    IsPairFrame p i U → ∀ ω : SplitState p i, IsHermitianExterior p i ω → ∀ e : ℝ,
      pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W))

/-!
## 2. The exterior window measure and the normalizer theorem
-/

/-- The exterior window measure `d𝔪_W = (n/2) w_W(e) Z(e) de dP_ext(ω)` on `ℝ × exterior`. -/
def pairWindowMeasure (p : Parameters) (i : ZMod p.n)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (Pω : Measure (SplitState p i)) (E : ℝ) (w : ℝ → ℝ) : Measure (ℝ × SplitState p i) :=
  (volume.prod Pω).withDensity fun x =>
    ENNReal.ofReal ((p.n : ℝ) / 2 * w (microCoord p E x.1)) * pairNormalizer p i U x.2 x.1

/-- The comparison probability `d𝔭_W(u, ω) = w(u) du dP_ext(ω)`. -/
def priorWindowMeasure {Ω : Type*} [MeasurableSpace Ω] (Pω : Measure Ω) (w : ℝ → ℝ) :
    Measure (ℝ × Ω) :=
  (volume.withDensity fun u => ENNReal.ofReal (w u)).prod Pω

/-- A fixed window: `w ≥ 0` continuous, compactly supported, `∫ w = 1`. -/
def IsWindow (w : ℝ → ℝ) : Prop :=
  Continuous w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧ ∫ x, w x = 1

/-- The normalizer theorem.
* `tv` (the "in particular"): for every measurable `F(u, ω)` with `|F| ≤ 1` (so also every
  sequence `F_W`, which may depend on the whole reconstructed clock),
  `|∫ F d𝔪_W - ∫ F d𝔭_W| ≤ ε`, `𝔪_W` read in the coordinate `u = Nρ(E)(e - E)`. -/
structure NormalizerContract : Prop where
  l1 : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
      ∀ U, IsPairFrame p i U →
        ∫⁻ x, ENNReal.ofReal |(pairNormalizer p i U x.2 (microEnergy p E x.1)).toReal /
            (2 * p.W * Parameters.semicircleDensity E) - 1| ∂priorWindowMeasure Pω w ≤
          ENNReal.ofReal ε
  tv : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (pairS p) Pω →
      ∀ U, IsPairFrame p i U → ∀ F : ℝ × SplitState p i → ℝ, Measurable F →
      (∀ x, |F x| ≤ 1) →
        |(∫ x, F (microCoord p E x.1, x.2) ∂pairWindowMeasure p i U Pω E w) -
            ∫ x, F x ∂priorWindowMeasure Pω w| ≤ ε

/-!
## 3. One-block versions
-/

section Block

variable (p : Parameters) (k : ZMod p.n)

/-- The one-block exterior `ω = (H_R, C)`, `R` = all blocks but `k`, `C = H_{R,k}`. -/
abbrev BlockState := Matrix (OffBlockSite p k) (OffBlockSite p k) ℂ ×
  Matrix (OffBlockSite p k) (BlockSite p k) ℂ

/-- Index type `Fin (W-1)` of a frame of `v^⊥ ⊂ ℂ^W`. -/
abbrev BlockFrameIndex := Fin (p.W - 1)

/-- Reassembly `H = [[G, C*],[C, H_R]]` with the fresh diagonal block `G = H_kk`. -/
def assembleBlock (ω : BlockState p k) (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    p.SiteMatrix :=
  fun x y =>
    if hx : x.1 = k then
      if hy : y.1 = k then G ⟨x, hx⟩ ⟨y, hy⟩ else star (ω.2 ⟨y, hy⟩ ⟨x, hx⟩)
    else
      if hy : y.1 = k then ω.2 ⟨x, hx⟩ ⟨y, hy⟩ else ω.1 ⟨x, hx⟩ ⟨y, hy⟩

/-- The fresh one-block variance `t = c/W`. -/
def blockTime : ℝ≥0 := Real.toNNReal (p.c / p.W)

/-- The one-block splitting: `Pω ⊗ GUE_W(c/W)` reassembles to the exact physical law. -/
def IsBlockSplitting (model : p.GaussianRingModel) (Pω : Measure (BlockState p k)) : Prop :=
  (Pω.prod (gueMeasure (BlockSite p k) (blockTime p))).map
      (fun x => assembleBlock p k x.1 x.2) = (model.law : Measure p.SiteMatrix)

/-- A measurable orthonormal frame `U_v` of `v^⊥` in the block. -/
def IsBlockFrame (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ) :
    Prop :=
  Measurable U ∧ ∀ v : BlockSite p k → ℂ, l2Norm v = 1 →
    (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0

/-- `F(e) = -C*(H_R - e)⁻¹C` (no residual block: the whole block is fresh). -/
def blockF (ω : BlockState p k) (e : ℝ) : Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  physicalCoareaF ω.1 ω.2 0 e

/-- `M = U_v* F(e) U_v + G' - e`. -/
def blockFrameM (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ)
    (G' : Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ) :
    Matrix (BlockFrameIndex p) (BlockFrameIndex p) ℂ :=
  (U v)ᴴ * blockF p k ω e * U v + G' - (e : ℂ) • 1

/-- One-block angular sector measure `𝒜⁰_{ℓ,e}[g]`, `g ≥ 0`. -/
def blockSectorFiber (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) (g : (BlockSite p k → ℂ) → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant p.W (blockTime p) *
        regressionFactor (blockTime p) e v (blockF p k ω e) *
        Complex.normSq (blockFrameM p k U ω e v G').det) *
      (if negativeCount (blockFrameM p k U ω e v G') = ℓ then 1 else 0) * g v
    ∂(gueMeasure (BlockFrameIndex p) (blockTime p)) ∂(projectiveHaar (BlockSite p k))

/-- One-block sector measure for real `g`. -/
def blockSectorFiberReal (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) (g : (BlockSite p k → ℂ) → ℝ) : ℝ := by
  classical
  exact ∫ v, ∫ G',
    coareaConstant p.W (blockTime p) *
        regressionFactor (blockTime p) e v (blockF p k ω e) *
        Complex.normSq (blockFrameM p k U ω e v G').det *
      (if negativeCount (blockFrameM p k U ω e v G') = ℓ then 1 else 0) * g v
    ∂(gueMeasure (BlockFrameIndex p) (blockTime p)) ∂(projectiveHaar (BlockSite p k))

/-- The full unranked one-block mass `Z₀(e) = 𝒜⁰_e(1)`. -/
def blockNormalizer (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant p.W (blockTime p) *
        regressionFactor (blockTime p) e v (blockF p k ω e) *
        Complex.normSq (blockFrameM p k U ω e v G').det)
    ∂(gueMeasure (BlockFrameIndex p) (blockTime p)) ∂(projectiveHaar (BlockSite p k))

/-- Reconstruction `L v = (v, -T(e)v)` on the ring, `T(e) = (H_R - e)⁻¹C`. -/
def blockLift (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ) : p.Site → ℂ :=
  fun x =>
    if hx : x.1 = k then v ⟨x, hx⟩ else -((physicalCoareaT ω.1 ω.2 e *ᵥ v) ⟨x, hx⟩)

/-- Crossing speed `v*D(e)v`, `D = I + T*T`. -/
def blockClockSpeed (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ) : ℝ :=
  (star v ⬝ᵥ (physicalCoareaD ω.1 ω.2 e *ᵥ v)).re

/-- Reconstructed block masses `p_j(v,e) = ‖P_j L v‖²/(v*Dv)`. -/
def blockReconMass (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ) (j : ZMod p.n) : ℝ :=
  (∑ a : Fin p.W, ‖blockLift p k ω e v (j, a)‖ ^ 2) / blockClockSpeed p k ω e v

/-- The one-block exterior window measure `n w_W(e) Z₀(e) de dP_ext` (prefactor `n`, since
`nW/N = 1`). -/
def blockWindowMeasure (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (Pω : Measure (BlockState p k)) (E : ℝ) (w : ℝ → ℝ) : Measure (ℝ × BlockState p k) :=
  (volume.prod Pω).withDensity fun x =>
    ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E x.1)) * blockNormalizer p k U x.2 x.1

end Block

/-- The exact one-block Palm formula.
* `mass`: for measurable `f ≥ 0`, `E Σ_α p_{αk} f(λ_α, p_α) = E_ext ∫ 𝒜⁰_e[f(e, p(v,e))] de`;
* `massReal`: the same for bounded measurable real `f` with compact energy support;
* `index`: `E f(λ_α, p_α) = E_ext ∫ 𝒜⁰_{α-1-N_-(H_R-e), e}[(v*Dv) f(e, p(v,e))] de`;
* `indexReal`: the same for bounded measurable real `f` with compact energy support;
* `upper`: `b` first, then `C`; `Z₀(e) ≤ C W` for every Hermitian `H_R`, every `C` and real `e`; -/
structure OneBlockPalmContract : Prop where
  splitting_exists : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n),
    ∃ Pω : Measure (BlockState p k), IsBlockSplitting p k model Pω
  frame_exists : ∀ (p : Parameters) (k : ZMod p.n),
    ∃ U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ, IsBlockFrame p k U
  mass : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞, Measurable (Function.uncurry f) →
      (∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiber p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)) ∂volume ∂Pω
  massReal : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ f : ℝ → (ZMod p.n → ℝ) → ℝ, Measurable (Function.uncurry f) →
      IsBoundedCompactEnergy f →
      (∫ H, ∑ α : Fin p.N, physicalOrderedBlockMass p H α k *
          f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiberReal p k U ω e ℓ (fun v => f e (blockReconMass p k ω e v)) ∂volume ∂Pω
  index : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ≥0∞),
      Measurable (Function.uncurry f) →
      (∫⁻ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫⁻ ω, ∫⁻ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiber p k U ω e ℓ
            (fun v => ENNReal.ofReal (blockClockSpeed p k ω e v) *
              f e (blockReconMass p k ω e v))
        ∂volume ∂Pω
  indexReal : ∀ (p : Parameters) (model : p.GaussianRingModel) (k : ZMod p.n)
    (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
    ∀ U, IsBlockFrame p k U → ∀ (α : Fin p.N) (f : ℝ → (ZMod p.n → ℝ) → ℝ),
      Measurable (Function.uncurry f) → IsBoundedCompactEnergy f →
      (∫ H, f (physicalOrderedEigenvalue p H α) (blockMassVector p H α)
        ∂(model.law : Measure p.SiteMatrix)) =
      ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
          (if ℓ + negativeCount (ω.1 - (e : ℂ) • 1) = α.val then 1 else 0) *
          blockSectorFiberReal p k U ω e ℓ
            (fun v => blockClockSpeed p k ω e v * f e (blockReconMass p k ω e v))
        ∂volume ∂Pω
  upper : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
    ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
    IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ,
      blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W)

/-- The one-block normalizer theorem.
* `l1`: `∫ |Z₀(e(u))/(Wρ(E)) - 1| d𝔭_W ≤ ε`;
* `tv`: `|∫ F d𝔪⁰_W - ∫ F d𝔭_W| ≤ ε` for measurable `|F| ≤ 1`. -/
structure OneBlockNormalizerContract : Prop where
  l1 : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (k : ZMod p.n)
      (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
      ∀ U, IsBlockFrame p k U →
        ∫⁻ x, ENNReal.ofReal |(blockNormalizer p k U x.2 (microEnergy p E x.1)).toReal /
            (p.W * Parameters.semicircleDensity E) - 1| ∂priorWindowMeasure Pω w ≤
          ENNReal.ofReal ε
  tv : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (w : ℝ → ℝ),
    IsWindow w → ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W → ∀ (model : p.GaussianRingModel) (k : ZMod p.n)
      (Pω : Measure (BlockState p k)), IsBlockSplitting p k model Pω →
      ∀ U, IsBlockFrame p k U → ∀ F : ℝ × BlockState p k → ℝ, Measurable F →
      (∀ x, |F x| ≤ 1) →
        |(∫ x, F (microCoord p E x.1, x.2) ∂blockWindowMeasure p k U Pω E w) -
            ∫ x, F x ∂priorWindowMeasure Pω w| ≤ ε

/-!
## 4. Fresh Palm ratios and two positive clocks
-/

section Fresh

variable {N : ℕ}

/-- The unranked Palm mass `Z = Σ_ℓ E[w_{ℓ,E}]` of a deterministic deformation. -/
def palmMass (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) : ℝ :=
  ∑ ℓ : Fin N, ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀

/-- The normalized unranked zero-eigenvector Palm law `Â[φ] = Σ_ℓ E[w_{ℓ,E} φ(u_ℓ)] / Z`. -/
def palmExpect (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (φ : (Fin N → ℂ) → ℝ) : ℝ :=
  (∑ ℓ : Fin N, ∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)
      ∂freshTracelessLaw N c₀) / palmMass F c₀ E

/-- Loewner sandwich `-D ⪯ B ⪯ D`. -/
def IsSandwiched (B D : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  B.IsHermitian ∧ (D - B).PosSemidef ∧ (D + B).PosSemidef

/-- `Re Tr(ΓD)`. -/
def traceAgainst (Γ D : Matrix (Fin N) (Fin N) ℂ) : ℝ := (Γ * D).trace.re

end Fresh

/-- The clamped ratio vector `(v*B_jv / v*Dv)_j` in the cube, with an arbitrary default `d(v)`
where `v*Dv = 0`. -/
def ratioCube {ι : Type*} [Fintype ι] {k : ℕ} (B : Fin k → Matrix ι ι ℂ) (D : Matrix ι ι ℂ)
    (d : (ι → ℂ) → Fin k → ℝ) (v : ι → ℂ) : Fin k → Set.Icc (-1 : ℝ) 1 :=
  fun j => Set.projIcc (-1) 1 (by norm_num)
    (if quadForm D v = 0 then d v j else quadForm (B j) v / quadForm D v)

/-- The clamped ratio `v*Cv / v*Dv` in `[0,∞)`, default `d(v)` where `v*Dv = 0`. -/
def ratioHalfLine {ι : Type*} [Fintype ι] (C D : Matrix ι ι ℂ) (d : (ι → ℂ) → ℝ) (v : ι → ℂ) :
    Set.Ici (0 : ℝ) :=
  Set.projIci 0 (if quadForm D v = 0 then d v else quadForm C v / quadForm D v)

/-- A clamped pair of clocks `(x, y)` in `[0,∞)²`. -/
def clockPair (x y : ℝ) : Set.Ici (0 : ℝ) × Set.Ici (0 : ℝ) := (Set.projIci 0 x, Set.projIci 0 y)

/-- **The Gaussian ratios theorem** (used in the one-mark Gaussian theorem, the physical lead
profile theorem and the two-positive-clocks lemma). Fixed first: the
constants `A, c₀, r₀, s₀, v₀` (`FreshConstants`), `k` and a continuous `Φ: [-1,1]^k → ℝ`.
For every
`ε > 0` there is `N₀`; for `N ≥ N₀`, every deformation `F` in `FreshClass F A c₀ E r₀ s₀ v₀`, every
`D ⪰ 0`, Hermitian `B_j` with `-D ⪯ B_j ⪯ D` and `T = Tr(ΓD) > 0` (no norm or condition-number
restriction), every measurable default `d` for zero denominators and every `M` with `MM* = Γ`:
`|Â[Φ(v*B_jv / v*Dv)] - E_g Φ(g*M*B_jMg / g*M*DMg)| ≤ ε`, `g ~ CN(0, I_N)`.
-/
def GaussianRatiosContract : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ (k : ℕ)
    (Φ : C(Fin k → Set.Icc (-1 : ℝ) 1, ℝ)), ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
    FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ (D : Matrix (Fin N) (Fin N) ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ), D.PosSemidef →
      (∀ j, IsSandwiched (B j) D) → 0 < traceAgainst (freshGamma F c₀ E) D →
    ∀ d : (Fin N → ℂ) → Fin k → ℝ, Measurable d →
    ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
      |palmExpect F c₀ E (fun v => Φ (ratioCube B D d v)) -
          ∫ g, Φ (ratioCube B D d (M *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ ε

/-- Two positive clocks under the fresh Palm law.
* `joint`: `|Â[ψ(Nv*Dv/T, Nv*Cv/T)] - E_g ψ(g*M*DMg/T, g*M*CMg/T)| ≤ ε`; -/
structure TwoPositiveClocksPalmContract : Prop where
  joint : ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ K : ℝ,
    ∀ ψ : (Set.Ici (0 : ℝ) × Set.Ici (0 : ℝ)) →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
    FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ D C : Matrix (Fin N) (Fin N) ℂ, D.PosSemidef → C.PosSemidef →
      0 < traceAgainst (freshGamma F c₀ E) D →
      traceAgainst (freshGamma F c₀ E) C ≤ K * traceAgainst (freshGamma F c₀ E) D →
    ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
      let T := traceAgainst (freshGamma F c₀ E) D
      |palmExpect F c₀ E (fun v => ψ (clockPair (N * quadForm D v / T) (N * quadForm C v / T))) -
          ∫ g, ψ (clockPair (quadForm D (M *ᵥ g) / T) (quadForm C (M *ᵥ g) / T))
            ∂circularVectorLaw (Fin N)| ≤ ε
  ratio : ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ K : ℝ,
    ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
    FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ D C : Matrix (Fin N) (Fin N) ℂ, D.PosSemidef → C.PosSemidef →
      0 < traceAgainst (freshGamma F c₀ E) D →
      traceAgainst (freshGamma F c₀ E) C ≤ K * traceAgainst (freshGamma F c₀ E) D →
    ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
    ∀ d : (Fin N → ℂ) → ℝ, Measurable d →
      |palmExpect F c₀ E (fun v => Φ (ratioHalfLine C D d v)) -
          ∫ g, Φ (ratioHalfLine C D d (M *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ ε

/-- **Uniform clock tags, Palm part.**
Fixed first:
`A, c₀, r₀, s₀, v₀` and `Φ ∈ C_b([0,∞))`.
For every
`ε > 0` there is `N₀`; for `N ≥ N₀`, every `F` in the class, every number of tags `q ≥ 1` (which
may grow with `N`), every family `D_j ⪰ 0`, `j < q`, with `D = Σ_j D_j` and `Tr(ΓD) > 0`, every
`M` with `MM* = Γ` and measurable default `d`: with `J` uniform on the `q` tags and `C = qD_J`,
`|q⁻¹ Σ_j Â[Φ(qv*D_jv / v*Dv)] - q⁻¹ Σ_j E_g Φ(qg*M*D_jMg / g*M*DMg)| ≤ ε`.
-/
def UniformClockTagsPalmContract : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ,
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
    FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ (q : ℕ), 0 < q → ∀ Dt : Fin q → Matrix (Fin N) (Fin N) ℂ, (∀ j, (Dt j).PosSemidef) →
      0 < traceAgainst (freshGamma F c₀ E) (∑ j, Dt j) →
    ∀ M : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = freshGamma F c₀ E →
    ∀ d : (Fin N → ℂ) → ℝ, Measurable d →
      |(q : ℝ)⁻¹ * ∑ j, palmExpect F c₀ E (fun v => Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d v)) -
          (q : ℝ)⁻¹ * ∑ j, ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) d (M *ᵥ g))
            ∂circularVectorLaw (Fin N)| ≤ ε

/-!
## 5. The matched-lead one-mark comparison
-/

/-- `U = G_lead V`: the port columns of the inverse of the path of length `r` with its two
matched leads (diagonal `z_b` at the auxiliary ports), at real energy `e`. -/
def leadResponse (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Matrix (FullSite W r) (Fin 2 × Fin W) ℂ :=
  fun x y => fullInverse b e W r ω x (Sum.inr y)

/-- The mass `h*U*P_xUh = ‖P_xUh‖²` of the response at position `x ∈ Fin r ⊕ Fin 2`. -/
def leadPositionMass (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ)
    (x : Fin r ⊕ Fin 2) : ℝ :=
  let ψ := leadResponse b e W r ω *ᵥ h
  match x with
  | Sum.inl i => ∑ a : Fin W, ‖ψ (Sum.inl (i, a))‖ ^ 2
  | Sum.inr j => ∑ a : Fin W, ‖ψ (Sum.inr (j, a))‖ ^ 2

/-- Ring block of a matched-lead position (path of `r = n - 3` blocks): path position `i` at
block `i + 2`, near port at block `1`, far port at block `r + 2 = n - 1`. -/
def leadRingBlock (r : ℕ) : Fin r ⊕ Fin 2 → ℕ
  | Sum.inl i => i.val + 2
  | Sum.inr j => if j = 0 then 1 else r + 2

/-- The rotated matched-lead profile `ℛ_J ν^lead_W` on the circle: mass
`h*U*P_xUh / h*Yh` at `(block(x) + J)/n`; `δ_0` on the null event where it is not a
probability measure. -/
def leadProfile (b e : ℝ) (n W : ℕ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ) (J : ℕ) :
    MassProfile := by
  classical
  let r := n - 3
  let tot := ∑ x : Fin r ⊕ Fin 2, leadPositionMass b e W r ω h x
  let μ : Measure Torus := ∑ x : Fin r ⊕ Fin 2,
    ENNReal.ofReal (leadPositionMass b e W r ω h x / tot) •
      Measure.dirac (QuotientAddGroup.mk ((((leadRingBlock r x + J) % n : ℕ) : ℝ) / n))
  exact if hμ : IsProbabilityMeasure μ then ⟨μ, hμ⟩ else ⟨Measure.dirac 0, inferInstance⟩

/-- The physical one-mark statistic `E Σ_α w(u_α) Φ(ν_α)` of a realization at energy `E`. -/
def physicalOneMark {p : Parameters} (R : FiniteRealization p) (E : ℝ) (w : ℝ → ℝ)
    (Φ : MassProfile →ᵇ ℝ) : ℝ :=
  ∫ H, ∫ x, w x.1 * Φ x.2 ∂(R.spectral.markedConfig E H).marked.measure
    ∂(R.model.law : Measure p.SiteMatrix)

/-- The matched-lead side `∫ w(u) E Φ(ℛ_J ν^lead_W(e(u))) du` (path prior, `h`, uniform `J`). -/
def leadOneMark (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (Φ : MassProfile →ᵇ ℝ) : ℝ :=
  ∫ u, w u * ∫ x, (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n,
      Φ (leadProfile p.b (microEnergy p E u) p.n p.W x.1 x.2 J)
    ∂((growthPathLaw p.W p.b).prod (circularVectorLaw (Fin 2 × Fin p.W)))

/-- **The physical lead profile theorem.**
Fixed:
`b ∈ (0,1/2)`, a bulk energy `E` (`-2 < E < 2`), a smooth compactly supported (possibly
signed) spectral weight `w` and a bounded continuous functional `Φ` on `𝒫(𝕋)`.
For every `τ > 0`,
every critical sequence `n/W → τ` and every sequence of realizations,
`E Σ_α w(u_α) Φ(ν_α) - ∫ w(u) E Φ(ℛ_J ν^lead_W(e(u))) du → 0`, `e(u) = E + u/(Nρ(E))`, the right
expectation over the independent path and port prior (path of `n - 3` blocks, two matched
leads, `h ~ CN(0, I_{2W})`, `J` uniform).
-/
def PhysicalLeadProfileContract : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → HasCompactSupport w → ∀ Φ : MassProfile →ᵇ ℝ,
    ∀ (τ : ℝ), 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      Tendsto (fun j => physicalOneMark (R j) E w Φ - leadOneMark (s.parameters b hb hb' j) E w Φ)
        atTop (𝓝 0)

/-!
## 6. Stability of Gaussian clocks under a relative change of covariance
-/

/-- **Covariance stability** (Step 4 of the proof of the two-positive-clocks lemma, as used in the
physical lead profile theorem and the microscopic tag comparison: "by the last paragraph of the
two-positive-clocks lemma"). A purely Gaussian, dimension-free clause:
fixed first `K`, a bounded continuous test `ψ` of two clocks and `Φ ∈ C_b([0,∞))`; for every
`ε > 0` there is `ω₀ > 0`; for every `N`, `Γ₀ ⪰ 0` and `Γ` with
`(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `0 ≤ ω ≤ ω₀`, every `D, C ⪰ 0` with `T₀ = Tr(Γ₀D) > 0`,
`Tr(Γ₀C) ≤ KT₀`, every `M, M₀` with `MM* = Γ`, `M₀M₀* = Γ₀`, and measurable default `d`, the
clocks of `q = Mg` and `q₀ = M₀g` (`g ~ CN(0,I_N)`), both normalized by `T₀`, satisfy
`|E ψ(q*Dq/T₀, q*Cq/T₀) - E ψ(q₀*Dq₀/T₀, q₀*Cq₀/T₀)| ≤ ε` and
`|E Φ(q*Cq/q*Dq) - E Φ(q₀*Cq₀/q₀*Dq₀)| ≤ ε`. Combined with `TwoPositiveClocksPalmContract`
this is the statement that the assertion is stable under a relative change of the covariance.
The ratio clause is stated for one ratio; the `k`-ratio form used in the physical lead profile
theorem follows by the same coupling.
When chaining with `joint`, the normalizations `Tr(ΓD)` and `Tr(Γ₀D)` differ by the
factor `1 + O(ω)`.
-/
def ClockCovarianceStabilityContract : Prop :=
  ∀ (K : ℝ) (ψ : (Set.Ici (0 : ℝ) × Set.Ici (0 : ℝ)) →ᵇ ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ),
    ∀ ε : ℝ, 0 < ε → ∃ ω₀ : ℝ, 0 < ω₀ ∧
    ∀ (N : ℕ) (Γ₀ Γ : Matrix (Fin N) (Fin N) ℂ) (ω : ℝ), 0 ≤ ω → ω ≤ ω₀ → Γ₀.PosSemidef →
      (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef → (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef →
    ∀ D C : Matrix (Fin N) (Fin N) ℂ, D.PosSemidef → C.PosSemidef →
      0 < traceAgainst Γ₀ D → traceAgainst Γ₀ C ≤ K * traceAgainst Γ₀ D →
    ∀ M M₀ : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = Γ → M₀ * M₀ᴴ = Γ₀ →
    ∀ d : (Fin N → ℂ) → ℝ, Measurable d →
      let T := traceAgainst Γ₀ D
      |(∫ g, ψ (clockPair (quadForm D (M *ᵥ g) / T) (quadForm C (M *ᵥ g) / T))
            ∂circularVectorLaw (Fin N)) -
          ∫ g, ψ (clockPair (quadForm D (M₀ *ᵥ g) / T) (quadForm C (M₀ *ᵥ g) / T))
            ∂circularVectorLaw (Fin N)| ≤ ε ∧
      |(∫ g, Φ (ratioHalfLine C D d (M *ᵥ g)) ∂circularVectorLaw (Fin N)) -
          ∫ g, Φ (ratioHalfLine C D d (M₀ *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ ε

/-!
## 7. Lower tails of the full clock
-/

/-- The full two-input interior clock `Y = 𝒰_n*𝒰_n` of the path of length `n`. -/
def fullClock (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω

/-- The joint law of the path and an independent `h ~ CN(0, I_{2W})`. -/
def probedClockLaw (W : ℕ) (b : ℝ) : Measure (GrowthPath W × (Fin 2 × Fin W → ℂ)) :=
  (growthPathLaw W b).prod (circularVectorLaw (Fin 2 × Fin W))

/-- The law on `ℝ` of a scalar clock `X(ω, h)`. -/
def clockLaw (W : ℕ) (b : ℝ) (X : GrowthPath W × (Fin 2 × Fin W → ℂ) → ℝ) : Measure ℝ :=
  (probedClockLaw W b).map X

/-- `μ` is a subsequential weak limit of the measures `ν j` on `ℝ`. -/
def IsSubsequentialLimit (ν : ℕ → Measure ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂ν (φ j)) atTop (𝓝 (∫ x, f x ∂μ))

/-- Tightness of a sequence of measures on `ℝ`. -/
def IsTightSeq (ν : ℕ → Measure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ j, ν j {x | R < |x|} ≤ ENNReal.ofReal ε

/-- A sequence of path lengths `n_j` and widths `W_j → ∞` with `n_j/W_j → τ` and energies
`E_j → E` (the constants are uniform on compact energy sets, and the clocks are used at the
moving energies `e(u)`). No lower bound on `n_j` is imposed (the path length `r = n - 3` is
used). -/
structure ClockSequence (τ E : ℝ) where
  n : ℕ → ℕ
  W : ℕ → ℕ
  energy : ℕ → ℝ
  W_pos : ∀ j, 0 < W j
  width_tendsto : Tendsto W atTop atTop
  ratio_tendsto : Tendsto (fun j => (n j : ℝ) / (W j : ℝ)) atTop (𝓝 τ)
  energy_tendsto : Tendsto energy atTop (𝓝 E)

/-- `T_W = W⁻²h*Yh` along a clock sequence (energy `E_j`). -/
def scaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ) → ℝ :=
  fun x => quadForm (fullClock b (s.energy j) (s.W j) (s.n j) x.1) x.2 / (s.W j : ℝ) ^ 2

/-- Tightness and negative moments of the scaled clock.
* `tight`: for every `b ∈ (0,1/2)`, `τ > 0`, bulk `E` and clock sequence (energies `E_j → E`),
  the laws of `T_W` are tight.
* `negative`: `β, κ, T₀` and `p > 0` first; then `C = C_{p,T₀}`; for every such `b`, `τ`, limit
  energy `E ∈ bulkInterval κ`, clock sequence with eventually all `E_j ∈ bulkInterval κ` and subsequential
  limit law `μ` of `T_W`: `μ(-∞, 0] = 0` (the limit is strictly positive) and
  `E T^{-p} ≤ C τ^{-p}`. No prelimit inverse moment is asserted. -/
structure NegativeClockContract : Prop where
  tight : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ τ : ℝ, 0 < τ →
    ∀ s : ClockSequence τ E, IsTightSeq (fun j => clockLaw (s.W j) b (scaledClock b s j))
  negative : ∀ β κ T₀ p : ℝ, 0 < β → β < 1 / 4 → 0 < κ → 0 < T₀ → 0 < p → ∃ C : ℝ,
    ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ →
    ∀ (s : ClockSequence τ E), (∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ) → ∀ μ : Measure ℝ,
      IsSubsequentialLimit (fun j => clockLaw (s.W j) b (scaledClock b s j)) μ →
        μ (Set.Iic 0) = 0 ∧ ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ ≤ ENNReal.ofReal (C * τ ^ (-p))

/-- `A_W = Tr Y/(nW)` along a clock sequence. -/
def traceClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) (ω : GrowthPath (s.W j)) : ℝ :=
  (fullClock b (s.energy j) (s.W j) (s.n j) ω).trace.re / ((s.n j : ℝ) * s.W j)

/-- `M_W = h*Yh/(nW) = T_W/τ_W` along a clock sequence. -/
def rescaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ) → ℝ :=
  fun x => quadForm (fullClock b (s.energy j) (s.W j) (s.n j) x.1) x.2 / ((s.n j : ℝ) * s.W j)

/-- Negative moments and the small-ball bound of the rescaled clock.
* `limit`: every subsequential limit law `μ` of `M_W` has `μ(-∞,0] = 0` and `E M^{-p} ≤ C`;
* `smallBall`: for `0 < ε < 1`,
  `limsup_W P(A_W ≤ ε) ≤ C ε^{p/2}/(1 - √ε)` (the width limit precedes the small-ball limit). -/
def ClockSmallBallContract : Prop :=
  ∀ β κ T₀ p : ℝ, 0 < β → β < 1 / 4 → 0 < κ → 0 < T₀ → 0 < p → ∃ C : ℝ,
    ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ, ∀ τ : ℝ, 0 < τ → τ ≤ T₀ →
    ∀ s : ClockSequence τ E, (∀ᶠ j in atTop, s.energy j ∈ bulkInterval κ) →
      (∀ μ : Measure ℝ,
        IsSubsequentialLimit (fun j => clockLaw (s.W j) b (rescaledClock b s j)) μ →
          μ (Set.Iic 0) = 0 ∧ ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ ≤ ENNReal.ofReal C) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        limsup (fun j => growthPathLaw (s.W j) b {ω | traceClock b s j ω ≤ ε}) atTop ≤
          ENNReal.ofReal (C * ε ^ (p / 2) / (1 - Real.sqrt ε))

end BlockBand.Internal.Contracts.Clocks
