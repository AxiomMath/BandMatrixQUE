module

public import BlockBand.Palm.MomentFlow.BridgeLaw
public import BlockBand.PointProcess.Specifications

/-!
# The relative mixed-vector theorem: statement

Definitions only. The main clause `RelativeMixedVectorsComparison` (the conditional comparison
of the marks `z_ℓ = √N e^{iθ_ℓ} V^* u_ℓ` of finitely many labels with independent circular
Gaussians, conditionally on good eigenvalue paths), the decorated-sine clause
`RelativeMixedVectorsDecorated`, and their conjunction `RelativeMixedVectorsStatement`.

The matrix Brownian flow is `H_σ = F + G_σ`, `G_σ ~ GUE_N(σ/N)` (`flowLaw`, `flowMatrix`,
`flowEigenvalue`); `pathSigma` is the σ-algebra of the eigenvalue path; `freshGamma` is
`Γ = c|F - E - c m_c(E)|^{-2}` and `freshDyson` is `m_{F,s}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

/-!
## Phases, marks and the Gaussian mark law
-/

/-- Law of one uniform phase `e^{2πiθ}`, `θ ~ Unif[0,1]` (a probability measure on the unit
circle of `ℂ`). -/
def phaseLaw : Measure ℂ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map
    (fun θ : ℝ => Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I))

/-- `N` independent uniform phases, one per eigenvector label. -/
def phaseVectorLaw (N : ℕ) : Measure (Fin N → ℂ) :=
  Measure.pi fun _ : Fin N => phaseLaw

/-- An array of `k` marks in `ℂ^r` (one `r`-vector per tested label). -/
abbrev MarkArray (k r : ℕ) := Fin k → Fin r → ℂ

/-- `k` independent standard circular Gaussian `r`-vectors. -/
def gaussianMarkLaw (k r : ℕ) : Measure (MarkArray k r) :=
  Measure.pi fun _ : Fin k => circularVectorLaw (Fin r)

/-- The mark `z_ℓ = √N e^{iθ_ℓ} V^* u_ℓ` of the rank-`ℓ` eigenvector `u_ℓ` of `K`, with phases
`θ`. -/
def relativeMark {N r : ℕ} (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (θ : Fin N → ℂ) (ℓ : Fin N) : Fin r → ℂ :=
  ((Real.sqrt N : ℝ) : ℂ) • θ ℓ • (Vᴴ *ᵥ freshEigenvector K ℓ)

/-- Bounded `C²` class with bound `K` on a real normed space: `f` is `C²` and
`|f|, ‖Df‖, ‖D²f‖ ≤ K` everywhere (real derivatives on `ℂ^{rk}` viewed as `ℝ^{2rk}`, sup norm on
the product). -/
structure IsC2Bounded {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (K : ℝ)
    (f : X → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  bound : ∀ z, |f z| ≤ K
  deriv_bound : ∀ z, ‖fderiv ℝ f z‖ ≤ K
  hessian_bound : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ K

/-!
## The conditional comparison
-/

/-- Starting variance `a = c - t`, `t = N^{-θ}`, `θ = 1/500`; the statement conditions on the
eigenvalue path on `[a, c]`. -/
def rmvStart (c : ℝ) (N : ℕ) : ℝ := c - (N : ℝ) ^ (-(1 / 500 : ℝ))

/-- A test of marks that may depend on the eigenvalue path: jointly measurable for
`𝓛 ⊗ Borel`, and bounded `C²` with bound `1` in the marks for every sample. Products
`Φ(λ) g(z)` with bounded path-measurable `Φ` cover "independently of bounded eigenvalue tests";
general path dependence is the conditional form "conditionally on good full eigenvalue paths". -/
structure IsPathMarkTest {Ω X : Type*} [MeasurableSpace X] [NormedAddCommGroup X]
    [NormedSpace ℝ X] (𝓛 : MeasurableSpace Ω) (f : Ω → X → ℝ) : Prop where
  measurable : Measurable[MeasurableSpace.comap Prod.fst 𝓛 ⊔
    MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace X)] (Function.uncurry f)
  c2 : ∀ ω, IsC2Bounded 1 (f ω)

/-- **The relative mixed-vector theorem, main clause**, conditional form.

*Law.* `flowLaw N a` (`G_a ~ GUE_N(a/N)` and an independent Hermitian Brownian motion,
`H_σ = F + G_σ`, `G_σ ~ GUE_N(σ/N)` on `[a, c]`, `a = rmvStart c N`), times `N` independent
uniform phases (`phaseVectorLaw N`). Marks `z_ℓ = √N e^{iθ_ℓ} V^* u_ℓ(c)` (`relativeMark` at
`H_c`), `u_ℓ(c)` the rank-`ℓ` (increasing) eigenvector of `H_c`.
*Domain.* Fixed first: `A` and `FreshConstants c r₀ s₀ v₀`, the frame rank `r`, the number `k` of
labels, the microscopic window constant `C_w`. Then `χ > 0` and `C`. Then every failure exponent
`D` has `N₀`. For `N ≥ N₀`, every `F` in `FreshClass` (Hermitian, `‖F‖ ≤ N^A`, regular at
`(c, E)`), every frame `V ∈ ℂ^{N×r}` with `V^*ΓV = I_r` (`Γ = freshGamma F c E`): there is a set
`𝒢` of good eigenvalue paths (`𝓛`-measurable, `𝓛 = pathSigma F a a c`) with `P(𝒢ᶜ) ≤ N^{-D}`,
such that for all distinct labels `ι : Fin k ↪ Fin N`, every `𝓛`-measurable `B ⊆ 𝒢` on which the
terminal eigenvalues of the labels lie in `[E - C_w/N, E + C_w/N]`, and every path-dependent
bounded-`C²` test `f` (`IsPathMarkTest`, bound `1`):
`|E[1_B (f(z_ι) - ∫ f dγ_r^{⊗k})]| ≤ C N^{-χ} P(B)`.
*Uniformity.* `χ, C, N₀` are uniform over the deformation class, frames, labels, `B` and tests;
`𝒢` depends on `(N, F, E, V, D)` only. The bound proportional to `P(B)` for every
path-measurable `B ⊆ 𝒢` is the statement "conditionally on good full eigenvalue paths, the
bounded-`C²` distance of the conditional law of `z_ι` from `γ_r^{⊗k}` is `O(N^{-χ})`"; labels
selected measurably from the path are covered by partitioning `B`. -/
def RelativeMixedVectorsComparison : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
  ∀ (r k : ℕ) (Cw : ℝ), ∃ χ : ℝ, 0 < χ ∧ ∃ C : ℝ, ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
  ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
  ∀ V : Matrix (Fin N) (Fin r) ℂ, Vᴴ * freshGamma F c E * V = 1 →
    ∃ 𝒢 : Set (FlowSample N),
      MeasurableSet[BlockBand.Palm.MomentFlow.pathSigma F (rmvStart c N) (rmvStart c N) c] 𝒢 ∧
      flowLaw N (rmvStart c N) 𝒢ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
      ∀ ι : Fin k → Fin N, Function.Injective ι →
      ∀ B : Set (FlowSample N),
        MeasurableSet[BlockBand.Palm.MomentFlow.pathSigma F (rmvStart c N) (rmvStart c N) c] B →
        B ⊆ 𝒢 →
        (∀ ω ∈ B, ∀ m : Fin k, |flowEigenvalue F (rmvStart c N) ω c (ι m) - E| ≤ Cw / N) →
      ∀ f : FlowSample N → MarkArray k r → ℝ,
        IsPathMarkTest (BlockBand.Palm.MomentFlow.pathSigma F (rmvStart c N) (rmvStart c N) c) f →
        |∫ ω in B, ∫ θ, (f ω (fun m => relativeMark V (flowMatrix F (rmvStart c N) ω c) θ (ι m)) -
            ∫ g, f ω g ∂gaussianMarkLaw k r) ∂phaseVectorLaw N ∂flowLaw N (rmvStart c N)| ≤
          C * (N : ℝ) ^ (-χ) * (flowLaw N (rmvStart c N) B).toReal

/-!
## The decorated-sine clause
-/

/-- Unfolding density `ρ = π^{-1} Im m_{F,c}(E)` (`ρ ≥ v₀/π` on the regular class). -/
def unfoldingDensity {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (c E : ℝ) : ℝ :=
  (freshDyson F c E).im / Real.pi

/-- Admissible test of the decorated clause: `φ : ℝ × ℂ^r → ℝ` continuous, `φ ≥ 0`, supported in
`[-R, R] × ℂ^r` (no decay in the mark), and bounded `C²` in the mark with bound `K` uniformly in
the location. Not `C_c(ℝ × ℂ^r)`: vague convergence on `ℝ × ℂ^r` would let mark mass escape to
infinity. -/
structure IsDecoratedTest (r : ℕ) (R K : ℝ) (φ : ℝ × (Fin r → ℂ) → ℝ) : Prop where
  continuous : Continuous φ
  nonneg : ∀ p, 0 ≤ φ p
  support : ∀ x z, R < |x| → φ (x, z) = 0
  c2 : ∀ x, IsC2Bounded K (fun z => φ (x, z))

/-- Finite-`N` Laplace functional of the marked unfolded spectrum of `H = F + G`,
`G ~ GUE_N(c/N)` (terminal law of the flow at variance `c`), with independent uniform phases:
`E exp{-Σ_ℓ φ(Nρ(λ_ℓ - E), z_ℓ)}`, `z_ℓ = √N e^{iθ_ℓ} V^* u_ℓ`. -/
def markedLaplace {N r : ℕ} (c : ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) (φ : ℝ × (Fin r → ℂ) → ℝ) : ℝ :=
  ∫ G, ∫ θ, Real.exp (-∑ ℓ : Fin N,
      φ ((N : ℝ) * unfoldingDensity F c E * (freshEigenvalue (F + G) ℓ - E),
        relativeMark V (F + G) θ ℓ)) ∂phaseVectorLaw N ∂gueMeasure (Fin N) (Real.toNNReal (c / N))

/-- Laplace functional of the unit-intensity sine process with i.i.d. standard circular Gaussian
`ℂ^r` marks independent of the points, for a test of `IsDecoratedTest` (the Fredholm series of
`CriticalEntire.decoratedSineLaplace`, with the same formula for the wider class). -/
def markedSineLaplace (r : ℕ) (φ : ℝ × (Fin r → ℂ) → ℝ) : ℝ :=
  ∑' k : ℕ, ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
    ∫ x : Fin k → ℝ,
      Matrix.det (fun i j : Fin k => sineKernel (x i) (x j)) *
        ∏ i : Fin k, (1 - ∫ g, Real.exp (-φ (x i, g)) ∂circularVectorLaw (Fin r))
      ∂Measure.pi (fun _ : Fin k => volume)

/-- **The relative mixed-vector theorem, decorated-sine clause.**

*Law.* `markedLaplace`: `G ~ GUE_N(c/N)`, independent uniform phases, points
`x_ℓ = Nρ(λ_ℓ(F+G) - E)`, `ρ = unfoldingDensity F c E`, marks `z_ℓ = √N e^{iθ_ℓ} V^* u_ℓ`.
*Limit.* the unit-intensity sine process with i.i.d. `CN(0, I_r)` marks independent of the
points (`markedSineLaplace`).
*Topology.* configurations on `ℝ` with `ℂ^r`-valued marks: tested by every `φ ≥ 0`, continuous,
supported in `[-R, R] × ℂ^r`, bounded `C²` in the mark (`IsDecoratedTest`).
*Frame normalization.* `V^*ΓV = I_r + o(1)`: for every `δ` there is `ε` such that every frame
with `|(V^*ΓV - I_r)_{ij}| ≤ ε` is admissible (an application with `V^*Γ_F V → (πρ)^{-1} I_r`
uses this clause for the scalar renormalization `(πρ_F)^{1/2} V`, whose residues
`Nρ_F V^*u u^*V` are exactly `z z^*/π`). Exact normalization `V^*ΓV = I_r` is the case `ε = 0`.
*Uniformity.* Fixed first: `A`, `FreshConstants c r₀ s₀ v₀`, `r`, `R`, `K` and the test `φ`; then
`δ > 0`; then `ε > 0` and `N₀`; uniformly for `N ≥ N₀`, `F` in `FreshClass` at `(c, E)` and
admissible frames. -/
def RelativeMixedVectorsDecorated : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
  ∀ (r : ℕ) (R K : ℝ) (φ : ℝ × (Fin r → ℂ) → ℝ), IsDecoratedTest r R K φ →
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
  ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
  ∀ V : Matrix (Fin N) (Fin r) ℂ, (∀ i j : Fin r, ‖(Vᴴ * freshGamma F c E * V - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ ε) →
    |markedLaplace c F E V φ - markedSineLaplace r φ| ≤ δ

/-- **The relative mixed-vector theorem**: the conditional comparison and the decorated-sine
clause. -/
def RelativeMixedVectorsStatement : Prop :=
  RelativeMixedVectorsComparison ∧ RelativeMixedVectorsDecorated

end BlockBand.Critical.RelativeVectors
