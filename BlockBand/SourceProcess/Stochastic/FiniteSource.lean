module
public import BlockBand.SourceProcess.Stochastic.SDE
public import BlockBand.SourceProcess.GramMatrices
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Matrix.Basis
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The finite source equation and the finite Gram law: statements

In a finite ambient space with a rank-`Naux` projection `P`
and `P' = P + V 𝖣 Vᴴ` also a rank-`Naux` projection, with `Z` a complex Brownian matrix
normalized by `E|dZ_ij|² = 2 dt`, the finite source equation is

  `dA = (√D₀/2) P dZ P'`,  `dV = dAᴴ V - (D₀ Naux / 4) P V dt`.

Real noise coordinates: `κ = (ι × ι) × Fin 2`, `Z_kj = W_((k,j),0) + i W_((k,j),1)` with
independent standard real Brownian `W` (`E dW² = dt`, hence `E|dZ|² = 2dt`). Then
`dAᴴ V = (√D₀/2) P' dZᴴ P V` and `(dZᴴ)_jk = dW_((k,j),0) - i dW_((k,j),1)`, so the
diffusion coefficient of `V` along `W_((k,j),r)` is `c_r (√D₀/2) P' E_jk P V` with
`c_0 = 1`, `c_1 = -i` and `E_jk` the matrix unit. (The adopted `commonComplexBrownian` is
`(W_0 + i W_1)/√2`, i.e. `Z/√2`.)

`Naux` is the trace of `P`. The ambient index type `ι` is arbitrary (the paper's
`ℂ^{2 Naux}` and every padding by unused near or far dimensions are instances).
Signature: `𝖣` Hermitian with `𝖣³ = 𝖣` (eigenvalues in `{-1,0,1}`).
Matrices carry the Frobenius norm (local instance); all statements are norm-independent.
-/

namespace BlockBand.SourceProcess.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal ComplexOrder
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

/-- Real noise coordinates of the complex Brownian matrix `Z`. -/
abbrev SourceNoise (ι : Type*) := (ι × ι) × Fin 2

/-- The near projection hypothesis: `P` Hermitian, idempotent, of trace `Naux`. -/
def IsNearProjection (P : Matrix ι ι ℂ) (Naux : ℕ) : Prop :=
  Pᴴ = P ∧ P * P = P ∧ P.trace = (Naux : ℂ)

/-- Fixed Hermitian signature with eigenvalues in `{-1,0,1}`. -/
def IsSignature (D : Matrix c c ℂ) : Prop := Dᴴ = D ∧ D * D * D = D

/-- The two-projection constraint: `P' = P + V𝖣Vᴴ` is an orthogonal projection with the
same trace (rank) as `P`. -/
def TwoProjection (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) : Prop :=
  (gramProjection P V D)ᴴ = gramProjection P V D ∧
    gramProjection P V D * gramProjection P V D = gramProjection P V D ∧
    (gramProjection P V D).trace = P.trace

/-- Drift `-(D₀ Naux/4) P V` of the finite source equation. -/
def sourceDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) : Matrix ι c ℂ :=
  ((-(D0 * Naux / 4) : ℝ) : ℂ) • (P * V)

/-- Diffusion of the finite source equation along the real coordinate `W_((k,j),r)`:
`c_r (√D₀/2) P' E_jk P V`, `c_0 = 1`, `c_1 = -i`. -/
def sourceDiffusion (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : Matrix ι c ℂ :=
  ((if a.2 = 0 then (1 : ℂ) else -Complex.I) * ((Real.sqrt D0 / 2 : ℝ) : ℂ)) •
    (gramProjection P V D * Matrix.single a.1.2 a.1.1 (1 : ℂ) * P * V)

/-- The conductance-type scalar `g = ½ Tr(𝖣M𝖣M)`. -/
def gramScalar (D M : Matrix c c ℂ) : ℂ := (1 / 2 : ℂ) * (D * M * D * M).trace

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

/-- **Finite Gram law, well-posedness.** For every augmented-`F_0`
initial frame satisfying the two-projection constraint a.s., the finite source equation has a
global (nonexplosive) strong solution; global solutions are pathwise unique; and
every global solution satisfies the constraint at all times a.s. -/
def FiniteSourceWellPosed (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) : Prop :=
  0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x)) →
    (∃ X, IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X) ∧
    (∀ X Y, IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X →
      IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ Y →
      ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, X t x = Y t x) ∧
    (∀ X, IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X →
      ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, TwoProjection P D (X t x))

/-- The Gram pair `(M, B) = (VᴴV, VᴴPV)`. -/
def gramPair (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) : Matrix c c ℂ × Matrix c c ℂ :=
  (sourceGram V, nearGram P V)

/-- The crossed Gram covariance pattern:
`crossedBracket D0 B Cl Cr i j k l = (D₀/2)(B_il (Cl)_kj + (Cr)_il B_kj)`. -/
def crossedBracket (D0 : ℝ) (B Cleft Cright : Matrix c c ℂ) (i j k l : c) : ℂ :=
  ((D0 / 2 : ℝ) : ℂ) * (B i l * Cleft k j + Cright i l * B k j)

/-- **Finite Gram law, drift and covariance.**
For every constrained initial frame and global solution `V`, the Gram pair `(M,B)` is an
Itô process with drift `(0, -½ D₀ g B)` and some diffusion `σ^G` whose complex
bilinear brackets `∑_a σ^G_a(·)_ij σ^G_a(·)_kl` are
* `dM_ij dM_kl = (D₀/2)[B_il (C₀)_kj + (C₀)_il B_kj]`,
* `dM_ij dB_kl = (D₀/2)[B_il (C₁ᴴ)_kj + (C₁)_il B_kj]`,
* `dB_ij dB_kl = (D₀/2)[B_il (C₂)_kj + (C₂)_il B_kj]`,
with `C₀ = B + M𝖣M`, `C₁ = B + M𝖣B`, `C₂ = B + B𝖣B`, at all times a.s. -/
def FiniteSourceGramCharacteristics (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ) : Prop :=
  0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x)) →
  ∀ X, IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X →
    ∃ σG : SourceNoise ι → ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix c c ℂ × Matrix c c ℂ,
      IsNativeItoProcess μ (fun t x => gramPair P (X t x))
        (fun t x => (0, (-(((D0 / 2 : ℝ) : ℂ) * gramScalar D (sourceGram (X t x)))) •
          nearGram P (X t x))) σG ∧
      ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ t, ∀ i j k l : c,
        let M := sourceGram (X t x)
        let B := nearGram P (X t x)
        (∑ a, (σG a t x).1 i j * (σG a t x).1 k l =
            crossedBracket D0 B (gramC0 M B D) (gramC0 M B D) i j k l) ∧
        (∑ a, (σG a t x).1 i j * (σG a t x).2 k l =
            crossedBracket D0 B (gramC1 M B D)ᴴ (gramC1 M B D) i j k l) ∧
        (∑ a, (σG a t x).2 i j * (σG a t x).2 k l =
            crossedBracket D0 B (gramC2 B D) (gramC2 B D) i j k l)

/-- Law of the Gram path `t ↦ (M_t, B_t)` on the product σ-algebra of
`ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ` (finite-dimensional distributions). -/
def gramPathLaw {κ : Type*} [Fintype κ] (P : Matrix ι ι ℂ)
    (X : ℝ≥0 → DriverSample S κ → Matrix ι c ℂ) :
    Measure (ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ) :=
  (driverLaw (κ := κ) μ).map fun x t => gramPair P (X t x)

/-- **Finite Gram law, invariance.** The Gram law depends only on the law of
`(M₀, B₀)` and on `𝖣`: for two setups — possibly different ambient spaces (padding by
unused near or far dimensions), near projections, ranks and old-state laws — with the same
`D₀`, the same signature `𝖣`, constrained initial frames whose initial Gram pairs have the
same law, and global solutions `X, X'`, the Gram path laws coincide. -/
def FiniteSourceGramLawInvariance {ι' S' : Type*} [Fintype ι'] [DecidableEq ι']
    [MeasurableSpace S'] (μ' : Measure S') [IsProbabilityMeasure μ'] (D0 : ℝ)
    (D : Matrix c c ℂ) (Naux Naux' : ℕ) (P : Matrix ι ι ℂ) (Pb : Matrix ι' ι' ℂ) : Prop :=
  0 < D0 → IsNearProjection P Naux → IsNearProjection Pb Naux' → IsSignature D →
  ∀ (ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ)
    (ξ' : DriverSample S' (SourceNoise ι') → Matrix ι' c ℂ),
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ →
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι') μ' 0] ξ' →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x)) →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι') μ', TwoProjection Pb D (ξ' x)) →
    (driverLaw (κ := SourceNoise ι) μ).map (fun x => gramPair P (ξ x)) =
      (driverLaw (κ := SourceNoise ι') μ').map (fun x => gramPair Pb (ξ' x)) →
  ∀ X X', IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X →
    IsSDESolution μ' (sourceDrift D0 Naux' Pb) (sourceDiffusion D0 Pb D) ξ' X' →
    gramPathLaw μ P X = gramPathLaw μ' Pb X'

/-!
### The Gram martingale problem on an arbitrary filtered probability space
-/

/-- Gram coordinates: `(0,i,j) ↦ M_ij`, `(1,i,j) ↦ B_ij`. -/
def gramEntry (e : Fin 2 × c × c) (G : Matrix c c ℂ × Matrix c c ℂ) : ℂ :=
  if e.1 = 0 then G.1 e.2.1 e.2.2 else G.2 e.2.1 e.2.2

/-- Gram drift coordinates: `0` for `M`, `-½ D₀ g B_ij` for `B`. -/
def gramDriftEntry (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c)
    (G : Matrix c c ℂ × Matrix c c ℂ) : ℂ :=
  if e.1 = 0 then 0 else -(((D0 / 2 : ℝ) : ℂ) * gramScalar D G.1) * G.2 e.2.1 e.2.2

/-- Gram covariance coordinates, complex bilinear `dG_e dG_e'`. -/
def gramCovEntry (D0 : ℝ) (D : Matrix c c ℂ) (e e' : Fin 2 × c × c)
    (G : Matrix c c ℂ × Matrix c c ℂ) : ℂ :=
  let M := G.1
  let B := G.2
  match e.1, e'.1 with
  | 0, 0 => crossedBracket D0 B (gramC0 M B D) (gramC0 M B D) e.2.1 e.2.2 e'.2.1 e'.2.2
  | 0, 1 => crossedBracket D0 B (gramC1 M B D)ᴴ (gramC1 M B D) e.2.1 e.2.2 e'.2.1 e'.2.2
  | 1, 0 => crossedBracket D0 B (gramC1 M B D)ᴴ (gramC1 M B D) e'.2.1 e'.2.2 e.2.1 e.2.2
  | 1, 1 => crossedBracket D0 B (gramC2 B D) (gramC2 B D) e.2.1 e.2.2 e'.2.1 e'.2.2

/-- Trace stop `σ_K = inf {t : Re Tr M_t ≥ K}`. -/
def gramTraceStop {Ω : Type*} (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : K ≤ ((G t ω).1.trace).re), (t : WithTop ℝ≥0)

/-- Compensated Gram coordinate `G_e(t) - G_e(0) - ∫_0^t b_e(G_s) ds`. -/
def gramCompensated {Ω : Type*} (D0 : ℝ) (D : Matrix c c ℂ)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) : ℂ :=
  gramEntry e (G t ω) - gramEntry e (G 0 ω) -
    ∫ s in Set.Ioc (0 : ℝ) t, gramDriftEntry D0 D e (G s.toNNReal ω)

/-- A Gram state is feasible for the signature `𝖣` if it has a finite constrained factor
realization: some finite ambient space, near projection and frame `V` with the
two-projection constraint and `(VᴴV, VᴴPV) = G` ("every feasible Gram state has a finite factor
realization"). Feasibility implies `B ⪰ 0`, `M - B ⪰ 0` and identities such as
`Tr(𝖣M) = 0`. -/
def GramFeasible (D : Matrix c c ℂ) (G : Matrix c c ℂ × Matrix c c ℂ) : Prop :=
  ∃ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) c ℂ),
    Pᴴ = P ∧ P * P = P ∧ TwoProjection P D V ∧ gramPair P V = G

/-- A (feasible) solution of the Gram martingale problem on `(Ω, 𝓖, Q)`: adapted, a.s.
continuous, feasible at all times a.s., and for every trace level `K` the stopped
compensated coordinates and the stopped compensated products `N_e N_e' - ∫ Γ_ee'(G_s) ds`
have `𝓖`-martingale modifications (modification form: the filtration is not completed and
paths are continuous only a.s.). -/
structure IsGramMartingaleSolution {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) (D : Matrix c c ℂ)
    (G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (G t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => G t ω
  feasible : ∀ᵐ ω ∂Q, ∀ t, GramFeasible D (G t ω)
  drift : ∀ (K : ℝ) (e : Fin 2 × c × c), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (gramCompensated D0 D G e) (gramTraceStop G K) t
  bracket : ∀ (K : ℝ) (e e' : Fin 2 × c × c), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => gramCompensated D0 D G e t ω *
        gramCompensated D0 D G e' t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (G s.toNNReal ω))
      (gramTraceStop G K) t

/-- **Finite Gram law, uniqueness for the Gram martingale problem, including initially
singular strata.** Every feasible solution `G` of the Gram martingale
problem whose initial law equals the initial Gram law of a constrained ambient solution `X`
has the same path law as the Gram process of `X`. No rank assumption is made on `G₀`. -/
def GramMartingaleProblemUniqueness {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (D0 : ℝ) (D : Matrix c c ℂ) (Naux : ℕ) (P : Matrix ι ι ℂ) : Prop :=
  0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ, IsGramMartingaleSolution Q 𝓖 D0 D G →
  ∀ ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ x)) →
    Q.map (G 0) = (driverLaw (κ := SourceNoise ι) μ).map (fun x => gramPair P (ξ x)) →
  ∀ X, IsSDESolution μ (sourceDrift D0 Naux P) (sourceDiffusion D0 P D) ξ X →
    Q.map (fun ω t => G t ω) = gramPathLaw μ P X

end BlockBand.SourceProcess.Stochastic
