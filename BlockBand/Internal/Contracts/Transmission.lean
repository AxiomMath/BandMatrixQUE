module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Statements of continuous-semimartingale calculus and Dyson Brownian motion

Definitions only. Everything is stated on an arbitrary filtered probability space `(Ω, 𝓖, Q)` with real time
`ℝ≥0`, no usual conditions. Because paths are continuous only almost surely and `𝓖` is not
completed, martingale properties are in modification form (`HasMartingaleModification`).

* Semimartingales: `IsContinuousSemimartingale`, `SemimartingaleItoFormula`,
  `StoppedSemimartingale`.
* Dyson Brownian motion: `IsHermitianBrownian`, `dysonEigenvalue`, `dysonOverlap`, `DysonBrownianMotion`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.Transmission
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix

/-!
### Continuous semimartingales and the Itô formula
-/

/-- `X` has a `𝓖`-martingale modification under `Q`. -/
def HasMartingaleModification {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (X : ℝ≥0 → Ω → E) : Prop :=
  ∃ M : ℝ≥0 → Ω → E, Martingale M 𝓖 Q ∧ ∀ t, M t =ᵐ[Q] X t

variable {d : ℕ}

/-- Compensated coordinate `Y^i_t - Y^i_0 - ∫_0^t β^i_s ds` (pathwise, over `(0,t]`). -/
def smCompensated {Ω : Type*} (Y : ℝ≥0 → Ω → Fin d → ℝ) (β : ℝ≥0 → Ω → Fin d → ℝ)
    (i : Fin d) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Y t ω i - Y 0 ω i - ∫ s in Set.Ioc (0 : ℝ) t, β s.toNNReal ω i

/-- **Continuous semimartingale with absolutely continuous characteristics** in `ℝ^d`:
`dY = β dt + dN` with `d⟨N^i, N^j⟩ = α^{ij} dt`. `Y` is adapted with a.s. continuous paths,
`β`, `α` are progressively measurable with a.s. locally integrable paths, and along some
localizing sequence of `𝓖`-stopping times `τ_n → ⊤` a.s. the stopped compensated coordinates
and the stopped compensated products `N^i N^j - ∫ α^{ij}` have martingale modifications. -/
structure IsContinuousSemimartingale {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (Y t)
  progressive : IsStronglyProgressive 𝓖 Y
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω
  drift_progressive : IsStronglyProgressive 𝓖 β
  cov_progressive : IsStronglyProgressive 𝓖 α
  integrable : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (∀ i, IntegrableOn (fun s : ℝ => β s.toNNReal ω i)
      (Set.Ioc 0 t)) ∧ ∀ i j, IntegrableOn (fun s : ℝ => α s.toNNReal ω i j) (Set.Ioc 0 t)
  localizing : ∃ τ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓖 (τ n)) ∧
    (∀ᵐ ω ∂Q, Tendsto (fun n => τ n ω) atTop (𝓝 ⊤)) ∧ ∀ n,
      (∀ i, HasMartingaleModification Q 𝓖 (stoppedProcess (smCompensated Y β i) (τ n))) ∧
      ∀ i j, HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω =>
        smCompensated Y β i t ω * smCompensated Y β j t ω -
          ∫ s in Set.Ioc (0 : ℝ) t, α s.toNNReal ω i j) (τ n))

/-- Partial derivative `∂_t φ` of `φ : ℝ × ℝ^d → ℝ`. -/
def partialTime (φ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  fderiv ℝ φ p (1, 0)

/-- Partial derivative `∂_i φ`. -/
def partialSpace (φ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) (i : Fin d) : ℝ :=
  fderiv ℝ φ p (0, Pi.single i 1)

/-- Second partial derivative `∂_i ∂_j φ`. -/
def partialSpace2 (φ : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) (i j : Fin d) : ℝ :=
  fderiv ℝ (fderiv ℝ φ) p (0, Pi.single i 1) (0, Pi.single j 1)

/-- Itô drift `∂_tφ + ∑ β^i ∂_iφ + ½ ∑ α^{ij} ∂_i∂_jφ` at `(t, Y_t)`. -/
def itoDrift (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0) (b : Fin d → ℝ)
    (a : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  partialTime φ ((t : ℝ), y) + ∑ i, b i * partialSpace φ ((t : ℝ), y) i +
    (1 / 2 : ℝ) * ∑ i, ∑ j, a i j * partialSpace2 φ ((t : ℝ), y) i j

/-- Bracket density `∑ α^{ij} ∂_iφ ∂_jφ` of the martingale part of `φ(t, Y_t)`. -/
def itoBracket (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0)
    (a : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, a i j * partialSpace φ ((t : ℝ), y) i * partialSpace φ ((t : ℝ), y) j

/-- **Contract (a1):
Itô formula for continuous semimartingales.** If `Y` is a continuous
semimartingale in `ℝ^d` with characteristics `(β, α)` taking values a.s. in an open set `U`
for all times, and `φ` is Borel measurable and `C²` on `ℝ × U` (time-dependent), then the real process `φ(t, Y_t)` is a
continuous semimartingale (in `ℝ¹`) with drift `itoDrift` and bracket density `itoBracket`.
The localizing sequence of the conclusion is part of the conclusion (it may depend on `φ`).
`Measurable φ` is needed because `Y` is in `U` only a.s.
Use for the weighted mass:
`Y = (λ, v)` with `v` absolutely continuous (zero covariance rows),
`φ(t,λ,v) = ∑_i e^{νψ(λ_i)} v_i`.
-/
def SemimartingaleItoFormula (d : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
    IsContinuousSemimartingale Q 𝓖 Y β α →
  ∀ U : Set (Fin d → ℝ), IsOpen U → (∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ U) →
  ∀ φ : ℝ × (Fin d → ℝ) → ℝ, Measurable φ → ContDiffOn ℝ 2 φ (Set.univ ×ˢ U) →
    IsContinuousSemimartingale (d := 1) Q 𝓖 (fun t ω (_ : Fin 1) => φ ((t : ℝ), Y t ω))
      (fun t ω (_ : Fin 1) => itoDrift φ (Y t ω) t (β t ω) (α t ω))
      (fun t ω => Matrix.of fun (_ _ : Fin 1) => itoBracket φ (Y t ω) t (α t ω))

/-- Characteristics switched off strictly after `ρ`. -/
def switchAfter {Ω G : Type*} [Zero G] (ρ : Ω → WithTop ℝ≥0) (f : ℝ≥0 → Ω → G) :
    ℝ≥0 → Ω → G :=
  fun t ω => if (t : WithTop ℝ≥0) ≤ ρ ω then f t ω else 0

/-- **Stopping.** A continuous semimartingale stopped at any `𝓖`-stopping time `ρ` is a
continuous semimartingale with characteristics switched off after `ρ`. With
`SemimartingaleItoFormula` this gives the stopped Itô formula. -/
def StoppedSemimartingale (d : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
    IsContinuousSemimartingale Q 𝓖 Y β α →
  ∀ ρ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 ρ →
    IsContinuousSemimartingale Q 𝓖 (stoppedProcess Y ρ) (switchAfter ρ β) (switchAfter ρ α)

/-!
### Hermitian Brownian motion and Dyson Brownian motion (β = 2)
-/

/-- Hermitian matrix from real coordinates `r : (Fin N × Fin N) × Fin 2 → ℝ`:
`G = (Z + Zᴴ)/(2√N)` with `Z_ij = r_(i,j),0 + i r_(i,j),1`. With independent `N(0,δ)`
coordinates this is GUE with `E|G_ij|² = δ/N` (`i ≠ j`) and `E G_ii² = δ/N`. -/
def hermitianOfCoords (N : ℕ) (r : (Fin N × Fin N) × Fin 2 → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let Z : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j => (r ((i, j), 0) : ℂ) +
    (r ((i, j), 1) : ℂ) * Complex.I
  ((1 / (2 * Real.sqrt N) : ℝ) : ℂ) • (Z + Zᴴ)

/-- The GUE increment law of variance `δ` (the GUE normalization of Dyson Brownian motion). -/
def gueIncrementLaw (N : ℕ) (δ : ℝ≥0) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  (Measure.pi fun _ : (Fin N × Fin N) × Fin 2 => gaussianReal 0 δ).map (hermitianOfCoords N)

/-- `G` is a Hermitian matrix Brownian motion for `𝓖` (GUE normalization `GUE_N(δ/N)` for an
increment over time `δ`): adapted, continuous for every sample (this gives progressive
measurability and makes hitting times stopping times), Hermitian, `G_0 = 0`, and every
increment `G_t - G_s` is independent of `𝓖_s` with law `gueIncrementLaw N (t - s)`. -/
structure IsHermitianBrownian {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (N : ℕ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) : Prop where
  adapted : ∀ t, Measurable[𝓖 t] (G t)
  continuous : ∀ ω, Continuous fun t => G t ω
  hermitian : ∀ t ω, (G t ω).IsHermitian
  zero : ∀ ω, G 0 ω = 0
  indep : ∀ s t, s ≤ t → Indep (MeasurableSpace.comap (fun ω => G t ω - G s ω) inferInstance)
    (𝓖 s) Q
  law : ∀ s t, s ≤ t → HasLaw (fun ω => G t ω - G s ω) (gueIncrementLaw N (t - s)) Q

/-- Eigenvalues `λ_1 ≥ … ≥ λ_N` of the Hermitian part `(H + Hᴴ)/2` (for Hermitian `H`, of
`H`), in nonincreasing order. -/
def dysonEigenvalue (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℝ :=
  (Matrix.isHermitian_add_transpose_self H).eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm i) / 2

/-- Simple spectrum: the ordered eigenvalues are pairwise distinct. -/
def HasSimpleSpectrum (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  StrictAnti (dysonEigenvalue N H)

/-- Spectral projection onto the `i`-th eigenline for simple spectrum, as the Lagrange product
`∏_{j ≠ i} (H - λ_j)/(λ_i - λ_j)`. -/
def dysonProjection (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  (((List.finRange N).filter fun j => j ≠ i).map fun j =>
    ((dysonEigenvalue N H i - dysonEigenvalue N H j)⁻¹ : ℂ) •
      (H - (dysonEigenvalue N H j : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).prod

/-- Radial overlap `X_i = N |q* u_i|²` for simple spectrum. -/
def dysonOverlap (N : ℕ) (q : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℝ :=
  (N : ℝ) * (star q ⬝ᵥ (dysonProjection N H i *ᵥ q)).re

/-- Coupling `c_ij = 1/(N(λ_i - λ_j)²)`. -/
def dysonCoupling (N : ℕ) (lam : Fin N → ℝ) (i j : Fin N) : ℝ :=
  1 / ((N : ℝ) * (lam i - lam j) ^ 2)

/-- Eigenvalue drift `(1/N) ∑_{j ≠ i} 1/(λ_i - λ_j)`. -/
def dysonDrift (N : ℕ) (lam : Fin N → ℝ) (i : Fin N) : ℝ :=
  (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, 1 / (lam i - lam j)

/-- Joint coordinates `(λ, X) ∈ ℝ^{2N}`: `Sum.inl i ↦ λ_i`, `Sum.inr i ↦ X_i`, as `Fin (2N)`
through `finSumFinEquiv`. -/
def dysonState (N : ℕ) (q : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) : Fin (N + N) → ℝ :=
  fun k => match finSumFinEquiv.symm k with
    | Sum.inl i => dysonEigenvalue N H i
    | Sum.inr i => dysonOverlap N q H i

/-- Joint drift: `λ_i ↦ dysonDrift`, `X_i ↦ ∑_{j≠i} c_ij (X_j - X_i)`. -/
def dysonStateDrift (N : ℕ) (y : Fin (N + N) → ℝ) : Fin (N + N) → ℝ :=
  let lam : Fin N → ℝ := fun i => y (finSumFinEquiv (Sum.inl i))
  let X : Fin N → ℝ := fun i => y (finSumFinEquiv (Sum.inr i))
  fun k => match finSumFinEquiv.symm k with
    | Sum.inl i => dysonDrift N lam i
    | Sum.inr i => ∑ j ∈ Finset.univ.erase i, dysonCoupling N lam i j * (X j - X i)

/-- Joint covariance: `d⟨λ_i,λ_j⟩ = δ_ij/N`, `d⟨λ, X⟩ = 0`,
`d⟨X_i⟩ = 2∑_{j≠i} c_ij X_i X_j`, `d⟨X_i,X_j⟩ = -2 c_ij X_i X_j` (`i ≠ j`); from the pair
generator `c_ij{xy(∂_x-∂_y)² + (y-x)(∂_x-∂_y)}`. -/
def dysonStateCov (N : ℕ) (y : Fin (N + N) → ℝ) : Matrix (Fin (N + N)) (Fin (N + N)) ℝ :=
  let lam : Fin N → ℝ := fun i => y (finSumFinEquiv (Sum.inl i))
  let X : Fin N → ℝ := fun i => y (finSumFinEquiv (Sum.inr i))
  Matrix.of fun k l => match finSumFinEquiv.symm k, finSumFinEquiv.symm l with
    | Sum.inl i, Sum.inl j => if i = j then 1 / (N : ℝ) else 0
    | Sum.inr i, Sum.inr j => if i = j then
        2 * ∑ m ∈ Finset.univ.erase i, dysonCoupling N lam i m * X i * X m
      else -2 * dysonCoupling N lam i j * X i * X j
    | _, _ => 0

/-- Angular generator on functions of the overlaps, with couplings from `lam`:
`∑_{i<j} c_ij {X_iX_j(∂_i-∂_j)² + (X_j-X_i)(∂_i-∂_j)}`. -/
def angularGenerator (N : ℕ) (lam : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (X : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), dysonCoupling N lam i j *
    (X i * X j * (fderiv ℝ (fderiv ℝ f) X (Pi.single i 1 - Pi.single j 1)
        (Pi.single i 1 - Pi.single j 1)) +
      (X j - X i) * fderiv ℝ f X (Pi.single i 1 - Pi.single j 1))

/-- First time after `s` that some eigenvalue gap of `H` is at most `1/n` (`⊤` if never),
measured from `s`. -/
def gapStop {Ω : Type*} (N : ℕ) (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (n : ℕ)
    (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (u : ℝ≥0) (_ : ∃ i j : Fin N, i ≠ j ∧
      |dysonEigenvalue N (H (s + u) ω) i - dysonEigenvalue N (H (s + u) ω) j| ≤ 1 / (n : ℝ)),
    (u : WithTop ℝ≥0)

/-- The filtration `u ↦ 𝓖_{s+u}` restarted at time `s`. -/
def shiftFiltration {Ω : Type*} [MeasurableSpace Ω]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (s : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) where
  seq u := 𝓖 (s + u)
  mono' _ _ h := 𝓖.mono (add_le_add_right h s)
  le' u := 𝓖.le (s + u)

/-- **Dyson Brownian motion, β = 2.** Let `G` be a Hermitian
Brownian motion for `𝓖` and `F` an `𝓖_0`-measurable Hermitian matrix; `H_t = F + G_t`. Then
* non-collision: a.s., for every `t > 0`, `H_t` has simple spectrum;
* semimartingale: for every start time `s > 0`, every direction `q`, the joint process
  `u ↦ (λ(H_{s+u}), X^q(H_{s+u}))` is a continuous semimartingale for `u ↦ 𝓖_{s+u}` with
  drift `dysonStateDrift` and covariance `dysonStateCov` (in particular
  `dλ_i = N^{-1/2} dB_i + (1/N)∑_{j≠i} dt/(λ_i-λ_j)` and the eigenvalue noise is orthogonal to
  the overlap noise);
* conditional angular martingale problem: for `s > 0`, `q`, every gap level `n > 0`, every
  `C²` function `f` of the overlaps, every `u`, and every bounded random variable `Λ` measurable
  for the σ-algebra of the whole eigenvalue path `σ(λ(H_{s+v}) : v ≥ 0)`,
  the integrand `Λ (f(X_{u∧σ_n}) - f(X_0) - ∫_0^{u∧σ_n} 𝒜_v f(X_v) dv)` is integrable and has
  expectation `0`, where `σ_n` is the gap stop
  and `𝒜_v = angularGenerator` with couplings `c_ij(v)` (conditionally on the eigenvalue path the
  overlaps solve the angular martingale problem; this yields the complex moment generator);
* gap stops: for `s > 0` every gap stop `σ_n` is a stopping time for `u ↦ 𝓖_{s+u}`, and
  `σ_n → ⊤` almost surely. -/
def DysonBrownianMotion (N : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)) ∧
    (∀ (s : ℝ≥0), 0 < s → ∀ q : Fin N → ℂ,
      IsContinuousSemimartingale Q (shiftFiltration 𝓖 s)
        (fun u ω => dysonState N q (F ω + G (s + u) ω))
        (fun u ω => dysonStateDrift N (dysonState N q (F ω + G (s + u) ω)))
        (fun u ω => dysonStateCov N (dysonState N q (F ω + G (s + u) ω)))) ∧
    (∀ (s : ℝ≥0), 0 < s → ∀ (q : Fin N → ℂ) (n : ℕ), 0 < n → ∀ (f : (Fin N → ℝ) → ℝ), ContDiff ℝ 2 f →
      ∀ (u : ℝ≥0) (Λ : Ω → ℝ),
        Measurable[⨆ v : ℝ≥0, MeasurableSpace.comap
          (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) inferInstance] Λ →
        (∃ C, ∀ ω, |Λ ω| ≤ C) →
        let e : Ω → ℝ := fun ω => Λ ω * (stoppedProcess (fun v ω =>
            f (fun i => dysonOverlap N q (F ω + G (s + v) ω) i) -
            f (fun i => dysonOverlap N q (F ω + G s ω) i) -
            ∫ r in Set.Ioc (0 : ℝ) v, angularGenerator N
              (dysonEigenvalue N (F ω + G (s + r.toNNReal) ω)) f
              (fun i => dysonOverlap N q (F ω + G (s + r.toNNReal) ω) i))
          (gapStop N (fun t ω => F ω + G t ω) s n) u ω)
        Integrable e Q ∧ ∫ ω, e ω ∂Q = 0) ∧
    (∀ (s : ℝ≥0), 0 < s →
      (∀ n : ℕ, 0 < n → IsStoppingTime (shiftFiltration 𝓖 s) (gapStop N (fun t ω => F ω + G t ω) s n)) ∧
      ∀ᵐ ω ∂Q, Tendsto (fun n => gapStop N (fun t ω => F ω + G t ω) s n ω) atTop (𝓝 ⊤))

end BlockBand.Internal.Contracts.Transmission
