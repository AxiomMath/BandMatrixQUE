module

public import BlockBand.SourceProcess.Stochastic.Angular.Phase
public import BlockBand.SourceProcess.Stochastic.Dyson.FirstDeriv
public import BlockBand.SourceProcess.Stochastic.Dyson.BrownianSemimartingale

/-!
# Complex angular martingale problem: intermediate statements

**Definitions.**
* `arrZ V y`: the array `Z_{ia} = v_a^* u_i` for the canonical selection `canonEv`;
* `arrayFn V f₀ y = f₀(arrZ V y)` on `simpleSet N` (`0` elsewhere): the scalar `F(H)`;
  `arrGen V f₀ y = 𝒜 f₀ (arrZ V y)` with couplings `c_ij(λ(y))`;
* `angVar`: the stopped variable `f(Z_{u∧σ_n}) - f(Z_0) - ∫_0^{u∧σ_n} 𝒜 f(Z_w) dw` of
  `ComplexAngularMartingaleProblem` for a random test `f`, as written there; `coordVar`: its
  analogue for a scalar `φ` of the coordinates with compensator density `A`.

**Intermediate propositions**:
1. `ArrayLaplacian N r` (deterministic): on `simpleSet N`,
   `Δ arrayFn = 2N · arrGen` (Laplacian in the coordinates) and
   `⟨∇ arrayFn, ∇ λ_i⟩ = 0` (zero covariation with every eigenvalue). The covariation half is
   `arrayFn_cross`; the Laplacian half is `ArrayLaplacianDiag N r`.
2. `GenericConditioning N` (stochastic): for every `s` at which the
   spectrum stays simple a.s., every gap level and every scalar `φ` that is `C²` on
   `simpleSet N`, bounded, with `Δφ = 2N A` and `⟨∇φ, ∇λ_i⟩ = 0`, the variable
   `coordVar` is integrable and integrates to `0` over every set of `𝓖_s ⊔ eigenPathSigma`.
   This is the Fourier / π–λ / strong-solution argument of the Dyson angular martingale problem
   with the overlap state replaced by `φ`.
3. `DeterministicAngular N r`: `angVar` for deterministic phase-invariant `C²` tests, any
   selection, integrable with zero integral over every set of `𝓖_s ⊔ eigenPathSigma`, at every
   `s` at which the spectrum stays simple a.s. (from 1, 2 and the regularity of `arrayFn`).
4. `SimpleSpectrumAngular N r`: the martingale problem for random tests under the same simplicity
   hypothesis (from 3 by simple random tests and `C²`-approximation).
`ComplexAngularMartingaleProblem` follows from 4 by non-collision (`DysonNonCollision`) for
`s > 0` and a modification of `F` on `{gap(F) ≤ 1/n}` for `s = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

/-!
### Definitions
-/

/-- The angular array of the canonical selection, in the coordinates. -/
def arrZ {N r : ℕ} (V : Matrix (Fin N) (Fin r) ℂ) (y : Fin (N * N) → ℝ) : AngularArray N r :=
  angularArray V (canonEv N (vecHerm N y))

open Classical in
/-- The scalar `F(H) = f₀(Z(H))` in the coordinates (`0` off the simple spectrum). -/
def arrayFn {N r : ℕ} (V : Matrix (Fin N) (Fin r) ℂ) (f₀ : AngularArray N r → ℝ)
    (y : Fin (N * N) → ℝ) : ℝ :=
  if y ∈ simpleSet N then f₀ (arrZ V y) else 0

open Classical in
/-- The generator `𝒜 f₀ (Z(H))` with couplings `c_ij(λ(H))` (`0` off the simple spectrum). -/
def arrGen {N r : ℕ} (V : Matrix (Fin N) (Fin r) ℂ) (f₀ : AngularArray N r → ℝ)
    (y : Fin (N * N) → ℝ) : ℝ :=
  if y ∈ simpleSet N then complexAngularGenerator N r (fun i => lam N i y) f₀ (arrZ V y) else 0

/-- **The stopped variable** of `ComplexAngularMartingaleProblem`. -/
def angVar {Ω : Type*} {N r : ℕ} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ) (f : Ω → AngularArray N r → ℝ) (u : ℝ≥0) :
    Ω → ℝ :=
  let Z : ℝ≥0 → Ω → AngularArray N r := fun v ω => angularArray V (ev (F ω + G (s + v) ω))
  stoppedProcess (fun v ω =>
      f ω (Z v ω) - f ω (Z 0 ω) -
      ∫ w in Set.Ioc (0 : ℝ) v, complexAngularGenerator N r
        (dysonEigenvalue N (F ω + G (s + w.toNNReal) ω)) (f ω) (Z w.toNNReal ω))
    (gapStop N (fun t ω => F ω + G t ω) s n) u

/-- The stopped compensated variable of a scalar `φ` of the coordinates with density `A`. -/
def coordVar {Ω : Type*} {N : ℕ} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (n : ℕ)
    (φ A : (Fin (N * N) → ℝ) → ℝ) (u : ℝ≥0) : Ω → ℝ :=
  stoppedProcess (fun v ω =>
      φ (hermVec N (F ω + G (s + v) ω)) - φ (hermVec N (F ω + G (s + 0) ω)) -
      ∫ w in Set.Ioc (0 : ℝ) v, A (hermVec N (F ω + G (s + w.toNNReal) ω)))
    (gapStop N (fun t ω => F ω + G t ω) s n) u

/-!
### Intermediate propositions
-/

/-- **(1) Laplacian identity** (second-order eigenvector perturbation). For a
frame `V` and a deterministic phase-invariant `C²` test `f₀`, at every point of simple spectrum:
`∑_a ∂_a² F = 2N · 𝒜 f₀(Z)` and `∑_a ∂_a F ∂_a λ_i = 0` for every `i`, where `F = arrayFn V f₀`
and `∂_a` are the coordinate partials (an orthonormal basis of the Hermitian matrices for
`Re tr(AB)`). With covariance `I/N` this says: the Itô drift of `F(H_t)` is `𝒜 f₀(Z_t)` and its
covariation with every eigenvalue vanishes. -/
def ArrayLaplacian (N r : ℕ) : Prop :=
  ∀ (V : Matrix (Fin N) (Fin r) ℂ) (f₀ : AngularArray N r → ℝ), ContDiff ℝ 2 f₀ →
    IsPhaseInvariant f₀ → ∀ y ∈ simpleSet N,
      (∑ a, fderiv ℝ (fderiv ℝ (arrayFn V f₀)) y (Pi.single a 1) (Pi.single a 1) =
        2 * N * arrGen V f₀ y) ∧
      ∀ i : Fin N, ∑ a, fderiv ℝ (arrayFn V f₀) y (Pi.single a 1) *
        fderiv ℝ (lam N i) y (Pi.single a 1) = 0

/-- **(1′) The Laplacian half of `ArrayLaplacian`** (the covariation half is
`arrayFn_cross`): `∑_a ∂_a² F = 2N · 𝒜 f₀(Z)` on simple spectrum. -/
def ArrayLaplacianDiag (N r : ℕ) : Prop :=
  ∀ (V : Matrix (Fin N) (Fin r) ℂ) (f₀ : AngularArray N r → ℝ), ContDiff ℝ 2 f₀ →
    IsPhaseInvariant f₀ → ∀ y ∈ simpleSet N,
      ∑ a, fderiv ℝ (fderiv ℝ (arrayFn V f₀)) y (Pi.single a 1) (Pi.single a 1) =
        2 * N * arrGen V f₀ y

/-- **(2) Generic conditioning.** Let `s` be such that a.s. the spectrum of
`H_{s+v}` is simple for every `v ≥ 0`, `n > 0`, and `φ` a bounded measurable scalar of the
coordinates, `C²` on `simpleSet N`, with `Δφ = 2N A` and `⟨∇φ, ∇λ_i⟩ = 0` there, where `A` is
measurable, continuous on `simpleSet N` and bounded on the region of gaps `≥ 1/n`. Then for
every `u` the gap-stopped compensated variable `coordVar` is integrable, and its integral over
every set of `𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)` vanishes. -/
def GenericConditioning (N : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    ∀ s : ℝ≥0, (∀ᵐ ω ∂Q, ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) →
    ∀ n : ℕ, 0 < n → ∀ φ A : (Fin (N * N) → ℝ) → ℝ,
      Measurable φ → (∀ y ∈ simpleSet N, ContDiffAt ℝ 2 φ y) →
      Measurable A → ContinuousOn A (simpleSet N) →
      (∀ y ∈ simpleSet N,
        ∑ a, fderiv ℝ (fderiv ℝ φ) y (Pi.single a 1) (Pi.single a 1) = 2 * N * A y) →
      (∀ y ∈ simpleSet N, ∀ i : Fin N,
        ∑ a, fderiv ℝ φ y (Pi.single a 1) * fderiv ℝ (lam N i) y (Pi.single a 1) = 0) →
      (∃ C, ∀ y, |φ y| ≤ C) →
      (∃ C, ∀ y ∈ simpleSet N,
        (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) → |A y| ≤ C) →
      ∀ u : ℝ≥0, Integrable (coordVar F G s n φ A u) Q ∧
        ∀ S, MeasurableSet[𝓖 s ⊔ eigenPathSigma N F G s] S →
          ∫ ω in S, coordVar F G s n φ A u ω ∂Q = 0

/-- **(3) Deterministic tests.** At every start `s` at which the spectrum stays simple a.s.:
for every selection, frame, gap level, deterministic phase-invariant `C²` test `f₀` and `u`,
the stopped variable is integrable and integrates to `0` over every set of
`𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)`. -/
def DeterministicAngular (N r : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    ∀ ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ, IsEigenSelection N ev →
    ∀ s : ℝ≥0, (∀ᵐ ω ∂Q, ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) →
    ∀ (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ), 0 < n →
    ∀ f₀ : AngularArray N r → ℝ, ContDiff ℝ 2 f₀ → IsPhaseInvariant f₀ → ∀ u : ℝ≥0,
      Integrable (angVar F G ev s V n (fun _ => f₀) u) Q ∧
        ∀ S, MeasurableSet[𝓖 s ⊔ eigenPathSigma N F G s] S →
          ∫ ω in S, angVar F G ev s V n (fun _ => f₀) u ω ∂Q = 0

/-- **(4) Random tests under simple spectrum**: the martingale problem at every start `s` at which
the spectrum stays simple a.s. -/
def SimpleSpectrumAngular (N r : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    ∀ ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ, IsEigenSelection N ev →
    ∀ s : ℝ≥0, (∀ᵐ ω ∂Q, ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) →
    ∀ (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ), 0 < n →
    ∀ f : Ω → AngularArray N r → ℝ, (∀ ω, ContDiff ℝ 2 (f ω)) → (∀ ω, IsPhaseInvariant (f ω)) →
      (∀ Z, Measurable[𝓖 s ⊔ eigenPathSigma N F G s] fun ω => f ω Z) →
      (∀ R : ℝ, ∃ C : ℝ, ∀ ω Z, ‖Z‖ ≤ R →
        |f ω Z| ≤ C ∧ ‖fderiv ℝ (f ω) Z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (f ω)) Z‖ ≤ C) →
    ∀ u : ℝ≥0, Integrable (angVar F G ev s V n f u) Q ∧ ∫ ω, angVar F G ev s V n f u ω ∂Q = 0

/-- The stopped variable of `ComplexAngularMartingaleProblem` is `angVar` (definitional
unfolding of the `let`s). -/
theorem angVar_eq_contract {Ω : Type*} {N r : ℕ} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ) (f : Ω → AngularArray N r → ℝ) (u : ℝ≥0) :
    angVar F G ev s V n f u = stoppedProcess (fun v ω =>
        f ω (angularArray V (ev (F ω + G (s + v) ω))) -
          f ω (angularArray V (ev (F ω + G (s + 0) ω))) -
        ∫ w in Set.Ioc (0 : ℝ) v, complexAngularGenerator N r
          (dysonEigenvalue N (F ω + G (s + w.toNNReal) ω)) (f ω)
          (angularArray V (ev (F ω + G (s + w.toNNReal) ω))))
      (gapStop N (fun t ω => F ω + G t ω) s n) u := rfl

end BlockBand.SourceProcess.Stochastic.ComplexAngular
