module

public import BlockBand.Internal.Contracts.Transmission

/-!
# The complex angular martingale problem of Dyson Brownian motion

The statement that, conditionally on the eigenvalue path, the eigenvector components along a
fixed frame solve the martingale problem of the complex angular generator
`¼ ∑_{i<j} c_ij (X_ij² + Y_ij²)`, up to the gap stops.

* **Conditioning.** The test may be random. It is measurable for `𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)`:
  the past up to the start time, including the initial angular state, together with the whole
  later eigenvalue path. This contains the σ-algebra of the conditional angular martingale
  clause of `DysonBrownianMotion`. Its `C²` bounds are uniform in `ω` on every ball. A bounded
  multiplier `Λ` times a deterministic test, the form of that clause, is a special case.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionAngular
open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

/-- An `N × r` array of complex components: `Z i a` for label `i` and frame column `a`. -/
abbrev AngularArray (N r : ℕ) := Fin N → Fin r → ℂ

/-- `ev` selects eigenvectors spanning the eigenprojections `dysonProjection`: for every Hermitian `H` with
simple spectrum and every label `i`, `dysonProjection N H i = ev H i (ev H i)^*`.
The selection
need not be measurable.
-/
def IsEigenSelection (N : ℕ) (ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ) : Prop :=
  ∀ H : Matrix (Fin N) (Fin N) ℂ, H.IsHermitian → HasSimpleSpectrum N H → ∀ i : Fin N,
    dysonProjection N H i = Matrix.vecMulVec (ev H i) (star (ev H i))

/-- Components `Z i a = v_a^* u_i` of the eigenvectors `u_i` along the columns `v_a` of `V`. -/
def angularArray {N r : ℕ} (V : Matrix (Fin N) (Fin r) ℂ) (u : Fin N → Fin N → ℂ) :
    AngularArray N r :=
  fun i => Vᴴ *ᵥ u i

/-- `f` is invariant under an independent unimodular phase on each label. -/
def IsPhaseInvariant {N r : ℕ} (f : AngularArray N r → ℝ) : Prop :=
  ∀ θ : Fin N → ℂ, (∀ i, ‖θ i‖ = 1) → ∀ Z : AngularArray N r,
    f (fun i a => θ i * Z i a) = f Z

/-- The real rotation field `X_ij`: `z_i ↦ z_j`, `z_j ↦ -z_i`, other labels `0`. -/
def pairRotX {N r : ℕ} (i j : Fin N) (Z : AngularArray N r) : AngularArray N r :=
  fun k => if k = i then Z j else if k = j then -Z i else 0

/-- The complex rotation field `Y_ij`: `z_i ↦ i z_j`, `z_j ↦ i z_i`, other labels `0`. -/
def pairRotY {N r : ℕ} (i j : Fin N) (Z : AngularArray N r) : AngularArray N r :=
  fun k => if k = i then Complex.I • Z j else if k = j then Complex.I • Z i else 0

/-- **The complex angular generator** `¼ ∑_{i<j} c_ij (X_ij² + Y_ij²)` with couplings from
`lam`, where `A² f (Z) = D²f(Z)[AZ, AZ] + Df(Z)[A²Z]` for the linear fields
`A = X_ij, Y_ij`. -/
def complexAngularGenerator (N r : ℕ) (lam : Fin N → ℝ) (f : AngularArray N r → ℝ)
    (Z : AngularArray N r) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), dysonCoupling N lam i j *
    (fderiv ℝ (fderiv ℝ f) Z (pairRotX i j Z) (pairRotX i j Z) +
      fderiv ℝ f Z (pairRotX i j (pairRotX i j Z)) +
      fderiv ℝ (fderiv ℝ f) Z (pairRotY i j Z) (pairRotY i j Z) +
      fderiv ℝ f Z (pairRotY i j (pairRotY i j Z)))

/-- The σ-algebra of the eigenvalue path `σ(λ(F + G_{s+v}): v ≥ 0)`. -/
abbrev eigenPathSigma {Ω : Type*} (N : ℕ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ v : ℝ≥0, MeasurableSpace.comap (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) inferInstance

/-- **The complex angular martingale problem.** Let `G` be a Hermitian Brownian motion for
`𝓖`, let `F` be an `𝓖_0`-measurable Hermitian matrix and let `H_t = F + G_t`. Let `ev` be any
eigenvector selection. Fix a start time `s ≥ 0`, a frame `V ∈ ℂ^{N×r}` and a gap level `n > 0`,
and put `Z_v = (v_a^* u_i(H_{s+v}))_{i,a}`. Let `f` be a **random test**: for every `ω`, `f ω` is
`C²` and phase invariant; for every `Z`, `ω ↦ f ω Z` is measurable for
`𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)`; and on every ball `f ω`, `Df ω`, `D²f ω` are bounded uniformly
in `ω`. Then for every `u` the stopped variable
`f(Z_{u∧σ_n}) - f(Z_0) - ∫_0^{u∧σ_n} 𝒜_w f(Z_w) dw` is integrable and has expectation `0`.
Here `σ_n` is the gap stop and `𝒜_w = complexAngularGenerator` with couplings
`c_ij(w) = 1/(N(λ_i - λ_j)²)` at `H_{s+w}`. -/
def ComplexAngularMartingaleProblem (N r : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
    ∀ ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ, IsEigenSelection N ev →
    ∀ (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ), 0 < n →
    ∀ f : Ω → AngularArray N r → ℝ, (∀ ω, ContDiff ℝ 2 (f ω)) → (∀ ω, IsPhaseInvariant (f ω)) →
      (∀ Z, Measurable[𝓖 s ⊔ eigenPathSigma N F G s] fun ω => f ω Z) →
      (∀ R : ℝ, ∃ C : ℝ, ∀ ω Z, ‖Z‖ ≤ R →
        |f ω Z| ≤ C ∧ ‖fderiv ℝ (f ω) Z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (f ω)) Z‖ ≤ C) →
    ∀ u : ℝ≥0,
      let Z : ℝ≥0 → Ω → AngularArray N r := fun v ω => angularArray V (ev (F ω + G (s + v) ω))
      let e : Ω → ℝ := stoppedProcess (fun v ω =>
          f ω (Z v ω) - f ω (Z 0 ω) -
          ∫ w in Set.Ioc (0 : ℝ) v, complexAngularGenerator N r
            (dysonEigenvalue N (F ω + G (s + w.toNNReal) ω)) (f ω) (Z w.toNNReal ω))
        (gapStop N (fun t ω => F ω + G t ω) s n) u
      Integrable e Q ∧ ∫ ω, e ω ∂Q = 0

/-- **The complex angular contract**: the complex angular martingale problem for
every size `N` and frame rank `r`.
-/
structure ComplexAngularContract : Prop where
  angular : ∀ N r : ℕ, ComplexAngularMartingaleProblem N r

end BlockBand.Internal.Contracts.TransmissionAngular
