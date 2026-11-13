module

public import BlockBand.Critical.RelativeVectors.AngularFields

/-!
# The angular martingale and reference flow statements

Definitions of the two stochastic statements used by the relative mixed-vector theorem.
`complexAngularMartingaleStatement_of_contract` derives the first from `ComplexAngularContract`;
`referenceFlowStatement_holds` proves the second.

* `ComplexAngularMartingaleStatement N r`: the conditional angular martingale problem of
  `Transmission.DysonBrownianMotion`, in the space-time, path-parametrized form that the Duhamel
  identity uses: time-dependent test functions `h(ω, v, z)` of the complex array
  `z_i = √N V^*u_i`, measurable in `ω` for the whole eigenvalue path σ-algebra, `C^{1,2}` with
  jointly continuous derivatives and bounds (`IsSpaceTimeAngularTest`), label-phase invariant;
  generator `∂_v + ¼ Σ_{i<j} c_ij (X_ij² + Y_ij²)`. The start time may be `s = 0` when the initial
  matrix has a.s. simple spectrum.
* `ReferenceFlowStatement N r`: one auxiliary probability space and propagators `𝓜, Ξ` depending
  jointly measurably on the flow sample (for `𝓛 = pathSigma F a a c`) and the auxiliary sample,
  which for every path with simple spectrum on `[a, c]` are a reference flow (`IsReferenceFlow`,
  with phase covariance in law and joint regularity of the backward function with
  `‖D^j g_s‖ ≤ ‖D^j f‖`), and whose mean squares `s ↦ E_aux |(𝓜_{s,c})_{kj}|²` solve
  `BackwardPropagator (referenceGenerator)` (for this one flow; no uniqueness is needed).

The test functions of the Duhamel argument depend on the whole eigenvalue path (the reference
coefficients on `[s, c]`), so they are measurable for the path σ-algebra but not adapted. This is
legitimate because, conditionally on the eigenvalue path, the angular Brownian motions are still
Brownian motions; the statement has exactly that conditional form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix ProbabilityTheory Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N r : ℕ}

/-!
## The space-time conditional angular martingale problem
-/

/-- σ-algebra of the whole eigenvalue path `σ(λ(H_{s+v}): v ≥ 0)` of `H_t = F + G_t` after
time `s`, with eigenvalues in increasing ranks.
-/
@[instance_reducible]
def eigenPathSigma {Ω : Type*} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ v : ℝ≥0, MeasurableSpace.comap
    (fun ω => fun i => freshEigenvalue (F ω + G (s + v) ω) i) inferInstance

/-- Admissible space-time test on the horizon `[0, T]`, with time derivative `ht`:
1. `ω ↦ h(ω, v, z)` and `ω ↦ ∂_v h(ω, v, z)` are `𝓛`-measurable (path-parametrized, not
   necessarily adapted);
2. `h(ω, v, ·)` is label-phase invariant;
3. `C^{1,2}`: `h(ω, v, ·)` is `C²` for `v ∈ [0, T]`; `∂_v h = ht` on `(0, T)`; `h`, `D_z h`,
   `D_z² h` are jointly continuous on `[0, T] × ℂ^{N×r}`, and `ht` on `(0, T) × ℂ^{N×r}`;
4. `|h|, ‖D_z h‖, ‖D_z² h‖ ≤ C` uniformly in `ω`, `v ∈ [0, T]`, `z`;
5. before the stopping time `σ(ω)` (the gap stop), `|∂_v h(ω, v, z)| ≤ C(1 + ‖z‖²)` uniformly
   (the backward functions of the Duhamel argument have `∂_v g = -𝓛_ref g`, whose coefficients
   are bounded while the gaps stay `≥ 1/n`). -/
structure IsSpaceTimeAngularTest {Ω : Type*} (𝓛 : MeasurableSpace Ω) (σ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ) : Prop where
  measurable : ∀ v z, Measurable[𝓛] (fun ω => h ω v z) ∧ Measurable[𝓛] (fun ω => ht ω v z)
  phase : ∀ ω v, IsLabelPhaseInvariant (h ω v)
  contDiff : ∀ ω, ∀ v ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (h ω v)
  hasDerivAt : ∀ ω z, ∀ v ∈ Ioo (0 : ℝ) T, HasDerivAt (fun v' => h ω v' z) (ht ω v z) v
  continuousOn : ∀ ω,
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => h ω p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (h ω p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (fderiv ℝ (h ω p.1)) p.2)
      (Icc (0 : ℝ) T ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => ht ω p.1 p.2) (Ioo (0 : ℝ) T ×ˢ univ)
  bound : ∃ C : ℝ, ∀ ω, ∀ v ∈ Icc (0 : ℝ) T, ∀ z,
    |h ω v z| ≤ C ∧ ‖fderiv ℝ (h ω v) z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (h ω v)) z‖ ≤ C
  time_bound : ∃ C : ℝ, ∀ ω, ∀ v ∈ Ioo (0 : ℝ) T,
    ((Real.toNNReal v : ℝ≥0) : WithTop ℝ≥0) < σ ω → ∀ z, |ht ω v z| ≤ C * (1 + ‖z‖ ^ 2)

/-- **The space-time conditional angular martingale problem.** Setting as in
`DysonBrownianMotion`: `G` a Hermitian Brownian motion for `𝓖`, `F` an `𝓖_0`-measurable Hermitian
matrix, `H_t = F + G_t`. For every start time `s` with `s > 0`, or `s = 0` when `F` has a.s.
simple spectrum, frame `V ∈ ℂ^{N×r}`, gap level `n > 0`, horizon `T`, every space-time test `h`
with time derivative `ht` (`IsSpaceTimeAngularTest` for the path σ-algebra
`𝓛_s = σ(λ(H_{s+v}) : v ≥ 0)` and the gap stop `σ_n`), every `u ≤ T` and every bounded
`𝓛_s`-measurable `Λ`, with `Z_v = frameArray V H_{s+v}` (`z_i = √N V^*u_i`):
`Λ (h(v, Z_v) - h(0, Z_0) - ∫_0^v (∂_x h + 𝒜_x h)(x, Z_x) dx)` stopped at `u ∧ σ_n` is
integrable with expectation `0`, `𝒜_x = complexAngularGenerator` with the couplings of
`λ(H_{s+x})`. This is the conditional (given the whole eigenvalue path) space-time Itô formula
for the unitary Dyson flow. It covers cross terms `v_a^*u_i u_i^*v_b`, joint functions of several
labels and frame columns, time dependence and path-dependent tests. -/
def ComplexAngularMartingaleStatement (N r : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ),
    IsHermitianBrownian Q 𝓖 N G → Measurable[𝓖 0] F → (∀ ω, (F ω).IsHermitian) →
  ∀ (s : ℝ≥0), (0 < s ∨ ∀ᵐ ω ∂Q, HasSimpleSpectrum N (F ω)) →
  ∀ (V : Matrix (Fin N) (Fin r) ℂ) (n : ℕ), 0 < n → ∀ (T : ℝ≥0)
    (h ht : Ω → ℝ → (Fin N → Fin r → ℂ) → ℝ),
    IsSpaceTimeAngularTest (eigenPathSigma F G s) (gapStop N (fun t ω => F ω + G t ω) s n) T
      h ht →
  ∀ (u : ℝ≥0), u ≤ T → ∀ (Λ : Ω → ℝ), Measurable[eigenPathSigma F G s] Λ →
    (∃ C, ∀ ω, |Λ ω| ≤ C) →
    let e : Ω → ℝ := fun ω => Λ ω * (stoppedProcess (fun (v : ℝ≥0) ω =>
        h ω (v : ℝ) (frameArray V (F ω + G (s + v) ω)) - h ω 0 (frameArray V (F ω + G s ω)) -
        ∫ x in Ioc (0 : ℝ) (v : ℝ),
          (ht ω x (frameArray V (F ω + G (s + x.toNNReal) ω)) +
            complexAngularGenerator N r
              (fun i => freshEigenvalue (F ω + G (s + x.toNNReal) ω) i) (h ω x)
              (frameArray V (F ω + G (s + x.toNNReal) ω))))
      (gapStop N (fun t ω => F ω + G t ω) s n) u ω)
    Integrable e Q ∧ ∫ ω, e ω ∂Q = 0

/-!
## The reference flow and its mean-square propagator
-/

/-- The auxiliary objects `(𝓜, Ξ)` on `(Ω_aux, P_aux)` are the reference flow of the fixed path
`ω` on `[a, c]`:
1. measurability, `𝓜_{s,s} = I`, `Ξ_{s,s} = 0`;
2. contraction `‖𝓜_{s,u} v‖₂ ≤ e^{-b₀N(u-s)/(2ℓ)} ‖v‖₂` for `a ≤ s ≤ u ≤ c`;
3.: jointly with `𝓜_{s,u}`, `Ξ_{s,u}` is circular Gaussian with
 `E ΞΞ^* = (I - 𝓜𝓜^*) ⊗ I_r`, `E ΞΞᵀ = 0`, in characteristic-functional form
 `E[h(𝓜) e^{i Re⟨w, Ξ⟩}] = E[h(𝓜) e^{-¼ Σ_q w_q^*(I - 𝓜𝓜^*)w_q}]` for bounded measurable `h`;
4. phase covariance in law: for every label phase `P_α = diag(e^{iα_i})`,
 `(P_α^{-1}𝓜_{s,u}P_α, P_α^{-1}Ξ_{s,u})` has the law of `(𝓜_{s,u}, Ξ_{s,u})` (the reference
 rotations and the circular OU noise are phase invariant in law); hence the backward function
 of a label-phase-invariant `f` is label-phase invariant;
5. backward equation with joint regularity (F1(b)): for every `f` with Euclidean bounded-`C²`
 constant `C` (`IsArrayC2Bounded C f`), `g_s(z) = E_aux f(𝓜_{s,c}z + Ξ_{s,c})` has, for every
 `s ∈ [a, c]`, the same constant (`‖D^j g_s‖ ≤ ‖D^j f‖`, from `‖𝓜‖₂ ≤ 1`);
`g`, `D_z g`,
 `D_z² g` are jointly continuous on `[a, c] × ℂ^{N×r}`, `𝓛_ref(s) g_s(z)` is jointly continuous
 on `(a, c) × ℂ^{N×r}`, and `∂_s g_s(z) = -(𝓛_ref(s) g_s)(z)` on `(a, c)`.
-/
structure IsReferenceFlow (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (ω : FlowSample N)
    {Ωaux : Type} [MeasurableSpace Ωaux] (Paux : Measure Ωaux)
    (𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ) (Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ) :
    Prop where
  measurable : ∀ s u, Measurable (𝓜 s u) ∧ Measurable (Ξ s u)
  initial : ∀ s ω', 𝓜 s s ω' = 1 ∧ Ξ s s ω' = 0
  contraction : ∀ s u, a ≤ s → s ≤ u → u ≤ c → ∀ ω' (v : Fin N → ℂ),
    l2Norm (𝓜 s u ω' *ᵥ v) ≤ Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) * l2Norm v
  covariance : ∀ s u, a ≤ s → s ≤ u → u ≤ c →
    ∀ h : Matrix (Fin N) (Fin N) ℂ → ℝ, Measurable h → (∃ C, ∀ M, |h M| ≤ C) →
    ∀ w : Fin N → Fin r → ℂ,
      ∫ ω', (h (𝓜 s u ω') : ℂ) * Complex.exp (Complex.I *
          (∑ i, ∑ q, (star (w i q) * Ξ s u ω' i q).re : ℝ)) ∂Paux =
        ∫ ω', (h (𝓜 s u ω') * Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
          (star (fun i => w i q) ⬝ᵥ ((1 - 𝓜 s u ω' * (𝓜 s u ω')ᴴ) *ᵥ fun i => w i q)).re) : ℂ)
          ∂Paux
  phase_covariant : ∀ s u, a ≤ s → s ≤ u → u ≤ c → ∀ α : Fin N → ℝ,
    Paux.map (fun ω' => (labelPhaseMatrix α (𝓜 s u ω'), labelPhase (fun i => -α i) (Ξ s u ω'))) =
      Paux.map (fun ω' => (𝓜 s u ω', Ξ s u ω'))
  backward : ∀ (C : ℝ) (f : (Fin N → Fin r → ℂ) → ℝ), IsArrayC2Bounded C f →
    let g : ℝ → (Fin N → Fin r → ℂ) → ℝ :=
      fun s z => ∫ ω', f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux
    (∀ s ∈ Icc a c, IsArrayC2Bounded C (g s)) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => g p.1 p.2) (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (g p.1) p.2) (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (fderiv ℝ (g p.1)) p.2)
      (Icc a c ×ˢ univ) ∧
    ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
      referenceArrayGenerator F a b₀ ω ℓ p.1 (g p.1) p.2) (Ioo a c ×ˢ univ) ∧
    ∀ z, ∀ s ∈ Ioo a c,
      HasDerivAt (fun s' => g s' z) (-(referenceArrayGenerator F a b₀ ω ℓ s (g s) z)) s

/-- For every Hermitian `F`, `a < c`, damping floor `b₀ > 0` and short range `ℓ ≥ 1` there are one
auxiliary probability space and maps `𝓜(ω, s, u, ω')`, `Ξ(ω, s, u, ω')`, jointly measurable for
`𝓛 ⊗ Borel(Ω_aux)` with `𝓛 = pathSigma F a a c` (measurability in the eigenvalue path),
such that for every flow sample `ω` whose eigenvalue path has simple spectrum on `[a, c]` (so the
couplings are finite):
* `(𝓜(ω), Ξ(ω))` is a reference flow of that path (`IsReferenceFlow`): existence of the
  auxiliary linear Stratonovich SDE with path-dependent short rotations and Ornstein–Uhlenbeck
  damping `½β̂_i`, its solution `ẑ(u) = 𝓜_{s,u}z(s) + Ξ_{s,u}`, the reference covariance identity,
  phase covariance and the regular backward equation;
* `P(s)_{kj} = E_aux |(𝓜_{s,c})_{kj}|²` solves `BackwardPropagator (referenceGenerator F a b₀ ω ℓ)
  a c`. Only this one flow is concerned, so no uniqueness of the backward equation is needed;
  `RelativeLocalizationContract.reference_finite_speed` bounds every solution on its good event,
  in particular this one. -/
def ReferenceFlowStatement (N r : ℕ) : Prop :=
  ∀ (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ),
    F.IsHermitian → a < c → 0 < b₀ → 0 < ℓ →
    ∃ (Ωaux : Type) (_ : MeasurableSpace Ωaux) (Paux : Measure Ωaux),
      IsProbabilityMeasure Paux ∧
      ∃ (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
        (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ),
        (∀ s u,
          Measurable[MeasurableSpace.comap Prod.fst (BlockBand.Palm.MomentFlow.pathSigma F a a c) ⊔
              MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
            (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
          Measurable[MeasurableSpace.comap Prod.fst (BlockBand.Palm.MomentFlow.pathSigma F a a c) ⊔
              MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
            (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2)) ∧
        ∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
          IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω) ∧
          BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c
            (fun s k j => ∫ ω', ‖𝓜 ω s c ω' k j‖ ^ 2 ∂Paux)

end BlockBand.Critical.RelativeVectors
