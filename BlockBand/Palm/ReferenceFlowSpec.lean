module

public import BlockBand.Palm.RelativeLocalizationBridgeRates

/-!
# The reference flow of the relative mixed-vectors theorem (statements)

Definitions and statements only; no proofs.

**Setting.** Conditionally on the eigenvalue path, the short rates `r_ij(σ)` and the damping
`κ_i(σ) = β̂_i(σ)` are deterministic (the auxiliary noises are independent of the path), and
continuous on `[a,c]` on collision-free paths. So the statement is first given for deterministic
coefficients (`IsReferenceFlow`, generic in `r, κ`), then along every collision-free sample of
`flowLaw` (`ReferenceFlowStatement`, coefficients `shortRate`, `refDamping`; collision-free
paths have full measure, `ae_noCollision`). The auxiliary randomness lives on the driver space
`DriverSample S ((Fin N × Fin N) × Fin 2)` with law `driverLaw μ`.

**State.** An `N × p` array `z = (z_i)_{i < N}`, `z_i ∈ ℂ^p` (`RefState N p`, the marks
`z_i = √N V^*u_i` of all labels, `p` the frame rank). A matrix `K` acts on the label index
(`lmul K z = K z`).

**Reference flow** (Itô form): short rotations `√(r_ij/2)(X_ij dW + Y_ij dW')`
(Stratonovich), damping `-½κ_i z_i ds`, and independent circular Ornstein–Uhlenbeck noise
`√κ_i dC_i`, `E dC_i dC_i^* = I_p ds`. Its generator on `C²` functions is `refGenerator r κ s`:
`¼ Σ_{i<j} r_ij(s) (X_ij² + Y_ij²) + Σ_i κ_i(s) (-½ z_i·∂_{z_i} + ¼ Δ_{z_i})`, where
`X² g(z) = D²g(z)[Xz, Xz] + Dg(z)[X X z]` is the square of the linear vector field `z ↦ Xz`
and `Δ_{z_i}` is the real Laplacian in the `2p` real coordinates of `z_i`. The short part has the
same form as the true angular generator, so the short generators cancel in the Duhamel identity.

**Solution.** `ẑ(c) = K_s z(s) + Ξ_s`, `Ξ_s` circular Gaussian given `K_s` with
`Cov Ξ_s = (I - K_sK_s^*) ⊗ I_p`, `E Ξ Ξᵀ = 0`. In `IsReferenceFlow` this is `Ξ_s = L_s G`
with `G` standard circular (`matCircularLaw`) and `L_s L_s^* = I - K_s K_s^*`; the law of the
reference flow from time `s` to `c` started at `z` is that of `K_s z + L_s G`, and its backward
function is `g_s = refSemigroup μ K L f s`. `K_s` is the propagator `𝓜_{s,c}` in law; it is not
required to be the pathwise propagator of a two-parameter flow, because only its law enters
`g_s`, the contraction and the mass identity.

**Clauses of `IsReferenceFlow`** (structure fields, all for `s ∈ [a,c]`):
* `IsReferenceFlow.covariance`: `L_s L_s^* = I - K_s K_s^*` a.s.;
* `IsReferenceFlow.contraction`: if `κ ≥ b` on `[a,c]` then `‖K_s v‖² ≤ e^{-b(c-s)} ‖v‖²` a.s.;
* `IsReferenceFlow.factor_continuous`, `IsReferenceFlow.factor_hermitian`: `L_s` is Hermitian and a.s. continuous in `s` on
  `[a,c]` (so `g_s`, `Dg_s`, `D²g_s` are jointly continuous in `(s,z)` through the
  representations below);
* `IsReferenceFlow.factor_near_one`: under the same floor `‖(I - L_s)v‖² ≤ e^{-2b(c-s)} ‖v‖²` a.s., i.e.
  `‖I - L_s‖ ≤ ‖K_sK_s^*‖` as for the principal root `(I - K_sK_s^*)^{1/2}`; with
  the contraction clause this gives the terminal bounded-Lipschitz coupling of `K_a z + L_a G` to `G`;
* `IsReferenceFlow.mass`: `P(s)_{kj} = E_aux |(K_s)_{kj}|²` is a `BackwardPropagator (massGenerator r κ) a c`;
  with `r = shortRate`, `κ = refDamping` this is `referenceGenerator`
  (`referenceGenerator_eq_massGenerator`); `IsReferenceFlow.mass_unique`: every such backward propagator equals
  `E_aux |(K_s)_{kj}|²` on `[a,c]`;
* `IsReferenceFlow.backward`: for every bounded-`C²` test `f` on `RefState N p` (`IsC2BoundedBy`),
  `g_s = refSemigroup μ K L f s` has `g_c = f`, is continuous in `s`, `C²` in `z` with the
  derivative representations `Dg_s(z)[h] = E Df(K_s z + L_s G)[K_s h]`,
  `D²g_s(z)[h,h'] = E D²f(K_s z + L_s G)[K_s h, K_s h']`, and solves the backward Kolmogorov
  equation `∂_s g_s(z) = -refGenerator r κ s g_s (z)` on `(a,c)`.

`ReferenceFlowExistence N`: such `(K, L)` exist for all deterministic coefficients with a
positive damping floor. `ReferenceFlowStatement`: the same along every collision-free eigenvalue
path, with the coefficients `shortRate` and `refDamping`; `ReferenceFlowAEStatement`: the same
for `flowLaw`-a.e. sample. `ReferenceKernelFiniteSpeedStatement`: the reference finite-speed
bound for every such `K`.

The statements are pathwise in the eigenvalue sample `ω` (`∀ ω, NoCollision → ∃ K L`): `K, L`
and hence `g_s` are not claimed measurable in `ω`; they are used at a fixed path, inside the
conditional law given the path. Only the terminal time `u = c` of the two-parameter propagator
`𝓜_{s,u}` is provided.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Matrix BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (rotX rotY massGenerator)
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Palm.RelativeLocalization.StochasticBridge (shortRate refDamping NoCollision)
open scoped NNReal ENNReal

variable {N p : ℕ}

/-- Coordinates `((i,j),q)` of the rotation noises. -/
abbrev RotIdx (N : ℕ) := (Fin N × Fin N) × Fin 2

/-- The `N × p` array of marks `z = (z_i)_i`, `z_i ∈ ℂ^p` (sup norm on the product). -/
abbrev RefState (N p : ℕ) := Fin N → Fin p → ℂ

/-- A matrix acting on the label index: `(K z)_i = Σ_j K_ij z_j`. -/
def lmul (K : Matrix (Fin N) (Fin N) ℂ) (z : RefState N p) : RefState N p :=
  fun i α => ∑ j, K i j * z j α

/-- Standard circular Gaussian `N × p` array (i.i.d. `CN(0,1)` entries, `E GG^* = p I`,
`E|G_iα|² = 1`). -/
def matCircularLaw (N p : ℕ) : Measure (RefState N p) :=
  (circularVectorLaw (Fin N × Fin p)).map fun g i α => g (i, α)

/-- Second derivative `D²g(z)[u,v]`. -/
def D2 (g : RefState N p → ℝ) (z u v : RefState N p) : ℝ :=
  fderiv ℝ (fderiv ℝ g) z u v

/-- `X² g(z)` for the linear vector field `z ↦ Xz`: `D²g(z)[Xz,Xz] + Dg(z)[X X z]`. -/
def vfSq (X : Matrix (Fin N) (Fin N) ℂ) (g : RefState N p → ℝ) (z : RefState N p) : ℝ :=
  D2 g z (lmul X z) (lmul X z) + fderiv ℝ g z (lmul X (lmul X z))

/-- The array with a single entry `1` at `(i, α)`. -/
def unitEntry (i : Fin N) (α : Fin p) : RefState N p :=
  fun k β => if k = i ∧ β = α then 1 else 0

/-- The row `z_i` alone (`E_ii z`). -/
def rowProj (i : Fin N) (z : RefState N p) : RefState N p :=
  fun k β => if k = i then z k β else 0

/-- **Generator of the reference flow** at time `s`:
`¼ Σ_{i<j} r_ij(s) (X_ij² + Y_ij²) g + Σ_i κ_i(s) (-½ Dg[z_i] + ¼ Δ_{z_i} g)`, with `X_ij, Y_ij`
the rotations `rotX`, `rotY` (`X e_i = e_j`, `X e_j = -e_i`, `Y e_i = i e_j`, `Y e_j = i e_i`) and
`Δ_{z_i} = Σ_α (∂²_{Re z_iα} + ∂²_{Im z_iα})`. -/
def refGenerator (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (s : ℝ)
    (g : RefState N p → ℝ) (z : RefState N p) : ℝ :=
  (1 / 4 : ℝ) * ∑ i : Fin N, ∑ j : Fin N,
      (if i < j then r s i j * (vfSq (rotX i j) g z + vfSq (rotY i j) g z) else 0) +
    ∑ i : Fin N, κ s i * (-(1 / 2 : ℝ) * fderiv ℝ g z (rowProj i z) +
      (1 / 4 : ℝ) * ∑ α : Fin p, (D2 g z (unitEntry i α) (unitEntry i α) +
        D2 g z (Complex.I • unitEntry i α) (Complex.I • unitEntry i α)))

/-- Bounded `C²` with bound `C`: `|f|, ‖Df‖, ‖D²f‖ ≤ C`. -/
structure IsC2BoundedBy {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (C : ℝ)
    (f : X → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  bound : ∀ z, |f z| ≤ C
  deriv_bound : ∀ z, ‖fderiv ℝ f z‖ ≤ C
  hessian_bound : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ C

variable {S : Type} [MeasurableSpace S]

/-- **Backward function of the reference flow**:
`g_s(z) = E_aux E_G f(K_s z + L_s G)`. -/
def refSemigroup (μ : Measure S) (K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ)
    (f : RefState N p → ℝ) (s : ℝ) (z : RefState N p) : ℝ :=
  ∫ y, ∫ G, f (lmul (K s y) z + lmul (L s y) G) ∂matCircularLaw N p
    ∂driverLaw (κ := RotIdx N) μ

/-- **The reference flow on `[a,c]`** for deterministic coefficients `r, κ`: `K_s` is the propagator
from `s` to `c` (in law), `L_s G` the Ornstein–Uhlenbeck integral.
See the module docstring for the clauses. -/
structure IsReferenceFlow (μ : Measure S) (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ)
    (a c : ℝ) (K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ) : Prop where
  measurable_kernel : ∀ s, Measurable (K s)
  measurable_factor : ∀ s, Measurable (L s)
  continuous : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ContinuousOn (fun s => K s y) (Icc a c)
  terminal : ∀ y, K c y = 1
  covariance : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c,
    L s y * (L s y)ᴴ = 1 - K s y * (K s y)ᴴ
  contraction : ∀ b : ℝ, (∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) →
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ,
      ∑ k, ‖(K s y *ᵥ v) k‖ ^ 2 ≤ Real.exp (-(b * (c - s))) * ∑ k, ‖v k‖ ^ 2
  factor_continuous : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ContinuousOn (fun s => L s y) (Icc a c)
  factor_hermitian : ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, (L s y).IsHermitian
  factor_near_one : ∀ b : ℝ, (∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) →
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ,
      ∑ k, ‖((1 - L s y) *ᵥ v) k‖ ^ 2 ≤ Real.exp (-(2 * b * (c - s))) * ∑ k, ‖v k‖ ^ 2
  mass : BackwardPropagator (massGenerator r κ) a c
    (fun s k j => ∫ y, ‖K s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ)
  mass_unique : ∀ P : ℝ → Fin N → Fin N → ℝ, BackwardPropagator (massGenerator r κ) a c P →
    ∀ s ∈ Icc a c, ∀ k j, ∫ y, ‖K s y k j‖ ^ 2 ∂driverLaw (κ := RotIdx N) μ = P s k j
  backward : ∀ (p : ℕ) (C : ℝ) (f : RefState N p → ℝ), IsC2BoundedBy C f →
    (∀ z, refSemigroup μ K L f c z = f z) ∧
    (∀ z, ContinuousOn (fun s => refSemigroup μ K L f s z) (Icc a c)) ∧
    (∀ s ∈ Icc a c, ContDiff ℝ 2 (refSemigroup μ K L f s)) ∧
    (∀ s ∈ Icc a c, ∀ z h, fderiv ℝ (refSemigroup μ K L f s) z h =
      ∫ y, ∫ G, fderiv ℝ f (lmul (K s y) z + lmul (L s y) G) (lmul (K s y) h)
        ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ) ∧
    (∀ s ∈ Icc a c, ∀ z h h', D2 (refSemigroup μ K L f s) z h h' =
      ∫ y, ∫ G, D2 f (lmul (K s y) z + lmul (L s y) G) (lmul (K s y) h) (lmul (K s y) h')
        ∂matCircularLaw N p ∂driverLaw (κ := RotIdx N) μ) ∧
    (∀ s ∈ Ioo a c, ∀ z, HasDerivAt (fun x => refSemigroup μ K L f x z)
      (-refGenerator r κ s (refSemigroup μ K L f s) z) s)

/-- **Existence for deterministic coefficients.** For continuous symmetric nonnegative rates `r`,
continuous damping `κ` with a positive floor `b`, on any auxiliary space, a reference flow
exists. -/
def ReferenceFlowExistence (N : ℕ) : Prop :=
  ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (a c b : ℝ), a ≤ c → 0 < b →
    ContinuousOn r (Icc a c) → ContinuousOn κ (Icc a c) →
    (∀ x k l, r x k l = r x l k) → (∀ x k l, 0 ≤ r x k l) → (∀ x k, 0 ≤ κ x k) →
    (∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) →
    ∃ K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ,
      IsReferenceFlow μ r κ a c K L

/-- **Existence along the eigenvalue path.** For Hermitian `F`, `0 < a ≤ c`, damping floor
`b₀ > 0` and short range `ℓ ≥ 1`: for every collision-free sample `ω` of `flowLaw N a`
(`NoCollision`: simple spectrum on all of `[a,c]`), on every auxiliary space, the reference flow
with the coefficients (`shortRate`: all short rotations, no bulk cut; `refDamping`:
`β̂ = max(β, b₀N/ℓ)`) exists. -/
def ReferenceFlowStatement : Prop :=
  ∀ (N : ℕ) (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → 0 < N →
    ∀ a c : ℝ, 0 < a → a ≤ c → ∀ b₀ : ℝ, 0 < b₀ → ∀ ℓ : ℕ, 0 < ℓ →
    ∀ ω : FlowSample N, NoCollision F a c ω → ∀ (S : Type) [MeasurableSpace S] (μ : Measure S)
      [IsProbabilityMeasure μ],
      ∃ K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ,
        IsReferenceFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c K L

/-- `ReferenceFlowStatement` for `flowLaw N a`-almost every sample. -/
def ReferenceFlowAEStatement : Prop :=
  ∀ (N : ℕ) (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → 0 < N →
    ∀ a c : ℝ, 0 < a → a ≤ c → ∀ b₀ : ℝ, 0 < b₀ → ∀ ℓ : ℕ, 0 < ℓ →
    ∀ᵐ ω ∂flowLaw N a, ∀ (S : Type) [MeasurableSpace S] (μ : Measure S)
      [IsProbabilityMeasure μ],
      ∃ K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ,
        IsReferenceFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c K L

/-- **Reference finite speed for the reference kernels.** Same quantifiers, scales and window `J`
as `RelativeLocalizationContract.reference_finite_speed`; the integrand is
`E_aux Σ_{j∉J} |(K_s)_{kj}|²` for every reference flow `(K, L)` of the path. -/
def ReferenceKernelFiniteSpeedStatement : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ b₀ : ℝ, 0 < b₀ → ∀ Cw D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ))
      let a : ℝ := c - t
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
      let w : ℕ := ⌈(N : ℝ) * Real.sqrt t * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
      ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      flowLaw N a {ω | ∃ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N ∧
          ∃ K L : ℝ → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ,
            IsReferenceFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c K L ∧
            ENNReal.ofReal ((N : ℝ) ^ (-D)) <
              ∫⁻ s in Set.Icc a c, ENNReal.ofReal (∫ y, ∑ j : Fin N,
                (if Int.natAbs ((j : ℤ) -
                    ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
                  then 0 else 1) * ‖K s y k j‖ ^ 2
                ∂driverLaw (κ := RotIdx N) μ)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

end BlockBand.Palm.ReferenceFlow
