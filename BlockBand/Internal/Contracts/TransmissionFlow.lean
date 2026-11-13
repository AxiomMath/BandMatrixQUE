module

public import BlockBand.SourceProcess.Stochastic.Ito
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Matrix.Basis

/-!
# Linear rotation–damping flows and their mass equations

**Equation.** The homogeneous Stratonovich flow with the short skew-Hermitian rotations
`X_ij e_i = e_j, X_ij e_j = -e_i`, `Y_ij e_i = i e_j, Y_ij e_j = i e_i` with coefficient
`√(r_ij/2)` (`i < j`) and damping `½ diag(κ)` has Itô form
`d𝓜 = ∑_{i<j} √(r_ij/2) (X_ij dW_((i,j),0) + Y_ij dW_((i,j),1)) 𝓜 − ½ diag(∑_{m≠k} r_km + κ_k) 𝓜 dt`,
`𝓜_{s,s} = I`; the rotation Itô correction is `-½ diag(∑_{m≠k} r_km)`. The statement below
asserts existence and uniqueness of the flow and identifies the mean squared entries of its
propagator with solutions of the forward and backward one-particle mass equations.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionFlow
open MeasureTheory Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ}

/-- The forward mass equation `∂_u v = L(u) v` on `[s,u]` with `v(s) = v₀` (the same definition
as `CoareaPalm.ForwardMassSolution`). -/
def ForwardMassSolution (L : ℝ → Fin N → Fin N → ℝ) (s u : ℝ) (v₀ : Fin N → ℝ)
    (v : ℝ → Fin N → ℝ) : Prop :=
  v s = v₀ ∧ ContinuousOn v (Set.Icc s u) ∧
    ∀ x ∈ Set.Ioo s u, HasDerivAt v (fun k => ∑ l, L x k l * v x l) x

/-- The backward propagator: `∂_s P(s) = -P(s) L(s)` on `[a,c]`, `P(c) = I` (the same
definition as `CoareaPalm.BackwardPropagator`).
-/
def BackwardPropagator (L : ℝ → Fin N → Fin N → ℝ) (a c : ℝ) (P : ℝ → Fin N → Fin N → ℝ) :
    Prop :=
  P c = (fun k l => if k = l then 1 else 0) ∧ ContinuousOn P (Set.Icc a c) ∧
    ∀ x ∈ Set.Ioo a c, HasDerivAt P (fun k l => -∑ m, P x k m * L x m l) x

/-- The one-particle mass generator `(L v)_k = ∑_{l≠k} r_kl (v_l − v_k) − κ_k v_k`. -/
def massGenerator (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (x : ℝ) (k l : Fin N) : ℝ :=
  if k = l then -(∑ m ∈ Finset.univ.erase k, r x k m) - κ x k else r x k l

/-- Real rotation `X_ij`: `X e_i = e_j`, `X e_j = -e_i`. -/
def rotX (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ := Matrix.single j i 1 - Matrix.single i j 1

/-- Phase rotation `Y_ij`: `Y e_i = i e_j`, `Y e_j = i e_i`. -/
def rotY (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Complex.I • (Matrix.single j i 1 + Matrix.single i j 1)

/-- Itô diffusion coefficient along the noise coordinate `((i,j),q)`: `√(r_ij/2) X_ij` (`q = 0`)
or `√(r_ij/2) Y_ij` (`q = 1`) for `i < j`, and `0` for `i ≥ j`. -/
def rotationNoise (r : Fin N → Fin N → ℝ) (α : (Fin N × Fin N) × Fin 2) :
    Matrix (Fin N) (Fin N) ℂ :=
  if α.1.1 < α.1.2 then ((Real.sqrt (r α.1.1 α.1.2 / 2) : ℝ) : ℂ) •
    (if α.2 = 0 then rotX α.1.1 α.1.2 else rotY α.1.1 α.1.2) else 0

/-- Itô drift coefficient `-½ diag(∑_{m≠k} r_km + κ_k)` (rotation correction plus damping). -/
def rotationDrift (r : Fin N → Fin N → ℝ) (κ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun k => (((-(1 / 2 : ℝ)) * ((∑ m ∈ Finset.univ.erase k, r k m) + κ k) : ℝ) : ℂ)

/-- Time clamped to `[a, c]` (coefficients are constant outside the interval). -/
def clampTime (a c x : ℝ) : ℝ := max a (min x c)

/-- `M` is the propagator `t ↦ 𝓜_{s,s+t}` of the linear rotation–damping flow started at time
`s` with the identity, coefficients evaluated at the clamped time `s + t`: an Itô process in
`Matrix (Fin N) (Fin N) ℂ` with drift `rotationDrift · M` and diffusion `rotationNoise · M`. -/
def IsRotationFlow {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (a c s : ℝ)
    (M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsNativeItoProcess μ M
      (fun t x => rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t))) * M t x)
      (fun α t x => rotationNoise (r (clampTime a c (s + t))) α * M t x) ∧
    ∀ x, M 0 x = 1

/-- **Linear rotation–damping flows and their mass equations.**
For deterministic coefficients on `[a,c]` — rates `r` continuous, symmetric, nonnegative and
damping `κ` continuous, nonnegative — and every start time `s ∈ [a,c]`:
* (existence) the propagator `IsRotationFlow` exists;
* (uniqueness) any two are indistinguishable;
* (forward mass equation) for every `v₀`, `v_k(x) = E ∑_j |𝓜_{s,x}(k,j)|² v₀_j`
  solves `ForwardMassSolution (massGenerator r κ) s c v₀`;
* (backward propagator) for every family of propagators `𝓜_{x,·}`, `x ∈ [a,c]`,
  `P(x)_{kj} = E |𝓜_{x,c}(k,j)|²` satisfies `BackwardPropagator (massGenerator r κ) a c`.
Expectations are over `driverLaw μ` (the auxiliary noise). -/
def LinearRotationFlowContract (N : ℕ) : Prop :=
  ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (a c : ℝ), a ≤ c →
    ContinuousOn r (Set.Icc a c) → ContinuousOn κ (Set.Icc a c) →
    (∀ x k l, r x k l = r x l k) → (∀ x k l, 0 ≤ r x k l) → (∀ x k, 0 ≤ κ x k) →
    (∀ s ∈ Set.Icc a c, ∃ M, IsRotationFlow μ r κ a c s M) ∧
    (∀ s ∈ Set.Icc a c, ∀ M M', IsRotationFlow μ r κ a c s M → IsRotationFlow μ r κ a c s M' →
      ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t, M t x = M' t x) ∧
    (∀ s ∈ Set.Icc a c, ∀ M, IsRotationFlow μ r κ a c s M → ∀ v₀ : Fin N → ℝ,
      ForwardMassSolution (massGenerator r κ) s c v₀ (fun x k =>
        ∫ ω, ∑ j, ‖M (x - s).toNNReal ω k j‖ ^ 2 * v₀ j
          ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ)) ∧
    (∀ Mf : ℝ → ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ,
      (∀ x ∈ Set.Icc a c, IsRotationFlow μ r κ a c x (Mf x)) →
      BackwardPropagator (massGenerator r κ) a c (fun x k j =>
        ∫ ω, ‖Mf x (c - x).toNNReal ω k j‖ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ))

end BlockBand.Internal.Contracts.TransmissionFlow
