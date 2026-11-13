module
public import BlockBand.SourceProcess.Stochastic.Ito
public import Mathlib.Topology.EMetricSpace.Lipschitz
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Strong SDEs: statements

Time-homogeneous equations `dX = b(X) dt + ∑_a σ_a(X) dW^a`, `X_0 = ξ`, on the native
driver space, with `ξ` measurable for the augmented time-zero σ-algebra (so `ξ` may depend
on the old state). Solutions are Itô processes (`IsNativeItoProcess`). A solution
"until `τ`" has its coefficients switched off after `τ`; the exit-time form encodes
solutions up to explosion without partial processes.

Uses: the finite Gram law (local strong uniqueness and the nonnegative trace martingale `Tr M`
give nonexplosion), the linear near/far equations of its uniqueness step, and the dual boundary
lemma (nonexplosion through the martingale `R`). This file only states.
-/

namespace BlockBand.SourceProcess.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- First time `‖X_t‖ ≥ R` (`⊤` if never). -/
def exitTime (X : ℝ≥0 → DriverSample S κ → E) (R : ℝ) (x : DriverSample S κ) :
    WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : R ≤ ‖X t x‖), (t : WithTop ℝ≥0)

/-- A process switched off strictly after `τ`. -/
def switchOff {G : Type*} [Zero G] (τ : DriverSample S κ → WithTop ℝ≥0)
    (f : ℝ≥0 → DriverSample S κ → G) : ℝ≥0 → DriverSample S κ → G :=
  fun t x => if (t : WithTop ℝ≥0) ≤ τ x then f t x else 0

/-- The diffusion generator `𝓛φ(y) = Dφ(y)[b y] + ½ ∑_a D²φ(y)[σ_a y, σ_a y]`. -/
def sdeGenerator (b : E → E) (σ : κ → E → E) (φ : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ φ y (b y) + (1 / 2 : ℝ) * ∑ a, fderiv ℝ (fderiv ℝ φ) y (σ a y) (σ a y)

variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- `X` solves `dX = b(X) dt + ∑_a σ_a(X) dW^a`, `X_0 = ξ`, until `τ`. -/
def IsSDESolutionUntil (b : E → E) (σ : κ → E → E) (ξ : DriverSample S κ → E)
    (τ : DriverSample S κ → WithTop ℝ≥0) (X : ℝ≥0 → DriverSample S κ → E) : Prop :=
  IsNativeItoProcess μ X (switchOff τ fun t x => b (X t x))
      (fun a => switchOff τ fun t x => σ a (X t x)) ∧
    ∀ᵐ x ∂driverLaw (κ := κ) μ, X 0 x = ξ x

/-- A global (nonexplosive) solution: coefficients never switched off. -/
def IsSDESolution (b : E → E) (σ : κ → E → E) (ξ : DriverSample S κ → E)
    (X : ℝ≥0 → DriverSample S κ → E) : Prop :=
  IsSDESolutionUntil μ b σ ξ (fun _ => ⊤) X

/-- **Local strong well-posedness for locally Lipschitz coefficients.**
For locally Lipschitz `b, σ_a` and every augmented-`F_0`-measurable `ξ`:
* for every radius `R` there is a solution until its own exit time from the open
  `R`-ball, and any two such solutions are indistinguishable;
* any two global solutions are indistinguishable (pathwise uniqueness). -/
def LocalWellPosednessFor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  ∀ (b : E → E) (σ : κ → E → E), LocallyLipschitz b → (∀ a, LocallyLipschitz (σ a)) →
  ∀ ξ : DriverSample S κ → E, StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ →
    (∀ R : ℝ, ∃ X : ℝ≥0 → DriverSample S κ → E,
        IsSDESolutionUntil μ b σ ξ (exitTime X R) X) ∧
    (∀ (R : ℝ) (X Y : ℝ≥0 → DriverSample S κ → E),
        IsSDESolutionUntil μ b σ ξ (exitTime X R) X →
        IsSDESolutionUntil μ b σ ξ (exitTime Y R) Y →
        ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x = Y t x) ∧
    (∀ X Y : ℝ≥0 → DriverSample S κ → E, IsSDESolution μ b σ ξ X → IsSDESolution μ b σ ξ Y →
        ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x = Y t x)

/-- **Nonexplosion on an invariant closed set with a Lyapunov function.**
Let `b, σ` be locally Lipschitz, `ξ` augmented-`F_0`-measurable with values a.s. in a closed
set `K` that every exit-time solution keeps a.s. for all time, and let `Φ : E → ℝ` be `C²`,
nonnegative and coercive on `K`, with `𝓛Φ ≤ C (1 + Φ)` on `K`. Then a global solution
exists. (Instances: `Φ = Tr M = ‖V‖²_HS` with `𝓛Φ = 0` on the two-projection set for the
source equation; `Φ = R` for the dual diffusion.) -/
def NonexplosionFor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Prop :=
  ∀ (b : E → E) (σ : κ → E → E), LocallyLipschitz b → (∀ a, LocallyLipschitz (σ a)) →
  ∀ ξ : DriverSample S κ → E, StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ →
  ∀ K : Set E, IsClosed K → (∀ᵐ x ∂driverLaw (κ := κ) μ, ξ x ∈ K) →
    (∀ (R : ℝ) (X : ℝ≥0 → DriverSample S κ → E), IsSDESolutionUntil μ b σ ξ (exitTime X R) X →
        ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X t x ∈ K) →
  ∀ (Φ : E → ℝ) (C : ℝ), ContDiff ℝ 2 Φ → (∀ y ∈ K, 0 ≤ Φ y) →
    (∀ M : ℝ, ∃ R : ℝ, ∀ y ∈ K, R ≤ ‖y‖ → M ≤ Φ y) →
    (∀ y ∈ K, sdeGenerator b σ Φ y ≤ C * (1 + Φ y)) →
    ∃ X : ℝ≥0 → DriverSample S κ → E, IsSDESolution μ b σ ξ X

end BlockBand.SourceProcess.Stochastic
