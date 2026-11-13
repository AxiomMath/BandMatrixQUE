module
public import BlockBand.SourceProcess.Stochastic.Basic
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Itô processes and the Itô formula: statements

An Itô process with values in a finite-dimensional real normed space `E` is an
augmented-adapted, almost surely continuous process
`X_t = X_0 + ∫_0^t b_s ds + ∑_a ∫_0^t σ_a(s) dW^a_s`
on the driver space, where the stochastic integral is the adopted integral
(`nativeIntegralOf`) applied after localization. The identity is required through every
continuous linear functional `ℓ : E →L[ℝ] ℝ`, so no basis is chosen. Matrix-valued
processes use `E = Matrix ι c ℂ` with any norm (e.g. the Frobenius instance).
-/

namespace BlockBand.SourceProcess.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The pathwise drift integral `∫_0^{t∧τ} b_s(x) ds`, as a Bochner integral over
`(0,t]` of the drift switched off after `τ`. -/
def stoppedDrift (τ : DriverSample S κ → WithTop ℝ≥0) (b : ℝ≥0 → DriverSample S κ → E)
    (t : ℝ≥0) (x : DriverSample S κ) : E :=
  ∫ s in Set.Ioc (0 : ℝ) t,
    if ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ x then b s.toNNReal x else 0

/-- The real integrand family `(s,x) ↦ ℓ(σ_a(s,x))` on `ℝ × Ω` (time read through
`Real.toNNReal`; only `s ∈ (0,T]` matters for `timeProbMeasure T`). -/
def functionalIntegrand (ℓ : E →L[ℝ] ℝ) (σ : κ → ℝ≥0 → DriverSample S κ → E) :
    κ → ℝ × DriverSample S κ → ℝ :=
  fun a p => ℓ (σ a p.1.toNNReal p.2)

variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- **Itô process** `dX = b dt + ∑_a σ_a dW^a` on `driverLaw μ`.

* `X` is adapted and progressively measurable for the augmented filtration and has a.s.
  continuous paths (progressive measurability is required explicitly: a.s. continuity alone
  does not control `X` on a null set, where joint measurability could fail);
* `b` and every `σ_a` are progressively measurable (augmented), `b` with a.s. locally
  integrable paths;
* there is a localizing sequence of augmented stopping times `τ_n → ⊤` a.s. such that
  every functional of the stopped diffusion is an integrand on every horizon;
* for every functional `ℓ`, augmented stopping time `τ` and horizon `T` for which the
  stopped integrand `ℓ∘σ·1{s ≤ τ}` is an integrand, and every `t ≤ T`,
  `ℓ(X_{t∧τ}) - ℓ(X_0) - ℓ(∫_0^{t∧τ} b ds)` equals the integral of
  `ℓ∘σ·1{s ≤ t∧τ}` almost surely. -/
structure IsNativeItoProcess (X : ℝ≥0 → DriverSample S κ → E) (b : ℝ≥0 → DriverSample S κ → E)
    (σ : κ → ℝ≥0 → DriverSample S κ → E) : Prop where
  adapted : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t)
  progressive : IsStronglyProgressive (driverAugmented (κ := κ) μ) X
  continuous : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => X t x
  drift_progressive : IsStronglyProgressive (driverAugmented (κ := κ) μ) b
  diffusion_progressive : ∀ a, IsStronglyProgressive (driverAugmented (κ := κ) μ) (σ a)
  drift_integrable : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0,
    IntegrableOn (fun s : ℝ => b s.toNNReal x) (Set.Ioc 0 t)
  localizing : ∃ τ : ℕ → DriverSample S κ → WithTop ℝ≥0,
    (∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (τ n)) ∧
    (∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => τ n x) atTop (𝓝 ⊤)) ∧
    ∀ n (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand (τ n) (functionalIntegrand ℓ σ))
  identity : ∀ (ℓ : E →L[ℝ] ℝ) (τ : DriverSample S κ → WithTop ℝ≥0),
    IsStoppingTime (driverAugmented (κ := κ) μ) τ → ∀ T : ℝ≥0,
    NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ σ)) → ∀ t ≤ T,
      ∃ hs : NativeIntegrand μ T
          (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) (functionalIntegrand ℓ σ)),
        (fun x => ℓ (stoppedProcess X τ t x) - ℓ (X 0 x) - ℓ (stoppedDrift τ b t x))
          =ᵐ[driverLaw (κ := κ) μ] (nativeIntegralOf hs : DriverSample S κ → ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Time derivative `∂_t φ(t,x)` of `φ : ℝ × E → F`. -/
def timeDeriv (φ : ℝ × E → F) (p : ℝ × E) : F := fderiv ℝ φ p (1, 0)

/-- Space derivative `D_x φ(t,x)[v]`. -/
def spaceDeriv (φ : ℝ × E → F) (p : ℝ × E) (v : E) : F := fderiv ℝ φ p (0, v)

/-- Second space derivative `D_x² φ(t,x)[v,w]`. -/
def spaceDeriv2 (φ : ℝ × E → F) (p : ℝ × E) (v w : E) : F :=
  fderiv ℝ (fderiv ℝ φ) p (0, v) (0, w)

/-- **Multidimensional time-dependent Itô formula** (space, values in `F`).

If `X` is an Itô process in `E` with drift `b` and diffusion `σ`, and
`φ : ℝ × E → F` is `C²`, then `φ(t, X_t)` is an Itô process with
* drift `∂_tφ(t,X_t) + D_xφ(t,X_t)[b_t] + ½ ∑_a D_x²φ(t,X_t)[σ_a(t), σ_a(t)]`,
* diffusion `a ↦ D_xφ(t,X_t)[σ_a(t)]`.
The Brownian coordinates are independent with `d[W^a,W^b] = δ_ab dt`.

Uses: the finite Gram law (Itô for `M = V*V`, `B = V*PV`, the projection identity
`(P')² = P'`, exterior powers `‖∧^k L‖²_HS`, the Gram drift); the duality step of the
transmission law (diffusion duality on a compact domain) and the dual boundary lemma (Itô for
`R`). Local (compact-domain) uses reduce to this global form by stopping and a `C²`
extension. -/
def ItoFormulaFor (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] : Prop :=
  ∀ (X : ℝ≥0 → DriverSample S κ → E) (b : ℝ≥0 → DriverSample S κ → E)
    (σ : κ → ℝ≥0 → DriverSample S κ → E), IsNativeItoProcess μ X b σ →
  ∀ φ : ℝ × E → F, ContDiff ℝ 2 φ →
    IsNativeItoProcess μ (fun t x => φ ((t : ℝ), X t x))
      (fun t x => timeDeriv φ ((t : ℝ), X t x) + spaceDeriv φ ((t : ℝ), X t x) (b t x) +
        (1 / 2 : ℝ) • ∑ a, spaceDeriv2 φ ((t : ℝ), X t x) (σ a t x) (σ a t x))
      (fun a t x => spaceDeriv φ ((t : ℝ), X t x) (σ a t x))

/-- **Bilinear (matrix) Itô product rule.** For Itô processes `X` in `E` and
`Y` in `F` and a real bilinear map `β : E →L F →L G` (e.g. matrix multiplication
`(A,B) ↦ A B`, or `(V,W) ↦ Vᴴ W` as a real-bilinear map),
`d β(X,Y) = β(dX, Y) + β(X, dY) + ∑_a β(σ^X_a, σ^Y_a) dt`. -/
def ItoProductRuleFor (E F G : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G]
    [BorelSpace G] : Prop :=
  ∀ (X : ℝ≥0 → DriverSample S κ → E) (bX : ℝ≥0 → DriverSample S κ → E)
    (σX : κ → ℝ≥0 → DriverSample S κ → E) (Y : ℝ≥0 → DriverSample S κ → F)
    (bY : ℝ≥0 → DriverSample S κ → F) (σY : κ → ℝ≥0 → DriverSample S κ → F),
    IsNativeItoProcess μ X bX σX → IsNativeItoProcess μ Y bY σY →
  ∀ β : E →L[ℝ] F →L[ℝ] G,
    IsNativeItoProcess μ (fun t x => β (X t x) (Y t x))
      (fun t x => β (bX t x) (Y t x) + β (X t x) (bY t x) + ∑ a, β (σX a t x) (σY a t x))
      (fun a t x => β (σX a t x) (Y t x) + β (X t x) (σY a t x))

end BlockBand.SourceProcess.Stochastic
