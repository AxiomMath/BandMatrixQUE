module
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Matrix.Normed
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Martingale problems on arbitrary filtered spaces: statements

Diffusion martingale problems in real coordinates `ℝ^d = Fin d → ℝ`, with drift `b` and
covariance `a`, on an arbitrary filtered probability space `(Ω, 𝓖, Q)` (no usual
conditions). Localization is by exit from every open `W` with compact closure inside the
domain `U`, so no global integrability is assumed.

Why these are needed beyond the Brownian space: the paper applies Itô's formula
and stopped-law uniqueness to processes that are *only* known as martingale-problem
solutions —
* the dual boundary lemma: Itô for `R = ∑(x_i+y_i)`, and on each relatively compact interior
  domain the coefficients of `𝒟_p` are smooth and the diffusion matrix is strictly positive, so
  the stopped law is unique;
* the finite Gram law: the rank barrier `𝒢 e_k(B) ≤ C e_k(B)` holds for every solution, and
  local uniqueness in smooth Gram charts;
* the transmission law: diffusion duality on compact domains by Itô.
This file only states.
-/

namespace BlockBand.SourceProcess.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ}

/-- First time the path leaves `W` (`⊤` if never). -/
def exitTimeFrom {Ω : Type*} (W : Set (Fin d → ℝ)) (Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : Y t ω ∉ W), (t : WithTop ℝ≥0)

/-- `W` is a relatively compact subdomain of `U`: open, compact closure inside `U`. -/
def IsInteriorDomain (W U : Set (Fin d → ℝ)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U

/-- The generator `𝓛φ = ∑ b_i ∂_iφ + ½ ∑ a_ij ∂_ij φ`. -/
def mpGenerator (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (φ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  ∑ i, b y i * fderiv ℝ φ y (Pi.single i 1) +
    (1 / 2 : ℝ) * ∑ i, ∑ j, a y i j * fderiv ℝ (fderiv ℝ φ) y (Pi.single i 1) (Pi.single j 1)

/-- Compensated coordinate `Y^i_t - Y^i_0 - ∫_0^t b_i(Y_s) ds`. -/
def mpCompensated {Ω : Type*} (b : (Fin d → ℝ) → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (i : Fin d) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Y t ω i - Y 0 ω i - ∫ s in Set.Ioc (0 : ℝ) t, b (Y s.toNNReal ω) i

/-- `Y` solves the `(b, a)` martingale problem in the domain `U`, localized by exits from
relatively compact subdomains: for every such `W`, the coordinates compensated by `∫ b` and
their products compensated by `∫ a`, stopped at the exit from `W`, have `𝓖`-martingale
modifications (modification form, matching the conclusion of `MartingaleProblemIto`). -/
structure IsMPSolutionOn {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U : Set (Fin d → ℝ)) (Y : ℝ≥0 → Ω → Fin d → ℝ) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (Y t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω
  drift : ∀ W, IsInteriorDomain W U → ∀ i, ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t
  bracket : ∀ W, IsInteriorDomain W U → ∀ i j, ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => mpCompensated b Y i t ω * mpCompensated b Y j t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j) (exitTimeFrom W Y) t

/-- **Itô's formula for martingale-problem solutions.** If `b, a` are continuous on
the open set `U` and `Y` solves the `(b,a)` martingale problem in `U`, then for every
`φ ∈ C²(U)` and every relatively compact subdomain `W`, the process
`φ(Y_t) - φ(Y_0) - ∫_0^t 𝓛φ(Y_s) ds` stopped at the exit from `W` has a `𝓖`-martingale
modification (equal a.s. at every time).

The conclusion is a modification, not the raw process: paths are continuous only a.s. and
`𝓖` is not completed (on a null set the raw process need not be `𝓖_t`-measurable). -/
def MartingaleProblemIto (d : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U : Set (Fin d → ℝ)), IsOpen U → ContinuousOn b U → ContinuousOn a U →
  ∀ Y : ℝ≥0 → Ω → Fin d → ℝ, IsMPSolutionOn Q 𝓖 b a U Y →
  ∀ φ : (Fin d → ℝ) → ℝ, ContDiffOn ℝ 2 φ U →
  ∀ W, IsInteriorDomain W U →
    ∃ Mφ : ℝ≥0 → Ω → ℝ, Martingale Mφ 𝓖 Q ∧ ∀ t,
      Mφ t =ᵐ[Q] stoppedProcess (fun t ω => φ (Y t ω) - φ (Y 0 ω) -
        ∫ s in Set.Ioc (0 : ℝ) t, mpGenerator b a φ (Y s.toNNReal ω)) (exitTimeFrom W Y) t

/-- **Stopped-law uniqueness with a locally Lipschitz square root.** Let `b` and `σ`
be locally Lipschitz on the open set `U`, `a = σ σᵀ`, and `W` a relatively compact
subdomain. Two solutions of the `(b,a)` martingale problem in the domain `W` itself (on
arbitrary filtered probability spaces) with the same initial law have the same law of their
paths stopped at the exit from `W` (product σ-algebra on `ℝ≥0 → ℝ^d`). The covariance may
degenerate. (Solutions are not assumed to be constant after the exit: such a path would violate
the martingale-problem conditions on larger subdomains.) -/
def StoppedMartingaleProblemUniqueness (d m : ℕ) : Prop :=
  ∀ (b : (Fin d → ℝ) → Fin d → ℝ) (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ)
    (U W : Set (Fin d → ℝ)), IsOpen U → LocallyLipschitzOn U b → LocallyLipschitzOn U σ →
    IsInteriorDomain W U →
  ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (Q₁ : Measure Ω₁) [IsProbabilityMeasure Q₁]
    (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)) (Y₁ : ℝ≥0 → Ω₁ → Fin d → ℝ)
    (Ω₂ : Type) [MeasurableSpace Ω₂] (Q₂ : Measure Ω₂) [IsProbabilityMeasure Q₂]
    (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)) (Y₂ : ℝ≥0 → Ω₂ → Fin d → ℝ),
    IsMPSolutionOn Q₁ 𝓖₁ b (fun y => σ y * (σ y).transpose) W Y₁ →
    IsMPSolutionOn Q₂ 𝓖₂ b (fun y => σ y * (σ y).transpose) W Y₂ →
    Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0) →
    Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω)

/-- **Stopped-law uniqueness for a positive definite covariance** (coefficients smooth and
diffusion matrix strictly positive ⇒ the stopped law is unique): `b` locally Lipschitz and `a`
of class `C²` with `a(y)` positive definite on `U`; same conclusion as
`StoppedMartingaleProblemUniqueness` with `a` itself. -/
def StoppedMartingaleProblemUniquenessPosDef (d : ℕ) : Prop :=
  ∀ (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U W : Set (Fin d → ℝ)), IsOpen U → LocallyLipschitzOn U b → ContDiffOn ℝ 2 a U →
    (∀ y ∈ U, (a y).PosDef) → IsInteriorDomain W U →
  ∀ (Ω₁ : Type) [MeasurableSpace Ω₁] (Q₁ : Measure Ω₁) [IsProbabilityMeasure Q₁]
    (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)) (Y₁ : ℝ≥0 → Ω₁ → Fin d → ℝ)
    (Ω₂ : Type) [MeasurableSpace Ω₂] (Q₂ : Measure Ω₂) [IsProbabilityMeasure Q₂]
    (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)) (Y₂ : ℝ≥0 → Ω₂ → Fin d → ℝ),
    IsMPSolutionOn Q₁ 𝓖₁ b a W Y₁ → IsMPSolutionOn Q₂ 𝓖₂ b a W Y₂ →
    Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0) →
    Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω)

end BlockBand.SourceProcess.Stochastic
