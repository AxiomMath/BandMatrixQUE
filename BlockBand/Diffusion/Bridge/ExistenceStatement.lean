module

public import BlockBand.Diffusion.Base.TransitionLawDefs

/-!
# The bridge existence statement for the base diffusion

Local copies of the endpoint-side definitions `bridgeFddDensity`, `IsBaseBridge` and
`LbkBridgeExistence`, specialized to the base kernel `exKernel D0`:
* `brBridgeFddDensity p z e t ts zs`: the finite-dimensional density
  `∏ p_{tᵢ - tᵢ₋₁}(zᵢ₋₁, zᵢ) p_{t - t_k}(z_k, e) / p_t(z, e)` of a bridge from `z` to `e`;
* `IsBrBaseBridge P p z t Z`: `Z` is a process with continuous paths on `[0, t]` from `z` to
  `(0, 0)` whose finite-dimensional laws have this density;
* `BrLbkBridgeExistence D0`: for every dual start `(x, y)` and every `t > 0` such a bridge exists.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- **Boundary starts**: a copy of `IsDualStart`. -/
def BrIsDualStart {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  StrictMono x ∧ StrictMono y ∧ (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
    ∀ i j, 0 < x i + y j

/-- **The finite-dimensional bridge density**: a copy of `bridgeFddDensity`. -/
def brBridgeFddDensity {α : Type*} (p : ℝ → α → α → ℝ) (z e : α) (t : ℝ) {k : ℕ}
    (ts : Fin k → ℝ) (zs : Fin k → α) : ℝ≥0∞ :=
  (∏ i : Fin k, ENNReal.ofReal
      (p (ts i - (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc)
        ((Fin.cons z zs : Fin (k + 1) → α) i.castSucc) (zs i))) *
    ENNReal.ofReal (p (t - (Fin.cons 0 ts : Fin (k + 1) → ℝ) (Fin.last k))
      ((Fin.cons z zs : Fin (k + 1) → α) (Fin.last k)) e) /
    ENNReal.ofReal (p t z e)

/-- **The base bridge from `z` to the corner `(0,0)` of length `t`**: a copy of `IsBaseBridge`
with `brBridgeFddDensity`. -/
structure IsBrBaseBridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ) (z : ℝ × ℝ) (t : ℝ) (Z : ℝ → Ω → ℝ × ℝ) : Prop where
  prob : IsProbabilityMeasure P
  meas : ∀ s, Measurable (Z s)
  paths : ∀ᵐ ω ∂P, ContinuousOn (fun s => Z s ω) (Icc 0 t) ∧ Z 0 ω = z ∧ Z t ω = (0, 0)
  fdd : ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i ∧ ts i < t) →
    ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ ω, F (fun i => Z (ts i) ω) ∂P = ∫⁻ zs, F zs * brBridgeFddDensity p z (0, 0) t ts zs

/-- **Existence of the continuous base bridge**: a copy of `LbkBridgeExistence` with
`BrIsDualStart`, `IsBrBaseBridge` and `exKernel`. -/
def BrLbkBridgeExistence (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, BrIsDualStart ![x] ![y] → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ℝ → Ω → ℝ × ℝ),
      IsBrBaseBridge P (exKernel D0) (x, y) t Z

end BlockBand.Diffusion
