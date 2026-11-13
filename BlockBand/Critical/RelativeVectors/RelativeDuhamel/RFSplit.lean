module

public import BlockBand.Critical.RelativeVectors.StochasticStatements
public import BlockBand.Palm.ReferenceFlowSpec

/-!
# Four statements about an abstract reference flow

Definitions only. For an abstract reference flow `(K, L)` on a probability space `(Ωd, P)`, with
an independent standard circular array `G`, and its backward function `refBackward`:
`RFCovarianceStatement`, `RFBackwardRegularStatement`, `RFGeneratorContinuousStatement` and
`RFGeneratorEqStatement`, used to prove `ReferenceFlowStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm

variable {N r : ℕ}

/-- Backward function of an abstract reference flow: `g_s(z) = E_y E_G f(K_s z + L_s G)`, where
`G` is a standard circular `N × r` array independent of `y ∼ P`. -/
def refBackward {Ωd : Type} [MeasurableSpace Ωd] (P : Measure Ωd)
    (K L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ) (f : (Fin N → Fin r → ℂ) → ℝ) (s : ℝ)
    (z : Fin N → Fin r → ℂ) : ℝ :=
  ∫ y, ∫ G, f (arrayMul (K s y) z + arrayMul (L s y) G) ∂BlockBand.Palm.ReferenceFlow.matCircularLaw N r ∂P

/-- **The reference covariance identity in characteristic-functional form.** If
`L L^* = I − M M^*` a.s., then under `P ⊗ matCircularLaw` the array `Ξ = L G` is circular Gaussian
given `M`, with `E ΞΞ^* = (I − MM^*) ⊗ I_r`. This is the exact form of the `covariance` field of
`IsReferenceFlow`, with `Ωaux = Ωd × (Fin N → Fin r → ℂ)` and `Ξ(y, G) = L(y) G`. -/
def RFCovarianceStatement (N r : ℕ) : Prop :=
  ∀ (Ωd : Type) [MeasurableSpace Ωd] (P : Measure Ωd) [IsProbabilityMeasure P]
    (M L : Ωd → Matrix (Fin N) (Fin N) ℂ), Measurable M → Measurable L →
    (∀ᵐ y ∂P, L y * (L y)ᴴ = 1 - M y * (M y)ᴴ) →
    ∀ h : Matrix (Fin N) (Fin N) ℂ → ℝ, Measurable h → (∃ C, ∀ M, |h M| ≤ C) →
    ∀ w : Fin N → Fin r → ℂ,
      ∫ p : Ωd × (Fin N → Fin r → ℂ), (h (M p.1) : ℂ) * Complex.exp (Complex.I *
          (∑ i, ∑ q, (star (w i q) * arrayMul (L p.1) p.2 i q).re : ℝ))
          ∂(P.prod (BlockBand.Palm.ReferenceFlow.matCircularLaw N r)) =
        ∫ p : Ωd × (Fin N → Fin r → ℂ), (h (M p.1) * Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
          (star (fun i => w i q) ⬝ᵥ ((1 - M p.1 * (M p.1)ᴴ) *ᵥ fun i => w i q)).re) : ℂ)
          ∂(P.prod (BlockBand.Palm.ReferenceFlow.matCircularLaw N r))

/-- **Regularity of the backward function.** For a family `K, L` that is measurable in `y`, a.s.
continuous in `s` on `[a, c]`, with `K_s` an a.s. `ℓ²`-contraction, and for every Euclidean
bounded-`C²` test `f` with constant `C`:
* `g_s` has the same constant `C` for every `s ∈ [a, c]`;
* `g`, `D_z g` and `D_z² g` are jointly continuous on `[a, c] × ℂ^{N×r}`.

These are the first four conjuncts of the `backward` field of `IsReferenceFlow`. -/
def RFBackwardRegularStatement (N r : ℕ) : Prop :=
  ∀ (Ωd : Type) [MeasurableSpace Ωd] (P : Measure Ωd) [IsProbabilityMeasure P]
    (K L : ℝ → Ωd → Matrix (Fin N) (Fin N) ℂ) (a c : ℝ), a ≤ c →
    (∀ s, Measurable (K s)) → (∀ s, Measurable (L s)) →
    (∀ᵐ y ∂P, ContinuousOn (fun s => K s y) (Icc a c) ∧ ContinuousOn (fun s => L s y) (Icc a c)) →
    (∀ᵐ y ∂P, ∀ s ∈ Icc a c, ∀ v : Fin N → ℂ, l2Norm (K s y *ᵥ v) ≤ l2Norm v) →
    ∀ (C : ℝ) (f : (Fin N → Fin r → ℂ) → ℝ), IsArrayC2Bounded C f →
      (∀ s ∈ Icc a c, IsArrayC2Bounded C (refBackward P K L f s)) ∧
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => refBackward P K L f p.1 p.2)
        (Icc a c ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (refBackward P K L f p.1) p.2)
        (Icc a c ×ˢ univ) ∧
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
          fderiv ℝ (fderiv ℝ (refBackward P K L f p.1)) p.2) (Icc a c ×ˢ univ)

/-- **Continuity of the generator applied to a regular family.** If the rates `ρ` and the damping
`κ` are continuous on `[a, c]`, and `g`, `D_z g`, `D_z² g` are jointly continuous on
`[a, c] × ℂ^{N×r}`, then `(s, z) ↦ refGenerator ρ κ s (g s) z` is continuous there. This gives the
fifth conjunct of `backward` (on `Ioo a c ⊆ Icc a c`). -/
def RFGeneratorContinuousStatement (N r : ℕ) : Prop :=
  ∀ (ρ : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (a c : ℝ),
    ContinuousOn ρ (Icc a c) → ContinuousOn κ (Icc a c) →
    ∀ g : ℝ → (Fin N → Fin r → ℂ) → ℝ,
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (g p.1) p.2) (Icc a c ×ˢ univ) →
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) => fderiv ℝ (fderiv ℝ (g p.1)) p.2)
        (Icc a c ×ˢ univ) →
      ContinuousOn (fun p : ℝ × (Fin N → Fin r → ℂ) =>
          BlockBand.Palm.ReferenceFlow.refGenerator ρ κ p.1 (g p.1) p.2) (Icc a c ×ˢ univ)

/-- **The two forms of the reference generator agree.** `referenceArrayGenerator` is
`refGenerator` with the coefficients `shortRate` and `refDamping`, for every function and point;
no smoothness is needed.

The vector field `rotX` of `AngularFields` is the negative of the matrix `rotX` acting by
`arrayMul`. Squares of vector fields are unchanged by `X ↦ −X`. -/
def RFGeneratorEqStatement (N r : ℕ) : Prop :=
  ∀ (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ)
    (h : (Fin N → Fin r → ℂ) → ℝ) (z : Fin N → Fin r → ℂ),
    referenceArrayGenerator F a b₀ ω ℓ σ h z =
      BlockBand.Palm.ReferenceFlow.refGenerator
        (BlockBand.Palm.RelativeLocalization.StochasticBridge.shortRate F a ω ℓ)
        (BlockBand.Palm.RelativeLocalization.StochasticBridge.refDamping F a b₀ ω ℓ) σ h z

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF
