module

public import BlockBand.Critical.RelativeVectors.StochasticStatements

/-!
# The Duhamel identity along the true flow

`RelativeDuhamelStatement` states the following.

* **Reference flow.** Any auxiliary probability space and maps `𝓜, Ξ`, jointly measurable for
  `𝓛 ⊗ Borel(Ω_aux)` (`𝓛 = pathSigma F a a c`, exactly as in `ReferenceFlowStatement`), that are a
  reference flow (`IsReferenceFlow`) of every path with simple spectrum on `[a, c]`.
* **Test.** A path-dependent function `h ω` of the array, jointly measurable for `𝓛 ⊗ Borel`,
  Euclidean bounded-`C²` with constant `C` and label-phase invariant for every `ω`.
* **Event.** A path event `B` on which, for `flowLaw`-a.e. `ω`, the spectrum is simple on
  `[a, c]` and every long gap (`|i - j| ≥ ℓ`) is at least `δ > 0`. (Almost surely: the
  path-measurable good-path sets give these conditions only for Hermitian `ω.1`, an a.s. event that
  is not path-measurable.) So the long couplings are a.s. bounded on `B`, and the short rotations
  cancel in `𝒜 - 𝓛_ref` (no inverse short gap appears).
* **Identity.** Under `flowLaw N a`, with `Z_σ = frameArray V H_σ` and
  `g^ω_s(z) = E_aux h_ω(𝓜^ω_{s,c} z + Ξ^ω_{s,c})`:
  `E[1_B (h(Z_c) - g_a(Z_a))] = E[1_B ∫_a^c (𝒜_σ - 𝓛_ref(σ)) g_σ(Z_σ) dσ]`.
  The gap stop is removed (time runs from `a`); `ω` are raw flow samples. No integrability is
  part of the conclusion (it is used only to bound the right side by the integral of a pointwise
  bound).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Set
open BlockBand.Internal.Contracts.CoareaPalm

/-- **The Duhamel identity along the true flow, conditional form.** See the module docstring. -/
def RelativeDuhamelStatement (N r : ℕ) : Prop :=
  ∀ (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ),
    F.IsHermitian → 0 < a → a < c → 0 < b₀ → 0 < ℓ →
  ∀ (Ωaux : Type) [MeasurableSpace Ωaux] (Paux : Measure Ωaux) [IsProbabilityMeasure Paux]
    (𝓜 : FlowSample N → ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ)
    (Ξ : FlowSample N → ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ),
    (∀ s u,
      Measurable[MeasurableSpace.comap Prod.fst (BlockBand.Palm.MomentFlow.pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => 𝓜 p.1 s u p.2) ∧
      Measurable[MeasurableSpace.comap Prod.fst (BlockBand.Palm.MomentFlow.pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Ωaux)]
        (fun p : FlowSample N × Ωaux => Ξ p.1 s u p.2)) →
    (∀ ω : FlowSample N, (∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) →
      IsReferenceFlow F a c b₀ ℓ ω Paux (𝓜 ω) (Ξ ω)) →
  ∀ (V : Matrix (Fin N) (Fin r) ℂ) (C : ℝ) (h : FlowSample N → (Fin N → Fin r → ℂ) → ℝ),
    Measurable[MeasurableSpace.comap Prod.fst (BlockBand.Palm.MomentFlow.pathSigma F a a c) ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace (Fin N → Fin r → ℂ))]
      (Function.uncurry h) →
    (∀ ω, IsArrayC2Bounded C (h ω) ∧ IsLabelPhaseInvariant (h ω)) →
  ∀ δ : ℝ, 0 < δ →
  ∀ B : Set (FlowSample N), MeasurableSet[BlockBand.Palm.MomentFlow.pathSigma F a a c] B →
    (∀ᵐ ω ∂flowLaw N a, ω ∈ B → ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) ∧
      ∀ i j : Fin N, ℓ ≤ labelDist i j →
        δ ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) →
    let g : FlowSample N → ℝ → (Fin N → Fin r → ℂ) → ℝ :=
      fun ω s z => ∫ ω', h ω (arrayMul (𝓜 ω s c ω') z + Ξ ω s c ω') ∂Paux
    ∫ ω in B, (h ω (frameArray V (flowMatrix F a ω c)) -
        g ω a (frameArray V (flowMatrix F a ω a))) ∂flowLaw N a =
      ∫ ω in B, (∫ s in Ioc a c,
        (complexAngularGenerator N r (flowEigenvalue F a ω s) (g ω s)
            (frameArray V (flowMatrix F a ω s)) -
          referenceArrayGenerator F a b₀ ω ℓ s (g ω s) (frameArray V (flowMatrix F a ω s))))
        ∂flowLaw N a

end BlockBand.Critical.RelativeVectors
