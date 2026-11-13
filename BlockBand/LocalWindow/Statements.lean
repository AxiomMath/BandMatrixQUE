module

public import BlockBand.Internal.Contracts.Layers

/-!
# Statement of the physical local window

Local estimates at the selected energy: a local eigenvalue count (part (i)) and eigenvector
thermalization in a spectral window (part (ii)) for the Schur complement of the reassembled matrix
on an adjacent pair of blocks.

## Setting and representation choices

* **Splitting.** `S = {i, i+1}`, `d = 2W`, `s = min(b, 1-2b) = Layers.splitS p`, `t = s/d`
  (`pairTime p s`). The probability space is the split space `(ω, G)`, `ω = (H_R, C, V)`,
  with law `Pω ⊗ GUE_d(t)` for any pair splitting law `Pω` (`CoareaPalm.IsPairSplitting`);
  `H = assemble ω G` has the exact physical law. The statement is required for every such `Pω`
  (`splitLaw`). The original probability is `splitLaw`; the pair law is its
  `n/2 (p_{αi}+p_{α,i+1})` tilt `splitPairLaw` (the split-space form of the pair law,
  `CoareaContract.pairLaw_formula`).
* **Selected bulk energies.** "At every selected bulk energy" is read as: simultaneously for
  every `ϑ`-bulk rank `α` (`IsBulkRank p ϑ α`, zero-based), at `E = λ_α(H)` (the ordered
  eigenvalue of the reassembled matrix). The fixed-rank form is a special case. A fixed compact
  bulk interval containing the classical locations of the `ϑ`-bulk ranks is internal to the proof
  (rank location bounds the exit), so it does not appear; constants depend on `b, T, ϑ`.
* **Observables (part (ii)).** Part (ii) is stated for two classes (`IsWindowObservable`):
  (a) every measurable `ω ↦ B(ω)` with Hermitian contraction values (including the deterministic
  `B = P_i - P_{i+1}`); (b) `B = f(F(E) - E)` for bounded smooth `f` (`IsSpectralTest k K₀ f`:
  `C^∞`, `|f| ≤ 1`, the first `k` derivatives bounded by `K₀`, finite limits at `±∞`, which makes
  the limiting compression at an infinite rank-one parameter defined). The derivative order `k` is
  a fixed regularity constant chosen by the lemma; the constants are uniform over the class for
  each `K₀`. This covers `K₀χ(K₀/L₀)/L₀ = g(K₀/L₀)`, `L₀ = W^{1/4}` (dilations do not increase
  derivative bounds). At a nonpole energy `F(E)` is finite, so the observable is
  `f(F(E) - E)` and the centre is `j_B(E, λ)`.
* **The exceptional event** may depend on the observable (the ETH bound cannot hold for all
  contractions simultaneously); it is a set of the split space, whose measure is the outer
  measure. "Outside an event of original probability at most `C_D W^{-D}`" and "the same under
  the pair law, after increasing the failure exponent by one" are stated as one event with both
  bounds; since `dP♯ ≤ (n/2) dP ≤ (TW/2) dP`, this is equivalent.
* **Quantifiers.** `b, T, ϑ` first; then the fixed regularity constants: `0 < δ < 1` (below the
  certificate radius), `c, C₁` of part (i), and `k`; then `0 < γ < γ₀ = 1/2`, `ε > 0`, `D > 0` and
  the class bound `K₀`; then `C`; uniformly in `4 ≤ n ≤ TW` (both parities), every model,
  adjacent pair, splitting law and observable. The size parameters are the binder
  `∀ p : Parameters, p.b = b → n ≤ TW` (equivalent to `∀ n ≥ 4, W ≥ 1` at fixed `b`; a
  `let`-bound `p := ⟨n, W, b, …⟩` would hide the `NeZero p.n` instance of the site type). Part
  (ii)'s `C W^{-1/2+ε}` uses the same `C` (any `γ, ε, D`-dependent constant can be absorbed,
  since `C W^{-D} ≥ 1` for small `W`). Counting is with multiplicity (`Inputs.spectralSum`,
  eigenvalues of the Hermitian `A(E)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal ContDiff Matrix.Norms.L2Operator

section Vocabulary

variable (p : Parameters) (i : ZMod p.n)

/-- `K₀(E) = F(E) - E`, `F(E) = V - C*(H_R - E)⁻¹C` (the Schur data). -/
def schurK0 (om : SplitState p i) (E : ℝ) : PairMatrix p i :=
  physicalCoareaF om.1 om.2.1 om.2.2 E - (E : ℂ) • 1

/-- The Schur complement `A(E) = F(E) + G - E` of `H - E` on the pair. -/
def schurA (om : SplitState p i) (G : PairMatrix p i) (E : ℝ) : PairMatrix p i :=
  schurK0 p i om E + G

/-- `m_E(z)`: the `freshDyson` of a pair deformation `K`, after reindexing the pair by
`Fin (card S)`; for `K = K₀(E)` and real `z = λ` this is `m_E(λ)` of.
-/
def pairDyson (K : PairMatrix p i) (s : ℝ) (z : ℂ) : ℂ :=
  freshDyson (Matrix.reindex (Fintype.equivFin (PairSite p i))
    (Fintype.equivFin (PairSite p i)) K) s z

/-- `Γ_E(λ) = s |K₀ - λ - s m_E(λ)|⁻²` (with `|X|⁻² = (X*X)⁻¹`). -/
def windowGamma (K : PairMatrix p i) (s lam : ℝ) : PairMatrix p i :=
  let X := K - ((lam : ℂ) + (s : ℂ) * pairDyson p i K s lam) • (1 : PairMatrix p i)
  (s : ℂ) • (Xᴴ * X)⁻¹

/-- `j_B(E,λ) = d⁻¹ Tr B Γ_E(λ)`, `d = 2W` (real part). -/
def windowCenter (B K : PairMatrix p i) (s lam : ℝ) : ℝ :=
  (2 * (p.W : ℝ))⁻¹ * (B * windowGamma p i K s lam).trace.re

/-- Original split law `Pω ⊗ GUE_d(t)`, `t = s/d`, `s = min(c, b)`. -/
def splitLaw (Pω : Measure (SplitState p i)) : Measure (SplitState p i × PairMatrix p i) :=
  Pω.prod (gueMeasure (PairSite p i) (pairTime p (splitS p)))

/-- The pair law on the split space: density `(n/2)(p_{αi} + p_{α,i+1})` of the
reassembled matrix with respect to `splitLaw`. -/
def splitPairLaw (α : Fin p.N) (Pω : Measure (SplitState p i)) :
    Measure (SplitState p i × PairMatrix p i) :=
  (splitLaw p i Pω).withDensity fun x =>
    ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2))

end Vocabulary

/-- Spectral function `f(X)` of a Hermitian matrix (Mathlib's `IsHermitian.cfc`); zero off the
Hermitian set. -/
def spectralFn {ι : Type} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  if h : X.IsHermitian then h.cfc f else 0

/-- Bounded smooth spectral test: `C^∞`, `|f| ≤ 1`, derivatives of order `≤ k` bounded by `K₀`,
finite limits at `±∞` (so the compression limit at an infinite rank-one parameter exists). -/
def IsSpectralTest (k : ℕ) (K₀ : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ (∀ x, |f x| ≤ 1) ∧ (∀ j ≤ k, ∀ x, |iteratedDeriv j f x| ≤ K₀) ∧
    ∃ a b : ℝ, Tendsto f atTop (𝓝 a) ∧ Tendsto f atBot (𝓝 b)

/-- The observables of part (ii), as functions of the exterior data `ω` and the energy `E`:
(a) an exterior-measurable Hermitian contraction not depending on `E` (e.g. `P_i - P_{i+1}`), or
(b) a bounded smooth spectral function of `F(E) - E`. -/
def IsWindowObservable (p : Parameters) (i : ZMod p.n) (k : ℕ) (K₀ : ℝ)
    (B : SplitState p i → ℝ → PairMatrix p i) : Prop :=
  (∃ B₀ : SplitState p i → PairMatrix p i, Measurable B₀ ∧
      (∀ om, (B₀ om).IsHermitian ∧ ‖B₀ om‖ ≤ 1) ∧ ∀ om E, B om E = B₀ om) ∨
    ∃ f : ℝ → ℝ, IsSpectralTest k K₀ f ∧ ∀ om E, B om E = spectralFn f (schurK0 p i om E)

/-- **The physical local window.** `b, T, ϑ` first; then fixed `0 < δ < 1`, `c, C₁ > 0` and a
derivative order `k`; then for every `0 < γ < γ₀ = 1/2`, `ε > 0`, `D > 0` and spectral-class
bound `K₀` a constant `C`; uniformly in `4 ≤ n ≤ TW`, models, adjacent pairs `S = {i,i+1}`,
splitting laws and observables `B` of `IsWindowObservable`, there is an event `Ω` of original
probability and of every pair-law probability at most `C W^{-D}` outside which, simultaneously
for every `ϑ`-bulk rank `α`, at `E = λ_α`, with `A = F(E) + G - E` and `η = W^{-1+γ}`:
* (i) `N_A([-C₁η, C₁η]) ≥ c W η` and `Σ_{λ ∈ Spec A} η²/(λ² + η²) ≤ C₁ W η`;
* (ii) for `|λ| ≤ δ` and every unit `u` with `A u = λ u`, `|u*B u - j_B(E,λ)| ≤ C W^{-1/2+ε}`. -/
def PhysicalLocalWindowStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (δ c C₁ : ℝ) (k : ℕ), 0 < δ ∧ δ < 1 ∧ 0 < c ∧ 0 < C₁ ∧
      ∀ γ : ℝ, 0 < γ → γ < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∀ K₀ : ℝ,
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
            ∀ B : SplitState p i → ℝ → PairMatrix p i, IsWindowObservable p i k K₀ B →
              ∃ Ω : Set (SplitState p i × PairMatrix p i),
                splitLaw p i Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ∧
                (∀ α : Fin p.N, splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x ∉ Ω, ∀ α : Fin p.N, IsBulkRank p ϑ α →
                  let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
                  let A := schurA p i x.1 x.2 E
                  let η := (p.W : ℝ) ^ (-1 + γ)
                  (c * (p.W : ℝ) * η ≤ spectralSum A (fun l => if |l| ≤ C₁ * η then 1 else 0) ∧
                    spectralSum A (fun l => η ^ 2 / (l ^ 2 + η ^ 2)) ≤ C₁ * (p.W : ℝ) * η) ∧
                  ∀ lam : ℝ, |lam| ≤ δ → ∀ u : PairSite p i → ℂ, l2Norm u = 1 →
                    A *ᵥ u = (lam : ℂ) • u →
                    |(star u ⬝ᵥ (B x.1 E *ᵥ u)).re -
                        windowCenter p i (B x.1 E) (schurK0 p i x.1 E) (splitS p) lam| ≤
                      C * (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε)

end BlockBand.LocalWindow
