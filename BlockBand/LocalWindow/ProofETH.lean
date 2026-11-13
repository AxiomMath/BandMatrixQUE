module

public import BlockBand.LocalWindow.Statements

/-!
# The two parts of the physical local window and their assembly

`PhysicalLocalWindowStatement` bundles (i) and (ii) with one exceptional event. This file
states each part with exactly its own clauses (same quantifier order, same measures, same
observable class, same centre `windowCenter`), and proves that the two parts give the bundled
statement (`physicalLocalWindow_of_parts`: the union of the two events, whose outer measure
is at most the sum, under both laws).

## Main results

* `PhysicalLocalWindowPartOneClauses`: clauses (i) only (no observable; the constants `c, C₁`
  precede `γ`; for each `γ, D` a constant `C`).
* `PhysicalLocalWindowPartTwoStatement`: clauses (ii) only (`δ` and the derivative order `k`
  first, then `ε, D, K₀`, then `C`; uniformly in `4 ≤ n ≤ TW`, models, pairs, splitting laws
  and observables of `IsWindowObservable`).
* `physicalLocalWindow_of_parts`: (i) ∧ (ii) → `PhysicalLocalWindowStatement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal

/-- **Part (i) of the physical local window** alone (the local count):
the clauses of part (i) of `PhysicalLocalWindowStatement`, with the same quantifier order
(the observable, `ε` and `K₀` play no role in (i) and are dropped). -/
def PhysicalLocalWindowPartOneClauses : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (c C₁ : ℝ), 0 < c ∧ 0 < C₁ ∧
      ∀ γ : ℝ, 0 < γ → γ < 1 / 2 → ∀ D : ℝ, 0 < D →
        ∃ C : ℝ, ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
          ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
            IsPairSplitting p i model (splitS p) Pω →
              ∃ Ω : Set (SplitState p i × PairMatrix p i),
                splitLaw p i Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D)) ∧
                (∀ α : Fin p.N, splitPairLaw p i α Pω Ω ≤ ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
                ∀ x ∉ Ω, ∀ α : Fin p.N, IsBulkRank p ϑ α →
                  let E := physicalOrderedEigenvalue p (assemble p i x.1 x.2) α
                  let A := schurA p i x.1 x.2 E
                  let η := (p.W : ℝ) ^ (-1 + γ)
                  c * (p.W : ℝ) * η ≤ spectralSum A (fun l => if |l| ≤ C₁ * η then 1 else 0) ∧
                    spectralSum A (fun l => η ^ 2 / (l ^ 2 + η ^ 2)) ≤ C₁ * (p.W : ℝ) * η

/-- **Part (ii) of the physical local window** alone (eigenvector thermalization in the
window): the clauses of part (ii) of `PhysicalLocalWindowStatement`. `b, T, ϑ`
first; then the fixed `0 < δ < 1` and the derivative order `k` of
the spectral class; then `ε > 0`, `D > 0` and the class bound `K₀`; then `C`; uniformly in
`4 ≤ n ≤ TW`, models, adjacent pairs, splitting laws and observables `B` of
`IsWindowObservable`: an event `Ω` of original and of every pair-law probability at most
`C W^{-D}` outside which, at every `ϑ`-bulk selected energy `E = λ_α`, for `|λ| ≤ δ` and every
unit `u` with `A(E) u = λ u`, `|u*B u - j_B(E, λ)| ≤ C W^{-1/2+ε}`. -/
def PhysicalLocalWindowPartTwoStatement : Prop :=
  ∀ b T ϑ : ℝ, 0 < ϑ →
    ∃ (δ : ℝ) (k : ℕ), 0 < δ ∧ δ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ∀ D : ℝ, 0 < D → ∀ K₀ : ℝ,
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
                  ∀ lam : ℝ, |lam| ≤ δ → ∀ u : PairSite p i → ℂ, l2Norm u = 1 →
                    A *ᵥ u = (lam : ℂ) • u →
                    |(star u ⬝ᵥ (B x.1 E *ᵥ u)).re -
                        windowCenter p i (B x.1 E) (schurK0 p i x.1 E) (splitS p) lam| ≤
                      C * (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε)

/-- `μ(Ω₁ ∪ Ω₂) ≤ ofReal (C₁ a) + ofReal (C₂ a) ≤ ofReal ((max C₁ 0 + max C₂ 0) a)` for every
measure and arbitrary sets (outer-measure subadditivity). -/
theorem measure_union_le_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {Ω₁ Ω₂ : Set α} {C₁ C₂ a : ℝ} (ha : 0 ≤ a) (h₁ : μ Ω₁ ≤ ENNReal.ofReal (C₁ * a))
    (h₂ : μ Ω₂ ≤ ENNReal.ofReal (C₂ * a)) :
    μ (Ω₁ ∪ Ω₂) ≤ ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * a) := by
  refine (measure_union_le Ω₁ Ω₂).trans ?_
  have e1 : ENNReal.ofReal (C₁ * a) ≤ ENNReal.ofReal (max C₁ 0 * a) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
  have e2 : ENNReal.ofReal (C₂ * a) ≤ ENNReal.ofReal (max C₂ 0 * a) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
  calc μ Ω₁ + μ Ω₂ ≤ ENNReal.ofReal (max C₁ 0 * a) + ENNReal.ofReal (max C₂ 0 * a) :=
        add_le_add (h₁.trans e1) (h₂.trans e2)
    _ = ENNReal.ofReal ((max C₁ 0 + max C₂ 0) * a) := by
        rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) ha)
          (mul_nonneg (le_max_right _ _) ha), add_mul]

/-- **Assembly of the physical local window**: parts (i) and (ii), each
with its own exceptional event, give `PhysicalLocalWindowStatement` with the union of the two
events (constant `max C₁ 0 + max C₂ 0` for both laws; part (ii)'s bound is raised to that
constant since `W^{-1/2+ε} ≥ 0`). -/
theorem physicalLocalWindow_of_parts (h1 : PhysicalLocalWindowPartOneClauses)
    (h2 : PhysicalLocalWindowPartTwoStatement) : PhysicalLocalWindowStatement := by
  intro b T ϑ hϑ
  obtain ⟨c, C₁, hc, hC₁, hone⟩ := h1 b T ϑ hϑ
  obtain ⟨δ, k, hδ, hδ1, htwo⟩ := h2 b T ϑ hϑ
  refine ⟨δ, c, C₁, k, hδ, hδ1, hc, hC₁, fun γ hγ hγ1 ε hε D hD K₀ => ?_⟩
  obtain ⟨Ca, ha⟩ := hone γ hγ hγ1 D hD
  obtain ⟨Cb, hb⟩ := htwo ε hε D hD K₀
  refine ⟨max Ca 0 + max Cb 0, fun p hpb hn model i Pω hPω B hB => ?_⟩
  obtain ⟨Ω₁, hΩ₁, hΩ₁', hgood₁⟩ := ha p hpb hn model i Pω hPω
  obtain ⟨Ω₂, hΩ₂, hΩ₂', hgood₂⟩ := hb p hpb hn model i Pω hPω B hB
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hWD : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  refine ⟨Ω₁ ∪ Ω₂, measure_union_le_ofReal _ hWD hΩ₁ hΩ₂,
    fun α => measure_union_le_ofReal _ hWD (hΩ₁' α) (hΩ₂' α), fun x hx α hα => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  refine ⟨hgood₁ x hx.1 α hα, fun lam hlam u hu hAu => ?_⟩
  refine (hgood₂ x hx.2 α hα lam hlam u hu hAu).trans ?_
  have hWe : 0 ≤ (p.W : ℝ) ^ (-(1 / 2 : ℝ) + ε) := Real.rpow_nonneg hW.le _
  exact mul_le_mul_of_nonneg_right
    ((le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))) hWe

end BlockBand.LocalWindow
