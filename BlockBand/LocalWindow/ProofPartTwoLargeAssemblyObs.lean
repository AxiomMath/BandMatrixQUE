module

public import BlockBand.LocalWindow.ProofPartTwoLargeEventsObs
public import BlockBand.LocalWindow.ProofPartTwoSmallGrid

/-!
# The compressed observable family of the large-`ρ` branch

Measurable families of compressed grid observables approximating the compression of a part (ii)
observable, for the large-`ρ` branch of the physical local-window lemma.

## Main results

* **`exists_largeGridJ`**: for a part (ii) observable `B` of order `k = 1`, a family of compressed
  grid observables `J_c j₀ e` on `Fin (2W - 1)`, measurable in the exterior point (class (b)
  through `measurable_spectralFn`), Hermitian contractions on the label events, with
  `‖B‖ ≤ 1` and `‖J_c j₀ e ω - U*B(ω, E)U‖ ≤ √(2W - 1) K_q (‖C‖²/ε² + 1)|E - e| +
  √(2W)(3K_qK'² + 4K')/|ρ(E)|` (`K_q = max K₀ 0`; class (a): the left side is `0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

/-- **The compressed grid observables of the large-`ρ` branch**: class (a) `J_c = U*B₀U`
(exact), class (b) `J_c = f(compRegM e)` (`largeObsB_close`). -/
theorem exists_largeGridJ (sel : CEH.EigenpairSelection (2 * p.W)) {K₀ ε : ℝ} (hε : 0 < ε)
    {B : SplitState p i → ℝ → PairMatrix p i}
    (hB : BlockBand.LocalWindow.IsWindowObservable p i 1 K₀ B) :
    ∃ Jc : ExteriorSite p i → ℝ → SplitState p i →
        Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ,
      (∀ j₀ e, Measurable (Jc j₀ e)) ∧
      (∀ j₀ e om, om ∈ poleLabelSet ε j₀ e → (Jc j₀ e om).IsHermitian ∧ ‖Jc j₀ e om‖ ≤ 1) ∧
      (∀ om E, ‖B om E‖ ≤ 1) ∧
      ∀ (om : SplitState p i) (hH : om.1.IsHermitian), om.2.2.IsHermitian →
        ∀ j₀ : ExteriorSite p i, PoleSimple hH j₀ → ∀ E e : ℝ, PoleSeparated ε hH j₀ E →
        PoleSeparated ε hH j₀ e → (om.1 - (E : ℂ) • 1).det ≠ 0 → ∀ K' : ℝ, 0 < K' →
        ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1‖ ≤ K' →
        6 * K' ≤ |poleRho hH j₀ om.2.1 E| →
        ‖Jc j₀ e om - (poleIsometry sel j₀ om)ᴴ * B om E * poleIsometry sel j₀ om‖ ≤
          Real.sqrt ((2 * p.W - 1 : ℕ) : ℝ) * max K₀ 0 * ((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) +
            Real.sqrt (2 * (p.W : ℝ)) *
              ((3 * max K₀ 0 * K' ^ 2 + 4 * K') / |poleRho hH j₀ om.2.1 E|) := by
  rcases hB with ⟨B₀, hB₀m, hB₀, hBE⟩ | ⟨f, hf, hBE⟩
  · refine ⟨largeObsA sel B₀, fun j₀ e => measurable_largeObsA sel hB₀m j₀ e,
      fun j₀ e om hl => largeObsA_spec sel hB₀ hl, fun om E => by rw [hBE]; exact (hB₀ om).2,
      fun om hH _ j₀ _ E e _ _ _ K' hK' _ _ => ?_⟩
    have h : largeObsA sel B₀ j₀ e om -
        (poleIsometry sel j₀ om)ᴴ * B om E * poleIsometry sel j₀ om = 0 := by
      rw [hBE]; unfold largeObsA; exact sub_self _
    rw [h, norm_zero]
    have hK0 : 0 ≤ max K₀ 0 := le_max_right _ _
    have h1 : 0 ≤ Real.sqrt ((2 * p.W - 1 : ℕ) : ℝ) * max K₀ 0 *
        ((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e|) := by positivity
    have h2 : 0 ≤ (3 * max K₀ 0 * K' ^ 2 + 4 * K') / |poleRho hH j₀ om.2.1 E| :=
      div_nonneg (by have := hK'.le; positivity) (abs_nonneg _)
    have h3 := mul_nonneg (Real.sqrt_nonneg (2 * (p.W : ℝ))) h2
    linarith
  · have hf' : BlockBand.LocalWindow.IsSpectralTest 1 (max K₀ 0) f :=
      ⟨hf.1, hf.2.1, fun j hj x => (hf.2.2.1 j hj x).trans (le_max_left _ _), hf.2.2.2⟩
    refine ⟨largeObsB sel ε f,
      fun j₀ e => measurable_largeObsB sel hε (measurable_spectralFn hf.1.continuous) j₀ e,
      fun j₀ e om _ => largeObsB_spec sel ε hf.2.1 j₀ e om,
      fun om E => by rw [hBE]; exact opNorm_spectralFn_le hf.2.1 _,
      fun om hH hV j₀ hs E e hsepE hsepe hdet K' hK' hM' hρ' => ?_⟩
    rw [hBE]
    exact largeObsB_close sel hε hH hV hs hsepE hsepe hdet hf' le_rfl hK' hM' hρ'

end BlockBand.LocalWindow.ProofPartTwo
