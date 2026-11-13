module

public import BlockBand.LocalWindow.Statements
public import BlockBand.LocalWindow.ProofPoisson
public import BlockBand.LocalWindow.ProofTruncationBounds
public import BlockBand.LocalWindow.ProofPairLaw

/-!
# Deterministic core of the physical local window

Deterministic counting estimates behind part (i) of the physical local-window lemma: a count of
eigenvalues in a window from Poisson sums at two heights, and the transfer of the upper Poisson
bound, for a Hermitian matrix that is a finite-rank, small-norm perturbation of another.

## Main results

* `partOne_core`: the two-height count and the Poisson bound transfer under a perturbation of rank
  `k` and size `r`.
* `isPerturbation_actual`: the exact Schur complement is a perturbation of rank `≤ 1` of a grid
  truncation when at most one exterior eigenvalue lies within `ε` of the energy.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow

open Matrix BlockBand.LocalWindow.ProofCount BlockBand.Coarea

/-- **Deterministic core of part (i) of the physical local window.** Let `Â` (the
truncated Schur complement at a grid energy) and `A` (the exact one) be Hermitian, `A` a
perturbation of `Â` of rank `k` and size `r ≥ 0`, and `η, L > 0`. Then
* `N_A([-(Lη + r), Lη + r]) ≥ Σ_Â P_η - (2/L²) Σ_Â P_{Lη} - 2k` (count from two heights,
  Weyl, rank-`k` interlacing);
* `Σ_A P_η ≤ Σ_Â P_η + |ι| r/η + 2k` (upper Poisson bound transfer). -/
theorem partOne_core {ι : Type} [Fintype ι] [DecidableEq ι] {A Ahat : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian) {k : ℕ} {r : ℝ} (hr : 0 <= r)
    (hpert : IsPerturbation Ahat A k r) {η L : ℝ} (hη : 0 < η) (hL : 0 < L) :
    BlockBand.Internal.Contracts.Inputs.spectralSum Ahat (poissonWeight η) -
          2 / L ^ 2 * BlockBand.Internal.Contracts.Inputs.spectralSum Ahat
            (poissonWeight (L * η)) - 2 * k ≤
        BlockBand.Internal.Contracts.Inputs.spectralSum A
          (fun l => if |l| ≤ L * η + r then 1 else 0) ∧
      BlockBand.Internal.Contracts.Inputs.spectralSum A (poissonWeight η) ≤
        BlockBand.Internal.Contracts.Inputs.spectralSum Ahat (poissonWeight η) +
          Fintype.card ι * (r / η) + 2 * k := by
  constructor
  · have h1 := spectralSum_poisson_le_count_add hAhat hη hL
    have h2 := window_count_le hAhat hA hpert (L * η)
    linarith
  · exact spectralSum_poisson_le hA hAhat hr hpert.symm hη

/-- The deterministic core at the exact Schur complement: at a nonpole energy `E` with at
most one exterior eigenvalue within `ε` of `E`, `F(E) + G - E` is a perturbation of rank
`≤ 1` and size `0` of the truncated `F̂(E) + G - E`; composing with a norm perturbation of
size `r` (grid move) gives rank `≤ 1`, size `r`. -/
theorem isPerturbation_actual {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)
    (V G : Matrix β β ℂ) {ε E : ℝ} (hdet : (H_R - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0)
    (hnear : (nearSet ε hH E).card ≤ 1) {Ahat : Matrix β β ℂ} {r : ℝ}
    (hgrid : IsPerturbation Ahat (truncF ε H_R C V E + G - (E : ℂ) • 1) 0 r) :
    IsPerturbation Ahat (physicalCoareaF H_R C V E + G - (E : ℂ) • 1) 1 r := by
  have h := hgrid.trans (isPerturbation_truncF hH C ε V G hdet)
  rw [zero_add, add_zero] at h
  obtain ⟨Y, hY, hr⟩ := h
  exact ⟨Y, by omega, hr⟩

end BlockBand.LocalWindow
