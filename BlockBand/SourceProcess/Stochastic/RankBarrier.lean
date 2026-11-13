module
public import BlockBand.SourceProcess.Stochastic.FiniteSource
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Gram rank barrier: statement

In the proof of the finite Gram law, with `e_k` the `k`-th elementary
symmetric function of the eigenvalues of a positive matrix (`e_k(U*U) = ‖∧^k U‖²_HS` by
Cauchy–Binet, also at singular matrices), on a trace stop `Tr M ≤ K`,

  `𝒢 e_k(B) ≤ C_{K,k,Naux} e_k(B)`,  `𝒢 e_k(C) ≤ C_{K,k,Naux} e_k(C)`,  `C = M − B`,

where `𝒢` is the generator. The paper proves it through the ambient lift: the near rows
solve a left-linear equation and the far rows a right-linear one, so `∧^k L`, `∧^k F` solve
linear equations with bounded coefficients. We state it in that ambient form, with the generator
`sdeGenerator` of the finite source equation applied to `V ↦ e_k(VᴴPV)` and
`V ↦ e_k(VᴴV − VᴴPV)`. The constant may depend on `K, k`, the ambient and column dimensions (it
need not be independent of the finite padding dimension), `D₀`, `P`, `𝖣`. This file only states.
-/

namespace BlockBand.SourceProcess.Stochastic
open MeasureTheory Matrix
open BlockBand.SourceProcess

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

/-- `e_k(A)`: the sum of the `k × k` principal minors (real part), i.e. the `k`-th elementary
symmetric function of the eigenvalues for Hermitian `A`. -/
def principalMinorSum (k : ℕ) (A : Matrix c c ℂ) : ℝ :=
  (∑ s ∈ (Finset.univ : Finset c).powersetCard k,
    (A.submatrix (fun i : s => (i : c)) (fun i : s => (i : c))).det).re

/-- **Rank barrier, ambient form.** Under the standing hypotheses, for
every `k` and trace level `K` there is a constant `C` such that for every constrained frame `V`
with `Tr M = ‖V‖²_HS ≤ K`, the generator of the finite source equation applied to `e_k(B)` and to
`e_k(M − B)` is at most `C` times the function. -/
def GramRankBarrier (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) : Prop :=
  0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ (k : ℕ) (K : ℝ), ∃ C : ℝ, ∀ V : Matrix ι c ℂ, TwoProjection P D V → ‖V‖ ^ 2 ≤ K →
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
        (fun W => principalMinorSum k (nearGram P W)) V ≤
      C * principalMinorSum k (nearGram P V) ∧
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
        (fun W => principalMinorSum k (sourceGram W - nearGram P W)) V ≤
      C * principalMinorSum k (sourceGram V - nearGram P V)

/-- **Rank barrier, uniform over realizations.** For fixed `D₀`, column type `c`
and signature `𝖣`, the constant depends only on `k` and the trace level `K`: it is uniform over
every finite ambient dimension `n`, rank `Naux` and near projection `P` realizing a constrained
frame.
This is the form needed to apply the barrier along a Gram path whose states are only
known to be feasible (`GramFeasible`, each with its own realization).
-/
def GramRankBarrierUniform (D0 : ℝ) (D : Matrix c c ℂ) : Prop :=
  0 < D0 → IsSignature D →
  ∀ (k : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (n Naux : ℕ) (P : Matrix (Fin n) (Fin n) ℂ)
    (V : Matrix (Fin n) c ℂ), IsNearProjection P Naux → TwoProjection P D V → ‖V‖ ^ 2 ≤ K →
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
        (fun W => principalMinorSum k (nearGram P W)) V ≤
      C * principalMinorSum k (nearGram P V) ∧
    sdeGenerator (sourceDrift D0 Naux P) (sourceDiffusion D0 P D)
        (fun W => principalMinorSum k (sourceGram W - nearGram P W)) V ≤
      C * principalMinorSum k (sourceGram V - nearGram P V)

end BlockBand.SourceProcess.Stochastic
