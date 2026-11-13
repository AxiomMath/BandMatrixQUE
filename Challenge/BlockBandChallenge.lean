module

public import BlockBand.Statements

/-!
# The formal challenge

Formal statements of Theorems 1.1, 1.3 and 1.4 of *Quantum unique ergodicity and the critical crossover for
1-d Gaussian band matrices*, with `sorry` as proof. The definitions they use are in `BlockBand.Statements` and
its imports. The module `BlockBandSolution` proves the same statements.
-/

set_option autoImplicit false
set_option warningAsError false

@[expose] public section

noncomputable section

namespace BlockBand

open MeasureTheory

/-- **Theorem 1.1** (quantum unique ergodicity at every bulk rank).

There is one constant depending only on `(b, θ, T)`. Dimensions, the exact
physical Gaussian model, deterministic rank, and deterministic real site test
are quantified after that constant and outside the expectation. The estimate
uses the physical row-variance-one matrix and admits every parity. -/
theorem que
    (b θ T : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hθ : 0 < θ) (hθ' : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n W : ℕ)
        (hn : 4 ≤ n) (hW : 0 < W)
        (hnW : (n : ℝ) ≤ T * (W : ℝ)),
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      Nonempty (FiniteRealization p) ∧
        ∀ (R : FiniteRealization p) (α : Fin p.N),
          IsBulkRank p θ α →
        ∀ v : p.Site → ℝ, (∀ x, |v x| ≤ 1) →
          R.spectral.queStatistic α v ≤
            C * (p.ratio + Real.rpow p.ratio (3 / 2 : ℝ)) +
              1 / ((W : ℝ) + 1) := by
  sorry

/-- **Theorem 1.3** (the critical joint law of eigenvalues and eigenvector profiles).

For every fixed admissible `(b,E)` there is a unique all-ratio family. Its
characterization includes convergence along every critical sequence, the full
marked vague topology, simple locations, both mean-intensity identities, and
both stationarities. There is no rate or subsequence parameter. -/
theorem critical
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family := by
  sorry

/-- **Theorem 1.4** (positive profile variance and the sine and Poisson endpoints).

The assertion applies to the already-characterized critical family. It gives a
single smoothing-independent variance, positivity for every positive ratio,
the right limit at zero, and the sine/Poisson spectral limits in that order of
limits. No diagonal `n/W → ∞` assertion is made. -/
theorem endpoints
    (b E : ℝ)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) :
    ∀ family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsCriticalFamily b E hb hb' family →
        HasCriticalEndpoints b E hb hb' family := by
  sorry

end BlockBand
