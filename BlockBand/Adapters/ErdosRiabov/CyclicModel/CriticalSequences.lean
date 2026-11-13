module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Conventions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Nat
public import Mathlib

/-!
# Critical sequences

An admissible integer sequence of dimensions `n ≥ 4`, `W ≥ 1` with `W → ∞` and real
ratio `n/W → τ`. The ratio may be zero: the QUE regime includes bounded `n`,
so divergence of `n` is deliberately not a structure field.
-/

@[expose] public section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel

open Filter Topology MeasureTheory

/-- An admissible integer sequence with
`W → ∞` and real `n/W → τ`. No rate, parity, subsequence, positive-`τ` premise,
or `n → ∞` premise is imposed. Positive finite critical-law theorems separately
require `0 < τ`; the same dimensions also represent the zero-ratio QUE regime. -/
structure CriticalSequence (τ : ℝ) where
  n : ℕ → ℕ
  W : ℕ → ℕ
  n_ge_four : ∀ j, 4 ≤ n j
  W_ge_one : ∀ j, 1 ≤ W j
  width_tendsto : Tendsto W atTop atTop
  ratio_tendsto : Tendsto (fun j => (n j : ℝ) / (W j : ℝ)) atTop (𝓝 τ)

namespace CriticalSequence

/-- The ratio is real division, not truncated division of naturals. -/
noncomputable def ratio {τ : ℝ} (s : CriticalSequence τ) (j : ℕ) : ℝ :=
  (s.n j : ℝ) / (s.W j : ℝ)

end CriticalSequence

end BlockBand.Adapters.ErdosRiabov.CyclicModel
