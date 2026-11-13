module

public import BlockBand.Model.Parameters

/-!
# Admissible critical sequences

There is no rate, parity, monotonicity, or `n → ∞` hypothesis. Width diverges
and the real ratio `n/W` converges to the prescribed value.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand

open Filter Topology

/-- An admissible sequence with `W → ∞` and `n/W → τ`. -/
structure CriticalSequence (τ : ℝ) where
  n : ℕ → ℕ
  W : ℕ → ℕ
  n_ge_four : ∀ j, 4 ≤ n j
  W_pos : ∀ j, 0 < W j
  width_tendsto : Tendsto W atTop atTop
  ratio_tendsto :
    Tendsto (fun j => (n j : ℝ) / (W j : ℝ)) atTop (𝓝 τ)

/-- Evaluate a critical sequence at fixed bond parameter `b`. -/
def CriticalSequence.parameters {τ : ℝ} (s : CriticalSequence τ)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (j : ℕ) : Parameters where
  n := s.n j
  W := s.W j
  b := b
  n_ge_four := s.n_ge_four j
  W_pos := s.W_pos j
  b_pos := hb
  b_lt_half := hb'

end BlockBand

