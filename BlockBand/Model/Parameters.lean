module

public import BlockBand.Prelude

/-!
# Finite block-band parameters

This module fixes the finite-dimensional conventions of the paper:
`n ≥ 4` cyclic blocks, block width `W ≥ 1`, total dimension `N = nW`,
bond weight `0 < b < 1/2`, and diagonal weight `c = 1 - 2b`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand

/-- Admissible finite parameters for the Gaussian block-band ring. -/
structure Parameters where
  n : ℕ
  W : ℕ
  b : ℝ
  n_ge_four : 4 ≤ n
  W_pos : 0 < W
  b_pos : 0 < b
  b_lt_half : b < 1 / 2

namespace Parameters

/-- Total matrix dimension `N = nW`. -/
def N (p : Parameters) : ℕ := p.n * p.W

/-- Diagonal-block weight `c = 1 - 2b`. -/
def c (p : Parameters) : ℝ := 1 - 2 * p.b

/-- A site is a cyclic block index together with an internal block coordinate. -/
abbrev Site (p : Parameters) := ZMod p.n × Fin p.W

theorem n_pos (p : Parameters) : 0 < p.n :=
  lt_of_lt_of_le (by norm_num) p.n_ge_four

theorem N_pos (p : Parameters) : 0 < p.N :=
  Nat.mul_pos p.n_pos p.W_pos

theorem c_pos (p : Parameters) : 0 < p.c := by
  unfold c
  nlinarith [p.b_lt_half]

theorem c_add_two_b (p : Parameters) : p.c + 2 * p.b = 1 := by
  simp [c]

instance (p : Parameters) : NeZero p.n := ⟨p.n_pos.ne'⟩
instance (p : Parameters) : NeZero p.W := ⟨p.W_pos.ne'⟩
instance (p : Parameters) : NeZero p.N := ⟨p.N_pos.ne'⟩

/-- Real critical ratio `n/W`, never truncated natural-number division. -/
noncomputable def ratio (p : Parameters) : ℝ :=
  (p.n : ℝ) / (p.W : ℝ)

end Parameters

end BlockBand
