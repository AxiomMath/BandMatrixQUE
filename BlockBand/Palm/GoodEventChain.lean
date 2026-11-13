module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Good spectral event: deterministic dyadic chaining

Deterministic, no measure. Let `d` be a pseudo-distance on `ℝ` (triangle inequality,
`d u u = 0`) that is continuous in its first argument, `T > 0`, and suppose every dyadic
increment of level `n` (`d((k+1)T/2ⁿ, kT/2ⁿ)`, `k < 2ⁿ`) is at most `b n ≥ 0`. Then for
every level `m`, every `k < 2^m` and every `u` in the dyadic interval
`[kT/2^m, (k+1)T/2^m]`, `d(u, kT/2^m) ≤ B` whenever all partial sums
`Σ_{n ≤ j} b(m+n)` are at most `B` (`chain_bound`).

Proof: induction on the refinement depth `j` for the dyadic points
`(k2^j + i)T/2^{m+j}`, `i ≤ 2^j` (`chain_dyadic`), then approximation of `u` by the dyadic
points `u_j ↑ u` and continuity of `d(·, kT/2^m)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open Filter Topology

section Chain

variable (d : ℝ → ℝ → ℝ) (htri : ∀ u v w, d u w ≤ d u v + d v w) (hself : ∀ u, d u u = 0)
  {T : ℝ} (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
  (hinc : ∀ n k : ℕ, k < 2 ^ n → d (((k : ℝ) + 1) * T / 2 ^ n) ((k : ℝ) * T / 2 ^ n) ≤ b n)

include htri hself hb hinc in
/-- Chaining along dyadic refinements: for `i ≤ 2^j`,
`d((k 2^j + i) T / 2^{m+j}, kT/2^m) ≤ Σ_{n ≤ j} b(m+n)`. -/
theorem chain_dyadic (m k : ℕ) (hk : k < 2 ^ m) :
    ∀ j : ℕ, ∀ i : ℕ, i ≤ 2 ^ j →
      d (((k * 2 ^ j + i : ℕ) : ℝ) * T / 2 ^ (m + j)) ((k : ℝ) * T / 2 ^ m) ≤
        ∑ n ∈ Finset.range (j + 1), b (m + n) := by
  intro j
  induction j with
  | zero =>
    intro i hi
    simp only [pow_zero, add_zero, mul_one, zero_add, Finset.sum_range_one] at hi ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with h | h
    · subst h; simp only [add_zero]; rw [hself]; exact hb m
    · subst h; push_cast; exact hinc m k hk
  | succ j ih =>
    intro i hi
    set i' := i / 2 with hi'
    have hdiv : i = 2 * i' + i % 2 := (Nat.div_add_mod i 2).symm
    have hi'le : i' ≤ 2 ^ j := by
      rw [hi', Nat.div_le_iff_le_mul_add_pred (by norm_num)]
      rw [pow_succ] at hi; omega
    have hQ : (((k * 2 ^ (j + 1) + 2 * i' : ℕ) : ℝ) * T / 2 ^ (m + (j + 1))) =
        ((k * 2 ^ j + i' : ℕ) : ℝ) * T / 2 ^ (m + j) := by
      push_cast
      rw [show m + (j + 1) = (m + j) + 1 by ring, pow_succ, pow_succ]
      have : (0 : ℝ) < 2 ^ (m + j) := by positivity
      field_simp
    have hih := ih i' hi'le
    rw [Finset.sum_range_succ]
    have hstep : d (((k * 2 ^ (j + 1) + i : ℕ) : ℝ) * T / 2 ^ (m + (j + 1)))
        (((k * 2 ^ (j + 1) + 2 * i' : ℕ) : ℝ) * T / 2 ^ (m + (j + 1))) ≤ b (m + (j + 1)) := by
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · have : i = 2 * i' := by omega
        rw [this, hself]; exact hb _
      · have hieq : k * 2 ^ (j + 1) + i = (k * 2 ^ (j + 1) + 2 * i') + 1 := by omega
        have hlt : k * 2 ^ (j + 1) + 2 * i' < 2 ^ (m + (j + 1)) := by
          have h1 : k + 1 ≤ 2 ^ m := hk
          have h2 : (k + 1) * 2 ^ (j + 1) ≤ 2 ^ m * 2 ^ (j + 1) := Nat.mul_le_mul_right _ h1
          rw [← pow_add] at h2
          rw [pow_succ] at hi ⊢
          rw [pow_succ] at h2
          nlinarith
        have := hinc (m + (j + 1)) (k * 2 ^ (j + 1) + 2 * i') hlt
        rw [hieq]
        push_cast at this ⊢
        exact this
    calc _ ≤ d (((k * 2 ^ (j + 1) + i : ℕ) : ℝ) * T / 2 ^ (m + (j + 1)))
          (((k * 2 ^ (j + 1) + 2 * i' : ℕ) : ℝ) * T / 2 ^ (m + (j + 1))) +
          d (((k * 2 ^ (j + 1) + 2 * i' : ℕ) : ℝ) * T / 2 ^ (m + (j + 1)))
            ((k : ℝ) * T / 2 ^ m) := htri _ _ _
      _ ≤ b (m + (j + 1)) + ∑ n ∈ Finset.range (j + 1), b (m + n) := by
          refine add_le_add hstep ?_
          rw [hQ]; exact hih
      _ = _ := add_comm _ _

end Chain

/-- **Dyadic chaining.** Every point of a level-`m` dyadic interval is within `B` of its
left endpoint, when level-`n` increments are at most `b n` and the tail partial sums from
level `m` are at most `B`. -/
theorem chain_bound (d : ℝ → ℝ → ℝ) (htri : ∀ u v w, d u w ≤ d u v + d v w)
    (hself : ∀ u, d u u = 0)
    (hcont : ∀ w, Continuous fun u => d u w) {T : ℝ} (hT : 0 < T) (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hinc : ∀ n k : ℕ, k < 2 ^ n → d (((k : ℝ) + 1) * T / 2 ^ n) ((k : ℝ) * T / 2 ^ n) ≤ b n)
    (m : ℕ) {B : ℝ} (hB : ∀ j, ∑ n ∈ Finset.range (j + 1), b (m + n) ≤ B)
    (k : ℕ) (hk : k < 2 ^ m) (u : ℝ) (hu1 : (k : ℝ) * T / 2 ^ m ≤ u)
    (hu2 : u ≤ ((k : ℝ) + 1) * T / 2 ^ m) :
    d u ((k : ℝ) * T / 2 ^ m) ≤ B := by
  set a := (k : ℝ) * T / 2 ^ m with ha
  set w := T / 2 ^ m with hw
  have hwpos : 0 < w := by positivity
  have hua : 0 ≤ u - a := by linarith
  have huw : u - a ≤ w := by
    have : ((k : ℝ) + 1) * T / 2 ^ m = a + w := by rw [ha, hw]; ring
    linarith
  -- dyadic approximants
  let x : ℕ → ℝ := fun j => (u - a) * 2 ^ j / w
  let i : ℕ → ℕ := fun j => ⌊x j⌋₊
  have hx0 : ∀ j, 0 ≤ x j := fun j => by positivity
  have hile : ∀ j, i j ≤ 2 ^ j := fun j => by
    apply Nat.floor_le_of_le
    have : x j ≤ 2 ^ j := by
      change (u - a) * 2 ^ j / w ≤ 2 ^ j
      rw [div_le_iff₀ hwpos]
      have : (0 : ℝ) ≤ 2 ^ j := by positivity
      nlinarith
    exact_mod_cast this
  let uj : ℕ → ℝ := fun j => ((k * 2 ^ j + i j : ℕ) : ℝ) * T / 2 ^ (m + j)
  have huj : ∀ j, uj j = a + (i j : ℝ) * w / 2 ^ j := fun j => by
    change ((k * 2 ^ j + i j : ℕ) : ℝ) * T / 2 ^ (m + j) = _
    rw [ha, hw, pow_add]
    push_cast
    field_simp
  have hbelow : ∀ j, uj j ≤ u := fun j => by
    rw [huj]
    have h1 : (i j : ℝ) ≤ x j := Nat.floor_le (hx0 j)
    have : (i j : ℝ) * w / 2 ^ j ≤ x j * w / 2 ^ j := by gcongr
    have hx : x j * w / 2 ^ j = u - a := by
      change (u - a) * 2 ^ j / w * w / 2 ^ j = u - a
      field_simp
    linarith
  have habove : ∀ j, u - w * (1 / 2) ^ j ≤ uj j := fun j => by
    rw [huj]
    have h1 : x j < (i j : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : x j * w / 2 ^ j < ((i j : ℝ) + 1) * w / 2 ^ j := by gcongr
    have hx : x j * w / 2 ^ j = u - a := by
      change (u - a) * 2 ^ j / w * w / 2 ^ j = u - a
      field_simp
    have h3 : ((i j : ℝ) + 1) * w / 2 ^ j = (i j : ℝ) * w / 2 ^ j + w * (1 / 2) ^ j := by
      rw [one_div_pow]; ring
    linarith
  have htend : Tendsto uj atTop (𝓝 u) := by
    have hl : Tendsto (fun j : ℕ => u - w * (1 / 2 : ℝ) ^ j) atTop (𝓝 u) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul w
      simpa using (tendsto_const_nhds (x := u)).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds habove hbelow
  have hlim : Tendsto (fun j => d (uj j) a) atTop (𝓝 (d u a)) :=
    ((hcont a).tendsto u).comp htend
  refine le_of_tendsto' hlim (fun j => ?_)
  exact (chain_dyadic d htri hself b hb hinc m k hk j (i j) (hile j)).trans (hB j)

end BlockBand.Palm.GoodEvent
