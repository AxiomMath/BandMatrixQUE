module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# The Hermitian eigenvector moment-flow generator on `r`-particle configurations

* A configuration `ξ : Fin N → ℕ` gives the number of particles at each eigenvalue label.
  The `r`-particle sector is `sector N r = {ξ : ∑ ξ_i = r}` (Mathlib's
  `Finset.Nat.antidiagonalTuple`), a finite set.
* `move ξ i j = ξ^{i,j}` moves one particle from `i` to `j`.
* `momentGenerator c f ξ = ∑_{i ≠ j} c_ij ξ_i (1 + ξ_j) [f(ξ^{i,j}) - f(ξ)]`, the moment-flow
  operator `𝓑_u` when `c_ij = c_ij(u) = 1/(N(λ_i(u) - λ_j(u))²)` (`flowRate`); the short
  generator `𝓢` is the same operator with the rate matrix masked to `|i - j| < ℓ` (`maskRate`).
* Proved: sector invariance of legal moves, the generator kills constants and is linear,
  it depends only on the values on the sector, the pointwise maximum/minimum principle
  (`momentGenerator_nonpos_of_isMax`), pointwise detailed balance with counting measure
  (the reverse coefficient at `ξ^{i,j}` is `(ξ_j + 1) ξ_i`), the global
  symmetry `∑_ξ g 𝓑f = ∑_ξ f 𝓑g` on the sector (self-adjointness for counting measure), and the
  exact removal identity at the level of monomials.

The variance-one circular normalization is `r!`; the normalized monomial is
`momentMonomial X ξ = ∏_i X_i^{ξ_i} / ξ_i!`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset

/-- Occupation configurations: `ξ i` particles at label `i`. -/
abbrev Occ (N : ℕ) := Fin N → ℕ

variable {N : ℕ}

/-- The `r`-particle sector `{ξ : ∑_i ξ_i = r}`. -/
def sector (N r : ℕ) : Finset (Occ N) := Finset.Nat.antidiagonalTuple N r

theorem mem_sector {r : ℕ} {ξ : Occ N} : ξ ∈ sector N r ↔ ∑ i, ξ i = r :=
  Finset.Nat.mem_antidiagonalTuple

/-- `ξ^{i,j}`: move one particle from `i` to `j` (total; used when `ξ i > 0`, `i ≠ j`). -/
def move (ξ : Occ N) (i j : Fin N) : Occ N :=
  Function.update (Function.update ξ i (ξ i - 1)) j (ξ j + 1)

/-- `ξ - δ_i`: remove one particle at `i` (total; used when `ξ i > 0`). -/
def remove (ξ : Occ N) (i : Fin N) : Occ N := Function.update ξ i (ξ i - 1)

theorem move_apply_source (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) : move ξ i j i = ξ i - 1 := by
  simp [move, hij]

theorem move_apply_target (ξ : Occ N) (i j : Fin N) : move ξ i j j = ξ j + 1 := by
  simp [move]

theorem move_apply_of_ne (ξ : Occ N) {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j) :
    move ξ i j k = ξ k := by
  simp [move, hki, hkj]

theorem move_eq_update_remove (ξ : Occ N) (i j : Fin N) :
    move ξ i j = Function.update (remove ξ i) j (ξ j + 1) := by
  simp [move, remove]

/-- A legal move preserves the particle number. -/
theorem sum_move (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) (hi : 0 < ξ i) :
    ∑ k, move ξ i j k = ∑ k, ξ k := by
  classical
  have hsplit : ∀ g : Occ N, ∑ k, g k = g i + g j + ∑ k ∈ (univ.erase i).erase j, g k := by
    intro g
    rw [← Finset.add_sum_erase _ _ (mem_univ i),
      ← Finset.add_sum_erase _ _ (mem_erase.2 ⟨Ne.symm hij, mem_univ j⟩)]
    ring
  rw [hsplit (move ξ i j), hsplit ξ, move_apply_source ξ hij, move_apply_target]
  have hrest : ∑ k ∈ (univ.erase i).erase j, move ξ i j k = ∑ k ∈ (univ.erase i).erase j, ξ k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := (mem_erase.1 hk).1
    have hki : k ≠ i := (mem_erase.1 (mem_erase.1 hk).2).1
    exact move_apply_of_ne ξ hki hkj
  rw [hrest]
  omega

theorem move_mem_sector {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {i j : Fin N} (hij : i ≠ j)
    (hi : 0 < ξ i) : move ξ i j ∈ sector N r := by
  rw [mem_sector] at hξ ⊢
  rw [sum_move ξ hij hi, hξ]

/-- Moving back undoes a legal move. -/
theorem move_move (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) (hi : 0 < ξ i) :
    move (move ξ i j) j i = ξ := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [move_apply_target, move_apply_source ξ hij]
    omega
  · by_cases hkj : k = j
    · subst hkj
      rw [move_apply_source _ (Ne.symm hij), move_apply_target]
      omega
    · rw [move_apply_of_ne _ hkj hki, move_apply_of_ne _ hki hkj]

/-- The ordered jump coefficient `ξ_i (1 + ξ_j)` of the Hermitian (β = 2) flow. -/
def jumpCoeff (ξ : Occ N) (i j : Fin N) : ℝ := (ξ i : ℝ) * (1 + (ξ j : ℝ))

theorem jumpCoeff_nonneg (ξ : Occ N) (i j : Fin N) : 0 ≤ jumpCoeff ξ i j := by
  unfold jumpCoeff; positivity

theorem jumpCoeff_eq_zero_of_eq_zero (ξ : Occ N) {i : Fin N} (j : Fin N) (hi : ξ i = 0) :
    jumpCoeff ξ i j = 0 := by
  simp [jumpCoeff, hi]

/-- **Detailed balance with counting measure**: the reverse coefficient at
`ξ^{i,j}` equals the forward one, `(ξ_j + 1) ξ_i`. -/
theorem jumpCoeff_move_reverse (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) (hi : 0 < ξ i) :
    jumpCoeff (move ξ i j) j i = jumpCoeff ξ i j := by
  unfold jumpCoeff
  rw [move_apply_target, move_apply_source ξ hij]
  have : ((ξ i - 1 : ℕ) : ℝ) = (ξ i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [this]; push_cast; ring

/-- `𝓑 f (ξ) = ∑_{i ≠ j} c_ij ξ_i (1 + ξ_j) [f(ξ^{i,j}) - f(ξ)]`, the moment-flow generator at a
fixed time, for the rate matrix `c`. -/
def momentGenerator (c : Fin N → Fin N → ℝ) (f : Occ N → ℝ) (ξ : Occ N) : ℝ :=
  ∑ i, ∑ j ∈ univ.erase i, c i j * jumpCoeff ξ i j * (f (move ξ i j) - f ξ)

/-- The rate matrix masked to the pairs satisfying `P` (short jumps: `P i j ↔ |i-j| < ℓ`). -/
def maskRate (P : Fin N → Fin N → Prop) [DecidableRel P] (c : Fin N → Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  if P i j then c i j else 0

theorem maskRate_nonneg (P : Fin N → Fin N → Prop) [DecidableRel P] {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, i ≠ j → 0 ≤ c i j) (i j : Fin N) (hij : i ≠ j) : 0 ≤ maskRate P c i j := by
  unfold maskRate; split_ifs
  · exact hc i j hij
  · exact le_rfl

theorem maskRate_symm (P : Fin N → Fin N → Prop) [DecidableRel P] {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, c i j = c j i) (hP : ∀ i j, P i j ↔ P j i) (i j : Fin N) :
    maskRate P c i j = maskRate P c j i := by
  unfold maskRate
  by_cases h : P i j
  · simp [h, (hP i j).1 h, hc]
  · have h' : ¬ P j i := fun h' => h ((hP i j).2 h')
    simp [h, h']

/-- The generator kills constants (conservation). -/
@[simp]
theorem momentGenerator_const (c : Fin N → Fin N → ℝ) (a : ℝ) (ξ : Occ N) :
    momentGenerator c (fun _ => a) ξ = 0 := by
  simp [momentGenerator]

theorem momentGenerator_add (c : Fin N → Fin N → ℝ) (f g : Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c (f + g) ξ = momentGenerator c f ξ + momentGenerator c g ξ := by
  simp only [momentGenerator, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem momentGenerator_smul (c : Fin N → Fin N → ℝ) (a : ℝ) (f : Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c (a • f) ξ = a * momentGenerator c f ξ := by
  simp only [momentGenerator, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem momentGenerator_sub (c : Fin N → Fin N → ℝ) (f g : Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c (f - g) ξ = momentGenerator c f ξ - momentGenerator c g ξ := by
  simp only [momentGenerator, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem momentGenerator_neg (c : Fin N → Fin N → ℝ) (f : Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c (fun ζ => -f ζ) ξ = -momentGenerator c f ξ := by
  simp only [momentGenerator, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- On the sector the generator only sees the values of `f` on the sector. -/
theorem momentGenerator_congr_sector (c : Fin N → Fin N → ℝ) {r : ℕ} {f g : Occ N → ℝ}
    (hfg : ∀ ζ ∈ sector N r, f ζ = g ζ) {ξ : Occ N} (hξ : ξ ∈ sector N r) :
    momentGenerator c f ξ = momentGenerator c g ξ := by
  unfold momentGenerator
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (Ne.symm (mem_erase.1 hj).1)
  rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
  · simp [jumpCoeff_eq_zero_of_eq_zero ξ j hi]
  · rw [hfg _ (move_mem_sector hξ hij hi), hfg _ hξ]

/-- **Maximum principle at a configuration.** For off-diagonal rates `c ≥ 0`, at a maximizer
over the sector the generator is nonpositive: every legal jump lowers or keeps the value. -/
theorem momentGenerator_nonpos_of_isMax {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, i ≠ j → 0 ≤ c i j) {r : ℕ} {f : Occ N → ℝ} {ξ : Occ N}
    (hξ : ξ ∈ sector N r) (hmax : ∀ ζ ∈ sector N r, f ζ ≤ f ξ) :
    momentGenerator c f ξ ≤ 0 := by
  unfold momentGenerator
  refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_
  have hij : i ≠ j := (Ne.symm (mem_erase.1 hj).1)
  rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
  · simp [jumpCoeff_eq_zero_of_eq_zero ξ j hi]
  · have h1 : f (move ξ i j) - f ξ ≤ 0 := sub_nonpos.2 (hmax _ (move_mem_sector hξ hij hi))
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hc i j hij) (jumpCoeff_nonneg ξ i j)) h1

/-- **Minimum principle at a configuration.** -/
theorem momentGenerator_nonneg_of_isMin {c : Fin N → Fin N → ℝ}
    (hc : ∀ i j, i ≠ j → 0 ≤ c i j) {r : ℕ} {f : Occ N → ℝ} {ξ : Occ N}
    (hξ : ξ ∈ sector N r) (hmin : ∀ ζ ∈ sector N r, f ξ ≤ f ζ) :
    0 ≤ momentGenerator c f ξ := by
  have h := momentGenerator_nonpos_of_isMax hc (f := fun ζ => -f ζ) hξ
    (fun ζ hζ => neg_le_neg (hmin ζ hζ))
  rw [momentGenerator_neg] at h
  linarith

/-!
## Global detailed balance: self-adjointness for counting measure on the sector
-/

/-- Legal transitions out of the sector: `(ξ, i, j)` with `ξ ∈ sector`, `i ≠ j`, `ξ_i > 0`. -/
def legalTriples (N r : ℕ) : Finset (Occ N × Fin N × Fin N) :=
  (sector N r ×ˢ (univ ×ˢ univ)).filter fun p => p.2.1 ≠ p.2.2 ∧ 0 < p.1 p.2.1

/-- The off-diagonal part `∑_{ξ} g(ξ) ∑_{i≠j} c_ij ξ_i(1+ξ_j) f(ξ^{i,j})` as a sum over legal
transitions. -/
theorem sum_sector_jump_eq (c : Fin N → Fin N → ℝ) (r : ℕ) (F : Occ N → Fin N → Fin N → ℝ) :
    ∑ ξ ∈ sector N r, ∑ i, ∑ j ∈ univ.erase i, c i j * jumpCoeff ξ i j * F ξ i j =
      ∑ p ∈ legalTriples N r, c p.2.1 p.2.2 * jumpCoeff p.1 p.2.1 p.2.2 * F p.1 p.2.1 p.2.2 := by
  classical
  unfold legalTriples
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_erase_add _ _ (mem_univ i)]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
  rcases Nat.eq_zero_or_pos (ξ i) with hi | hi
  · simp [jumpCoeff_eq_zero_of_eq_zero ξ j hi, hi]
  · simp [hij, hi]

/-- The involution `(ξ, i, j) ↦ (ξ^{i,j}, j, i)` of legal transitions reverses the
off-diagonal part: `∑ w g(ξ) f(ξ^{ij}) = ∑ w f(ξ) g(ξ^{ij})` for symmetric rates. -/
theorem sum_legal_swap {c : Fin N → Fin N → ℝ} (hc : ∀ i j, c i j = c j i) (r : ℕ)
    (f g : Occ N → ℝ) :
    ∑ p ∈ legalTriples N r, c p.2.1 p.2.2 * jumpCoeff p.1 p.2.1 p.2.2 *
        (g p.1 * f (move p.1 p.2.1 p.2.2)) =
      ∑ p ∈ legalTriples N r, c p.2.1 p.2.2 * jumpCoeff p.1 p.2.1 p.2.2 *
        (f p.1 * g (move p.1 p.2.1 p.2.2)) := by
  classical
  let σ : Occ N × Fin N × Fin N → Occ N × Fin N × Fin N := fun p => (move p.1 p.2.1 p.2.2, p.2.2, p.2.1)
  have hmem : ∀ p ∈ legalTriples N r, σ p ∈ legalTriples N r := by
    intro p hp
    simp only [legalTriples, mem_filter, mem_product, mem_univ, and_true] at hp ⊢
    obtain ⟨hs, hij, hi⟩ := hp
    refine ⟨move_mem_sector hs hij hi, Ne.symm hij, ?_⟩
    simp only [σ, move_apply_target]; omega
  have hinv : ∀ p ∈ legalTriples N r, σ (σ p) = p := by
    intro p hp
    simp only [legalTriples, mem_filter, mem_product, mem_univ, and_true] at hp
    obtain ⟨_, hij, hi⟩ := hp
    simp only [σ, move_move p.1 hij hi]
  refine Finset.sum_nbij' σ σ hmem hmem hinv hinv ?_
  intro p hp
  simp only [legalTriples, mem_filter, mem_product, mem_univ, and_true] at hp
  obtain ⟨_, hij, hi⟩ := hp
  simp only [σ, move_move p.1 hij hi, jumpCoeff_move_reverse p.1 hij hi, hc p.2.2 p.2.1]
  ring

/-- **Detailed balance with counting measure (global form).** For symmetric rates the moment
generator is self-adjoint on every sector for counting measure. -/
theorem sum_mul_momentGenerator_symm {c : Fin N → Fin N → ℝ} (hc : ∀ i j, c i j = c j i)
    (r : ℕ) (f g : Occ N → ℝ) :
    ∑ ξ ∈ sector N r, g ξ * momentGenerator c f ξ =
      ∑ ξ ∈ sector N r, f ξ * momentGenerator c g ξ := by
  have key : ∀ f g : Occ N → ℝ, ∑ ξ ∈ sector N r, g ξ * momentGenerator c f ξ =
      ∑ p ∈ legalTriples N r, c p.2.1 p.2.2 * jumpCoeff p.1 p.2.1 p.2.2 *
        (g p.1 * f (move p.1 p.2.1 p.2.2)) -
      ∑ p ∈ legalTriples N r, c p.2.1 p.2.2 * jumpCoeff p.1 p.2.1 p.2.2 * (g p.1 * f p.1) := by
    intro f g
    rw [← sum_sector_jump_eq c r (fun ξ i j => g ξ * f (move ξ i j)),
      ← sum_sector_jump_eq c r (fun ξ i j => g ξ * f ξ), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    simp only [momentGenerator, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key f g, key g f, sum_legal_swap hc r f g]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- Conservation of total mass for counting measure: `∑_ξ 𝓑 f(ξ) = 0` on every sector. -/
theorem sum_momentGenerator_eq_zero {c : Fin N → Fin N → ℝ} (hc : ∀ i j, c i j = c j i)
    (r : ℕ) (f : Occ N → ℝ) : ∑ ξ ∈ sector N r, momentGenerator c f ξ = 0 := by
  have h := sum_mul_momentGenerator_symm hc r f (fun _ => 1)
  simpa using h

/-!
## Normalized monomials and the removal identity
-/

/-- `∏_i X_i^{ξ_i} / ξ_i!`, the normalized moment observable (variance-one circular). -/
def momentMonomial (X : Fin N → ℝ) (ξ : Occ N) : ℝ :=
  ∏ i, X i ^ ξ i / ((ξ i).factorial : ℝ)

theorem momentMonomial_zero (X : Fin N → ℝ) : momentMonomial X (fun _ => 0) = 1 := by
  simp [momentMonomial]

theorem momentMonomial_update (X : Fin N → ℝ) (ξ : Occ N) (j : Fin N) (n : ℕ) :
    momentMonomial X (Function.update ξ j n) =
      X j ^ n / (n.factorial : ℝ) * ∏ k ∈ univ.erase j, X k ^ ξ k / ((ξ k).factorial : ℝ) := by
  classical
  unfold momentMonomial
  rw [← Finset.mul_prod_erase _ _ (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (mem_erase.1 hk).1]

theorem momentMonomial_split (X : Fin N → ℝ) (ξ : Occ N) (j : Fin N) :
    momentMonomial X ξ =
      X j ^ ξ j / ((ξ j).factorial : ℝ) * ∏ k ∈ univ.erase j, X k ^ ξ k / ((ξ k).factorial : ℝ) := by
  conv_lhs => rw [← Function.update_eq_self j ξ]
  exact momentMonomial_update X ξ j (ξ j)

/-- **Removal identity, unoccupied or occupied destination `j ≠ i`**:
`P_i X_j = (1 + ξ_j) ∏_h X_h^{ξ^{ij}_h}/ξ^{ij}_h!`, with `P_i` the monomial of `ξ - δ_i`. -/
theorem momentMonomial_remove_mul_ne (X : Fin N → ℝ) (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    momentMonomial X (remove ξ i) * X j =
      ((ξ j : ℝ) + 1) * momentMonomial X (move ξ i j) := by
  rw [move_eq_update_remove ξ i j, momentMonomial_update, momentMonomial_split X (remove ξ i) j]
  have hj : remove ξ i j = ξ j := by simp [remove, Ne.symm hij]
  rw [hj, Nat.factorial_succ, pow_succ]
  push_cast
  have hf : ((ξ j).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Removal identity, destination `j = i`**: `P_i X_i = ξ_i ∏_h X_h^{ξ_h}/ξ_h!`. -/
theorem momentMonomial_remove_mul_self (X : Fin N → ℝ) (ξ : Occ N) {i : Fin N} (hi : 0 < ξ i) :
    momentMonomial X (remove ξ i) * X i = (ξ i : ℝ) * momentMonomial X ξ := by
  unfold remove
  rw [momentMonomial_update, momentMonomial_split X ξ i]
  obtain ⟨m, hm⟩ : ∃ m, ξ i = m + 1 := ⟨ξ i - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  push_cast
  have hf : ((m).factorial : ℝ) ≠ 0 := by positivity
  field_simp

end BlockBand.Palm.MomentFlow
