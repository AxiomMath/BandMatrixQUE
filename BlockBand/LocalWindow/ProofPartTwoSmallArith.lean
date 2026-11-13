module

public import BlockBand.LocalWindow.ProofPartTwoSmallGood

/-!
# Grid counts and norm scales of the small-`ρ` branch

Polynomial bounds on the size of the index set and on the norm of the grid deformations used in
the small-`ρ` branch of part (ii).

With `W ≥ 1`, `0 ≤ T`, `n ≤ TW`, `c = nW`, `ε₀ = W^{-A₀}`, `ε₁ = W^{-(A₀+1)}`, `A₀ ≥ 0`:

## Main results

* **`smallIndex_card_le`**: the index set `labels × E-grid × ρ-grid × λ-grid` (with
  `|E-grid| ≤ W^{2(A₀+1)+7}`, `L_ρ = W^H + c²/ε₀`, `d_ρ = W^{-2}`, `δ ≤ 1/2`, `h = (2W)^{-1+β}`)
  has at most `6(T+1)(2T²+4) W^{3A₀+18+|H|}` points.
* **`smallGridK_scale`**: `(c + C_G) + c²/ε₁ + 2 + L_ρ ≤ (T + C_G + 2T² + 3) W^{A₀+5+|H|}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs

/-- `c² / W^{-a} ≤ T² W^{a+4}` for `0 ≤ c ≤ T W²`. -/
theorem sq_div_rpow_neg_le {W c T a : ℝ} (hW : 1 ≤ W) (hc0 : 0 ≤ c) (hc : c ≤ T * W ^ 2) :
    c ^ 2 / W ^ (-a) ≤ T ^ 2 * W ^ (a + 4) := by
  have hW0 : 0 < W := by linarith
  rw [Real.rpow_neg hW0.le, div_inv_eq_mul, Real.rpow_add hW0]
  have h1 : c ^ 2 ≤ (T * W ^ 2) ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have h4 : W ^ (4 : ℝ) = W ^ 4 := by norm_cast
  rw [h4]
  have hWa : 0 ≤ W ^ a := Real.rpow_nonneg hW0.le _
  calc c ^ 2 * W ^ a ≤ (T * W ^ 2) ^ 2 * W ^ a := mul_le_mul_of_nonneg_right h1 hWa
    _ = T ^ 2 * (W ^ a * W ^ 4) := by ring

theorem rpow_le_rpow_one_le {W a b : ℝ} (hW : 1 ≤ W) (hab : a ≤ b) : W ^ a ≤ W ^ b :=
  Real.rpow_le_rpow_of_exponent_le hW hab

/-- **The norm scale of the small-`ρ` grid deformations**. -/
theorem smallGridK_scale {W c CG T A₀ H : ℝ} (hW : 1 ≤ W) (hc0 : 0 ≤ c) (hc : c ≤ T * W ^ 2)
    (hCG : 0 ≤ CG) (hA₀ : 0 ≤ A₀) :
    (c + CG) + c ^ 2 / W ^ (-(A₀ + 1)) + 2 + (W ^ H + c ^ 2 / W ^ (-A₀)) ≤
      (T + CG + 2 * T ^ 2 + 3) * W ^ (A₀ + 5 + |H|) := by
  have hW0 : 0 < W := by linarith
  have hT : 0 ≤ T := by
    by_contra h; push Not at h
    have : T * W ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith
  set X := W ^ (A₀ + 5 + |H|) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hW (by positivity)
  have h1 : c ≤ T * X := by
    have : W ^ 2 ≤ X := by
      rw [show W ^ 2 = W ^ (2 : ℝ) by norm_cast]
      exact rpow_le_rpow_one_le hW (by have := abs_nonneg H; linarith)
    exact hc.trans (mul_le_mul_of_nonneg_left this hT)
  have h2 : c ^ 2 / W ^ (-(A₀ + 1)) ≤ T ^ 2 * X :=
    (sq_div_rpow_neg_le hW hc0 hc).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_one_le hW (by have := abs_nonneg H; linarith)) (sq_nonneg T))
  have h3 : c ^ 2 / W ^ (-A₀) ≤ T ^ 2 * X :=
    (sq_div_rpow_neg_le hW hc0 hc).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_one_le hW (by have := abs_nonneg H; linarith)) (sq_nonneg T))
  have h4 : W ^ H ≤ X := rpow_le_rpow_one_le hW (by have := le_abs_self H; linarith)
  have h5 : CG ≤ CG * X := le_mul_of_one_le_right hCG hX1
  nlinarith

variable {p : Parameters} {i : ZMod p.n}

/-- **The polynomial size of the small-`ρ` index set**. -/
theorem smallIndex_card_le {Es : Finset ℝ} {T A₀ H δ β : ℝ} (hT : 0 ≤ T)
    (hn : (p.n : ℝ) ≤ T * p.W) (hA₀ : 0 ≤ A₀) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hβ0 : 0 ≤ β)
    (hEs : (Es.card : ℝ) ≤ (p.W : ℝ) ^ (2 * (A₀ + 1) + 7)) :
    ((smallIndex (p := p) (i := i) Es ((p.W : ℝ) ^ H + ((p.n : ℝ) * p.W) ^ 2 / (p.W : ℝ) ^ (-A₀))
        ((p.W : ℝ) ^ (-2 : ℝ)) δ (((2 * p.W : ℕ) : ℝ) ^ (-1 + β))).card : ℝ) ≤
      6 * (T + 1) * (2 * T ^ 2 + 4) * (p.W : ℝ) ^ (3 * A₀ + 18 + |H|) := by
  set W : ℝ := (p.W : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by rw [hWdef]; exact_mod_cast p.W_pos
  have hW0 : (0 : ℝ) < W := by linarith
  have key : ∀ a b : ℝ, W ^ a * W ^ b = W ^ (a + b) := fun a b => (Real.rpow_add hW0 a b).symm
  set c := (p.n : ℝ) * W with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc : c ≤ T * W ^ 2 := by
    calc c = (p.n : ℝ) * W := rfl
      _ ≤ T * W * W := mul_le_mul_of_nonneg_right hn hW0.le
      _ = T * W ^ 2 := by ring
  -- labels
  have hlab : ((Finset.univ : Finset (Option (ExteriorSite p i))).card : ℝ) ≤
      (T + 1) * W ^ (2 : ℝ) := by
    rw [Finset.card_univ, Fintype.card_option]
    have h1 : Fintype.card (ExteriorSite p i) ≤ Fintype.card p.Site := Fintype.card_subtype_le _
    have h2 : (Fintype.card p.Site : ℝ) = (p.n : ℝ) * W := by
      simp [Parameters.Site, ZMod.card, hWdef]
    have h3 : ((Fintype.card (ExteriorSite p i) + 1 : ℕ) : ℝ) ≤ (p.n : ℝ) * W + 1 := by
      push_cast; have := (Nat.cast_le (α := ℝ)).mpr h1; linarith
    have hW2 : W ^ (2 : ℝ) = W ^ 2 := by norm_cast
    rw [hW2]
    have : (p.n : ℝ) * W ≤ T * W ^ 2 := hc
    have : (1 : ℝ) ≤ W ^ 2 := one_le_pow₀ hW1
    nlinarith
  -- the `ρ`-grid
  have hρ : ((intervalGrid (W ^ H + c ^ 2 / W ^ (-A₀)) (W ^ (-2 : ℝ))).card : ℝ) ≤
      (2 * T ^ 2 + 4) * W ^ (6 + A₀ + |H|) := by
    have hL0 : 0 ≤ W ^ H + c ^ 2 / W ^ (-A₀) := by positivity
    refine (intervalGrid_card_le hL0 (Real.rpow_pos_of_pos hW0 _)).trans ?_
    set X := W ^ (6 + A₀ + |H|) with hX
    have hX1 : 1 ≤ X := Real.one_le_rpow hW1 (by positivity)
    have e1 : 2 * (W ^ H + c ^ 2 / W ^ (-A₀)) / W ^ (-2 : ℝ) =
        2 * (W ^ H * W ^ (2 : ℝ)) + 2 * (c ^ 2 / W ^ (-A₀) * W ^ (2 : ℝ)) := by
      have hinv : (W ^ (-2 : ℝ))⁻¹ = W ^ (2 : ℝ) := by rw [Real.rpow_neg hW0.le, inv_inv]
      rw [div_eq_mul_inv (2 * (W ^ H + c ^ 2 / W ^ (-A₀))) (W ^ (-2 : ℝ)), hinv]; ring
    have e2 : W ^ H * W ^ (2 : ℝ) ≤ X := by
      rw [key]; exact rpow_le_rpow_one_le hW1 (by have := le_abs_self H; linarith)
    have e3 : c ^ 2 / W ^ (-A₀) * W ^ (2 : ℝ) ≤ T ^ 2 * X := by
      have h1 := sq_div_rpow_neg_le (a := A₀) hW1 hc0 hc
      have h2 : T ^ 2 * W ^ (A₀ + 4) * W ^ (2 : ℝ) ≤ T ^ 2 * X := by
        rw [mul_assoc, key]
        exact mul_le_mul_of_nonneg_left (rpow_le_rpow_one_le hW1
          (by have := abs_nonneg H; linarith)) (sq_nonneg T)
      exact (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hW0.le _)).trans h2
    rw [e1]
    nlinarith
  -- the window-centre grid
  have hμ : ((intervalGrid δ ((((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) / 2)).card : ℝ) ≤ 6 * W ^ (1 : ℝ) := by
    have hd0 : (0 : ℝ) < ((2 * p.W : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.mul_pos two_pos p.W_pos)
    have hdW : ((2 * p.W : ℕ) : ℝ) = 2 * W := by rw [Nat.cast_mul, Nat.cast_two]
    refine (intervalGrid_card_le hδ0 (by positivity)).trans ?_
    have e1 : 2 * δ / (((2 * p.W : ℕ) : ℝ) ^ (-1 + β) / 2) =
        4 * δ * ((2 * p.W : ℕ) : ℝ) ^ (1 - β) := by
      rw [show (-1 + β) = -(1 - β) by ring, Real.rpow_neg hd0.le]
      have : 0 < ((2 * p.W : ℕ) : ℝ) ^ (1 - β) := Real.rpow_pos_of_pos hd0 _
      field_simp
      ring
    have e2 : ((2 * p.W : ℕ) : ℝ) ^ (1 - β) ≤ 2 * W := by
      rw [← hdW]
      calc ((2 * p.W : ℕ) : ℝ) ^ (1 - β) ≤ ((2 * p.W : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by rw [hdW]; linarith) (by linarith)
        _ = _ := Real.rpow_one _
    rw [e1, Real.rpow_one]
    have : 4 * δ * ((2 * p.W : ℕ) : ℝ) ^ (1 - β) ≤ 4 * (1 / 2) * (2 * W) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hδ (by norm_num)) e2 (by positivity) (by norm_num)
    linarith
  unfold smallIndex
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_mul]
  have hEs' : (Es.card : ℝ) ≤ W ^ (2 * (A₀ + 1) + 7) := hEs
  have hp : (T + 1) * W ^ (2 : ℝ) * (W ^ (2 * (A₀ + 1) + 7) *
      ((2 * T ^ 2 + 4) * W ^ (6 + A₀ + |H|) * (6 * W ^ (1 : ℝ)))) =
      6 * (T + 1) * (2 * T ^ 2 + 4) * W ^ (3 * A₀ + 18 + |H|) := by
    have e : W ^ (2 : ℝ) * (W ^ (2 * (A₀ + 1) + 7) * (W ^ (6 + A₀ + |H|) * W ^ (1 : ℝ))) =
        W ^ (3 * A₀ + 18 + |H|) := by
      rw [key, key, key]; ring_nf
    calc _ = 6 * (T + 1) * (2 * T ^ 2 + 4) *
          (W ^ (2 : ℝ) * (W ^ (2 * (A₀ + 1) + 7) * (W ^ (6 + A₀ + |H|) * W ^ (1 : ℝ)))) := by ring
      _ = _ := by rw [e]
  rw [← hp]
  refine mul_le_mul hlab (mul_le_mul hEs' (mul_le_mul hρ hμ (Nat.cast_nonneg _) (by positivity))
    (by positivity) (by positivity)) (by positivity) (by positivity)

end BlockBand.LocalWindow.ProofPartTwo
