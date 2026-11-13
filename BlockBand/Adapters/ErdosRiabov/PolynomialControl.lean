module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs

/-!
# Elementary facts for the polynomial control

Properties of the localization length `ℓ(η) = min(N, W/√η)`, of the cyclic distance on
`Fin N`, and the summation bound `Σ_a (1 + d(x,a)/L)^{-2} ≤ 2(1 + L)` on the `N`-cycle.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

/-!
## Localization length
-/

/-- `ℓ(η) > 0` for `N, W, η > 0`. -/
theorem loc_pos {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {η : ℝ} (hη : 0 < η) :
    0 < ErdosRiabov.localizationLength N W η := by
  unfold ErdosRiabov.localizationLength
  exact lt_min (div_pos (by exact_mod_cast hW) (Real.sqrt_pos.2 hη)) (by exact_mod_cast hN)

theorem loc_le_N (N W : ℕ) (η : ℝ) : ErdosRiabov.localizationLength N W η ≤ N :=
  min_le_right _ _

/-- `ℓ` is antitone in the height. -/
theorem loc_antitone (N W : ℕ) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) :
    ErdosRiabov.localizationLength N W η₂ ≤ ErdosRiabov.localizationLength N W η₁ := by
  unfold ErdosRiabov.localizationLength
  apply min_le_min_right
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.sqrt_pos.2 h₁)
  exact Real.sqrt_le_sqrt h

/-- `ℓ(η) η = min (W √η) (N η)`. -/
theorem loc_mul_eq (N W : ℕ) {η : ℝ} (hη : 0 < η) :
    ErdosRiabov.localizationLength N W η * η = min ((W : ℝ) * Real.sqrt η) ((N : ℝ) * η) := by
  unfold ErdosRiabov.localizationLength
  rw [min_mul_of_nonneg _ _ hη.le]
  congr 1
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have : η = Real.sqrt η * Real.sqrt η := (Real.mul_self_sqrt hη.le).symm
  field_simp
  nlinarith [this]

/-- ER (2.17): `ℓη` is monotone in the height. -/
theorem loc_mul_mono (N W : ℕ) {η₁ η₂ : ℝ} (h₁ : 0 < η₁) (h : η₁ ≤ η₂) :
    ErdosRiabov.localizationLength N W η₁ * η₁ ≤ ErdosRiabov.localizationLength N W η₂ * η₂ := by
  rw [loc_mul_eq N W h₁, loc_mul_eq N W (h₁.trans_le h)]
  apply min_le_min
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Nat.cast_nonneg _)
  · exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

/-- `W ≤ √C₀ ℓ(η)` for `0 < η ≤ C₀`, `C₀ ≥ 1`, `W ≤ N`. -/
theorem W_le_sqrt_mul_loc {N W : ℕ} (hWN : W ≤ N) {C₀ η : ℝ} (hC₀ : 1 ≤ C₀) (hη : 0 < η)
    (hηC : η ≤ C₀) :
    (W : ℝ) ≤ Real.sqrt C₀ * ErdosRiabov.localizationLength N W η := by
  unfold ErdosRiabov.localizationLength
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hsC : Real.sqrt η ≤ Real.sqrt C₀ := Real.sqrt_le_sqrt hηC
  have h1C : 1 ≤ Real.sqrt C₀ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hC₀
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  rcases min_cases ((W : ℝ) / Real.sqrt η) (N : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · rw [mul_div_assoc', le_div_iff₀ hs]
    rw [mul_comm (Real.sqrt C₀)]
    exact mul_le_mul_of_nonneg_left hsC hW0
  · have : (W : ℝ) ≤ N := by exact_mod_cast hWN
    nlinarith

/-- `ℓ(η) ≥ 1/√C₀` for `0 < η ≤ C₀`, `N, W ≥ 1`, `C₀ ≥ 1`. -/
theorem inv_sqrt_le_loc {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {C₀ η : ℝ} (hC₀ : 1 ≤ C₀)
    (hη : 0 < η) (hηC : η ≤ C₀) :
    1 / Real.sqrt C₀ ≤ ErdosRiabov.localizationLength N W η := by
  unfold ErdosRiabov.localizationLength
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hsC : Real.sqrt η ≤ Real.sqrt C₀ := Real.sqrt_le_sqrt hηC
  have h1C : 1 ≤ Real.sqrt C₀ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hC₀
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply le_min
  · rw [div_le_div_iff₀ (by linarith) hs]
    nlinarith
  · rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- At height one the localization length is the bandwidth (`W ≤ N`). -/
theorem loc_one {N W : ℕ} (hWN : W ≤ N) : ErdosRiabov.localizationLength N W 1 = W := by
  unfold ErdosRiabov.localizationLength
  rw [Real.sqrt_one, div_one]
  exact min_eq_left (by exact_mod_cast hWN)

/-- Below `(W/N)²` the localization length is the full dimension. -/
theorem loc_eq_N {N W : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η)
    (hsmall : η ≤ ((W : ℝ) / (N : ℝ)) ^ 2) :
    ErdosRiabov.localizationLength N W η = N := by
  unfold ErdosRiabov.localizationLength
  apply min_eq_right
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hle : Real.sqrt η ≤ (W : ℝ) / N := by
    rw [show (W : ℝ) / N = Real.sqrt (((W : ℝ) / N) ^ 2) by
      rw [Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) hNr.le)]]
    exact Real.sqrt_le_sqrt hsmall
  rw [le_div_iff₀ hs]
  rw [le_div_iff₀ hNr] at hle
  linarith

/-!
## Cyclic distance
-/

theorem cyclicDistance_self (N : ℕ) (x : Fin N) : ErdosRiabov.cyclicDistance N x x = 0 := by
  simp [ErdosRiabov.cyclicDistance]

theorem cyclicDistance_triangle (N : ℕ) (x y z : Fin N) :
    ErdosRiabov.cyclicDistance N x z ≤
      ErdosRiabov.cyclicDistance N x y + ErdosRiabov.cyclicDistance N y z := by
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  simp only [ErdosRiabov.cyclicDistance]
  omega

theorem two_mul_cyclicDistance_le (N : ℕ) (x y : Fin N) :
    2 * ErdosRiabov.cyclicDistance N x y ≤ N := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [ErdosRiabov.cyclicDistance]
  omega

/-- The distance from `x` to `j + x` (addition in `Fin N`) is `min j (N - j)`. -/
theorem cyclicDistance_add_right {N : ℕ} [NeZero N] (x j : Fin N) :
    ErdosRiabov.cyclicDistance N x (j + x) = min j.val (N - j.val) := by
  have hx := x.isLt
  have hj := j.isLt
  have hval : (j + x).val = (j.val + x.val) % N := Fin.val_add j x
  simp only [ErdosRiabov.cyclicDistance]
  rcases lt_or_ge (j.val + x.val) N with h | h
  · rw [hval, Nat.mod_eq_of_lt h]
    omega
  · have : (j.val + x.val) % N = j.val + x.val - N := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hval, this]
    omega

/-!
## The summation bound
-/

/-- Telescoping: `Σ_{j ≤ n} (1 + j/L)^{-2} ≤ 1 + L - L/(1 + n/L)`. -/
theorem sum_range_inv_sq_le (L : ℝ) (hL : 0 < L) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ((1 + (j : ℝ) / L) ^ 2)⁻¹ ≤ 1 + L - L / (1 + (n : ℝ) / L) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hu : 0 < 1 + (n : ℝ) / L := by positivity
    have hv : 0 < 1 + ((n + 1 : ℕ) : ℝ) / L := by positivity
    have key : ((1 + ((n + 1 : ℕ) : ℝ) / L) ^ 2)⁻¹ ≤
        L / (1 + (n : ℝ) / L) - L / (1 + ((n + 1 : ℕ) : ℝ) / L) := by
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hv ⊢
      rw [div_sub_div _ _ hu.ne' hv.ne', inv_eq_one_div, div_le_div_iff₀ (by positivity)
        (mul_pos hu hv)]
      have e1 : L * (1 + ((n : ℝ) + 1) / L) - (1 + (n : ℝ) / L) * L = 1 := by
        field_simp; ring
      rw [e1]
      nlinarith [mul_pos hu hv]
    linarith

theorem sum_range_inv_sq_le' (L : ℝ) (hL : 0 < L) (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 + (j : ℝ) / L) ^ 2)⁻¹ ≤ 1 + L := by
  rcases n with _ | n
  · simp; linarith
  · refine (sum_range_inv_sq_le L hL n).trans ?_
    have : 0 ≤ L / (1 + (n : ℝ) / L) := by positivity
    linarith

/-- Summation bound, squared form: `Σ_a (1 + d(x,a)/L)^{-2} ≤ 2(1+L)` on the `N`-cycle. -/
theorem sum_inv_sq_le {N : ℕ} (L : ℝ) (hL : 0 < L) (x : Fin N) :
    ∑ a : Fin N, ((1 + (ErdosRiabov.cyclicDistance N x a : ℝ) / L) ^ 2)⁻¹ ≤ 2 * (1 + L) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact x.elim0
  have : NeZero N := ⟨hN.ne'⟩
  set f : ℕ → ℝ := fun k => ((1 + (k : ℝ) / L) ^ 2)⁻¹ with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  rw [← Equiv.sum_comp (Equiv.addRight x)]
  have hpt : ∀ j : Fin N, f (ErdosRiabov.cyclicDistance N x (j + x)) ≤ f j.val + f (N - j.val) := by
    intro j
    rw [cyclicDistance_add_right]
    rcases min_choice j.val (N - j.val) with h | h <;> rw [h]
    · linarith [hf0 (N - j.val)]
    · linarith [hf0 j.val]
  calc ∑ j : Fin N, ((1 + (ErdosRiabov.cyclicDistance N x ((Equiv.addRight x) j) : ℝ) / L) ^ 2)⁻¹
        = ∑ j : Fin N, f (ErdosRiabov.cyclicDistance N x (j + x)) := rfl
    _ ≤ ∑ j : Fin N, (f j.val + f (N - j.val)) := Finset.sum_le_sum fun j _ => hpt j
    _ = ∑ j ∈ Finset.range N, f j + ∑ j ∈ Finset.range N, f (N - j) := by
      rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range f N,
        Fin.sum_univ_eq_sum_range (fun j => f (N - j)) N]
    _ ≤ (1 + L) + (1 + L) := by
      apply add_le_add (sum_range_inv_sq_le' L hL N)
      have hre : ∑ j ∈ Finset.range N, f (N - j) = ∑ j ∈ Finset.range N, f (j + 1) := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        congr 1
        omega
      rw [hre]
      calc ∑ j ∈ Finset.range N, f (j + 1) ≤ ∑ j ∈ Finset.range (N + 1), f j := by
            rw [Finset.sum_range_succ']
            linarith [hf0 0]
        _ ≤ 1 + L := sum_range_inv_sq_le' L hL (N + 1)
    _ = 2 * (1 + L) := by ring

end BlockBand.Adapters.ErdosRiabov
