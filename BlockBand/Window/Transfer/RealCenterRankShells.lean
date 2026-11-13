module

public import BlockBand.Window.Transfer.ScalarKernel

/-!
# Rank shells about a real centre

One-based ranks `α = i+1` about an arbitrary real center (here `N F_sc(E)`); unit
shells hold at most two ranks; the finite capped rank sum is bounded by twice the shell series.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open scoped BigOperators

namespace BlockBand.Window.Transfer

variable {N : ℕ}

/-- The one-based rank `α = i + 1`, as a real number. -/
def rankCoordinate (i : Fin N) : ℝ := (i.val : ℝ) + 1

/-- Unit absolute-distance shell about an arbitrary real center. -/
noncomputable def rankShell (center : ℝ) (i : Fin N) : ℕ :=
  Nat.floor |rankCoordinate i - center|

/-- The two sides of the real center distinguish at most two integer ranks
in a unit shell; the center itself belongs to the right side. -/
noncomputable def rankSide (center : ℝ) (i : Fin N) : Bool := by
  classical
  exact decide (center ≤ rankCoordinate i)

/-- Distinct integer ranks are at distance at least one. -/
theorem rank_eq_of_coordinate_distance_lt_one (i j : Fin N)
    (h : |rankCoordinate i - rankCoordinate j| < 1) : i = j := by
  have hijR : (i.val : ℝ) < (j.val : ℝ) + 1 := by
    have hh := (abs_lt.mp h).2
    unfold rankCoordinate at hh
    linarith
  have hjiR : (j.val : ℝ) < (i.val : ℝ) + 1 := by
    have hh := (abs_lt.mp h).1
    unfold rankCoordinate at hh
    linarith
  have hij : i.val < j.val + 1 := by exact_mod_cast hijR
  have hji : j.val < i.val + 1 := by exact_mod_cast hjiR
  apply Fin.ext
  omega

/-- Within one unit absolute-distance shell and on one side of the real centre there is at most
one integer rank. -/
theorem rank_shell_same_side_eq (center : ℝ) (m : ℕ) (i j : Fin N)
    (hi : rankShell center i = m) (hj : rankShell center j = m)
    (hside : rankSide center i = rankSide center j) : i = j := by
  classical
  have hilo : (m : ℝ) ≤ |rankCoordinate i - center| := by
    rw [← hi]
    exact Nat.floor_le (abs_nonneg (rankCoordinate i - center))
  have hihi : |rankCoordinate i - center| < (m : ℝ) + 1 := by
    rw [← hi]
    exact Nat.lt_floor_add_one |rankCoordinate i - center|
  have hjlo : (m : ℝ) ≤ |rankCoordinate j - center| := by
    rw [← hj]
    exact Nat.floor_le (abs_nonneg (rankCoordinate j - center))
  have hjhi : |rankCoordinate j - center| < (m : ℝ) + 1 := by
    rw [← hj]
    exact Nat.lt_floor_add_one |rankCoordinate j - center|
  apply rank_eq_of_coordinate_distance_lt_one
  unfold rankSide at hside
  by_cases hci : center ≤ rankCoordinate i
  · have hcj : center ≤ rankCoordinate j := by
      by_contra hcj
      simp [hci, hcj] at hside
    rw [abs_of_nonneg (sub_nonneg.mpr hci)] at hilo hihi
    rw [abs_of_nonneg (sub_nonneg.mpr hcj)] at hjlo hjhi
    apply abs_lt.mpr
    constructor <;> linarith
  · have hcj : ¬ center ≤ rankCoordinate j := by
      intro hcj
      simp [hci, hcj] at hside
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hci))] at hilo hihi
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hcj))] at hjlo hjhi
    apply abs_lt.mpr
    constructor <;> linarith

/-- Shell multiplicity: at most two one-based ranks per unit absolute rank-distance shell,
uniformly in `N`, the real centre and the finite rank set. -/
theorem rank_shell_card_le_two (s : Finset (Fin N)) (center : ℝ) (m : ℕ) :
    (s.filter (fun i => rankShell center i = m)).card ≤ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (rankSide center)
    (s := s.filter (fun i => rankShell center i = m)) (t := Finset.univ)
    (by intro i hi; exact Finset.mem_univ _)
    (by
      intro i hi j hj hside
      exact rank_shell_same_side_eq center m i j
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hside)
  simpa only [Finset.card_univ, Fintype.card_bool] using h

/-- A finite rank sum is bounded by twice the shell series. -/
theorem sum_rank_shell_weights_le (s : Finset (Fin N)) (center : ℝ)
    (v : ℕ → ℝ) (hv0 : ∀ m, 0 ≤ v m) (hvs : Summable v) :
    (∑ i ∈ s, v (rankShell center i)) ≤ 2 * ∑' m : ℕ, v m := by
  classical
  let shells := s.image (rankShell center)
  have hgroup : (∑ m ∈ shells, ∑ i ∈ s with rankShell center i = m, v m) =
      ∑ i ∈ s, v (rankShell center i) :=
    Finset.sum_fiberwise_of_maps_to' (by
      intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩) v
  calc
    _ = ∑ m ∈ shells, ((s.filter (fun i => rankShell center i = m)).card : ℝ) * v m := by
      rw [← hgroup]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ shells, 2 * v m := Finset.sum_le_sum fun m hm =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast rank_shell_card_le_two s center m) (hv0 m)
    _ = 2 * ∑ m ∈ shells, v m := (Finset.mul_sum shells v 2).symm
    _ ≤ 2 * ∑' m : ℕ, v m := mul_le_mul_of_nonneg_left
      (hvs.sum_le_tsum shells (fun m hm => hv0 m)) (by norm_num)

/-- The finite rank tail about a real centre, with the Hölder power `ε^{1-1/q}` and a factor two
from the shell multiplicity. -/
theorem actual_rank_tail_sum_bound (s : Finset (Fin N)) (center q a epsilon C : ℝ)
    (hq : 1 < q) (ha : 1 ≤ a) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hC : 0 ≤ C) :
    (∑ i ∈ s, min epsilon (C * (a / (1 + |rankCoordinate i - center|)) ^ q)) ≤
      2 * (((2 : ℝ) ^ q * C ^ (1 / q) / (q - 1)) * a * epsilon ^ (1 - 1 / q)) := by
  have hseries := rank_tail_series_bound q a epsilon C hq ha hepsilon hepsilon1 hC
  have hq0 : 0 ≤ q := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hterm (i : Fin N) :
      min epsilon (C * (a / (1 + |rankCoordinate i - center|)) ^ q) ≤
        min epsilon (C * (a / (1 + (rankShell center i : ℝ))) ^ q) := by
    apply min_le_min_left
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow (by positivity) _ hq0
    apply div_le_div_of_nonneg_left ha0 (by positivity)
    simpa only [rankShell, add_comm] using
      add_le_add_left (Nat.floor_le (abs_nonneg (rankCoordinate i - center))) 1
  calc
    _ ≤ ∑ i ∈ s, min epsilon (C * (a / (1 + (rankShell center i : ℝ))) ^ q) :=
      Finset.sum_le_sum fun i hi => hterm i
    _ ≤ 2 * ∑' m : ℕ, min epsilon (C * (a / (1 + (m : ℝ))) ^ q) :=
      sum_rank_shell_weights_le s center _ (fun m => by positivity) hseries.1
    _ ≤ _ := mul_le_mul_of_nonneg_left hseries.2 (by norm_num)

/-- At small rank distance `m ≤ R`, the cap `ε` is the minimum: `min(ε, C (a/(1+m))^q) = ε` when
`a ≥ 1` and `(1+R)^q ≤ C`. -/
theorem small_distance_capped_term_eq (q a epsilon C R m : ℝ) (hq : 0 < q)
    (ha : 1 ≤ a) (hepsilon1 : epsilon ≤ 1) (hR : 0 ≤ R) (hm : 0 ≤ m)
    (hmR : m ≤ R) (hC : (1 + R) ^ q ≤ C) :
    min epsilon (C * (a / (1 + m)) ^ q) = epsilon := by
  have hratio : 1 ≤ (1 + R) * (a / (1 + m)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < 1 + m)).mpr
    nlinarith
  have hpow : 1 ≤ (1 + R) ^ q * (a / (1 + m)) ^ q := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.one_le_rpow hratio hq.le
  exact min_eq_left (hepsilon1.trans (hpow.trans
    (mul_le_mul_of_nonneg_right hC (by positivity))))

/-- For `m ≥ 1`, `(a/m)^q ≤ 2^q (a/(1+m))^q`. -/
theorem large_distance_denominator_pay (q a m : ℝ) (hq : 0 < q) (ha : 0 ≤ a)
    (hm : 1 ≤ m) :
    (a / m) ^ q ≤ (2 : ℝ) ^ q * (a / (1 + m)) ^ q := by
  have hm0 : 0 < m := by linarith
  have hratio : a / m ≤ 2 * (a / (1 + m)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hm0 (by positivity : 0 < 1 + m)).mpr
    nlinarith
  have hp := Real.rpow_le_rpow (div_nonneg ha hm0.le) hratio hq.le
  rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)] at hp

end BlockBand.Window.Transfer
