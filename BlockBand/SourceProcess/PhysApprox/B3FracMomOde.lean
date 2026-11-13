module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A sharp discrete comparison for `x'^q ≤ x^q - a x^{q+1} + K`

The `q`-th moment recursion of the fractional trace reads, in the variable `x = (E P^q)^{1/q}`,
`x_{m+1}^q ≤ x_m^q - a x_m^{q+1} + K` (`a = c/W`, `K = K'/W`). The comparison ODE
`ẋ = -(a/q)x²` gives `x_m ≲ q/(am)`; the discrete version is exact enough to keep the forcing
at `K` (not `K^{1/q}`):

* `ode_poly_key`: `θ^q(1 - (q/N)θ) ≤ 1 - q/N` for `0 ≤ θ ≤ 1`, `N ≥ q + 1`;
* `pow_add_ge`: `M^q + K ≤ (M + K)^q` for `M ≥ 1`, `K ≥ 0`;
* `ode_step`: one step of the invariant `x ≤ max(M + K, 2q/(aN))`;
* **`ode_iter`**: if `x_0 ≤ max(M + K, 2q/(aN₀))` with `N₀ ≥ q + 1`, `M ≥ 1`, `2K ≤ aM^{q+1}`,
  then `x_m ≤ max(M + K, 2q/(a(N₀ + m)))` for all `m ≤ n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

/-- `θ^q(1 - (q/N)θ) ≤ 1 - q/N` for `0 ≤ θ ≤ 1`, `N ≥ q + 1`. -/
theorem ode_poly_key (q : ℕ) {θ N : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hN : (q : ℝ) + 1 ≤ N) :
    θ ^ q * (1 - q / N * θ) ≤ 1 - q / N := by
  have hNp : 0 < N := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  set r := (q : ℝ) / N with hr
  have hr0 : 0 ≤ r := by positivity
  have hrq : r * ((q : ℝ) + 1) ≤ q := by
    rw [hr, div_mul_eq_mul_div, div_le_iff₀ hNp]
    exact mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg q)
  set S := ∑ i ∈ Finset.range q, θ ^ i with hS
  have hgs : S * (θ - 1) = θ ^ q - 1 := geom_sum_mul θ q
  have hSq : (q : ℝ) * θ ^ q ≤ S := by
    have : ∑ _i ∈ Finset.range q, θ ^ q ≤ S :=
      Finset.sum_le_sum fun i hi => pow_le_pow_of_le_one h0 h1 (Finset.mem_range.1 hi).le
    simpa using this
  have hθq : 0 ≤ θ ^ q := pow_nonneg h0 q
  have hr1 : r ≤ 1 := by nlinarith
  have hinner : 0 ≤ S * (1 - r) - r * θ ^ q := by nlinarith
  have hprod : 0 ≤ (1 - θ) * (S * (1 - r) - r * θ ^ q) := mul_nonneg (by linarith) hinner
  have e : 1 - r - θ ^ q * (1 - r * θ) = (1 - θ) * (S * (1 - r) - r * θ ^ q) := by
    linear_combination (1 - r) * hgs
  linarith

/-- `M^q + K ≤ (M + K)^q` for `M ≥ 1`, `K ≥ 0`, `q ≥ 1`. -/
theorem pow_add_ge {q : ℕ} (hq : 1 ≤ q) {M K : ℝ} (hM : 1 ≤ M) (hK : 0 ≤ K) :
    M ^ q + K ≤ (M + K) ^ q := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hMn : 0 ≤ M ^ n := pow_nonneg (by linarith) n
    rw [pow_succ, pow_succ]
    nlinarith [mul_nonneg hMn hK, mul_nonneg hK hK]

/-- One step of the invariant `x ≤ max(M + K, 2q/(aN))`. -/
theorem ode_step {q : ℕ} (hq : 1 ≤ q) {a K M x x' N : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hM : 1 ≤ M) (hMK : 2 * K ≤ a * M ^ (q + 1)) (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hrec : x' ^ q ≤ x ^ q - a * x ^ (q + 1) + K) (hN : (q : ℝ) + 1 ≤ N)
    (hxb : x ≤ max (M + K) (2 * q / (a * N))) :
    x' ≤ max (M + K) (2 * q / (a * (N + 1))) := by
  have hq0 : q ≠ 0 := by omega
  have hNp : 0 < N := by have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith
  have hMK0 : 0 ≤ M + K := by linarith
  have hfin : ∀ y : ℝ, 0 ≤ y → x' ^ q ≤ y ^ q → x' ≤ y := fun y hy h =>
    (pow_le_pow_iff_left₀ hx' hy hq0).1 h
  have hxq1 : 0 ≤ x ^ (q + 1) := pow_nonneg hx _
  by_cases hxM : x < M
  · refine le_max_of_le_left (hfin _ hMK0 ?_)
    have h1 : x ^ q ≤ M ^ q := pow_le_pow_left₀ hx hxM.le q
    have h2 := pow_add_ge hq hM hK
    nlinarith [mul_nonneg ha.le hxq1]
  push Not at hxM
  have hMq : M ^ (q + 1) ≤ x ^ (q + 1) := pow_le_pow_left₀ (by linarith) hxM _
  have hhalf : x' ^ q ≤ x ^ q - a / 2 * x ^ (q + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hMq ha.le]
  by_cases hxK : x ≤ M + K
  · refine le_max_of_le_left (hfin _ hMK0 ?_)
    have h1 : x ^ q ≤ (M + K) ^ q := pow_le_pow_left₀ hx hxK q
    nlinarith [mul_nonneg ha.le hxq1]
  push Not at hxK
  have hxβ : x ≤ 2 * q / (a * N) := by
    rcases le_max_iff.1 hxb with h | h
    · linarith
    · exact h
  set β := 2 * (q : ℝ) / (a * N) with hβ
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hβ0 : 0 < β := by positivity
  set θ := x / β with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hx hβ0.le
  have hθ1 : θ ≤ 1 := (div_le_one hβ0).2 hxβ
  have hxθ : x = θ * β := by rw [hθ]; field_simp
  have haβ : a / 2 * β = q / N := by rw [hβ]; field_simp
  have hkey := ode_poly_key q hθ0 hθ1 hN
  have hβq : 0 ≤ β ^ q := pow_nonneg hβ0.le q
  have hstep1 : x ^ q - a / 2 * x ^ (q + 1) ≤ β ^ q * (1 - q / N) := by
    have e : x ^ q - a / 2 * x ^ (q + 1) = β ^ q * (θ ^ q * (1 - q / N * θ)) := by
      rw [hxθ, ← haβ, mul_pow, pow_succ, mul_pow]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hkey hβq
  -- Bernoulli: `(N/(N+1))^q ≥ 1 - q/(N+1) ≥ 1 - q/N`
  have hBer : 1 - (q : ℝ) / N ≤ (N / (N + 1)) ^ q := by
    have hb := one_add_mul_le_pow (a := -(1 / (N + 1))) (by
      have : 0 ≤ 1 / (N + 1) := by positivity
      have : 1 / (N + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith) q
    have e : 1 + -(1 / (N + 1)) = N / (N + 1) := by field_simp; ring
    rw [e] at hb
    have : (q : ℝ) / (N + 1) ≤ q / N :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg q) hNp (by linarith)
    have e2 : 1 + (q : ℝ) * -(1 / (N + 1)) = 1 - q / (N + 1) := by ring
    rw [e2] at hb
    linarith
  have hβ' : 2 * (q : ℝ) / (a * (N + 1)) = β * (N / (N + 1)) := by
    rw [hβ]; field_simp
  refine le_max_of_le_right (hfin _ (by positivity) ?_)
  rw [hβ', mul_pow]
  calc x' ^ q ≤ β ^ q * (1 - q / N) := hhalf.trans hstep1
    _ ≤ β ^ q * (N / (N + 1)) ^ q := mul_le_mul_of_nonneg_left hBer hβq

/-- **The iterated comparison.** -/
theorem ode_iter {q : ℕ} (hq : 1 ≤ q) {a K M N₀ : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hM : 1 ≤ M)
    (hMK : 2 * K ≤ a * M ^ (q + 1)) (hN₀ : (q : ℝ) + 1 ≤ N₀) (x : ℕ → ℝ) (hx : ∀ m, 0 ≤ x m)
    (n : ℕ) (hrec : ∀ m, m < n → x (m + 1) ^ q ≤ x m ^ q - a * x m ^ (q + 1) + K)
    (h0 : x 0 ≤ max (M + K) (2 * q / (a * N₀))) :
    ∀ m, m ≤ n → x m ≤ max (M + K) (2 * q / (a * (N₀ + m))) := by
  intro m
  induction m with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hN : (q : ℝ) + 1 ≤ N₀ + k := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have := ode_step hq ha hK hM hMK (hx k) (hx (k + 1)) (hrec k (by omega)) hN hprev
    push_cast
    rwa [show N₀ + ((k : ℝ) + 1) = N₀ + k + 1 by ring]

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
