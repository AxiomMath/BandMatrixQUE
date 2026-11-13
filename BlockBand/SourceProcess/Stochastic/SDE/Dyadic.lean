module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Dyadic samplings of a horizon `[0,T]`

Deterministic time grids used to pass from discrete to continuous-time martingale estimates.
`dyadicTime T n k = T · min(k, 2ⁿ) / 2ⁿ` is monotone in `k`, stays in `[0,T]`, equals `T` for
`k ≥ 2ⁿ`, and the grids are nested (`dyadicTime T (n+1) (2k) = dyadicTime T n k`). For every
`t ≤ T` the upper grid points `dyadicTime T n ⌈t 2ⁿ / T⌉₊` decrease to `t` within
`[t, t + T/2ⁿ]`, so they converge to `t` from the right (`tendsto_dyadicUpper`).
No measure is involved.
-/

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.SDE
open Filter Topology
open scoped NNReal

/-- The level-`n` dyadic sampling of `[0,T]`, saturated at `T`. -/
def dyadicTime (T : ℝ≥0) (n k : ℕ) : ℝ≥0 := T * ((min k (2 ^ n) : ℕ) : ℝ≥0) / 2 ^ n

theorem dyadicTime_monotone (T : ℝ≥0) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro k k' hk
  unfold dyadicTime
  gcongr

theorem dyadicTime_le (T : ℝ≥0) (n k : ℕ) : dyadicTime T n k ≤ T := by
  unfold dyadicTime
  rw [div_le_iff₀ (by positivity)]
  gcongr
  exact_mod_cast min_le_right k (2 ^ n)

theorem dyadicTime_of_le (T : ℝ≥0) (n : ℕ) {k : ℕ} (hk : 2 ^ n ≤ k) : dyadicTime T n k = T := by
  unfold dyadicTime
  rw [min_eq_right hk, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_right₀ _ (by positivity)]

theorem dyadicTime_succ (T : ℝ≥0) (n k : ℕ) : dyadicTime T (n + 1) (2 * k) = dyadicTime T n k := by
  unfold dyadicTime
  have h : min (2 * k) (2 ^ (n + 1)) = 2 * min k (2 ^ n) := by
    rw [pow_succ']
    generalize 2 ^ n = m
    omega
  rw [h, pow_succ']
  push_cast
  field_simp

/-- The index of the first level-`n` grid point at or after `t`. -/
def dyadicCeil (T t : ℝ≥0) (n : ℕ) : ℕ := ⌈t * 2 ^ n / T⌉₊

theorem dyadicCeil_le {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) : dyadicCeil T t n ≤ 2 ^ n := by
  unfold dyadicCeil
  rw [Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat]
  rcases eq_or_ne T 0 with hT | hT
  · simp [hT]
  · rw [div_le_iff₀ (pos_of_ne_zero hT), mul_comm]
    gcongr

/-- The upper level-`n` dyadic approximation of `t`. -/
def dyadicUpper (T t : ℝ≥0) (n : ℕ) : ℝ≥0 := dyadicTime T n (dyadicCeil T t n)

theorem dyadicUpper_eq {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) :
    dyadicUpper T t n = T * (dyadicCeil T t n : ℝ≥0) / 2 ^ n := by
  unfold dyadicUpper dyadicTime
  rw [min_eq_left (dyadicCeil_le ht n)]

theorem le_dyadicUpper {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) : t ≤ dyadicUpper T t n := by
  rw [dyadicUpper_eq ht]
  rcases eq_or_ne T 0 with hT | hT
  · subst hT; simp [nonpos_iff_eq_zero.1 ht]
  · rw [le_div_iff₀ (by positivity)]
    have h1 : t * 2 ^ n / T ≤ (dyadicCeil T t n : ℝ≥0) := Nat.le_ceil _
    calc t * 2 ^ n = T * (t * 2 ^ n / T) := by field_simp
      _ ≤ T * (dyadicCeil T t n : ℝ≥0) := by gcongr

theorem dyadicUpper_le {T t : ℝ≥0} (ht : t ≤ T) (n : ℕ) :
    dyadicUpper T t n ≤ t + T / 2 ^ n := by
  rw [dyadicUpper_eq ht]
  rcases eq_or_ne T 0 with hT | hT
  · simp [hT]
  · have h1 : (dyadicCeil T t n : ℝ≥0) < t * 2 ^ n / T + 1 := Nat.ceil_lt_add_one zero_le
    rw [div_le_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    calc T * (dyadicCeil T t n : ℝ≥0) ≤ T * (t * 2 ^ n / T + 1) := by gcongr
      _ = t * 2 ^ n + T := by field_simp

/-- The upper dyadic approximations converge to `t` from the right. -/
theorem tendsto_dyadicUpper {T t : ℝ≥0} (ht : t ≤ T) :
    Tendsto (dyadicUpper T t) atTop (𝓝[≥] t) := by
  have h0 : Tendsto (fun n : ℕ => t + T / 2 ^ n) atTop (𝓝 t) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (zero_le : (0 : ℝ≥0) ≤ 2⁻¹)
      (by norm_num)).const_mul T
    rw [mul_zero] at h
    simpa [div_eq_mul_inv, inv_pow] using tendsto_const_nhds.add h
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => le_dyadicUpper ht n⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (le_dyadicUpper ht) (dyadicUpper_le ht)

end BlockBand.SourceProcess.Stochastic.SDE
