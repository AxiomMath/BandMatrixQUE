module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Matrix
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Euler scheme on a path

Deterministic setting: coefficients `c : LipCoef d` (bounded, globally Lipschitz in the sup norm
of `ℝ^d`, entrywise), dyadic grid `t_j = j 2^{-m}`, an initial point `x` and a path
`w : ℝ≥0 → ℝ^d` (no regularity).

* `eulerE c m x w j`: the grid values, `E_0 = x`,
  `E_{j+1} = E_j + 2^{-m} b(E_j) + σ(E_j)(w(t_{j+1}) - w(t_j))`.
* `eulerX c m x w t = E_j + (t - t_j) b(E_j) + σ(E_j)(w(t) - w(t_j))`, `j = ⌈t 2^m⌉ - 1`
  (`eulerX_of_mem`: the formula on `(t_j, t_{j+1}]`; `eulerX_gridT`: `X(t_j) = E_j`).
* **`eulerX_eq_sum`**: telescoping, for `t ≤ t_J`, `X(t) = x + ∑_{j<J} inc_j(t)` with
  `inc_j(t) = (t_{j+1}∧t - t_j∧t) b(E_j) + σ(E_j)(w(t_{j+1}∧t) - w(t_j∧t))`.
* `eulerE_congr`, `eulerX_congr`: the scheme only reads `w` at grid points and at `t`.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open Matrix Set
open scoped NNReal

variable {d : ℕ}

/-- Bounded globally Lipschitz coefficients (sup norm on `ℝ^d`, entrywise bounds). -/
structure LipCoef (d : ℕ) where
  b : (Fin d → ℝ) → Fin d → ℝ
  σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ
  L : ℝ
  M : ℝ
  L_nonneg : 0 ≤ L
  M_nonneg : 0 ≤ M
  lip_b : ∀ x y i, |b x i - b y i| ≤ L * ‖x - y‖
  lip_σ : ∀ x y i k, |σ x i k - σ y i k| ≤ L * ‖x - y‖
  bd_b : ∀ x i, |b x i| ≤ M
  bd_σ : ∀ x i k, |σ x i k| ≤ M

namespace LipCoef

variable (c : LipCoef d)

theorem continuous_of_lip {f : (Fin d → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) : Continuous f :=
  (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) fun x y => by
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]; exact hf x y).continuous

theorem continuous_b : Continuous c.b :=
  continuous_pi fun i => continuous_of_lip c.L_nonneg fun x y => c.lip_b x y i

theorem continuous_σ : Continuous c.σ :=
  continuous_pi fun i => continuous_pi fun k =>
    continuous_of_lip c.L_nonneg fun x y => c.lip_σ x y i k

end LipCoef

/-- The dyadic grid `t_j = j 2^{-m}`. -/
def gridT (m j : ℕ) : ℝ≥0 := j / 2 ^ m

/-- The index `j` with `t ∈ (t_j, t_{j+1}]` (`0` at `t = 0`). -/
def gridIdx (m : ℕ) (t : ℝ≥0) : ℕ := ⌈t * 2 ^ m⌉₊ - 1

theorem gridT_zero (m : ℕ) : gridT m 0 = 0 := by simp [gridT]

theorem gridT_mul (m j : ℕ) : gridT m j * 2 ^ m = j := by
  rw [gridT, div_mul_cancel₀ _ (by positivity)]

theorem coe_gridT (m j : ℕ) : (gridT m j : ℝ) = j / 2 ^ m := by simp [gridT]

theorem gridT_mono (m : ℕ) : Monotone (gridT m) := fun i j hij => by
  unfold gridT; gcongr

theorem gridT_succ_sub (m j : ℕ) : (gridT m (j + 1) : ℝ) - gridT m j = 1 / 2 ^ m := by
  rw [coe_gridT, coe_gridT]; push_cast; ring

theorem gridIdx_eq_of_mem {m j : ℕ} {t : ℝ≥0} (h1 : gridT m j < t) (h2 : t ≤ gridT m (j + 1)) :
    gridIdx m t = j := by
  have hpos : (0 : ℝ≥0) < 2 ^ m := by positivity
  have e : ⌈t * 2 ^ m⌉₊ = j + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero j)]
    constructor
    · have := mul_lt_mul_of_pos_right h1 hpos
      rw [Nat.succ_sub_one]; rwa [gridT_mul] at this
    · have := mul_le_mul_of_nonneg_right h2 hpos.le
      rwa [gridT_mul] at this
  simp [gridIdx, e]

theorem gridIdx_zero (m : ℕ) : gridIdx m 0 = 0 := by simp [gridIdx]

theorem gridT_idx_lt {m : ℕ} {t : ℝ≥0} (ht : 0 < t) : gridT m (gridIdx m t) < t := by
  have hpos : (0 : ℝ≥0) < 2 ^ m := by positivity
  have hc : 1 ≤ ⌈t * 2 ^ m⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  rw [← mul_lt_mul_iff_of_pos_right hpos, gridT_mul, gridIdx]
  have h3 := Nat.ceil_lt_add_one (zero_le : (0 : ℝ≥0) ≤ t * 2 ^ m)
  have h4 : ((⌈t * 2 ^ m⌉₊ - 1 : ℕ) : ℝ≥0) + 1 = ⌈t * 2 ^ m⌉₊ := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hc]
  rw [← h4] at h3
  exact lt_of_add_lt_add_right h3

theorem le_gridT_idx_succ (m : ℕ) (t : ℝ≥0) : t ≤ gridT m (gridIdx m t + 1) := by
  have hpos : (0 : ℝ≥0) < 2 ^ m := by positivity
  rw [← mul_le_mul_iff_of_pos_right hpos, gridT_mul, gridIdx]
  rcases Nat.eq_zero_or_pos ⌈t * 2 ^ m⌉₊ with h | h
  · rw [h, Nat.zero_sub, zero_add, Nat.cast_one]
    exact (Nat.ceil_eq_zero.1 h).trans zero_le_one
  · rw [Nat.sub_add_cancel h]; exact Nat.le_ceil _

section Scheme

variable (c : LipCoef d) (m : ℕ) (x : Fin d → ℝ) (w : ℝ≥0 → Fin d → ℝ)

/-- The grid values of the Euler scheme. -/
def eulerE : ℕ → Fin d → ℝ
  | 0 => x
  | j + 1 => eulerE j + (1 / 2 ^ m : ℝ) • c.b (eulerE j) +
      c.σ (eulerE j) *ᵥ (w (gridT m (j + 1)) - w (gridT m j))

/-- The interpolated Euler scheme. -/
def eulerX (t : ℝ≥0) : Fin d → ℝ :=
  eulerE c m x w (gridIdx m t) +
    ((t : ℝ) - gridT m (gridIdx m t)) • c.b (eulerE c m x w (gridIdx m t)) +
      c.σ (eulerE c m x w (gridIdx m t)) *ᵥ (w t - w (gridT m (gridIdx m t)))

/-- The `j`-th increment up to time `t`. -/
def eulerInc (j : ℕ) (t : ℝ≥0) : Fin d → ℝ :=
  (((min (gridT m (j + 1)) t : ℝ≥0) : ℝ) - ((min (gridT m j) t : ℝ≥0) : ℝ)) •
      c.b (eulerE c m x w j) +
    c.σ (eulerE c m x w j) *ᵥ (w (min (gridT m (j + 1)) t) - w (min (gridT m j) t))

theorem eulerX_of_mem {j : ℕ} {t : ℝ≥0} (h1 : gridT m j < t) (h2 : t ≤ gridT m (j + 1)) :
    eulerX c m x w t = eulerE c m x w j + ((t : ℝ) - gridT m j) • c.b (eulerE c m x w j) +
      c.σ (eulerE c m x w j) *ᵥ (w t - w (gridT m j)) := by
  rw [eulerX, gridIdx_eq_of_mem h1 h2]

theorem eulerX_zero : eulerX c m x w 0 = x := by
  simp [eulerX, gridIdx_zero, gridT_zero, eulerE]

theorem eulerX_gridT (j : ℕ) : eulerX c m x w (gridT m j) = eulerE c m x w j := by
  cases j with
  | zero => rw [gridT_zero, eulerX_zero]; rfl
  | succ j =>
    have h1 : gridT m j < gridT m (j + 1) := by unfold gridT; gcongr; exact Nat.lt_succ_self j
    rw [eulerX_of_mem c m x w h1 le_rfl, eulerE, gridT_succ_sub]

theorem eulerInc_of_le {j : ℕ} {t : ℝ≥0} (ht : t ≤ gridT m j) : eulerInc c m x w j t = 0 := by
  have h2 : t ≤ gridT m (j + 1) := ht.trans (gridT_mono m (Nat.le_succ j))
  rw [eulerInc, min_eq_right ht, min_eq_right h2]
  simp

theorem eulerInc_of_ge {j : ℕ} {t t' : ℝ≥0} (ht : gridT m (j + 1) ≤ t)
    (ht' : gridT m (j + 1) ≤ t') : eulerInc c m x w j t = eulerInc c m x w j t' := by
  have h1 : gridT m j ≤ gridT m (j + 1) := gridT_mono m (Nat.le_succ j)
  rw [eulerInc, eulerInc, min_eq_left ht, min_eq_left ht', min_eq_left (h1.trans ht),
    min_eq_left (h1.trans ht')]

/-- **Telescoping**: `X(t) = x + ∑_{j<J} inc_j(t)` for `t ≤ t_J`. -/
theorem eulerX_eq_sum (J : ℕ) {t : ℝ≥0} (ht : t ≤ gridT m J) :
    eulerX c m x w t = x + ∑ j ∈ Finset.range J, eulerInc c m x w j t := by
  induction J generalizing t with
  | zero =>
    rw [gridT_zero, nonpos_iff_eq_zero] at ht
    subst ht
    simp [eulerX_zero]
  | succ J ih =>
    rw [Finset.sum_range_succ]
    rcases le_or_gt t (gridT m J) with h | h
    · rw [ih h, eulerInc_of_le c m x w h, add_zero]
    · have hs : ∑ j ∈ Finset.range J, eulerInc c m x w j t =
          ∑ j ∈ Finset.range J, eulerInc c m x w j (gridT m J) :=
        Finset.sum_congr rfl fun j hj => eulerInc_of_ge c m x w
          ((gridT_mono m (Finset.mem_range.1 hj)).trans h.le) (gridT_mono m (Finset.mem_range.1 hj))
      rw [hs, ← add_assoc, ← ih le_rfl, eulerX_gridT, eulerX_of_mem c m x w h ht]
      rw [eulerInc, min_eq_right ht, min_eq_left h.le, add_assoc]

end Scheme

theorem eulerE_congr (c : LipCoef d) (m : ℕ) (x : Fin d → ℝ) {w w' : ℝ≥0 → Fin d → ℝ}
    (hw : ∀ j, w (gridT m j) = w' (gridT m j)) (j : ℕ) :
    eulerE c m x w j = eulerE c m x w' j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [eulerE, ih, hw]

theorem eulerX_congr (c : LipCoef d) (m : ℕ) (x : Fin d → ℝ) {w w' : ℝ≥0 → Fin d → ℝ}
    (hw : ∀ j, w (gridT m j) = w' (gridT m j)) {t : ℝ≥0} (ht : w t = w' t) :
    eulerX c m x w t = eulerX c m x w' t := by
  simp only [eulerX, eulerE_congr c m x hw, hw, ht]

end BlockBand.SourceProcess.Stochastic.Uniqueness
