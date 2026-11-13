module

public import BlockBand.Palm.MomentFlow.IndFinal
public import BlockBand.Palm.MomentFlow.MaxPath

/-!
# Scale bookkeeping for the induction step

The number of dyadic heights `stL N = ⌊log₂ N⌋/1000`, the identities for the scales `η`, `τ`,
`ℓ`, `w` of the induction (`cmEta`, `cmTau`, `cmEll`, `cmW`), and elementary eventual bounds on
powers of `N`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Filter Topology

/-- Number of dyadic heights. -/
def stL (N : ℕ) : ℕ := Nat.log 2 N / 1000

theorem rpow_le_rpow_exp {N : ℕ} (hN : 1 ≤ N) {p q : ℝ} (h : p ≤ q) :
    (N : ℝ) ^ p ≤ (N : ℝ) ^ q :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) h

theorem cmEta_eq {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) : cmEta N ε = (N : ℝ) ^ (-(ε + 1 / 100)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cmEta cmTau
  rw [← Real.rpow_add hNp]; congr 1; ring

theorem cmEta_pos {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) : 0 < cmEta N ε := by
  rw [cmEta_eq hN]; exact Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem cmEta_inv {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) : (cmEta N ε)⁻¹ = (N : ℝ) ^ (ε + 1 / 100) := by
  rw [cmEta_eq hN, Real.rpow_neg (by positivity), inv_inv]

theorem cmTau_div_cmEta {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) : cmTau N / cmEta N ε = (N : ℝ) ^ ε := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_eq_mul_inv, cmEta_inv hN, cmTau, ← Real.rpow_add hNp]; congr 1; ring

theorem N_mul_cmEta {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) :
    (N : ℝ) * cmEta N ε = (N : ℝ) ^ (1 - ε - 1 / 100) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [cmEta_eq hN]
  have e : (N : ℝ) * (N : ℝ) ^ (-(ε + 1 / 100)) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(ε + 1 / 100)) := by
    rw [Real.rpow_one]
  rw [e, ← Real.rpow_add hNp]; congr 1; ring

theorem cmEll_le {N : ℕ} : (cmEll N : ℝ) ≤ (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) :=
  Nat.floor_le (by positivity)

theorem cmEll_ge {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) / 2 ≤ cmEll N := by
  set x := (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)
  have hx : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have h1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  show x / 2 ≤ (⌊x⌋₊ : ℝ)
  linarith

theorem cmEll_pos {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < cmEll N := by
  have h := cmEll_ge hN
  have : 0 < (N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3) := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  linarith

theorem cmW_pos {N : ℕ} (hN : 1 ≤ N) : 0 < cmW N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem N_div_cmW {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) / cmW N = (N : ℝ) ^ (1 / 600 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := cmW_div (N := N) (by omega)
  have hw := cmW_pos hN
  have : (N : ℝ) / cmW N = (cmW N / N)⁻¹ := by field_simp
  rw [this, h, ← Real.rpow_neg hNp.le, neg_neg]

theorem two_pow_stL_le {N : ℕ} (hN : 1 ≤ N) : (2 : ℝ) ^ stL N ≤ (N : ℝ) ^ (1 / 1000 : ℝ) := by
  have h1 : 2 ^ (1000 * stL N) ≤ N := by
    have := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    exact (Nat.pow_le_pow_right (by norm_num) (by unfold stL; omega)).trans this
  have h2 : ((2 : ℝ) ^ stL N) ^ (1000 : ℝ) ≤ N := by
    rw [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul,
      mul_comm]
    exact_mod_cast h1
  rw [show (1 / 1000 : ℝ) = (1000 : ℝ)⁻¹ by norm_num]
  exact (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)).2 h2

theorem le_two_pow_stL {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 / 1000 : ℝ) ≤ 2 * (2 : ℝ) ^ stL N := by
  have h1 : N < 2 ^ (1000 * (stL N + 1)) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) N
    exact this.trans_le (Nat.pow_le_pow_right (by norm_num) (by unfold stL; omega))
  have h2 : (N : ℝ) ≤ ((2 : ℝ) ^ (stL N + 1)) ^ (1000 : ℝ) := by
    rw [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul,
      mul_comm]
    exact_mod_cast h1.le
  rw [show (1 / 1000 : ℝ) = (1000 : ℝ)⁻¹ by norm_num, ← pow_succ']
  exact (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by norm_num)).2 h2

theorem stL_succ_le (N : ℕ) : ((stL N : ℝ) + 1) ≤ (2 : ℝ) ^ stL N := by
  have := Nat.lt_two_pow_self (n := stL N)
  have h : stL N + 1 ≤ 2 ^ stL N := this
  exact_mod_cast h

/-- `K N^{-p} ≤ c` eventually (`p, c > 0`). -/
theorem ev_mul_rpow_neg_le (K : ℝ) {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, K * (N : ℝ) ^ (-p) ≤ c := by
  have h : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-p)) atTop (𝓝 (K * 0)) :=
    ((tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul K
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds hc)).mono fun N hN => hN.le

/-- `K ≤ N^p` eventually (`p > 0`). -/
theorem ev_le_rpow (K : ℝ) {p : ℝ} (hp : 0 < p) : ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ p :=
  ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop K)

end BlockBand.Palm.MomentFlow
