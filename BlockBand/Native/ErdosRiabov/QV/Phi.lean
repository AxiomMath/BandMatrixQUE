module

public import BlockBand.Native.ErdosRiabov.QV.APriori

/-!
# Quadratic variation: the control parameters `φ^{qv}` and exponent facts

The quadratic-variation control parameters (following Erdős–Riabov), as functions of `L = ℓη > 0`
and the thresholds `psiI = ψ`, `psiA = ψ^av`:
* `qvPhiAv psiI psiA k L` (`φ^{av,qv}_k`), `qvPhiTilde psiI psiA k L` (`φ̃^{iso,qv}_k`) and
  `qvPhiIso psiI psiA k L` (`φ^{iso,qv}_k`, its sum over `j ∈ [2, ⌊(k+1)/2⌋]`);
* `qvPhiAv_anti`, `qvPhiTilde_anti`, `qvPhiIso_anti`: they are antitone in `L > 0` for
  `ψ ≥ 0` (every `L`-exponent is `≤ 0`), so `s ↦ φ(L_s)` is nondecreasing;
* exponent facts: `α_k ∈ [0, 1/2]`, monotone, the values `α₄ = 0`, `α₅ = 1/4`, `α₈ = 1/2`,
  `β₈ = 3/4`, and the concavity `2α_k - α_{k-1} - α_{k+1} ≥ 0` for `k = 5, 6, 7`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.Native.ErdosRiabov.Flow
open Expo (lossAlpha lossBeta)

/-!
## Exponent facts
-/

theorem qv_alpha_of_le_four {k : ℕ} (hk : k ≤ 4) : lossAlpha k = 0 := by
  simp [lossAlpha, hk]

theorem qv_alpha_nonneg (k : ℕ) : 0 ≤ lossAlpha k := by
  unfold lossAlpha
  split_ifs
  · exact le_rfl
  · positivity

theorem qv_alpha_le_half {k : ℕ} (hk : k ≤ 8) : lossAlpha k ≤ 1 / 2 := by
  unfold lossAlpha
  split_ifs
  · norm_num
  · have h1 : (2 * (k : ℝ) / 8 - 1) ≤ 1 := by
      have : (k : ℝ) ≤ 8 := by exact_mod_cast hk
      linarith
    have h2 : Real.sqrt (2 * (k : ℝ) / 8 - 1) ≤ 1 :=
      (Real.sqrt_le_sqrt h1).trans_eq Real.sqrt_one
    linarith

theorem qv_alpha_mono {j k : ℕ} (hjk : j ≤ k) : lossAlpha j ≤ lossAlpha k := by
  unfold lossAlpha
  split_ifs with h1 h2 h2
  · exact le_rfl
  · positivity
  · omega
  · have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    gcongr

private theorem qv_sqrt_sq_eq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (x ^ 2) = x := Real.sqrt_sq hx

theorem qv_alpha_five : lossAlpha 5 = 1 / 4 := by
  have h : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, qv_sqrt_sq_eq (by norm_num)]
  simp only [lossAlpha]
  norm_num [h]

theorem qv_alpha_eight : lossAlpha 8 = 1 / 2 := by
  simp only [lossAlpha]
  norm_num

theorem qv_beta_eight : lossBeta 8 = 3 / 4 := by
  simp only [lossBeta]
  norm_num [qv_alpha_five]

theorem qv_beta_eq_alpha {k : ℕ} (hk : k ≤ 7) : lossBeta k = lossAlpha (k + 1) := by
  simp [lossBeta, hk]

theorem qv_beta_le_one {k : ℕ} (hk : k ≤ 8) : lossBeta k ≤ 1 := by
  rcases Nat.lt_or_ge k 8 with h | h
  · rw [qv_beta_eq_alpha (by omega)]
    linarith [qv_alpha_le_half (k := k + 1) (by omega)]
  · rw [show k = 8 by omega, qv_beta_eight]
    norm_num

theorem qv_beta_nonneg (k : ℕ) : 0 ≤ lossBeta k := by
  unfold lossBeta
  split_ifs
  · exact qv_alpha_nonneg _
  · linarith [qv_alpha_nonneg 5]

/-- `2β₈ = 1 + 2α₅`. -/
theorem qv_two_beta_eight : 2 * lossBeta 8 = 1 + 2 * lossAlpha 5 := by
  rw [qv_beta_eight, qv_alpha_five]
  norm_num

private theorem qv_alpha_six : lossAlpha 6 = Real.sqrt (1 / 2) / 2 := by
  simp only [lossAlpha]
  norm_num

private theorem qv_alpha_seven : lossAlpha 7 = Real.sqrt (3 / 4) / 2 := by
  simp only [lossAlpha]
  norm_num

/-- Concavity `2α_k - α_{k-1} - α_{k+1} ≥ 0` for `k = 5, 6, 7` (values `0.146, 0.024, 0.012`). -/
theorem qv_alpha_concave {k : ℕ} (hk5 : 5 ≤ k) (hk7 : k ≤ 7) :
    0 ≤ 2 * lossAlpha k - lossAlpha (k - 1) - lossAlpha (k + 1) := by
  have ha1 : 7 / 10 ≤ Real.sqrt (1 / 2) := by
    rw [← qv_sqrt_sq_eq (show (0 : ℝ) ≤ 7 / 10 by norm_num)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have ha2 : Real.sqrt (1 / 2) ≤ 71 / 100 := by
    rw [← qv_sqrt_sq_eq (show (0 : ℝ) ≤ 71 / 100 by norm_num)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hb1 : 86 / 100 ≤ Real.sqrt (3 / 4) := by
    rw [← qv_sqrt_sq_eq (show (0 : ℝ) ≤ 86 / 100 by norm_num)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hb2 : Real.sqrt (3 / 4) ≤ 87 / 100 := by
    rw [← qv_sqrt_sq_eq (show (0 : ℝ) ≤ 87 / 100 by norm_num)]
    exact Real.sqrt_le_sqrt (by norm_num)
  rcases (show k = 5 ∨ k = 6 ∨ k = 7 by omega) with h | h | h <;> subst h
  · rw [show (5 : ℕ) - 1 = 4 from rfl, qv_alpha_of_le_four le_rfl, qv_alpha_five,
      show (5 : ℕ) + 1 = 6 from rfl, qv_alpha_six]
    nlinarith
  · rw [show (6 : ℕ) - 1 = 5 from rfl, qv_alpha_five, qv_alpha_six,
      show (6 : ℕ) + 1 = 7 from rfl, qv_alpha_seven]
    nlinarith
  · rw [show (7 : ℕ) - 1 = 6 from rfl, qv_alpha_six, qv_alpha_seven,
      show (7 : ℕ) + 1 = 8 from rfl, qv_alpha_eight]
    nlinarith

/-!
## The control parameters
-/

/-- `φ^{av,qv}_k(L)`. -/
def qvPhiAv (psiI psiA : ℕ → ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  if k ≤ 3 then Real.sqrt (1 + psiI (2 * k + 2) * L ^ (-(1 / 2 - lossAlpha (2 * k + 2))))
  else if k ≤ 7 then psiI (k + 1)
  else psiI 5 * Real.sqrt (1 + psiA 8 * L ^ (-(1 - lossBeta 8)))

/-- `φ̃^{iso,qv}_k(L)`. -/
def qvPhiTilde (psiI psiA : ℕ → ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  if k ≤ 4 then Real.sqrt (1 + psiI (2 * k) * L ^ (-(1 / 2 - lossAlpha (2 * k))))
  else if k ≤ 7 then Real.sqrt (psiI (k - 1) * psiI (k + 1) *
    L ^ (-(2 * lossAlpha k - lossAlpha (k - 1) - lossAlpha (k + 1))))
  else psiI 4 * Real.sqrt (1 + psiA 8 * L ^ (-(1 - lossBeta 8)))

/-- The `j`-th middle term of `φ^{iso,qv}_k(L)`. -/
def qvPhiMid (psiI : ℕ → ℝ) (k j : ℕ) (L : ℝ) : ℝ :=
  psiI (k - j + 1) * L ^ (-(lossAlpha k - lossAlpha (k - j + 1))) *
    Real.sqrt (1 + psiI (2 * j) * L ^ (-(1 / 2 - lossAlpha (2 * j))))

/-- `φ^{iso,qv}_k(L)`. -/
def qvPhiIso (psiI psiA : ℕ → ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  psiI k * Real.sqrt (psiI 2) * L ^ (-(1 / 4 : ℝ)) +
    ∑ j ∈ Finset.Icc 2 ((k + 1) / 2), qvPhiMid psiI k j L + qvPhiTilde psiI psiA k L

section Anti

variable {psiI psiA : ℕ → ℝ} (hI : ∀ j, 0 ≤ psiI j) (hA : ∀ j, 0 ≤ psiA j)
  {L L' : ℝ} (hL' : 0 < L') (hLL : L' ≤ L)

include hL' hLL in
private theorem qv_rpow_anti {g : ℝ} (hg : 0 ≤ g) : L ^ (-g) ≤ L' ^ (-g) :=
  Real.rpow_le_rpow_of_nonpos hL' hLL (by linarith)

include hI hL' hLL in
private theorem qv_sqrt_one_anti {p : ℕ} {g : ℝ} (hg : 0 ≤ g) :
    Real.sqrt (1 + psiI p * L ^ (-g)) ≤ Real.sqrt (1 + psiI p * L' ^ (-g)) :=
  Real.sqrt_le_sqrt (by nlinarith [qv_rpow_anti hL' hLL hg, hI p])

include hI hA hL' hLL in
theorem qvPhiAv_anti {k : ℕ} : qvPhiAv psiI psiA k L ≤ qvPhiAv psiI psiA k L' := by
  unfold qvPhiAv
  split_ifs with h1 h2
  · exact qv_sqrt_one_anti hI hL' hLL (by linarith [qv_alpha_le_half (k := 2 * k + 2) (by omega)])
  · exact le_rfl
  · have hb : 0 ≤ 1 - lossBeta 8 := by linarith [qv_beta_le_one (k := 8) le_rfl]
    have hr := qv_rpow_anti hL' hLL hb
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hI 5)
    nlinarith [hA 8]

include hI hA hL' hLL in
theorem qvPhiTilde_anti {k : ℕ} (hk : k ≤ 8) :
    qvPhiTilde psiI psiA k L ≤ qvPhiTilde psiI psiA k L' := by
  unfold qvPhiTilde
  split_ifs with h1 h2
  · exact qv_sqrt_one_anti hI hL' hLL (by linarith [qv_alpha_le_half (k := 2 * k) (by omega)])
  · refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (qv_rpow_anti hL' hLL ?_)
      (mul_nonneg (hI _) (hI _)))
    exact qv_alpha_concave (by omega) h2
  · have hb : 0 ≤ 1 - lossBeta 8 := by linarith [qv_beta_le_one (k := 8) le_rfl]
    have hr := qv_rpow_anti hL' hLL hb
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (hI 4)
    nlinarith [hA 8]

include hI hL' hLL in
theorem qvPhiMid_anti {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hj : 2 * j ≤ 8) :
    qvPhiMid psiI k j L ≤ qvPhiMid psiI k j L' := by
  unfold qvPhiMid
  have h1 := qv_rpow_anti hL' hLL (g := lossAlpha k - lossAlpha (k - j + 1))
    (by linarith [qv_alpha_mono (j := k - j + 1) (k := k) (by omega)])
  have h2 := qv_sqrt_one_anti hI hL' hLL (p := 2 * j) (g := 1 / 2 - lossAlpha (2 * j))
    (by linarith [qv_alpha_le_half hj])
  have h0 : 0 ≤ L ^ (-(lossAlpha k - lossAlpha (k - j + 1))) :=
    Real.rpow_nonneg (hL'.le.trans hLL) _
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (hI _)) h2 (Real.sqrt_nonneg _)
    (mul_nonneg (hI _) (Real.rpow_nonneg hL'.le _))

include hI hA hL' hLL in
theorem qvPhiIso_anti {k : ℕ} (hk : k ≤ 8) :
    qvPhiIso psiI psiA k L ≤ qvPhiIso psiI psiA k L' := by
  unfold qvPhiIso
  refine add_le_add (add_le_add ?_ ?_) (qvPhiTilde_anti hI hA hL' hLL hk)
  · exact mul_le_mul_of_nonneg_left (qv_rpow_anti hL' hLL (by norm_num))
      (mul_nonneg (hI k) (Real.sqrt_nonneg _))
  · refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hjk : j ≤ k := le_trans hj2 (Nat.div_le_of_le_mul (by omega))
    have hj8 : 2 * j ≤ 8 := by
      have := Nat.mul_le_mul_left 2 hj2
      have h2 := Nat.mul_div_le (k + 1) 2
      omega
    exact qvPhiMid_anti hI hL' hLL (by omega) hjk hj8

end Anti

end BlockBand.Native.ErdosRiabov.QV
