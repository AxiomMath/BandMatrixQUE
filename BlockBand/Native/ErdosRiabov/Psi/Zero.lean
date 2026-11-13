module

public import BlockBand.Native.ErdosRiabov.Psi.Defs

/-!
# `Ψ_0 = 0` at `H_0 = 0`

Deterministic; no law.

**Conditional.** The M-term side uses `Split.ZeroStatement` (`M^{(0)}_{[1,k]} =
(∏ m_i) ∏ A_p`). It is an explicit hypothesis of every theorem here.

At `t = 0`, `z_{j,0} ∈ {-1/m, -1/m̄}` (`Flow.vsFlow_d`), so at `H = 0` every resolvent slot is
`(0 - z_{j,0})⁻¹ = m_j · 1` and the chain is `(∏ m_j) S^{x_1} ⋯ S^{x_{k-1}}` (diagonal). Hence
`𝒴^k_0 = 0` and `𝒳^k_0 = 0` for every pattern and all sites (`isoErr_zero`, `avErr_zero`), and
`Ψ^iso_{k,0}(0) = Ψ^av_{k,0}(0) = 0` for `k ≥ 1` (`bigPsiIso_zero`, `bigPsiAv_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Psi

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open Matrix
open scoped ComplexConjugate NNReal

variable {N k : ℕ}

theorem inv_smul_one {c : ℂ} (hc : c ≠ 0) :
    (c • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = c⁻¹ • 1 := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_mul, one_smul]

theorem ofFn_smul_prod :
    ∀ {k : ℕ} (c : Fin k → ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ),
      (List.ofFn fun l => c l • B l).prod = (∏ l, c l) • (List.ofFn B).prod
  | 0, _, _ => by simp
  | k + 1, c, B => by
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ofFn_smul_prod (fun l => c l.succ) (fun l => B l.succ), smul_mul_smul_comm]

theorem ofFn_diagonal_prod :
    ∀ {k : ℕ} (v : Fin k → Fin N → ℂ),
      (List.ofFn fun l => diagonal (v l)).prod = diagonal fun a => ∏ l, v l a
  | 0, _ => by simp [diagonal_one]
  | k + 1, v => by
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ofFn_diagonal_prod (fun l => v l.succ), diagonal_mul_diagonal]

theorem prod_Ico_one_succ {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ p ∈ Finset.Ico 1 (n + 1), f p = ∏ j : Fin n, f (j.val + 1) := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range]
  simp only [add_comm]

theorem prod_Icc_patM (z : ℂ) (σ : Fin k → Bool) :
    ∏ i ∈ Finset.Icc 1 k, patM z σ i = ∏ j : Fin k, VS.patConj (σ j) (semicircleM z) := by
  have hI : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, prod_Ico_one_succ]
  exact Finset.prod_congr rfl fun j _ => patM_of_mem z σ j

/-- At `t = 0` and `H = 0` every resolvent slot is `m_j · 1` (`Im z ≠ 0`). -/
theorem resolvent_zero {z : ℂ} (σ : Fin k → Bool) (j : Fin k) :
    ((0 : Matrix (Fin N) (Fin N) ℂ) - patZ z σ 0 j • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      VS.patConj (σ j) (semicircleM z) • 1 := by
  have hm0 : semicircleM z ≠ 0 := ne_zero_of_root (semicircleM_dyson z)
  have h0 : vsTraj z 0 = -1 / semicircleM z := by
    rw [eq_div_iff hm0]
    simp only [vsTraj, Complex.ofReal_zero, sub_zero, one_mul]
    linear_combination semicircleM_dyson z
  rw [zero_sub, ← neg_smul]
  unfold patZ
  rw [h0]
  have hw : -VS.patConj (σ j) (-1 / semicircleM z) ≠ 0 := by
    cases σ j <;> simp [VS.patConj, hm0]
  rw [inv_smul_one hw]
  congr 1
  cases σ j <;> simp [VS.patConj, map_div₀] <;> ring

theorem gChain_zero_zero (z : ℂ) (σ : Fin k → Bool) (B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    gChain (patZ z σ 0) B 0 =
      (∏ j : Fin k, VS.patConj (σ j) (semicircleM z)) • (List.ofFn B).prod := by
  unfold gChain Chains.slotProd Chains.slotList
  simp_rw [resolvent_zero, smul_mul_assoc, one_mul]
  exact ofFn_smul_prod _ _

theorem isoSlots_eq (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) (j : Fin k) :
    isoSlots S x j = diagonal fun a => if j.val + 1 < k then (S (x j) a : ℂ) else 1 := by
  unfold isoSlots obsMat Split.rowObs
  split_ifs <;> simp [diagonal_one]

theorem gChain_iso_zero (z : ℂ) (σ : Fin k → Bool) (S : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin k → Fin N) :
    gChain (patZ z σ 0) (isoSlots S x) 0 =
      (∏ j : Fin k, VS.patConj (σ j) (semicircleM z)) •
        diagonal fun a => ∏ j : Fin k, if j.val + 1 < k then (S (x j) a : ℂ) else 1 := by
  rw [gChain_zero_zero]
  congr 1
  rw [show isoSlots S x = fun j => diagonal fun a =>
      if j.val + 1 < k then (S (x j) a : ℂ) else 1 from funext (isoSlots_eq S x)]
  exact ofFn_diagonal_prod _

namespace PsiData

variable (P : PsiData N)

/-- **`𝒴^k_0(H = 0) = 0`** (conditional on `Split.ZeroStatement`; `k ≥ 1`). -/
theorem isoErr_zero (hZ : Split.ZeroStatement) (hk : 1 ≤ k) (σ : Fin k → Bool) (a b : Fin N)
    (x : Fin k → Fin N) : P.isoErr σ a b x 0 0 = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold isoErr mChain
  rw [hZ N P.S (patM P.z σ) (obsSeq P.S x) (k' + 1) hk, prod_Icc_patM, gChain_iso_zero,
    prod_Ico_one_succ, Matrix.smul_apply, diagonal_apply]
  simp only [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
  have hobs : ∀ j : Fin k', obsSeq P.S x (j.val + 1) = Split.rowObs P.S (x j.castSucc) := by
    intro j
    unfold obsSeq
    rw [dite_eq_left (by omega)]
    rfl
  simp_rw [hobs]
  split_ifs with hab
  · subst hab
    rw [Fin.prod_univ_castSucc (fun j : Fin (k' + 1) =>
      if (j : ℕ) + 1 < k' + 1 then (P.S (x j) a : ℂ) else 1)]
    simp [Split.rowObs]
  · simp

/-- **`𝒳^k_0(H = 0) = 0`** (conditional on `Split.ZeroStatement`; `k ≥ 1`). -/
theorem avErr_zero (hZ : Split.ZeroStatement) (hk : 1 ≤ k) (σ : Fin k → Bool)
    (x : Fin k → Fin N) : P.avErr σ x 0 0 = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold avErr mChain
  rw [hZ N P.S (patM P.z σ) (obsSeq P.S x) (k' + 1) hk, prod_Icc_patM, gChain_zero_zero]
  have hav : (List.ofFn (avSlots P.S x)).prod = diagonal fun a => ∏ j, (P.S (x j) a : ℂ) := by
    unfold avSlots obsMat Split.rowObs
    exact ofFn_diagonal_prod _
  rw [hav, prod_Ico_one_succ]
  have hobs : ∀ j : Fin k', obsSeq P.S x (j.val + 1) = Split.rowObs P.S (x j.castSucc) := by
    intro j
    unfold obsSeq
    rw [dite_eq_left (by omega)]
    rfl
  have hlast : obsSeq P.S x (k' + 1) = Split.rowObs P.S (x (Fin.last k')) := by
    unfold obsSeq
    rw [dite_eq_left (by omega)]
    rfl
  simp_rw [hobs, hlast]
  rw [trace_smul, trace_diagonal, Finset.smul_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.smul_apply, Finset.prod_apply, smul_eq_mul, Split.rowObs]
  rw [Fin.prod_univ_castSucc (fun j => (P.S (x j) a : ℂ))]
  ring

/-- **`Ψ^iso_{k,0}(0) = 0`** for `k ≥ 1` (conditional on `Split.ZeroStatement`). -/
theorem bigPsiIso_zero (hZ : Split.ZeroStatement) (hk : 1 ≤ k) : P.bigPsiIso k 0 0 = 0 := by
  unfold bigPsiIso isoRatio
  simp [P.isoErr_zero hZ hk]

/-- **`Ψ^av_{k,0}(0) = 0`** for `k ≥ 1` (conditional on `Split.ZeroStatement`). -/
theorem bigPsiAv_zero (hZ : Split.ZeroStatement) (hk : 1 ≤ k) : P.bigPsiAv k 0 0 = 0 := by
  unfold bigPsiAv avRatio
  simp [P.avErr_zero hZ hk]

end PsiData

end BlockBand.Native.ErdosRiabov.Psi
