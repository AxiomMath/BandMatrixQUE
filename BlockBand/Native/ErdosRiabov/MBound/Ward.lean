module

public import BlockBand.Native.ErdosRiabov.MBound.Defs
public import BlockBand.Native.ErdosRiabov.MBound.Remainder

/-!
# Partial traces of the averaged `M`-term by the Ward identity

Partial traces of the averaged `M`-term over one site reduce to differences of shorter `M`-terms,
which gives the bounds on the reduced traces used for the remainder and the extra forcing.

For `X = Evol.avM P σ · t` (`Tr[M^{(t)}_{[1,k]}(x') S^{x_k}]`), 0-based sites:
* `mbAvM_ward_last` (last site):
  `Σ_c X(y[last ↦ c]) = (z_{k,t} - z_{1,t})⁻¹ (X^{σ_a}(y) - X^{σ_b}(y))`
  with `σ_a = (σ_{k-1}, σ_1, …, σ_{k-2})` (`update (Fin.init σ) 0 (σ (last))`) and
  `σ_b = Fin.init σ`, if `σ_{k-1} ≠ σ_0`;
* `mbAvM_ward_mid` (interior site): for a slot `j ≤ k-2`, `Σ_c X(y[j ↦ c]) =
  (z_{j+1,t} - z_{j+2,t})⁻¹ (X^{σ \ σ_{j+1}}(y) - X^{σ \ σ_j}(y))`, if `σ_j ≠ σ_{j+1}`;
* **`mbWard_bounds`**: for a saturated pattern of length `n+4`, `t ∈ [0,1]` and
  `AvB(n+3, A₃)`, `AvB(n+2, A₂)`: `|mbTrL X|, |mbTrM X| ≤ (A₃/η) L s^av_{n+3}` and
  `|mbTrLM X| ≤ (A₂/η²) L s^av_{n+2}`, i.e. the hypotheses of `mbRem_bound`, `mbFt_bound`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Propagator
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-!
## `Fin` index computations
-/

theorem mb_succAbove_val {m : ℕ} (j : Fin (m + 1)) (i : Fin m) :
    ((j.succAbove i : Fin (m + 1)) : ℕ) =
      (if (i : ℕ) < (j : ℕ) then (i : ℕ) else (i : ℕ) + 1) := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
    simp

theorem mb_insertNth_lt {m : ℕ} (j : Fin (m + 1)) (c : Fin N) (y : Fin m → Fin N) {q : ℕ}
    (hq : q < j) : Fin.insertNth (α := fun _ => Fin N) j c y ⟨q, by omega⟩ = y ⟨q, by omega⟩ := by
  have : (⟨q, by omega⟩ : Fin (m + 1)) = j.succAbove ⟨q, by omega⟩ := by
    apply Fin.ext
    rw [mb_succAbove_val, ite_eq_left (show (q : ℕ) < (j : ℕ) from hq)]
  rw [this, Fin.insertNth_apply_succAbove]

theorem mb_insertNth_gt {m : ℕ} (j : Fin (m + 1)) (c : Fin N) (y : Fin m → Fin N) {q : ℕ}
    (hq : (j : ℕ) < q) (hqm : q < m + 1) :
    Fin.insertNth (α := fun _ => Fin N) j c y ⟨q, hqm⟩ = y ⟨q - 1, by omega⟩ := by
  have : (⟨q, hqm⟩ : Fin (m + 1)) = j.succAbove ⟨q - 1, by omega⟩ := by
    apply Fin.ext
    rw [mb_succAbove_val, ite_eq_right (by simp only; omega)]
    simp only
    omega
  rw [this, Fin.insertNth_apply_succAbove]

theorem mb_removeNth_val {m : ℕ} {α : Type*} (j : Fin (m + 1)) (f : Fin (m + 1) → α) {q : ℕ}
    (hq : q < m) :
    Fin.removeNth j f ⟨q, hq⟩ = f ⟨if q < j then q else q + 1, by split_ifs <;> omega⟩ := by
  rw [Fin.removeNth_apply]
  congr 1
  exact Fin.ext (mb_succAbove_val j ⟨q, hq⟩)

theorem mb_patM_apply (z : ℂ) {k : ℕ} (σ : Fin k → Bool) {p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ k) :
    patM z σ p = VS.patConj (σ ⟨p - 1, by omega⟩) (semicircleM z) := by
  rw [patM, dite_eq_left ⟨h1, h2⟩]

theorem mb_patMExt_apply (z : ℂ) {k : ℕ} (σ : Fin k → Bool) {p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ k) :
    mbPatMExt z σ p = VS.patConj (σ ⟨p - 1, by omega⟩) (semicircleM z) := by
  rw [mbPatMExt_of_mem z σ h1 h2, mb_patM_apply z σ h1 h2]

theorem mb_obsSeq_apply (S : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (x : Fin k → Fin N) {p : ℕ}
    (h1 : 1 ≤ p) (h2 : p ≤ k) : obsSeq S x p = Split.rowObs S (x ⟨p - 1, by omega⟩) := by
  rw [obsSeq, dite_eq_left ⟨h1, h2⟩]

theorem mb_obsSeq_out (S : Matrix (Fin N) (Fin N) ℝ) {k : ℕ} (x : Fin k → Fin N) {p : ℕ}
    (h : k < p) : obsSeq S x p = fun _ => 1 := by
  rw [obsSeq, dite_eq_right (by omega)]

theorem mb_sum_rowObs {S : Matrix (Fin N) (Fin N) ℝ} (hS : Split.ProfileHyp S) :
    ∑ c, Split.rowObs S c = fun _ => 1 := by
  funext a
  simp only [Finset.sum_apply, Split.rowObs]
  rw [← Complex.ofReal_sum]
  have : ∑ c, S c a = 1 := by
    rw [← hS.rowSum a]
    exact Finset.sum_congr rfl fun c _ => hS.symm c a
  rw [this, Complex.ofReal_one]

/-- `Split.dropAt j (update A j B) = Split.dropAt j A`. -/
theorem mb_dropAt_update_self {α : Type*} (j : ℕ) (A : ℕ → α) (B : α) :
    Split.dropAt j (update A j B) = Split.dropAt j A := by
  funext i
  unfold Split.dropAt
  split_ifs with h
  · exact update_of_ne (by omega) _ _
  · exact update_of_ne (by omega) _ _

/-!
## Products and multilinearity at the `chainM` level
-/

theorem mb_prod_Icc_one {M : Type*} [CommMonoid M] (g : ℕ → M) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 k, g i = ∏ i ∈ Finset.range k, g (i + 1) := by
  induction k with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem mb_prod_rotateChain {M : Type*} [CommMonoid M] (m : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 (n + 2), Split.rotateChain (n + 2) m i =
      ∏ i ∈ Finset.Icc 1 (n + 2), m i := by
  rw [mb_prod_Icc_one, mb_prod_Icc_one]
  conv_lhs => rw [Finset.prod_range_succ']
  conv_rhs => rw [Finset.prod_range_succ]
  have h1 : Split.rotateChain (n + 2) m (0 + 1) = m (n + 2) := by
    simp [Split.rotateChain]
  have h2 : ∀ i ∈ Finset.range (n + 1), Split.rotateChain (n + 2) m (i + 1 + 1) = m (i + 1) := by
    intro i _
    simp [Split.rotateChain]
  rw [h1, Finset.prod_congr rfl h2, mul_comm]

theorem mb_chainM_sum_obs (t : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) (B : Fin N → Fin N → ℂ) {p k : ℕ} (hp1 : 1 ≤ p) (hpk : p < k) :
    ∑ c, Split.chainM t S m (update A p (B c)) 1 k =
      Split.chainM t S m (update A p (∑ c, B c)) 1 k := by
  simp only [Split.chainM]
  rw [← Finset.smul_sum, mb_chainTilde_sum_obs t S m A Finset.univ B p (k - 1) 1 k rfl hp1 hpk]

/-!
## The Split-level Ward reductions
-/

section Core

variable {S : Matrix (Fin N) (Fin N) ℝ} (hS : Split.ProfileHyp S) {t : ℝ}
  (ht : t ∈ Icc (0 : ℝ) 1) {m : ℕ → ℂ} (hm1 : ∀ i, ‖m i‖ < 1) (hm0 : ∀ i, m i ≠ 0)

include hS ht hm1 hm0 in
/-- Trace Ward (cyclicity + Ward at `j = 1` of the rotated chain): for `k = n+2`, `A_k = 1`,
`m_k ≠ m_1`: `Σ_a M_{[1,k]}(a) = (z_k - z_1)⁻¹ Σ_a A_{k-1}(a) (M^{(m_k,m_2..m_{k-1})}(a) -
M^{(m_1..m_{k-1})}(a))`, with the shifted observables `dropAt 1 (rotateChain k A)`. -/
theorem mb_ward_trace (hC : Split.CyclicStatement) (hW : Split.WardStatement) {n : ℕ}
    (A : ℕ → Fin N → ℂ) (hAk : A (n + 2) = fun _ => 1) (hmk : m (n + 2) ≠ m 1) :
    ∑ a, Split.chainM t S m A 1 (n + 2) a =
      (Split.zParam t (m (n + 2)) - Split.zParam t (m 1))⁻¹ *
        (∑ a, A (n + 1) a * Split.chainM t S (Split.dropAt 2 (Split.rotateChain (n + 2) m))
            (Split.dropAt 1 (Split.rotateChain (n + 2) A)) 1 (n + 1) a -
          ∑ a, A (n + 1) a * Split.chainM t S (Split.dropAt 1 (Split.rotateChain (n + 2) m))
            (Split.dropAt 1 (Split.rotateChain (n + 2) A)) 1 (n + 1) a) := by
  have hcyc := hC N S hS t ht m hm1 A (n + 2) (by omega)
  rw [hAk] at hcyc
  simp only [mul_one] at hcyc
  have hrot1 : ∀ i, ‖Split.rotateChain (n + 2) m i‖ < 1 := fun i => by
    unfold Split.rotateChain; split_ifs <;> exact hm1 _
  have hrot0 : ∀ i, Split.rotateChain (n + 2) m i ≠ 0 := fun i => by
    unfold Split.rotateChain; split_ifs <;> exact hm0 _
  have hRA : Split.rotateChain (n + 2) A 1 = fun _ => 1 := by
    simp [Split.rotateChain, hAk]
  have hr1 : Split.rotateChain (n + 2) m 1 = m (n + 2) := by simp [Split.rotateChain]
  have hr2 : Split.rotateChain (n + 2) m (1 + 1) = m 1 := by simp [Split.rotateChain]
  have hward := hW N S hS t ht (Split.rotateChain (n + 2) m) hrot1 hrot0
    (Split.rotateChain (n + 2) A) (n + 2) 1 (by omega) le_rfl (by omega) hRA
    (by rw [hr1, hr2]; exact hmk)
  rw [hr1, hr2, show n + 2 - 1 = n + 1 by omega] at hward
  -- the trace of `M` through cyclicity
  have htr : ∑ a, Split.chainM t S m A 1 (n + 2) a =
      ∑ a, A (n + 1) a * Split.chainM t S (Split.rotateChain (n + 2) m)
        (Split.rotateChain (n + 2) A) 1 (n + 2) a := by
    simp only [Split.chainM, Pi.smul_apply, smul_eq_mul, mb_prod_rotateChain]
    rw [← Finset.mul_sum, hcyc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [show n + 2 - 1 = n + 1 by omega]
    ring
  rw [htr, hward]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine congrArg₂ _ (Finset.sum_congr rfl fun a _ => by ring)
    (Finset.sum_congr rfl fun a _ => by ring)

end Core

/-!
## The averaged `M`-term
-/

section Pattern

/-- Conjugate pattern letters give different `m`'s (`Im m > 0`). -/
theorem mb_patConj_ne {z : ℂ} (hz : 0 < z.im) {b b' : Bool} (hb : b ≠ b') :
    VS.patConj b (semicircleM z) ≠ VS.patConj b' (semicircleM z) := by
  have him := semicircleM_im_pos hz
  have hne : semicircleM z ≠ conj (semicircleM z) := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  cases b <;> cases b' <;> simp only [ne_eq, not_true_eq_false] at hb <;>
    simp only [VS.patConj, Bool.false_eq_true, ite_false, ite_true]
  · exact hne
  · exact fun h => hne h.symm

variable (P : PsiData N) (hS : Split.ProfileHyp P.S) (hz : 0 < P.z.im) {t : ℝ}
  (ht : t ∈ Icc (0 : ℝ) 1)

/-- The cyclic pattern `σ_a = (σ_{k-1}, σ_1, …, σ_{k-2})` of the trace Ward. -/
def mbPatRot {n : ℕ} (σ : Fin (n + 2) → Bool) : Fin (n + 1) → Bool :=
  update (Fin.init σ) 0 (σ (Fin.last (n + 1)))

include hS hz ht in

/-- **Ward identity at the last slot** (under `Split.CyclicStatement` and
`Split.WardStatement`): for `σ : Fin (n+2) → Bool` with `σ_{n+1} ≠ σ_0` and sites `y`,
`Σ_c Tr[M^σ(y[last ↦ c])] = (z_{n+2,t} - z_{1,t})⁻¹ (Tr[M^{σ_a}(y)] - Tr[M^{init σ}(y)])`.
-/
theorem mbAvM_ward_last (hC : Split.CyclicStatement) (hW : Split.WardStatement) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (y : Fin (n + 1) → Fin N) :
    ∑ c, Evol.avM P σ (Fin.insertNth (Fin.last (n + 1)) c y) t =
      (Split.zParam t (VS.patConj (σ (Fin.last (n + 1))) (semicircleM P.z)) -
          Split.zParam t (VS.patConj (σ 0) (semicircleM P.z)))⁻¹ *
        (Evol.avM P (mbPatRot σ) y t - Evol.avM P (Fin.init σ) y t) := by
  set m := mbPatMExt P.z σ with hmdef
  have hm1 : ∀ i, ‖m i‖ < 1 := norm_mbPatMExt_lt_one hz.ne' σ
  have hm0 : ∀ i, m i ≠ 0 := mbPatMExt_ne_zero P.z σ
  -- the chain does not see the closing site
  have hch : ∀ c, P.mChain σ (Fin.insertNth (Fin.last (n + 1)) c y) t =
      Split.chainM t P.S m (obsSeq P.S y) 1 (n + 2) := by
    intro c
    rw [mb_mChain_eq_ext]
    refine Evol.chainM_congr t P.S _ fun p hp1 hp2 => ?_
    rw [mb_obsSeq_apply _ _ hp1 (by omega), mb_obsSeq_apply _ _ hp1 (by omega),
      mb_insertNth_lt _ _ _ (by simp; omega)]
  have hsum : ∑ c, Evol.avM P σ (Fin.insertNth (Fin.last (n + 1)) c y) t =
      ∑ a, Split.chainM t P.S m (obsSeq P.S y) 1 (n + 2) a := by
    simp only [Evol.avM, hch]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum]
    have hl : ∀ c, obsSeq P.S (Fin.insertNth (Fin.last (n + 1)) c y) (n + 2) =
        Split.rowObs P.S c := fun c => by
      rw [mb_obsSeq_apply _ _ (by omega) le_rfl]
      congr 1
      rw [show (⟨n + 2 - 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) from Fin.ext (by simp),
        Fin.insertNth_apply_same]
    simp only [hl]
    have := congrFun (mb_sum_rowObs hS) a
    simp only [Finset.sum_apply] at this
    rw [this, mul_one]
  rw [hsum, mb_ward_trace hS ht hm1 hm0 hC hW (obsSeq P.S y) (mb_obsSeq_out _ _ (by omega))]
  · have hmk : m (n + 2) = VS.patConj (σ (Fin.last (n + 1))) (semicircleM P.z) := by
      rw [hmdef, mb_patMExt_apply _ _ (by omega) le_rfl]
      congr 2
    have hm1' : m 1 = VS.patConj (σ 0) (semicircleM P.z) := by
      rw [hmdef, mb_patMExt_apply _ _ le_rfl (by omega)]
      rfl
    rw [hmk, hm1']
    congr 2
    · unfold Evol.avM
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm]
      congr 1
      unfold PsiData.mChain
      refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)) a
      · unfold Split.dropAt Split.rotateChain
        rw [mb_patM_apply _ _ hp1 hp2]
        by_cases hp : p < 2
        · have : p = 1 := by omega
          subst this
          simp only [hp, ite_true, ite_true]
          rw [hmk]
          congr 1
        · simp only [hp, ite_false, show p + 1 ≠ 1 by omega, ite_false,
            show p + 1 - 1 = p by omega]
          rw [hmdef, mb_patMExt_apply _ _ hp1 (by omega)]
          congr 1
          simp only [mbPatRot]
          rw [update_of_ne (by rw [Ne, Fin.ext_iff]; simp; omega)]
          rfl
      · unfold Split.dropAt Split.rotateChain
        rw [ite_eq_right (by omega), ite_eq_right (by omega), show p + 1 - 1 = p by omega]
    · unfold Evol.avM
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_comm]
      congr 1
      unfold PsiData.mChain
      refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)) a
      · unfold Split.dropAt Split.rotateChain
        rw [mb_patM_apply _ _ hp1 hp2, ite_eq_right (by omega), ite_eq_right (by omega),
          show p + 1 - 1 = p by omega, hmdef, mb_patMExt_apply _ _ hp1 (by omega)]
        rfl
      · unfold Split.dropAt Split.rotateChain
        rw [ite_eq_right (by omega), ite_eq_right (by omega), show p + 1 - 1 = p by omega]
  · rw [show m (n + 2) = VS.patConj (σ (Fin.last (n + 1))) (semicircleM P.z) by
      rw [hmdef, mb_patMExt_apply _ _ (by omega) le_rfl]; congr 2,
      show m 1 = VS.patConj (σ 0) (semicircleM P.z) by
      rw [hmdef, mb_patMExt_apply _ _ le_rfl (by omega)]; rfl]
    exact mb_patConj_ne hz hσ

include hS hz ht in

/-- **Ward identity at an interior slot** (under `Split.WardStatement`): for
`σ : Fin (n+2) → Bool`, a slot `j ≤ n` (`j.castSucc`) with `σ_j ≠ σ_{j+1}` and sites `y`,
`Σ_c Tr[M^σ(y[j ↦ c])] = (z_{j+1,t} - z_{j+2,t})⁻¹ (Tr[M^{σ \ σ_{j+1}}(y)] - Tr[M^{σ \ σ_j}(y)])`.
-/
theorem mbAvM_ward_mid (hW : Split.WardStatement) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (j : Fin (n + 1)) (hσ : σ j.castSucc ≠ σ j.succ) (y : Fin (n + 1) → Fin N) :
    ∑ c, Evol.avM P σ (Fin.insertNth j.castSucc c y) t =
      (Split.zParam t (VS.patConj (σ j.castSucc) (semicircleM P.z)) -
          Split.zParam t (VS.patConj (σ j.succ) (semicircleM P.z)))⁻¹ *
        (Evol.avM P (Fin.removeNth j.succ σ) y t -
          Evol.avM P (Fin.removeNth j.castSucc σ) y t) := by
  set m := mbPatMExt P.z σ with hmdef
  have hm1 : ∀ i, ‖m i‖ < 1 := norm_mbPatMExt_lt_one hz.ne' σ
  have hm0 : ∀ i, m i ≠ 0 := mbPatMExt_ne_zero P.z σ
  have hj := j.isLt
  set B : ℕ → Fin N → ℂ := fun p => if p < (j : ℕ) + 1 then obsSeq P.S y p
    else obsSeq P.S y (p - 1) with hBdef
  have hobs : ∀ c, P.mChain σ (Fin.insertNth j.castSucc c y) t =
      Split.chainM t P.S m (update B ((j : ℕ) + 1) (Split.rowObs P.S c)) 1 (n + 2) := by
    intro c
    rw [mb_mChain_eq_ext]
    refine Evol.chainM_congr t P.S _ fun p hp1 hp2 => ?_
    rw [mb_obsSeq_apply _ _ hp1 (by omega)]
    by_cases hpj : p = (j : ℕ) + 1
    · subst hpj
      rw [update_self]
      congr 1
      rw [show (⟨(j : ℕ) + 1 - 1, by omega⟩ : Fin (n + 2)) = j.castSucc from Fin.ext (by simp),
        Fin.insertNth_apply_same]
    · rw [update_of_ne hpj, hBdef]
      simp only
      by_cases hlt : p < (j : ℕ) + 1
      · rw [ite_eq_left hlt, mb_obsSeq_apply _ _ hp1 (by omega)]
        congr 1
        exact mb_insertNth_lt _ _ _ (by simp; omega)
      · rw [ite_eq_right hlt, mb_obsSeq_apply _ _ (by omega) (by omega)]
        congr 1
        rw [mb_insertNth_gt _ _ _ (by simp; omega)]
  have hclose : ∀ c, obsSeq P.S (Fin.insertNth j.castSucc c y) (n + 2) =
      obsSeq P.S y (n + 1) := by
    intro c
    rw [mb_obsSeq_apply _ _ (by omega) le_rfl, mb_obsSeq_apply _ _ (by omega) le_rfl]
    congr 1
    rw [mb_insertNth_gt _ _ _ (by simp; omega)]
    exact congrArg y (Fin.ext (by simp))
  have hsum : ∑ c, Evol.avM P σ (Fin.insertNth j.castSucc c y) t =
      ∑ a, Split.chainM t P.S m (update B ((j : ℕ) + 1) (fun _ => 1)) 1 (n + 2) a *
        obsSeq P.S y (n + 1) a := by
    simp only [Evol.avM, hobs, hclose]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    rw [← Finset.sum_apply, mb_chainM_sum_obs t P.S m B _ (by omega) (by omega),
      mb_sum_rowObs hS]
  have hmj : m ((j : ℕ) + 1) = VS.patConj (σ j.castSucc) (semicircleM P.z) := by
    rw [hmdef, mb_patMExt_apply _ _ (by omega) (by omega)]
    congr 2
  have hmj' : m ((j : ℕ) + 1 + 1) = VS.patConj (σ j.succ) (semicircleM P.z) := by
    rw [hmdef, mb_patMExt_apply _ _ (by omega) (by omega)]
    congr 2
  have hward := hW N P.S hS t ht m hm1 hm0 (update B ((j : ℕ) + 1) (fun _ => 1)) (n + 2)
    ((j : ℕ) + 1) (by omega) (by omega) (by omega) (update_self _ _ _)
    (by rw [hmj, hmj']; exact mb_patConj_ne hz hσ)
  rw [hsum, hward, hmj, hmj', mb_dropAt_update_self, show n + 2 - 1 = n + 1 by omega]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, sub_mul, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum]
  have hdB : ∀ p, 1 ≤ p → p < n + 1 → Split.dropAt ((j : ℕ) + 1) B p = obsSeq P.S y p := by
    intro p hp1 hp2
    unfold Split.dropAt
    rw [hBdef]
    by_cases hlt : p < (j : ℕ) + 1
    · simp only [hlt, ite_true]
    · simp only [hlt, ite_false, show ¬ (p + 1 < (j : ℕ) + 1) by omega, Nat.add_sub_cancel]
  congr 2
  · unfold Evol.avM
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    unfold PsiData.mChain
    refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_)
      (fun p hp1 hp2 => (hdB p hp1 hp2))) a
    unfold Split.dropAt
    rw [mb_patM_apply _ _ hp1 hp2, mb_removeNth_val _ _ (by omega)]
    by_cases hlt : p < (j : ℕ) + 1 + 1
    · rw [ite_eq_left hlt, hmdef, mb_patMExt_apply _ _ hp1 (by omega)]
      congr 2
      apply Fin.ext
      simp only [Fin.val_succ]
      split_ifs <;> omega
    · rw [ite_eq_right hlt, hmdef, mb_patMExt_apply _ _ (by omega) (by omega)]
      congr 2
      apply Fin.ext
      simp only [Fin.val_succ]
      split_ifs <;> omega
  · unfold Evol.avM
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    unfold PsiData.mChain
    refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_)
      (fun p hp1 hp2 => (hdB p hp1 hp2))) a
    unfold Split.dropAt
    rw [mb_patM_apply _ _ hp1 hp2, mb_removeNth_val _ _ (by omega)]
    by_cases hlt : p < (j : ℕ) + 1
    · rw [ite_eq_left hlt, hmdef, mb_patMExt_apply _ _ hp1 (by omega)]
      congr 2
      apply Fin.ext
      simp only [Fin.val_castSucc]
      split_ifs <;> omega
    · rw [ite_eq_right hlt, hmdef, mb_patMExt_apply _ _ (by omega) (by omega)]
      congr 2
      apply Fin.ext
      simp only [Fin.val_castSucc]
      split_ifs <;> omega

/-!
## The bounds for a saturated pattern
-/

/-- Saturation, adjacent form: `σ_j ≠ σ_{j+1}`. -/
theorem mb_sat_adj {k : ℕ} {σ : Fin (k + 1) → Bool} (hσ : ¬ HasDesatFactor σ) (j : Fin k) :
    σ j.castSucc ≠ σ j.succ := by
  intro h
  apply hσ
  refine ⟨j.castSucc, ?_⟩
  unfold patNext
  rw [dite_eq_left (by simp)]
  rw [h]
  congr 1

/-- Saturation, cyclic form: `σ_{k} ≠ σ_0`. -/
theorem mb_sat_last {k : ℕ} {σ : Fin (k + 1) → Bool} (hσ : ¬ HasDesatFactor σ) :
    σ (Fin.last k) ≠ σ 0 := by
  intro h
  apply hσ
  refine ⟨Fin.last k, ?_⟩
  unfold patNext
  rw [dite_eq_right (by simp)]
  rw [h]
  rfl

/-- `‖c⁻¹ (a - b)‖ ≤ B/η` when `‖c‖ = 2η` and `‖a‖, ‖b‖ ≤ B`. -/
theorem mb_ward_norm_le {c a b : ℂ} {η B : ℝ} (hη : 0 < η) (hc : ‖c‖ = 2 * |η|)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) : ‖c⁻¹ * (a - b)‖ ≤ B / η := by
  rw [norm_mul, norm_inv, hc, abs_of_pos hη]
  have hab : ‖a - b‖ ≤ 2 * B := (norm_sub_le _ _).trans (by linarith)
  calc (2 * η)⁻¹ * ‖a - b‖ ≤ (2 * η)⁻¹ * (2 * B) :=
        mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr (by linarith))
    _ = B / η := by field_simp

include hS hz ht in

/-- **Ward bounds on the reduced partial traces** (under `Split.CyclicStatement` and
`Split.WardStatement`): for
a saturated pattern `σ` of length `n+4`, `t ∈ [0,1]`, `AvB(n+3, A₃)` and `AvB(n+2, A₂)`, the
reduced partial traces of `X = Tr[M^σ_t(·)]` satisfy
`|mbTrL X|, |mbTrM X| ≤ (A₃/η_t) L s^av_{n+3}` and `|mbTrLM X| ≤ (A₂/η_t²) L s^av_{n+2}`.
-/
theorem mbWard_bounds (hC : Split.CyclicStatement) (hW : Split.WardStatement) {n : ℕ}
    (σ : Fin (n + 4) → Bool) (hsat : ¬ HasDesatFactor σ) {A₃ A₂ : ℝ}
    (h3 : MBAvB P (n + 3) A₃) (h2 : MBAvB P (n + 2) A₂) (hη : 0 < vsHeight P.z t) :
    (∀ y, ‖mbTrL (fun x => Evol.avM P σ x t) y‖ ≤
        A₃ / vsHeight P.z t * (P.lEta t * P.sAv y t)) ∧
    (∀ y, ‖mbTrM (fun x => Evol.avM P σ x t) y‖ ≤
        A₃ / vsHeight P.z t * (P.lEta t * P.sAv y t)) ∧
    (∀ w, ‖mbTrLM (fun x => Evol.avM P σ x t) w‖ ≤
        A₂ / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv w t)) := by
  have hden : ∀ b b' : Bool, b ≠ b' →
      ‖Split.zParam t (VS.patConj b (semicircleM P.z)) -
        Split.zParam t (VS.patConj b' (semicircleM P.z))‖ = 2 * |vsHeight P.z t| :=
    fun b b' hb => norm_mb_zParam_sub P.z t hb
  have hL : ∀ y, ‖mbTrL (fun x => Evol.avM P σ x t) y‖ ≤
      A₃ / vsHeight P.z t * (P.lEta t * P.sAv y t) := by
    intro y
    unfold mbTrL
    rw [mbAvM_ward_last P hS hz ht hC hW (n := n + 2) σ (mb_sat_last hsat) y]
    rw [div_mul_eq_mul_div]
    exact mb_ward_norm_le hη (hden _ _ (mb_sat_last hsat)) (h3 t ht _ y) (h3 t ht _ y)
  refine ⟨hL, ?_, ?_⟩
  · intro y
    unfold mbTrM
    have hj : mbJ' n = (⟨n + 1, by omega⟩ : Fin (n + 3)).castSucc := Fin.ext rfl
    rw [hj, mbAvM_ward_mid P hS hz ht hW (n := n + 2) σ ⟨n + 1, by omega⟩
      (mb_sat_adj hsat _) y, div_mul_eq_mul_div]
    exact mb_ward_norm_le hη (hden _ _ (mb_sat_adj hsat _)) (h3 t ht _ y) (h3 t ht _ y)
  · intro w
    unfold mbTrLM mbTrL
    have hrot := mbAvM_ward_last P hS hz ht hC hW (n := n + 2) σ (mb_sat_last hsat)
    simp_rw [hrot]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    have hj : (⟨n + 1, by omega⟩ : Fin (n + 3)) = (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc :=
      Fin.ext rfl
    have hsa : mbPatRot σ (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc ≠
        mbPatRot σ (⟨n + 1, by omega⟩ : Fin (n + 2)).succ := by
      simp only [mbPatRot]
      rw [update_of_ne (by rw [Ne, Fin.ext_iff]; simp),
        update_of_ne (by rw [Ne, Fin.ext_iff]; simp)]
      convert mb_sat_adj hsat (⟨n + 1, by omega⟩ : Fin (n + 3)) using 2 <;> rfl
    have hsb : Fin.init σ (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc ≠
        Fin.init σ (⟨n + 1, by omega⟩ : Fin (n + 2)).succ := by
      convert mb_sat_adj hsat (⟨n + 1, by omega⟩ : Fin (n + 3)) using 2 <;> rfl
    rw [hj, mbAvM_ward_mid P hS hz ht hW (n := n + 1) _ _ hsa w,
      mbAvM_ward_mid P hS hz ht hW (n := n + 1) _ _ hsb w]
    have hA2 : ∀ (τ : Fin (n + 2) → Bool), ‖Evol.avM P τ w t‖ ≤ A₂ * (P.lEta t * P.sAv w t) :=
      fun τ => h2 t ht τ w
    have hi1 := mb_ward_norm_le hη (hden _ _ hsa)
      (hA2 (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2)).succ (mbPatRot σ)))
      (hA2 (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc (mbPatRot σ)))
    have hi2 := mb_ward_norm_le hη (hden _ _ hsb)
      (hA2 (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2)).succ (Fin.init σ)))
      (hA2 (Fin.removeNth (⟨n + 1, by omega⟩ : Fin (n + 2)).castSucc (Fin.init σ)))
    have := mb_ward_norm_le hη (hden _ _ (mb_sat_last hsat)) hi1 hi2
    calc _ ≤ A₂ * (P.lEta t * P.sAv w t) / vsHeight P.z t / vsHeight P.z t := this
      _ = A₂ / vsHeight P.z t ^ 2 * (P.lEta t * P.sAv w t) := by field_simp

end Pattern

end BlockBand.Native.ErdosRiabov.MBound
