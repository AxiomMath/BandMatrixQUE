module

public import BlockBand.Native.ErdosRiabov.MBound.Defs
public import BlockBand.Native.ErdosRiabov.Evol.TermList

/-!
# The VS evolution of the averaged `M`-term

The time derivative of the averaged `M`-term is the generator term plus the `M`-forcing.

For a pattern `σ` of length `k ≥ 3` (any pattern), symmetric `S`:
`dMav = (⊕_{j=1}^k Â_j)[Tr M] + F_M`, where
* `mbAvGen P σ x t = Σ_j Σ_q (Â_j)_{x_j q} Tr[M^σ_t](x[j ↦ q])` (`Â_j = Evol.aKer`, cyclic);
* `mbFM P σ x t = Σ_{i<j, 2 ≤ j-i ≤ k-2} Σ_q (M_{[i,j]})_{qq} Tr[M^{(q)}_{[1,i],[j,k]} S^{x_k}]`
  (the Erdős–Riabov `M`-forcing; `Evol.aM`, `Evol.bMav`).
For `k = 2` the single pair `(1,2)` is both adjacent and cyclic, so the formula
`⊕_{j=1}^2 Â_j` would count it twice; the decomposition is therefore stated only for `k ≥ 3`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Evol
open scoped BigOperators

variable {N k : ℕ}

/-- The generator term `(⊕_{j=1}^k Â_j)[Tr M^σ_t]`. -/
def mbAvGen (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) : ℂ :=
  ∑ j, ∑ q, aKer P σ j t (x j) q * avM P σ (update x j q) t

/-- The `M`-forcing `F_M` (pairs with `2 ≤ j - i ≤ k - 2`). -/
def mbFM (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) : ℂ :=
  ∑ j : Fin k, ∑ i with i < j,
    if 2 ≤ (j : ℕ) - i ∧ (j : ℕ) - i ≤ k - 2 then ∑ q, aM P σ x t i j q * bMav P σ x t i j q
    else 0

section Lemmas

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)

/-- Adjacent pair `(s, s+1)`: `Σ_q aM bMav = Σ_q (Â_s)_{x_s q} Tr M(x[s ↦ q])`. -/
theorem mb_pair_adj (hS : ∀ a b, P.S a b = P.S b a) {s : Fin k} (hs : (s : ℕ) + 1 < k) :
    ∑ q, aM P σ x t s ⟨(s : ℕ) + 1, hs⟩ q * bMav P σ x t s ⟨(s : ℕ) + 1, hs⟩ q =
      ∑ q, aKer P σ s t (x s) q * avM P σ (update x s q) t := by
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [aM_adj P σ x t hS hs]
  congr 1
  rw [bMav, avM]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mChain_update_adj P σ x t hs, obsSeq_update, update_of_ne (by omega)]

/-- The cyclic pair `(1, k)`: `Σ_q aM bMav = Σ_p (Â_k)_{x_k p} Tr M(x[k ↦ p])`. -/
theorem mb_pair_cyc (hS : ∀ a b, P.S a b = P.S b a) (hk : 2 ≤ k) :
    ∑ q, aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q *
        bMav P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      ∑ p, aKer P σ ⟨k - 1, by omega⟩ t (x ⟨k - 1, by omega⟩) p *
        avM P σ (update x ⟨k - 1, by omega⟩ p) t := by
  have hl : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) + 1 = k := by simp only; omega
  have hA : ∀ q, aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q = P.mChain σ x t q := by
    intro q
    rw [aM, mSeg]
    simp only [Nat.zero_add]
    rw [show k - 1 + 1 = k by omega]
    rfl
  have hX : ∀ p, avM P σ (update x ⟨k - 1, by omega⟩ p) t =
      ∑ q, P.mChain σ x t q * (P.S p q : ℂ) := by
    intro p
    rw [avM, mChain_update_last P σ x t hl, obsSeq_update, hl, update_self]
    rfl
  simp_rw [hA, hX, aKer_last P σ t hl, vsKernel_apply_stabOp, bMav, mGlue_cyc P σ x t hk,
    obsSeq_last P.S x hl]
  rw [mul_comm (patM P.z σ k)]
  have := sum_cyc_alg hS (Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ k))
    (patM P.z σ 1 * patM P.z σ k) (fun q => P.mChain σ x t q) (x ⟨k - 1, by omega⟩)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Split.rowObs] at this ⊢
  rw [← this]

/-- **M.1**: for `k ≥ 3` and symmetric `S`,
`dMav = (⊕_{j=1}^k Â_j)[Tr M] + F_M`.
Unconditional (it is a statement about `Evol.dMav`, the
explicit right-hand side of `Split.DerivStatement`).
-/
theorem mbAvM_evol (hS : ∀ a b, P.S a b = P.S b a) (hk : 3 ≤ k) :
    dMav P σ x t = mbAvGen P σ x t + mbFM P σ x t := by
  rw [dMav_split]
  set T : Fin k → Fin k → ℂ := fun i j => ∑ q, aM P σ x t i j q * bMav P σ x t i j q
  have hsplit : ∀ j : Fin k, ∀ i ∈ (Finset.univ.filter fun i : Fin k => i < j),
      T i j = (if (j : ℕ) = i + 1 then T i j else 0) +
        (if (j : ℕ) - i = k - 1 then T i j else 0) +
        (if 2 ≤ (j : ℕ) - i ∧ (j : ℕ) - i ≤ k - 2 then T i j else 0) := by
    intro j i hi
    have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
    have hjk := j.isLt
    by_cases h1 : (j : ℕ) = i + 1
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
      ring
    · by_cases h2 : (j : ℕ) - i = k - 1
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right (by omega)]
        ring
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left (by omega)]
        ring
  have e : ∑ j : Fin k, ∑ i with i < j, T i j =
      (∑ j : Fin k, ∑ i with i < j, if (j : ℕ) = i + 1 then T i j else 0) +
        (∑ j : Fin k, ∑ i with i < j, if (j : ℕ) - i = k - 1 then T i j else 0) +
        mbFM P σ x t := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl (hsplit j)]
    simp only [Finset.sum_add_distrib]
    rfl
  rw [e, lAdj_eq, lCyc_eq (by omega)]
  congr 1
  rw [mbAvGen, sum_split_last (by omega)
    (fun s => ∑ q, aKer P σ s t (x s) q * avM P σ (update x s q) t)]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : (s : ℕ) + 1 < k
    · rw [dite_eq_left hs, ite_eq_left hs]
      exact mb_pair_adj P σ x t hS hs
    · rw [dite_eq_right hs, ite_eq_right hs]
  · exact mb_pair_cyc P σ x t hS (by omega)

end Lemmas

end BlockBand.Native.ErdosRiabov.MBound
