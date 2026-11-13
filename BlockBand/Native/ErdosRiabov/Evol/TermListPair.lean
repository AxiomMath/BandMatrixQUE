module

public import BlockBand.Native.ErdosRiabov.Evol.TermListDefs

/-!
# Term list of the forcing: the linear family (L), pair lemmas

* Re-indexing of the (L) pair sums: `lAdj_eq` (pairs `(i, i+1)` ↔ slots `i < k-1`), `lCyc_eq`
  (the pair `(1,k)`), `sum_split_last`.
* Observables under a site update: `obsSeq_update`, `avSlots_update`, `isoSlots_update`,
  `update_avSlots_last`; the glued chain of an adjacent pair is the chain with `x_i := q`
  (`glueChain_adj`, `glueObs_adj`).
* **Adjacent pairs** (`aM_adj`, `avErr_adj`, `isoErr_adj`): `(M^{(t)}_{[i,i+1]})_qq = (Â_i)_{x_i q}`
  and `B - B_M = 𝒳^k(x[x_i := q])` (resp. `𝒴^k`), so `A_M (B - B_M)` at `j = i+1` is `Â_i`
  acting on `x_i`.
* **The pair `(1,k)`** (`lCyc_av`, `lCyc_iso`): av `∑_q (A - A_M) B_M = ∑_p (Â_k)_{x_k p}
  𝒳^k(x', p)` (from `Tr[M^{(t)}(z_1, S^q, z_k) S^{x_k}] = (S Â_k)_{x_k q}`); iso
  `∑_q (A - A_M) B_M = δ_ab m_1 m_k ∑_p (I + tÂ_k)_{ap} 𝒳^k(x', p)` (from `(I - tY)⁻¹ = I + tÂ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi

variable {N k : ℕ}

/-!
### Re-indexing
-/

theorem lAdj_eq (F : Fin k → Fin k → ℂ) :
    ∑ j : Fin k, ∑ i with i < j, (if (j : ℕ) = i + 1 then F i j else 0) =
      ∑ i : Fin k, if h : (i : ℕ) + 1 < k then F i ⟨(i : ℕ) + 1, h⟩ else 0 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) + 1 < k
  · rw [dite_eq_left h, Fintype.sum_eq_single ⟨(i : ℕ) + 1, h⟩]
    · have hlt : i < (⟨(i : ℕ) + 1, h⟩ : Fin k) := by
        rw [Fin.lt_def]
        simp
      simp [hlt]
    · intro j hj
      split_ifs with h1 h2
      · exact absurd (Fin.ext h2) hj
      · rfl
      · rfl
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h1 h2
    · have := j.isLt
      omega
    · rfl
    · rfl

theorem lCyc_eq (hk : 2 ≤ k) (F : Fin k → Fin k → ℂ) :
    ∑ j : Fin k, ∑ i with i < j, (if (j : ℕ) - i = k - 1 then F i j else 0) =
      F ⟨0, by omega⟩ ⟨k - 1, by omega⟩ := by
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [Fintype.sum_eq_single ⟨0, by omega⟩]
    · have hlt : (⟨0, by omega⟩ : Fin k) < ⟨k - 1, by omega⟩ := by
        rw [Fin.lt_def]
        simp only
        omega
      simp [hlt]
    · intro i hi
      split_ifs with h1 h2
      · exfalso
        apply hi
        apply Fin.ext
        simp only at h2 ⊢
        omega
      · rfl
      · rfl
  · intro j hj
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h1 h2
    · exfalso
      apply hj
      apply Fin.ext
      have := j.isLt
      simp only
      omega
    · rfl
    · rfl

theorem sum_split_last (hk : 1 ≤ k) (G : Fin k → ℂ) :
    ∑ s, G s = (∑ s : Fin k, if (s : ℕ) + 1 < k then G s else 0) + G ⟨k - 1, by omega⟩ := by
  have h1 : ∑ s, G s = ∑ s : Fin k, ((if (s : ℕ) + 1 < k then G s else 0) +
      (if (s : ℕ) + 1 < k then 0 else G s)) :=
    Finset.sum_congr rfl fun s _ => by split_ifs <;> simp
  rw [h1, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_eq_single ⟨k - 1, by omega⟩]
  · simp only
    rw [ite_eq_right (by omega)]
  · intro s hs
    have : (s : ℕ) + 1 < k := by
      have h2 := s.isLt
      have h3 : (s : ℕ) ≠ k - 1 := fun e => hs (Fin.ext e)
      omega
    rw [ite_eq_left this]

/-!
### Observables under a site update
-/

theorem obsSeq_update (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) (s : Fin k)
    (q : Fin N) :
    obsSeq S (update x s q) = update (obsSeq S x) ((s : ℕ) + 1) (Split.rowObs S q) := by
  funext p
  by_cases hp : p = (s : ℕ) + 1
  · subst hp
    rw [update_self]
    have h1 : 1 ≤ (s : ℕ) + 1 ∧ (s : ℕ) + 1 ≤ k := ⟨by omega, s.isLt⟩
    rw [obsSeq, dite_eq_left h1]
    have he : (⟨(s : ℕ) + 1 - 1, by omega⟩ : Fin k) = s := Fin.ext (by simp)
    rw [he, update_self]
  · rw [update_of_ne hp]
    unfold obsSeq
    split_ifs with h
    · congr 1
      apply update_of_ne
      intro he
      apply hp
      have := congrArg Fin.val he
      simp only at this
      omega
    · rfl

theorem glueChain_adj (i : ℕ) (m : ℕ → ℂ) : Split.glueChain i (i + 1) m = m := by
  funext p
  unfold Split.glueChain
  split_ifs
  · rfl
  · congr 1
    omega

theorem glueObs_adj (i : ℕ) (X : Fin N → ℂ) (A : ℕ → Fin N → ℂ) :
    Split.glueObs i (i + 1) X A = update A i X := by
  funext p
  unfold Split.glueObs
  by_cases h1 : p < i
  · rw [ite_eq_left h1, update_of_ne (by omega)]
  · by_cases h2 : p = i
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl, update_self]
    · rw [ite_eq_right h1, ite_eq_right h2, update_of_ne h2]
      congr 1
      omega

theorem avSlots_update (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) (s : Fin k)
    (q : Fin N) : avSlots S (update x s q) = update (avSlots S x) s (obsMat S q) := by
  funext l
  by_cases h : l = s
  · subst h
    simp [avSlots]
  · simp [avSlots, update_of_ne h]

theorem isoSlots_update (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) {s : Fin k}
    (hs : (s : ℕ) + 1 < k) (q : Fin N) :
    isoSlots S (update x s q) = update (isoSlots S x) s (obsMat S q) := by
  funext l
  by_cases h : l = s
  · subst h
    simp [isoSlots, hs]
  · simp [isoSlots, update_of_ne h]

theorem update_avSlots_last (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) {l : Fin k}
    (hl : (l : ℕ) + 1 = k) (X : Matrix (Fin N) (Fin N) ℂ) :
    update (avSlots S x) l X = update (isoSlots S x) l X := by
  funext j
  by_cases h : j = l
  · subst h
    simp
  · have hj : (j : ℕ) + 1 < k := by
      have h2 := j.isLt
      have h3 : (j : ℕ) ≠ l := fun e => h (Fin.ext e)
      omega
    simp [avSlots, isoSlots, update_of_ne h, hj]

theorem trace_mul_obsMat (S : Matrix (Fin N) (Fin N) ℝ) (Y : Matrix (Fin N) (Fin N) ℂ)
    (p : Fin N) : trace (Y * obsMat S p) = ∑ q, Y q q * (S p q : ℂ) := by
  simp [trace, obsMat, Matrix.mul_diagonal, Split.rowObs]

theorem obsSeq_last (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) {l : Fin k}
    (hl : (l : ℕ) + 1 = k) : obsSeq S x k = Split.rowObs S (x l) := by
  have h1 : 1 ≤ k ∧ k ≤ k := ⟨by omega, le_rfl⟩
  rw [obsSeq, dite_eq_left h1]
  congr 2
  exact Fin.ext (by simp only; omega)

/-!
### Kernel entries
-/

theorem vsKernel_apply_stabOp (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) (a b : Fin N) :
    vsKernel S μ μ' t a b =
      μ * μ' * ∑ d, (S a d : ℂ) * Split.stabOp t S (μ * μ') d b := by
  rw [vsKernel_eq_stabOp, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Split.profileC, mul_assoc]

theorem one_add_smul_vsKernel {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : ℂ} {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    1 + (t : ℂ) • vsKernel S μ μ' t = Split.stabOp t S (μ * μ') := by
  have h := one_sub_vsY_mul_inv hS ht
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  rw [← inv_one_sub_vsY_eq_stabOp, vsKernel]
  exact (sub_eq_iff_eq_add.mp h).symm

/-!
### Two finite-sum identities (symmetric `S`, `K`)
-/

theorem sum_SKS {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a b, S a b = S b a)
    (K : Matrix (Fin N) (Fin N) ℂ) (x q : Fin N) :
    ∑ a, (∑ d, K a d * (S q d : ℂ)) * (S x a : ℂ) =
      ∑ p, (∑ d, (S x d : ℂ) * K d p) * (S p q : ℂ) := by
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  rw [hS q d]
  ring

theorem sum_cyc_alg {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a b, S a b = S b a)
    (K : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (Y : Fin N → ℂ) (x : Fin N) :
    ∑ q, Y q * ∑ a, c * (∑ d, K a d * (S q d : ℂ)) * (S x a : ℂ) =
      ∑ p, (c * ∑ d, (S x d : ℂ) * K d p) * ∑ q, Y q * (S p q : ℂ) := by
  have hL : ∀ q, Y q * ∑ a, c * (∑ d, K a d * (S q d : ℂ)) * (S x a : ℂ) =
      Y q * (c * ∑ p, (∑ d, (S x d : ℂ) * K d p) * (S p q : ℂ)) := fun q => by
    rw [← sum_SKS hS K x q, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sum_iso_alg {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a b, S a b = S b a)
    (K : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (Y : Fin N → ℂ) (a : Fin N) :
    ∑ q, Y q * (c * ∑ d, K a d * (S q d : ℂ)) =
      ∑ p, c * K a p * ∑ q, Y q * (S p q : ℂ) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [hS q p]
  ring

end BlockBand.Native.ErdosRiabov.Evol
