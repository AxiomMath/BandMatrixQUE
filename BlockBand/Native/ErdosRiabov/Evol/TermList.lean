module

public import BlockBand.Native.ErdosRiabov.Evol.TermListPair

/-!
# The term list of the forcing

The forcing of the averaged and isotropic chains as an explicit sum of term families.

Main results (`x` sites, `σ` pattern, `R = slotsH`, `m_j = patM P.z σ j`):
* **`forcingAv_termList`** (`k ≥ 2`, the Erdős–Riabov forcing without the Ornstein–Uhlenbeck term
  `k/2`):
  `𝓕^av = Tr[famF1] + famQ + famM1 + famM2`, i.e. (F1) `∑_j Tr[G_{[1,j]} 𝒮[G_j - m_j]
  G_{[j,k]} S^{x_k}]`, (FQ) `∑_{i<j} ∑_q (A - A_M)(B - B_M)`, (FM) `∑_{j-i ≤ k-2} (A - A_M) B_M`
  and `∑_{j-i ≥ 2} A_M (B - B_M)`; the (L) terms are exactly `(⊕_{j=1}^k Â_j)[𝒳^k]`.
* **`forcingIso_termList`** (`k ≥ 2`, the isotropic forcing): the same families plus the last line
  `δ_ab m_1 m_k ∑_q (I + tÂ_k)_{aq} 𝒳^k(x', q)` (`lastLine`); needs `t ∈ [0,1]`, `Im z ≠ 0`.
* **`forcingAv_one`** (`k = 1`):
  `𝓕^av = Tr[𝒮[G - m_1] (G S^{x_1} G - M(z_1, S^{x_1}, z_1))]`;
  the isotropic case `k = 1` is `forcingIso_one`.
`(A, B)` are the pair data (`aG, aM, bGav/bGiso, bMav/bMiso`); the `G`-parts are ER's
`Tr[𝒮[(G-M)_{[i,j]}] (G-M)^{(x_k)}_{[j,i]}]` and `Tr[𝒮[(G-M)^{(x_k)}_{[j,i]}] M_{[i,j]}]` by
`pairIns_bandSelfEnergy` and cyclicity of the trace; for the `M`-parts the form
`B_M = Tr[M^{(q)}_{[1,i],[j,k]} S^{x_k}]` is used (ER's `Tr[S^q M^{(x_k)}_{[j,i]}]` is the same by
`M`-cyclicity, `Split.CyclicStatement`, which is not used here).
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

variable {N k : ℕ} (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-!
### Adjacent pairs
-/

theorem obsSeq_succ (s : Fin k) : obsSeq P.S x ((s : ℕ) + 1) = Split.rowObs P.S (x s) := by
  have h1 : 1 ≤ (s : ℕ) + 1 ∧ (s : ℕ) + 1 ≤ k := ⟨by omega, s.isLt⟩
  rw [obsSeq, dite_eq_left h1]
  exact congrArg (fun i => Split.rowObs P.S (x i)) (Fin.ext (by simp))

/-- `(M^{(t)}_{[i,i+1]})_qq = (Â_i)_{x_i q}`. -/
theorem aM_adj (hS : ∀ a b, P.S a b = P.S b a) {s : Fin k} (hs : (s : ℕ) + 1 < k) (q : Fin N) :
    aM P σ x t s ⟨(s : ℕ) + 1, hs⟩ q = aKer P σ s t (x s) q := by
  have hn : nextIdx s = (s : ℕ) + 1 + 1 := by rw [nextIdx, ite_eq_left hs]
  rw [aM, mSeg, chainM_adj, aKer, hn, vsKernel_apply_stabOp, obsSeq_succ]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Split.rowObs]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [stabOp_symm hS]
  ring

theorem mChain_update_adj {s : Fin k} (hs : (s : ℕ) + 1 < k) (q : Fin N) :
    P.mChain σ (update x s q) t = mGlue P σ x t s ⟨(s : ℕ) + 1, hs⟩ q := by
  rw [PsiData.mChain, mGlue]
  simp only
  rw [glueChain_adj, glueObs_adj, ← obsSeq_update,
    show k - ((s : ℕ) + 1 + 1) + ((s : ℕ) + 1) + 1 = k by omega]

/-- av: `B - B_M = 𝒳^k(x[x_i := q])` at an adjacent pair `(i, i+1)`. -/
theorem avErr_adj {s : Fin k} (hs : (s : ℕ) + 1 < k) (q : Fin N) :
    P.avErr σ (update x s q) t H =
      bGav P σ x t H s ⟨(s : ℕ) + 1, hs⟩ q - bMav P σ x t s ⟨(s : ℕ) + 1, hs⟩ q := by
  rw [PsiData.avErr, bGav, bMav, avSlots_update, gChain,
    slotProd_updateB_adj (avSlots P.S x) _ (j := ⟨(s : ℕ) + 1, hs⟩) rfl,
    mChain_update_adj P σ x t hs, obsSeq_update, update_of_ne (by omega)]
  rfl

/-- iso: `B - B_M = 𝒴^k(x[x_i := q])` at an adjacent pair `(i, i+1)`. -/
theorem isoErr_adj (a b : Fin N) {s : Fin k} (hs : (s : ℕ) + 1 < k) (q : Fin N) :
    P.isoErr σ a b (update x s q) t H =
      bGiso P σ x t H a b s ⟨(s : ℕ) + 1, hs⟩ q - bMiso P σ x t a b s ⟨(s : ℕ) + 1, hs⟩ q := by
  rw [PsiData.isoErr, bGiso, bMiso, isoSlots_update P.S x hs, gChain,
    slotProd_updateB_adj (isoSlots P.S x) _ (j := ⟨(s : ℕ) + 1, hs⟩) rfl,
    mChain_update_adj P σ x t hs]
  rfl

/-!
### The pair `(1,k)`
-/

theorem mChain_update_last {l : Fin k} (hl : (l : ℕ) + 1 = k) (p : Fin N) :
    P.mChain σ (update x l p) t = P.mChain σ x t := by
  rw [PsiData.mChain, PsiData.mChain]
  refine chainM_congr _ _ _ fun p' _ hp' => ?_
  rw [obsSeq_update, update_of_ne (by omega)]

theorem avErr_last {l : Fin k} (hl : (l : ℕ) + 1 = k) (p : Fin N) :
    P.avErr σ (update x l p) t H =
      ∑ q, (gHead (isoSlots P.S x) (slotsH P.z σ t H) l q q - P.mChain σ x t q) *
        (P.S p q : ℂ) := by
  rw [PsiData.avErr, avSlots_update, gChain, update_avSlots_last P.S x hl,
    slotProd_updateB_last _ _ hl, trace_mul_obsMat, mChain_update_last P σ x t hl,
    obsSeq_update, hl, update_self]
  simp only [Split.rowObs, sub_mul, Finset.sum_sub_distrib]
  rfl

theorem gHead_av_eq_iso {l : Fin k} (hl : (l : ℕ) + 1 = k) :
    gHead (avSlots P.S x) (slotsH P.z σ t H) l = gHead (isoSlots P.S x) (slotsH P.z σ t H) l := by
  have h := slotProd_updateB_last (avSlots P.S x) (slotsH P.z σ t H) hl 1
  rw [update_avSlots_last P.S x hl, slotProd_updateB_last _ _ hl, Matrix.mul_one,
    Matrix.mul_one] at h
  exact h.symm

/-- `M^{(q)}_{[1,1],[k,k]} = m_1 m_k (1 - t m_1 m_k S)⁻¹ S^q` (`k ≥ 2`). -/
theorem mGlue_cyc (hk : 2 ≤ k) (q : Fin N) :
    mGlue P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      (patM P.z σ 1 * patM P.z σ k) •
        (Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ k) *ᵥ Split.rowObs P.S q) := by
  rw [mGlue]
  simp only
  rw [show k - (k - 1 + 1) + (0 + 1) + 1 = 1 + 1 by omega, show k - 1 + 1 = k by omega,
    chainM_adj]
  have h1 : Split.glueChain 1 k (patM P.z σ) 1 = patM P.z σ 1 := by
    simp [Split.glueChain]
  have h2 : Split.glueChain 1 k (patM P.z σ) (1 + 1) = patM P.z σ k := by
    unfold Split.glueChain
    rw [ite_eq_right (by omega)]
    congr 1
    omega
  have h3 : Split.glueObs 1 k (Split.rowObs P.S q) (obsSeq P.S x) 1 = Split.rowObs P.S q := by
    simp [Split.glueObs]
  rw [h1, h2, h3]

theorem aKer_last {l : Fin k} (hl : (l : ℕ) + 1 = k) :
    aKer P σ l t = vsKernel P.S (patM P.z σ k) (patM P.z σ 1) t := by
  have hn : nextIdx l = 1 := by rw [nextIdx, ite_eq_right (by omega)]
  rw [aKer, hn, hl]

/-- Averaged case, the pair `(1,k)`: `∑_q (A - A_M) B_M = ∑_p (Â_k)_{x_k p} 𝒳^k(x', p)`. -/
theorem lCyc_av (hS : ∀ a b, P.S a b = P.S b a) (hk : 2 ≤ k) :
    ∑ q, (aG P σ t H (avSlots P.S x) ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q -
        aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q) *
        bMav P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      ∑ p, aKer P σ ⟨k - 1, by omega⟩ t (x ⟨k - 1, by omega⟩) p *
        P.avErr σ (update x ⟨k - 1, by omega⟩ p) t H := by
  have hl : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) + 1 = k := by simp only; omega
  simp_rw [avErr_last P σ x t H hl, aKer_last P σ t hl, vsKernel_apply_stabOp]
  have hA : ∀ q, aG P σ t H (avSlots P.S x) ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q -
      aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      gHead (isoSlots P.S x) (slotsH P.z σ t H) ⟨k - 1, by omega⟩ q q - P.mChain σ x t q := by
    intro q
    rw [aG, aM, mSeg, ← gHead_av_eq_iso P σ x t H hl]
    simp only [Nat.zero_add]
    rw [show k - 1 + 1 = k by omega]
    rfl
  simp_rw [hA, bMav, mGlue_cyc P σ x t hk, obsSeq_last P.S x hl]
  rw [mul_comm (patM P.z σ k)]
  have := sum_cyc_alg hS (Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ k))
    (patM P.z σ 1 * patM P.z σ k)
    (fun q => gHead (isoSlots P.S x) (slotsH P.z σ t H) ⟨k - 1, by omega⟩ q q -
      P.mChain σ x t q) (x ⟨k - 1, by omega⟩)
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Split.rowObs] at this ⊢
  rw [← this]

/-- Isotropic case, the pair `(1,k)`: `∑_q (A - A_M) B_M` is the last line `lastLine`. -/
theorem lCyc_iso (hSS : StochasticSymm P.S) (hz : P.z.im ≠ 0) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hk : 2 ≤ k) (a b : Fin N) :
    ∑ q, (aG P σ t H (isoSlots P.S x) ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q -
        aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q) *
        bMiso P σ x t a b ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      lastLine P σ x t H a b ⟨k - 1, by omega⟩ := by
  have hS := hSS.symm
  have hl : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) + 1 = k := by simp only; omega
  have hA : ∀ q, aG P σ t H (isoSlots P.S x) ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q -
      aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      gHead (isoSlots P.S x) (slotsH P.z σ t H) ⟨k - 1, by omega⟩ q q - P.mChain σ x t q := by
    intro q
    rw [aG, aM, mSeg]
    simp only [Nat.zero_add]
    rw [show k - 1 + 1 = k by omega]
    rfl
  have hn : ‖(t : ℂ) * (patM P.z σ k * patM P.z σ 1)‖ < 1 :=
    norm_smul_lt_one (norm_patM_lt_one hz σ _) (norm_patM_lt_one hz σ _) ht.1 ht.2
  unfold lastLine bMiso
  by_cases hab : a = b
  · simp only [hab, ite_true]
    simp_rw [hA, avErr_last P σ x t H hl, aKer_last P σ t hl, one_add_smul_vsKernel hSS hn,
      mGlue_cyc P σ x t hk]
    rw [mul_comm (patM P.z σ k)]
    have := sum_iso_alg hS (Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ k))
      (patM P.z σ 1 * patM P.z σ k)
      (fun q => gHead (isoSlots P.S x) (slotsH P.z σ t H) ⟨k - 1, by omega⟩ q q -
        P.mChain σ x t q) b
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Split.rowObs] at this ⊢
    rw [this]
  · simp [hab]

/-!
### The (L) family is the generator term
-/

theorem lAdj_lCyc_av (hS : ∀ a b, P.S a b = P.S b a) (hk : 2 ≤ k) :
    lAdj (aM P σ x t) (bGav P σ x t H) (bMav P σ x t) +
        lCyc (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bMav P σ x t) =
      aTermAv P σ x t H := by
  unfold lAdj lCyc
  rw [lAdj_eq (fun i j => ∑ q, aM P σ x t i j q * (bGav P σ x t H i j q - bMav P σ x t i j q)),
    lCyc_eq hk (fun i j => ∑ q, (aG P σ t H (avSlots P.S x) i j q - aM P σ x t i j q) *
      bMav P σ x t i j q), lCyc_av P σ x t H hS hk, aTermAv,
    sum_split_last (by omega) (fun s => ∑ q, aKer P σ s t (x s) q * P.avErr σ (update x s q) t H)]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : (s : ℕ) + 1 < k
  · rw [dite_eq_left hs, ite_eq_left hs]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [aM_adj P σ x t hS hs, avErr_adj P σ x t H hs]
  · rw [dite_eq_right hs, ite_eq_right hs]

theorem lAdj_iso (hS : ∀ a b, P.S a b = P.S b a) (a b : Fin N) :
    lAdj (aM P σ x t) (bGiso P σ x t H a b) (bMiso P σ x t a b) = aTermIso P σ a b x t H := by
  unfold lAdj
  rw [lAdj_eq (fun i j => ∑ q, aM P σ x t i j q *
      (bGiso P σ x t H a b i j q - bMiso P σ x t a b i j q)), aTermIso, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : (s : ℕ) + 1 < k
  · rw [dite_eq_left hs, ite_eq_left hs]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [aM_adj P σ x t hS hs, isoErr_adj P σ x t H a b hs]
  · rw [dite_eq_right hs, ite_eq_right hs]

/-!
### The term list
-/

/-- **The averaged forcing as a list of terms** (`k ≥ 2`, with `M^{(t)}`, unscaled `𝒮`, no
`k/2`). For symmetric `S`, every `(t, H)`: `𝓕^av = Tr[famF1] + famQ + famM1 + famM2` ((F1),
(FQ), (FM)); the (L) terms are `(⊕_{j=1}^k Â_j)[𝒳^k]` and cancel against `aTermAv`. No
`Split.DerivStatement` is used. -/
theorem forcingAv_termList (hS : ∀ a b, P.S a b = P.S b a) (hk : 2 ≤ k) :
    forcingAv P σ x t H = trace (famF1 P σ t H (avSlots P.S x)) +
      famQ (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bGav P σ x t H) (bMav P σ x t) +
      famM1 (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bMav P σ x t) +
      famM2 (aM P σ x t) (bGav P σ x t H) (bMav P σ x t) := by
  have hp := pair_expand (aG P σ t H (avSlots P.S x)) (aM P σ x t) (bGav P σ x t H)
    (bMav P σ x t)
  have hL := lAdj_lCyc_av P σ x t H hS hk
  rw [forcingAv, dGav_split P hS, dMav_split, ← hL]
  have hsub : (∑ j : Fin k, ∑ i with i < j, ∑ q,
      aG P σ t H (avSlots P.S x) i j q * bGav P σ x t H i j q) -
      ∑ j : Fin k, ∑ i with i < j, ∑ q, aM P σ x t i j q * bMav P σ x t i j q =
      ∑ j : Fin k, ∑ i with i < j, ∑ q, (aG P σ t H (avSlots P.S x) i j q *
        bGav P σ x t H i j q - aM P σ x t i j q * bMav P σ x t i j q) := by
    simp only [← Finset.sum_sub_distrib]
  rw [add_sub_assoc, hsub, hp]
  ring

/-- For stochastic
symmetric `S`, `Im z ≠ 0`, `t ∈ [0,1]` and every `H`:
`𝓕^iso = (famF1)_{ab} + famQ + famM1 + famM2 + δ_ab m_1 m_k ∑_q (I + tÂ_k)_{aq} 𝒳^k(x', q)`.
No `Split.DerivStatement` is used.
-/
theorem forcingIso_termList (hSS : StochasticSymm P.S) (hz : P.z.im ≠ 0)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hk : 2 ≤ k) (a b : Fin N) :
    forcingIso P σ a b x t H = famF1 P σ t H (isoSlots P.S x) a b +
      famQ (aG P σ t H (isoSlots P.S x)) (aM P σ x t) (bGiso P σ x t H a b)
        (bMiso P σ x t a b) +
      famM1 (aG P σ t H (isoSlots P.S x)) (aM P σ x t) (bMiso P σ x t a b) +
      famM2 (aM P σ x t) (bGiso P σ x t H a b) (bMiso P σ x t a b) +
      lastLine P σ x t H a b ⟨k - 1, by omega⟩ := by
  have hS := hSS.symm
  have hp := pair_expand (aG P σ t H (isoSlots P.S x)) (aM P σ x t) (bGiso P σ x t H a b)
    (bMiso P σ x t a b)
  have hA := lAdj_iso P σ x t H hS a b
  have hC : lCyc (aG P σ t H (isoSlots P.S x)) (aM P σ x t) (bMiso P σ x t a b) =
      lastLine P σ x t H a b ⟨k - 1, by omega⟩ := by
    unfold lCyc
    rw [lCyc_eq hk (fun i j => ∑ q, (aG P σ t H (isoSlots P.S x) i j q - aM P σ x t i j q) *
      bMiso P σ x t a b i j q), lCyc_iso P σ x t H hSS hz ht hk a b]
  rw [forcingIso, dGiso_split P hS, dMiso_split, ← hA, ← hC]
  have hsub : (∑ j : Fin k, ∑ i with i < j, ∑ q,
      aG P σ t H (isoSlots P.S x) i j q * bGiso P σ x t H a b i j q) -
      ∑ j : Fin k, ∑ i with i < j, ∑ q, aM P σ x t i j q * bMiso P σ x t a b i j q =
      ∑ j : Fin k, ∑ i with i < j, ∑ q, (aG P σ t H (isoSlots P.S x) i j q *
        bGiso P σ x t H a b i j q - aM P σ x t i j q * bMiso P σ x t a b i j q) := by
    simp only [← Finset.sum_sub_distrib]
  rw [add_sub_assoc, hsub, hp]
  ring

/-!
### The case `k = 1`
-/

/-- `M(z_1, S^{x_1}, z_1)` (diagonal), the deterministic approximation of `G S^{x_1} G`. -/
def mSelf (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) (t : ℝ) : Fin N → ℂ :=
  Split.chainM t P.S (fun _ => patM P.z σ 1) (fun _ => Split.rowObs P.S (x 0)) 1 2

theorem sum_one_alg (K : Matrix (Fin N) (Fin N) ℂ) (hK : ∀ a b, K a b = K b a)
    (S : Matrix (Fin N) (Fin N) ℝ) (c : ℂ) (Y : Fin N → ℂ) (x : Fin N) :
    ∑ q, (c * ∑ d, (S x d : ℂ) * K d q) * ∑ b, Y b * (S q b : ℂ) =
      ∑ a, (∑ b, (S a b : ℂ) * Y b) * (c * ∑ d, K a d * (S x d : ℂ)) := by
  have hW : ∀ q, c * ∑ d, (S x d : ℂ) * K d q = c * ∑ d, K q d * (S x d : ℂ) := fun q => by
    congr 1
    exact Finset.sum_congr rfl fun d _ => by rw [hK d q, mul_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hW q, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **The averaged forcing for `k = 1`** (Ornstein–Uhlenbeck term deleted): for symmetric `S`
and every `(t, H)`, `𝓕^av = Tr[𝒮[G - m_1] (G S^{x_1} G - M(z_1, S^{x_1}, z_1))]`,
`G = (H - z_{1,t})⁻¹`. -/
theorem forcingAv_one (hS : ∀ a b, P.S a b = P.S b a) (σ : Fin 1 → Bool) (x : Fin 1 → Fin N)
    (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    forcingAv P σ x t H = trace (bandSelfEnergy P.S
        (slotsH P.z σ t H 0 - VS.patConj (σ 0) (semicircleM P.z) • 1) *
      (slotsH P.z σ t H 0 * obsMat P.S (x 0) * slotsH P.z σ t H 0 -
        Matrix.diagonal (mSelf P σ x t))) := by
  set R := slotsH P.z σ t H 0 with hR
  set m1 := patM P.z σ 1 with hm1
  have hm : VS.patConj (σ 0) (semicircleM P.z) = m1 := (patM_of_mem P.z σ 0).symm
  rw [hm]
  have hdG : dGav P σ x t H =
      trace (R * bandSelfEnergy P.S (R - m1 • 1) * (R * obsMat P.S (x 0))) := by
    rw [dGav, ← hm]
    simp [dGmat, pairIns, segProd_self, avSlots, hR]
  have hdM : dMav P σ x t = 0 := by simp [dMav, mDerivP_one]
  have hav : ∀ q, P.avErr σ (update x 0 q) t H = ∑ b, (R b b - m1) * (P.S q b : ℂ) := by
    intro q
    have h1 : obsSeq P.S (update x 0 q) 1 = Split.rowObs P.S q := by
      have := obsSeq_succ P (update x 0 q) 0
      rwa [update_self] at this
    have hg : gChain (patZ P.z σ t) (avSlots P.S (update x 0 q)) H = R * obsMat P.S q := by
      simp [gChain, Chains.slotProd, Chains.slotList, avSlots, hR, slotsH]
    rw [PsiData.avErr, mChain_one, h1, hg, trace_mul_obsMat, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by simp only [Split.rowObs]; ring
  have hker : ∀ q, aKer P σ 0 t (x 0) q =
      m1 * m1 * ∑ d, (P.S (x 0) d : ℂ) * Split.stabOp t P.S (m1 * m1) d q := by
    intro q
    rw [aKer, show nextIdx (0 : Fin 1) = 1 by rfl, vsKernel_apply_stabOp]
    rfl
  have hself : mSelf P σ x t =
      (m1 * m1) • (Split.stabOp t P.S (m1 * m1) *ᵥ Split.rowObs P.S (x 0)) := by
    rw [mSelf, chainM_adj]
  have haT : aTermAv P σ x t H = ∑ q, (m1 * m1 * ∑ d, (P.S (x 0) d : ℂ) *
      Split.stabOp t P.S (m1 * m1) d q) * ∑ b, (R b b - m1) * (P.S q b : ℂ) := by
    rw [aTermAv, Fin.sum_univ_one]
    exact Finset.sum_congr rfl fun q _ => by rw [hker, hav]
  have hc : trace (R * bandSelfEnergy P.S (R - m1 • 1) * (R * obsMat P.S (x 0))) =
      trace (bandSelfEnergy P.S (R - m1 • 1) * (R * obsMat P.S (x 0) * R)) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [forcingAv, hdG, hdM, haT, sum_one_alg _ (stabOp_symm hS t _) P.S, Matrix.mul_sub,
    trace_sub, hself, hc, sub_zero]
  congr 1
  rw [bandSelfEnergy, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Pi.smul_apply, Matrix.mulVec, dotProduct, Split.rowObs]

end BlockBand.Native.ErdosRiabov.Evol
