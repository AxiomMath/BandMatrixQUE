module

public import BlockBand.Native.ErdosRiabov.Evol.RegWard

/-!
# The Ward reduction at an interior slot

The Ward identities for resolvent chains and their deterministic approximations
(Erdős–Riabov), at an interior slot. **Conditional on `Split.WardStatement`** (`hW`, an
explicit hypothesis). No cyclicity is used. Deterministic: fixed `(t, H)`, `H` Hermitian,
`t ∈ [0,1]`.

For a chain of length `K+2` and an interior observable slot `j` (0-based coordinate
`j.castSucc`, between the resolvents `G_j` and `G_{j+1}`, `j.succ`), with `σ_j ≠ σ_{j+1}`:
`Σ_b 𝒳(x[j ↦ b]) = (z_j - z_{j+1})⁻¹ (𝒳^{σ \ σ_{j+1}}(x \ x_j) - 𝒳^{σ \ σ_j}(x \ x_j))`, where
`\` is `Fin.removeNth` (the pattern without the entry `j+1`, resp. `j`, and the sites without
`x_j`).

* `circ_ofFn_prod_drop`: list bookkeeping for the two shortened chains.
* `circ_ward_gChain_mid` (`G`-part): `Σ_b S^b = I` and
  `G_j G_{j+1} = (z_j - z_{j+1})⁻¹(G_j - G_{j+1})`.
* `circ_chainTilde_sum_obs`, `circ_chainM_sum_obs`: `M̃` and `M` are additive in one interior
  observable (induction through `Split.chainTilde_eq`, locality `Evol.chainTilde_congr`).
* `circ_ward_mChain_mid` (`M`-part): `Split.WardStatement` at the interior index `j+1` applied to
  the nonzero extension `Evol.mExt`, transported back by locality.
* **`circ_wardMid`**: the identity for `𝒳`; **`circ_wardMid_norm`**:
  `‖Σ_b 𝒳(x[j ↦ b])‖ ≤ (2η_t)⁻¹ (‖𝒳^{σ \ σ_{j+1}}(x \ x_j)‖ + ‖𝒳^{σ \ σ_j}(x \ x_j)‖)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Evol
open scoped ComplexConjugate

variable {N : ℕ}

/-!
### `Fin.removeNth` and lists
-/

theorem circ_removeNth_lt {α : Type*} {K : ℕ} (p : Fin (K + 2)) (f : Fin (K + 2) → α)
    (i : Fin (K + 1)) (h : (i : ℕ) < p) : Fin.removeNth p f i = f i.castSucc := by
  rw [Fin.removeNth, Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]

theorem circ_removeNth_ge {α : Type*} {K : ℕ} (p : Fin (K + 2)) (f : Fin (K + 2) → α)
    (i : Fin (K + 1)) (h : (p : ℕ) ≤ i) : Fin.removeNth p f i = f i.succ := by
  rw [Fin.removeNth, Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h)]

/-- The product of a list of length `K+1` that agrees with `ofFn f` except that the two entries
`j, j+1` are merged into `c`. -/
theorem circ_ofFn_prod_drop {M : Type*} [Monoid M] {K : ℕ} (f : Fin (K + 2) → M)
    (g : Fin (K + 1) → M) (j : Fin (K + 1)) (c : M)
    (hlt : ∀ i : Fin (K + 1), (i : ℕ) < j → g i = f i.castSucc) (heq : g j = c)
    (hgt : ∀ i : Fin (K + 1), (j : ℕ) < i → g i = f i.succ) :
    (List.ofFn g).prod =
      ((List.ofFn f).take j).prod * c * ((List.ofFn f).drop ((j : ℕ) + 2)).prod := by
  have hj := j.isLt
  have hL : List.ofFn g = (List.ofFn f).take j ++ c :: (List.ofFn f).drop ((j : ℕ) + 2) := by
    refine List.ext_getElem (by simp; omega) fun q h1 h2 => ?_
    simp only [List.length_ofFn] at h1
    rw [List.getElem_ofFn, List.getElem_append]
    rcases lt_trichotomy q j with h | h | h
    · have hq : q < ((List.ofFn f).take j).length := by simp; omega
      rw [dite_eq_left hq, List.getElem_take, List.getElem_ofFn]
      exact hlt ⟨q, h1⟩ h
    · have hq : ¬ q < ((List.ofFn f).take j).length := by simp; omega
      have hq' : q - ((List.ofFn f).take j).length = 0 := by simp; omega
      rw [dite_eq_right hq]
      simp only [hq', List.getElem_cons_zero]
      have : (⟨q, h1⟩ : Fin (K + 1)) = j := Fin.ext h
      rw [this, heq]
    · have hq : ¬ q < ((List.ofFn f).take j).length := by simp; omega
      have hq' : q - ((List.ofFn f).take j).length = (q - j - 1) + 1 := by simp; omega
      rw [dite_eq_right hq]
      simp only [hq', List.getElem_cons_succ, List.getElem_drop, List.getElem_ofFn]
      rw [hgt ⟨q, h1⟩ h]
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  rw [hL, List.prod_append, List.prod_cons, mul_assoc]

/-!
### The `G`-part
-/

section GPart

variable {K : ℕ}

theorem circ_slotProd_eq_segs {ι : Type} [Fintype ι] [DecidableEq ι]
    (B R : Fin (K + 2) → Matrix ι ι ℂ) (B' R' : Fin (K + 1) → Matrix ι ι ℂ) (j : Fin (K + 1))
    (c : Matrix ι ι ℂ)
    (hlt : ∀ i : Fin (K + 1), (i : ℕ) < j → R' i * B' i = R i.castSucc * B i.castSucc)
    (heq : R' j * B' j = c)
    (hgt : ∀ i : Fin (K + 1), (j : ℕ) < i → R' i * B' i = R i.succ * B i.succ) :
    slotProd B' R' = segProd B R 0 j * c * segProd B R ((j : ℕ) + 2) (K + 2) := by
  have hk : (slotList B R).take (K + 2) = slotList B R :=
    List.take_of_length_le (by simp [length_slotList])
  rw [slotProd, slotList, segProd, segProd, List.drop_zero, hk]
  exact circ_ofFn_prod_drop (fun l => R l * B l) (fun l => R' l * B' l) j c hlt heq hgt

/-- **The `G`-part of the interior Ward reduction**: for Hermitian `H`, `Im z > 0`, `t ≤ 1`,
stochastic symmetric `S` and `σ_j ≠ σ_{j+1}`,
`Σ_b G_{[1,K+2]}(x[j ↦ b]) = (z_j - z_{j+1})⁻¹ (G^{σ \ σ_{j+1}}(x \ x_j) - G^{σ \ σ_j}(x \ x_j))`
(averaged slots, as matrices). -/
theorem circ_ward_gChain_mid {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {z : ℂ}
    (hz : 0 < z.im) (σ : Fin (K + 2) → Bool) (j : Fin (K + 1))
    (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ} (ht : t ≤ 1)
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ∑ b, gChain (patZ z σ t) (avSlots S (update x j.castSucc b)) H =
      (patZ z σ t j.castSucc - patZ z σ t j.succ)⁻¹ •
        (gChain (patZ z (Fin.removeNth j.succ σ) t) (avSlots S (Fin.removeNth j.castSucc x)) H -
          gChain (patZ z (Fin.removeNth j.castSucc σ) t)
            (avSlots S (Fin.removeNth j.castSucc x)) H) := by
  set R : Fin (K + 2) → Matrix (Fin N) (Fin N) ℂ :=
    fun l => (H - patZ z σ t l • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ with hR
  set B := avSlots S x with hB
  set A := segProd B R 0 j.castSucc
  set D := segProd B R ((j : ℕ) + 2) (K + 2)
  have hu : ∀ l, IsUnit (H - patZ z σ t l • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    fun l => isUnit_det_herm_sub hH (patZ_im_ne_zero hz σ ht l)
  have hres := res_mul_res H (hu j.castSucc) (hu j.succ) (patZ_ne hz σ ht hσ)
  -- the left side
  have hL : ∀ b, gChain (patZ z σ t) (avSlots S (update x j.castSucc b)) H =
      A * (R j.castSucc * obsMat S b) * segProd B R ((j.castSucc : ℕ) + 1) (K + 2) := by
    intro b
    rw [gChain, avSlots_update, slotProd_updateB]
  have htop : segProd B R ((j.castSucc : ℕ) + 1) (K + 2) = R j.succ * B j.succ * D := by
    have h := segProd_top_succ B R j.succ
    simp only [Fin.val_succ] at h
    simp only [Fin.val_castSucc, D]
    rw [h]
  have hsum : ∑ b, gChain (patZ z σ t) (avSlots S (update x j.castSucc b)) H =
      A * (R j.castSucc * R j.succ) * B j.succ * D := by
    simp only [hL]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, sum_obsMat hS, Matrix.mul_one,
      htop]
    simp only [Matrix.mul_assoc]
  -- the two shortened chains
  have hA : segProd B R 0 (j : ℕ) = A := by simp only [A, Fin.val_castSucc]
  have h1 : gChain (patZ z (Fin.removeNth j.succ σ) t) (avSlots S (Fin.removeNth j.castSucc x))
      H = A * (R j.castSucc * B j.succ) * D := by
    rw [gChain, ← hA]
    refine circ_slotProd_eq_segs B R _ _ j _ (fun i hi => ?_) ?_ (fun i hi => ?_)
    · simp only [avSlots, patZ, B, R]
      rw [circ_removeNth_lt _ _ _ (by simp; omega), circ_removeNth_lt _ _ _ (by simp; omega)]
    · simp only [avSlots, patZ, B, R]
      rw [circ_removeNth_lt _ _ _ (by simp), circ_removeNth_ge _ _ _ (by simp)]
    · simp only [avSlots, patZ, B, R]
      rw [circ_removeNth_ge _ _ _ (by simp; omega), circ_removeNth_ge _ _ _ (by simp; omega)]
  have h2 : gChain (patZ z (Fin.removeNth j.castSucc σ) t)
      (avSlots S (Fin.removeNth j.castSucc x)) H = A * (R j.succ * B j.succ) * D := by
    rw [gChain, ← hA]
    refine circ_slotProd_eq_segs B R _ _ j _ (fun i hi => ?_) ?_ (fun i hi => ?_)
    · simp only [avSlots, patZ, B, R]
      rw [circ_removeNth_lt _ _ _ (by simp; omega), circ_removeNth_lt _ _ _ (by simp; omega)]
    · simp only [avSlots, patZ, B, R]
      rw [circ_removeNth_ge _ _ _ (by simp), circ_removeNth_ge _ _ _ (by simp)]
    · simp only [avSlots, patZ, B, R]
      rw [circ_removeNth_ge _ _ _ (by simp; omega), circ_removeNth_ge _ _ _ (by simp; omega)]
  rw [hsum, h1, h2, hres]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    smul_sub]
  rfl

end GPart

/-!
### Additivity of `M̃` in one observable
-/

theorem circ_chainTilde_sum_obs (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) {ι : Type*} (s : Finset ι) (B : ι → Fin N → ℂ) (p : ℕ) (n : ℕ) :
    ∀ j l, l - j = n → j ≤ p → p < l →
      ∑ b ∈ s, Split.chainTilde σ S m (update A p (B b)) j l =
        Split.chainTilde σ S m (update A p (∑ b ∈ s, B b)) j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn hjp hpl
  have hjl : j < l := by omega
  have hE : ∀ A' : ℕ → Fin N → ℂ, Split.chainTilde σ S m A' j l =
      Split.stabOp σ S (m j * m l) *ᵥ (A' j * Split.chainTilde σ S m A' (j + 1) l +
        ∑ i ∈ Finset.Ioo j l, ((σ : ℂ) * m j * m i) •
          (Split.selfEnergy S (Split.chainTilde σ S m A' j i) *
            Split.chainTilde σ S m A' i l)) := fun A' => by
    rw [Split.chainTilde_eq, ite_eq_left hjl]
  simp only [hE]
  rw [← Matrix.mulVec_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases hp : p = j
    · subst hp
      have hc : ∀ C : Fin N → ℂ, Split.chainTilde σ S m (update A p C) (p + 1) l =
          Split.chainTilde σ S m A (p + 1) l := fun C =>
        chainTilde_congr σ S m (l - (p + 1)) (p + 1) l rfl fun q hq _ =>
          update_of_ne (by omega) _ _
      simp only [hc, update_self]
      rw [Finset.sum_mul]
    · have hA : ∀ C : Fin N → ℂ, update A p C j = A j := fun C =>
        update_of_ne (Ne.symm hp) _ _
      simp only [hA]
      rw [← Finset.mul_sum, ih (l - (j + 1)) (by omega) (j + 1) l rfl (by omega) hpl]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    rw [← Finset.smul_sum]
    congr 1
    by_cases hpi : p < i
    · have hc : ∀ C : Fin N → ℂ, Split.chainTilde σ S m (update A p C) i l =
          Split.chainTilde σ S m A i l := fun C =>
        chainTilde_congr σ S m (l - i) i l rfl fun q hq _ => update_of_ne (by omega) _ _
      simp only [hc]
      rw [← Finset.sum_mul]
      congr 1
      unfold Split.selfEnergy
      rw [← Matrix.mulVec_sum, ih (i - j) (by omega) j i rfl hjp hpi]
    · have hc : ∀ C : Fin N → ℂ, Split.chainTilde σ S m (update A p C) j i =
          Split.chainTilde σ S m A j i := fun C =>
        chainTilde_congr σ S m (i - j) j i rfl fun q _ hq => update_of_ne (by omega) _ _
      simp only [hc]
      rw [← Finset.mul_sum, ih (l - i) (by omega) i l rfl (by omega) hpl]

theorem circ_chainM_sum_obs (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) {ι : Type*} (s : Finset ι) (B : ι → Fin N → ℂ) {p j l : ℕ}
    (hjp : j ≤ p) (hpl : p < l) :
    ∑ b ∈ s, Split.chainM σ S m (update A p (B b)) j l =
      Split.chainM σ S m (update A p (∑ b ∈ s, B b)) j l := by
  simp only [Split.chainM]
  rw [← Finset.smul_sum, circ_chainTilde_sum_obs σ S m A s B p (l - j) j l rfl hjp hpl]

/-!
### Index bookkeeping for the `M`-part
-/

theorem circ_patM_removeNth (z : ℂ) {K : ℕ} (σ : Fin (K + 2) → Bool) (r : Fin (K + 2)) {q : ℕ}
    (h1 : 1 ≤ q) (h2 : q ≤ K + 1) :
    patM z (Fin.removeNth r σ) q = if q ≤ r then patM z σ q else patM z σ (q + 1) := by
  have hL : patM z (Fin.removeNth r σ) q =
      VS.patConj (Fin.removeNth r σ ⟨q - 1, by omega⟩) (semicircleM z) := by
    unfold patM
    rw [dite_eq_left ⟨h1, h2⟩]
  rw [hL]
  split_ifs with h
  · rw [circ_removeNth_lt r σ ⟨q - 1, by omega⟩ (by simp; omega)]
    unfold patM
    rw [dite_eq_left ⟨h1, by omega⟩]
    rfl
  · rw [circ_removeNth_ge r σ ⟨q - 1, by omega⟩ (by simp; omega)]
    unfold patM
    rw [dite_eq_left ⟨by omega, by omega⟩]
    congr 2
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

theorem circ_obsSeq_removeNth (S : Matrix (Fin N) (Fin N) ℝ) {K : ℕ} (x : Fin (K + 2) → Fin N)
    (r : Fin (K + 2)) {q : ℕ} (h2 : q ≤ K + 1) :
    obsSeq S (Fin.removeNth r x) q = if q ≤ r then obsSeq S x q else obsSeq S x (q + 1) := by
  by_cases h1 : 1 ≤ q
  · have hL : obsSeq S (Fin.removeNth r x) q =
        Split.rowObs S (Fin.removeNth r x ⟨q - 1, by omega⟩) := by
      unfold obsSeq
      rw [dite_eq_left ⟨h1, h2⟩]
    rw [hL]
    split_ifs with h
    · rw [circ_removeNth_lt r x ⟨q - 1, by omega⟩ (by simp; omega)]
      unfold obsSeq
      rw [dite_eq_left ⟨h1, by omega⟩]
      rfl
    · rw [circ_removeNth_ge r x ⟨q - 1, by omega⟩ (by simp; omega)]
      unfold obsSeq
      rw [dite_eq_left ⟨by omega, by omega⟩]
      congr 2
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · unfold obsSeq
    rw [dite_eq_right (by omega), ite_eq_left (by omega), dite_eq_right (by omega)]

theorem circ_sum_rowObs {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) :
    ∑ b, Split.rowObs S b = fun _ => (1 : ℂ) := by
  funext a
  rw [Finset.sum_apply]
  simp only [Split.rowObs]
  rw [← Complex.ofReal_sum]
  have : ∑ b, S b a = 1 := by
    rw [← hS.rowSum a]
    exact Finset.sum_congr rfl fun b _ => hS.symm b a
  rw [this, Complex.ofReal_one]

/-!
### The `M`-part
-/

/-- **The `M`-part of the interior Ward reduction** (the Ward identity for `M` at the interior
junction `(z_j, z_{j+1})`). **Conditional on `Split.WardStatement`.** For stochastic symmetric `S`,
`Im z ≠ 0`, `t ∈ [0,1]` and `σ_j ≠ σ_{j+1}`:
`Σ_b M_{[1,K+2]}(x[j ↦ b]) = (z_j - z_{j+1})⁻¹ (M^{σ \ σ_{j+1}}(x \ x_j) - M^{σ \ σ_j}(x \ x_j))`
(as diagonals, `z_i = zParam t m_i`). -/
theorem circ_ward_mChain_mid (hW : Split.WardStatement) (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0) {K : ℕ} (σ : Fin (K + 2) → Bool)
    (j : Fin (K + 1)) (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ b, P.mChain σ (update x j.castSucc b) t =
      (Split.zParam t (patM P.z σ ((j : ℕ) + 1)) - Split.zParam t (patM P.z σ ((j : ℕ) + 2)))⁻¹ •
        (P.mChain (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t -
          P.mChain (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t) := by
  have hprof := stochasticSymm_iff_profileHyp.mp hS
  have hj := j.isLt
  set me := mExt P.z σ with hme
  set Ae := update (obsSeq P.S x) ((j : ℕ) + 1) (fun _ => (1 : ℂ)) with hAe
  -- additivity in the observable `A_{j+1}`
  have hlin : ∑ b, P.mChain σ (update x j.castSucc b) t =
      Split.chainM t P.S (patM P.z σ) Ae 1 (K + 2) := by
    simp only [PsiData.mChain, obsSeq_update, Fin.val_castSucc]
    rw [circ_chainM_sum_obs t P.S _ _ Finset.univ _ (by omega) (by omega), circ_sum_rowObs hS]
  have hext : Split.chainM t P.S (patM P.z σ) Ae 1 (K + 2) =
      Split.chainM t P.S me Ae 1 (K + 2) :=
    chainM_congr_m t P.S _ fun q hq hq' => (mExt_eq σ hq hq').symm
  have hme1 : me ((j : ℕ) + 1) = patM P.z σ ((j : ℕ) + 1) := mExt_eq σ (by omega) (by omega)
  have hme2 : me ((j : ℕ) + 2) = patM P.z σ ((j : ℕ) + 2) := mExt_eq σ (by omega) (by omega)
  have hne : me ((j : ℕ) + 1) ≠ me ((j : ℕ) + 1 + 1) := by
    rw [show (j : ℕ) + 1 + 1 = (j : ℕ) + 2 by omega, hme1, hme2]
    have e1 := patM_of_mem P.z σ j.castSucc
    have e2 := patM_of_mem P.z σ j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
    rw [e1, show (j : ℕ) + 2 = (j : ℕ) + 1 + 1 by omega, e2]
    intro h
    apply hσ
    have hm : semicircleM P.z ≠ conj (semicircleM P.z) := by
      intro hc
      have := congrArg Complex.im hc
      simp only [Complex.conj_im] at this
      have hy := semicircleM_same_sign hz
      have h0 : (semicircleM P.z).im = 0 := by linarith
      rw [h0, zero_mul] at hy
      exact lt_irrefl 0 hy
    cases h1 : σ j.castSucc <;> cases h0 : σ j.succ <;> simp_all [VS.patConj]
  have hward := hW N P.S hprof t ht me (norm_mExt_lt_one hz σ) (mExt_ne_zero P.z σ) Ae (K + 2)
    ((j : ℕ) + 1) (by omega) (by omega) (by omega) (by rw [hAe, update_self]) hne
  have hdA : ∀ q, 1 ≤ q → q < K + 1 →
      Split.dropAt ((j : ℕ) + 1) Ae q = obsSeq P.S (Fin.removeNth j.castSucc x) q := by
    intro q _ hq'
    rw [circ_obsSeq_removeNth P.S x j.castSucc (by omega)]
    simp only [Split.dropAt, Fin.val_castSucc, hAe]
    split_ifs with h1 h2 h2
    · rw [update_of_ne (by omega)]
    · omega
    · omega
    · rw [update_of_ne (by omega)]
  have hM1 : Split.chainM t P.S (Split.dropAt ((j : ℕ) + 1 + 1) me) (Split.dropAt ((j : ℕ) + 1) Ae)
      1 (K + 2 - 1) = P.mChain (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t := by
    rw [PsiData.mChain, show K + 2 - 1 = K + 1 by omega]
    calc _ = Split.chainM t P.S (patM P.z (Fin.removeNth j.succ σ))
          (Split.dropAt ((j : ℕ) + 1) Ae) 1 (K + 1) :=
          chainM_congr_m t P.S _ fun q hq hq' => by
            rw [circ_patM_removeNth P.z σ j.succ hq hq']
            simp only [Split.dropAt, Fin.val_succ, hme]
            split_ifs with h1 h2 h2
            · exact mExt_eq σ hq (by omega)
            · omega
            · omega
            · exact mExt_eq σ (by omega) (by omega)
      _ = _ := chainM_congr t P.S _ hdA
  have hM2 : Split.chainM t P.S (Split.dropAt ((j : ℕ) + 1) me) (Split.dropAt ((j : ℕ) + 1) Ae)
      1 (K + 2 - 1) = P.mChain (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t := by
    rw [PsiData.mChain, show K + 2 - 1 = K + 1 by omega]
    calc _ = Split.chainM t P.S (patM P.z (Fin.removeNth j.castSucc σ))
          (Split.dropAt ((j : ℕ) + 1) Ae) 1 (K + 1) :=
          chainM_congr_m t P.S _ fun q hq hq' => by
            rw [circ_patM_removeNth P.z σ j.castSucc hq hq']
            simp only [Split.dropAt, Fin.val_castSucc, hme]
            split_ifs with h1 h2 h2
            · exact mExt_eq σ hq (by omega)
            · omega
            · omega
            · exact mExt_eq σ (by omega) (by omega)
      _ = _ := chainM_congr t P.S _ hdA
  rw [hlin, hext, hward, hM1, hM2, hme1, show (j : ℕ) + 1 + 1 = (j : ℕ) + 2 by omega, hme2]

/-!
### The Ward reduction for `𝒳`
-/

/-- **Interior Ward reduction.** **Conditional on `Split.WardStatement`** (`hW`). For stochastic
symmetric `S`, `Im z > 0`, `t ∈ [0,1]`, Hermitian `H`, a chain of length `K+2` and an interior
slot `j` with `σ_j ≠ σ_{j+1}`:
`Σ_b 𝒳(x[j ↦ b]) = (z_j - z_{j+1})⁻¹ (𝒳^{σ \ σ_{j+1}}(x \ x_j) - 𝒳^{σ \ σ_j}(x \ x_j))`. -/
theorem circ_wardMid (hW : Split.WardStatement) (P : PsiData N) (hS : StochasticSymm P.S)
    (hz : 0 < P.z.im) {K : ℕ} (σ : Fin (K + 2) → Bool) (j : Fin (K + 1))
    (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ∑ b, P.avErr σ (update x j.castSucc b) t H =
      (patZ P.z σ t j.castSucc - patZ P.z σ t j.succ)⁻¹ *
        (P.avErr (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t H -
          P.avErr (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t H) := by
  have hj := j.isLt
  have hO : ∀ b, obsSeq P.S (update x j.castSucc b) (K + 2) = obsSeq P.S x (K + 2) := by
    intro b
    rw [obsSeq_update, update_of_ne (by simp; omega)]
  have hO' : obsSeq P.S (Fin.removeNth j.castSucc x) (K + 1) = obsSeq P.S x (K + 2) := by
    rw [circ_obsSeq_removeNth P.S x j.castSucc le_rfl, ite_eq_right (by simp; omega)]
  have hG := circ_ward_gChain_mid hS hz σ j hσ x ht.2 hH
  have hM := circ_ward_mChain_mid hW P hS hz.ne' σ j hσ x ht
  have e1 : Split.zParam t (patM P.z σ ((j : ℕ) + 1)) = patZ P.z σ t j.castSucc := by
    have h := zParam_patM P.z σ t j.castSucc
    simpa only [Fin.val_castSucc] using h
  have e2 : Split.zParam t (patM P.z σ ((j : ℕ) + 2)) = patZ P.z σ t j.succ := by
    have h := zParam_patM P.z σ t j.succ
    simpa only [Fin.val_succ, show (j : ℕ) + 1 + 1 = (j : ℕ) + 2 by omega] using h
  rw [e1, e2] at hM
  simp only [PsiData.avErr, hO, hO']
  rw [Finset.sum_sub_distrib, ← trace_sum, hG, trace_smul, smul_eq_mul]
  have hMs : ∑ b, ∑ a, P.mChain σ (update x j.castSucc b) t a * obsSeq P.S x (K + 2) a =
      ∑ a, (∑ b, P.mChain σ (update x j.castSucc b) t) a * obsSeq P.S x (K + 2) a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_apply, Finset.sum_mul]
  have key : ∑ a, ((patZ P.z σ t j.castSucc - patZ P.z σ t j.succ)⁻¹ •
      (P.mChain (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t -
        P.mChain (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t)) a *
          obsSeq P.S x (K + 2) a =
      (patZ P.z σ t j.castSucc - patZ P.z σ t j.succ)⁻¹ *
        (∑ a, P.mChain (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t a *
            obsSeq P.S x (K + 2) a -
          ∑ a, P.mChain (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t a *
            obsSeq P.S x (K + 2) a) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hMs, hM, trace_sub, key]
  ring

/-- **Interior Ward reduction, size form**: under the hypotheses of `circ_wardMid`,
`‖Σ_b 𝒳(x[j ↦ b])‖ ≤ (2η_t)⁻¹ (‖𝒳^{σ \ σ_{j+1}}(x \ x_j)‖ + ‖𝒳^{σ \ σ_j}(x \ x_j)‖)`.
**Conditional on `Split.WardStatement`.** -/
theorem circ_wardMid_norm (hW : Split.WardStatement) (P : PsiData N) (hS : StochasticSymm P.S)
    (hz : 0 < P.z.im) {K : ℕ} (σ : Fin (K + 2) → Bool) (j : Fin (K + 1))
    (hσ : σ j.castSucc ≠ σ j.succ) (x : Fin (K + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ‖∑ b, P.avErr σ (update x j.castSucc b) t H‖ ≤
      (2 * vsHeight P.z t)⁻¹ *
        (‖P.avErr (Fin.removeNth j.succ σ) (Fin.removeNth j.castSucc x) t H‖ +
          ‖P.avErr (Fin.removeNth j.castSucc σ) (Fin.removeNth j.castSucc x) t H‖) := by
  rw [circ_wardMid hW P hS hz σ j hσ x ht hH, norm_mul, norm_inv]
  have hη := vsHeight_pos hz ht.2
  have h2 := two_eta_le_norm_patZ_sub (z := P.z) σ (t := t) hσ
  exact mul_le_mul ((inv_le_inv₀ (by linarith) (by positivity)).mpr h2) (norm_sub_le _ _)
    (norm_nonneg _) (inv_nonneg.mpr (by positivity))

end BlockBand.Native.ErdosRiabov.Circ
