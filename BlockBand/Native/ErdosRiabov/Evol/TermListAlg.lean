module

public import BlockBand.Native.ErdosRiabov.Evol.Main

/-!
# Algebra for the term list of the forcing

* Slot products: `gHead B R i = G_{[0,i]}`, `gSeg B R i j = G_{[i,j]}`, `gTail B R j =
  G_j B_j G_{j+1} ⋯ B_{k-1}` (0-based), with `pairIns B R T i j = gHead i · T(gSeg i j) · gTail j`
  (`pairIns_eq`); a slot update of the observables `B` at `i` is `gHead i · X · gTail (i+1)`
  (`slotProd_updateB_adj`) or, at the last slot, `gHead i · X` (`slotProd_updateB_last`).
* `bandSelfEnergy_eq_sum`: `𝒮[X] = ∑_q X_qq S^q` for symmetric `S`.
* Terms of the deterministic chain: `chainM_adj` (`M_{[j,j+1]} = m_j m_{j+1} (1 - σ m_j m_{j+1} S)⁻¹ A_j`, from the
  recursion itself), `chainTilde_congr` (`M_{[j,l]}` only reads `A_j, …, A_{l-1}`),
  `stabOp_symm` (symmetric resolvent).
* `sum_Icc_Ioc_reindex`: the pair sums `∑_{1 ≤ i < j ≤ k}` of `Split.DerivStatement` as sums over
  `Fin k` pairs.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open Matrix Finset Function
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi

variable {N k : ℕ}

/-!
### Slot products
-/

section Slots

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `G_{[0,i]} = G_0 B_0 ⋯ B_{i-1} G_i`. -/
def gHead (B R : Fin k → Matrix ι ι ℂ) (i : Fin k) : Matrix ι ι ℂ := segProd B R 0 i * R i

/-- `G_{[i,j]} = G_i B_i ⋯ B_{j-1} G_j`. -/
def gSeg (B R : Fin k → Matrix ι ι ℂ) (i j : Fin k) : Matrix ι ι ℂ := segProd B R i j * R j

/-- `G_j B_j G_{j+1} ⋯ G_{k-1} B_{k-1}`. -/
def gTail (B R : Fin k → Matrix ι ι ℂ) (j : Fin k) : Matrix ι ι ℂ :=
  R j * B j * segProd B R ((j : ℕ) + 1) k

theorem pairIns_eq (B R : Fin k → Matrix ι ι ℂ) (T : Matrix ι ι ℂ → Matrix ι ι ℂ)
    (i j : Fin k) : pairIns B R T i j = gHead B R i * T (gSeg B R i j) * gTail B R j := rfl

theorem gSeg_self (B R : Fin k → Matrix ι ι ℂ) (j : Fin k) : gSeg B R j j = R j := by
  rw [gSeg, segProd_self, Matrix.one_mul]

omit [DecidableEq ι] in
theorem slotList_updateB (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) (X : Matrix ι ι ℂ) :
    slotList (update B j X) M = (slotList B M).set j (M j * X) := by
  have h : (fun l => M l * update B j X l) = update (fun l => M l * B l) j (M j * X) := by
    funext l
    exact apply_update (fun l (b : Matrix ι ι ℂ) => M l * b) B j X l
  unfold slotList
  rw [h, ofFn_update_eq_set]

/-- Updating the observable of slot `j`. -/
theorem slotProd_updateB (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) (X : Matrix ι ι ℂ) :
    slotProd (update B j X) M = segProd B M 0 j * (M j * X) * segProd B M ((j : ℕ) + 1) k := by
  have hlt : (j : ℕ) < (slotList B M).length := by simp [length_slotList]
  have hk : (slotList B M).take k = slotList B M :=
    List.take_of_length_le (by simp [length_slotList])
  rw [slotProd, slotList_updateB, List.prod_set, ite_eq_left hlt]
  simp only [segProd, List.drop_zero, hk]

theorem segProd_top_succ (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) :
    segProd B M j k = M j * B j * segProd B M ((j : ℕ) + 1) k := by
  have hk : (slotList B M).take k = slotList B M :=
    List.take_of_length_le (by simp [length_slotList])
  have hlen : (j : ℕ) < (slotList B M).length := by simp [length_slotList]
  rw [segProd, segProd, hk, List.drop_eq_getElem_cons hlen, List.prod_cons]
  congr 1
  simp [slotList]

theorem slotProd_updateB_adj (B M : Fin k → Matrix ι ι ℂ) {i j : Fin k}
    (hij : (j : ℕ) = i + 1) (X : Matrix ι ι ℂ) :
    slotProd (update B i X) M = gHead B M i * X * gTail B M j := by
  rw [slotProd_updateB, ← hij, segProd_top_succ B M j, gHead, gTail]
  simp only [Matrix.mul_assoc]

theorem slotProd_updateB_last (B M : Fin k → Matrix ι ι ℂ) {i : Fin k} (hi : (i : ℕ) + 1 = k)
    (X : Matrix ι ι ℂ) : slotProd (update B i X) M = gHead B M i * X := by
  rw [slotProd_updateB, hi, segProd_self, Matrix.mul_one, gHead, Matrix.mul_assoc]

end Slots

/-!
### The self-energy as a sum over sites
-/

theorem bandSelfEnergy_eq_sum {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a b, S a b = S b a)
    (X : Matrix (Fin N) (Fin N) ℂ) :
    bandSelfEnergy S X = ∑ q, X q q • obsMat S q := by
  ext a c
  rw [Matrix.sum_apply]
  simp only [bandSelfEnergy, obsMat, Matrix.smul_apply, Matrix.diagonal_apply, Split.rowObs,
    smul_eq_mul]
  by_cases hac : a = c
  · subst hac
    simp only [ite_true]
    exact Finset.sum_congr rfl fun q _ => by rw [hS a q, mul_comm]
  · simp [hac]

theorem pairIns_bandSelfEnergy {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a b, S a b = S b a)
    (B R : Fin k → Matrix (Fin N) (Fin N) ℂ) (i j : Fin k) :
    pairIns B R (bandSelfEnergy S) i j =
      ∑ q, gSeg B R i j q q • (gHead B R i * obsMat S q * gTail B R j) := by
  rw [pairIns_eq, bandSelfEnergy_eq_sum hS, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-!
### `M`-terms
-/

theorem chainTilde_self (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) (j : ℕ) : Split.chainTilde σ S m A j j = fun _ => 1 := by
  rw [Split.chainTilde_eq, ite_eq_right (lt_irrefl j)]

/-- `M_{[j,j+1]} = m_j m_{j+1} (1 - σ m_j m_{j+1} S)⁻¹ A_j` (directly from the recursion). -/
theorem chainM_adj (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin N → ℂ)
    (j : ℕ) :
    Split.chainM σ S m A j (j + 1) =
      (m j * m (j + 1)) • (Split.stabOp σ S (m j * m (j + 1)) *ᵥ A j) := by
  have hI : Finset.Icc j (j + 1) = {j, j + 1} := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hO : Finset.Ioo j (j + 1) = ∅ := by
    ext i
    simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]
    omega
  rw [Split.chainM, Split.chainTilde_eq, ite_eq_left (Nat.lt_succ_self j), hO,
    Finset.sum_empty, add_zero, chainTilde_self, hI, Finset.prod_pair (by omega)]
  congr 2
  funext a
  simp

/-- `M̃_{[j,l]}` only reads the observables `A_j, …, A_{l-1}`. -/
theorem chainTilde_congr (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    {A A' : ℕ → Fin N → ℂ} (n : ℕ) :
    ∀ j l, l - j = n → (∀ p, j ≤ p → p < l → A p = A' p) →
      Split.chainTilde σ S m A j l = Split.chainTilde σ S m A' j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn hA
  rw [Split.chainTilde_eq σ S m A j l, Split.chainTilde_eq σ S m A' j l]
  by_cases hjl : j < l
  · simp only [hjl, ite_true]
    have h1 := ih (l - (j + 1)) (by omega) (j + 1) l rfl fun p hp hp' => hA p (by omega) hp'
    rw [hA j le_rfl hjl, h1]
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    rw [ih (i - j) (by omega) j i rfl fun p hp hp' => hA p hp (by omega),
      ih (l - i) (by omega) i l rfl fun p hp hp' => hA p (by omega) hp']
  · simp only [hjl, ite_false]

theorem chainM_congr (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    {A A' : ℕ → Fin N → ℂ} {j l : ℕ} (hA : ∀ p, j ≤ p → p < l → A p = A' p) :
    Split.chainM σ S m A j l = Split.chainM σ S m A' j l := by
  rw [Split.chainM, Split.chainM, chainTilde_congr σ S m (l - j) j l rfl hA]

theorem stabOp_symm {S : Matrix (Fin N) (Fin N) ℝ} (hS : ∀ a b, S a b = S b a) (σ : ℝ)
    (c : ℂ) (a b : Fin N) : Split.stabOp σ S c a b = Split.stabOp σ S c b a := by
  have hP : (Split.profileC S)ᵀ = Split.profileC S := by
    ext x y
    simp [Split.profileC, hS y x]
  have hT : (Split.stabOp σ S c)ᵀ = Split.stabOp σ S c := by
    rw [Split.stabOp, Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.transpose_smul, hP]
  have h := congrFun (congrFun hT b) a
  rwa [Matrix.transpose_apply] at h

/-!
### Reindexing the pair sums
-/

theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, g i = ∑ i ∈ Finset.range k, g (i + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_Ioc_eq_sum_Icc_ite {M : Type*} [AddCommMonoid M] (h : ℕ → M) (i k : ℕ) :
    ∑ j ∈ Finset.Ioc i k, h j = ∑ j ∈ Finset.Icc 1 k, if i < j then h j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The pair sums of `Split.DerivStatement` over `Fin k` pairs `i < j` (0-based). -/
theorem sum_Icc_Ioc_reindex {M : Type*} [AddCommMonoid M] (f : ℕ → ℕ → M) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, ∑ j ∈ Finset.Ioc i k, f i j =
      ∑ j : Fin k, ∑ i with i < j, f ((i : ℕ) + 1) ((j : ℕ) + 1) := by
  simp_rw [sum_Ioc_eq_sum_Icc_ite, sum_Icc_one_eq_range]
  have hR : ∀ j : Fin k, (∑ i with i < j, f ((i : ℕ) + 1) ((j : ℕ) + 1)) =
      ∑ i ∈ Finset.range k, if i < (j : ℕ) then f (i + 1) ((j : ℕ) + 1) else 0 := by
    intro j
    rw [Finset.sum_filter]
    exact Fin.sum_univ_eq_sum_range (fun i => if i < (j : ℕ) then f (i + 1) ((j : ℕ) + 1)
      else 0) k
  simp_rw [hR]
  rw [Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ Finset.range k,
    if i < j then f (i + 1) (j + 1) else 0) k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [add_lt_add_iff_right]

end BlockBand.Native.ErdosRiabov.Evol
