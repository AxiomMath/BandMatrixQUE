module

public import BlockBand.Native.ErdosRiabov.MBound.Evol
public import BlockBand.Native.ErdosRiabov.MBound.Ward
public import BlockBand.Native.ErdosRiabov.Contr.Local

/-!
# The `M`-forcing bound

The `M`-forcing `F_M` is bounded by the isotropic and averaged `M`-bounds of shorter lengths.

* `mb_chainTilde_shift`, `mb_chainM_shift`: `M_{[j+s, l+s]}` with data `m, A` is `M_{[j,l]}`
  with the shifted data `m(·+s)`, `A(·+s)`;
* `mb_aM_eq`: the segment `(M_{[i+1,j+1]})_{qq}` (`Evol.aM`) is the pattern `M`-term of the
  sub-pattern `(σ_i, …, σ_j)` at the sites `(x_i, …, x_j)` (`mbSubPat`, `mbSubSites`);
* `mb_bMav_eq`: `Tr[M^{(q)}_{[1,i],[j,k]} S^{x_k}]` (`Evol.bMav`) is `Evol.avM` of the glued
  pattern `(σ_0..σ_i, σ_j..σ_{k-1})` at the sites `(x_0..x_{i-1}, q, x_j..x_{k-1})`
  (`mbGluePat`, `mbGlueSites`);
* **`mbFM_bound`**: if `IsoB(p+1, I(p+1))` and `AvB(k-p+1, A(k-p+1))` for `2 ≤ p ≤ k-2`, then
  `|F_M(x)| ≤ (C_wc/η) · Σ_{i<j, 2 ≤ j-i ≤ k-2} I(j-i+1) A(k-(j-i)+1) · L s^av_k(x)` (i.e.
  `F_k η⁻¹ L s^av`, the pair sum being `Σ_p (k-p) I_{p+1} A_{k-p+1}`), via the local contraction
  `Contr.avInsertion_vs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open scoped BigOperators

variable {N : ℕ}

/-!
## Shifts of the recursion
-/

theorem mb_chainTilde_shift (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) (s n : ℕ) :
    ∀ j l, l - j = n → Split.chainTilde σ S m A (j + s) (l + s) =
      Split.chainTilde σ S (fun p => m (p + s)) (fun p => A (p + s)) j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn
  rw [Split.chainTilde_eq σ S m A, Split.chainTilde_eq σ S _ _ j l]
  by_cases hjl : j < l
  · rw [ite_eq_left (by omega), ite_eq_left hjl]
    rw [show j + s + 1 = (j + 1) + s by ring, ih (l - (j + 1)) (by omega) (j + 1) l rfl,
      ← Finset.map_add_right_Ioo, Finset.sum_map]
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    simp only [addRightEmbedding_apply]
    rw [ih (i - j) (by omega) j i rfl, ih (l - i) (by omega) i l rfl]
  · rw [ite_eq_right (by omega), ite_eq_right hjl]

theorem mb_chainM_shift (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) (s j l : ℕ) :
    Split.chainM σ S m A (j + s) (l + s) =
      Split.chainM σ S (fun p => m (p + s)) (fun p => A (p + s)) j l := by
  rw [Split.chainM, Split.chainM, mb_chainTilde_shift σ S m A s (l - j) j l rfl,
    ← Finset.map_add_right_Icc, Finset.prod_map]
  rfl

/-!
## Segments and glued chains as pattern `M`-terms
-/

section Index

variable {k : ℕ}

/-- The sub-pattern `(σ_i, …, σ_j)` (length `j - i + 1`). -/
def mbSubPat (σ : Fin k → Bool) (i j : Fin k) : Fin ((j : ℕ) - i + 1) → Bool :=
  fun r => σ ⟨min ((i : ℕ) + r) (k - 1), by omega⟩

/-- The sub-sites `(x_i, …, x_j)`. -/
def mbSubSites (x : Fin k → Fin N) (i j : Fin k) : Fin ((j : ℕ) - i + 1) → Fin N :=
  fun r => x ⟨min ((i : ℕ) + r) (k - 1), by omega⟩

/-- The glued pattern `(σ_0, …, σ_i, σ_j, …, σ_{k-1})` (length `k - j + i + 1`). -/
def mbGluePat (σ : Fin k → Bool) (i j : Fin k) : Fin (k - j + i + 1) → Bool :=
  fun r => if h : (r : ℕ) ≤ i then σ ⟨r, lt_of_le_of_lt h i.isLt⟩ else
    σ ⟨min ((r : ℕ) + j - i - 1) (k - 1), by have := i.isLt; omega⟩

/-- The glued sites `(x_0, …, x_{i-1}, q, x_j, …, x_{k-1})`. -/
def mbGlueSites (x : Fin k → Fin N) (i j : Fin k) (q : Fin N) : Fin (k - j + i + 1) → Fin N :=
  fun r => if h : (r : ℕ) < i then x ⟨r, h.trans i.isLt⟩ else if (r : ℕ) = i then q else
    x ⟨min ((r : ℕ) + j - i - 1) (k - 1), by have := i.isLt; omega⟩

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)

/-- `(M_{[i+1,j+1]})_{qq}` is the pattern `M`-term of the sub-pattern. -/
theorem mb_aM_eq {i j : Fin k} (hij : i ≤ j) (q : Fin N) :
    aM P σ x t i j q = P.mChain (mbSubPat σ i j) (mbSubSites x i j) t q := by
  rw [aM, mSeg, PsiData.mChain]
  have hj := j.isLt
  have e : Split.chainM t P.S (patM P.z σ) (obsSeq P.S x) ((i : ℕ) + 1) ((j : ℕ) + 1) =
      Split.chainM t P.S (fun p => patM P.z σ (p + i)) (fun p => obsSeq P.S x (p + i)) 1
        ((j : ℕ) - i + 1) := by
    rw [← mb_chainM_shift, show 1 + (i : ℕ) = (i : ℕ) + 1 by ring,
      show (j : ℕ) - i + 1 + i = (j : ℕ) + 1 by omega]
  rw [e]
  refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)) q
  · rw [mb_patM_apply _ _ (by omega) (by omega), mb_patM_apply _ _ hp1 hp2]
    congr 2
    apply Fin.ext
    simp only
    omega
  · rw [mb_obsSeq_apply _ _ (by omega) (by omega), mb_obsSeq_apply _ _ hp1 (by omega)]
    congr 2
    apply Fin.ext
    simp only
    omega

/-- `Tr[M^{(q)}_{[1,i],[j,k]} S^{x_k}]` is `Evol.avM` of the glued pattern at the glued sites. -/
theorem mb_bMav_eq {i j : Fin k} (hij : i < j) (q : Fin N) :
    bMav P σ x t i j q = avM P (mbGluePat σ i j) (mbGlueSites x i j q) t := by
  have hj := j.isLt
  have hn : k - ((j : ℕ) + 1) + ((i : ℕ) + 1) + 1 = k - j + i + 1 := by omega
  rw [bMav, avM]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  · rw [mGlue, PsiData.mChain, hn]
    refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)) a
    · unfold Split.glueChain
      rw [mb_patM_apply _ _ hp1 hp2]
      by_cases hp : p ≤ (i : ℕ) + 1
      · rw [ite_eq_left hp, mb_patM_apply _ _ hp1 (by omega)]
        congr 2
        unfold mbGluePat
        rw [dite_eq_left (by simp only; omega)]
      · rw [ite_eq_right hp, mb_patM_apply _ _ (by omega) (by omega)]
        congr 2
        unfold mbGluePat
        rw [dite_eq_right (by simp only; omega)]
        congr 1
        apply Fin.ext
        simp only
        omega
    · unfold Split.glueObs
      rw [mb_obsSeq_apply P.S (mbGlueSites x i j q) hp1 (by omega)]
      by_cases hp : p < (i : ℕ) + 1
      · rw [ite_eq_left hp, mb_obsSeq_apply _ _ hp1 (by omega)]
        congr 2
        unfold mbGlueSites
        rw [dite_eq_left (by simp only; omega)]
      · rw [ite_eq_right hp]
        by_cases hp' : p = (i : ℕ) + 1
        · rw [ite_eq_left hp']
          unfold mbGlueSites
          rw [dite_eq_right (by simp only; omega), ite_eq_left (by simp only; omega)]
        · rw [ite_eq_right hp', mb_obsSeq_apply _ _ (by omega) (by omega)]
          congr 2
          unfold mbGlueSites
          rw [dite_eq_right (by simp only; omega), ite_eq_right (by simp only; omega)]
          congr 1
          apply Fin.ext
          simp only
          omega
  · rw [mb_obsSeq_apply _ _ (by omega) le_rfl, mb_obsSeq_apply _ _ (by omega) le_rfl]
    congr 2
    unfold mbGlueSites
    rw [dite_eq_right (by simp only; omega), ite_eq_right (by simp only; omega)]
    congr 1
    apply Fin.ext
    simp only
    omega

end Index

/-!
## The bound
-/

theorem mbGlueSites_eq_q {k : ℕ} (x : Fin k → Fin N) (i j : Fin k) (q : Fin N)
    {r : Fin (k - j + i + 1)} (h : (r : ℕ) = i) : mbGlueSites x i j q r = q := by
  unfold mbGlueSites
  rw [dite_eq_right (by omega), ite_eq_left h]

theorem mbGlueSites_lt {k : ℕ} (x : Fin k → Fin N) (i j : Fin k) (q : Fin N)
    {r : Fin (k - j + i + 1)} (h : (r : ℕ) < i) :
    mbGlueSites x i j q r = x ⟨r, h.trans i.isLt⟩ := by
  unfold mbGlueSites
  rw [dite_eq_left h]

theorem mbGlueSites_gt {k : ℕ} (x : Fin k → Fin N) (i j : Fin k) (q : Fin N)
    {r : Fin (k - j + i + 1)} (h : (i : ℕ) < r) (hb : (r : ℕ) + j - i - 1 < k) :
    mbGlueSites x i j q r = x ⟨(r : ℕ) + j - i - 1, hb⟩ := by
  unfold mbGlueSites
  rw [dite_eq_right (by omega), ite_eq_right (by omega)]
  congr 1
  apply Fin.ext
  simp only
  omega

theorem mb_sAv_cast (P : PsiData N) {m m' : ℕ} (h : m = m') (x : Fin m' → Fin N) (t : ℝ) :
    P.sAv (fun r => x (Fin.cast h r)) t = P.sAv x t := by
  subst h
  rfl

theorem mb_sIso_nonneg (P : PsiData N) {t : ℝ} {d : VSData} (hin : ContrVSInputs d P t)
    {m : ℕ} (a b : Fin N) (x : Fin m → Fin N) : 0 ≤ P.sIso a b x t :=
  mul_nonneg (Real.rpow_nonneg hin.lEta_pos.le _) (Real.sqrt_nonneg _)

theorem mb_sAv_nonneg (P : PsiData N) {t : ℝ} {d : VSData} (hin : ContrVSInputs d P t)
    {m : ℕ} (x : Fin m → Fin N) : 0 ≤ P.sAv x t := by
  unfold PsiData.sAv
  split_ifs
  · exact inv_nonneg.mpr hin.lEta_pos.le
  · exact mul_nonneg (Real.rpow_nonneg hin.lEta_pos.le _) (Real.sqrt_nonneg _)

section Bound

variable (P : PsiData N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {d : VSData}
  (hin : ContrVSInputs d P t)
include ht hin

/-- One pair `(i, j)` of `F_M`, `2 ≤ j - i ≤ k - 2`:
`|Σ_q (M_{[i,j]})_{qq} Tr[M^{(q)} S^{x_k}]| ≤ (C_wc/η) I A L s^av_k(x)` under
`IsoB(j-i+1, I)` and `AvB(k-j+i+1, A)`.
-/
theorem mb_pair_forcing_bound {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin N) (i j : Fin k)
    (h2 : 2 ≤ (j : ℕ) - i) (hk : (j : ℕ) - i ≤ k - 2) {I A : ℝ} (hI0 : 0 ≤ I) (hA0 : 0 ≤ A)
    (hI : MBIsoB P ((j : ℕ) - i + 1) I) (hA : MBAvB P (k - j + i + 1) A) :
    ‖∑ q, aM P σ x t i j q * bMav P σ x t i j q‖ ≤
      d.Cwc / vsHeight P.z t * (I * A) * (P.lEta t * P.sAv x t) := by
  have hij : i < j := by rw [Fin.lt_def]; omega
  have hjk := j.isLt
  have hL := hin.lEta_pos
  set i' := k - j + i with hi'
  set j' := (j : ℕ) - i with hj'
  have hk' : i' + j' = k := by omega
  -- the rotated sites
  set w : Fin (i' + j') → Fin N := fun r => x ⟨((r : ℕ) + j) % k, Nat.mod_lt _ (by omega)⟩
  have hw : P.sAv w t = P.sAv x t :=
    (mb_sAv_cast P hk' (fun r' : Fin k => x ⟨((r' : ℕ) + j) % k, Nat.mod_lt _ (by omega)⟩)
      t).trans (contr_sAv_rotate P x _ j (fun n hn => rfl) t)
  set xq : Fin N → Fin (i' + 1) → Fin N := fun q r =>
    mbGlueSites x i j q ⟨((r : ℕ) + i + 1) % (i' + 1), Nat.mod_lt _ (by omega)⟩
  have hxq : ∀ q, P.sAv (xq q) t = P.sAv (mbGlueSites x i j q) t := fun q =>
    contr_sAv_rotate P (mbGlueSites x i j q) (xq q) ((i : ℕ) + 1) (fun n hn => by
      simp only [xq]
      congr 1) t
  have hlast : ∀ q, xq q ⟨i', by omega⟩ = q := by
    intro q
    have : (i' + (i : ℕ) + 1) % (i' + 1) = i := by
      rw [show i' + (i : ℕ) + 1 = (i : ℕ) + (i' + 1) by ring, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    exact mbGlueSites_eq_q x i j q this
  have hxqw : ∀ (q : Fin N) (n : ℕ) (hn : n < i'), xq q ⟨n, by omega⟩ = w ⟨n, by omega⟩ := by
    intro q n hn
    show mbGlueSites x i j q _ = x _
    by_cases hc : n + (i : ℕ) + 1 < i' + 1
    · have e1 : (n + (i : ℕ) + 1) % (i' + 1) = n + i + 1 := Nat.mod_eq_of_lt hc
      rw [mbGlueSites_gt x i j q (by simp only; omega) (by simp only; omega)]
      congr 1
      apply Fin.ext
      simp only [e1]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have e1 : (n + (i : ℕ) + 1) % (i' + 1) = n + i + 1 - (i' + 1) := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [mbGlueSites_lt x i j q (by simp only; omega)]
      congr 1
      apply Fin.ext
      simp only [e1]
      rw [show n + (j : ℕ) = (n + j - k) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hy : ∀ (n : ℕ) (hn : n < j'), mbSubSites x i j ⟨n, by omega⟩ = w ⟨i' + n, by omega⟩ := by
    intro n hn
    simp only [mbSubSites, w]
    congr 1
    apply Fin.ext
    simp only
    rw [show i' + n + (j : ℕ) = ((i : ℕ) + n) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hins := avInsertion_of P t hin.nonneg hL (K := d.Cwc / vsHeight P.z t) hin.schwarz
    (i := i') (j := j') (by omega) (by omega) xq (mbSubSites x i j) w hlast hxqw hy
  have hpw : Real.sqrt (P.lEta t) * P.lEta t ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    norm_num
  calc ‖∑ q, aM P σ x t i j q * bMav P σ x t i j q‖
      ≤ ∑ q, ‖aM P σ x t i j q‖ * ‖bMav P σ x t i j q‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
    _ ≤ ∑ q, (I * (Real.sqrt (P.lEta t) * P.sIso q q (mbSubSites x i j) t)) *
          (A * (P.lEta t * P.sAv (mbGlueSites x i j q) t)) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [mb_aM_eq P σ x t hij.le, mb_bMav_eq P σ x t hij]
        exact mul_le_mul (hI t ht _ q _) (hA t ht _ _) (norm_nonneg _)
          (mul_nonneg hI0 (mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P hin _ _ _)))
    _ = I * A * P.lEta t * Real.sqrt (P.lEta t) *
          ∑ q, P.sAv (xq q) t * P.sIso q q (mbSubSites x i j) t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hxq q]
        ring
    _ ≤ I * A * P.lEta t * Real.sqrt (P.lEta t) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv w t) :=
        mul_le_mul_of_nonneg_left hins (mul_nonneg (mul_nonneg (mul_nonneg hI0 hA0) hL.le)
          (Real.sqrt_nonneg _))
    _ = d.Cwc / vsHeight P.z t * (I * A) * (P.lEta t * P.sAv x t) := by
        rw [hw]
        calc I * A * P.lEta t * Real.sqrt (P.lEta t) *
              (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sAv x t)
            = d.Cwc / vsHeight P.z t * (I * A) * (P.lEta t * P.sAv x t) *
                (Real.sqrt (P.lEta t) * P.lEta t ^ (-(1 / 2 : ℝ))) := by ring
          _ = _ := by rw [hpw, mul_one]

/-- The forcing constant `Σ_{i<j, 2 ≤ j-i ≤ k-2} I(j-i+1) A(k-(j-i)+1)` (`F_k / C_wc`). -/
def mbFPairSum (k : ℕ) (A I : ℕ → ℝ) : ℝ :=
  ∑ j : Fin k, ∑ i with i < j,
    if 2 ≤ (j : ℕ) - i ∧ (j : ℕ) - i ≤ k - 2 then I ((j : ℕ) - i + 1) * A (k - j + i + 1)
    else 0

/-- **M.9**: if `IsoB(n, I n)` and `AvB(n, A n)` for
all `3 ≤ n ≤ k-1` (with `I, A ≥ 0`), then for every pattern of length `k` and all sites,
`|F_M(x)| ≤ (C_wc/η) · mbFPairSum k A I · L s^av_k(x)`.
-/
theorem mbFM_bound {k : ℕ} (A I : ℕ → ℝ) (hA0 : ∀ n, 0 ≤ A n) (hI0 : ∀ n, 0 ≤ I n)
    (hA : ∀ n, 3 ≤ n → n + 1 ≤ k → MBAvB P n (A n))
    (hI : ∀ n, 3 ≤ n → n + 1 ≤ k → MBIsoB P n (I n)) (σ : Fin k → Bool) (x : Fin k → Fin N) :
    ‖mbFM P σ x t‖ ≤ d.Cwc / vsHeight P.z t * mbFPairSum k A I * (P.lEta t * P.sAv x t) := by
  unfold mbFM mbFPairSum
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hij := (Finset.mem_filter.mp hi).2
  have hij' : (i : ℕ) < j := hij
  have hjk := j.isLt
  split_ifs with hc
  · have := mb_pair_forcing_bound P ht hin σ x i j hc.1 hc.2 (hI0 _) (hA0 _)
      (hI _ (by omega) (by omega)) (hA _ (by omega) (by omega))
    simpa only [mul_assoc] using this
  · simp

end Bound

end BlockBand.Native.ErdosRiabov.MBound
