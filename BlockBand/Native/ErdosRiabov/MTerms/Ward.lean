module

public import BlockBand.Native.ErdosRiabov.MTerms.Basic

/-!
# Deterministic `M`-terms: the divided-difference (Ward) identity

Proves `WardStatement` (the Ward identity for `M`-terms of Erdős–Riabov, arXiv 2506.06441v1, at
profile `σ S`): if `A j = I`, `1 ≤ j < k`, `m j ≠ m (j + 1)`, then
`M_{[1,k]} = (z_{j,σ} - z_{j+1,σ})⁻¹ (M(chain without z_{j+1}) - M(chain without z_j))`,
both shorter chains without `A_j`, `z_{j,σ} = zParam σ (m j) = -1/m_j - σ m_j`.

Setting: `n : ℕ`, profile `S` with `ProfileHyp S`, `σ ∈ [0,1]`, spectral data `m : ℕ → ℂ` with
`‖m i‖ < 1` and `m i ≠ 0` (needed for `zParam` and for the first-index case), observables
`A : ℕ → Fin n → ℂ`.

Main declarations.
* `ward_holds : WardStatement`.
* `Ward.ward_window`: the identity for every window `[p, q]` with `p ≤ j < q`
  (`dropAt` acts on the whole sequence, so the windows `[p, q - 1]` of the dropped sequences
  are the shorter chains); `ward_holds` is `p = 1`.
* `Ward.one_sub_mulVec_chainM`: the `M`-level recursion without division,
  `(1 - σ m_a m_b S) M_{[a,b]} = m_a (A_a M_{[a+1,b]} + σ ∑_{a<i<b} S[M_{[a,i]}] M_{[i,b]})`.
* `Ward.ward_base`, `Ward.ward_first`, `Ward.ward_interior`, `Ward.ward_last`: the four cases
  (`q = p + 1`; `j = p`; `p < j < q - 1`; `p < j = q - 1`).

Inputs: Mathlib; `BlockBand.Native.ErdosRiabov.Split.MTermsStatement`;
`BlockBand.Native.ErdosRiabov.MTerms.Basic` (`stabOp_mulVec_one_sub`, `one_sub_mulVec_chainTilde`,
`selfEnergy_const`, `chainM_self`, `chainM_congr`, `chainM_shift`, `norm_mul_lt_one_of_lt_one`,
`one_sub_sigma_mul_ne_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split Matrix Finset

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} {σ : ℝ} {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ}

namespace Ward

/-- Cancellation of the stability operator. -/
theorem one_sub_mulVec_cancel (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1) {a : ℂ}
    (ha : ‖a‖ < 1) {v w : Fin n → ℂ}
    (h : (1 - ((σ:ℂ) * a) • profileC S) *ᵥ v = (1 - ((σ:ℂ) * a) • profileC S) *ᵥ w) :
    v = w := by
  rw [← stabOp_mulVec_one_sub hS hσ ha v, h, stabOp_mulVec_one_sub hS hσ ha w]

/-- Pointwise expansion of `(1 - c S) v`. -/
theorem one_sub_mulVec_apply (c : ℂ) (v : Fin n → ℂ) (x : Fin n) :
    ((1 - c • profileC S) *ᵥ v) x = v x - c * (profileC S *ᵥ v) x := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- `∏_{i=a}^b m i = m a ∏_{i=a+1}^b m i` for `a ≤ b`. -/
theorem prod_Icc_eq_mul_prod_Icc (m : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∏ i ∈ Icc a b, m i = m a * ∏ i ∈ Icc (a + 1) b, m i := by
  have h : Icc a b = insert a (Icc (a + 1) b) := by
    ext x; simp only [mem_Icc, mem_insert]; omega
  rw [h, prod_insert (by simp)]

/-- `(∏_{x=a}^b m x) m i = (∏_{x=a}^i m x)(∏_{x=i}^b m x)` for `a ≤ i ≤ b`. -/
theorem prod_Icc_mul_eq (m : ℕ → ℂ) {a i b : ℕ} (hai : a ≤ i) (hib : i ≤ b) :
    (∏ x ∈ Icc a b, m x) * m i = (∏ x ∈ Icc a i, m x) * ∏ x ∈ Icc i b, m x := by
  have h1 : ∀ c d : ℕ, Icc c d = Ico c (d + 1) := fun c d => by ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [h1, h1, h1, prod_Ico_succ_top hai, mul_right_comm,
    prod_Ico_consecutive _ hai (by omega : i ≤ b + 1)]

/-- M-level recursion in multiplied-out form (no division by `m`). -/
theorem one_sub_mulVec_chainM (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) {a b : ℕ} (hab : a < b) :
    (1 - ((σ:ℂ) * (m a * m b)) • profileC S) *ᵥ chainM σ S m A a b =
      m a • (A a * chainM σ S m A (a + 1) b +
        (σ:ℂ) • ∑ i ∈ Ioo a b, selfEnergy S (chainM σ S m A a i) * chainM σ S m A i b) := by
  rw [chainM, mulVec_smul, one_sub_mulVec_chainTilde hS hσ hm hab]
  funext x
  simp only [chainM, selfEnergy, mulVec_smul, Pi.smul_apply, Pi.add_apply, Pi.mul_apply,
    smul_eq_mul, Finset.sum_apply, Finset.mul_sum, mul_add]
  have hP := prod_Icc_eq_mul_prod_Icc m hab.le
  congr 1
  · rw [hP]; ring
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := mem_Ioo.mp hi
    have := prod_Icc_mul_eq m (a := a) (b := b) hi'.1.le hi'.2.le
    rw [hP] at this ⊢
    linear_combination (m a * σ * ((profileC S *ᵥ chainTilde σ S m A a i) x *
      chainTilde σ S m A i b x)) * this

/-!
### Dropped chains
-/

/-- Dropping `z_{j+1}` does not change a window `[a, b]` with `b ≤ j`. -/
theorem chainM_dropPlus_low {j a b : ℕ} (hb : b ≤ j) :
    chainM σ S (dropAt (j + 1) m) (dropAt j A) a b = chainM σ S m A a b :=
  chainM_congr (fun i _ hi => by simp [dropAt, show i < j + 1 by omega])
    (fun i _ hi => by simp [dropAt, show i < j by omega])

/-- Dropping `z_j` does not change a window `[a, b]` with `b < j`. -/
theorem chainM_dropMinus_low {j a b : ℕ} (hb : b < j) :
    chainM σ S (dropAt j m) (dropAt j A) a b = chainM σ S m A a b :=
  chainM_congr (fun i _ hi => by simp [dropAt, show i < j by omega])
    (fun i _ hi => by simp [dropAt, show i < j by omega])

/-- After dropping `z_{j+1}`, a window `[a, b]` with `a ≥ j + 1` is the original window
`[a + 1, b + 1]`. -/
theorem chainM_dropPlus_high {j a b : ℕ} (ha : j + 1 ≤ a) :
    chainM σ S (dropAt (j + 1) m) (dropAt j A) a b = chainM σ S m A (a + 1) (b + 1) := by
  rw [← chainM_shift]
  exact chainM_congr (fun i hi _ => by simp [dropAt, show ¬ i < j + 1 by omega])
    (fun i hi _ => by simp [dropAt, show ¬ i < j by omega])

/-- After dropping `z_j`, a window `[a, b]` with `a ≥ j` is the original window
`[a + 1, b + 1]`. -/
theorem chainM_dropMinus_high {j a b : ℕ} (ha : j ≤ a) :
    chainM σ S (dropAt j m) (dropAt j A) a b = chainM σ S m A (a + 1) (b + 1) := by
  rw [← chainM_shift]
  exact chainM_congr (fun i hi _ => by simp [dropAt, show ¬ i < j by omega])
    (fun i hi _ => by simp [dropAt, show ¬ i < j by omega])

/-- The one-point window `[j, j]` after dropping `z_{j+1}` is `m j`. -/
theorem chainM_dropPlus_self (j : ℕ) :
    chainM σ S (dropAt (j + 1) m) (dropAt j A) j j = fun _ => m j := by
  rw [chainM_self]; simp [dropAt]

/-- The one-point window `[j, j]` after dropping `z_j` is `m (j + 1)`. -/
theorem chainM_dropMinus_self (j : ℕ) :
    chainM σ S (dropAt j m) (dropAt j A) j j = fun _ => m (j + 1) := by
  rw [chainM_self]; simp [dropAt]

/-!
### Scalars
-/

/-- `(z_a - z_b)⁻¹ (a - b) (1 - σ a b) = a b`. -/
theorem zParam_sub_inv_mul (hσ : σ ∈ Set.Icc (0:ℝ) 1) {a b : ℂ} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    (zParam σ a - zParam σ b)⁻¹ * ((a - b) * (1 - (σ:ℂ) * a * b)) = a * b := by
  have h1 : 1 - (σ:ℂ) * a * b ≠ 0 := by
    rw [mul_assoc]; exact one_sub_sigma_mul_ne_zero hσ (norm_mul_lt_one_of_lt_one ha hb)
  have h2 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hz : zParam σ a - zParam σ b = (a - b) * (1 - (σ:ℂ) * a * b) / (a * b) := by
    unfold zParam; field_simp; ring
  rw [hz, inv_div, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero h2 h1)]

/-!
### Index helpers
-/

/-- `dropAt` below the dropped position. -/
theorem dropAt_of_lt {α : Type*} (f : ℕ → α) {p i : ℕ} (h : i < p) : dropAt p f i = f i := by
  simp [dropAt, h]

/-- `dropAt` at or above the dropped position. -/
theorem dropAt_of_le {α : Type*} (f : ℕ → α) {p i : ℕ} (h : p ≤ i) :
    dropAt p f i = f (i + 1) := by
  simp [dropAt, show ¬ i < p by omega]

/-- Dropping an entry preserves `‖m i‖ < 1`. -/
theorem norm_dropAt_lt (hm : ∀ i, ‖m i‖ < 1) (p i : ℕ) : ‖dropAt p m i‖ < 1 := by
  unfold dropAt; split_ifs <;> exact hm _

/-- `Ioo a b = Ico (a + 1) b` on `ℕ`. -/
theorem Ioo_eq_Ico (a b : ℕ) : Ioo a b = Ico (a + 1) b := by
  ext x; simp only [mem_Ioo, mem_Ico]; omega

/-- `Ioo a (a + 1) = ∅` on `ℕ`. -/
theorem Ioo_succ_eq_empty (a : ℕ) : Ioo a (a + 1) = ∅ := by
  ext x; simp only [mem_Ioo, Finset.notMem_empty, iff_false]; omega

/-- Splitting `∑_{a<i<b}` at an interior index `j`. -/
theorem sum_Ioo_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) {a j b : ℕ} (h1 : a < j)
    (h2 : j < b) : ∑ i ∈ Ioo a b, f i = ∑ i ∈ Ioo a j, f i + f j + ∑ i ∈ Ioo j b, f i := by
  rw [Ioo_eq_Ico, Ioo_eq_Ico, Ioo_eq_Ico, ← sum_Ico_consecutive f (show a + 1 ≤ j by omega) h2.le,
    sum_eq_sum_Ico_succ_bot h2 f, add_assoc]

/-- Index shift `∑_{a+1<i<b} f i = ∑_{a<i<b-1} f (i + 1)`. -/
theorem sum_Ioo_succ_left {α : Type*} [AddCommMonoid α] (f : ℕ → α) {a b : ℕ} (h : a < b) :
    ∑ i ∈ Ioo (a + 1) b, f i = ∑ i ∈ Ioo a (b - 1), f (i + 1) := by
  rw [Ioo_eq_Ico, Ioo_eq_Ico, sum_Ico_add' f (a + 1) (b - 1) 1, Nat.sub_add_cancel (by omega)]

/-- Linearity of the self-energy. -/
theorem selfEnergy_smul_sub (c : ℂ) (u v : Fin n → ℂ) :
    selfEnergy S (c • (u - v)) = c • (selfEnergy S u - selfEnergy S v) := by
  unfold selfEnergy; rw [mulVec_smul, mulVec_sub]

/-!
### The four cases
-/

/-- Base case `M(z_j, I, z_{j+1}) = (z_{j,σ} - z_{j+1,σ})⁻¹ (m_j - m_{j+1})`, with `c` any scalar
satisfying `c (m_j - m_{j+1})(1 - σ m_j m_{j+1}) = m_j m_{j+1}`. -/
theorem ward_base (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hm : ∀ i, ‖m i‖ < 1)
    {j : ℕ} (hAj : A j = fun _ => 1) {c : ℂ}
    (hc : c * ((m j - m (j + 1)) * (1 - (σ:ℂ) * m j * m (j + 1))) = m j * m (j + 1)) :
    chainM σ S m A j (j + 1) =
      c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) j j -
        chainM σ S (dropAt j m) (dropAt j A) j j) := by
  rw [chainM_dropPlus_self, chainM_dropMinus_self]
  have hconst : c • ((fun _ : Fin n => m j) - fun _ => m (j + 1)) =
      fun _ => c * (m j - m (j + 1)) := by
    funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hconst]
  refine one_sub_mulVec_cancel hS hσ (norm_mul_lt_one_of_lt_one (hm j) (hm (j + 1))) ?_
  rw [one_sub_mulVec_chainM hS hσ hm (Nat.lt_succ_self j), chainM_self, hAj,
    Ioo_succ_eq_empty, sum_empty]
  have hS1 := selfEnergy_const hS (c * (m j - m (j + 1)))
  unfold selfEnergy at hS1
  funext x
  rw [one_sub_mulVec_apply, hS1]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, smul_zero, add_zero]
  linear_combination -hc

/-- First-index case `j = p`, `q ≥ p + 2`, from the
Ward identity for the shorter windows `[p, i]`, `p < i < q`. Uses `m (p + 1) ≠ 0`. -/
theorem ward_first (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hm : ∀ i, ‖m i‖ < 1)
    (hm0 : ∀ i, m i ≠ 0) {p q : ℕ} (hpq : p + 1 < q) (hAp : A p = fun _ => 1) {c : ℂ}
    (hc : c * ((m p - m (p + 1)) * (1 - (σ:ℂ) * m p * m (p + 1))) = m p * m (p + 1))
    (ih : ∀ i, p < i → i < q → chainM σ S m A p i =
      c • (chainM σ S (dropAt (p + 1) m) (dropAt p A) p (i - 1) -
        chainM σ S (dropAt p m) (dropAt p A) p (i - 1))) :
    chainM σ S m A p q =
      c • (chainM σ S (dropAt (p + 1) m) (dropAt p A) p (q - 1) -
        chainM σ S (dropAt p m) (dropAt p A) p (q - 1)) := by
  have hq : q - 1 + 1 = q := by omega
  have hDm : chainM σ S (dropAt p m) (dropAt p A) p (q - 1) = chainM σ S m A (p + 1) q := by
    rw [chainM_dropMinus_high le_rfl, hq]
  have hfirst : chainM σ S m A p (p + 1) = c • ((fun _ => m p) - fun _ => m (p + 1)) := by
    rw [ih (p + 1) (by omega) hpq, Nat.add_sub_cancel, chainM_dropPlus_self,
      chainM_dropMinus_self]
  -- the two sums
  set Tp := ∑ i ∈ Ioo p (q - 1), selfEnergy S (chainM σ S (dropAt (p + 1) m) (dropAt p A) p i) *
    chainM σ S m A (i + 1) q with hTp
  set Tm := ∑ i ∈ Ioo p (q - 1), selfEnergy S (chainM σ S m A (p + 1) (i + 1)) *
    chainM σ S m A (i + 1) q with hTm
  have hsum : ∑ i ∈ Ioo p q, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q =
      (c * (m p - m (p + 1))) • chainM σ S m A (p + 1) q + c • (Tp - Tm) := by
    rw [sum_Ioo_split _ (Nat.lt_succ_self p) hpq, Ioo_succ_eq_empty, sum_empty, zero_add,
      sum_Ioo_succ_left _ (show p < q by omega)]
    congr 1
    · rw [hfirst]
      have hconst : c • ((fun _ : Fin n => m p) - fun _ => m (p + 1)) =
          fun _ => c * (m p - m (p + 1)) := by
        funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [hconst, selfEnergy_const hS]
      funext x; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    · rw [hTp, hTm, ← sum_sub_distrib, smul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_Ioo.mp hi
      rw [ih (i + 1) (by omega) (by omega), Nat.add_sub_cancel, chainM_dropMinus_high le_rfl,
        selfEnergy_smul_sub, smul_mul_assoc, sub_mul]
  have hDp : (1 - ((σ:ℂ) * (m p * m q)) • profileC S) *ᵥ
      chainM σ S (dropAt (p + 1) m) (dropAt p A) p (q - 1) =
        m p • (A (p + 1) * chainM σ S m A (p + 2) q + (σ:ℂ) • Tp) := by
    have h := one_sub_mulVec_chainM (m := dropAt (p + 1) m) (A := dropAt p A) hS hσ
      (norm_dropAt_lt hm (p + 1)) (show p < q - 1 by omega)
    rw [dropAt_of_lt m (Nat.lt_succ_self p), dropAt_of_le m (show p + 1 ≤ q - 1 by omega), hq,
      dropAt_of_le A le_rfl, chainM_dropPlus_high le_rfl, hq] at h
    rw [h, hTp]
    congr 3
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_Ioo.mp hi
    rw [chainM_dropPlus_high (show p + 1 ≤ i by omega), hq]
  have hY : (1 - ((σ:ℂ) * (m (p + 1) * m q)) • profileC S) *ᵥ chainM σ S m A (p + 1) q =
      m (p + 1) • (A (p + 1) * chainM σ S m A (p + 2) q + (σ:ℂ) • Tm) := by
    rw [one_sub_mulVec_chainM hS hσ hm hpq, sum_Ioo_succ_left _ (show p < q by omega)]
  refine one_sub_mulVec_cancel hS hσ (norm_mul_lt_one_of_lt_one (hm p) (hm q)) ?_
  rw [one_sub_mulVec_chainM hS hσ hm (show p < q by omega), hsum, hDm, hAp, mulVec_smul,
    mulVec_sub, hDp]
  funext x
  have hY' := congrFun hY x
  simp only [one_sub_mulVec_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
    smul_eq_mul] at hY' ⊢
  apply mul_left_cancel₀ (hm0 (p + 1))
  linear_combination (c * m p) * hY' - chainM σ S m A (p + 1) q x * hc

/-- Interior case `p < j < q - 1`, from the Ward identity for the windows `[i, q]` (`p < i ≤ j`)
and `[p, i]` (`j < i < q`). -/
theorem ward_interior (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hm : ∀ i, ‖m i‖ < 1)
    {p j q : ℕ} (hpj : p < j) (hjq : j + 1 < q) {c : ℂ}
    (ih2 : ∀ i, p < i → i ≤ j → chainM σ S m A i q =
      c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) i (q - 1) -
        chainM σ S (dropAt j m) (dropAt j A) i (q - 1)))
    (ih3 : ∀ i, j < i → i < q → chainM σ S m A p i =
      c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) p (i - 1) -
        chainM σ S (dropAt j m) (dropAt j A) p (i - 1))) :
    chainM σ S m A p q =
      c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) p (q - 1) -
        chainM σ S (dropAt j m) (dropAt j A) p (q - 1)) := by
  have hq : q - 1 + 1 = q := by omega
  have hsum : ∑ i ∈ Ioo p q, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q =
      c • ∑ i ∈ Ioo p (q - 1),
        (selfEnergy S (chainM σ S (dropAt (j + 1) m) (dropAt j A) p i) *
            chainM σ S (dropAt (j + 1) m) (dropAt j A) i (q - 1) -
          selfEnergy S (chainM σ S (dropAt j m) (dropAt j A) p i) *
            chainM σ S (dropAt j m) (dropAt j A) i (q - 1)) := by
    rw [sum_Ioo_split _ hpj (show j < q by omega), sum_Ioo_split _ hpj (show j < q - 1 by omega),
      sum_Ioo_split _ (Nat.lt_succ_self j) hjq, Ioo_succ_eq_empty, sum_empty, zero_add,
      sum_Ioo_succ_left _ (show j < q by omega), smul_add, smul_add]
    have hA : ∑ i ∈ Ioo p j, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q =
        c • ∑ i ∈ Ioo p j,
          (selfEnergy S (chainM σ S (dropAt (j + 1) m) (dropAt j A) p i) *
              chainM σ S (dropAt (j + 1) m) (dropAt j A) i (q - 1) -
            selfEnergy S (chainM σ S (dropAt j m) (dropAt j A) p i) *
              chainM σ S (dropAt j m) (dropAt j A) i (q - 1)) := by
      rw [smul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_Ioo.mp hi
      rw [ih2 i hi'.1 hi'.2.le, chainM_dropPlus_low (a := p) (b := i) hi'.2.le,
        chainM_dropMinus_low (a := p) (b := i) hi'.2, mul_smul_comm, mul_sub]
    have hC : ∑ i ∈ Ioo j (q - 1), selfEnergy S (chainM σ S m A p (i + 1)) *
          chainM σ S m A (i + 1) q =
        c • ∑ i ∈ Ioo j (q - 1),
          (selfEnergy S (chainM σ S (dropAt (j + 1) m) (dropAt j A) p i) *
              chainM σ S (dropAt (j + 1) m) (dropAt j A) i (q - 1) -
            selfEnergy S (chainM σ S (dropAt j m) (dropAt j A) p i) *
              chainM σ S (dropAt j m) (dropAt j A) i (q - 1)) := by
      rw [smul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_Ioo.mp hi
      rw [ih3 (i + 1) (by omega) (by omega), Nat.add_sub_cancel,
        chainM_dropPlus_high (a := i) (b := q - 1) (by omega),
        chainM_dropMinus_high (a := i) (b := q - 1) (by omega), hq, selfEnergy_smul_sub,
        smul_mul_assoc, sub_mul]
    have hB : selfEnergy S (chainM σ S m A p j) * chainM σ S m A j q +
        selfEnergy S (chainM σ S m A p (j + 1)) * chainM σ S m A (j + 1) q =
        c • (selfEnergy S (chainM σ S (dropAt (j + 1) m) (dropAt j A) p j) *
              chainM σ S (dropAt (j + 1) m) (dropAt j A) j (q - 1) -
            selfEnergy S (chainM σ S (dropAt j m) (dropAt j A) p j) *
              chainM σ S (dropAt j m) (dropAt j A) j (q - 1)) := by
      rw [ih2 j hpj le_rfl, ih3 (j + 1) (Nat.lt_succ_self j) hjq, Nat.add_sub_cancel,
        chainM_dropPlus_low (a := p) (b := j) le_rfl,
        show chainM σ S m A (j + 1) q = chainM σ S (dropAt j m) (dropAt j A) j (q - 1) by
          rw [chainM_dropMinus_high le_rfl, hq],
        selfEnergy_smul_sub]
      funext x
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hA, hC, ← hB]
    abel
  have hDp : (1 - ((σ:ℂ) * (m p * m q)) • profileC S) *ᵥ
      chainM σ S (dropAt (j + 1) m) (dropAt j A) p (q - 1) =
        m p • (A p * chainM σ S (dropAt (j + 1) m) (dropAt j A) (p + 1) (q - 1) +
          (σ:ℂ) • ∑ i ∈ Ioo p (q - 1),
            selfEnergy S (chainM σ S (dropAt (j + 1) m) (dropAt j A) p i) *
              chainM σ S (dropAt (j + 1) m) (dropAt j A) i (q - 1)) := by
    have h := one_sub_mulVec_chainM (m := dropAt (j + 1) m) (A := dropAt j A) hS hσ
      (norm_dropAt_lt hm (j + 1)) (show p < q - 1 by omega)
    rwa [dropAt_of_lt m (show p < j + 1 by omega), dropAt_of_le m (show j + 1 ≤ q - 1 by omega),
      hq, dropAt_of_lt A hpj] at h
  have hDm : (1 - ((σ:ℂ) * (m p * m q)) • profileC S) *ᵥ
      chainM σ S (dropAt j m) (dropAt j A) p (q - 1) =
        m p • (A p * chainM σ S (dropAt j m) (dropAt j A) (p + 1) (q - 1) +
          (σ:ℂ) • ∑ i ∈ Ioo p (q - 1),
            selfEnergy S (chainM σ S (dropAt j m) (dropAt j A) p i) *
              chainM σ S (dropAt j m) (dropAt j A) i (q - 1)) := by
    have h := one_sub_mulVec_chainM (m := dropAt j m) (A := dropAt j A) hS hσ
      (norm_dropAt_lt hm j) (show p < q - 1 by omega)
    rwa [dropAt_of_lt m hpj, dropAt_of_le m (show j ≤ q - 1 by omega), hq,
      dropAt_of_lt A hpj] at h
  refine one_sub_mulVec_cancel hS hσ (norm_mul_lt_one_of_lt_one (hm p) (hm q)) ?_
  rw [one_sub_mulVec_chainM hS hσ hm (show p < q by omega), hsum, ih2 (p + 1) (by omega) hpj,
    mulVec_smul, mulVec_sub, hDp, hDm, sum_sub_distrib]
  funext x
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Last-index case `p < j = q - 1`, from the Ward identity for the windows `[i, j + 1]`,
`p < i ≤ j`; uses `(1 - σ m_p m_j S) + σ m_p (m_j - m_{j+1}) S = 1 - σ m_p m_{j+1} S`. -/
theorem ward_last (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hm : ∀ i, ‖m i‖ < 1)
    {p j : ℕ} (hpj : p < j) {c : ℂ}
    (ih2 : ∀ i, p < i → i ≤ j → chainM σ S m A i (j + 1) =
      c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) i j -
        chainM σ S (dropAt j m) (dropAt j A) i j)) :
    chainM σ S m A p (j + 1) =
      c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) p j -
        chainM σ S (dropAt j m) (dropAt j A) p j) := by
  set P := ∑ i ∈ Ioo p j, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i j with hP
  set Q := ∑ i ∈ Ioo p j, selfEnergy S (chainM σ S m A p i) *
    chainM σ S (dropAt j m) (dropAt j A) i j with hQ
  have hsum : ∑ i ∈ Ioo p (j + 1), selfEnergy S (chainM σ S m A p i) * chainM σ S m A i (j + 1) =
      c • (P - Q) + selfEnergy S (chainM σ S m A p j) *
        (c • ((fun _ => m j) - fun _ => m (j + 1))) := by
    rw [sum_Ioo_split _ hpj (Nat.lt_succ_self j), Ioo_succ_eq_empty, sum_empty, add_zero,
      ih2 j hpj le_rfl, chainM_dropPlus_self, chainM_dropMinus_self]
    congr 1
    rw [hP, hQ, ← sum_sub_distrib, smul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_Ioo.mp hi
    rw [ih2 i hi'.1 hi'.2.le, chainM_dropPlus_low (a := i) (b := j) le_rfl, mul_smul_comm, mul_sub]
  have hDp := one_sub_mulVec_chainM (A := A) hS hσ hm hpj
  rw [← hP] at hDp
  have hDm : (1 - ((σ:ℂ) * (m p * m (j + 1))) • profileC S) *ᵥ
      chainM σ S (dropAt j m) (dropAt j A) p j =
        m p • (A p * chainM σ S (dropAt j m) (dropAt j A) (p + 1) j + (σ:ℂ) • Q) := by
    have h := one_sub_mulVec_chainM (m := dropAt j m) (A := dropAt j A) hS hσ
      (norm_dropAt_lt hm j) hpj
    rw [dropAt_of_lt m hpj, dropAt_of_le m le_rfl, dropAt_of_lt A hpj] at h
    rw [h, hQ]
    congr 3
    refine sum_congr rfl fun i hi => ?_
    rw [chainM_dropMinus_low (a := p) (b := i) (mem_Ioo.mp hi).2]
  rw [chainM_dropPlus_low (a := p) (b := j) le_rfl]
  refine one_sub_mulVec_cancel hS hσ (norm_mul_lt_one_of_lt_one (hm p) (hm (j + 1))) ?_
  rw [one_sub_mulVec_chainM hS hσ hm (show p < j + 1 by omega), hsum,
    ih2 (p + 1) (Nat.lt_succ_self p) hpj,
    chainM_dropPlus_low (a := p + 1) (b := j) le_rfl, mulVec_smul, mulVec_sub, hDm]
  funext x
  have hDp' := congrFun hDp x
  simp only [selfEnergy, one_sub_mulVec_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply, smul_eq_mul] at hDp' ⊢
  linear_combination (-c) * hDp'

/-- The window form of the Ward identity: for `p ≤ j < q`, `A j = I`, `m j ≠ m (j + 1)`,
`M_{[p,q]} = (z_{j,σ} - z_{j+1,σ})⁻¹ (M^{(no z_{j+1})}_{[p,q-1]} - M^{(no z_j)}_{[p,q-1]})`,
where both shorter chains use `dropAt j A`. Strong induction on `q - p`. -/
theorem ward_window (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0:ℝ) 1) (hm : ∀ i, ‖m i‖ < 1)
    (hm0 : ∀ i, m i ≠ 0) {j : ℕ} (hAj : A j = fun _ => 1) (hj : m j ≠ m (j + 1)) (p q : ℕ)
    (hpj : p ≤ j) (hjq : j < q) :
    chainM σ S m A p q =
      (zParam σ (m j) - zParam σ (m (j + 1)))⁻¹ •
        (chainM σ S (dropAt (j + 1) m) (dropAt j A) p (q - 1) -
          chainM σ S (dropAt j m) (dropAt j A) p (q - 1)) := by
  set c := (zParam σ (m j) - zParam σ (m (j + 1)))⁻¹ with hc_def
  have hc : c * ((m j - m (j + 1)) * (1 - (σ:ℂ) * m j * m (j + 1))) = m j * m (j + 1) :=
    zParam_sub_inv_mul hσ (hm j) (hm _) (hm0 j) (hm0 _) hj
  induction h : q - p using Nat.strong_induction_on generalizing p q with
  | _ d ih =>
  have IH : ∀ p' q', q' - p' < d → p' ≤ j → j < q' →
      chainM σ S m A p' q' = c • (chainM σ S (dropAt (j + 1) m) (dropAt j A) p' (q' - 1) -
        chainM σ S (dropAt j m) (dropAt j A) p' (q' - 1)) :=
    fun p' q' hd h1 h2 => ih _ hd p' q' h1 h2 rfl
  rcases Nat.lt_or_ge p j with hpj' | hpj'
  · rcases Nat.lt_or_ge (j + 1) q with hjq' | hjq'
    · exact ward_interior hS hσ hm hpj' hjq'
        (fun i h1 h2 => IH i q (by omega) h2 (by omega))
        (fun i h1 h2 => IH p i (by omega) hpj h1)
    · obtain rfl : q = j + 1 := by omega
      rw [Nat.add_sub_cancel]
      refine ward_last hS hσ hm hpj' (fun i h1 h2 => ?_)
      rw [IH i (j + 1) (by omega) h2 (Nat.lt_succ_self j), Nat.add_sub_cancel]
  · obtain rfl : p = j := by omega
    rcases Nat.lt_or_ge (p + 1) q with h' | h'
    · exact ward_first hS hσ hm hm0 h' hAj hc (fun i h1 h2 => IH p i (by omega) le_rfl h1)
    · obtain rfl : q = p + 1 := by omega
      rw [Nat.add_sub_cancel]
      exact ward_base hS hσ hm hAj hc

end Ward

/-- The Ward identity at profile `σ S`: the divided-difference identity for `M_{[1,k]}`
with `A_j = I`; the case `p = 1` of `Ward.ward_window`. -/
theorem ward_holds : WardStatement := by
  intro n S hS σ hσ m hm hm0 A k j _ hj1 hjk hAj hmj
  exact Ward.ward_window hS hσ hm hm0 hAj hmj 1 k hj1 hjk

end BlockBand.Native.ErdosRiabov.MTerms
