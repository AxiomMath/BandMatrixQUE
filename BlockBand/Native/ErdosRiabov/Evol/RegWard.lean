module

public import BlockBand.Native.ErdosRiabov.Evol.TermList
public import BlockBand.Native.ErdosRiabov.Psi.Cont

/-!
# The Ward reduction of averaged chains

The partial trace of an averaged chain over its last site reduces to two chains of length one
less.

For a chain of length `k = n + 2` whose first and last spectral parameters are conjugate
(`σ_last ≠ σ_0`, e.g. a saturated pattern), the partial trace over the last site is
`𝒯_k[𝒳^k](x') = ∑_a 𝒳^k(x', a) = Tr[(G - M)_{[1,k]}(x')]`, and
`G_k G_1 = (z_k - z_1)⁻¹ (G_k - G_1)` gives, with `M`'s divided-difference identity,
`𝒯_k[𝒳^k](x') = (z_k - z_1)⁻¹ (𝒳^{k-1}_{σ'}(x') - 𝒳^{k-1}_{σ''}(x'))`, where
`σ'' = (σ_1, …, σ_{k-1})` and `σ' = (σ_k, σ_2, …, σ_{k-1})` (`wardPatHead`, `wardPatLast`),
`x' = (x_1, …, x_{k-1})` (`wardSites`); `|z_k - z_1| = 2η_t`.

* `res_mul_res`: the resolvent identity.
* `ward_gChain` (the `G`-part).
* **`wardReduction`**: the identity for `𝒳`; `wardReduction_norm`: `‖𝒯_k[𝒳^k]‖ ≤
  (2η_t)⁻¹ (‖𝒳^{k-1}_{σ'}‖ + ‖𝒳^{k-1}_{σ''}‖)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi
open scoped ComplexConjugate

variable {N n : ℕ}

/-!
### Patterns and sites of the reduced chains
-/

/-- `σ'' = (σ_1, …, σ_{k-1})`. -/
def wardPatHead (σ : Fin (n + 2) → Bool) : Fin (n + 1) → Bool := fun i => σ i.castSucc

/-- `σ' = (σ_k, σ_2, …, σ_{k-1})`. -/
def wardPatLast (σ : Fin (n + 2) → Bool) : Fin (n + 1) → Bool :=
  fun i => if i = 0 then σ (Fin.last (n + 1)) else σ i.castSucc

/-- `x' = (x_1, …, x_{k-1})`. -/
def wardSites (x : Fin (n + 2) → Fin N) : Fin (n + 1) → Fin N := fun i => x i.castSucc

/-!
### The resolvent identity and the `G`-part
-/

theorem res_mul_res (H : Matrix (Fin N) (Fin N) ℂ) {a b : ℂ}
    (ha : IsUnit (H - a • (1 : Matrix (Fin N) (Fin N) ℂ)).det)
    (hb : IsUnit (H - b • (1 : Matrix (Fin N) (Fin N) ℂ)).det) (hab : a ≠ b) :
    (H - a • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ * (H - b • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      (a - b)⁻¹ • ((H - a • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (H - b • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) := by
  set A := H - a • (1 : Matrix (Fin N) (Fin N) ℂ)
  set B := H - b • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hBA : B - A = (a - b) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    simp only [A, B, sub_smul]
    abel
  have e : A⁻¹ - B⁻¹ = (a - b) • (A⁻¹ * B⁻¹) := by
    calc A⁻¹ - B⁻¹ = A⁻¹ * (B * B⁻¹) - (A⁻¹ * A) * B⁻¹ := by
          rw [mul_nonsing_inv B hb, nonsing_inv_mul A ha, Matrix.mul_one, Matrix.one_mul]
      _ = A⁻¹ * (B - A) * B⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (a - b) • (A⁻¹ * B⁻¹) := by
          rw [hBA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [e, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul]

theorem patZ_im (z : ℂ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (j : Fin k) :
    (patZ z σ t j).im = if σ j then -vsHeight z t else vsHeight z t := by
  unfold patZ
  cases σ j <;> simp [VS.patConj, vsTraj_im]

theorem patZ_ne {z : ℂ} (hz : 0 < z.im) {k : ℕ} (σ : Fin k → Bool) {t : ℝ} (ht : t ≤ 1)
    {i j : Fin k} (hij : σ i ≠ σ j) : patZ z σ t i ≠ patZ z σ t j := by
  intro h
  have h1 := congrArg Complex.im h
  rw [patZ_im, patZ_im] at h1
  have hp := vsHeight_pos hz ht
  by_cases hi : σ i <;> by_cases hj : σ j
  · exact hij (by rw [hi, hj])
  · simp only [hi, hj, ite_true, Bool.false_eq_true, ite_false] at h1
    linarith
  · simp only [hi, hj, ite_true, Bool.false_eq_true, ite_false] at h1
    linarith
  · exact hij (by simp only [Bool.not_eq_true] at hi hj; rw [hi, hj])

theorem slotProd_succ_succ {ι : Type} [Fintype ι] [DecidableEq ι]
    (B R : Fin (n + 2) → Matrix ι ι ℂ) :
    slotProd B R = R 0 * B 0 *
      (List.ofFn fun i : Fin n => R i.succ.castSucc * B i.succ.castSucc).prod *
        (R (Fin.last (n + 1)) * B (Fin.last (n + 1))) := by
  rw [slotProd, slotList, List.ofFn_succ', List.concat_eq_append, List.prod_append,
    List.prod_singleton, List.ofFn_succ, List.prod_cons]
  rfl

theorem slotProd_succ {ι : Type} [Fintype ι] [DecidableEq ι]
    (B R : Fin (n + 1) → Matrix ι ι ℂ) :
    slotProd B R = R 0 * B 0 * (List.ofFn fun i : Fin n => R i.succ * B i.succ).prod := by
  rw [slotProd, slotList, List.ofFn_succ, List.prod_cons]

/-- **The `G`-part of the Ward reduction**: for Hermitian `H`, `Im z > 0`,
`t ≤ 1` and `σ_last ≠ σ_0`,
`Tr[G_{[1,k]}(x')] = (z_k - z_1)⁻¹ (Tr[G^{σ'}_{[1,k-1]} S^{x_{k-1}}] -`
`Tr[G^{σ''}_{[1,k-1]} S^{x_{k-1}}])`. -/
theorem ward_gChain (S : Matrix (Fin N) (Fin N) ℝ) {z : ℂ} (hz : 0 < z.im)
    (σ : Fin (n + 2) → Bool) (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N)
    {t : ℝ} (ht : t ≤ 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    trace (gChain (patZ z σ t) (isoSlots S x) H) =
      (patZ z σ t (Fin.last (n + 1)) - patZ z σ t 0)⁻¹ *
        (trace (gChain (patZ z (wardPatLast σ) t) (avSlots S (wardSites x)) H) -
          trace (gChain (patZ z (wardPatHead σ) t) (avSlots S (wardSites x)) H)) := by
  set R : Fin (n + 2) → Matrix (Fin N) (Fin N) ℂ :=
    fun j => (H - patZ z σ t j • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ with hR
  set Q := (List.ofFn fun i : Fin n => R i.succ.castSucc * isoSlots S x i.succ.castSucc).prod
  have hB0 : isoSlots S x 0 = obsMat S (x 0) := by simp [isoSlots]
  have hBl : isoSlots S x (Fin.last (n + 1)) = 1 := by simp [isoSlots]
  have hG : gChain (patZ z σ t) (isoSlots S x) H =
      R 0 * obsMat S (x 0) * Q * R (Fin.last (n + 1)) := by
    rw [gChain, slotProd_succ_succ, hB0, hBl, Matrix.mul_one]
  have hQ : ∀ i : Fin n, isoSlots S x i.succ.castSucc = obsMat S (wardSites x i.succ) := by
    intro i
    have : (i.succ.castSucc : ℕ) + 1 < n + 2 := by simp
    simp [isoSlots, wardSites]
  have hG'' : gChain (patZ z (wardPatHead σ) t) (avSlots S (wardSites x)) H =
      R 0 * obsMat S (x 0) * Q := by
    rw [gChain, slotProd_succ]
    simp only [avSlots, wardSites, wardPatHead, patZ, R, Q, hQ]
    rfl
  have hG' : gChain (patZ z (wardPatLast σ) t) (avSlots S (wardSites x)) H =
      R (Fin.last (n + 1)) * obsMat S (x 0) * Q := by
    rw [gChain, slotProd_succ]
    have h0 : wardPatLast σ 0 = σ (Fin.last (n + 1)) := by simp [wardPatLast]
    have hs : ∀ i : Fin n, wardPatLast σ i.succ = σ i.succ.castSucc := by
      intro i
      simp [wardPatLast, Fin.succ_ne_zero]
    simp only [avSlots, wardSites, patZ, h0, hs, R, Q, hQ]
    rfl
  have hu : ∀ j, IsUnit (H - patZ z σ t j • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    fun j => isUnit_det_herm_sub hH (patZ_im_ne_zero hz σ ht j)
  have hres := res_mul_res H (hu (Fin.last (n + 1))) (hu 0) (patZ_ne hz σ ht hσ)
  rw [hG, hG', hG'', Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change trace (R (Fin.last (n + 1)) * R 0 * obsMat S (x 0) * Q) = _
  rw [hres, Matrix.smul_mul, Matrix.smul_mul, trace_smul, Matrix.sub_mul, Matrix.sub_mul,
    trace_sub, smul_eq_mul]

/-!
### Locality in the spectral data
-/

theorem chainTilde_congr_m (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) {m m' : ℕ → ℂ}
    (A : ℕ → Fin N → ℂ) (n : ℕ) :
    ∀ j l, l - j = n → (∀ p, j ≤ p → p ≤ l → m p = m' p) →
      Split.chainTilde σ S m A j l = Split.chainTilde σ S m' A j l := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j l hn hm
  rw [Split.chainTilde_eq σ S m A j l, Split.chainTilde_eq σ S m' A j l]
  by_cases hjl : j < l
  · simp only [hjl, ite_true]
    rw [hm j le_rfl hjl.le, hm l hjl.le le_rfl,
      ih (l - (j + 1)) (by omega) (j + 1) l rfl fun p hp hp' => hm p (by omega) hp']
    congr 2
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    rw [hm i (by omega) (by omega),
      ih (i - j) (by omega) j i rfl fun p hp hp' => hm p hp (by omega),
      ih (l - i) (by omega) i l rfl fun p hp hp' => hm p (by omega) hp']
  · simp only [hjl, ite_false]

theorem chainM_congr_m (σ : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) {m m' : ℕ → ℂ}
    (A : ℕ → Fin N → ℂ) {j l : ℕ} (hm : ∀ p, j ≤ p → p ≤ l → m p = m' p) :
    Split.chainM σ S m A j l = Split.chainM σ S m' A j l := by
  rw [Split.chainM, Split.chainM, chainTilde_congr_m σ S A (l - j) j l rfl hm]
  congr 1
  exact Finset.prod_congr rfl fun p hp => hm p (Finset.mem_Icc.mp hp).1
    (Finset.mem_Icc.mp hp).2

/-!
### Index bookkeeping
-/

theorem prod_Icc_one_eq_range {M : Type*} [CommMonoid M] (g : ℕ → M) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 k, g i = ∏ i ∈ Finset.range k, g (i + 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem prod_rotateChain {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∏ i ∈ Finset.Icc 1 (k + 1), Split.rotateChain (k + 1) f i =
      ∏ i ∈ Finset.Icc 1 (k + 1), f i := by
  rw [prod_Icc_one_eq_range, prod_Icc_one_eq_range,
    Finset.prod_range_succ' (fun i => Split.rotateChain (k + 1) f (i + 1)) k,
    Finset.prod_range_succ (fun i => f (i + 1)) k]
  congr 1

/-- The nonzero extension of the pattern values (`semicircleM z` outside `[1, k]`). -/
def mExt (z : ℂ) {k : ℕ} (σ : Fin k → Bool) : ℕ → ℂ :=
  fun p => if 1 ≤ p ∧ p ≤ k then patM z σ p else semicircleM z

theorem patConj_ne_zero (b : Bool) {w : ℂ} (hw : w ≠ 0) : VS.patConj b w ≠ 0 := by
  cases b <;> simp [VS.patConj, hw]

theorem mExt_ne_zero (z : ℂ) {k : ℕ} (σ : Fin k → Bool) (p : ℕ) : mExt z σ p ≠ 0 := by
  have hm0 : semicircleM z ≠ 0 := ne_zero_of_root (semicircleM_dyson z)
  unfold mExt patM
  split_ifs <;> first | exact patConj_ne_zero _ hm0 | exact hm0

theorem norm_mExt_lt_one {z : ℂ} (hz : z.im ≠ 0) {k : ℕ} (σ : Fin k → Bool) (p : ℕ) :
    ‖mExt z σ p‖ < 1 := by
  unfold mExt
  split_ifs
  · exact norm_patM_lt_one hz σ p
  · exact norm_semicircleM_lt_one hz

theorem mExt_eq {z : ℂ} {k : ℕ} (σ : Fin k → Bool) {p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ k) :
    mExt z σ p = patM z σ p := by
  rw [mExt, ite_eq_left ⟨h1, h2⟩]

theorem patM_wardHead (z : ℂ) (σ : Fin (n + 2) → Bool) {p : ℕ} (h1 : 1 ≤ p)
    (h2 : p ≤ n + 1) : patM z (wardPatHead σ) p = patM z σ p := by
  unfold patM
  rw [dite_eq_left ⟨h1, h2⟩, dite_eq_left ⟨h1, by omega⟩]
  rfl

theorem patM_wardLast (z : ℂ) (σ : Fin (n + 2) → Bool) {p : ℕ} (h1 : 1 ≤ p)
    (h2 : p ≤ n + 1) :
    patM z (wardPatLast σ) p = if p = 1 then patM z σ (n + 2) else patM z σ p := by
  have hl := patM_of_mem z σ (Fin.last (n + 1))
  simp only [Fin.val_last] at hl
  unfold patM
  rw [dite_eq_left ⟨h1, h2⟩]
  by_cases hp : p = 1
  · subst hp
    rw [ite_eq_left rfl, dite_eq_left ⟨by omega, le_rfl⟩]
    simp [wardPatLast]
    rfl
  · rw [ite_eq_right hp, dite_eq_left ⟨h1, by omega⟩]
    have hne : (⟨p - 1, by omega⟩ : Fin (n + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega
    simp only [wardPatLast, hne, ite_false]
    rfl

theorem obsSeq_wardSites (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin (n + 2) → Fin N) {p : ℕ}
    (h2 : p ≤ n + 1) : obsSeq S (wardSites x) p = obsSeq S x p := by
  unfold obsSeq
  by_cases h1 : 1 ≤ p
  · rw [dite_eq_left ⟨h1, h2⟩, dite_eq_left ⟨h1, by omega⟩]
    rfl
  · rw [dite_eq_right (by omega), dite_eq_right (by omega)]

/-- `zParam t (m_{j+1}) = z_{j,t}` (`-1/m - tm = z_t`). -/
theorem zParam_patM (z : ℂ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (j : Fin k) :
    Split.zParam t (patM z σ ((j : ℕ) + 1)) = patZ z σ t j := by
  rw [patM_of_mem, patZ]
  have h := (vsFlow_a z t).1
  have hz : vsTraj z t = -1 / semicircleM z - (t : ℂ) * semicircleM z := by
    rw [h]
    ring
  unfold Split.zParam
  cases σ j
  · simp [VS.patConj, hz]
  · simp [VS.patConj, hz, map_div₀]

/-!
### The `M`-part
-/

/-- **The `M`-part of the Ward reduction** (the `M`-Ward identity at the junction `(z_k, z_1)`),
under the hypotheses `Split.CyclicStatement` and `Split.WardStatement`. For stochastic symmetric
`S`, `Im z ≠ 0`, `t ∈ [0,1]`, `σ_last ≠ σ_0`:
`Tr[M_{[1,k]}] = (z_k - z_1)⁻¹ (Tr[M^{σ'}_{[1,k-1]} S^{x_{k-1}}] -`
`Tr[M^{σ''}_{[1,k-1]} S^{x_{k-1}}])`.
-/
theorem ward_mChain (hC : Split.CyclicStatement) (hW : Split.WardStatement) (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0) (σ : Fin (n + 2) → Bool)
    (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ b, P.mChain σ x t b =
      (Split.zParam t (patM P.z σ (n + 2)) - Split.zParam t (patM P.z σ 1))⁻¹ *
        (∑ b, P.mChain (wardPatLast σ) (wardSites x) t b * obsSeq P.S (wardSites x) (n + 1) b -
          ∑ b, P.mChain (wardPatHead σ) (wardSites x) t b *
            obsSeq P.S (wardSites x) (n + 1) b) := by
  have hprof := stochasticSymm_iff_profileHyp.mp hS
  set me := mExt P.z σ with hme
  set Ae := update (obsSeq P.S x) (n + 2) (fun _ => (1 : ℂ)) with hAe
  set rm := Split.rotateChain (n + 2) me
  set rA := Split.rotateChain (n + 2) Ae
  -- (1) extension
  have h1 : P.mChain σ x t = Split.chainM t P.S me Ae 1 (n + 2) := by
    rw [PsiData.mChain]
    calc Split.chainM t P.S (patM P.z σ) (obsSeq P.S x) 1 (n + 2) =
        Split.chainM t P.S me (obsSeq P.S x) 1 (n + 2) :=
          chainM_congr_m t P.S _ fun p hp hp' => (mExt_eq σ hp hp').symm
      _ = Split.chainM t P.S me Ae 1 (n + 2) :=
          chainM_congr t P.S me (A' := Ae) fun p _ hp' => by rw [hAe, update_of_ne (by omega)]
  -- (2)-(4) cyclicity and the product
  have hcyc := hC N P.S hprof t ht me (norm_mExt_lt_one hz σ) Ae (n + 2) (by omega)
  have hAk : Ae (n + 2) = fun _ => 1 := by rw [hAe, update_self]
  have hprod : ∏ i ∈ Finset.Icc 1 (n + 2), rm i = ∏ i ∈ Finset.Icc 1 (n + 2), me i :=
    prod_rotateChain me (n + 1)
  have h2 : ∑ b, Split.chainM t P.S me Ae 1 (n + 2) b =
      ∑ b, Ae (n + 1) b * Split.chainM t P.S rm rA 1 (n + 2) b := by
    simp only [Split.chainM, Pi.smul_apply, smul_eq_mul, hprod]
    rw [← Finset.mul_sum]
    simp only [mul_left_comm _ (∏ i ∈ Finset.Icc 1 (n + 2), me i)]
    rw [← Finset.mul_sum]
    congr 1
    rw [hAk] at hcyc
    simpa using hcyc
  -- (5) Ward at the interior position 1 of the rotated chain
  have hrA1 : rA 1 = fun _ => 1 := by simp [rA, Split.rotateChain, hAk]
  have hrm1 : rm 1 = patM P.z σ (n + 2) := by
    simp [rm, Split.rotateChain, hme, mExt_eq σ (by omega : 1 ≤ n + 2) le_rfl]
  have hrm2 : rm (1 + 1) = patM P.z σ 1 := by
    simp only [rm, Split.rotateChain]
    rw [ite_eq_right (by omega), show 1 + 1 - 1 = 1 by rfl, hme, mExt_eq σ le_rfl (by omega)]
  have hne : rm 1 ≠ rm (1 + 1) := by
    rw [hrm1, hrm2]
    have e1 := patM_of_mem P.z σ (Fin.last (n + 1))
    have e0 := patM_of_mem P.z σ 0
    simp only [Fin.val_last, Fin.val_zero] at e1 e0
    rw [e1, e0]
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
    cases h1 : σ (Fin.last (n + 1)) <;> cases h0 : σ 0 <;> simp_all [VS.patConj]
  have hrmn : ∀ i, ‖rm i‖ < 1 := fun i => by
    simp only [rm, Split.rotateChain]
    split_ifs <;> exact norm_mExt_lt_one hz σ _
  have hrm0 : ∀ i, rm i ≠ 0 := fun i => by
    simp only [rm, Split.rotateChain]
    split_ifs <;> exact mExt_ne_zero P.z σ _
  have hward := hW N P.S hprof t ht rm hrmn hrm0 rA (n + 2) 1 (by omega) le_rfl (by omega) hrA1 hne
  -- (6) the two reduced chains
  have hrA : ∀ p, 1 ≤ p → p < n + 1 →
      Split.dropAt 1 rA p = obsSeq P.S (wardSites x) p := by
    intro p hp hp'
    simp only [Split.dropAt, rA, Split.rotateChain]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), show p + 1 - 1 = p by omega, hAe,
      update_of_ne (by omega), obsSeq_wardSites P.S x (by omega)]
  have hM' : Split.chainM t P.S (Split.dropAt (1 + 1) rm) (Split.dropAt 1 rA) 1 (n + 2 - 1) =
      P.mChain (wardPatLast σ) (wardSites x) t := by
    rw [PsiData.mChain, show n + 2 - 1 = n + 1 by omega]
    calc Split.chainM t P.S (Split.dropAt (1 + 1) rm) (Split.dropAt 1 rA) 1 (n + 1) =
        Split.chainM t P.S (patM P.z (wardPatLast σ)) (Split.dropAt 1 rA) 1 (n + 1) :=
          chainM_congr_m t P.S _ fun p hp hp' => by
            rw [patM_wardLast P.z σ hp hp']
            simp only [Split.dropAt, rm, Split.rotateChain]
            by_cases h1 : p = 1
            · subst h1
              simp [hme, mExt_eq σ (by omega : 1 ≤ n + 2) le_rfl]
            · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1,
                show p + 1 - 1 = p by omega, hme, mExt_eq σ hp (by omega)]
      _ = _ := chainM_congr t P.S _ (A' := obsSeq P.S (wardSites x)) hrA
  have hM'' : Split.chainM t P.S (Split.dropAt 1 rm) (Split.dropAt 1 rA) 1 (n + 2 - 1) =
      P.mChain (wardPatHead σ) (wardSites x) t := by
    rw [PsiData.mChain, show n + 2 - 1 = n + 1 by omega]
    calc Split.chainM t P.S (Split.dropAt 1 rm) (Split.dropAt 1 rA) 1 (n + 1) =
        Split.chainM t P.S (patM P.z (wardPatHead σ)) (Split.dropAt 1 rA) 1 (n + 1) :=
          chainM_congr_m t P.S _ fun p hp hp' => by
            rw [patM_wardHead P.z σ hp hp']
            simp only [Split.dropAt, rm, Split.rotateChain]
            rw [ite_eq_right (by omega), ite_eq_right (by omega), show p + 1 - 1 = p by omega,
              hme, mExt_eq σ hp (by omega)]
      _ = _ := chainM_congr t P.S _ (A' := obsSeq P.S (wardSites x)) hrA
  have hAn : Ae (n + 1) = obsSeq P.S (wardSites x) (n + 1) := by
    rw [hAe, update_of_ne (by omega), obsSeq_wardSites P.S x le_rfl]
  rw [h1, h2, hward, hrm1, hrm2, hM', hM'', hAn]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => by ring

/-!
### The Ward reduction
-/

theorem sum_obsMat {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) :
    ∑ a, obsMat S a = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [obsMat, Matrix.diagonal_apply, Split.rowObs, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [← Complex.ofReal_sum]
    have : ∑ a, S a i = 1 := by
      rw [← hS.rowSum i]
      exact Finset.sum_congr rfl fun a _ => hS.symm a i
    rw [this, Complex.ofReal_one]
  · simp [hij]

/-- `𝒯_k[𝒳^k](x') = Tr[G_{[1,k]}(x')] - Tr[M_{[1,k]}(x')]` (columns of `S` sum to one). -/
theorem sum_avErr_last (P : PsiData N) (hS : StochasticSymm P.S) (σ : Fin (n + 2) → Bool)
    (x : Fin (n + 2) → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    ∑ a, P.avErr σ (update x (Fin.last (n + 1)) a) t H =
      trace (gChain (patZ P.z σ t) (isoSlots P.S x) H) - ∑ b, P.mChain σ x t b := by
  have hl : ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) + 1 = n + 2 := by simp
  have hG : ∀ a, gChain (patZ P.z σ t) (avSlots P.S (update x (Fin.last (n + 1)) a)) H =
      gHead (isoSlots P.S x) (slotsH P.z σ t H) (Fin.last (n + 1)) * obsMat P.S a := by
    intro a
    rw [avSlots_update, update_avSlots_last P.S x hl, gChain]
    exact slotProd_updateB_last _ _ hl _
  have hG0 : gChain (patZ P.z σ t) (isoSlots P.S x) H =
      gHead (isoSlots P.S x) (slotsH P.z σ t H) (Fin.last (n + 1)) := by
    have h := slotProd_updateB_last (isoSlots P.S x) (slotsH P.z σ t H) hl
      (isoSlots P.S x (Fin.last (n + 1)))
    rw [update_eq_self] at h
    have h' : gChain (patZ P.z σ t) (isoSlots P.S x) H =
        slotProd (isoSlots P.S x) (slotsH P.z σ t H) := rfl
    rw [h', h]
    simp [isoSlots]
  simp only [PsiData.avErr]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [hG, ← trace_sum, ← Matrix.mul_sum, sum_obsMat hS, Matrix.mul_one, hG0]
  · simp_rw [mChain_update_last P σ x t hl, obsSeq_update, hl, update_self, Split.rowObs]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, ← Complex.ofReal_sum]
    have : ∑ a, P.S a b = 1 := by
      rw [← hS.rowSum b]
      exact Finset.sum_congr rfl fun a _ => hS.symm a b
    rw [this, Complex.ofReal_one, mul_one]

/-- **The Ward reduction**, under the hypotheses `Split.CyclicStatement` and
`Split.WardStatement` (proved as `MTerms.cyclic_holds`, `MTerms.ward_holds`). For stochastic
symmetric `S`, `Im z > 0`, `t ∈ [0,1]`, Hermitian `H`, a chain of length `k = n+2` with
`σ_last ≠ σ_0`: `∑_a 𝒳^k(x', a) = (z_k - z_1)⁻¹ (𝒳^{k-1}_{σ'}(x') - 𝒳^{k-1}_{σ''}(x'))`. -/
theorem wardReduction (hC : Split.CyclicStatement) (hW : Split.WardStatement) (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : 0 < P.z.im) (σ : Fin (n + 2) → Bool)
    (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ∑ a, P.avErr σ (update x (Fin.last (n + 1)) a) t H =
      (patZ P.z σ t (Fin.last (n + 1)) - patZ P.z σ t 0)⁻¹ *
        (P.avErr (wardPatLast σ) (wardSites x) t H -
          P.avErr (wardPatHead σ) (wardSites x) t H) := by
  have e1 : Split.zParam t (patM P.z σ (n + 2)) = patZ P.z σ t (Fin.last (n + 1)) :=
    zParam_patM P.z σ t (Fin.last (n + 1))
  have e0 : Split.zParam t (patM P.z σ 1) = patZ P.z σ t 0 := zParam_patM P.z σ t 0
  rw [sum_avErr_last P hS, ward_gChain P.S hz σ hσ x ht.2 hH,
    ward_mChain hC hW P hS hz.ne' σ hσ x ht, e1, e0]
  simp only [PsiData.avErr]
  ring

/-- `|z_k - z_1| ≥ 2η_t` for `σ_last ≠ σ_0`. -/
theorem two_eta_le_norm_patZ_sub {z : ℂ} {k : ℕ} (σ : Fin k → Bool) {t : ℝ}
    {i j : Fin k} (hij : σ i ≠ σ j) : 2 * vsHeight z t ≤ ‖patZ z σ t i - patZ z σ t j‖ := by
  have h := Complex.abs_im_le_norm (patZ z σ t i - patZ z σ t j)
  rw [Complex.sub_im, patZ_im, patZ_im] at h
  by_cases hi : σ i <;> by_cases hj : σ j
  · exact absurd (by rw [hi, hj]) hij
  · simp only [hi, hj, ite_true, Bool.false_eq_true, ite_false] at h
    have : |-vsHeight z t - vsHeight z t| = 2 * |vsHeight z t| := by
      rw [show -vsHeight z t - vsHeight z t = -(2 * vsHeight z t) by ring, abs_neg, abs_mul,
        abs_two]
    rw [this] at h
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two).trans h
  · simp only [hi, hj, ite_true, Bool.false_eq_true, ite_false] at h
    have : |vsHeight z t - -vsHeight z t| = 2 * |vsHeight z t| := by
      rw [show vsHeight z t - -vsHeight z t = 2 * vsHeight z t by ring, abs_mul, abs_two]
    rw [this] at h
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two).trans h
  · exact absurd (by simp only [Bool.not_eq_true] at hi hj; rw [hi, hj]) hij

/-- **The Ward reduction, size form**: under the hypotheses of `wardReduction`,
`‖𝒯_k[𝒳^k](x')‖ ≤ (2η_t)⁻¹ (‖𝒳^{k-1}_{σ'}(x')‖ + ‖𝒳^{k-1}_{σ''}(x')‖)`. -/
theorem wardReduction_norm (hC : Split.CyclicStatement) (hW : Split.WardStatement)
    (P : PsiData N) (hS : StochasticSymm P.S) (hz : 0 < P.z.im) (σ : Fin (n + 2) → Bool)
    (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    ‖∑ a, P.avErr σ (update x (Fin.last (n + 1)) a) t H‖ ≤
      (2 * vsHeight P.z t)⁻¹ * (‖P.avErr (wardPatLast σ) (wardSites x) t H‖ +
        ‖P.avErr (wardPatHead σ) (wardSites x) t H‖) := by
  rw [wardReduction hC hW P hS hz σ hσ x ht hH, norm_mul, norm_inv]
  have hη := vsHeight_pos hz ht.2
  have h2 := two_eta_le_norm_patZ_sub (z := P.z) σ (t := t) hσ
  refine mul_le_mul ((inv_le_inv₀ (by linarith) (by positivity)).mpr h2) (norm_sub_le _ _)
    (norm_nonneg _) (inv_nonneg.mpr (by positivity))

end BlockBand.Native.ErdosRiabov.Evol
