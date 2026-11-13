module

public import BlockBand.Native.ErdosRiabov.MBound.Time

/-!
# Rotation of the averaged `M`-term

Deterministic. The rotation results are conditional on `Split.CyclicStatement`.

* `mbAvM_rotate`: `Tr[M^σ(x)] = Tr[M^{σ∘rot}(x∘rot)]`, `rot = finRotate k` (the inverse of
  ER's cyclic shift `X^ζ(x) = X^{ρζ}(ρx)`), and its powers `mbAvM_rotate_pow`;
* `not_hasDesatFactor_comp`: rotations preserve saturation;
* `mbSlot_avM_rotTo`: `K^{(j)}[Tr M^σ](x) = K^{(last)}[Tr M^{σ'}](x')` with `x' = mbRotTo j x`,
  `σ' = σ ∘ rot^{j+1}` (saturated if `σ` is), which reduces every slot to the last one.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Evol BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Contr
open scoped BigOperators

variable {N : ℕ}

theorem mb_finRotate_symm_val {n : ℕ} (r : Fin (n + 2)) :
    (((finRotate (n + 2)).symm r : Fin (n + 2)) : ℕ) = if (r : ℕ) = 0 then n + 1 else r - 1 := by
  rcases Fin.eq_zero_or_eq_succ r with h | ⟨r', rfl⟩
  · subst h
    have : (finRotate (n + 2)).symm 0 = Fin.last (n + 1) := by
      rw [Equiv.symm_apply_eq, finRotate_last]
    rw [this]
    simp
  · have : (finRotate (n + 2)).symm r'.succ = r'.castSucc := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff]; omega)]
      simp
    rw [this]
    simp

/-- The cyclic shift `X^σ(x) = X^{σ∘rot⁻¹}(x∘rot⁻¹)` (ER: `X^ζ(x) = X^{ρζ}(ρx)`). -/
theorem mbAvM_rotate_symm (hC : Split.CyclicStatement) (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    avM P σ x t =
      avM P (fun r => σ ((finRotate (n + 2)).symm r)) (fun r => x ((finRotate (n + 2)).symm r))
        t := by
  set e := (finRotate (n + 2)).symm
  set m := mbPatMExt P.z σ with hmdef
  have hm1 : ∀ i, ‖m i‖ < 1 := norm_mbPatMExt_lt_one hz σ
  have hcyc := hC N P.S hS t ht m hm1 (obsSeq P.S x) (n + 2) (by omega)
  rw [show n + 2 - 1 = n + 1 by omega] at hcyc
  unfold avM
  rw [show (fun a => P.mChain σ x t a * obsSeq P.S x (n + 2) a) =
    fun a => (∏ i ∈ Finset.Icc 1 (n + 2), m i) *
      (Split.chainTilde t P.S m (obsSeq P.S x) 1 (n + 2) a * obsSeq P.S x (n + 2) a) from by
    funext a
    rw [mb_mChain_eq_ext, Split.chainM]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring]
  rw [← Finset.mul_sum, hcyc, Finset.mul_sum, ← mb_prod_rotateChain m n]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (obsSeq P.S x (n + 1) a), ← mul_assoc]
  congr 1
  · -- the chain
    rw [mb_mChain_eq_ext]
    have := mb_chainM_congr (σ := t) (S := P.S) (j := 1) (l := n + 2)
      (m := Split.rotateChain (n + 2) m) (m' := mbPatMExt P.z (fun r => σ (e r)))
      (A := Split.rotateChain (n + 2) (obsSeq P.S x)) (A' := obsSeq P.S (fun r => x (e r)))
      (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)
    · rw [← this, Split.chainM]
      simp only [Pi.smul_apply, smul_eq_mul]
    · rw [mb_patMExt_apply _ _ hp1 hp2]
      unfold Split.rotateChain
      by_cases hp : p = 1
      · subst hp
        rw [ite_eq_left rfl, hmdef, mb_patMExt_apply _ _ (by omega) le_rfl]
        congr 2
      · rw [ite_eq_right hp, hmdef, mb_patMExt_apply _ _ (by omega) (by omega)]
        congr 2
        apply Fin.ext
        rw [mb_finRotate_symm_val]
        simp only
        rw [ite_eq_right (by omega)]
    · rw [mb_obsSeq_apply _ _ hp1 (by omega)]
      unfold Split.rotateChain
      by_cases hp : p = 1
      · subst hp
        rw [ite_eq_left rfl, mb_obsSeq_apply _ _ (by omega) le_rfl]
        congr 2
      · rw [ite_eq_right hp, mb_obsSeq_apply _ _ (by omega) (by omega)]
        congr 2
        apply Fin.ext
        rw [mb_finRotate_symm_val]
        simp only
        rw [ite_eq_right (by omega)]
  · rw [mb_obsSeq_apply _ _ (by omega) (by omega), mb_obsSeq_apply _ _ (by omega) le_rfl]
    congr 2
    apply Fin.ext
    rw [mb_finRotate_symm_val]
    simp

/-- `Tr[M^σ(x)] = Tr[M^{σ∘rot}(x∘rot)]` (`rot = finRotate`). -/
theorem mbAvM_rotate (hC : Split.CyclicStatement) (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    avM P σ x t =
      avM P (fun r => σ (finRotate (n + 2) r)) (fun r => x (finRotate (n + 2) r)) t := by
  rw [mbAvM_rotate_symm hC P hS hz ht (fun r => σ (finRotate (n + 2) r))
    (fun r => x (finRotate (n + 2) r))]
  simp only [Equiv.apply_symm_apply]

/-- **Rotation by `rot^r`**: `Tr[M^σ(x)] = Tr[M^{σ∘rot^r}(x∘rot^r)]`. Conditional on
`Split.CyclicStatement`. -/
theorem mbAvM_rotate_pow (hC : Split.CyclicStatement) (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (r : ℕ) (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N) :
    avM P σ x t = avM P (fun i => σ ((finRotate (n + 2) ^ r) i))
      (fun i => x ((finRotate (n + 2) ^ r) i)) t := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [ih, mbAvM_rotate hC P hS hz ht]
    simp only [pow_succ, Equiv.Perm.mul_apply]

theorem patNext_eq_finRotate {k : ℕ} (σ : Fin k → Bool) (j : Fin k) :
    patNext σ j = σ (finRotate k j) := by
  rcases k with _ | n
  · exact j.elim0
  unfold patNext
  by_cases h : (j : ℕ) + 1 < n + 1
  · rw [dite_eq_left h]
    congr 1
    apply Fin.ext
    rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff]; omega)]
  · rw [dite_eq_right h]
    have hj : j = Fin.last n := Fin.ext (by simp; omega)
    subst hj
    rw [finRotate_last]
    rfl

/-- Rotations preserve the absence of a non-saturated factor. -/
theorem not_hasDesatFactor_comp {k : ℕ} {σ : Fin k → Bool} (hσ : ¬ HasDesatFactor σ) (r : ℕ) :
    ¬ HasDesatFactor (fun i => σ ((finRotate k ^ r) i)) := by
  rintro ⟨i, hi⟩
  apply hσ
  refine ⟨(finRotate k ^ r) i, ?_⟩
  rw [patNext_eq_finRotate] at hi ⊢
  simp only at hi
  have hc : (finRotate k ^ r) (finRotate k i) = finRotate k ((finRotate k ^ r) i) := by
    have := congrArg (fun f : Equiv.Perm (Fin k) => f i) (Commute.self_pow (finRotate k) r).eq
    simpa only [Equiv.Perm.mul_apply] using this.symm
  rw [hi, hc]

/-- **Slot transport**: `K^{(j)}[Tr M^σ](x) = K^{(last)}[Tr M^{σ'}](mbRotTo j x)` with the
rotated pattern `σ' = σ ∘ rot^{j+1}`. Conditional on `Split.CyclicStatement`. -/
theorem mbSlot_avM_rotTo (hC : Split.CyclicStatement) (P : PsiData N)
    (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (σ : Fin (n + 2) → Bool) (j : Fin (n + 2))
    (x : Fin (n + 2) → Fin N) :
    mbSlot K j (fun y => avM P σ y t) x =
      mbSlot K (Fin.last (n + 1))
        (fun y => avM P (fun i => σ ((finRotate (n + 2) ^ ((j : ℕ) + 1)) i)) y t)
        (mbRotTo j x) := by
  unfold mbSlot
  rw [mbRotTo_last]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  show avM P σ (update x j c) t = avM P _ (update (mbRotTo j x) (Fin.last (n + 1)) c) t
  rw [mbAvM_rotate_pow hC P hS hz ht ((j : ℕ) + 1), ← mbRotTo_update]
  rfl

end BlockBand.Native.ErdosRiabov.MBound
