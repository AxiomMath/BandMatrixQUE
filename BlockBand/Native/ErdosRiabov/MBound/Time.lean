module

public import BlockBand.Native.ErdosRiabov.MBound.Forcing
public import BlockBand.Native.ErdosRiabov.Prop.Bridge

/-!
# Slot operators as tensor matrices; the saturated kernel `T̂_t`

One-slot operators as tensor matrices, and the saturated kernel `T̂_t` with its bounds.

* `mbSlotMat j K = I ⊗ … ⊗ K ⊗ … ⊗ I` (`K` at slot `j`); `mbSlot_eq_propOp`: the slot operator
  `K^{(j)}` is `propOp (mbSlotMat j K)`; `mbSlot_tensor_comm`: `K^{(j)}` commutes with a tensor
  propagator whose slot-`j` factor commutes with `K`; `mbSlot_mul`: `(KK')^{(j)} = K^{(j)}K'^{(j)}`.
* `mbTheta P t = T̂_t = vsKernel P.S m m̄ t`; for a saturated pattern every generator kernel
  `Evol.aKer P σ j t` is `T̂_t` (`aKer_eq_mbTheta`), so `mbAvGen = (⊕_j T̂^{(j)}_t)[Tr M]`
  (`mbAvGen_eq_oplus`), and `⊕_j T̂^{(j)}_t = propOp (vsTensorGen S m m̄ t)` (`mbOplus_eq_propOp`).
* VS facts (`VSData` `d`, `m ≥ 4`, `W ≥ 1`, `P.S = shortRingProfile d.b m W`, `P.W = W`,
  `P.D = d.D`, `P.z ∈ 𝒟`, `t ∈ [0,1]`): `‖T̂_t‖ ≤ C_K Υ_t` (`mbTheta_bound`, clause (K1) of the
  kernel lemma),
  symmetry and constant row/column sums (`mbTheta_symm`, `mbTheta_rowSum`, `mbTheta_colSum`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators

variable {N k : ℕ}

/-!
## Slot operators as matrices
-/

/-- `I ⊗ … ⊗ K ⊗ … ⊗ I` (`K` at slot `j`). -/
def mbSlotMat (j : Fin k) (K : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  tensorMat (update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) j K)

/-- `K^{(j)} f = propOp (mbSlotMat j K) f`. -/
theorem mbSlot_eq_propOp (K : Matrix (Fin N) (Fin N) ℂ) (j : Fin k)
    (f : (Fin k → Fin N) → ℂ) : mbSlot K j f = propOp (mbSlotMat j K) f := by
  funext x
  rw [propOp_apply]
  simp_rw [mbSlotMat, tensorMat_update_one_apply, ite_mul, zero_mul]
  have hinj : Set.InjOn (fun c : Fin N => update x j c) (Finset.univ : Finset (Fin N)) :=
    fun c _ c' _ hcc => by simpa using congrFun hcc j
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun y : Fin k → Fin N => y = update x j (y j)) =
      Finset.univ.image (fun c : Fin N => update x j c) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      exact ⟨y j, hy.symm⟩
    · rintro ⟨c, rfl⟩
      simp
  rw [hfil, Finset.sum_image hinj]
  simp [mbSlot]

theorem mbSlotMat_tensor_comm (K : Matrix (Fin N) (Fin N) ℂ) (j : Fin k)
    (F : Fin k → Matrix (Fin N) (Fin N) ℂ) (h : Commute K (F j)) :
    mbSlotMat j K * tensorMat F = tensorMat F * mbSlotMat j K := by
  rw [mbSlotMat, ← tensorMat_mul, ← tensorMat_mul]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi
    rw [update_self]
    exact h.eq
  · rw [update_of_ne hi, Matrix.one_mul, Matrix.mul_one]

/-- `K^{(j)}` commutes with `propOp (⊗ F)` when `K` commutes with the factor `F_j`. -/
theorem mbSlot_tensor_comm (K : Matrix (Fin N) (Fin N) ℂ) (j : Fin k)
    (F : Fin k → Matrix (Fin N) (Fin N) ℂ) (h : Commute K (F j)) (f : (Fin k → Fin N) → ℂ) :
    mbSlot K j (propOp (tensorMat F) f) = propOp (tensorMat F) (mbSlot K j f) := by
  rw [mbSlot_eq_propOp, mbSlot_eq_propOp, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply, ← propOp_mul, ← propOp_mul,
    mbSlotMat_tensor_comm K j F h]

/-- `(KK')^{(j)} = K^{(j)} K'^{(j)}`. -/
theorem mbSlot_mul (K K' : Matrix (Fin N) (Fin N) ℂ) (j : Fin k) (f : (Fin k → Fin N) → ℂ) :
    mbSlot (K * K') j f = mbSlot K j (mbSlot K' j f) := by
  funext x
  simp only [mbSlot, Matrix.mul_apply, update_self, update_idem, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- `⊕_i K_i^{(i)}` (`propOp` of `vsTensorGen`), pointwise. -/
theorem mbOplus_eq_propOp (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (s : ℝ)
    (f : (Fin k → Fin N) → ℂ) :
    mbOplus (vsKernel S μ μ' s) f =
      propOp (vsTensorGen S (fun _ => μ) (fun _ => μ') s) f := by
  funext x
  rw [propOp_vsTensorGen_apply]
  rfl

/-!
## The saturated kernel
-/

/-- `T̂_t = vsKernel P.S m m̄ t` (`m = m_sc(z)`). -/
def mbTheta (P : PsiData N) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t

theorem patConj_pair_sat (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) {b b' : Bool} (h : b ≠ b') :
    vsKernel S (VS.patConj b (semicircleM z)) (VS.patConj b' (semicircleM z)) =
      vsKernel S (semicircleM z) (conj (semicircleM z)) := by
  cases b <;> cases b' <;> simp only [ne_eq, not_true_eq_false] at h <;>
    simp only [VS.patConj, Bool.false_eq_true, ite_false, ite_true]
  funext t
  exact vsKernel_swap S _ _ t

/-- For a saturated pattern every generator kernel is `T̂_t`. -/
theorem aKer_eq_mbTheta (P : PsiData N) {σ : Fin k → Bool} (hσ : ¬ HasDesatFactor σ)
    (j : Fin k) (t : ℝ) : aKer P σ j t = mbTheta P t := by
  have hj := j.isLt
  have h1 : patM P.z σ ((j : ℕ) + 1) = VS.patConj (σ j) (semicircleM P.z) :=
    patM_of_mem P.z σ j
  have h2 : patM P.z σ (nextIdx j) = VS.patConj (patNext σ j) (semicircleM P.z) := by
    unfold nextIdx patNext
    by_cases h : (j : ℕ) + 1 < k
    · rw [ite_eq_left h, dite_eq_left h, mb_patM_apply _ _ (by omega) (by omega)]
      congr 2
    · rw [ite_eq_right h, dite_eq_right h, mb_patM_apply _ _ le_rfl (by omega)]
  have hne : σ j ≠ patNext σ j := fun e => hσ ⟨j, e⟩
  rw [aKer, h1, h2, mbTheta]
  exact congrFun (patConj_pair_sat P.S P.z hne) t

/-- For a saturated pattern, `mbAvGen = (⊕_j T̂^{(j)}_t)[Tr M]`. -/
theorem mbAvGen_eq_oplus (P : PsiData N) {σ : Fin k → Bool} (hσ : ¬ HasDesatFactor σ)
    (x : Fin k → Fin N) (t : ℝ) :
    mbAvGen P σ x t = mbOplus (mbTheta P t) (fun y => avM P σ y t) x := by
  unfold mbAvGen mbOplus mbSlot
  simp only [aKer_eq_mbTheta P hσ]

/-!
## VS facts for `T̂_t`
-/

section VS

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
  (hPS : P.S = shortRingProfile d.b m W) (hPW : P.W = W) (hPD : P.D = d.D)
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)

include hm hW hPS hPW hPD hz in
/-- (K1): `‖T̂_t(a,b)‖ ≤ C_K Υ_t(a,b)`, `t ∈ [0,1]`. -/
theorem mbTheta_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (a b : Fin (m * W)) :
    ‖mbTheta P t a b‖ ≤ vsCK d * P.ups t a b := by
  obtain ⟨hK1, -, -, -⟩ := lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hm hW hz ht.1 ht.2
  have := hK1 a b
  rw [mbTheta, hPS]
  unfold PsiData.ups
  rw [hPW, hPD]
  exact this

theorem mb_norm_mm_lt {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(t : ℂ) * (semicircleM z * conj (semicircleM z))‖ < 1 :=
  norm_smul_lt_one (norm_semicircleM_lt_one hz.ne')
    (by rw [Complex.norm_conj]; exact norm_semicircleM_lt_one hz.ne') ht.1 ht.2

include hm hW hPS in
theorem mbTheta_symm (hzi : 0 < P.z.im) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (a b : Fin (m * W)) :
    mbTheta P t a b = mbTheta P t b a := by
  rw [mbTheta, hPS]
  exact vsKernel_symm (shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega) hW)
    (mb_norm_mm_lt hzi ht) a b

/-- The row sum `ρ_t` of `T̂_t`. -/
def mbRho (P : PsiData N) (t : ℝ) : ℂ :=
  (semicircleM P.z * conj (semicircleM P.z)) /
    (1 - (t : ℂ) * (semicircleM P.z * conj (semicircleM P.z)))

include hm hW hPS in
theorem mbTheta_rowSum (hzi : 0 < P.z.im) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (a : Fin (m * W)) :
    ∑ b, mbTheta P t a b = mbRho P t := by
  rw [mbTheta, hPS]
  exact vsKernel_rowSum (shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega) hW)
    (mb_norm_mm_lt hzi ht) a

include hm hW hPS in
theorem mbTheta_colSum (hzi : 0 < P.z.im) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (b : Fin (m * W)) :
    ∑ a, mbTheta P t a b = mbRho P t := by
  rw [← mbTheta_rowSum d hm hW P hPS hzi ht b]
  exact Finset.sum_congr rfl fun a _ => mbTheta_symm d hm hW P hPS hzi ht a b

end VS

end BlockBand.Native.ErdosRiabov.MBound
