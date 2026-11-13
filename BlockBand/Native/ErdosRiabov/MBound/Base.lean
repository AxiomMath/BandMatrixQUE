module

public import BlockBand.Native.ErdosRiabov.MBound.NonSat

/-!
# Base cases of the `M`-bounds, lengths 1 and 2

Under `MBCtx d P`: `AvB(1, 1)`, `IsoB(1, 1)`, `AvB(2, C_K²)`, `IsoB(2, C_K)` (`C_K = vsCK d`),
from `|m| < 1`, `Υ_h(a,a) = (ℓh)⁻¹`, the kernel bounds (K1) of the kernel lemma
(`|T̂_t| ≤ C_K Υ_t`, `|X̂_t| ≤ C_K Υ_{η_0} ≤ C_K Υ_t`,
the conjugate kernel by `vsPropagator_conj`) and (K4) (`S Υ ≤ C_K Υ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.LemmaK
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-- The conjugate kernel: `A_t(conj μ, conj μ')_{ax} = conj A_t(μ, μ')_{ax}`. -/
theorem mb_vsKernel_conj {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {μ μ' : ℂ}
    {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (a x : Fin N) :
    vsKernel S (conj μ) (conj μ') t a x = conj (vsKernel S μ μ' t a x) := by
  have hc : (t : ℂ) * (conj μ * conj μ') = conj ((t : ℂ) * (μ * μ')) := by
    simp only [map_mul, Complex.conj_ofReal]
  have ht' : ‖(t : ℂ) * (conj μ * conj μ')‖ < 1 := by rwa [hc, Complex.norm_conj]
  have h := vsPropagator_conj hS (s := t - 1) ht a x
  rw [vsPropagator_eq hS ht', vsPropagator_eq hS ht] at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub,
    Complex.ofReal_one, sub_sub_cancel, one_mul, map_add] at h
  have h1 : conj ((1 : Matrix (Fin N) (Fin N) ℂ) a x) = (1 : Matrix (Fin N) (Fin N) ℂ) a x := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [h1] at h
  exact add_left_cancel h

section VS

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in
/-- (K1) for every pair of pattern letters: `|A_t(m_a, m_b)| ≤ C_K Υ_t`, `t ∈ [0,1]`. -/
theorem mb_kernel_bound (a b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u v : Fin (m * W)) :
    ‖vsKernel P.S (VS.patConj a (semicircleM P.z)) (VS.patConj b (semicircleM P.z)) t u v‖ ≤
      vsCK d * P.ups t u v := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  obtain ⟨hK1, hK2, -, -⟩ := lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hc.hm hc.hW hc.hz ht.1 ht.2
  have hups : P.ups t u v = polynomialControl (m * W) W d.D (vsHeight P.z t) u v := by
    unfold PsiData.ups
    rw [hc.hPW, hc.hPD]
  have hη := hc.zpos
  have hηt := vsHeight_pos hη ht.2
  have hmono : polynomialControl (m * W) W d.D (vsHeight P.z 0) u v ≤
      polynomialControl (m * W) W d.D (vsHeight P.z t) u v :=
    polynomialControl_mono hN hc.hW (by linarith [d.D_ge_six]) hηt
      (mb_heights hc ht.1) u v
  have hCK := (vsCK_pos d).le
  have hXi : ‖vsKernel P.S (semicircleM P.z) (semicircleM P.z) t u v‖ ≤ vsCK d * P.ups t u v := by
    rw [hups, hc.hPS]
    exact (hK2 u v).trans (mul_le_mul_of_nonneg_left hmono hCK)
  have hTh : ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) t u v‖ ≤
      vsCK d * P.ups t u v := by
    rw [hups, hc.hPS]
    exact hK1 u v
  cases a <;> cases b <;> simp only [VS.patConj, Bool.false_eq_true, ite_false, ite_true]
  · exact hXi
  · exact hTh
  · rw [vsKernel_swap]; exact hTh
  · rw [mb_vsKernel_conj hc.stoch (norm_smul_lt_one (mb_norm_m_lt hη) (mb_norm_m_lt hη) ht.1 ht.2),
      Complex.norm_conj]
    exact hXi

include hc in
theorem mb_ups_self (t : ℝ) (a : Fin (m * W)) :
    P.ups t a a = (P.lEta t)⁻¹ := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  unfold PsiData.ups PsiData.lEta
  rw [hc.hPW, BlockBand.Internal.Contracts.Inputs.polynomialControl,
    BlockBand.Adapters.ErdosRiabov.cyclicDistance_self]
  simp

/-- `M_{[1,1]} = m_1`. -/
theorem mb_mChain_one (P : PsiData N) (σ : Fin 1 → Bool) (x : Fin 1 → Fin N) (t : ℝ)
    (a : Fin N) : P.mChain σ x t a = VS.patConj (σ 0) (semicircleM P.z) := by
  unfold PsiData.mChain
  rw [Split.chainM, Evol.chainTilde_self]
  simp only [Finset.Icc_self, Finset.prod_singleton, Pi.smul_apply, smul_eq_mul, mul_one]
  exact patM_of_mem P.z σ 0

include hc in
/-- **Base case**, length 1: `AvB(1, 1)`. -/
theorem mbBase_av1 : MBAvB P 1 1 := by
  intro t ht σ x
  have hL := (hc.inputs ht).lEta_pos
  unfold avM
  simp only [mb_mChain_one]
  rw [← Finset.mul_sum, mb_obsSeq_apply _ _ le_rfl le_rfl]
  have hsum : ∑ a, Split.rowObs P.S (x ⟨1 - 1, by omega⟩) a = 1 := by
    simp only [Split.rowObs]
    rw [← Complex.ofReal_sum, hc.stoch.rowSum, Complex.ofReal_one]
  rw [hsum, mul_one, norm_patConj, contr_sAv_one P rfl, mul_inv_cancel₀ hL.ne', one_mul]
  exact (norm_semicircleM_lt_one hc.zpos.ne').le

include hc in
/-- **Base case**, length 1: `IsoB(1, 1)`. -/
theorem mbBase_iso1 : MBIsoB P 1 1 := by
  intro t ht σ a x
  have hL := (hc.inputs ht).lEta_pos
  rw [mb_mChain_one, norm_patConj, one_mul]
  have hs : P.sIso a a x t = Real.sqrt (P.lEta t)⁻¹ := by
    unfold PsiData.sIso
    simp only [Nat.cast_one, sub_self, neg_zero, zero_div, Real.rpow_zero, one_mul,
      Finset.range_one, Finset.prod_singleton]
    rw [zero_add, contr_isoPoint_zero, contr_isoPoint_of_le _ _ _ one_ne_zero le_rfl,
      mb_ups_self hc t]
  rw [hs, ← Real.sqrt_mul hL.le, mul_inv_cancel₀ hL.ne', Real.sqrt_one]
  exact (norm_semicircleM_lt_one hc.zpos.ne').le

/-- `M_{[1,2]}(a) = A_t(m_1, m_2)(x_0, a)`. -/
theorem mb_mChain_two (P : PsiData N) (hS : StochasticSymm P.S) (σ : Fin 2 → Bool)
    (x : Fin 2 → Fin N) (t : ℝ) (a : Fin N) :
    P.mChain σ x t a = vsKernel P.S (VS.patConj (σ 0) (semicircleM P.z))
      (VS.patConj (σ 1) (semicircleM P.z)) t (x 0) a := by
  have h2 : P.mChain σ x t = Split.chainM t P.S (patM P.z σ) (obsSeq P.S x) 1 (1 + 1) := rfl
  have hp1 : patM P.z σ 1 = VS.patConj (σ 0) (semicircleM P.z) := patM_of_mem P.z σ 0
  have hp2 : patM P.z σ (1 + 1) = VS.patConj (σ 1) (semicircleM P.z) := patM_of_mem P.z σ 1
  rw [h2, chainM_adj, vsKernel_apply_stabOp, hp1, hp2, mb_obsSeq_apply _ _ le_rfl (by omega)]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Split.rowObs]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [stabOp_symm hS.symm]
  ring_nf
  rfl

include hc in
/-- **Base case**, length 2: `IsoB(2, C_K)`. -/
theorem mbBase_iso2 : MBIsoB P 2 (vsCK d) := by
  intro t ht σ a x
  have hin := hc.inputs ht
  have hL := hin.lEta_pos
  have hU := hin.nonneg
  rw [mb_mChain_two P hc.stoch]
  have hs : Real.sqrt (P.lEta t) * P.sIso a a x t = P.ups t (x 0) a := by
    unfold PsiData.sIso
    simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul]
    rw [contr_isoPoint_zero, zero_add, contr_isoPoint_succ _ _ _ (by norm_num),
      contr_isoPoint_of_le _ _ _ two_ne_zero le_rfl, hin.symm a]
    have he : (-(((2 : ℕ) : ℝ) - 1) / 2) = -(1 / 2 : ℝ) := by norm_num
    rw [he, Real.sqrt_mul_self (hU _ _), ← mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    norm_num
  rw [hs]
  exact mb_kernel_bound hc (σ 0) (σ 1) ht (x 0) a

include hc in
/-- **Base case**, length 2: `AvB(2, C_K²)`. -/
theorem mbBase_av2 : MBAvB P 2 (vsCK d ^ 2) := by
  intro t ht σ x
  have hin := hc.inputs ht
  have hL := hin.lEta_pos
  have hCK := (vsCK_pos d).le
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  unfold avM
  simp only [mb_mChain_two P hc.stoch]
  rw [mb_obsSeq_apply _ _ (by omega) le_rfl]
  have hs : P.lEta t * P.sAv x t = P.ups t (x 1) (x 0) := by
    rw [mb_sAv_last P t (n := 0) x]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    have e1 : P.ups t (x (Fin.last 0).castSucc) (x (Fin.last 1)) *
        P.ups t (x (Fin.last 1)) (x 0) = P.ups t (x 1) (x 0) * P.ups t (x 1) (x 0) := by
      rw [show (Fin.last 0).castSucc = (0 : Fin 2) from rfl,
        show Fin.last 1 = (1 : Fin 2) from rfl, hin.symm (x 0) (x 1)]
    rw [e1, Real.sqrt_mul_self (hin.nonneg _ _), ← mul_assoc]
    have he : P.lEta t * P.lEta t ^ (-((0 + 2 : ℕ) : ℝ) / 2) = 1 := by
      rw [show (-((0 + 2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one,
        mul_inv_cancel₀ hL.ne']
    rw [he, one_mul]
  rw [hs]
  have hK4 := (lemmaK_K4 (κ := d.kappa) (C₀ := d.C0) (D := d.D) d.b_pos d.b_lt_half
    d.kappa_pos d.C0_ge_one
    (by linarith [d.D_ge_six]) hc.hm hc.hW (vsHeight_pos hc.zpos ht.2)
    ((P.height_bounds hN hc.hW (Nat.le_mul_of_pos_left W (by have := hc.hm; omega))
      d.kappa_pos (by linarith [d.C0_ge_one]) hc.hz hc.hPW ht.1 ht.2).2.1) (x 1) (x 0)).2
  have hups : ∀ u v, P.ups t u v = polynomialControl (m * W) W d.D (vsHeight P.z t) u v := by
    intro u v
    unfold PsiData.ups
    rw [hc.hPW, hc.hPD]
  calc ‖∑ a, vsKernel P.S (VS.patConj (σ 0) (semicircleM P.z))
          (VS.patConj (σ 1) (semicircleM P.z)) t (x 0) a * Split.rowObs P.S (x ⟨2 - 1, _⟩) a‖
      ≤ ∑ a, vsCK d * P.ups t (x 0) a * P.S (x 1) a := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        rw [norm_mul]
        refine mul_le_mul (mb_kernel_bound hc _ _ ht _ _) (le_of_eq ?_) (norm_nonneg _)
          (mul_nonneg hCK (hin.nonneg _ _))
        simp only [Split.rowObs, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (hc.stoch.nonneg _ _)]
        rfl
    _ = vsCK d * (P.S * P.ups t) (x 1) (x 0) := by
        rw [Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hin.symm (x 0) a]
        ring
    _ ≤ vsCK d * (vsCK d * P.ups t (x 1) (x 0)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCK
        have : P.S * P.ups t = shortRingProfile d.b m W *
            polynomialControl (m * W) W d.D (vsHeight P.z t) := by
          rw [hc.hPS]
          congr 1
          funext u v
          exact hups u v
        rw [this, hups]
        exact hK4
    _ = _ := by ring

end VS

end BlockBand.Native.ErdosRiabov.MBound
