module

public import BlockBand.Native.ErdosRiabov.Grid.MLip
public import BlockBand.Native.ErdosRiabov.Grid.ChainLip
public import BlockBand.Native.ErdosRiabov.Grid.NormRatio

set_option autoImplicit false

/-!
# Two-time comparison of the control quantities `Ψ` (deterministic part)

Setting: `P : PsiData N` (`N, W ≥ 1`, `Im z > 0`, stochastic symmetric `S`, `D ≥ 0`), two times
`s, t ∈ [0, 1]`, two Hermitian matrices `H, H'` with `‖(H - H')_{ab}‖ ≤ δ`, and
`q = 1 + |t - s|/Im z`.

* `PsiData.heights_le_mul`: `η_t ≤ q η_s`;
* `PsiData.sIso_le_mul`, `PsiData.sAv_le_mul`, `PsiData.norm_le_mul`: the size functions and the
  normalizations `(ℓη)^{α} s^{iso/av}` change by at most `q^{E}`, `E = normExp k D`, for
  `0 ≤ α ≤ 1`.

These comparisons are used in the sibling module `PsiNear`, which proves:
* `PsiData.norm_isoErr_sub_le`, `PsiData.norm_avErr_sub_le`: the errors `𝒴`, `𝒳` are
  Lipschitz: `≤ Λ = k c^k (Im z)⁻² (N² δ + |t - s|) + B^{4(k-1)} |t - s|` (times `N` for `𝒳`),
  `c = max 1 (Im z)⁻¹`, `B ≥ 2`, `B ≥ (k - 1)(1 - |m|²)⁻¹` (M-terms: `Grid.chainM_lipschitz`);
* **`PsiData.bigPsiIso_le_of_near`**, **`PsiData.bigPsiAv_le_of_near`**: if every normalization at
  time `t` is `≥ φ > 0`, then `Ψ_t(H) ≤ q^E Ψ_s(H') + Λ/φ`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open Matrix Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {N k : ℕ}

/-- The exponent of the two-time comparison of the normalizations. -/
def normExp (k : ℕ) (D : ℝ) : ℝ :=
  3 / 2 * ((k : ℝ) / 2 + 1) + (3 / 2 + D / 2) * ((k : ℝ) / 2) + 3 / 2

theorem normExp_nonneg (k : ℕ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ normExp k D := by
  unfold normExp
  positivity

/-!
### Elementary facts on the pattern data
-/

theorem norm_patConj_sub (b : Bool) (u u' : ℂ) :
    ‖VS.patConj b u - VS.patConj b u'‖ = ‖u - u'‖ := by
  cases b
  · simp [VS.patConj]
  · simp only [VS.patConj, ite_true, ← map_sub, Complex.norm_conj]

theorem norm_patZ_sub_le {z : ℂ} (hz : z.im ≠ 0) (σ : Fin k → Bool) (t s : ℝ) (j : Fin k) :
    ‖patZ z σ t j - patZ z σ s j‖ ≤ |t - s| := by
  unfold patZ
  rw [norm_patConj_sub]
  have e : vsTraj z t - vsTraj z s = ((s - t : ℝ) : ℂ) * semicircleM z := by
    simp only [vsTraj]
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_semicircleM_lt_one hz).le

theorem abs_im_patZ {z : ℂ} (σ : Fin k → Bool) (t : ℝ) (j : Fin k) :
    |(patZ z σ t j).im| = |vsHeight z t| := by
  unfold patZ
  cases σ j <;> simp [VS.patConj, vsTraj_im]

theorem im_le_vsHeight {z : ℂ} (hz : 0 < z.im) {t : ℝ} (ht : t ≤ 1) : z.im ≤ vsHeight z t := by
  have hm := semicircleM_im_pos hz
  unfold vsHeight
  nlinarith

theorem norm_patM_le (z : ℂ) (σ : Fin k → Bool) (i : ℕ) : ‖patM z σ i‖ ≤ ‖semicircleM z‖ := by
  unfold patM
  split_ifs
  · rw [norm_patConj]
  · simp

theorem norm_rowObs_le {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) (x : Fin N) :
    ‖Split.rowObs S x‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  rw [Split.rowObs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS.nonneg x a)]
  simpa using hS.pow_le_one 1 x a

theorem norm_obsSeq_le {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    (x : Fin k → Fin N) (p : ℕ) : ‖obsSeq S x p‖ ≤ 1 := by
  unfold obsSeq
  split_ifs
  · exact norm_rowObs_le hS _
  · exact norm_one_vec_le

theorem norm_obsMat_le {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) (x : Fin N) :
    ‖obsMat S x‖ ≤ 1 := by
  rw [obsMat, l2_opNorm_diagonal]
  exact norm_rowObs_le hS x

theorem norm_isoSlots_le {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    (x : Fin k → Fin N) (l : Fin k) : ‖isoSlots S x l‖ ≤ 1 := by
  unfold isoSlots
  split_ifs
  · exact norm_obsMat_le hS _
  · exact Chains.norm_one_le

theorem norm_avSlots_le {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    (x : Fin k → Fin N) (l : Fin k) : ‖avSlots S x l‖ ≤ 1 :=
  norm_obsMat_le hS _

theorem mHyp_pat {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {z : ℂ} (hz : 0 < z.im)
    (σ : Fin k → Bool) (x : Fin k → Fin N) :
    MHyp S (patM z σ) (obsSeq S x) (‖semicircleM z‖ ^ 2) where
  stoch := hS
  r_lt := by
    have h := norm_semicircleM_lt_one hz.ne'
    have h0 := norm_nonneg (semicircleM z)
    nlinarith
  m_le := fun i => (norm_patM_lt_one hz.ne' σ i).le
  mm_le := fun i j => by
    rw [norm_mul, sq]
    exact mul_le_mul (norm_patM_le z σ i) (norm_patM_le z σ j) (norm_nonneg _) (norm_nonneg _)
  A_le := norm_obsSeq_le hS x

namespace PsiData

variable (P : PsiData N)

/-!
### Heights and normalizations
-/

/-- `η_t ≤ (1 + |t - s|/Im z) η_s` for `t, s ≤ 1`. -/
theorem heights_le_mul (hz : 0 < P.z.im) {t s : ℝ} (hs : s ≤ 1) :
    vsHeight P.z t ≤ (1 + |t - s| / P.z.im) * vsHeight P.z s := by
  have hm1 : (semicircleM P.z).im ≤ 1 :=
    (Complex.im_le_norm _).trans (norm_semicircleM_lt_one hz.ne').le
  have hm0 := semicircleM_im_pos hz
  have hηs := im_le_vsHeight hz hs
  have hdiff : vsHeight P.z t - vsHeight P.z s ≤ |t - s| := by
    rw [vsHeight_sub, ← neg_sub]
    calc -(t - s) * (semicircleM P.z).im ≤ |t - s| * 1 := by
          rw [neg_mul]
          nlinarith [neg_abs_le (t - s), abs_nonneg (t - s)]
      _ = |t - s| := mul_one _
  have h2 : |t - s| ≤ |t - s| / P.z.im * vsHeight P.z s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hz]
    exact mul_le_mul_of_nonneg_left hηs (abs_nonneg _)
  nlinarith

theorem q_ge_one (hz : 0 < P.z.im) (t s : ℝ) : 1 ≤ 1 + |t - s| / P.z.im := by
  have : 0 ≤ |t - s| / P.z.im := div_nonneg (abs_nonneg _) hz.le
  linarith

theorem lEta_le_mul (hz : 0 < P.z.im) {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) :
    P.lEta t ≤ (1 + |t - s| / P.z.im) ^ (3 / 2 : ℝ) * P.lEta s := by
  unfold Psi.PsiData.lEta
  have h1 := (PsiData.heights_le_mul P) hz (t := t) hs
  have h2 := (PsiData.heights_le_mul P) hz (t := s) ht
  rw [abs_sub_comm] at h2
  exact lEtaH_le_mul (vsHeight_pos hz ht) (vsHeight_pos hz hs) ((PsiData.q_ge_one P) hz t s) h1 h2

theorem ups_le_mul (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (hD : 0 ≤ P.D) {t s : ℝ}
    (ht : t ≤ 1) (hs : s ≤ 1) (x y : Fin N) :
    P.ups t x y ≤ (1 + |t - s| / P.z.im) ^ (3 / 2 + P.D / 2 : ℝ) * P.ups s x y := by
  unfold Psi.PsiData.ups
  have h1 := (PsiData.heights_le_mul P) hz (t := t) hs
  have h2 := (PsiData.heights_le_mul P) hz (t := s) ht
  rw [abs_sub_comm] at h2
  exact polynomialControl_le_mul hN hW hD (vsHeight_pos hz ht) (vsHeight_pos hz hs)
    ((PsiData.q_ge_one P) hz t s) h1 h2 x y

theorem lEta_rpow_neg_le_mul (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t s : ℝ}
    (ht : t ≤ 1) (hs : s ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    P.lEta t ^ (-c) ≤ (1 + |t - s| / P.z.im) ^ (3 / 2 * c) * P.lEta s ^ (-c) := by
  have hq := (PsiData.q_ge_one P) hz t s
  have h := (PsiData.lEta_le_mul P) hz hs ht
  rw [abs_sub_comm] at h
  have := rpow_neg_le_mul_rpow_neg (P.lEta_pos hN hW hz ht)
    (Real.rpow_pos_of_pos (by linarith) _) (P.lEta_pos hN hW hz hs) h hc
  rwa [← Real.rpow_mul (by linarith)] at this

theorem lEta_rpow_le_mul (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t s : ℝ}
    (ht : t ≤ 1) (hs : s ≤ 1) {c : ℝ} (hc : 0 ≤ c) :
    P.lEta t ^ c ≤ (1 + |t - s| / P.z.im) ^ (3 / 2 * c) * P.lEta s ^ c := by
  have hq := (PsiData.q_ge_one P) hz t s
  have h := (PsiData.lEta_le_mul P) hz ht hs
  have := rpow_le_mul_rpow (P.lEta_pos hN hW hz ht).le (Real.rpow_nonneg (by linarith) _)
    (P.lEta_pos hN hW hz hs).le h hc
  rwa [← Real.rpow_mul (by linarith)] at this

theorem sIso_le_mul (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (hD : 0 ≤ P.D)
    (hk : 1 ≤ k) {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) (a b : Fin N) (x : Fin k → Fin N) :
    P.sIso a b x t ≤ (1 + |t - s| / P.z.im) ^ (normExp k P.D - 3 / 2) * P.sIso a b x s := by
  set q := 1 + |t - s| / P.z.im
  have hq := (PsiData.q_ge_one P) hz t s
  have hq0 : 0 < q := by linarith
  unfold Psi.PsiData.sIso
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have e : -((k : ℝ) - 1) / 2 = -(((k : ℝ) - 1) / 2) := by ring
  rw [e]
  have h1 := (PsiData.lEta_rpow_neg_le_mul P) hN hW hz ht hs (c := ((k : ℝ) - 1) / 2) (by linarith)
  have h2 := sqrt_prod_le_mul (Finset.range k)
    (fun i => P.ups t (isoPoint a b x i) (isoPoint a b x (i + 1)))
    (fun i => P.ups s (isoPoint a b x i) (isoPoint a b x (i + 1)))
    (Real.rpow_nonneg hq0.le _) (fun i _ => (P.ups_pos hN hW hz ht _ _).le)
    (fun i _ => (PsiData.ups_le_mul P) hN hW hz hD ht hs _ _)
  rw [Finset.card_range, ← Real.rpow_mul hq0.le] at h2
  have hsq0 : 0 ≤ Real.sqrt (∏ i ∈ Finset.range k,
      P.ups t (isoPoint a b x i) (isoPoint a b x (i + 1))) := Real.sqrt_nonneg _
  calc P.lEta t ^ (-(((k : ℝ) - 1) / 2)) *
        Real.sqrt (∏ i ∈ Finset.range k, P.ups t (isoPoint a b x i) (isoPoint a b x (i + 1)))
      ≤ (q ^ (3 / 2 * (((k : ℝ) - 1) / 2)) * P.lEta s ^ (-(((k : ℝ) - 1) / 2))) *
        (q ^ ((3 / 2 + P.D / 2) * ((k : ℝ) / 2)) * Real.sqrt (∏ i ∈ Finset.range k,
          P.ups s (isoPoint a b x i) (isoPoint a b x (i + 1)))) :=
        mul_le_mul h1 h2 hsq0 (mul_nonneg (Real.rpow_nonneg hq0.le _)
          (Real.rpow_nonneg (P.lEta_pos hN hW hz hs).le _))
    _ = q ^ (3 / 2 * (((k : ℝ) - 1) / 2) + (3 / 2 + P.D / 2) * ((k : ℝ) / 2)) *
        (P.lEta s ^ (-(((k : ℝ) - 1) / 2)) * Real.sqrt (∏ i ∈ Finset.range k,
          P.ups s (isoPoint a b x i) (isoPoint a b x (i + 1)))) := by
        rw [Real.rpow_add hq0]
        ring
    _ ≤ q ^ (normExp k P.D - 3 / 2) *
        (P.lEta s ^ (-(((k : ℝ) - 1) / 2)) * Real.sqrt (∏ i ∈ Finset.range k,
          P.ups s (isoPoint a b x i) (isoPoint a b x (i + 1)))) :=
        mul_le_mul_of_nonneg_right (rpow_mono_exp hq (by unfold normExp; linarith))
          (mul_nonneg (Real.rpow_nonneg (P.lEta_pos hN hW hz hs).le _) (Real.sqrt_nonneg _))

theorem sAv_le_mul (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) (hD : 0 ≤ P.D)
    (hk : 1 ≤ k) {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) (x : Fin k → Fin N) :
    P.sAv x t ≤ (1 + |t - s| / P.z.im) ^ (normExp k P.D - 3 / 2) * P.sAv x s := by
  set q := 1 + |t - s| / P.z.im
  have hq := (PsiData.q_ge_one P) hz t s
  have hq0 : 0 < q := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold Psi.PsiData.sAv
  split_ifs with h1
  · have h := (PsiData.lEta_rpow_neg_le_mul P) hN hW hz ht hs (c := 1) zero_le_one
    rw [Real.rpow_neg_one, Real.rpow_neg_one] at h
    refine h.trans (mul_le_mul_of_nonneg_right (rpow_mono_exp hq ?_)
      (inv_nonneg.2 (P.lEta_pos hN hW hz hs).le))
    unfold normExp
    subst h1
    norm_num
    linarith
  · have e : -(k : ℝ) / 2 = -((k : ℝ) / 2) := by ring
    rw [e]
    have h1' := (PsiData.lEta_rpow_neg_le_mul P) hN hW hz ht hs (c := (k : ℝ) / 2) (by linarith)
    have h2 := sqrt_prod_le_mul (Finset.univ : Finset (Fin k))
      (fun j => P.ups t (x j) (x (finRotate k j))) (fun j => P.ups s (x j) (x (finRotate k j)))
      (Real.rpow_nonneg hq0.le _) (fun j _ => (P.ups_pos hN hW hz ht _ _).le)
      (fun j _ => (PsiData.ups_le_mul P) hN hW hz hD ht hs _ _)
    rw [Finset.card_univ, Fintype.card_fin, ← Real.rpow_mul hq0.le] at h2
    have hsq0 : 0 ≤ Real.sqrt (∏ j : Fin k, P.ups t (x j) (x (finRotate k j))) :=
      Real.sqrt_nonneg _
    calc P.lEta t ^ (-((k : ℝ) / 2)) * Real.sqrt (∏ j : Fin k, P.ups t (x j) (x (finRotate k j)))
        ≤ (q ^ (3 / 2 * ((k : ℝ) / 2)) * P.lEta s ^ (-((k : ℝ) / 2))) *
          (q ^ ((3 / 2 + P.D / 2) * ((k : ℝ) / 2)) *
            Real.sqrt (∏ j : Fin k, P.ups s (x j) (x (finRotate k j)))) :=
          mul_le_mul h1' h2 hsq0 (mul_nonneg (Real.rpow_nonneg hq0.le _)
            (Real.rpow_nonneg (P.lEta_pos hN hW hz hs).le _))
      _ = q ^ (3 / 2 * ((k : ℝ) / 2) + (3 / 2 + P.D / 2) * ((k : ℝ) / 2)) *
          (P.lEta s ^ (-((k : ℝ) / 2)) *
            Real.sqrt (∏ j : Fin k, P.ups s (x j) (x (finRotate k j)))) := by
          rw [Real.rpow_add hq0]
          ring
      _ ≤ q ^ (normExp k P.D - 3 / 2) * (P.lEta s ^ (-((k : ℝ) / 2)) *
            Real.sqrt (∏ j : Fin k, P.ups s (x j) (x (finRotate k j)))) :=
          mul_le_mul_of_nonneg_right (rpow_mono_exp hq (by unfold normExp; linarith))
            (mul_nonneg (Real.rpow_nonneg (P.lEta_pos hN hW hz hs).le _) (Real.sqrt_nonneg _))

/-- Two-time comparison of a normalization `(ℓη)^{α} s`, `0 ≤ α ≤ 1`. -/
theorem norm_le_mul (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im) {t s : ℝ} (ht : t ≤ 1)
    (hs : s ≤ 1) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {f g : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hfg : f ≤ (1 + |t - s| / P.z.im) ^ (normExp k P.D - 3 / 2) * g) :
    P.lEta t ^ α * f ≤ (1 + |t - s| / P.z.im) ^ normExp k P.D * (P.lEta s ^ α * g) := by
  set q := 1 + |t - s| / P.z.im
  have hq := (PsiData.q_ge_one P) hz t s
  have hq0 : 0 < q := by linarith
  have h1 := (PsiData.lEta_rpow_le_mul P) hN hW hz ht hs hα0
  have hL : 0 ≤ P.lEta s ^ α := Real.rpow_nonneg (P.lEta_pos hN hW hz hs).le _
  calc P.lEta t ^ α * f ≤ (q ^ (3 / 2 * α) * P.lEta s ^ α) *
        (q ^ (normExp k P.D - 3 / 2) * g) :=
        mul_le_mul h1 hfg hf (mul_nonneg (Real.rpow_nonneg hq0.le _) hL)
    _ = q ^ (3 / 2 * α + (normExp k P.D - 3 / 2)) * (P.lEta s ^ α * g) := by
        rw [Real.rpow_add hq0]
        ring
    _ ≤ q ^ normExp k P.D * (P.lEta s ^ α * g) :=
        mul_le_mul_of_nonneg_right (rpow_mono_exp hq (by linarith)) (mul_nonneg hL hg)

end PsiData

end BlockBand.Native.ErdosRiabov.Grid
