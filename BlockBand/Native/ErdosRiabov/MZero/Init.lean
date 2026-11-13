module

public import BlockBand.Native.ErdosRiabov.MZero.Chain
public import BlockBand.Native.ErdosRiabov.MBound.Joint

/-!
# Initial `M`-bounds at `t = 0` and the joint `M`-bounds

Deterministic; no measure. The initial bounds are unconditional.

Setting: `MBCtx d P` (`P.S = shortRingProfile d.b m W`, `m ≥ 4`, `W ≥ 1`, `P.W = W`,
`P.D = d.D`, `P.z ∈ 𝒟`), `t = 0`, `r = √(C₀+1)`, `ℓ_0η_0 = P.lEta 0`.

* `mzeroConst d k = r^{k-1} (1+4r)^{Dk/2}`, the constant of the initial bounds;
* `mzero_av_two_le`, `mzero_iso_two_le` (`k ≥ 2`) :
  `|Tr[M^{(0)}_{[1,k]}(x') S^{x_k}]| ≤ r^{k-1}(1+4r)^{Dk/2} ℓ_0η_0 s^av_{k,0}(x)` and
  `|(M^{(0)}_{[1,k]}(x'))_{aa}| ≤ r^{k-1}(1+4r)^{Dk/2} √(ℓ_0η_0) s^iso_{k,0}(a,x',a)`; `k = 1` is
  `MBound.mbBase_av1`, `mbBase_iso1` (constant `1 ≤ mzeroConst d 1`);
* `mzero_initAv`, `mzero_initIso`: exactly the hypotheses `hInitAv`, `hInitIso` of
  `MBound.mbBounds_joint`, for **every** `k`, with `B₀ = mzeroInitConst d P`, which is
  `mzeroConst d k` for `k ≥ 1` and `N/(ℓ_0η_0)` at the unused length `k = 0` (where
  `Tr[M^{(0)}_{[1,0]}] = N`, so no `P`-independent constant works);
* `mzero_mbConstA_congr`, `mzero_mbConstI_congr`: `mbConstA`, `mbConstI` do not read `B₀ 0`;
* `mzero_mchain_zero_bound`: both initial bounds for every `k ≥ 1` with `mzeroConst d k`;
* `mzero_mbAlg_of_mTermAlgebra`: `Split.MTermAlgebra → MBAlg`;
* **`mbBounds_joint_of_mzero`**: `MBound.mbBounds_joint` with the initial bounds discharged, with
  the constants `mbConstA d Λ (mzeroConst d) k`, `mbConstI d Λ (mzeroConst d) k`; conditional on
  `MBAlg` only (besides `MBCtx`); `mbBounds_joint_of_mzero_mTermAlgebra` takes
  `Split.MTermAlgebra` instead. `mzeroConst d` depends on `d` only, so the `N`-uniformity of
  `A_k`, `I_k` (through `Λ` only) comes from this constant.

Proof of the initial bounds: `M^{(0)}_{[1,k]} = ∏ m_j ∏_{j<k} S^{x_j}`, `|m_j| < 1`,
`0 ≤ S_{xa} ≤ 1/W`, and `S_{xa} ≠ 0` forces block distance `≤ 1`; so where the product is
nonzero all sites of the chain are at block distance `≤ 2` from each other, hence at cyclic
distance `< 3W ≤ 4W`, where `Υ_{η_0} ≥ (W r)⁻¹ (1+4r)^{-D}` (`Kernel.polynomialControl_lower`).
With `ℓ_0η_0 ≤ W r` and `1 - k/2 ≤ 0` this gives `(ℓ_0η_0)^{1-k/2} √(∏ Υ) ≥
(W r)^{1-k} (1+4r)^{-Dk/2}` (`mzero_arith`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MZero

open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.MBound BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)

/-! ## Constants -/

/-- The constant of the initial bounds: `B₀(k) = r^{k-1} (1+4r)^{Dk/2}`, `r = √(C₀+1)`. -/
def mzeroConst (d : VSData) (k : ℕ) : ℝ := d.r ^ (k - 1) * (1 + 4 * d.r) ^ (d.D * k / 2)

/-- The initial constants fed to `mbBounds_joint`: `mzeroConst d k` for `k ≥ 1`, and
`N/(ℓ_0η_0)` at the length `k = 0` (never used by the induction). -/
def mzeroInitConst (d : VSData) {N : ℕ} (P : PsiData N) (k : ℕ) : ℝ :=
  if k = 0 then (N : ℝ) * (P.lEta 0)⁻¹ else mzeroConst d k

/-- The floor `(W r)⁻¹ (1+4r)^{-D}` of `Υ_{η_0}` at block distance `≤ 2`. -/
def mzeroUpsFloor (d : VSData) (W : ℕ) : ℝ := ((W : ℝ) * d.r)⁻¹ * (1 + 4 * d.r) ^ (-d.D)

theorem mzero_one_le_r (d : VSData) : 1 ≤ d.r :=
  Real.one_le_sqrt.mpr (by linarith [d.C0_ge_one])

theorem mzero_r_pos (d : VSData) : 0 < d.r := lt_of_lt_of_le one_pos (mzero_one_le_r d)

theorem mzeroConst_nonneg (d : VSData) (k : ℕ) : 0 ≤ mzeroConst d k :=
  mul_nonneg (pow_nonneg (mzero_r_pos d).le _)
    (Real.rpow_nonneg (by linarith [mzero_r_pos d]) _)

theorem mzero_one_le_mzeroConst (d : VSData) (k : ℕ) : 1 ≤ mzeroConst d k := by
  unfold mzeroConst
  have h1 : 1 ≤ d.r ^ (k - 1) := one_le_pow₀ (mzero_one_le_r d)
  have h2 : 1 ≤ (1 + 4 * d.r) ^ (d.D * k / 2) :=
    Real.one_le_rpow (by linarith [mzero_r_pos d])
      (div_nonneg (mul_nonneg (by linarith [d.D_ge_six]) (Nat.cast_nonneg _)) zero_le_two)
  nlinarith

theorem mzeroInitConst_zero (d : VSData) {N : ℕ} (P : PsiData N) :
    mzeroInitConst d P 0 = (N : ℝ) * (P.lEta 0)⁻¹ := by
  unfold mzeroInitConst
  rw [ite_eq_left rfl]

theorem mzeroInitConst_of_ne (d : VSData) {N : ℕ} (P : PsiData N) {k : ℕ} (hk : k ≠ 0) :
    mzeroInitConst d P k = mzeroConst d k := by
  unfold mzeroInitConst
  rw [ite_eq_right hk]

theorem mzero_upsFloor_nonneg (d : VSData) (W : ℕ) : 0 ≤ mzeroUpsFloor d W :=
  mul_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (mzero_r_pos d).le))
    (Real.rpow_nonneg (by linarith [mzero_r_pos d]) _)

/-! ## The arithmetic core -/

/-- `(1/w)^{k-1} ≤ r^{k-1} q^{Dk/2} L^{1-k/2} √(((w r)⁻¹ q^{-D})^k)` for `0 < L ≤ w r`,
`k ≥ 2` (`w, r, q > 0`). -/
theorem mzero_arith {w r q D L : ℝ} (hw : 0 < w) (hr : 0 < r) (hq : 0 < q) (hL : 0 < L)
    (hLw : L ≤ w * r) {k : ℕ} (hk : 2 ≤ k) :
    (1 / w) ^ (k - 1) ≤ r ^ (k - 1) * q ^ (D * k / 2) *
      (L ^ ((1 : ℝ) - k / 2) * Real.sqrt (((w * r)⁻¹ * q ^ (-D)) ^ k)) := by
  have hX : 0 < w * r := mul_pos hw hr
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 < (w * r)⁻¹ * q ^ (-D) := mul_pos (inv_pos.mpr hX) (Real.rpow_pos_of_pos hq _)
  have hs : Real.sqrt (((w * r)⁻¹ * q ^ (-D)) ^ k) =
      (w * r) ^ (-((k : ℝ) / 2)) * q ^ (-(D * k / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le,
      Real.mul_rpow (inv_nonneg.mpr hX.le) (Real.rpow_nonneg hq.le _),
      Real.inv_rpow hX.le, ← Real.rpow_neg hX.le, ← Real.rpow_mul hq.le,
      show -((k : ℝ) * (1 / 2)) = -((k : ℝ) / 2) by ring,
      show -D * ((k : ℝ) * (1 / 2)) = -(D * k / 2) by ring]
  have hLX : (w * r) ^ ((1 : ℝ) - k / 2) ≤ L ^ ((1 : ℝ) - k / 2) :=
    Real.rpow_le_rpow_of_nonpos hL hLw (by linarith)
  have h1 : q ^ (D * k / 2) * q ^ (-(D * k / 2)) = 1 := by
    rw [← Real.rpow_add hq, add_neg_cancel, Real.rpow_zero]
  have h2 : (w * r) ^ ((1 : ℝ) - k / 2) * (w * r) ^ (-((k : ℝ) / 2)) =
      ((w * r) ^ (k - 1))⁻¹ := by
    rw [← Real.rpow_add hX, ← Real.rpow_natCast, ← Real.rpow_neg hX.le,
      Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    congr 1
    ring
  have hw0 : w ≠ 0 := hw.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have heq : r ^ (k - 1) * q ^ (D * k / 2) * ((w * r) ^ ((1 : ℝ) - k / 2) *
      ((w * r) ^ (-((k : ℝ) / 2)) * q ^ (-(D * k / 2)))) = (1 / w) ^ (k - 1) := by
    calc _ = r ^ (k - 1) * (q ^ (D * k / 2) * q ^ (-(D * k / 2))) *
          ((w * r) ^ ((1 : ℝ) - k / 2) * (w * r) ^ (-((k : ℝ) / 2))) := by ring
      _ = _ := by
        rw [h1, h2, mul_pow, one_div, inv_pow]
        field_simp
  have hcoef : 0 ≤ r ^ (k - 1) * q ^ (D * k / 2) :=
    mul_nonneg (pow_nonneg hr.le _) (Real.rpow_nonneg hq.le _)
  rw [hs]
  calc (1 / w) ^ (k - 1) = _ := heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLX
        (mul_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hq.le _))) hcoef

/-! ## Geometry of the support -/

theorem mzero_blockDistance_pair {m W : ℕ} {u v a : Fin (m * W)}
    (hu : blockDistance m W u a ≤ 1) (hv : blockDistance m W v a ≤ 1) :
    blockDistance m W u v ≤ 2 := by
  have h := blockDistance_triangle u a v
  rw [blockDistance_comm m W a v] at h
  omega

section Ctx

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)
include hc

theorem mzero_lEta_bounds : 0 < P.lEta 0 ∧ P.lEta 0 ≤ (W : ℝ) * d.r := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  obtain ⟨-, -, hL, hLW⟩ := P.height_bounds hN hc.hW
    (Nat.le_mul_of_pos_left W (by have := hc.hm; omega)) d.kappa_pos
    (by linarith [d.C0_ge_one]) hc.hz hc.hPW le_rfl zero_le_one
  exact ⟨hL, hLW⟩

/-- `Υ_{η_0}(u,v) ≥ (W r)⁻¹ (1+4r)^{-D}` at block distance `≤ 2`. -/
theorem mzero_ups_floor {u v : Fin (m * W)} (h : blockDistance m W u v ≤ 2) :
    mzeroUpsFloor d W ≤ P.ups 0 u v := by
  have hin := hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩
  have hH : (1 : ℝ) ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by have := hc.hm; omega)
  have hD : (0 : ℝ) ≤ d.D := by linarith [d.D_ge_six]
  have hlow := polynomialControl_lower hWN hc.hW hD hH hin.height_pos hin.height_le u v
  have hups : P.ups 0 u v = polynomialControl (m * W) W d.D (vsHeight P.z 0) u v := by
    unfold PsiData.ups
    rw [hc.hPW, hc.hPD]
  rw [hups]
  refine le_trans ?_ hlow
  unfold mzeroUpsFloor VSData.r
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hc.hW
  have hcd : cyclicDistance (m * W) u v + 1 ≤ 3 * W :=
    (cyclicDistance_add_one_le u v).trans (Nat.mul_le_mul_right _ (by omega))
  have hcd' : (cyclicDistance (m * W) u v : ℝ) + 1 ≤ 3 * W := by exact_mod_cast hcd
  have hs0 := Real.sqrt_nonneg (d.C0 + 1)
  have hbase : 1 + Real.sqrt (d.C0 + 1) * (cyclicDistance (m * W) u v : ℝ) / W ≤
      1 + 4 * Real.sqrt (d.C0 + 1) := by
    have : Real.sqrt (d.C0 + 1) * (cyclicDistance (m * W) u v : ℝ) / W ≤
        4 * Real.sqrt (d.C0 + 1) := by
      rw [div_le_iff₀ hW0]
      nlinarith
    linarith
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)

/-- `S_{x_j a} ≠ 0` forces block distance `≤ 1`. -/
theorem mzero_near_of_obs {k : ℕ} (x : Fin k → Fin (m * W)) (j : Fin k) (a : Fin (m * W))
    (h : obsSeq P.S x (j.val + 1) a ≠ 0) : blockDistance m W (x j) a ≤ 1 := by
  rw [obsSeq_succ P x j] at h
  simp only [Split.rowObs, ne_eq, Complex.ofReal_eq_zero] at h
  rw [hc.hPS] at h
  exact shortRingProfile_support h

theorem mzero_norm_obsSeq_le {k : ℕ} (x : Fin k → Fin (m * W)) (j : Fin k) (a : Fin (m * W)) :
    ‖obsSeq P.S x (j.val + 1) a‖ ≤ 1 / (W : ℝ) := by
  rw [obsSeq_succ P x j]
  simp only [Split.rowObs, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (hc.stoch.nonneg _ _), hc.hPS]
  exact Adapters.ErdosRiabov.shortRingProfile_le d.b_pos d.b_lt_half m W _ _

/-- `|(M^{(0)}_{[1,k]}(x'))_{aa}| ≤ W^{-(k-1)}`. -/
theorem mzero_norm_mChain_le {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin (m * W))
    (a : Fin (m * W)) : ‖P.mChain σ x 0 a‖ ≤ (1 / (W : ℝ)) ^ (k - 1) := by
  rw [mzero_mChain_zero, norm_mul]
  have h1 : ‖∏ i ∈ Finset.Icc 1 k, patM P.z σ i‖ ≤ 1 := by
    refine (Finset.norm_prod_le _ _).trans ?_
    have := Finset.prod_le_prod₀ (s := Finset.Icc 1 k) (fun _ _ => norm_nonneg _)
      fun i _ => (norm_patM_lt_one hc.zpos.ne' σ i).le
    rwa [Finset.prod_const, one_pow] at this
  have hle : ∀ p ∈ Finset.Ico 1 k, ‖obsSeq P.S x p a‖ ≤ 1 / (W : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Ico.mp hp
    obtain ⟨j, rfl⟩ : ∃ j : Fin k, p = j.val + 1 :=
      ⟨⟨p - 1, by omega⟩, (Nat.sub_add_cancel hp1).symm⟩
    exact mzero_norm_obsSeq_le hc x j a
  have h2 : ‖∏ p ∈ Finset.Ico 1 k, obsSeq P.S x p a‖ ≤ (1 / (W : ℝ)) ^ (k - 1) := by
    refine (Finset.norm_prod_le _ _).trans ?_
    have := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hle
    rwa [Finset.prod_const, Nat.card_Ico] at this
  calc _ ≤ 1 * (1 / (W : ℝ)) ^ (k - 1) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- Where `(M^{(0)}_{[1,k]}(x'))_{aa} ≠ 0`, every `x_j` (`j < k-1`) is block-adjacent to `a`. -/
theorem mzero_near_of_ne {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin (m * W))
    {a : Fin (m * W)} (h : P.mChain σ x 0 a ≠ 0) (j : Fin k) (hj : j.val + 1 < k) :
    blockDistance m W (x j) a ≤ 1 := by
  rw [mzero_mChain_zero] at h
  exact mzero_near_of_obs hc x j a (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    (j.val + 1) (Finset.mem_Ico.mpr ⟨by omega, hj⟩))

/-! ## The initial bounds for `k ≥ 2` -/

/-- **Initial bound, isotropic, `k ≥ 2`**:
`|(M^{(0)}_{[1,k]}(x'))_{aa}| ≤ r^{k-1}(1+4r)^{Dk/2} √(ℓ_0η_0) s^iso_{k,0}(a,x',a)`. -/
theorem mzero_iso_two_le {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin (m * W))
    (x : Fin k → Fin (m * W)) :
    ‖P.mChain σ x 0 a‖ ≤ mzeroConst d k * (Real.sqrt (P.lEta 0) * P.sIso a a x 0) := by
  obtain ⟨hL, hLW⟩ := mzero_lEta_bounds hc
  have hin := hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩
  have hR : 0 ≤ mzeroConst d k * (Real.sqrt (P.lEta 0) * P.sIso a a x 0) :=
    mul_nonneg (mzeroConst_nonneg d k)
      (mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P hin _ _ _))
  by_cases h0 : P.mChain σ x 0 a = 0
  · rw [h0, norm_zero]
    exact hR
  have hnear : ∀ i, blockDistance m W (isoPoint a a x i) a ≤ 1 := by
    intro i
    rcases i with _ | i
    · rw [contr_isoPoint_zero, blockDistance_self]
      omega
    · by_cases hi : i + 1 < k
      · rw [contr_isoPoint_succ a a x hi]
        exact mzero_near_of_ne hc σ x h0 ⟨i, by omega⟩ hi
      · rw [contr_isoPoint_of_le a a x (Nat.succ_ne_zero i) (by omega), blockDistance_self]
        omega
  have hprod : mzeroUpsFloor d W ^ k ≤
      ∏ i ∈ Finset.range k, P.ups 0 (isoPoint a a x i) (isoPoint a a x (i + 1)) := by
    have := Finset.prod_le_prod₀ (s := Finset.range k) (fun _ _ => mzero_upsFloor_nonneg d W)
      (fun i _ => mzero_ups_floor hc (mzero_blockDistance_pair (hnear i) (hnear (i + 1))))
    rwa [Finset.prod_const, Finset.card_range] at this
  have hsq : Real.sqrt (P.lEta 0) * P.lEta 0 ^ (-((k : ℝ) - 1) / 2) =
      P.lEta 0 ^ ((1 : ℝ) - k / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    congr 1
    ring
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hc.hW
  calc ‖P.mChain σ x 0 a‖ ≤ (1 / (W : ℝ)) ^ (k - 1) := mzero_norm_mChain_le hc σ x a
    _ ≤ mzeroConst d k * (P.lEta 0 ^ ((1 : ℝ) - k / 2) * Real.sqrt (mzeroUpsFloor d W ^ k)) := by
        unfold mzeroConst mzeroUpsFloor
        exact mzero_arith hW0 (mzero_r_pos d) (by linarith [mzero_r_pos d]) hL hLW hk
    _ ≤ _ := by
        unfold PsiData.sIso
        rw [← mul_assoc (Real.sqrt _), hsq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod)
          (Real.rpow_nonneg hL.le _)) (mzeroConst_nonneg d k)

/-- **Initial bound, averaged, `k ≥ 2`**:
`|Tr[M^{(0)}_{[1,k]}(x') S^{x_k}]| ≤ r^{k-1}(1+4r)^{Dk/2} ℓ_0η_0 s^av_{k,0}(x)`. -/
theorem mzero_av_two_le {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (x : Fin k → Fin (m * W)) :
    ‖avM P σ x 0‖ ≤ mzeroConst d k * (P.lEta 0 * P.sAv x 0) := by
  obtain ⟨hL, hLW⟩ := mzero_lEta_bounds hc
  have hR : 0 ≤ mzeroConst d k * (P.lEta 0 * P.sAv x 0) :=
    mul_nonneg (mzeroConst_nonneg d k) (mb_LsAv_pos_nonneg hc ⟨le_rfl, zero_le_one⟩ x)
  by_cases h0 : ∀ a, P.mChain σ x 0 a * obsSeq P.S x k a = 0
  · unfold avM
    rw [Finset.sum_eq_zero (fun a _ => h0 a), norm_zero]
    exact hR
  obtain ⟨a0, ha0⟩ := not_forall.mp h0
  have hm0 := left_ne_zero_of_mul ha0
  have hk0 := right_ne_zero_of_mul ha0
  have hnear : ∀ j : Fin k, blockDistance m W (x j) a0 ≤ 1 := by
    intro j
    by_cases hj : j.val + 1 < k
    · exact mzero_near_of_ne hc σ x hm0 j hj
    · have hjk : j.val + 1 = k := by omega
      apply mzero_near_of_obs hc x j a0
      rw [hjk]
      exact hk0
  have hrow : ∑ a, ‖obsSeq P.S x k a‖ = 1 := by
    rw [mb_obsSeq_apply _ _ (by omega) le_rfl]
    simp only [Split.rowObs, Complex.norm_real, Real.norm_eq_abs]
    exact (Finset.sum_congr rfl fun a _ => abs_of_nonneg (hc.stoch.nonneg _ _)).trans
      (hc.stoch.rowSum _)
  have hup : ‖avM P σ x 0‖ ≤ (1 / (W : ℝ)) ^ (k - 1) := by
    unfold avM
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖P.mChain σ x 0 a * obsSeq P.S x k a‖
        ≤ ∑ a, (1 / (W : ℝ)) ^ (k - 1) * ‖obsSeq P.S x k a‖ :=
          Finset.sum_le_sum fun a _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (mzero_norm_mChain_le hc σ x a) (norm_nonneg _)
      _ = _ := by rw [← Finset.mul_sum, hrow, mul_one]
  have hprod : mzeroUpsFloor d W ^ k ≤ ∏ j : Fin k, P.ups 0 (x j) (x (finRotate k j)) := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => mzero_upsFloor_nonneg d W)
      (fun j _ => mzero_ups_floor hc
        (mzero_blockDistance_pair (hnear j) (hnear (finRotate k j))))
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hsq : P.lEta 0 * P.lEta 0 ^ (-(k : ℝ) / 2) = P.lEta 0 ^ ((1 : ℝ) - k / 2) := by
    rw [mul_comm, ← Real.rpow_add_one hL.ne']
    congr 1
    ring
  have hsAv : P.sAv x 0 = P.lEta 0 ^ (-(k : ℝ) / 2) *
      Real.sqrt (∏ j : Fin k, P.ups 0 (x j) (x (finRotate k j))) := by
    unfold PsiData.sAv
    rw [ite_eq_right (by omega)]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hc.hW
  calc ‖avM P σ x 0‖ ≤ (1 / (W : ℝ)) ^ (k - 1) := hup
    _ ≤ mzeroConst d k * (P.lEta 0 ^ ((1 : ℝ) - k / 2) * Real.sqrt (mzeroUpsFloor d W ^ k)) := by
        unfold mzeroConst mzeroUpsFloor
        exact mzero_arith hW0 (mzero_r_pos d) (by linarith [mzero_r_pos d]) hL hLW hk
    _ ≤ _ := by
        rw [hsAv, ← mul_assoc (P.lEta 0), hsq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hprod)
          (Real.rpow_nonneg hL.le _)) (mzeroConst_nonneg d k)

/-! ## The initial hypotheses of `mbBounds_joint` -/

theorem mzeroInitConst_nonneg : ∀ k, 0 ≤ mzeroInitConst d P k := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [mzeroInitConst_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (mzero_lEta_bounds hc).1.le)
  · rw [mzeroInitConst_of_ne d P hk.ne']
    exact mzeroConst_nonneg d k

omit hc in
theorem mzero_mChain_len_zero (σ : Fin 0 → Bool) (x : Fin 0 → Fin (m * W)) (a : Fin (m * W)) :
    P.mChain σ x 0 a = 1 := by
  rw [mzero_mChain_zero, Finset.Icc_eq_empty_of_lt zero_lt_one,
    Finset.Ico_eq_empty_of_le zero_le_one, Finset.prod_empty, Finset.prod_empty, mul_one]

/-- **`hInitAv`**: the averaged initial hypothesis of `mbBounds_joint`, for every length,
with `B₀ = mzeroInitConst d P` (`= r^{k-1}(1+4r)^{Dk/2}` for `k ≥ 1`). -/
theorem mzero_initAv : ∀ (k : ℕ) (σ : Fin k → Bool) (y : Fin k → Fin (m * W)),
    ‖avM P σ y 0‖ ≤ mzeroInitConst d P k * (P.lEta 0 * P.sAv y 0) := by
  intro k σ y
  have hL := (mzero_lEta_bounds hc).1
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · have hobs : ∀ a, obsSeq P.S y 0 a = 1 := fun a => by
        unfold obsSeq
        rw [dite_eq_right (by omega)]
      have hsum : avM P σ y 0 = ∑ _a : Fin (m * W), (1 : ℂ) :=
        Finset.sum_congr rfl fun a _ => by rw [mzero_mChain_len_zero, hobs, mul_one]
      have hs : P.sAv y 0 = 1 := by
        unfold PsiData.sAv
        rw [ite_eq_right (by omega)]
        simp
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        Complex.norm_natCast, hs, mul_one, mzeroInitConst_zero, mul_assoc,
        inv_mul_cancel₀ hL.ne', mul_one]
    · rw [mzeroInitConst_of_ne d P one_ne_zero]
      exact (mbBase_av1 hc 0 ⟨le_rfl, zero_le_one⟩ σ y).trans
        (mul_le_mul_of_nonneg_right (mzero_one_le_mzeroConst d 1)
          (mb_LsAv_pos_nonneg hc ⟨le_rfl, zero_le_one⟩ y))
  · rw [mzeroInitConst_of_ne d P (by omega)]
    exact mzero_av_two_le hc hk σ y

/-- **`hInitIso`**: the isotropic initial hypothesis of `mbBounds_joint`, for every
length, with `B₀ = mzeroInitConst d P`. -/
theorem mzero_initIso : ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin (m * W))
    (y : Fin k → Fin (m * W)),
    ‖P.mChain σ y 0 a‖ ≤ mzeroInitConst d P k * (Real.sqrt (P.lEta 0) * P.sIso a a y 0) := by
  intro k σ a y
  have hL := (mzero_lEta_bounds hc).1
  have hin := hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · have hs : Real.sqrt (P.lEta 0) * P.sIso a a y 0 = P.lEta 0 := by
        unfold PsiData.sIso
        rw [Finset.range_zero, Finset.prod_empty, Real.sqrt_one, mul_one, Nat.cast_zero,
          show (-((0 : ℝ) - 1) / 2) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
          Real.mul_self_sqrt hL.le]
      have hN : (1 : ℝ) ≤ ((m * W : ℕ) : ℝ) :=
        Nat.one_le_cast.mpr (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
      rw [hs, mzeroInitConst_zero, mul_assoc, inv_mul_cancel₀ hL.ne', mul_one,
        mzero_mChain_len_zero, norm_one]
      exact hN
    · rw [mzeroInitConst_of_ne d P one_ne_zero]
      exact (mbBase_iso1 hc 0 ⟨le_rfl, zero_le_one⟩ σ a y).trans
        (mul_le_mul_of_nonneg_right (mzero_one_le_mzeroConst d 1)
          (mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P hin _ _ _)))
  · rw [mzeroInitConst_of_ne d P (by omega)]
    exact mzero_iso_two_le hc hk σ a y

/-- **The initial bounds**: at `t = 0`,
`|(M^{(0)}_{[1,k]}(x'))_{aa}| ≤ r^{k-1}(1+4r)^{Dk/2} √(ℓ_0η_0) s^iso_{k,0}(a,x',a)` and
`|Tr[M^{(0)}_{[1,k]}(x') S^{x_k}]| ≤ r^{k-1}(1+4r)^{Dk/2} ℓ_0η_0 s^av_{k,0}(x)`. -/
theorem mzero_mchain_zero_bound {k : ℕ} (hk : 1 ≤ k) (σ : Fin k → Bool) (a : Fin (m * W))
    (x : Fin k → Fin (m * W)) :
    ‖P.mChain σ x 0 a‖ ≤ mzeroConst d k * (Real.sqrt (P.lEta 0) * P.sIso a a x 0) ∧
      ‖avM P σ x 0‖ ≤ mzeroConst d k * (P.lEta 0 * P.sAv x 0) := by
  have h := mzeroInitConst_of_ne d P (show k ≠ 0 by omega)
  have hi := mzero_initIso hc k σ a x
  have ha := mzero_initAv hc k σ x
  rw [h] at hi ha
  exact ⟨hi, ha⟩

end Ctx

/-- The `M`-term algebra `Split.MTermAlgebra` gives `MBAlg`. -/
theorem mzero_mbAlg_of_mTermAlgebra (h : Split.MTermAlgebra) : MBAlg :=
  ⟨h.2.2.2.1, h.2.1, h.2.2.1⟩

/-! ## `mbConstA`, `mbConstI` do not read `B₀ 0` -/

section Congr

variable (d : VSData) (Λ : ℝ) {B₀ B₀' : ℕ → ℝ}

theorem mzero_mbStepA_congr (h : ∀ k, k ≠ 0 → B₀ k = B₀' k) (k : ℕ) (A I : ℕ → ℝ) :
    mbStepA d Λ B₀ k A I = mbStepA d Λ B₀' k A I := by
  unfold mbStepA
  by_cases hk : k ≤ 1
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [h k (by omega)]

theorem mzero_mbStepI_congr (h : ∀ k, k ≠ 0 → B₀ k = B₀' k) (k : ℕ) (Ak : ℝ) (I : ℕ → ℝ) :
    mbStepI d Λ B₀ k Ak I = mbStepI d Λ B₀' k Ak I := by
  unfold mbStepI
  by_cases hk : k ≤ 1
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [h k (by omega)]

theorem mzero_mbTab_congr (h : ∀ k, k ≠ 0 → B₀ k = B₀' k) :
    ∀ k, mbTab d Λ B₀ k = mbTab d Λ B₀' k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n
    have hA : mbTabA d Λ B₀ k = mbTabA d Λ B₀' k := by
      unfold mbTabA
      rw [ih]
    have hI : mbTabI d Λ B₀ k = mbTabI d Λ B₀' k := by
      unfold mbTabI
      rw [ih]
    rcases lt_trichotomy n k with hn | rfl | hn
    · rw [mbTab_succ_lt d Λ B₀ hn, mbTab_succ_lt d Λ B₀' hn, ih]
    · rw [mbTab_succ_self, mbTab_succ_self, hA, hI, mzero_mbStepA_congr d Λ h,
        mzero_mbStepI_congr d Λ h]
    · rw [mbTab_succ_gt d Λ B₀ hn, mbTab_succ_gt d Λ B₀' hn]

theorem mzero_mbConstA_congr (h : ∀ k, k ≠ 0 → B₀ k = B₀' k) (k : ℕ) :
    mbConstA d Λ B₀ k = mbConstA d Λ B₀' k := by
  unfold mbConstA
  rw [mzero_mbTab_congr d Λ h]

theorem mzero_mbConstI_congr (h : ∀ k, k ≠ 0 → B₀ k = B₀' k) (k : ℕ) :
    mbConstI d Λ B₀ k = mbConstI d Λ B₀' k := by
  unfold mbConstI
  rw [mzero_mbTab_congr d Λ h]

end Congr

/-! ## The joint `M`-bounds with the initial bounds discharged -/

/-- **The joint `M`-bounds with the initial bounds discharged**, under the hypothesis `MBAlg`
only (`Split.DerivStatement`, `CyclicStatement`, `WardStatement`; proved as
`Discharge.mbAlg_holds`). Under `MBCtx d P`, for every `k ≥ 1`, all `t ∈ [0,1]`, patterns and sites,
`|Tr[M^σ_t(x') S^{x_k}]| ≤ A_k ℓ_tη_t s^av_{k,t}(x)` and
`|(M^σ_t(x'))_{aa}| ≤ I_k √(ℓ_tη_t) s^iso_{k,t}(a,x',a)`, with
`A_k = mbConstA d Λ B₀ k`, `I_k = mbConstI d Λ B₀ k`, `Λ = c_m⁻¹ log((C₀+1)N)` and
`B₀ k = r^{k-1}(1+4r)^{Dk/2}` (`mzeroConst`). Uniformity: `mzeroConst d` depends on `d`
only (`C₀`, `D`), not on `N`, `W`, `P`; so `A_k`, `I_k` depend on `N` only through `Λ`. The
`P`-dependent value `N/(ℓ_0η_0)` of `mzeroInitConst d P 0`, used to discharge the `k = 0`
instance of `hInitAv`/`hInitIso`, is not read by `mbConstA`, `mbConstI`
(`mzero_mbConstA_congr`). -/
theorem mbBounds_joint_of_mzero {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg)
    (hc : MBCtx d P) :
    ∀ k, 1 ≤ k → MBAvB P k (mbConstA d (mbLambda d (m * W)) (mzeroConst d) k) ∧
      MBIsoB P k (mbConstI d (mbLambda d (m * W)) (mzeroConst d) k) := by
  intro k hk
  have he : ∀ k, k ≠ 0 → mzeroInitConst d P k = mzeroConst d k :=
    fun _ hk' => mzeroInitConst_of_ne d P hk'
  have h := mbBounds_joint hA hc (mzeroInitConst d P) (mzeroInitConst_nonneg hc)
    (mzero_initAv hc) (mzero_initIso hc) k hk
  rwa [mzero_mbConstA_congr d _ he, mzero_mbConstI_congr d _ he] at h

/-- `mbBounds_joint_of_mzero` from `Split.MTermAlgebra` (via
`mzero_mbAlg_of_mTermAlgebra`). -/
theorem mbBounds_joint_of_mzero_mTermAlgebra {d : VSData} {m W : ℕ} {P : PsiData (m * W)}
    (hT : Split.MTermAlgebra) (hc : MBCtx d P) :
    ∀ k, 1 ≤ k → MBAvB P k (mbConstA d (mbLambda d (m * W)) (mzeroConst d) k) ∧
      MBIsoB P k (mbConstI d (mbLambda d (m * W)) (mzeroConst d) k) :=
  mbBounds_joint_of_mzero (mzero_mbAlg_of_mTermAlgebra hT) hc

end BlockBand.Native.ErdosRiabov.MZero
