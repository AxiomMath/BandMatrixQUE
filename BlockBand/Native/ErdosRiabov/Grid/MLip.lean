module

public import BlockBand.Native.ErdosRiabov.Psi.Cont

set_option autoImplicit false

/-!
# Bounds and Lipschitz continuity of the M-terms in the profile scale

Setting: a stochastic symmetric profile `S` on `Fin n` (`Kernel.StochasticSymm`), spectral data
`m : ℕ → ℂ` with `‖m i‖ ≤ 1` and `‖m i m j‖ ≤ r < 1`, observables with `‖A p‖ ≤ 1` (sup norm on
`Fin n → ℂ`), `ρ = (1 - r)⁻¹`. For `σ ∈ [0,1]`:

* `norm_profile_mulVec_le`: `‖S v‖ ≤ ‖v‖`;
* `norm_inv_mulVec_le`: `‖(1 - c S)⁻¹ v‖ ≤ (1 - ‖c‖)⁻¹ ‖v‖` for `‖c‖ < 1`;
* `norm_inv_sub_inv_mulVec_le`: `‖((1 - c S)⁻¹ - (1 - c' S)⁻¹) v‖ ≤ ρ² ‖c - c'‖ ‖v‖` for
  `‖c‖, ‖c'‖ ≤ r`;
* **`chainTilde_bounds`**: for `B ≥ 2`, `B ≥ L ρ` and `l - j ≤ L`:
  `‖M̃_{[j,l]}(σ)‖ ≤ B^{2(l-j)-1}` and `‖M̃_{[j,l]}(σ) - M̃_{[j,l]}(σ')‖ ≤ B^{4(l-j)} |σ - σ'|`;
* **`chainM_lipschitz`**, `chainM_bound`: the same for `M_{[j,l]} = (∏ m_i) M̃_{[j,l]}`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open Matrix Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ}

/-!
### The profile and the stability operator on the sup norm
-/

theorem norm_profile_mulVec_le (hS : StochasticSymm S) (v : Fin n → ℂ) :
    ‖Split.profileC S *ᵥ v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun a => ?_
  simp only [Matrix.mulVec, dotProduct, Split.profileC, Matrix.map_apply]
  calc ‖∑ b, (S a b : ℂ) * v b‖ ≤ ∑ b, ‖(S a b : ℂ) * v b‖ := norm_sum_le _ _
    _ ≤ ∑ b, S a b * ‖v‖ := Finset.sum_le_sum fun b _ => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hS.nonneg a b)]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v b) (hS.nonneg a b)
    _ = ‖v‖ := by rw [← Finset.sum_mul, hS.rowSum a, one_mul]

theorem norm_coef_le {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) (a : ℂ) : ‖(σ : ℂ) * a‖ ≤ ‖a‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hσ.2

theorem stabOp_right_inv (hS : StochasticSymm S) {c : ℂ} (hc : ‖c‖ < 1) :
    (1 - c • Split.profileC S) * (1 - c • Split.profileC S)⁻¹ = 1 := by
  rw [profileC_eq_cMat]
  exact one_sub_smul_mul_inv hS hc

theorem stabOp_left_inv (hS : StochasticSymm S) {c : ℂ} (hc : ‖c‖ < 1) :
    (1 - c • Split.profileC S)⁻¹ * (1 - c • Split.profileC S) = 1 := by
  rw [profileC_eq_cMat]
  exact inv_mul_one_sub_smul hS hc

/-- `‖(1 - c S)⁻¹ v‖ ≤ ‖v‖/(1 - ‖c‖)`. -/
theorem norm_inv_mulVec_le (hS : StochasticSymm S) {c : ℂ} (hc : ‖c‖ < 1) (v : Fin n → ℂ) :
    ‖(1 - c • Split.profileC S)⁻¹ *ᵥ v‖ ≤ (1 - ‖c‖)⁻¹ * ‖v‖ := by
  set w := (1 - c • Split.profileC S)⁻¹ *ᵥ v with hw
  have hv : w - c • (Split.profileC S *ᵥ w) = v := by
    have h := congrArg (fun M => M *ᵥ v) (stabOp_right_inv hS hc)
    simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.smul_mulVec] at h
    exact h
  have h1 : ‖w‖ ≤ ‖v‖ + ‖c‖ * ‖w‖ := by
    have : w = v + c • (Split.profileC S *ᵥ w) := by rw [← hv]; abel
    calc ‖w‖ = ‖v + c • (Split.profileC S *ᵥ w)‖ := by rw [← this]
      _ ≤ ‖v‖ + ‖c‖ * ‖Split.profileC S *ᵥ w‖ := (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ ‖v‖ + ‖c‖ * ‖w‖ := by
          gcongr
          exact norm_profile_mulVec_le hS w
  have hpos : 0 < 1 - ‖c‖ := by linarith
  rw [le_inv_mul_iff₀ hpos]
  linarith

/-- The resolvent identity for the stability operator, applied to a vector. -/
theorem inv_sub_inv_mulVec (hS : StochasticSymm S) {c c' : ℂ} (hc : ‖c‖ < 1) (hc' : ‖c'‖ < 1)
    (v : Fin n → ℂ) :
    (1 - c • Split.profileC S)⁻¹ *ᵥ v - (1 - c' • Split.profileC S)⁻¹ *ᵥ v =
      (1 - c • Split.profileC S)⁻¹ *ᵥ ((c - c') •
        (Split.profileC S *ᵥ ((1 - c' • Split.profileC S)⁻¹ *ᵥ v))) := by
  set P := (1 - c • Split.profileC S)⁻¹
  set P' := (1 - c' • Split.profileC S)⁻¹
  have hL : P * (1 - c • Split.profileC S) = 1 := stabOp_left_inv hS hc
  have hR : (1 - c' • Split.profileC S) * P' = 1 := stabOp_right_inv hS hc'
  have hM : P - P' = P * ((c - c') • Split.profileC S) * P' := by
    calc P - P' = P * ((1 - c' • Split.profileC S) * P') - (P * (1 - c • Split.profileC S)) * P' :=
          by rw [hR, hL, Matrix.mul_one, Matrix.one_mul]
      _ = P * ((c - c') • Split.profileC S) * P' := by
          rw [sub_smul, Matrix.mul_assoc]
          noncomm_ring
  rw [← Matrix.sub_mulVec, hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]

theorem norm_inv_sub_inv_mulVec_le (hS : StochasticSymm S) {c c' : ℂ} {r : ℝ} (hr : r < 1)
    (hc : ‖c‖ ≤ r) (hc' : ‖c'‖ ≤ r) (v : Fin n → ℂ) :
    ‖(1 - c • Split.profileC S)⁻¹ *ᵥ v - (1 - c' • Split.profileC S)⁻¹ *ᵥ v‖ ≤
      (1 - r)⁻¹ * ((1 - r)⁻¹ * (‖c - c'‖ * ‖v‖)) := by
  have hc1 : ‖c‖ < 1 := hc.trans_lt hr
  have hc1' : ‖c'‖ < 1 := hc'.trans_lt hr
  have hpos : 0 < 1 - r := by linarith
  have hmono : ∀ {c₀ : ℂ}, ‖c₀‖ ≤ r → (1 - ‖c₀‖)⁻¹ ≤ (1 - r)⁻¹ := fun h =>
    inv_anti₀ hpos (by linarith)
  rw [inv_sub_inv_mulVec hS hc1 hc1' v]
  refine (norm_inv_mulVec_le hS hc1 _).trans ?_
  have h2 := norm_inv_mulVec_le hS hc1' v
  have h3 := norm_profile_mulVec_le hS ((1 - c' • Split.profileC S)⁻¹ *ᵥ v)
  rw [norm_smul]
  have hv0 := norm_nonneg v
  have h4 : ‖Split.profileC S *ᵥ ((1 - c' • Split.profileC S)⁻¹ *ᵥ v)‖ ≤ (1 - r)⁻¹ * ‖v‖ :=
    h3.trans (h2.trans (mul_le_mul_of_nonneg_right (hmono hc') hv0))
  calc (1 - ‖c‖)⁻¹ * (‖c - c'‖ * ‖Split.profileC S *ᵥ ((1 - c' • Split.profileC S)⁻¹ *ᵥ v)‖)
      ≤ (1 - r)⁻¹ * (‖c - c'‖ * ((1 - r)⁻¹ * ‖v‖)) :=
        mul_le_mul (hmono hc) (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
          (by positivity) (by positivity)
    _ = (1 - r)⁻¹ * ((1 - r)⁻¹ * (‖c - c'‖ * ‖v‖)) := by ring

/-!
### The induction on the chain length
-/

/-- Hypotheses on the data of the M-recursion. -/
structure MHyp (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ) (r : ℝ) :
    Prop where
  stoch : StochasticSymm S
  r_lt : r < 1
  m_le : ∀ i, ‖m i‖ ≤ 1
  mm_le : ∀ i j, ‖m i * m j‖ ≤ r
  A_le : ∀ p, ‖A p‖ ≤ 1

theorem norm_one_vec_le : ‖(fun _ => (1 : ℂ) : Fin n → ℂ)‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp

theorem pow_two_mul_sub_one_le {B : ℝ} (hB : 1 ≤ B) {a b : ℕ} (h : a ≤ b) :
    B ^ (2 * a - 1) ≤ B ^ (2 * b - 1) := pow_le_pow_right₀ hB (by omega)

/-- **M-recursion bounds** (strong induction on `l - j`): under `MHyp`, for `B ≥ 2`,
`B ≥ L (1 - r)⁻¹` and `l - j ≤ L`, for `σ, σ' ∈ [0,1]`:
`‖M̃_{[j,l]}(σ)‖ ≤ B^{2(l-j)-1}` and `‖M̃_{[j,l]}(σ) - M̃_{[j,l]}(σ')‖ ≤ B^{4(l-j)} |σ - σ'|`. -/
theorem chainTilde_bounds {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ} {r : ℝ} (h : MHyp S m A r) {L : ℕ}
    {B : ℝ} (hB2 : 2 ≤ B) (hBL : (L : ℝ) * (1 - r)⁻¹ ≤ B) :
    ∀ d, d ≤ L → ∀ j l, l - j = d → ∀ σ ∈ Icc (0 : ℝ) 1, ∀ σ' ∈ Icc (0 : ℝ) 1,
      ‖Split.chainTilde σ S m A j l‖ ≤ B ^ (2 * d - 1) ∧
      ‖Split.chainTilde σ S m A j l - Split.chainTilde σ' S m A j l‖ ≤
        B ^ (4 * d) * |σ - σ'| := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hdL j l hd σ hσ σ' hσ'
  have hS := h.stoch
  have hr1 := h.r_lt
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (h.mm_le 0 0)
  have hρ1 : 1 ≤ (1 - r)⁻¹ := (one_le_inv₀ (by linarith)).2 (by linarith)
  rw [Split.chainTilde_eq σ S m A j l, Split.chainTilde_eq σ' S m A j l]
  by_cases hjl : j < l
  swap
  · simp only [hjl, ite_false]
    refine ⟨norm_one_vec_le.trans (one_le_pow₀ hB1), ?_⟩
    simp only [sub_self, norm_zero]
    positivity
  simp only [hjl, ite_true]
  have hd1 : 1 ≤ d := by omega
  have hdR : (d : ℝ) ≤ L := by exact_mod_cast hdL
  have hρd : (d : ℝ) * (1 - r)⁻¹ ≤ B :=
    le_trans (mul_le_mul_of_nonneg_right hdR (by positivity)) hBL
  have hρB : (1 - r)⁻¹ ≤ B :=
    le_trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast hd1)) hρd
  -- notations
  set M : ℝ → ℕ → ℕ → Fin n → ℂ := fun s a b => Split.chainTilde s S m A a b with hMdef
  set v : ℝ → Fin n → ℂ := fun s => A j * M s (j + 1) l +
    ∑ i ∈ Finset.Ioo j l, ((s : ℂ) * m j * m i) •
      (Split.selfEnergy S (M s j i) * M s i l) with hv
  -- bounds on the pieces
  have hIH : ∀ a b, b - a < d → ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1,
      ‖M s a b‖ ≤ B ^ (2 * (b - a) - 1) ∧
        ‖M s a b - M s' a b‖ ≤ B ^ (4 * (b - a)) * |s - s'| := fun a b hab s hs s' hs' =>
    ih (b - a) hab (by omega) a b rfl s hs s' hs'
  have hcoef : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖(s : ℂ) * m j * m i‖ ≤ r := fun s hs i => by
    rw [mul_assoc]
    exact (norm_coef_le hs _).trans (h.mm_le j i)
  have hcoef1 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖(s : ℂ) * m j * m i‖ ≤ 1 := fun s hs i =>
    (hcoef s hs i).trans hr1.le
  have hterm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i ∈ Finset.Ioo j l,
      ‖((s : ℂ) * m j * m i) • (Split.selfEnergy S (M s j i) * M s i l)‖ ≤ B ^ (2 * d - 2) := by
    intro s hs i hi
    have hi' := Finset.mem_Ioo.mp hi
    rw [norm_smul]
    have h1 := (hIH j i (by omega) s hs s hs).1
    have h2 := (hIH i l (by omega) s hs s hs).1
    have hse := norm_profile_mulVec_le hS (M s j i)
    calc ‖(s : ℂ) * m j * m i‖ * ‖Split.selfEnergy S (M s j i) * M s i l‖
        ≤ 1 * (‖M s j i‖ * ‖M s i l‖) := by
          gcongr
          · exact hcoef1 s hs i
          · exact (norm_mul_le _ _).trans (by gcongr; exact hse)
      _ ≤ 1 * (B ^ (2 * (i - j) - 1) * B ^ (2 * (l - i) - 1)) := by gcongr
      _ = B ^ (2 * d - 2) := by
          rw [one_mul, ← pow_add]
          congr 1
          omega
  have hvle : ∀ s ∈ Icc (0 : ℝ) 1, ‖v s‖ ≤ d * B ^ (2 * d - 2) := by
    intro s hs
    have h1 := (hIH (j + 1) l (by omega) s hs s hs).1
    have hA := h.A_le j
    have hfirst : ‖A j * M s (j + 1) l‖ ≤ B ^ (2 * d - 2) :=
      (norm_mul_le _ _).trans (by
        calc ‖A j‖ * ‖M s (j + 1) l‖ ≤ 1 * B ^ (2 * (l - (j + 1)) - 1) := by gcongr
          _ ≤ B ^ (2 * d - 2) := by rw [one_mul]; exact pow_le_pow_right₀ hB1 (by omega))
    have hsum : ‖∑ i ∈ Finset.Ioo j l, ((s : ℂ) * m j * m i) •
        (Split.selfEnergy S (M s j i) * M s i l)‖ ≤ (d - 1 : ℕ) * B ^ (2 * d - 2) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum (hterm s hs)).trans ?_
      rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul, hd]
    calc ‖v s‖ ≤ B ^ (2 * d - 2) + (d - 1 : ℕ) * B ^ (2 * d - 2) :=
          (norm_add_le _ _).trans (add_le_add hfirst hsum)
      _ = d * B ^ (2 * d - 2) := by
          rw [Nat.cast_sub hd1]
          push_cast
          ring
  have hstab : ∀ s ∈ Icc (0 : ℝ) 1, ‖((s : ℂ) * (m j * m l))‖ ≤ r := fun s hs =>
    (norm_coef_le hs _).trans (h.mm_le j l)
  refine ⟨?_, ?_⟩
  · -- the sup bound
    have hs := hstab σ hσ
    have h1 := norm_inv_mulVec_le hS (hs.trans_lt hr1) (v σ)
    have hmono : (1 - ‖(σ : ℂ) * (m j * m l)‖)⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ (by linarith)
      (by linarith)
    change ‖Split.stabOp σ S (m j * m l) *ᵥ v σ‖ ≤ _
    unfold Split.stabOp
    calc _ ≤ (1 - ‖(σ : ℂ) * (m j * m l)‖)⁻¹ * ‖v σ‖ := h1
      _ ≤ (1 - r)⁻¹ * (d * B ^ (2 * d - 2)) := by
          gcongr
          exact hvle σ hσ
      _ = ((d : ℝ) * (1 - r)⁻¹) * B ^ (2 * d - 2) := by ring
      _ ≤ B * B ^ (2 * d - 2) := by gcongr
      _ = B ^ (2 * d - 1) := by
          rw [← pow_succ']
          congr 1
          omega
  · -- the Lipschitz bound
    have hs := hstab σ hσ
    have hs' := hstab σ' hσ'
    set St : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s => Split.stabOp s S (m j * m l) with hSt
    have hsplit : St σ *ᵥ v σ - St σ' *ᵥ v σ' =
        (St σ *ᵥ v σ - St σ' *ᵥ v σ) + St σ' *ᵥ (v σ - v σ') := by
      rw [Matrix.mulVec_sub]
      abel
    have hdiffSt : ‖St σ *ᵥ v σ - St σ' *ᵥ v σ‖ ≤
        (1 - r)⁻¹ * ((1 - r)⁻¹ * (|σ - σ'| * (d * B ^ (2 * d - 2)))) := by
      have h0 := norm_inv_sub_inv_mulVec_le hS hr1 hs hs' (v σ)
      refine h0.trans ?_
      have hcc : ‖(σ : ℂ) * (m j * m l) - (σ' : ℂ) * (m j * m l)‖ ≤ |σ - σ'| := by
        rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) ((h.mm_le j l).trans hr1.le)
      gcongr
      exact hvle σ hσ
    -- the difference of the vectors
    have hdv : ‖v σ - v σ'‖ ≤ 3 * d * B ^ (4 * d - 3) * |σ - σ'| := by
      have h1 := hIH (j + 1) l (by omega) σ hσ σ' hσ'
      have hfirst : ‖A j * M σ (j + 1) l - A j * M σ' (j + 1) l‖ ≤
          B ^ (4 * d - 3) * |σ - σ'| := by
        rw [← mul_sub]
        refine (norm_mul_le _ _).trans ?_
        calc ‖A j‖ * ‖M σ (j + 1) l - M σ' (j + 1) l‖
            ≤ 1 * (B ^ (4 * (l - (j + 1))) * |σ - σ'|) := by
              gcongr
              · exact h.A_le j
              · exact h1.2
          _ ≤ B ^ (4 * d - 3) * |σ - σ'| := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega))
                (abs_nonneg _)
      have hterm' : ∀ i ∈ Finset.Ioo j l,
          ‖((σ : ℂ) * m j * m i) • (Split.selfEnergy S (M σ j i) * M σ i l) -
            ((σ' : ℂ) * m j * m i) • (Split.selfEnergy S (M σ' j i) * M σ' i l)‖ ≤
            3 * B ^ (4 * d - 3) * |σ - σ'| := by
        intro i hi
        have hi' := Finset.mem_Ioo.mp hi
        obtain ⟨a1, a2⟩ := hIH j i (by omega) σ hσ σ' hσ'
        obtain ⟨b1, b2⟩ := hIH i l (by omega) σ hσ σ' hσ'
        have a1' := (hIH j i (by omega) σ' hσ' σ' hσ').1
        have b1' := (hIH i l (by omega) σ' hσ' σ' hσ').1
        set x := Split.selfEnergy S (M σ j i) * M σ i l
        set x' := Split.selfEnergy S (M σ' j i) * M σ' i l
        have hcd : ‖(σ : ℂ) * m j * m i - (σ' : ℂ) * m j * m i‖ ≤ |σ - σ'| := by
          rw [mul_assoc, mul_assoc, ← sub_mul, norm_mul, ← Complex.ofReal_sub,
            Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg _) ((h.mm_le j i).trans hr1.le)
        have hx : ‖x‖ ≤ B ^ (2 * d - 2) := by
          have := hterm σ hσ i hi
          refine (norm_mul_le _ _).trans ?_
          calc ‖Split.selfEnergy S (M σ j i)‖ * ‖M σ i l‖ ≤ ‖M σ j i‖ * ‖M σ i l‖ := by
                gcongr
                exact norm_profile_mulVec_le hS _
            _ ≤ B ^ (2 * (i - j) - 1) * B ^ (2 * (l - i) - 1) := by gcongr
            _ = B ^ (2 * d - 2) := by
                rw [← pow_add]
                congr 1
                omega
        have hxx : ‖x - x'‖ ≤ 2 * B ^ (4 * d - 3) * |σ - σ'| := by
          have e : x - x' = Split.selfEnergy S (M σ j i - M σ' j i) * M σ i l +
              Split.selfEnergy S (M σ' j i) * (M σ i l - M σ' i l) := by
            simp only [x, x', Split.selfEnergy, Matrix.mulVec_sub, sub_mul, mul_sub]
            abel
          rw [e]
          have hp1 : ‖Split.selfEnergy S (M σ j i - M σ' j i) * M σ i l‖ ≤
              B ^ (4 * d - 3) * |σ - σ'| := by
            refine (norm_mul_le _ _).trans ?_
            calc ‖Split.selfEnergy S (M σ j i - M σ' j i)‖ * ‖M σ i l‖
                ≤ (B ^ (4 * (i - j)) * |σ - σ'|) * B ^ (2 * (l - i) - 1) := by
                  gcongr
                  exact (norm_profile_mulVec_le hS _).trans a2
              _ = B ^ (4 * (i - j) + (2 * (l - i) - 1)) * |σ - σ'| := by rw [pow_add]; ring
              _ ≤ B ^ (4 * d - 3) * |σ - σ'| :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (abs_nonneg _)
          have hp2 : ‖Split.selfEnergy S (M σ' j i) * (M σ i l - M σ' i l)‖ ≤
              B ^ (4 * d - 3) * |σ - σ'| := by
            refine (norm_mul_le _ _).trans ?_
            calc ‖Split.selfEnergy S (M σ' j i)‖ * ‖M σ i l - M σ' i l‖
                ≤ B ^ (2 * (i - j) - 1) * (B ^ (4 * (l - i)) * |σ - σ'|) := by
                  gcongr
                  exact (norm_profile_mulVec_le hS _).trans a1'
              _ = B ^ ((2 * (i - j) - 1) + 4 * (l - i)) * |σ - σ'| := by rw [pow_add]; ring
              _ ≤ B ^ (4 * d - 3) * |σ - σ'| :=
                  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB1 (by omega)) (abs_nonneg _)
          calc _ ≤ _ := norm_add_le _ _
            _ ≤ B ^ (4 * d - 3) * |σ - σ'| + B ^ (4 * d - 3) * |σ - σ'| := add_le_add hp1 hp2
            _ = 2 * B ^ (4 * d - 3) * |σ - σ'| := by ring
        have e2 : ((σ : ℂ) * m j * m i) • x - ((σ' : ℂ) * m j * m i) • x' =
            ((σ : ℂ) * m j * m i - (σ' : ℂ) * m j * m i) • x +
              ((σ' : ℂ) * m j * m i) • (x - x') := by
          rw [sub_smul, smul_sub]
          abel
        rw [e2]
        have hsq : B ^ (2 * d - 2) ≤ B ^ (4 * d - 3) := pow_le_pow_right₀ hB1 (by omega)
        calc _ ≤ _ := norm_add_le _ _
          _ ≤ |σ - σ'| * B ^ (2 * d - 2) + 1 * (2 * B ^ (4 * d - 3) * |σ - σ'|) := by
              rw [norm_smul, norm_smul]
              gcongr
              exact hcoef1 σ' hσ' i
          _ ≤ 3 * B ^ (4 * d - 3) * |σ - σ'| := by
              have := abs_nonneg (σ - σ')
              nlinarith
      have hsum : ‖(∑ i ∈ Finset.Ioo j l, ((σ : ℂ) * m j * m i) •
            (Split.selfEnergy S (M σ j i) * M σ i l)) -
          ∑ i ∈ Finset.Ioo j l, ((σ' : ℂ) * m j * m i) •
            (Split.selfEnergy S (M σ' j i) * M σ' i l)‖ ≤
          (d - 1 : ℕ) * (3 * B ^ (4 * d - 3) * |σ - σ'|) := by
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum hterm').trans ?_
        rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul, hd]
      have e : v σ - v σ' = (A j * M σ (j + 1) l - A j * M σ' (j + 1) l) +
          ((∑ i ∈ Finset.Ioo j l, ((σ : ℂ) * m j * m i) •
            (Split.selfEnergy S (M σ j i) * M σ i l)) -
          ∑ i ∈ Finset.Ioo j l, ((σ' : ℂ) * m j * m i) •
            (Split.selfEnergy S (M σ' j i) * M σ' i l)) := by
        simp only [hv]
        abel
      rw [e]
      have hab := abs_nonneg (σ - σ')
      have hBp : 0 ≤ B ^ (4 * d - 3) := by positivity
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ B ^ (4 * d - 3) * |σ - σ'| + (d - 1 : ℕ) * (3 * B ^ (4 * d - 3) * |σ - σ'|) :=
            add_le_add hfirst hsum
        _ ≤ 3 * d * B ^ (4 * d - 3) * |σ - σ'| := by
            rw [Nat.cast_sub hd1]
            push_cast
            have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
            nlinarith [mul_nonneg hBp hab]
    change ‖St σ *ᵥ v σ - St σ' *ᵥ v σ'‖ ≤ _
    rw [hsplit]
    have hs1 : ‖St σ' *ᵥ (v σ - v σ')‖ ≤ (1 - r)⁻¹ * (3 * d * B ^ (4 * d - 3) * |σ - σ'|) := by
      have h1 := norm_inv_mulVec_le hS (hs'.trans_lt hr1) (v σ - v σ')
      have hmono : (1 - ‖(σ' : ℂ) * (m j * m l)‖)⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ (by linarith)
        (by linarith)
      calc _ ≤ (1 - ‖(σ' : ℂ) * (m j * m l)‖)⁻¹ * ‖v σ - v σ'‖ := h1
        _ ≤ _ := by gcongr
    have hab := abs_nonneg (σ - σ')
    set ρ := (1 - r)⁻¹ with hρ
    have hρ0 : 0 ≤ ρ := by positivity
    have hP1 : B ^ (2 * d - 2) * B ^ 2 = B ^ (2 * d) := by rw [← pow_add]; congr 1; omega
    have hP2 : B ^ (4 * d - 3) * B = B ^ (4 * d - 2) := by rw [← pow_succ]; congr 1; omega
    have hP3 : B ^ (4 * d - 2) * B ^ 2 = B ^ (4 * d) := by rw [← pow_add]; congr 1; omega
    have hP4 : B ^ (2 * d) ≤ B ^ (4 * d - 2) := pow_le_pow_right₀ hB1 (by omega)
    have hb1 : ρ * (ρ * (|σ - σ'| * (d * B ^ (2 * d - 2)))) ≤ B ^ (2 * d) * |σ - σ'| := by
      calc ρ * (ρ * (|σ - σ'| * (d * B ^ (2 * d - 2))))
          = ρ * ((d * ρ) * B ^ (2 * d - 2)) * |σ - σ'| := by ring
        _ ≤ B * (B * B ^ (2 * d - 2)) * |σ - σ'| := by gcongr
        _ = B ^ (2 * d) * |σ - σ'| := by rw [← hP1]; ring
    have hb2 : ρ * (3 * d * B ^ (4 * d - 3) * |σ - σ'|) ≤ 3 * B ^ (4 * d - 2) * |σ - σ'| := by
      calc ρ * (3 * d * B ^ (4 * d - 3) * |σ - σ'|)
          = 3 * ((d * ρ) * B ^ (4 * d - 3)) * |σ - σ'| := by ring
        _ ≤ 3 * (B * B ^ (4 * d - 3)) * |σ - σ'| := by gcongr
        _ = 3 * B ^ (4 * d - 2) * |σ - σ'| := by rw [← hP2]; ring
    have hB4 : 4 ≤ B ^ 2 := by nlinarith
    have hBp : 0 ≤ B ^ (4 * d - 2) := by positivity
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ B ^ (2 * d) * |σ - σ'| + 3 * B ^ (4 * d - 2) * |σ - σ'| :=
          add_le_add (hdiffSt.trans hb1) (hs1.trans hb2)
      _ ≤ 4 * B ^ (4 * d - 2) * |σ - σ'| := by nlinarith [mul_nonneg hBp hab]
      _ ≤ B ^ (4 * d) * |σ - σ'| := by
          rw [← hP3]
          nlinarith [mul_nonneg hBp hab]

/-- `|∏_{i ∈ s} m i| ≤ 1`. -/
theorem norm_prod_le_one {m : ℕ → ℂ} (hm : ∀ i, ‖m i‖ ≤ 1) (s : Finset ℕ) :
    ‖∏ i ∈ s, m i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => hm i

/-- **Lipschitz continuity of the M-terms** in the profile scale. -/
theorem chainM_lipschitz {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ} {r : ℝ} (h : MHyp S m A r) {B : ℝ}
    (hB2 : 2 ≤ B) {j l : ℕ} (hBL : ((l - j : ℕ) : ℝ) * (1 - r)⁻¹ ≤ B) {σ σ' : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hσ' : σ' ∈ Icc (0 : ℝ) 1) :
    ‖Split.chainM σ S m A j l - Split.chainM σ' S m A j l‖ ≤ B ^ (4 * (l - j)) * |σ - σ'| := by
  have h0 := (chainTilde_bounds h hB2 hBL (l - j) le_rfl j l rfl σ hσ σ' hσ').2
  unfold Split.chainM
  rw [← smul_sub, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_prod_le_one h.m_le _)).trans h0

theorem chainM_bound {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ} {r : ℝ} (h : MHyp S m A r) {B : ℝ}
    (hB2 : 2 ≤ B) {j l : ℕ} (hBL : ((l - j : ℕ) : ℝ) * (1 - r)⁻¹ ≤ B) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) :
    ‖Split.chainM σ S m A j l‖ ≤ B ^ (2 * (l - j) - 1) := by
  have h0 := (chainTilde_bounds h hB2 hBL (l - j) le_rfl j l rfl σ hσ σ hσ).1
  unfold Split.chainM
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_prod_le_one h.m_le _)).trans h0

end BlockBand.Native.ErdosRiabov.Grid

