module

public import BlockBand.Palm.MomentFlow.MultiColInv
public import BlockBand.Palm.MomentFlow.MultiRowPerm
public import BlockBand.Palm.MomentFlow.MultiFixed

/-!
# Column form: the reciprocal matching weight as a smooth family

* `invW_contDiff`, `hasDerivAt_invW_line`, `hasDerivAt_invD1_line` (line derivatives
  `d1 = -F1/W²`, `d2 = -F2/W² + 2F1²/W³`);
* `rlPhi_ge_exp`, `permW_ge_pow`, `rlPhi_zero`, `permW_start_ge_one` (the uniform bound
  `1/W ≤ 1` on the start event is proved inline in `multi_col_any`, `hwM`);
* `inv_drift_le` (summed against `v ≥ 0` on the sector) and `inv_Q_le` (enumeration coordinates).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N r : ℕ}

theorem shift_zero_eq (lam : Fin N → ℝ) (i : Fin N) :
    (fun m => lam m + if m = i then (0 : ℝ) else 0) = lam := by
  funext m; simp

theorem invW_contDiff {φ : ℝ → ℝ} (hφc : ContDiff ℝ 2 φ) (hφp : ∀ z, 0 < φ z) {ζ : Occ N}
    (hζ : ζ ∈ sector N r) :
    ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => (permW φ z.1 z.2 ζ)⁻¹) :=
  (permW_contDiff hφc ζ).inv fun z => (permW_pos hφp z.1 z.2 hζ).ne'

theorem hasDerivAt_invW_line {φ φ1 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφp : ∀ z, 0 < φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ) {ζ : Occ N} (hζ : ζ ∈ sector N r)
    (i : Fin N) :
    HasDerivAt (fun s : ℝ => (permW φ (fun m => lam m + if m = i then s else 0) c ζ)⁻¹)
      (-(permF1 φ φ1 lam c ζ i) / permW φ lam c ζ ^ 2) 0 := by
  have h := (hasDerivAt_permW_line hφ lam c ζ i).inv (by
    rw [shift_zero_eq]; exact (permW_pos hφp lam c hζ).ne')
  rw [shift_zero_eq] at h
  exact h

theorem hasDerivAt_invD1_line {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z)
    (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z) (hφp : ∀ z, 0 < φ z) (lam : Fin N → ℝ) (c : Fin r → ℝ)
    {ζ : Occ N} (hζ : ζ ∈ sector N r) (i : Fin N) :
    HasDerivAt (fun s : ℝ => -(permF1 φ φ1 (fun m => lam m + if m = i then s else 0) c ζ i) /
        permW φ (fun m => lam m + if m = i then s else 0) c ζ ^ 2)
      (-(permF2 φ φ1 φ2 lam c ζ i) / permW φ lam c ζ ^ 2 +
        2 * permF1 φ φ1 lam c ζ i ^ 2 / permW φ lam c ζ ^ 3) 0 := by
  have hW := hasDerivAt_permW_line hφ lam c ζ i
  have hF := hasDerivAt_permWD1_line hφ hφ1 lam c ζ i
  have hWp : 0 < permW φ lam c ζ := permW_pos hφp lam c hζ
  have h := (hF.neg).fun_div (hW.fun_pow 2) (by
    simp only [shift_zero_eq]; exact pow_ne_zero 2 hWp.ne')
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, shift_zero_eq, permF1, permF2]
  field_simp
  ring

theorem rlPsi_ge {E d R : ℝ} (hR : 0 < R) (x : ℝ) : -(2 * R) ≤ rlPsi E d R x := by
  unfold rlPsi
  by_cases hy : rlG d (x - E) ≤ -2 * R
  · rw [rlTheta_eq_neg hR hy]; linarith
  · exact le_trans (by linarith) (le_rlTheta hR _)

theorem rlPhi_ge_exp {ν E d R : ℝ} (hν : 0 ≤ ν) (hR : 0 < R) (x : ℝ) :
    Real.exp (-(2 * ν * R)) ≤ rlPhi ν E d R x := by
  unfold rlPhi
  refine Real.exp_le_exp.mpr ?_
  have := rlPsi_ge (E := E) (d := d) hR x
  nlinarith

theorem rlPhi_zero {ν d R : ℝ} (hd : 0 < d) (hR : 0 < R) : rlPhi ν 0 d R 0 = 1 := by
  unfold rlPhi rlPsi
  have hg : rlG d (0 - 0) = 0 := by
    unfold rlG
    rw [sub_zero, show (0 : ℝ) ^ 2 + d ^ 2 = d ^ 2 by ring, Real.sqrt_sq hd.le, sub_self]
  rw [hg, rlTheta_eq_self hR (by linarith)]
  simp

theorem permW_ge_pow {φ : ℝ → ℝ} {m₀ : ℝ} (hm₀ : 0 ≤ m₀) (hφm : ∀ z, m₀ ≤ φ z)
    (lam : Fin N → ℝ) (c : Fin r → ℝ) {ζ : Occ N} (hζ : ζ ∈ sector N r) :
    m₀ ^ r ≤ permW φ lam c ζ := by
  obtain ⟨y, hy⟩ := exists_occOf r ζ hζ
  have hy' : y ∈ labs r ζ := mem_labs.2 hy
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => hm₀.trans (hφm z)
  have h1 : m₀ ^ r ≤ pW φ lam c y := by
    have : m₀ ^ r = ∏ _m : Fin r, m₀ := by simp
    rw [this]
    exact Finset.prod_le_prod₀ (fun _ _ => hm₀) fun m _ => hφm _
  have h2 : pW φ lam c y ≤ ∑ y ∈ labs r ζ, pW φ lam c y :=
    Finset.single_le_sum (f := fun y => pW φ lam c y) (fun y _ => pW_nonneg hφ0 _ _ y) hy'
  unfold permW
  calc m₀ ^ r ≤ ∑ y ∈ labs r ζ, pW φ lam c y := h1.trans h2
    _ ≤ _ := le_mul_of_one_le_left (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 _ _ y)
          (one_le_cfgFact ζ)

/-- The start configuration has matching weight `≥ 1` (identity matching, `φ(0) = 1`). -/
theorem permW_start_ge_one {φ : ℝ → ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : φ 0 = 1)
    (lam : Fin N → ℝ) {ξ : Occ N} {x : Fin r → Fin N} (hx : x ∈ labs r ξ) :
    1 ≤ permW φ lam (fun m => lam (x m)) ξ := by
  have h := permW_terminal_ge hφ0 lam (fun m => lam (x m)) hx (θ := 0) (fun m => by
    simp [hφ1])
  simpa using h

/-- **Drift of the reciprocal matching weight, summed against `v ≥ 0` on the sector.** -/
theorem inv_drift_le (lam : Fin N → ℝ) (ℓ : ℕ) (c : Fin r → ℝ)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφp : ∀ z, 0 < φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 < K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|)
    (v : Occ N → ℝ) (hv : ∀ ξ ∈ sector N r, 0 ≤ v ξ) :
    ∑ ξ ∈ sector N r, (permW φ lam c ξ)⁻¹ * momentGenerator (cfgRate N lam ℓ 0) v ξ +
        ∑ ξ ∈ sector N r, v ξ *
          ∑ i, (dysonDrift N lam i * (-(permF1 φ φ1 lam c ξ i) / permW φ lam c ξ ^ 2) +
          (-(permF2 φ φ1 φ2 lam c ξ i) / permW φ lam c ξ ^ 2 +
            2 * permF1 φ φ1 lam c ξ i ^ 2 / permW φ lam c ξ ^ 3) / (2 * N)) ≤
      ((r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) +
        r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N + r ^ 2 * A ^ 2 / N) *
        ∑ ξ ∈ sector N r, (permW φ lam c ξ)⁻¹ * v ξ := by
  rw [sum_mul_momentGenerator_symm (cfgRate_symm lam ℓ 0) r v (fun η => (permW φ lam c η)⁻¹),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun ξ hξ => ?_
  rw [← mul_add]
  have h := inv_point_drift_le lam ℓ c hφ hφ1 hφp hA hA0 hB hB0 hK0 hcomp hc₁ hshort hlong hξ
  calc _ ≤ v ξ * (((r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) +
        r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N + r ^ 2 * A ^ 2 / N) * (permW φ lam c ξ)⁻¹) :=
        mul_le_mul_of_nonneg_left h (hv ξ hξ)
    _ = _ := by ring

/-- The summed reciprocal drift inequality in enumeration coordinates. -/
theorem inv_Q_le (lam : Fin N → ℝ) (ℓ r : ℕ) (c : Fin r → ℝ) (vv : Fin (sectorCard N r) → ℝ)
    (hvv : ∀ q, 0 ≤ vv q)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B K G c₁ : ℝ} (hφp : ∀ z, 0 < φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hK0 : 0 < K)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ K * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    ∑ q, (permW φ lam c (sectorEnum N r q))⁻¹ *
          ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' +
        ∑ q, vv q * ∑ i, (dysonDrift N lam i *
          (-(permF1 φ φ1 lam c (sectorEnum N r q) i) / permW φ lam c (sectorEnum N r q) ^ 2) +
          (-(permF2 φ φ1 φ2 lam c (sectorEnum N r q) i) / permW φ lam c (sectorEnum N r q) ^ 2 +
            2 * permF1 φ φ1 lam c (sectorEnum N r q) i ^ 2 /
              permW φ lam c (sectorEnum N r q) ^ 3) / (2 * N)) ≤
      ((r * (2 * ℓ * B * K / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (K ^ 2 + 1)) / (2 * N)) +
        r * (2 * ℓ + r) * A ^ 2 * K ^ 3 / N + r ^ 2 * A ^ 2 / N) *
        ∑ q, (permW φ lam c (sectorEnum N r q))⁻¹ * vv q := by
  have hact : ∀ q, ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' =
      momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) (sectorEnum N r q) := by
    intro q
    rw [← cfgMat_act]
    exact Finset.sum_congr rfl fun q' _ => by rw [cfgExt_enum]
  have hv : ∀ ξ ∈ sector N r, 0 ≤ cfgExt r vv ξ := fun ξ hξ => by
    rw [cfgExt_of_mem vv hξ]; exact hvv _
  have h := inv_drift_le (r := r) lam ℓ c hφ hφ1 hφp hA hA0 hB hB0 hK0 hcomp hc₁ hshort hlong
    (cfgExt r vv) hv
  set T : Occ N → ℝ := fun ξ => ∑ i, (dysonDrift N lam i *
      (-(permF1 φ φ1 lam c ξ i) / permW φ lam c ξ ^ 2) +
      (-(permF2 φ φ1 φ2 lam c ξ i) / permW φ lam c ξ ^ 2 +
        2 * permF1 φ φ1 lam c ξ i ^ 2 / permW φ lam c ξ ^ 3) / (2 * N)) with hT
  have e1 : ∑ q, (permW φ lam c (sectorEnum N r q))⁻¹ *
        ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' =
      ∑ ξ ∈ sector N r, (permW φ lam c ξ)⁻¹ *
        momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [hact]).trans (sum_sectorEnum r (fun ξ =>
      (permW φ lam c ξ)⁻¹ * momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) ξ))
  have e2 : ∑ q, vv q * T (sectorEnum N r q) = ∑ ξ ∈ sector N r, cfgExt r vv ξ * T ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [cfgExt_enum]).trans
      (sum_sectorEnum r (fun ξ => cfgExt r vv ξ * T ξ))
  have e3 : ∑ q, (permW φ lam c (sectorEnum N r q))⁻¹ * vv q =
      ∑ ξ ∈ sector N r, (permW φ lam c ξ)⁻¹ * cfgExt r vv ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [cfgExt_enum]).trans (sum_sectorEnum r (fun ξ =>
      (permW φ lam c ξ)⁻¹ * cfgExt r vv ξ))
  rw [e1, e3]
  exact e2 ▸ h

end BlockBand.Palm.MomentFlow
