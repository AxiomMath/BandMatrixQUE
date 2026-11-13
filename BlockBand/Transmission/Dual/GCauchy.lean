module

public import BlockBand.Transmission.Dual.GCompact
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The general-`p` Cauchy determinant

* `det_cauchyMatrix_mul`: the Cauchy determinant identity over any field;
* `cauchyH_pos`: `H_q > 0` on `𝒞_q` (so `H_q = |det (1/(x_i + y_j))|` there);
* `cauchyH_le_sum`: the row-1 expansion bound
  `H_{q+1}(z) ≤ Σ_j h(x₀, y_j) H_q(restOf j z)`, `h(x, y) = 1/(x + y)`;
* `exists_cauchyH_le_of_gap`: the bound `H_p ≤ C δ` on
  `{some gap ≤ δ, x_i + y_j ≥ η, coordinates ≤ K}`, used for the collision bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath

section Field

variable {K : Type*} [Field K]

/-- The Cauchy matrix `(1/(x_i + y_j))`. -/
def cauchyMatrix {n : ℕ} (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  of fun i j => (x i + y j)⁻¹

/-- The Cauchy numerator `Π_{i<k} (x_k − x_i)(y_k − y_i)`. -/
def cauchyNum {n : ℕ} (x y : Fin n → K) : K :=
  ∏ i : Fin n, ∏ k ∈ Ioi i, ((x k - x i) * (y k - y i))

/-- The Cauchy denominator `Π_{i,j} (x_i + y_j)`. -/
def cauchyDen {n : ℕ} (x y : Fin n → K) : K := ∏ i : Fin n, ∏ j : Fin n, (x i + y j)

theorem cauchyNum_succ {n : ℕ} (x y : Fin (n + 1) → K) :
    cauchyNum x y = (∏ k : Fin n, ((x k.succ - x 0) * (y k.succ - y 0))) *
      cauchyNum (fun i => x i.succ) (fun i => y i.succ) := by
  unfold cauchyNum
  rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  congr 1
  exact Finset.prod_congr rfl fun i _ => Fin.prod_Ioi_succ _ i

theorem cauchyDen_succ {n : ℕ} (x y : Fin (n + 1) → K) :
    cauchyDen x y = (∏ j, (x 0 + y j)) * ((∏ i : Fin n, (x i.succ + y 0)) *
      cauchyDen (fun i => x i.succ) (fun i => y i.succ)) := by
  unfold cauchyDen
  rw [Fin.prod_univ_succ]
  congr 1
  simp only [Fin.prod_univ_succ (n := n) (fun j => _ + y j)]
  exact Finset.prod_mul_distrib

/-- One step of row and column elimination of the Cauchy matrix. -/
private theorem det_step {n : ℕ} (x y : Fin (n + 1) → K) (h : ∀ i j, x i + y j ≠ 0) :
    det (cauchyMatrix x y) =
      ((∏ i : Fin n, (x 0 - x i.succ)) * ∏ j, (x 0 + y j)⁻¹) *
        (((∏ i : Fin n, (x i.succ + y 0)⁻¹) * ∏ j : Fin n, (y 0 - y j.succ)) *
          det (cauchyMatrix (fun i => x i.succ) (fun i => y i.succ))) := by
  -- rows: subtract row `0` from the other rows
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := of fun i j =>
    if i = 0 then (x 0 + y j)⁻¹ else (x 0 - x i) * ((x 0 + y j)⁻¹ * (x i + y j)⁻¹) with hB
  have h1 : det (cauchyMatrix x y) = det B := by
    refine det_eq_of_forall_row_eq_smul_add_const (fun i => if i = 0 then 0 else 1) 0
      (by simp) fun i j => ?_
    by_cases hi : i = 0
    · subst hi; simp [cauchyMatrix, hB]
    · have := h i j; have := h 0 j
      simp only [cauchyMatrix, hB, of_apply, hi, ite_false, ite_true, one_mul]
      field_simp
      ring
  -- factor rows and columns
  set E : Matrix (Fin (n + 1)) (Fin (n + 1)) K := of fun i j =>
    if i = 0 then 1 else (x i + y j)⁻¹ with hE
  have h2 : det B = (∏ i, (if i = 0 then (1 : K) else x 0 - x i)) *
      ((∏ j, (x 0 + y j)⁻¹) * det E) := by
    rw [← det_mul_row, ← det_mul_column]
    congr 1
    ext i j
    by_cases hi : i = 0
    · subst hi; have := h 0 j; simp [hB, hE]
    · simp [hB, hE, hi]
  -- columns: subtract column `0` from the other columns
  set F : Matrix (Fin (n + 1)) (Fin (n + 1)) K := of fun i j =>
    if i = 0 then (if j = 0 then 1 else 0) else
      if j = 0 then (x i + y 0)⁻¹ else (y 0 - y j) * ((x i + y 0)⁻¹ * (x i + y j)⁻¹) with hF
  have h3 : det E = det F := by
    rw [← det_transpose E, ← det_transpose F]
    refine det_eq_of_forall_row_eq_smul_add_const (fun j => if j = 0 then 0 else 1) 0
      (by simp) fun j i => ?_
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi hj; simp [hE, hF]
    · subst hi; simp [hE, hF, hj]
    · subst hj; simp [hE, hF, hi]
    · have := h i j; have := h i 0
      simp only [transpose_apply, hE, hF, of_apply, hi, hj, ite_false, ite_true, one_mul]
      field_simp
      ring
  have h4 : det F = ((∏ i : Fin n, (x i.succ + y 0)⁻¹) * ∏ j : Fin n, (y 0 - y j.succ)) *
      det (cauchyMatrix (fun i => x i.succ) (fun i => y i.succ)) := by
    rw [det_succ_row_zero, Fin.sum_univ_succ]
    have hz : ∀ j : Fin n, F 0 j.succ = 0 := fun j => by simp [hF, Fin.succ_ne_zero]
    simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.succAbove_zero]
    have h00 : F 0 0 = 1 := by simp [hF]
    rw [h00, Fin.val_zero, pow_zero, one_mul, one_mul, mul_assoc, ← det_mul_row,
      ← det_mul_column]
    congr 1
    ext i j
    simp only [hF, cauchyMatrix, of_apply, submatrix_apply, Fin.succ_ne_zero, ite_false]
    ring
  rw [h1, h2, h3, h4, Fin.prod_univ_succ]
  simp only [ite_true, one_mul, Fin.succ_ne_zero, ite_false]
  ring

/-- **The Cauchy determinant**: `det (1/(x_i+y_j)) · Π_{i,j}(x_i+y_j) = Π_{i<k}(x_k−x_i)(y_k−y_i)`. -/
theorem det_cauchyMatrix_mul : ∀ {n : ℕ} (x y : Fin n → K), (∀ i j, x i + y j ≠ 0) →
    det (cauchyMatrix x y) * cauchyDen x y = cauchyNum x y
  | 0, x, y, _ => by simp [cauchyDen, cauchyNum]
  | n + 1, x, y, h => by
    have ih := det_cauchyMatrix_mul (fun i => x i.succ) (fun i => y i.succ)
      (fun i j => h i.succ j.succ)
    have hs : (∏ j, (x 0 + y j)⁻¹) * ∏ j, (x 0 + y j) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun j _ => inv_mul_cancel₀ (h 0 j)
    have hw : (∏ i : Fin n, (x i.succ + y 0)⁻¹) * ∏ i : Fin n, (x i.succ + y 0) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => inv_mul_cancel₀ (h i.succ 0)
    have hsign : (∏ i : Fin n, (x 0 - x i.succ)) * ∏ j : Fin n, (y 0 - y j.succ) =
        ∏ k : Fin n, ((x k.succ - x 0) * (y k.succ - y 0)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by ring
    rw [det_step x y h, cauchyDen_succ, cauchyNum_succ, ← ih, ← hsign]
    linear_combination
      (((∏ i : Fin n, (x 0 - x i.succ)) * ∏ j : Fin n, (y 0 - y j.succ)) *
        det (cauchyMatrix (fun i => x i.succ) (fun i => y i.succ)) *
        cauchyDen (fun i => x i.succ) (fun i => y i.succ)) *
        ((∏ i : Fin n, (x i.succ + y 0)⁻¹) * (∏ i : Fin n, (x i.succ + y 0)) * hs +
          hw)

theorem cauchyDen_ne_zero {n : ℕ} {x y : Fin n → K} (h : ∀ i j, x i + y j ≠ 0) :
    cauchyDen x y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => h i j

theorem det_cauchyMatrix {n : ℕ} {x y : Fin n → K} (h : ∀ i j, x i + y j ≠ 0) :
    det (cauchyMatrix x y) = cauchyNum x y / cauchyDen x y := by
  rw [← det_cauchyMatrix_mul x y h, mul_div_cancel_right₀ _ (cauchyDen_ne_zero h)]

/-- Row-`0` expansion: the minors are Cauchy matrices of `(x ∘ succ, y ∘ j.succAbove)`. -/
theorem det_cauchyMatrix_succ {n : ℕ} (x y : Fin (n + 1) → K) :
    det (cauchyMatrix x y) = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * (x 0 + y j)⁻¹ *
      det (cauchyMatrix (fun i => x i.succ) (fun l => y (j.succAbove l))) := by
  rw [det_succ_row_zero]; rfl

end Field

/-!
## On the chamber
-/

variable {q : ℕ}

/-- `H_q(z) = det (1/(x_i + y_j))`; positive on the chamber (`cauchyH_pos`). -/
def cauchyH (q : ℕ) (z : DualCoord q) : ℝ := det (cauchyMatrix z.1 z.2)

theorem add_pos_of_mem {z : DualCoord q} (hz : z ∈ dualChamber q) (i j : Fin q) :
    0 < z.1 i + z.2 j :=
  add_pos (hz.2.2.1 i) (hz.2.2.2 j).1

theorem cauchyNum_pos {z : DualCoord q} (hz : z ∈ dualChamber q) : 0 < cauchyNum z.1 z.2 :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hk =>
    mul_pos (sub_pos.2 (hz.1 (Finset.mem_Ioi.1 hk))) (sub_pos.2 (hz.2.1 (Finset.mem_Ioi.1 hk)))

theorem cauchyDen_pos {z : DualCoord q} (hz : z ∈ dualChamber q) : 0 < cauchyDen z.1 z.2 :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => add_pos_of_mem hz i j

theorem cauchyH_eq {z : DualCoord q} (hz : z ∈ dualChamber q) :
    cauchyH q z = cauchyNum z.1 z.2 / cauchyDen z.1 z.2 :=
  det_cauchyMatrix fun i j => (add_pos_of_mem hz i j).ne'

theorem cauchyH_pos {z : DualCoord q} (hz : z ∈ dualChamber q) : 0 < cauchyH q z := by
  rw [cauchyH_eq hz]; exact div_pos (cauchyNum_pos hz) (cauchyDen_pos hz)

/-- **Row-1 expansion bound**: `H_{q+1} ≤ Σ_j h(x₀, y_j) H_q(rest_j)`. -/
theorem cauchyH_le_sum {z : DualCoord (q + 1)} (hz : z ∈ dualChamber (q + 1)) :
    cauchyH (q + 1) z ≤ ∑ j, (z.1 0 + z.2 j)⁻¹ * cauchyH q (restOf j z) := by
  have he : cauchyH (q + 1) z = ∑ j : Fin (q + 1), (-1) ^ (j : ℕ) * (z.1 0 + z.2 j)⁻¹ *
      cauchyH q (restOf j z) := det_cauchyMatrix_succ z.1 z.2
  rw [← abs_of_pos (cauchyH_pos hz), he]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (inv_pos.2 (add_pos_of_mem hz 0 j)),
    abs_of_pos (cauchyH_pos (rest_mem_dualChamber j hz))]

/-!
## The gap bound
-/

private theorem prod_le_pow_of_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {M : ℝ}
    (hM : 1 ≤ M) {m : ℕ} (hs : s.card ≤ m) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ M) :
    ∏ i ∈ s, f i ≤ M ^ m := by
  calc ∏ i ∈ s, f i ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ h0 h1
    _ = M ^ s.card := Finset.prod_const M
    _ ≤ M ^ m := pow_le_pow_right₀ hM hs

/-- **The deterministic gap bound**: on the chamber, if every `x_i + y_j ≥ η > 0`, every
`x_i ≤ K`, and some gap (pairwise, equivalently consecutive) of the `x`'s or of the `y`'s is
`≤ δ`, then `H_q ≤ C δ`, with `C` depending only on `q, η, K`. -/
theorem exists_cauchyH_le_of_gap (q : ℕ) {η : ℝ} (hη : 0 < η) (K : ℝ) :
    ∃ C : ℝ, ∀ z ∈ dualChamber q, (∀ i j, η ≤ z.1 i + z.2 j) → (∀ i, z.1 i ≤ K) →
      ∀ δ : ℝ, ((∃ i k, i < k ∧ z.1 k - z.1 i ≤ δ) ∨ (∃ i k, i < k ∧ z.2 k - z.2 i ≤ δ)) →
        cauchyH q z ≤ C * δ := by
  set M := max K 1 with hMdef
  have hM : 1 ≤ M := le_max_right _ _
  refine ⟨M * M ^ q * (M ^ q) ^ q / (η ^ q) ^ q, fun z hz hηz hK δ hgap => ?_⟩
  set F : Fin q → Fin q → ℝ := fun i k => (z.1 k - z.1 i) * (z.2 k - z.2 i) with hFdef
  have hF0 : ∀ i, ∀ k ∈ Ioi i, 0 ≤ F i k := fun i k hk =>
    (mul_pos (sub_pos.2 (hz.1 (mem_Ioi.1 hk))) (sub_pos.2 (hz.2.1 (mem_Ioi.1 hk)))).le
  have hxle : ∀ i k, z.1 k - z.1 i ≤ M := fun i k => by
    have := hz.2.2.1 i; have := hK k; have := le_max_left K 1; linarith
  have hyle : ∀ i k, z.2 k - z.2 i ≤ 1 := fun i k => by
    have := (hz.2.2.2 i).1; have := (hz.2.2.2 k).2; linarith
  have hFM : ∀ i, ∀ k ∈ Ioi i, F i k ≤ M := fun i k hk => by
    have ha := sub_pos.2 (hz.1 (mem_Ioi.1 hk))
    calc F i k ≤ M * 1 := mul_le_mul (hxle i k) (hyle i k)
          (sub_pos.2 (hz.2.1 (mem_Ioi.1 hk))).le (by linarith)
      _ = M := mul_one M
  set g : Fin q → ℝ := fun i => ∏ k ∈ Ioi i, F i k with hgdef
  have hg0 : ∀ i, 0 ≤ g i := fun i => Finset.prod_nonneg (hF0 i)
  have hgM : ∀ i, g i ≤ M ^ q := fun i =>
    prod_le_pow_of_le _ _ hM ((card_le_univ _).trans (by simp)) (hF0 i) (hFM i)
  -- the special factor
  obtain ⟨i₀, k₀, hik, hspec⟩ : ∃ i k, i < k ∧ F i k ≤ M * δ := by
    rcases hgap with ⟨i, k, hik, hd⟩ | ⟨i, k, hik, hd⟩
    · refine ⟨i, k, hik, ?_⟩
      have ha := sub_pos.2 (hz.1 hik); have hb := sub_pos.2 (hz.2.1 hik)
      calc F i k ≤ δ * 1 := mul_le_mul hd (hyle i k) hb.le (by linarith)
        _ ≤ M * δ := by nlinarith
    · refine ⟨i, k, hik, ?_⟩
      have ha := sub_pos.2 (hz.1 hik); have hb := sub_pos.2 (hz.2.1 hik)
      exact mul_le_mul (hxle i k) hd hb.le (by linarith)
  have hk₀ : k₀ ∈ Ioi i₀ := mem_Ioi.2 hik
  have hgi₀ : g i₀ ≤ M * δ * M ^ q := by
    show ∏ k ∈ Ioi i₀, F i₀ k ≤ _
    rw [← Finset.mul_prod_erase _ _ hk₀]
    exact mul_le_mul hspec (prod_le_pow_of_le _ _ hM
      ((card_le_card (erase_subset _ _)).trans ((card_le_univ _).trans (by simp)))
      (fun k hk => hF0 i₀ k (mem_of_mem_erase hk)) (fun k hk => hFM i₀ k (mem_of_mem_erase hk)))
      (Finset.prod_nonneg fun k hk => hF0 i₀ k (mem_of_mem_erase hk)) (by
        have := hF0 i₀ k₀ hk₀; linarith)
  have hnum : cauchyNum z.1 z.2 ≤ M * δ * M ^ q * (M ^ q) ^ q := by
    show ∏ i, g i ≤ _
    rw [← Finset.mul_prod_erase _ _ (mem_univ i₀)]
    exact mul_le_mul hgi₀ (prod_le_pow_of_le _ _ (one_le_pow₀ hM)
      ((card_le_card (erase_subset _ _)).trans (by simp)) (fun i _ => hg0 i) (fun i _ => hgM i))
      (Finset.prod_nonneg fun i _ => hg0 i) (by have := hg0 i₀; linarith)
  have hden : (η ^ q) ^ q ≤ cauchyDen z.1 z.2 := by
    calc (η ^ q) ^ q = ∏ _i : Fin q, ∏ _j : Fin q, η := by simp
      _ ≤ cauchyDen z.1 z.2 := Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg
          fun _ _ => hη.le) fun i _ => Finset.prod_le_prod₀ (fun _ _ => hη.le)
          fun j _ => hηz i j
  have hηq : 0 < (η ^ q) ^ q := by positivity
  rw [cauchyH_eq hz, div_le_iff₀ (cauchyDen_pos hz)]
  calc cauchyNum z.1 z.2 ≤ M * δ * M ^ q * (M ^ q) ^ q := hnum
    _ = M * M ^ q * (M ^ q) ^ q / (η ^ q) ^ q * δ * (η ^ q) ^ q := by
        field_simp
    _ ≤ M * M ^ q * (M ^ q) ^ q / (η ^ q) ^ q * δ * cauchyDen z.1 z.2 := by
        refine mul_le_mul_of_nonneg_left hden ?_
        have : 0 ≤ M * δ * M ^ q * (M ^ q) ^ q := (Finset.prod_nonneg fun i _ => hg0 i).trans hnum
        have h' : M * M ^ q * (M ^ q) ^ q / (η ^ q) ^ q * δ =
            M * δ * M ^ q * (M ^ q) ^ q / (η ^ q) ^ q := by ring
        rw [h']; positivity

end BlockBand.Transmission.Dual.G
