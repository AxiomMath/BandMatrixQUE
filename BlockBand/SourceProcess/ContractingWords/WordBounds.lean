module

public import BlockBand.SourceProcess.ContractingWords.WordAlgebra

/-!
# Crude word bounds and product telescoping (deterministic)

* `norm_bilinear_herm_le`, `norm_le_nuclearNorm`: `|u*Av| ≤ Tr|A|‖u‖‖v‖`, `‖A‖ ≤ Tr|A|`;
* `norm_trace_herm_mul_le`: `|Tr(AR)| ≤ Tr|A|‖R‖` (Hermitian `A`);
* `norm_list_prod_sub_le`: `|Π a_i - Π b_i| ≤ (Σ|a_i - b_i|) Π(1 + |a_i| + |b_i|)`;
* `list_prod_smul_sep`: `Π_i A_i(f_iB_i) = (Π f_i) Π_i A_iB_i`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n]

theorem norm_bilinear_herm_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (u v : n → ℂ) :
    ‖bilinear u A v‖ ≤ nuclearNorm A * vecNorm u * vecNorm v := by
  have h := bilinear_mul_herm_mul hA 1 1 u v
  rw [Matrix.one_mul, Matrix.mul_one] at h
  rw [h, nuclearNorm_eq_sum hA, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_bilinear_le u 1 (eigVec hA m)
  have h2 := norm_bilinear_le (eigVec hA m) 1 v
  rw [vecNorm_eigVec] at h1 h2
  have h3 := norm_one_matrix_le (n := n)
  have hu := vecNorm_nonneg u
  have hv := vecNorm_nonneg v
  have e1 : ‖bilinear u 1 (eigVec hA m)‖ ≤ vecNorm u := by nlinarith [norm_nonneg (1 : Matrix n n ℂ)]
  have e2 : ‖bilinear (eigVec hA m) 1 v‖ ≤ vecNorm v := by nlinarith [norm_nonneg (1 : Matrix n n ℂ)]
  calc |hA.eigenvalues m| * ‖bilinear u 1 (eigVec hA m)‖ * ‖bilinear (eigVec hA m) 1 v‖ ≤
      |hA.eigenvalues m| * vecNorm u * vecNorm v := by
        gcongr
    _ = _ := by ring

theorem norm_le_nuclearNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) : ‖A‖ ≤ nuclearNorm A := by
  refine opNorm_le_of_vec A (nuclearNorm_nonneg A) fun x => ?_
  have h := norm_bilinear_herm_le hA (A *ᵥ x) x
  have e : bilinear (A *ᵥ x) A x = ((vecNorm (A *ᵥ x) ^ 2 : ℝ) : ℂ) := star_self_eq _
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
  have h0 := vecNorm_nonneg (A *ᵥ x)
  rcases h0.eq_or_lt with h1 | h1
  · rw [← h1]; exact mul_nonneg (nuclearNorm_nonneg A) (vecNorm_nonneg x)
  · nlinarith

theorem norm_trace_herm_mul_le {A : Matrix n n ℂ} (hA : A.IsHermitian) (R : Matrix n n ℂ) :
    ‖(A * R).trace‖ ≤ nuclearNorm A * ‖R‖ := by
  rw [trace_herm_mul hA, nuclearNorm_eq_sum hA, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := norm_bilinear_le (eigVec hA m) R (eigVec hA m)
  rw [vecNorm_eigVec, one_mul, mul_one] at h
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem norm_list_prod_sub_le {α : Type*} (L : List α) (a b : α → ℂ) :
    ‖(L.map a).prod - (L.map b).prod‖ ≤
      (L.map fun x => ‖a x - b x‖).sum * (L.map fun x => 1 + ‖a x‖ + ‖b x‖).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    set A := (L.map a).prod
    set B := (L.map b).prod
    set Sg := (L.map fun x => ‖a x - b x‖).sum
    set R := (L.map fun x => 1 + ‖a x‖ + ‖b x‖).prod
    have hR : 0 ≤ R := List.prod_nonneg fun y hy => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy; positivity
    have hSg : 0 ≤ Sg := List.sum_nonneg fun y hy => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy; positivity
    have hA : ‖A‖ ≤ R := by
      rw [List.norm_prod_map]
      exact list_prod_le_of_le L _ _ (fun _ _ => norm_nonneg _) fun z _ => by
        linarith [norm_nonneg (b z)]
    have e : a x * A - b x * B = (a x - b x) * A + b x * (A - B) := by ring
    rw [e]
    have hax := norm_nonneg (a x - b x)
    have hbx := norm_nonneg (b x)
    have hax' := norm_nonneg (a x)
    calc ‖(a x - b x) * A + b x * (A - B)‖ ≤ ‖a x - b x‖ * R + ‖b x‖ * (Sg * R) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul_of_nonneg_left hA hax
          · exact mul_le_mul_of_nonneg_left ih hbx
      _ ≤ (‖a x - b x‖ + Sg) * ((1 + ‖a x‖ + ‖b x‖) * R) := by
          nlinarith [mul_nonneg hax hR, mul_nonneg (mul_nonneg hax hax') hR,
            mul_nonneg (mul_nonneg hax hbx) hR, mul_nonneg hSg hR,
            mul_nonneg (mul_nonneg hSg hax') hR]

theorem list_prod_smul_sep {α β : Type*} (w : List (α × β)) (A : α → Matrix n n ℂ)
    (B : β → Matrix n n ℂ) (f : β → ℂ) :
    (w.map fun x => A x.1 * (f x.2 • B x.2)).prod =
      (w.map fun x => f x.2).prod • (w.map fun x => A x.1 * B x.2).prod := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [List.map_cons, List.prod_cons, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    rw [mul_comm]

end BlockBand.SourceProcess.ContractingWords
