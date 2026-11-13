module

public import BlockBand.SourceProcess.Stochastic.Dyson.Contraction

/-!
# Dyson Brownian motion: the overlap–overlap bracket contraction

With `qf q M = q* M q` and `z_a = q* P_a q`:
* `sum_qf_mul_qf`: `∑_x qf(A E_x B) qf(C E_x D) = qf(A D) qf(C B)`;
* `SpecFamily.sum_qf_dProj_mul`: `∑_x qf(dP_i[E_x]) qf(dP_k[E_x])` equals
  `2 ∑_{j ≠ i} (μ_i - μ_j)⁻² z_i z_j` if `i = k` and `-2 (μ_i - μ_k)⁻² z_i z_k` otherwise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix
open scoped Matrix

variable {N : ℕ}

/-- The quadratic form `q* M q`. -/
def qf (q : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) ℂ) : ℂ := star q ⬝ᵥ (M *ᵥ q)

theorem qf_eq_trace (q : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    qf q M = trace (M * vecMulVec q (star q)) := by
  simp only [qf, dotProduct, mulVec, trace, diag, mul_apply, vecMulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.star_apply]; ring

theorem qf_add (q : Fin N → ℂ) (A B : Matrix (Fin N) (Fin N) ℂ) :
    qf q (A + B) = qf q A + qf q B := by
  simp [qf, add_mulVec, dotProduct_add]

theorem qf_smul (q : Fin N → ℂ) (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    qf q (c • A) = c * qf q A := by
  simp [qf, smul_mulVec, dotProduct_smul]

theorem qf_sum {ι : Type*} (s : Finset ι) (q : Fin N → ℂ) (A : ι → Matrix (Fin N) (Fin N) ℂ) :
    qf q (∑ j ∈ s, A j) = ∑ j ∈ s, qf q (A j) := by
  simp [qf, sum_mulVec, dotProduct_sum]

theorem vecMulVec_mul_vecMulVec (q : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    vecMulVec q (star q) * X * vecMulVec q (star q) = qf q X • vecMulVec q (star q) := by
  ext a b
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, qf, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- `∑_x qf(A E_x B) qf(C E_x D) = qf(A D) qf(C B)`. -/
theorem sum_qf_mul_qf (q : Fin N → ℂ) (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, qf q (A * hermBasis x * B) * qf q (C * hermBasis x * D) = qf q (A * D) * qf q (C * B) := by
  set Qq := vecMulVec q (star q)
  have e : ∀ (A B : Matrix (Fin N) (Fin N) ℂ) x,
      qf q (A * hermBasis x * B) = trace ((B * Qq * A) * hermBasis x) := fun A B x => by
    rw [qf_eq_trace, show A * hermBasis x * B * Qq = (A * hermBasis x) * (B * Qq) by
      simp only [Matrix.mul_assoc], trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp_rw [e]
  rw [sum_trace_mul_trace_mul]
  have : B * Qq * A * (D * Qq * C) = B * (Qq * (A * D) * Qq) * C := by
    simp only [Matrix.mul_assoc]
  rw [this, vecMulVec_mul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  rw [qf_eq_trace, Matrix.mul_assoc C B, trace_mul_comm C]

namespace SpecFamily

variable {H : Matrix (Fin N) (Fin N) ℂ} {P : Fin N → Matrix (Fin N) (Fin N) ℂ} {μ : Fin N → ℂ}
  (hS : SpecFamily H P μ)
include hS

theorem qf_proj_mul (q : Fin N → ℂ) (a b : Fin N) :
    qf q (P a * P b) = if a = b then qf q (P a) else 0 := by
  rw [hS.mul_proj]; split_ifs <;> simp [qf]

omit hS in
theorem qf_dProj (q : Fin N → ℂ) (i : Fin N) (E : Matrix (Fin N) (Fin N) ℂ) :
    qf q (dProj P μ i E) = ∑ j ∈ Finset.univ.erase i,
      (μ i - μ j)⁻¹ * (qf q (P j * E * P i) + qf q (P i * E * P j)) := by
  simp only [dProj, qf_sum, qf_smul, qf_add]

/-- **Overlap bracket contraction.** -/
theorem sum_qf_dProj_mul (q : Fin N → ℂ) (i k : Fin N) :
    ∑ x, qf q (dProj P μ i (hermBasis x)) * qf q (dProj P μ k (hermBasis x)) =
      if i = k then 2 * ∑ j ∈ Finset.univ.erase i,
          (μ i - μ j)⁻¹ ^ 2 * (qf q (P i) * qf q (P j))
      else -2 * (μ i - μ k)⁻¹ ^ 2 * (qf q (P i) * qf q (P k)) := by
  simp_rw [qf_dProj q, Finset.sum_mul, Finset.mul_sum]
  -- exchange the coordinate sum to the inside
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  have hin : ∀ j l, ∑ x, (μ i - μ j)⁻¹ * (qf q (P j * hermBasis x * P i) +
        qf q (P i * hermBasis x * P j)) *
      ((μ k - μ l)⁻¹ * (qf q (P l * hermBasis x * P k) + qf q (P k * hermBasis x * P l))) =
      (μ i - μ j)⁻¹ * (μ k - μ l)⁻¹ *
        (qf q (P j * P k) * qf q (P l * P i) + qf q (P j * P l) * qf q (P k * P i) +
          (qf q (P i * P k) * qf q (P l * P j) + qf q (P i * P l) * qf q (P k * P j))) := by
    intro j l
    rw [← sum_qf_mul_qf, ← sum_qf_mul_qf, ← sum_qf_mul_qf, ← sum_qf_mul_qf,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp_rw [hin, hS.qf_proj_mul q]
  by_cases hik : i = k
  · subst hik
    simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Finset.sum_eq_single_of_mem j hj (fun l hl hlj => by
      have hli : l ≠ i := Finset.ne_of_mem_erase hl
      simp [hji, hlj, Ne.symm hlj, Ne.symm hli, hli])]
    simp only [hji, Ne.symm hji, ↓reduceIte, mul_zero, zero_add, add_zero]
    ring
  · simp only [hik, ↓reduceIte]
    have hki : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ k⟩
    have hik' : i ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩
    rw [Finset.sum_eq_single_of_mem k hki (fun j _ hj => Finset.sum_eq_zero fun l _ => by
      simp [hj, Ne.symm hj, Ne.symm hik])]
    rw [Finset.sum_eq_single_of_mem i hik' (fun l hl hli => by
      have hlk : l ≠ k := Finset.ne_of_mem_erase hl
      simp [hli, Ne.symm hli, Ne.symm hik, hlk, Ne.symm hlk])]
    simp only [hik, Ne.symm hik, ↓reduceIte, mul_zero, zero_add, add_zero]
    rw [show (μ k - μ i)⁻¹ = -(μ i - μ k)⁻¹ by rw [← neg_sub, inv_neg]]
    ring

end SpecFamily

end BlockBand.SourceProcess.Stochastic.Dyson
