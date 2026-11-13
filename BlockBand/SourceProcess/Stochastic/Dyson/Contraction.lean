module

public import BlockBand.SourceProcess.Stochastic.Dyson.PerturbAlgebra
public import BlockBand.SourceProcess.Stochastic.Dyson.Coordinates

/-!
# Dyson Brownian motion: GUE contraction identities and the Itô algebra of the spectrum

* `sum_hermBasis_conj`: `∑_x E_x M E_x = tr(M) · 1`;
* `sum_trace_mul_smul_hermBasis`: `∑_x tr(M E_x) E_x = M`;
* `sum_trace_mul_trace_mul`: `∑_x tr(M E_x) tr(M' E_x) = tr(M M')`.

On a `SpecFamily` with the first-variation map `dProj i K = ∑_{j≠i} (μ_i - μ_j)⁻¹ (P_j K P_i + P_i K P_j)`:
* `sum_trace_dProj_mul`: `∑_x tr(dProj i E_x · E_x) = 2 ∑_{j≠i} (μ_i - μ_j)⁻¹`
  (eigenvalue drift);
* `sum_trace_smul_dProj`: `∑_x tr(P_k E_x) dProj i E_x = 0` (eigenvalue–overlap bracket).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix
open scoped Matrix

variable {N : ℕ}

/-- `∑_x E_x M E_x = tr(M) · 1`. -/
theorem sum_hermBasis_conj (M : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, hermBasis x * M * hermBasis x = trace M • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext a d
  simp only [Matrix.sum_apply, mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul, trace,
    diag, Finset.sum_mul]
  have : ∀ x b c, hermBasis x a b * M b c * hermBasis x c d =
      M b c * (hermBasis x a b * hermBasis x c d) := fun x b c => by ring
  simp_rw [this]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N × Fin N)))]
  simp_rw [← Finset.mul_sum, sum_hermBasis_mul_hermBasis]
  by_cases h : a = d
  · subst h
    simp only [true_and, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_comm]; simp
  · simp [h]

theorem sum_smul_sandwich {ι : Type*} [Fintype ι] (A B : Matrix (Fin N) (Fin N) ℂ)
    (c : ι → ℂ) (E : ι → Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, c x • (A * E x * B) = A * (∑ x, c x • E x) * B := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem sum_trace_mul_smul_hermBasis (M : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, trace (M * hermBasis x) • hermBasis x = M := by
  simp_rw [trace_mul_comm M]
  exact sum_trace_smul_hermBasis M

theorem sum_trace_mul_trace_mul (M M' : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, trace (M * hermBasis x) * trace (M' * hermBasis x) = trace (M * M') := by
  conv_rhs => rw [← sum_trace_mul_smul_hermBasis M']
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, mul_comm]

namespace SpecFamily

variable {H : Matrix (Fin N) (Fin N) ℂ} {P : Fin N → Matrix (Fin N) (Fin N) ℂ} {μ : Fin N → ℂ}

/-- The first-variation map of the projection `P_i`. -/
def dProj (P : Fin N → Matrix (Fin N) (Fin N) ℂ) (μ : Fin N → ℂ) (i : Fin N)
    (K : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ j ∈ Finset.univ.erase i, (μ i - μ j)⁻¹ • (P j * K * P i + P i * K * P j)

variable (hS : SpecFamily H P μ)
include hS

theorem trace_proj_mul_proj (i j : Fin N) :
    trace (P i * P j) = if i = j then 1 else 0 := by
  rw [hS.mul_proj]; split_ifs <;> simp [hS.trace_proj]

/-- Eigenvalue drift contraction: `∑_x tr(dP_i[E_x] E_x) = 2 ∑_{j ≠ i} (μ_i - μ_j)⁻¹`. -/
theorem sum_trace_dProj_mul (i : Fin N) :
    ∑ x, trace (dProj P μ i (hermBasis x) * hermBasis x) =
      2 * ∑ j ∈ Finset.univ.erase i, (μ i - μ j)⁻¹ := by
  unfold dProj
  simp_rw [Finset.sum_mul, trace_sum, Matrix.smul_mul, trace_smul, smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.mul_sum]
  have e : ∀ x, trace ((P j * hermBasis x * P i + P i * hermBasis x * P j) * hermBasis x) =
      trace (P j * (hermBasis x * P i * hermBasis x)) +
        trace (P i * (hermBasis x * P j * hermBasis x)) := fun x => by
    rw [Matrix.add_mul, trace_add]
    simp only [Matrix.mul_assoc]
  simp_rw [e, Finset.sum_add_distrib, ← trace_sum, ← Finset.mul_sum, sum_hermBasis_conj,
    Matrix.mul_smul, Matrix.mul_one, trace_smul, hS.trace_proj, smul_eq_mul, mul_one]
  ring

/-- Eigenvalue–overlap bracket contraction: `∑_x tr(P_k E_x) dP_i[E_x] = 0`. -/
theorem sum_trace_smul_dProj (i k : Fin N) :
    ∑ x, trace (P k * hermBasis x) • dProj P μ i (hermBasis x) = 0 := by
  unfold dProj
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  simp_rw [smul_comm (trace _) (μ i - μ j)⁻¹, ← Finset.smul_sum, smul_add, Finset.sum_add_distrib]
  have e1 : ∑ x, trace (P k * hermBasis x) • (P j * hermBasis x * P i) = P j * P k * P i := by
    rw [sum_smul_sandwich, sum_trace_mul_smul_hermBasis]
  have e2 : ∑ x, trace (P k * hermBasis x) • (P i * hermBasis x * P j) = P i * P k * P j := by
    rw [sum_smul_sandwich, sum_trace_mul_smul_hermBasis]
  rw [e1, e2]
  have z1 : P j * P k * P i = 0 := by
    by_cases hk : k = i
    · subst hk; rw [hS.proj_mul_ne hji, Matrix.zero_mul]
    · rw [Matrix.mul_assoc, hS.proj_mul_ne hk, Matrix.mul_zero]
  have z2 : P i * P k * P j = 0 := by
    by_cases hk : k = i
    · subst hk; rw [hS.proj_mul_self, hS.proj_mul_ne (Ne.symm hji)]
    · rw [hS.proj_mul_ne (Ne.symm hk), Matrix.zero_mul]
  rw [z1, z2, add_zero, smul_zero]

omit hS in
/-- `∑_x A E_x B E_x C = tr(B) · A C`. -/
theorem sum_sandwich2 (A B C : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, A * hermBasis x * B * hermBasis x * C = trace B • (A * C) := by
  have : ∀ x, A * hermBasis x * B * hermBasis x * C = A * (hermBasis x * B * hermBasis x) * C :=
    fun x => by simp only [Matrix.mul_assoc]
  simp_rw [this, ← Finset.sum_mul, ← Finset.mul_sum, sum_hermBasis_conj, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul]

theorem sum_erase_smul_proj_mul {i j : Fin N} (hij : i ≠ j) (f : Fin N → ℂ) :
    ∑ l ∈ Finset.univ.erase j, f l • (P l * P i) = f i • P i := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    (fun l _ hl => by rw [hS.proj_mul_ne hl, smul_zero]), hS.proj_mul_self]

theorem sum_erase_smul_mul_proj {i j : Fin N} (hij : i ≠ j) (f : Fin N → ℂ) :
    ∑ l ∈ Finset.univ.erase j, f l • (P i * P l) = f i • P i := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    (fun l _ hl => by rw [hS.proj_mul_ne (Ne.symm hl), smul_zero]), hS.proj_mul_self]

/-- The second variation of `P_i` along `E`, as produced by differentiating `dProj i E`. -/
def d2Proj (P : Fin N → Matrix (Fin N) (Fin N) ℂ) (μ : Fin N → ℂ) (i : Fin N)
    (E : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ j ∈ Finset.univ.erase i, ((μ i - μ j)⁻¹ • (dProj P μ j E * E * P i + P j * E * dProj P μ i E +
      dProj P μ i E * E * P j + P i * E * dProj P μ j E) -
    ((μ i - μ j)⁻¹ ^ 2 * (trace (P i * E) - trace (P j * E))) • (P j * E * P i + P i * E * P j))

/-- **Overlap drift contraction**: `∑_x d²P_i[E_x, E_x] = ∑_{j ≠ i} 2 (μ_i - μ_j)⁻² (P_j - P_i)`. -/
theorem sum_d2Proj (i : Fin N) :
    ∑ x, d2Proj P μ i (hermBasis x) =
      ∑ j ∈ Finset.univ.erase i, (2 * (μ i - μ j)⁻¹ ^ 2) • (P j - P i) := by
  unfold d2Proj
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
  simp_rw [Finset.sum_add_distrib]
  -- the four first-order products
  have S1 : ∑ x, dProj P μ j (hermBasis x) * hermBasis x * P i = (μ j - μ i)⁻¹ • P i := by
    simp only [dProj, Finset.sum_mul, Matrix.smul_mul, Matrix.add_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, Finset.sum_add_distrib, sum_sandwich2, hS.trace_proj, one_smul,
      hS.proj_mul_ne hji, add_zero]
    exact hS.sum_erase_smul_proj_mul (Ne.symm hji) _
  have S2 : ∑ x, P j * hermBasis x * dProj P μ i (hermBasis x) = (μ i - μ j)⁻¹ • P j := by
    simp only [dProj, Finset.mul_sum, Matrix.mul_smul, Matrix.mul_add]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Matrix.mul_assoc, sum_sandwich2,
      hS.trace_proj, one_smul, hS.proj_mul_ne hji, zero_add]
    exact hS.sum_erase_smul_mul_proj hji _
  have S3 : ∑ x, dProj P μ i (hermBasis x) * hermBasis x * P j = (μ i - μ j)⁻¹ • P j := by
    simp only [dProj, Finset.sum_mul, Matrix.smul_mul, Matrix.add_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, Finset.sum_add_distrib, sum_sandwich2, hS.trace_proj, one_smul,
      hS.proj_mul_ne (Ne.symm hji), add_zero]
    exact hS.sum_erase_smul_proj_mul hji _
  have S4 : ∑ x, P i * hermBasis x * dProj P μ j (hermBasis x) = (μ j - μ i)⁻¹ • P i := by
    simp only [dProj, Finset.mul_sum, Matrix.mul_smul, Matrix.mul_add]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Matrix.mul_assoc, sum_sandwich2,
      hS.trace_proj, one_smul, hS.proj_mul_ne (Ne.symm hji), zero_add]
    exact hS.sum_erase_smul_mul_proj (Ne.symm hji) _
  -- the eigenvalue-variation term vanishes
  have S5 : ∑ x, ((μ i - μ j)⁻¹ ^ 2 * (trace (P i * hermBasis x) - trace (P j * hermBasis x))) •
      (P j * hermBasis x * P i + P i * hermBasis x * P j) = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, sub_smul, smul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, sum_smul_sandwich, sum_trace_mul_smul_hermBasis]
    simp [hS.proj_mul_ne hji, hS.proj_mul_ne (Ne.symm hji), hS.proj_mul_self]
  rw [S1, S2, S3, S4, S5, sub_zero]
  have hne : μ i - μ j ≠ 0 := hS.sub_ne_zero' (Ne.symm hji)
  rw [show (μ j - μ i)⁻¹ = -(μ i - μ j)⁻¹ by rw [← neg_sub, inv_neg]]
  simp only [neg_smul, smul_sub, smul_add, smul_smul]
  module

end SpecFamily

end BlockBand.SourceProcess.Stochastic.Dyson
