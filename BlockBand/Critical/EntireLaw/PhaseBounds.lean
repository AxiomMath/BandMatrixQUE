module

public import BlockBand.Critical.EntireLaw.GaussianPhase
public import BlockBand.Critical.EntireLaw.DeterminantBound

/-!
# The entire law: deterministic bounds on the Gaussian phase

For Hermitian `A` with eigenvalues `λ_k`, `hermitianPhase hA t = Π_k (1 + i t λ_k)⁻¹`
(`= E_g exp(-i t g^*Ag)`, `integral_circularVectorLaw_hermitian_phase`):

* `sum_sq_eigenvalues`: `Σ_k λ_k² = ‖A‖²_HS` (`hsSq`);
* `normSq_hermitianPhase_mul_le`: `‖Π_k (1 + i t λ_k)⁻¹‖² (1 + t²‖A‖²_HS) ≤ 1`;
* `norm_hermitianPhase_sub_exp_trace_le`: `‖Π_k (1 + i t λ_k)⁻¹ - e^{-it Tr A}‖ ≤ t²‖A‖²_HS`
  when `t²‖A‖²_HS ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory ProbabilityTheory Matrix Filter
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

/-!
## 1. Deterministic bounds on the Gaussian phase of a Hermitian matrix
-/

section Deterministic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖A‖²_HS = Σ_{i,j} |A_ij|²`. -/
def hsSq (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

omit [DecidableEq ι] in
theorem hsSq_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hsSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `Σ_k λ_k² = ‖A‖²_HS` for Hermitian `A`. -/
theorem sum_sq_eigenvalues {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ∑ k, hA.eigenvalues k ^ 2 = hsSq A := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ)
  have hsU : star U * U = 1 := Unitary.coe_star_mul_self _
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hAeq : A = U * D * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have h1 : (Aᴴ * A).trace = ((hsSq A : ℝ) : ℂ) := trace_conjTranspose_mul_self_eq A
  have h2 : (Aᴴ * A).trace = (D * D).trace := by
    rw [show Aᴴ = A from hA, hAeq]
    have : U * D * star U * (U * D * star U) = U * (D * D) * star U := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hsU, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hsU, Matrix.one_mul]
  have h3 : (D * D).trace = ((∑ k, hA.eigenvalues k ^ 2 : ℝ) : ℂ) := by
    simp only [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_apply]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sq]
  have := h1.symm.trans (h2.trans h3)
  exact_mod_cast this.symm

/-- The Gaussian phase `Π_k (1 + i t λ_k)⁻¹` of a Hermitian matrix. -/
def hermitianPhase {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) : ℂ :=
  ∏ k, (1 + Complex.I * ((t * hA.eigenvalues k : ℝ) : ℂ))⁻¹

theorem normSq_one_add_I_mul (u : ℝ) : ‖1 + Complex.I * (u : ℂ)‖ ^ 2 = 1 + u ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

theorem norm_inv_one_add_I_mul_le (u : ℝ) : ‖(1 + Complex.I * (u : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  refine inv_le_one_of_one_le₀ ?_
  have h := normSq_one_add_I_mul u
  nlinarith [norm_nonneg (1 + Complex.I * (u : ℂ)), sq_nonneg u]

theorem one_add_sum_le_prod_one_add {κ : Type*} (s : Finset κ) {a : κ → ℝ}
    (ha : ∀ k ∈ s, 0 ≤ a k) : 1 + ∑ k ∈ s, a k ≤ ∏ k ∈ s, (1 + a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hai := ha i (Finset.mem_insert_self i s)
    have hs := ih fun k hk => ha k (Finset.mem_insert_of_mem hk)
    have hS : 0 ≤ ∑ k ∈ s, a k := Finset.sum_nonneg fun k hk => ha k (Finset.mem_insert_of_mem hk)
    nlinarith

/-- `‖Π (1 + i t λ_k)⁻¹‖² (1 + t² ‖A‖²_HS) ≤ 1`. -/
theorem normSq_hermitianPhase_mul_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    ‖hermitianPhase hA t‖ ^ 2 * (1 + t ^ 2 * hsSq A) ≤ 1 := by
  have hprod : ‖hermitianPhase hA t‖ ^ 2 * ∏ k, (1 + (t * hA.eigenvalues k) ^ 2) = 1 := by
    unfold hermitianPhase
    rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [norm_inv, inv_pow, normSq_one_add_I_mul]
    exact inv_mul_cancel₀ (by positivity)
  have hle : 1 + t ^ 2 * hsSq A ≤ ∏ k, (1 + (t * hA.eigenvalues k) ^ 2) := by
    rw [← sum_sq_eigenvalues hA, Finset.mul_sum]
    convert one_add_sum_le_prod_one_add Finset.univ (a := fun k => (t * hA.eigenvalues k) ^ 2)
      (fun k _ => sq_nonneg _) using 2
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  calc ‖hermitianPhase hA t‖ ^ 2 * (1 + t ^ 2 * hsSq A)
      ≤ ‖hermitianPhase hA t‖ ^ 2 * ∏ k, (1 + (t * hA.eigenvalues k) ^ 2) :=
        mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    _ = 1 := hprod

theorem norm_hermitianPhase_le_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    ‖hermitianPhase hA t‖ ≤ 1 := by
  have h := normSq_hermitianPhase_mul_le hA t
  have h0 : 0 ≤ t ^ 2 * hsSq A := mul_nonneg (sq_nonneg _) (hsSq_nonneg A)
  nlinarith [norm_nonneg (hermitianPhase hA t), sq_nonneg (‖hermitianPhase hA t‖)]

/-- `‖Π a_k - Π b_k‖ ≤ Σ ‖a_k - b_k‖` when all factors lie in the closed unit disk. -/
theorem norm_prod_sub_prod_le {κ : Type*} (s : Finset κ) {a b : κ → ℂ}
    (ha : ∀ k ∈ s, ‖a k‖ ≤ 1) (hb : ∀ k ∈ s, ‖b k‖ ≤ 1) :
    ‖∏ k ∈ s, a k - ∏ k ∈ s, b k‖ ≤ ∑ k ∈ s, ‖a k - b k‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hai := ha i (Finset.mem_insert_self i s)
    have hs := ih (fun k hk => ha k (Finset.mem_insert_of_mem hk))
      (fun k hk => hb k (Finset.mem_insert_of_mem hk))
    have hQ : ‖∏ k ∈ s, b k‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        fun k hk => hb k (Finset.mem_insert_of_mem hk)
    have heq : a i * ∏ k ∈ s, a k - b i * ∏ k ∈ s, b k =
        a i * (∏ k ∈ s, a k - ∏ k ∈ s, b k) + (a i - b i) * ∏ k ∈ s, b k := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖a i‖ * ‖∏ k ∈ s, a k - ∏ k ∈ s, b k‖ ≤ ∑ k ∈ s, ‖a k - b k‖ :=
      (mul_le_of_le_one_left (norm_nonneg _) hai).trans hs
    have h2 : ‖a i - b i‖ * ‖∏ k ∈ s, b k‖ ≤ ‖a i - b i‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hQ
    linarith

/-- One factor: `‖(1 + iu)⁻¹ - e^{-iu}‖ ≤ u²` for `|u| ≤ 1`. -/
theorem norm_inv_one_add_I_mul_sub_exp_le {u : ℝ} (hu : |u| ≤ 1) :
    ‖(1 + Complex.I * (u : ℂ))⁻¹ - Complex.exp (-(Complex.I * (u : ℂ)))‖ ≤ u ^ 2 := by
  have hne : (1 + Complex.I * (u : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hexp : Complex.exp (-(Complex.I * (u : ℂ))) * Complex.exp (Complex.I * (u : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have heq : (1 + Complex.I * (u : ℂ))⁻¹ - Complex.exp (-(Complex.I * (u : ℂ))) =
      (1 + Complex.I * (u : ℂ))⁻¹ * Complex.exp (-(Complex.I * (u : ℂ))) *
        (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ)) := by
    have h : (1 + Complex.I * (u : ℂ))⁻¹ * Complex.exp (-(Complex.I * (u : ℂ))) *
        (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ)) =
        (1 + Complex.I * (u : ℂ))⁻¹ * (Complex.exp (-(Complex.I * (u : ℂ))) *
          Complex.exp (Complex.I * (u : ℂ))) -
        (1 + Complex.I * (u : ℂ))⁻¹ * (1 + Complex.I * (u : ℂ)) *
          Complex.exp (-(Complex.I * (u : ℂ))) := by ring
    rw [h, hexp, inv_mul_cancel₀ hne]
    ring
  rw [heq, norm_mul, norm_mul]
  have h1 := norm_inv_one_add_I_mul_le u
  have h2 : ‖Complex.exp (-(Complex.I * (u : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hiu : ‖Complex.I * (u : ℂ)‖ = |u| := by simp
  have h3 := Complex.norm_exp_sub_one_sub_id_le (x := Complex.I * (u : ℂ)) (by rw [hiu]; exact hu)
  rw [hiu, sq_abs] at h3
  rw [h2, mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans h3

/-- **Small-source expansion**: `‖Π (1 + i t λ_k)⁻¹ - e^{-it Tr A}‖ ≤ t² ‖A‖²_HS` when
`t² ‖A‖²_HS ≤ 1`. -/
theorem norm_hermitianPhase_sub_exp_trace_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {t : ℝ}
    (ht : t ^ 2 * hsSq A ≤ 1) :
    ‖hermitianPhase hA t - Complex.exp (-(Complex.I * ((t : ℂ) * A.trace)))‖ ≤ t ^ 2 * hsSq A := by
  have hlam : ∀ k, |t * hA.eigenvalues k| ≤ 1 := by
    intro k
    have hk : (t * hA.eigenvalues k) ^ 2 ≤ t ^ 2 * hsSq A := by
      rw [← sum_sq_eigenvalues hA, mul_pow]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun k => hA.eigenvalues k ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ k)) (sq_nonneg _)
    rw [← sq_le_one_iff_abs_le_one]
    exact hk.trans ht
  have htr : Complex.exp (-(Complex.I * ((t : ℂ) * A.trace))) =
      ∏ k, Complex.exp (-(Complex.I * ((t * hA.eigenvalues k : ℝ) : ℂ))) := by
    rw [← Complex.exp_sum, hA.trace_eq_sum_eigenvalues, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rfl
  rw [htr, hermitianPhase]
  refine (norm_prod_sub_prod_le _ (fun k _ => norm_inv_one_add_I_mul_le _)
    (fun k _ => by rw [Complex.norm_exp]; simp)).trans ?_
  refine (Finset.sum_le_sum fun k _ => norm_inv_one_add_I_mul_sub_exp_le (hlam k)).trans
    (le_of_eq ?_)
  rw [← sum_sq_eigenvalues hA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Deterministic

end BlockBand.Critical.EntireLaw
