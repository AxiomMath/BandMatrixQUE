module

public import BlockBand.Internal.Contracts.CriticalEntire
public import BlockBand.Critical.EntireLaw.DeterminantBound

/-!
# The entire law: growth bound of the finite determinant

`norm_finiteEntireDeterminant_le`: for every `H` and `z ∈ ℂ^m`,
`|D_W(z)| ≤ exp{Σ_a |z_a| |W⁻² Tr(R Q_a)| + ½ (Σ_a |z_a| ‖Q_a‖)² ‖W⁻² R‖²_HS}`, `R = (H - E)⁻¹`,
from the determinant bound `|det(I + B)| ≤ exp{Re Tr B + ½‖B‖²_HS}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open Matrix
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire

variable {p : Parameters}

/-- The source of the pencil, `W⁻² Σ_a z_a Q_a`. -/
def entireSource (p : Parameters) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (z : Fin m → ℂ) :
    p.SiteMatrix :=
  BlockBand.Critical.widthSourceScale p.W • ∑ a, z a • p.profileSourceMatrix (Q a)

/-- One-profile trace `W⁻² Tr(R Q_a)`, `R = (H - E)⁻¹`. -/
def profileTrace (p : Parameters) (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (H : p.SiteMatrix)
    (a : Fin m) : ℂ :=
  ((H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹ *
    (BlockBand.Critical.widthSourceScale p.W • p.profileSourceMatrix (Q a))).trace

/-- `‖W⁻² R‖²_HS`, `R = (H - E)⁻¹`. -/
def scaledResolventHS (p : Parameters) (E : ℝ) (H : p.SiteMatrix) : ℝ :=
  ∑ i, ∑ j, ‖(BlockBand.Critical.widthSourceScale p.W • (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹) i j‖ ^ 2

theorem entireSource_eq_diagonal {m : ℕ} (Q : Fin m → C(Torus, ℝ)) (z : Fin m → ℂ) :
    entireSource p Q z = Matrix.diagonal fun x =>
      BlockBand.Critical.widthSourceScale p.W * ∑ a, z a * (Q a (p.ringProfilePoint x.1) : ℂ) := by
  ext x x'
  by_cases hxx : x = x'
  · subst hxx
    simp [entireSource, Matrix.sum_apply, Parameters.profileSourceMatrix]
  · simp [entireSource, Matrix.sum_apply, Parameters.profileSourceMatrix,
      Matrix.diagonal_apply_ne _ hxx]

/-- **Growth bound of `D_W`**:
`|D_W(z)| ≤ exp{Σ_a |z_a| |W⁻² Tr(R Q_a)| + ½ (Σ_a |z_a| ‖Q_a‖)² ‖W⁻² R‖²_HS}`. -/
theorem norm_finiteEntireDeterminant_le (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ))
    (H : p.SiteMatrix) (z : Fin m → ℂ) :
    ‖finiteEntireDeterminant p E Q H z‖ ≤
      Real.exp (∑ a, ‖z a‖ * ‖profileTrace p E Q H a‖ +
        2⁻¹ * (∑ a, ‖z a‖ * ‖Q a‖) ^ 2 * scaledResolventHS p E H) := by
  set A := H - (E : ℂ) • (1 : p.SiteMatrix) with hAdef
  by_cases hA : A.det = 0
  · simp only [finiteEntireDeterminant, EntireFunction.coe_ofDifferentiable, ← hAdef, hA,
      _root_.inv_zero, mul_zero, norm_zero]
    exact (Real.exp_pos _).le
  set s := BlockBand.Critical.widthSourceScale p.W
  set B := A⁻¹ * entireSource p Q z with hB
  have hval : finiteEntireDeterminant p E Q H z = (1 + B).det := by
    simp only [finiteEntireDeterminant, EntireFunction.coe_ofDifferentiable,
      BlockBand.Critical.finiteCharacteristicDeterminant,
      BlockBand.Critical.finiteCharacteristicPencil, ← hAdef]
    have h : A + s • ∑ a, z a • p.profileSourceMatrix (Q a) = A * (1 + B) := by
      rw [Matrix.mul_add, Matrix.mul_one, hB, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]
      rfl
    rw [h, Matrix.det_mul, mul_comm A.det, mul_assoc, mul_inv_cancel₀ hA, mul_one]
  rw [hval]
  refine (norm_det_one_add_le B).trans (Real.exp_le_exp.mpr (add_le_add ?_ ?_))
  · have htr : B.trace = ∑ a, z a * profileTrace p E Q H a := by
      simp only [hB, entireSource, profileTrace, Matrix.mul_smul, Matrix.mul_sum,
        Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul, ← hAdef]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [htr]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
    simp only [norm_mul]
  · set c := ∑ a, ‖z a‖ * ‖Q a‖
    have hentry : ∀ i j, ‖B i j‖ ^ 2 ≤ c ^ 2 * ‖(s • A⁻¹) i j‖ ^ 2 := by
      intro i j
      have hBij : B i j = (s • A⁻¹) i j *
          ∑ a, z a * (Q a (p.ringProfilePoint j.1) : ℂ) := by
        rw [hB, entireSource_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
        ring
      have hsum : ‖∑ a, z a * (Q a (p.ringProfilePoint j.1) : ℂ)‖ ≤ c := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left ((Q a).norm_coe_le_norm _) (norm_nonneg _)
      rw [hBij, norm_mul, mul_pow, mul_comm (c ^ 2)]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hsum 2) (sq_nonneg _)
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hentry i j
    simp only [← Finset.mul_sum] at h
    unfold scaledResolventHS
    rw [← hAdef, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by norm_num)

end BlockBand.Critical.EntireLaw
