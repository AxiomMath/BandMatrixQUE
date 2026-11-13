module

public import BlockBand.Wegner.PassiveLogCore.SingularLog
public import BlockBand.Wegner.PassiveLogCore.PassiveLogRepair

/-!
# Full-absorber passive-log determinant ratios

This module completes the deterministic full-absorber reduction used for the
passive log bound.  For a finite complex Hermitian matrix whose
real eigenvalues avoid the reference pole zero, it identifies the squared
modulus determinant ratio with the product of the scalar singular factors
`1 + a² / λᵢ²`.  Taking the real logarithm then gives exactly the
`singularLogStatistic` normalization, including its factor `1/2`.

All pole exclusions and the absorber parameter are explicit.  There is no
probabilistic input and no limiting argument in these declarations.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped Matrix BigOperators

namespace BlockBand.Wegner.PassiveLogCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Matrix ι ι ℂ}

/-- For a complex Hermitian matrix, the squared modulus of its determinant is
the product of the squares of its real eigenvalues.  This is the denominator
reduction for the full-absorber passive-log ratio. -/
theorem normSq_det_eq_prod_eigenvalues_sq (hA : A.IsHermitian) :
    Complex.normSq A.det = ∏ i, (hA.eigenvalues i) ^ 2 := by
  rw [hA.det_eq_prod_eigenvalues, map_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [Complex.normSq_apply, pow_two]

/-- The exact full-absorber determinant ratio, at reference energy zero. The fixed-energy pole
exclusion is stated eigenvalue by eigenvalue: `λᵢ ≠ 0`. -/
theorem normSq_det_fullAbsorber_div_normSq_det_eq_prod
    (hA : A.IsHermitian) (a : ℝ)
    (hpole : ∀ i, hA.eigenvalues i ≠ 0) :
    Complex.normSq ((A + (Complex.I * a) • (1 : Matrix ι ι ℂ)).det) /
        Complex.normSq A.det =
      ∏ i, (1 + a ^ 2 / (hA.eigenvalues i) ^ 2) := by
  rw [normSq_det_add_I_smul_one_eq_prod hA, normSq_det_eq_prod_eigenvalues_sq hA]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  have hi2 : (hA.eigenvalues i) ^ 2 ≠ 0 := pow_ne_zero 2 (hpole i)
  rw [add_div, div_self hi2]

/-- Real-log form of the exact determinant ratio.  The left side is one half
of the logarithm of the squared modulus ratio; the right side is precisely the
singular finite log statistic. -/
theorem half_log_normSq_det_ratio_eq_singularLogStatistic
    (hA : A.IsHermitian) (a : ℝ)
    (hpole : ∀ i, hA.eigenvalues i ≠ 0) :
    (1 / 2 : ℝ) * Real.log
        (Complex.normSq ((A + (Complex.I * a) • (1 : Matrix ι ι ℂ)).det) /
          Complex.normSq A.det) =
      singularLogStatistic hA.eigenvalues 0 a := by
  rw [normSq_det_fullAbsorber_div_normSq_det_eq_prod hA a hpole]
  rw [Real.log_prod]
  · rw [Finset.mul_sum]
    unfold singularLogStatistic singularLogTerm
    simp only [sub_zero]
  · intro i _hi
    have hi2 : 0 < (hA.eigenvalues i) ^ 2 := sq_pos_of_ne_zero (hpole i)
    have hq : 0 ≤ a ^ 2 / (hA.eigenvalues i) ^ 2 :=
      div_nonneg (sq_nonneg a) hi2.le
    linarith

end BlockBand.Wegner.PassiveLogCore
