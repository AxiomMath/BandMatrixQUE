module

public import Mathlib
public import BlockBand.Wegner.PassiveLogCore.AbsorberRegulatorLimit
public import BlockBand.Internal.Contracts.Inputs

/-!
# Deterministic partial-absorber log comparison

For Hermitian `A` with `A - e` invertible, `0 ⪯ Q ⪯ I` and `a ≥ 0`, the partial-absorber log
`B_a(A; Q) = log |det(A - e + iaQ)/det(A - e)|` satisfies `0 ≤ B_a(A; Q) ≤ B_a(A; I)`, and
`B_a(A; I) = ½ Σ_λ log(1 + a²/(λ - e)²)` is the singular log statistic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open Matrix
open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A Hermitian invertible matrix plus `i a Q` with `Q ⪰ 0`, `a ≥ 0` stays invertible. -/
theorem det_add_I_smul_posSemidef_ne_zero {B Q : Matrix ι ι ℂ} (hB : B.IsHermitian)
    (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 ≤ a) (hdet : B.det ≠ 0) :
    (B + Complex.I • (a • Q)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hsplit : (B + Complex.I • (a • Q)) *ᵥ v =
      B *ᵥ v + (Complex.I * (a : ℂ)) • (Q *ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    congr 1
    ext k
    simp [Complex.real_smul]
    ring
  have hquad : star v ⬝ᵥ (B *ᵥ v) + (Complex.I * (a : ℂ)) * (star v ⬝ᵥ (Q *ᵥ v)) = 0 := by
    have h := congrArg (fun w => star v ⬝ᵥ w) hBv
    simp only [hsplit, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h
    exact h
  have hBim : (star v ⬝ᵥ (B *ᵥ v)).im = 0 :=
    Complex.conj_eq_iff_im.mp (hB.star_dotProduct_mulVec_comm v v)
  have hQnn : 0 ≤ star v ⬝ᵥ (Q *ᵥ v) := hQ.dotProduct_mulVec_nonneg v
  have hQim : (star v ⬝ᵥ (Q *ᵥ v)).im = 0 := (Complex.nonneg_iff.mp hQnn).2.symm
  have him := congrArg Complex.im hquad
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, hBim, hQim, Complex.zero_im] at him
  have hQv : Q *ᵥ v = 0 := by
    rcases ha.lt_or_eq with hpos | hzero
    · have hre : (star v ⬝ᵥ (Q *ᵥ v)).re = 0 := by
        have : a * (star v ⬝ᵥ (Q *ᵥ v)).re = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hpos.ne'
        · exact h
      exact hQ.dotProduct_mulVec_zero_iff.mp (Complex.ext hre hQim)
    · have hB0 : B *ᵥ v = 0 := by
        rw [hsplit, ← hzero] at hBv
        simpa using hBv
      exact absurd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hB0⟩) hdet
  have hB0 : B *ᵥ v = 0 := by
    rw [hsplit, hQv, smul_zero, add_zero] at hBv
    exact hBv
  exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hB0⟩)

/-- `log ‖x / y‖ = ½ log |x|² - ½ log |y|²` for nonzero complex numbers. -/
theorem log_norm_div_eq (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log ‖x / y‖ =
      (1 / 2 : ℝ) * Real.log (Complex.normSq x) - (1 / 2 : ℝ) * Real.log (Complex.normSq y) := by
  rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy),
    Complex.norm_def, Complex.norm_def,
    Real.log_sqrt (Complex.normSq_nonneg x), Real.log_sqrt (Complex.normSq_nonneg y)]
  ring

omit [Fintype ι] in
/-- The shifted matrix `A - e`. -/
theorem isHermitian_sub_smul_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (e : ℝ) :
    (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian :=
  hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))

/-- The contract's `B_a(X;Q)` is the passive increment at `X - e`. -/
theorem passiveLog_eq_increment (A Q : Matrix ι ι ℂ) (a e : ℝ)
    (h0 : (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0)
    (hQ : (A - (e : ℂ) • (1 : Matrix ι ι ℂ) + Complex.I • (a • Q)).det ≠ 0) :
    Internal.Contracts.Inputs.passiveLog A Q a e =
      PassiveLogCore.passiveLogIncrement (A - (e : ℂ) • (1 : Matrix ι ι ℂ)) Q a := by
  have hs : ((a : ℂ) * Complex.I) • Q = Complex.I • (a • Q) := by
    ext i j
    simp [Complex.real_smul]
    ring
  unfold Internal.Contracts.Inputs.passiveLog PassiveLogCore.passiveLogIncrement
  rw [hs, log_norm_div_eq _ _ hQ h0]

/-- The full-absorber log is the singular log statistic over the spectrum. -/
theorem passiveLog_one_eq_singularLogStatistic {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (a e : ℝ) (h0 : (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0) :
    Internal.Contracts.Inputs.passiveLog A 1 a e =
      Internal.Contracts.Inputs.singularLogStatistic A a e := by
  have hz (z : ℂ) : A - (e : ℂ) • (1 : Matrix ι ι ℂ) + ((a : ℂ) * Complex.I) • 1 =
      A + ((-(e : ℂ)) + (a : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) := by
    rw [add_smul, neg_smul, ← add_assoc, sub_eq_add_neg]
  have hz0 : A - (e : ℂ) • (1 : Matrix ι ι ℂ) = A + (-(e : ℂ)) • (1 : Matrix ι ι ℂ) := by
    rw [neg_smul, sub_eq_add_neg]
  have hden := PassiveLogCore.det_add_smul_one_eq_prod_eigenvalues hA (-(e : ℂ))
  have hnum := PassiveLogCore.det_add_smul_one_eq_prod_eigenvalues hA ((-(e : ℂ)) + (a : ℂ) * Complex.I)
  have hpole : ∀ i, hA.eigenvalues i - e ≠ 0 := by
    intro i hi
    apply h0
    rw [hz0, hden]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← sub_eq_add_neg]; exact_mod_cast hi)
  unfold Internal.Contracts.Inputs.passiveLog Internal.Contracts.Inputs.singularLogStatistic
    Internal.Contracts.Inputs.spectralSum
  rw [hz 0, hz0, hnum, hden, ← Finset.prod_div_distrib, Complex.norm_prod,
    Real.log_prod (fun i _ => ?_)]
  · rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, ← Finset.sum_eq_multiset_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi := hpole i
    simp only [Function.comp_apply]
    have hx : ((hA.eigenvalues i : ℂ) + -(e : ℂ)) = ((hA.eigenvalues i - e : ℝ) : ℂ) := by
      push_cast; ring
    have hy : ((hA.eigenvalues i : ℂ) + (-(e : ℂ) + (a : ℂ) * Complex.I)) =
        ((hA.eigenvalues i - e : ℝ) : ℂ) + (a : ℂ) * Complex.I := by
      push_cast; ring
    rw [hx, hy, norm_div, Real.log_div, Complex.norm_real, Real.norm_eq_abs]
    · rw [show ‖((hA.eigenvalues i - e : ℝ) : ℂ) + (a : ℂ) * Complex.I‖ =
          Real.sqrt ((hA.eigenvalues i - e) ^ 2 + a ^ 2) by
        rw [Complex.norm_def, Complex.normSq_add_mul_I]]
      have hY : 0 < (hA.eigenvalues i - e) ^ 2 := by positivity
      show _ = (1 / 2 : ℝ) * Real.log (1 + a ^ 2 / (hA.eigenvalues i - e) ^ 2)
      rw [Real.log_sqrt (by positivity), ← Real.sqrt_sq_eq_abs, Real.log_sqrt hY.le,
        show 1 + a ^ 2 / (hA.eigenvalues i - e) ^ 2 =
          ((hA.eigenvalues i - e) ^ 2 + a ^ 2) / (hA.eigenvalues i - e) ^ 2 by field_simp,
        Real.log_div (by positivity) hY.ne']
      ring
    · exact norm_ne_zero_iff.mpr (by
        intro h
        have := congrArg Complex.re h
        simp at this
        exact hi this)
    · exact norm_ne_zero_iff.mpr (by exact_mod_cast hi)
  · apply norm_ne_zero_iff.mpr
    apply div_ne_zero
    · intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact hpole i (by linarith)
    · intro h
      have := congrArg Complex.re h
      simp at this
      exact hpole i (by linarith)

/-- Clause 2 of `PassiveLog`, for every finite index type: `0 ≤ B_a(A; Q) ≤ B_a(A; I)` and
`B_a(A; I)` is the singular log statistic. -/
theorem passiveLog_partial_holds :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A Q : Matrix ι ι ℂ), A.IsHermitian →
      Q.PosSemidef → (1 - Q).PosSemidef → ∀ (e a : ℝ), 0 ≤ a →
        (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0 →
          0 ≤ Internal.Contracts.Inputs.passiveLog A Q a e ∧
            Internal.Contracts.Inputs.passiveLog A Q a e ≤
              Internal.Contracts.Inputs.passiveLog A 1 a e ∧
            Internal.Contracts.Inputs.passiveLog A 1 a e =
              Internal.Contracts.Inputs.singularLogStatistic A a e := by
  intro ι _ _ A Q hA hQ hIQ e a ha h0
  have hB := isHermitian_sub_smul_one hA e
  have hBQ := det_add_I_smul_posSemidef_ne_zero hB hQ ha h0
  have hBI := det_add_I_smul_posSemidef_ne_zero hB Matrix.PosSemidef.one ha h0
  have hmain := PassiveLogCore.passiveLogIncrement_nonneg_le_full _ Q hB hQ hIQ ha h0 hBQ hBI
  rw [passiveLog_eq_increment A Q a e h0 hBQ, passiveLog_eq_increment A 1 a e h0 hBI]
  exact ⟨hmain.1, hmain.2,
    (passiveLog_eq_increment A 1 a e h0 hBI).symm.trans
      (passiveLog_one_eq_singularLogStatistic hA a e h0)⟩

end BlockBand.Wegner
