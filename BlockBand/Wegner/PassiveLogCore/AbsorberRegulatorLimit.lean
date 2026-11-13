module

public import BlockBand.Wegner.PassiveLogCore.AbsorberLogPath
public import BlockBand.Wegner.PassiveLogCore.PassiveLogRatio
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.OrderClosed

/-!
# Removing the positive regulator from passive logarithmic determinants

This module proves the finite-dimensional regulator-removal step for the
passive log bound.  All limiting statements carry explicit nonvanishing
hypotheses at regulator zero.  Continuity of the determinant is obtained from
the formal determinant-line polynomial.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix Polynomial Set Filter
open scoped ComplexOrder Matrix Topology

namespace BlockBand.Wegner.PassiveLogCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unregulated passive-log increment in absorber direction `Q`. -/
def passiveLogIncrement
    (A Q : Matrix ι ι ℂ) (a : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
      (Complex.normSq (A + Complex.I • (a • Q)).det) -
    (1 / 2 : ℝ) * Real.log (Complex.normSq A.det)

/-- Continuity at zero of a half-log determinant under a scalar imaginary
regulator, assuming the limiting determinant is nonzero. -/
theorem tendsto_half_log_normSq_det_add_I_regulator
    (M : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    Tendsto
      (fun η : ℝ => (1 / 2 : ℝ) * Real.log
        (Complex.normSq (M + Complex.I •
          (η • (1 : Matrix ι ι ℂ))).det))
      (𝓝 0)
      (𝓝 ((1 / 2 : ℝ) * Real.log (Complex.normSq M.det))) := by
  let p := detLinePoly M (Complex.I • (1 : Matrix ι ι ℂ))
  have hp : Continuous (fun η : ℝ => p.eval (η : ℂ)) :=
    p.continuous.comp Complex.continuous_ofReal
  have hdet : Tendsto
      (fun η : ℝ => (M + Complex.I •
        (η • (1 : Matrix ι ι ℂ))).det)
      (𝓝 0) (𝓝 M.det) := by
    have hp0 : Tendsto (fun η : ℝ => p.eval (η : ℂ))
        (𝓝 0) (𝓝 (p.eval (0 : ℂ))) :=
      hp.continuousAt
    convert hp0 using 1
    · funext η
      rw [eval_detLinePoly]
      congr 1
      ext i j
      simp
      ring
    · simp [p, eval_detLinePoly]
  have hnorm : Tendsto
      (fun η : ℝ => Complex.normSq
        (M + Complex.I • (η • (1 : Matrix ι ι ℂ))).det)
      (𝓝 0) (𝓝 (Complex.normSq M.det)) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp hdet
  exact (Real.continuousAt_log
    (Complex.normSq_pos.mpr hM).ne').tendsto.const_mul (1 / 2 : ℝ) |>.comp hnorm

/-- Regulated passive-log increments converge to the unregulated increment.
The two explicit hypotheses exclude the determinant poles at the base matrix
and at the absorbed endpoint. -/
theorem tendsto_regulatedPassiveLogIncrement
    (A Q : Matrix ι ι ℂ) (a : ℝ)
    (hA0 : A.det ≠ 0)
    (hAa : (A + Complex.I • (a • Q)).det ≠ 0) :
    Tendsto (fun η : ℝ => regulatedPassiveLogIncrement A Q η a)
      (𝓝 0) (𝓝 (passiveLogIncrement A Q a)) := by
  have ha := tendsto_half_log_normSq_det_add_I_regulator
    (A + Complex.I • (a • Q)) hAa
  have h0 := tendsto_half_log_normSq_det_add_I_regulator A hA0
  have hend (η : ℝ) :
      regulatedAbsorberMatrix A 0 Q η a =
        (A + Complex.I • (a • Q)) +
          Complex.I • (η • (1 : Matrix ι ι ℂ)) := by
    ext i j
    simp [regulatedAbsorberMatrix]
    ring
  have hbase (η : ℝ) :
      regulatedAbsorberMatrix A 0 Q η 0 =
        A + Complex.I • (η • (1 : Matrix ι ι ℂ)) := by
    ext i j
    simp [regulatedAbsorberMatrix]
  simpa only [regulatedPassiveLogIncrement, regulatedAbsorberLogPath,
    passiveLogIncrement, hend, hbase] using ha.sub h0

/-- The full-absorber unregulated increment equals the singular-log statistic
when the real eigenvalues avoid the reference pole zero. -/
theorem passiveLogIncrement_one_eq_singularLogStatistic
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (a : ℝ)
    (hpole : ∀ i, hA.eigenvalues i ≠ 0) :
    passiveLogIncrement A (1 : Matrix ι ι ℂ) a =
      singularLogStatistic hA.eigenvalues 0 a := by
  have hdetA : A.det ≠ 0 := by
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (hpole i)
  have hnum : Complex.normSq
      ((A + (Complex.I * a) • (1 : Matrix ι ι ℂ)).det) ≠ 0 := by
    by_cases ha : a = 0
    · simpa [ha] using (Complex.normSq_pos.mpr hdetA).ne'
    · exact (Complex.normSq_pos.mpr
        (det_add_I_smul_one_ne_zero hA ha)).ne'
  have hden : Complex.normSq A.det ≠ 0 :=
    (Complex.normSq_pos.mpr hdetA).ne'
  rw [← half_log_normSq_det_ratio_eq_singularLogStatistic hA a hpole]
  rw [Real.log_div hnum hden]
  unfold passiveLogIncrement
  have hmatrix :
      A + Complex.I • (a • (1 : Matrix ι ι ℂ)) =
        A + (Complex.I * a) • (1 : Matrix ι ι ℂ) := by
    ext i j
    simp
    ring
  rw [hmatrix]
  ring

/-- The regulated full-absorber increment converges directly to the
singular-log statistic.  Thus the exact full-absorber identity is compatible
with removal of the positive regulator, under the same explicit exclusion of
zero eigenvalues. -/
theorem tendsto_regulatedPassiveLogIncrement_one
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (a : ℝ)
    (hpole : ∀ i, hA.eigenvalues i ≠ 0) :
    Tendsto
      (fun η : ℝ =>
        regulatedPassiveLogIncrement A (1 : Matrix ι ι ℂ) η a)
      (𝓝 0) (𝓝 (singularLogStatistic hA.eigenvalues 0 a)) := by
  have hdetA : A.det ≠ 0 := by
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (hpole i)
  have hmatrix :
      A + Complex.I • (a • (1 : Matrix ι ι ℂ)) =
        A + (Complex.I * a) • (1 : Matrix ι ι ℂ) := by
    ext i j
    simp
    ring
  have hfull :
      (A + Complex.I • (a • (1 : Matrix ι ι ℂ))).det ≠ 0 := by
    rw [hmatrix]
    by_cases ha : a = 0
    · simpa [ha] using hdetA
    · exact det_add_I_smul_one_ne_zero hA ha
  rw [← passiveLogIncrement_one_eq_singularLogStatistic hA a hpole]
  exact tendsto_regulatedPassiveLogIncrement A (1 : Matrix ι ι ℂ) a
    hdetA hfull

/-- The regulator-free `0 ≤ Q ≤ I` comparison.  Besides the Hermitian and
Loewner hypotheses, the determinants of the base, partial-absorber, and full-
absorber endpoints are required to be nonzero. -/
theorem passiveLogIncrement_nonneg_le_full
    (A Q : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hIQ : ((1 : Matrix ι ι ℂ) - Q).PosSemidef)
    {a : ℝ} (ha : 0 ≤ a)
    (hA0 : A.det ≠ 0)
    (hAQ : (A + Complex.I • (a • Q)).det ≠ 0)
    (hAI : (A + Complex.I •
      (a • (1 : Matrix ι ι ℂ))).det ≠ 0) :
    0 ≤ passiveLogIncrement A Q a ∧
      passiveLogIncrement A Q a ≤
        passiveLogIncrement A (1 : Matrix ι ι ℂ) a := by
  let l := 𝓝[>] (0 : ℝ)
  have hlimQ : Tendsto (fun η : ℝ => regulatedPassiveLogIncrement A Q η a)
      l (𝓝 (passiveLogIncrement A Q a)) :=
    (tendsto_regulatedPassiveLogIncrement A Q a hA0 hAQ).mono_left inf_le_left
  have hlimI : Tendsto
      (fun η : ℝ => regulatedPassiveLogIncrement A (1 : Matrix ι ι ℂ) η a)
      l (𝓝 (passiveLogIncrement A (1 : Matrix ι ι ℂ) a)) :=
    (tendsto_regulatedPassiveLogIncrement A (1 : Matrix ι ι ℂ) a hA0 hAI).mono_left
      inf_le_left
  have hev : ∀ᶠ η in l,
      0 ≤ regulatedPassiveLogIncrement A Q η a ∧
        regulatedPassiveLogIncrement A Q η a ≤
          regulatedPassiveLogIncrement A (1 : Matrix ι ι ℂ) η a := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact regulatedPassiveLogIncrement_nonneg_le_full A Q hA hQ hIQ hη ha
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hlimQ (hev.mono fun _ h => h.1)
  · exact le_of_tendsto_of_tendsto hlimQ hlimI (hev.mono fun _ h => h.2)

/-- Regulator-free comparison directly against the singular-log statistic.
The zero-eigenvalue exclusion supplies nonvanishing of the base and full
absorber determinants; nonvanishing at the partial-absorber endpoint is an
explicit determinant hypothesis (`hAQ`). -/
theorem passiveLogIncrement_nonneg_le_singularLogStatistic
    (A Q : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    (hIQ : ((1 : Matrix ι ι ℂ) - Q).PosSemidef)
    {a : ℝ} (ha : 0 ≤ a)
    (hpole : ∀ i, hA.eigenvalues i ≠ 0)
    (hAQ : (A + Complex.I • (a • Q)).det ≠ 0) :
    0 ≤ passiveLogIncrement A Q a ∧
      passiveLogIncrement A Q a ≤
        singularLogStatistic hA.eigenvalues 0 a := by
  have hdetA : A.det ≠ 0 := by
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (hpole i)
  have hmatrix :
      A + Complex.I • (a • (1 : Matrix ι ι ℂ)) =
        A + (Complex.I * a) • (1 : Matrix ι ι ℂ) := by
    ext i j
    simp
    ring
  have hfull :
      (A + Complex.I • (a • (1 : Matrix ι ι ℂ))).det ≠ 0 := by
    rw [hmatrix]
    by_cases ha0 : a = 0
    · simpa [ha0] using hdetA
    · exact det_add_I_smul_one_ne_zero hA ha0
  rw [← passiveLogIncrement_one_eq_singularLogStatistic hA a hpole]
  exact passiveLogIncrement_nonneg_le_full A Q hA hQ hIQ ha hdetA hAQ hfull

end BlockBand.Wegner.PassiveLogCore
