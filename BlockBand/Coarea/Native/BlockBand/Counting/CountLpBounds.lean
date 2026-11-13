module

public import BlockBand.Coarea.Native.BlockBand.Counting.ScaledMomentBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Lp bounds for rescaled eigenvalue counts

This module converts the PSSS ordinary-moment estimates into the real-valued
`L^r` seminorm bounds used in the counting argument.  The random variable is
the nonnegative real cast of the multiplicity-counted eigenvalue count.  All
measurability and `MemLp` obligations are discharged from the measurable block
GUE entries and the factorial-integrability field of `PSSSInput`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped BigOperators ENNReal NNReal

universe u

/-- The deterministically deformed block-GUE matrix is measurable as a map
into the exact Hermitian subtype. -/
theorem measurable_blockGUE_deformed
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) :
    Measurable (fun ω => BlockGUE.deformed M A₀ ω) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact measurable_const.add (M.measurable_entry x y)

/-- A closed-interval block-GUE count, cast to a nonnegative real random
variable, is measurable. -/
theorem measurable_blockGUE_intervalCount_real
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (a b : ℝ) :
    Measurable (fun ω =>
      (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)) := by
  exact measurable_from_nat.comp
    ((measurable_eigenCount_Icc a b).comp (measurable_blockGUE_deformed M A₀))

/-- Every ordinary integer power of a PSSS interval count is integrable.  This
is the integrability counterpart of the exact Stirling expansion; no moment
bound is needed beyond the factorial-integrability contract. -/
theorem psss_countPower_integrable
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (r : ℕ) :
    Integrable (fun ω =>
      (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ) ^ r) M.P := by
  let N : M.Ω → ℕ := fun ω => BlockGUE.intervalCount M A₀ (Set.Icc a b) ω
  have hsum : Integrable (fun ω =>
      ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * ((N ω).descFactorial j : ℝ)) M.P := by
    apply integrable_finsetSum
    intro j hj
    exact (input.factorialIntegrable hd M A₀ a b j).const_mul _
  apply hsum.congr
  filter_upwards [] with ω
  exact_mod_cast (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial (N ω) r).symm

/-- Positive-order PSSS interval counts belong to `L^r`. -/
theorem psss_intervalCount_memLp
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    MemLp (fun ω =>
      (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)) r M.P := by
  let X : M.Ω → ℝ := fun ω =>
    (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)
  have hX : AEStronglyMeasurable X M.P :=
    (measurable_blockGUE_intervalCount_real M A₀ a b).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hX (by positivity) (by simp)).mp
  simpa [X, Real.norm_eq_abs, abs_of_nonneg, Real.rpow_natCast] using
    psss_countPower_integrable input hd M A₀ a b r

/-- For positive integer order, the real `L^r` seminorm of a measurable
block-GUE interval count is the `r`th root of its ordinary moment.  This exact
bridge is independent of the PSSS estimate; that input is used separately to
prove finiteness and bound the displayed moment. -/
theorem blockGUE_intervalCount_lpNorm_eq_momentRoot
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    lpNorm (fun ω =>
      (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)) r M.P =
      (∫ ω, (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ) ^ r ∂M.P) ^
        ((r : ℝ)⁻¹) := by
  let X : M.Ω → ℝ := fun ω =>
    (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
    (measurable_blockGUE_intervalCount_real M A₀ a b).aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast]
  congr 2
  funext ω
  simp [Real.rpow_natCast]

/-- Small-window `L^r` count bound in the paper's scaling.  For
`0 < v ≤ 1`, the norm grows like `v^(1/r)`.  The displayed constant is the
`r`th root of the unit-scale Stirling polynomial and depends only on `r` and
the absolute constant in `PSSSInput`; it is uniform in all matrix parameters,
the deformation, energy, and dimension cutoff. -/
theorem psss_scaled_countLpNorm_small
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e v L : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) (hL : 0 < L)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (r : ℕ) (hr : 1 ≤ r) :
    lpNorm (fun ω =>
      (BlockGUE.intervalCount M A₀
        (Set.Icc (e - v / L) (e + v / L)) ω : ℝ)) r M.P ≤
      (∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j) ^
          ((r : ℝ)⁻¹) * v ^ ((r : ℝ)⁻¹) := by
  let K : ℝ := ∑ j ∈ Finset.range (r + 1),
    (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by positivity)
      (pow_nonneg (mul_nonneg (by norm_num) input.C_nonneg) j)
  rw [blockGUE_intervalCount_lpNorm_eq_momentRoot hd M A₀
    (e - v / L) (e + v / L) r hr]
  calc
    (∫ ω, (BlockGUE.intervalCount M A₀
        (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P) ^
          ((r : ℝ)⁻¹) ≤
        (v * K) ^ ((r : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow
      · exact integral_nonneg fun _ => by positivity
      · simpa [K] using
          psss_scaled_countMoment_small input hd M A₀ e v L hv.le hv1 hL hdim r hr
      · positivity
    _ = K ^ ((r : ℝ)⁻¹) * v ^ ((r : ℝ)⁻¹) := by
      rw [Real.mul_rpow hv.le hK]
      exact mul_comm _ _

/-- Large-window `L^r` count bound in the paper's scaling.  For `v ≥ 1`,
the norm is at most the same explicit Stirling constant times `v`.  The
linearity in `v` follows by taking the `r`th root of the proved `v^r` moment
bound; no asymptotic or hidden supremum is introduced. -/
theorem psss_scaled_countLpNorm_large
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e v L : ℝ) (hv : 1 ≤ v) (hL : 0 < L)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (r : ℕ) (hr : 1 ≤ r) :
    lpNorm (fun ω =>
      (BlockGUE.intervalCount M A₀
        (Set.Icc (e - v / L) (e + v / L)) ω : ℝ)) r M.P ≤
      (∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j) ^
          ((r : ℝ)⁻¹) * v := by
  let K : ℝ := ∑ j ∈ Finset.range (r + 1),
    (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (by positivity)
      (pow_nonneg (mul_nonneg (by norm_num) input.C_nonneg) j)
  rw [blockGUE_intervalCount_lpNorm_eq_momentRoot hd M A₀
    (e - v / L) (e + v / L) r hr]
  calc
    (∫ ω, (BlockGUE.intervalCount M A₀
        (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P) ^
          ((r : ℝ)⁻¹) ≤
        (K * v ^ r) ^ ((r : ℝ)⁻¹) := by
      apply Real.rpow_le_rpow
      · exact integral_nonneg fun _ => by positivity
      · simpa [K] using
          psss_scaled_countMoment_large input hd M A₀ e v L hv hL hdim r hr
      · positivity
    _ = K ^ ((r : ℝ)⁻¹) * v := by
      have hv0 : 0 ≤ v := le_trans (by norm_num) hv
      rw [Real.mul_rpow hK (pow_nonneg hv0 r)]
      rw [Real.pow_rpow_inv_natCast hv0 (Nat.ne_of_gt hr)]

end CoareaNative.BlockBand
