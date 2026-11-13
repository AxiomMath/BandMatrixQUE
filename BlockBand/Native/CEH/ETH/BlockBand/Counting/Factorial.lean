module

public import BlockBand.Native.CEH.ETH.BlockBand.Counting.Moments

/-!
# Counting consequences of the PSSS interface

This module performs the first specialization of the external counting theorem.
It keeps the deterministic deformation arbitrary and converts every positive
falling-factorial estimate into an ordinary integer moment by the exact
Stirling expansion.  This is the count-moment input used by the singular-log
shell argument and the later tightness proof.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open MeasureTheory
open scoped BigOperators

universe u

/-- PSSS factorial moments imply the ordinary local-count moment
bound, with no loss beyond the explicit Stirling polynomial. -/
theorem psss_countMoment
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) :
    let q := input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)
    ∫ ω, (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ) ^ r ∂M.P ≤
      ∑ j ∈ Finset.range (r + 1), (r.stirlingSecond j : ℝ) * q ^ j := by
  dsimp only
  apply ordinaryMoment_le_of_factorialMoments M.P
  · intro j hj
    exact input.factorialIntegrable hd M A₀ a b j
  · intro j hj
    cases j with
    | zero =>
        simp
    | succ j =>
        exact input.factorialCount hd M A₀ a b hab (j + 1) (Nat.succ_le_succ (Nat.zero_le j))

/-- Rescaled local-count moment bound used in the dyadic singular-log proof.
When the matrix dimension is at most `L`, an interval of radius `v / L`
has Stirling parameter at most `2 C v`, uniformly in the ambient dimension. -/
theorem psss_scaled_countMoment
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e v L : ℝ) (hv : 0 ≤ v) (hL : 0 < L)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (r : ℕ) :
    ∫ ω,
        (BlockGUE.intervalCount M A₀
          (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P ≤
      ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C * v) ^ j := by
  let D : ℝ := Fintype.card (BlockGUE.Index d)
  let q : ℝ := input.C * D * ((e + v / L) - (e - v / L))
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hratio : D / L ≤ 1 := (div_le_one hL).mpr hdim
  have hratio0 : 0 ≤ D / L := div_nonneg hD hL.le
  have hqeq : q = (2 * input.C * v) * (D / L) := by
    dsimp [q]
    field_simp
    ring
  have hq0 : 0 ≤ q := by
    rw [hqeq]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) input.C_nonneg) hv) hratio0
  have hqle : q ≤ 2 * input.C * v := by
    rw [hqeq]
    calc
      (2 * input.C * v) * (D / L) ≤ (2 * input.C * v) * 1 :=
        mul_le_mul_of_nonneg_left hratio
          (mul_nonneg (mul_nonneg (by norm_num) input.C_nonneg) hv)
      _ = 2 * input.C * v := mul_one _
  calc
    ∫ ω,
        (BlockGUE.intervalCount M A₀
          (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P ≤
        ∑ j ∈ Finset.range (r + 1),
          (r.stirlingSecond j : ℝ) * q ^ j := by
            simpa [q, D] using
              psss_countMoment input hd M A₀
                (e - v / L) (e + v / L)
                (by have := div_nonneg hv hL.le; linarith) r
    _ ≤ ∑ j ∈ Finset.range (r + 1),
          (r.stirlingSecond j : ℝ) * (2 * input.C * v) ^ j := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_left
            · exact pow_le_pow_left₀ hq0 hqle j
            · positivity

/-- Small-window form of `psss_scaled_countMoment`: for `v ≤ 1`, the
`r`th count moment is bounded by an explicit constant times `v`. -/
theorem psss_scaled_countMoment_small
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e v L : ℝ) (hv : 0 ≤ v) (hv1 : v ≤ 1) (hL : 0 < L)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω,
        (BlockGUE.intervalCount M A₀
          (Set.Icc (e - v / L) (e + v / L)) ω : ℝ) ^ r ∂M.P ≤
      v * ∑ j ∈ Finset.range (r + 1),
        (r.stirlingSecond j : ℝ) * (2 * input.C) ^ j := by
  exact (psss_scaled_countMoment input hd M A₀ e v L hv hL hdim r).trans
    (stirlingMomentPolynomial_small r hr
      (mul_nonneg (by norm_num) input.C_nonneg) hv hv1)

/-- The `r = 2` close-pair factorial estimate, in the exact ordered-pair
convention `N(N-1)` used in the paper. -/
theorem psss_closePairCount
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (hab : a ≤ b) :
    ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial 2 : ℝ) ∂M.P
      ≤ (input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ 2 :=
  input.factorialCount hd M A₀ a b hab 2 (by norm_num)

/-- First-moment tail bound for local counts.  This is the explicit Markov
step used to turn the uniform PSSS estimate into tightness: no asymptotic
quantifier is hidden in the statement. -/
theorem psss_count_tail
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b R : ℝ) (hab : a ≤ b) :
    R * M.P.real
        {ω | R ≤ (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)}
      ≤ input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a) := by
  let N : M.Ω → ℝ :=
    fun ω => (BlockGUE.intervalCount M A₀ (Set.Icc a b) ω : ℝ)
  have hint : Integrable N M.P := by
    simpa [N] using input.factorialIntegrable hd M A₀ a b 1
  calc
    R * M.P.real {ω | R ≤ N ω} ≤ ∫ ω, N ω ∂M.P :=
      mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _) hint R
    _ ≤ input.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a) := by
      simpa [N] using
        input.factorialCount hd M A₀ a b hab 1 (by norm_num)

/-- A deformed block-GUE ensemble has no eigenvalue at a prescribed real
energy, almost surely.  This is the zero-length-interval consequence used to
remove determinant regulators in the passive-log argument. -/
theorem psss_no_fixed_eigenvalue
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (e : ℝ) :
    ∀ᵐ ω ∂M.P, BlockGUE.intervalCount M A₀ (Set.Icc e e) ω = 0 := by
  let N : M.Ω → ℕ := fun ω => BlockGUE.intervalCount M A₀ (Set.Icc e e) ω
  have hint : Integrable (fun ω => (N ω : ℝ)) M.P := by
    simpa [N] using input.factorialIntegrable hd M A₀ e e 1
  have hle : ∫ ω, (N ω : ℝ) ∂M.P ≤ 0 := by
    simpa [N] using input.factorialCount hd M A₀ e e le_rfl 1 (by norm_num)
  have hzero : ∫ ω, (N ω : ℝ) ∂M.P = 0 :=
    le_antisymm hle (integral_nonneg fun _ => Nat.cast_nonneg _)
  have hae : (fun ω => (N ω : ℝ)) =ᵐ[M.P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => Nat.cast_nonneg _) hint).mp hzero
  filter_upwards [hae] with ω hω
  simp only [Pi.zero_apply] at hω
  have : N ω = 0 := by exact_mod_cast hω
  exact this

/-- Equivalent ordered-spectrum form of `psss_no_fixed_eigenvalue`: every
ordered eigenvalue avoids a prescribed deterministic energy almost surely. -/
theorem psss_no_fixed_orderedEigenvalue
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) (e : ℝ) :
    ∀ᵐ ω ∂M.P, ∀ i, orderedEigenvalue (BlockGUE.deformed M A₀ ω) i ≠ e := by
  filter_upwards [psss_no_fixed_eigenvalue input hd M A₀ e] with ω hω
  apply (eigenCount_singleton_eq_zero_iff (BlockGUE.deformed M A₀ ω) e).mp
  simpa [BlockGUE.intervalCount] using hω

end CEHNative.BlockBand
