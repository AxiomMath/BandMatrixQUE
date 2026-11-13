module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneGlobalStripGluing

/-!
# Dimension-free scalar estimates for the CEH boundary implicit function

This module records the quantitative part of the boundary implicit-function
argument whose constants do not depend on the matrix dimension.  The estimates
use only the exact scalar MDE equation, the effective-height lower bound, and a
lower bound for the mixed stability denominator.  They preserve the normalized
finite average and the exact CEH typical-spacing equation.

The final results identify the remaining large-`N` issue at its narrowest
scalar form: a dimension-uniform closeness estimate for the scalar upper branch
at one fixed test height divided by `N^ξ`.  Once that inequality is available,
the exact spacing equation puts every canonical height below the fixed strip.
No rate certificate or replacement input structure is introduced here.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped BigOperators Topology

/-- Difference identity for two scalar MDE solutions.  Unlike the
upper-half-plane specialization, the hypotheses are the exact nonvanishing
effective heights, so one endpoint may be a positive-density real boundary
value. -/
theorem solution_difference_identity_of_effectiveHeight
    {N : ℕ} (f : DeformationSpectrum N) {s : ℝ}
    {z₁ z₂ m₁ m₂ : ℂ}
    (hh₁ : 0 < effectiveHeight s z₁ m₁)
    (hh₂ : 0 < effectiveHeight s z₂ m₂)
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂) :
    m₁ - m₂ = (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
      average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i) := by
  have hentry (i : Fin N) :
      entry f s z₁ m₁ i - entry f s z₂ m₂ i =
        (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
          entry f s z₁ m₁ i * entry f s z₂ m₂ i := by
    have h₁ := denominator_ne_zero f hh₁ i
    have h₂ := denominator_ne_zero f hh₂ i
    unfold entry
    rw [inv_sub_inv' h₁ h₂]
    ring
  calc
    m₁ - m₂ = average (entry f s z₁ m₁) -
        average (entry f s z₂ m₂) := congrArg₂ (· - ·) hm₁.1 hm₂.1
    _ = average (fun i => entry f s z₁ m₁ i - entry f s z₂ m₂ i) := by
      unfold average
      rw [Finset.sum_sub_distrib]
      ring
    _ = average (fun i =>
        (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
          (entry f s z₁ m₁ i * entry f s z₂ m₂ i)) := by
      congr 1
      funext i
      rw [hentry]
      ring
    _ = (z₁ - z₂ + (s : ℂ) * (m₁ - m₂)) *
        average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i) :=
      average_const_mul _ _

/-- Rearranged boundary/strip difference identity with the exact mixed
stability denominator. -/
theorem mixedStability_mul_solution_sub
    {N : ℕ} (f : DeformationSpectrum N) {s : ℝ}
    {z₁ z₂ m₁ m₂ : ℂ}
    (hh₁ : 0 < effectiveHeight s z₁ m₁)
    (hh₂ : 0 < effectiveHeight s z₂ m₂)
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂) :
    fourAdjointDenominator false false f s z₁ m₁ z₂ m₂ * (m₁ - m₂) =
      (z₁ - z₂) *
        average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i) := by
  have hid := solution_difference_identity_of_effectiveHeight f hh₁ hh₂ hm₁ hm₂
  simp only [fourAdjointDenominator, adjointedEntry, Bool.false_eq_true,
    ↓reduceIte]
  linear_combination hid

/-- Dimension-free quantitative implicit-function estimate.  A mixed
stability margin `γ` and a mixed-entry bound `B` give the exact modulus
`B/γ`; no reciprocal spectral height appears. -/
theorem norm_solution_sub_le_of_mixedStability
    {N : ℕ} (f : DeformationSpectrum N) {s γ B : ℝ} (hγ : 0 < γ)
    {z₁ z₂ m₁ m₂ : ℂ}
    (hh₁ : 0 < effectiveHeight s z₁ m₁)
    (hh₂ : 0 < effectiveHeight s z₂ m₂)
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂)
    (hdenom : γ ≤ ‖fourAdjointDenominator false false f s
      z₁ m₁ z₂ m₂‖)
    (hpair : ‖average (fun i =>
      entry f s z₁ m₁ i * entry f s z₂ m₂ i)‖ ≤ B) :
    ‖m₁ - m₂‖ ≤ ‖z₁ - z₂‖ * B / γ := by
  have hid := mixedStability_mul_solution_sub f hh₁ hh₂ hm₁ hm₂
  apply (le_div_iff₀ hγ).2
  calc
    ‖m₁ - m₂‖ * γ = γ * ‖m₁ - m₂‖ := by ring
    _ ≤ ‖fourAdjointDenominator false false f s z₁ m₁ z₂ m₂‖ *
        ‖m₁ - m₂‖ :=
      mul_le_mul_of_nonneg_right hdenom (norm_nonneg _)
    _ = ‖z₁ - z₂‖ * ‖average (fun i =>
        entry f s z₁ m₁ i * entry f s z₂ m₂ i)‖ := by
      rw [← norm_mul, hid, norm_mul]
    _ ≤ ‖z₁ - z₂‖ * B :=
      mul_le_mul_of_nonneg_left hpair (norm_nonneg _)

/-- Uniform mixed-entry estimate from positive effective-height lower bounds.
The constant is independent of `N` because `average` is normalized by `N`. -/
theorem norm_average_entry_mul_le_of_effectiveHeight
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    {z₁ z₂ m₁ m₂ : ℂ}
    (hheight₁ : h₁ ≤ effectiveHeight s z₁ m₁)
    (hheight₂ : h₂ ≤ effectiveHeight s z₂ m₂) :
    ‖average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i)‖ ≤
      h₁⁻¹ * h₂⁻¹ := by
  have he₁ (i : Fin N) : ‖entry f s z₁ m₁ i‖ ≤ h₁⁻¹ := by
    have hpos : 0 < effectiveHeight s z₁ m₁ := lt_of_lt_of_le hh₁ hheight₁
    exact (norm_entry_le_inv_effectiveHeight f hpos i).trans
      (inv_anti₀ hh₁ hheight₁)
  have he₂ (i : Fin N) : ‖entry f s z₂ m₂ i‖ ≤ h₂⁻¹ := by
    have hpos : 0 < effectiveHeight s z₂ m₂ := lt_of_lt_of_le hh₂ hheight₂
    exact (norm_entry_le_inv_effectiveHeight f hpos i).trans
      (inv_anti₀ hh₂ hheight₂)
  calc
    ‖average (fun i => entry f s z₁ m₁ i * entry f s z₂ m₂ i)‖ ≤
        averageReal (fun i =>
          ‖entry f s z₁ m₁ i * entry f s z₂ m₂ i‖) :=
      norm_average_le hN _
    _ ≤ averageReal (fun _ : Fin N => h₁⁻¹ * h₂⁻¹) := by
      unfold averageReal
      gcongr with i
      change ‖entry f s z₁ m₁ i * entry f s z₂ m₂ i‖ ≤
        h₁⁻¹ * h₂⁻¹
      rw [norm_mul]
      exact mul_le_mul (he₁ i) (he₂ i) (norm_nonneg _) (by positivity)
    _ = h₁⁻¹ * h₂⁻¹ := by simp [averageReal, hN.ne']

/-- Quantitative variation from an ordinary stability denominator at the
boundary endpoint to the mixed denominator joining it to a nearby solution.
All three resolvent factors are controlled by effective height, giving the
dimension-free cubic scale. -/
theorem norm_stabilityDenominator_sub_mixed_le_of_effectiveHeight
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s h₁ h₀ : ℝ} (hs : 0 ≤ s) (hh₁ : 0 < h₁) (hh₀ : 0 < h₀)
    {z₁ z₀ m₁ m₀ : ℂ}
    (hheight₁ : h₁ ≤ effectiveHeight s z₁ m₁)
    (hheight₀ : h₀ ≤ effectiveHeight s z₀ m₀) :
    ‖stabilityDenominator f s z₀ m₀ -
      fourAdjointDenominator false false f s z₁ m₁ z₀ m₀‖ ≤
      s * (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) * h₁⁻¹ * h₀⁻¹ ^ 2 := by
  let e₁ := entry f s z₁ m₁
  let e₀ := entry f s z₀ m₀
  have hp₁ : 0 < effectiveHeight s z₁ m₁ := lt_of_lt_of_le hh₁ hheight₁
  have hp₀ : 0 < effectiveHeight s z₀ m₀ := lt_of_lt_of_le hh₀ hheight₀
  have he₁ (i : Fin N) : ‖e₁ i‖ ≤ h₁⁻¹ :=
    (norm_entry_le_inv_effectiveHeight f hp₁ i).trans
      (inv_anti₀ hh₁ hheight₁)
  have he₀ (i : Fin N) : ‖e₀ i‖ ≤ h₀⁻¹ :=
    (norm_entry_le_inv_effectiveHeight f hp₀ i).trans
      (inv_anti₀ hh₀ hheight₀)
  have hdiff (i : Fin N) :
      e₁ i - e₀ i =
        (z₁ - z₀ + (s : ℂ) * (m₁ - m₀)) * e₁ i * e₀ i := by
    have hn₁ := denominator_ne_zero f hp₁ i
    have hn₀ := denominator_ne_zero f hp₀ i
    dsimp only [e₁, e₀]
    unfold entry
    rw [inv_sub_inv' hn₁ hn₀]
    ring
  have hpoint (i : Fin N) :
      ‖(e₁ i - e₀ i) * e₀ i‖ ≤
        (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) * h₁⁻¹ * h₀⁻¹ ^ 2 := by
    rw [hdiff, norm_mul, norm_mul, norm_mul]
    have hzbound :
        ‖z₁ - z₀ + (s : ℂ) * (m₁ - m₀)‖ ≤
          ‖z₁ - z₀‖ + s * ‖m₁ - m₀‖ := by
      calc
        ‖z₁ - z₀ + (s : ℂ) * (m₁ - m₀)‖ ≤
            ‖z₁ - z₀‖ + ‖(s : ℂ) * (m₁ - m₀)‖ := norm_add_le _ _
        _ = ‖z₁ - z₀‖ + s * ‖m₁ - m₀‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hs]
    calc
      ‖z₁ - z₀ + (s : ℂ) * (m₁ - m₀)‖ *
            ‖e₁ i‖ * ‖e₀ i‖ * ‖e₀ i‖ ≤
          ((‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
            h₁⁻¹) * ‖e₀ i‖ * ‖e₀ i‖ := by
        gcongr
        exact he₁ i
      _ ≤ ((‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
            h₁⁻¹) * h₀⁻¹ * ‖e₀ i‖ := by
        gcongr
        exact he₀ i
      _ ≤ (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
            h₁⁻¹ * h₀⁻¹ * h₀⁻¹ := by
        gcongr
        exact he₀ i
      _ = (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
          h₁⁻¹ * h₀⁻¹ ^ 2 := by ring
  have havg : ‖average (fun i => (e₁ i - e₀ i) * e₀ i)‖ ≤
      (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) * h₁⁻¹ * h₀⁻¹ ^ 2 := by
    calc
      ‖average (fun i => (e₁ i - e₀ i) * e₀ i)‖ ≤
          averageReal (fun i => ‖(e₁ i - e₀ i) * e₀ i‖) :=
        norm_average_le hN _
      _ ≤ averageReal (fun _ : Fin N =>
          (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) * h₁⁻¹ * h₀⁻¹ ^ 2) := by
        unfold averageReal
        gcongr with i
        exact hpoint i
      _ = (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
          h₁⁻¹ * h₀⁻¹ ^ 2 := by simp [averageReal, hN.ne']
  have heq : stabilityDenominator f s z₀ m₀ -
      fourAdjointDenominator false false f s z₁ m₁ z₀ m₀ =
      (s : ℂ) * average (fun i => (e₁ i - e₀ i) * e₀ i) := by
    simp only [stabilityDenominator, fourAdjointDenominator,
      adjointedEntry, Bool.false_eq_true, ↓reduceIte]
    change (1 - (s : ℂ) * average (fun i => e₀ i ^ 2)) -
      (1 - (s : ℂ) * average (fun i => e₁ i * e₀ i)) = _
    have havgeq : average (fun i => e₁ i * e₀ i) -
        average (fun i => e₀ i ^ 2) =
        average (fun i => (e₁ i - e₀ i) * e₀ i) := by
      unfold average
      rw [← sub_div, ← Finset.sum_sub_distrib]
      apply congrArg (fun t : ℂ => t / (N : ℂ))
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [← havgeq]
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hs]
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left havg hs

/-- An ordinary boundary stability margin loses at most half its size when
the explicit cubic perturbation bound is at most `c/2`. -/
theorem mixedStability_ge_half_of_boundary
    {N : ℕ} (f : DeformationSpectrum N) {s c : ℝ}
    {z₁ z₀ m₁ m₀ : ℂ}
    (hboundary : c ≤ ‖stabilityDenominator f s z₀ m₀‖)
    (hperturb : ‖stabilityDenominator f s z₀ m₀ -
      fourAdjointDenominator false false f s z₁ m₁ z₀ m₀‖ ≤ c / 2) :
    c / 2 ≤ ‖fourAdjointDenominator false false f s
      z₁ m₁ z₀ m₀‖ := by
  have htri := norm_sub_norm_le
    (stabilityDenominator f s z₀ m₀)
    (fourAdjointDenominator false false f s z₁ m₁ z₀ m₀)
  nlinarith

/-- The quantitative boundary IFT modulus after inserting the uniform
positive-density scale.  This is the estimate used at a real boundary point:
if the mixed denominator retains half of the boundary margin, displacement is
at most `8|z₁-z₂|/(s²c³)`. -/
theorem norm_solution_sub_le_boundary_scale
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    {z₁ z₂ m₁ m₂ : ℂ}
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂)
    (hheight₁ : s * c / 2 ≤ effectiveHeight s z₁ m₁)
    (hheight₂ : s * c / 2 ≤ effectiveHeight s z₂ m₂)
    (hdenom : c / 2 ≤ ‖fourAdjointDenominator false false f s
      z₁ m₁ z₂ m₂‖) :
    ‖m₁ - m₂‖ ≤ 8 * ‖z₁ - z₂‖ / (s ^ 2 * c ^ 3) := by
  have hsc : 0 < s * c / 2 := by positivity
  have hpair := norm_average_entry_mul_le_of_effectiveHeight hN f
    hsc hsc hheight₁ hheight₂
  have hbase := norm_solution_sub_le_of_mixedStability f
    (show 0 < c / 2 by positivity)
    (lt_of_lt_of_le hsc hheight₁)
    (lt_of_lt_of_le hsc hheight₂) hm₁ hm₂ hdenom hpair
  calc
    ‖m₁ - m₂‖ ≤ ‖z₁ - z₂‖ * (s * c / 2)⁻¹ ^ 2 / (c / 2) := by
      simpa [pow_two] using hbase
    _ = 8 * ‖z₁ - z₂‖ / (s ^ 2 * c ^ 3) := by
      field_simp [hs.ne', hc.ne']
      ring

/-- Explicit dimension-free quantitative IFT bootstrap.  On the ball where
both effective heights retain `s*c/2`, the single scalar smallness inequality
shown below preserves half the boundary stability margin and forces the sharp
linear displacement estimate.  Closing this bootstrap for the branch
requires only ruling out escape from this ball; all analytic constants in the
implication are independent of `N`. -/
theorem boundary_quantitativeIFT_bootstrap
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    {z₁ z₀ m₁ m₀ : ℂ}
    (hm₁ : IsSolution f s z₁ m₁) (hm₀ : IsSolution f s z₀ m₀)
    (hheight₁ : s * c / 2 ≤ effectiveHeight s z₁ m₁)
    (hheight₀ : s * c / 2 ≤ effectiveHeight s z₀ m₀)
    (hboundary : c ≤ ‖stabilityDenominator f s z₀ m₀‖)
    (hsmall : s * (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
      (s * c / 2)⁻¹ ^ 3 ≤ c / 2) :
    c / 2 ≤ ‖fourAdjointDenominator false false f s
        z₁ m₁ z₀ m₀‖ ∧
      ‖m₁ - m₀‖ ≤ 8 * ‖z₁ - z₀‖ / (s ^ 2 * c ^ 3) := by
  have hsc : 0 < s * c / 2 := by positivity
  have hpert := norm_stabilityDenominator_sub_mixed_le_of_effectiveHeight
    hN f hs.le hsc hsc hheight₁ hheight₀
  have hpert' : ‖stabilityDenominator f s z₀ m₀ -
      fourAdjointDenominator false false f s z₁ m₁ z₀ m₀‖ ≤ c / 2 := by
    apply hpert.trans
    calc
      s * (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
          (s * c / 2)⁻¹ * (s * c / 2)⁻¹ ^ 2 =
          s * (‖z₁ - z₀‖ + s * ‖m₁ - m₀‖) *
            (s * c / 2)⁻¹ ^ 3 := by ring
      _ ≤ c / 2 := hsmall
  have hmixed := mixedStability_ge_half_of_boundary f hboundary hpert'
  exact ⟨hmixed, norm_solution_sub_le_boundary_scale
    hN f hs hc hm₁ hm₀ hheight₁ hheight₀ hmixed⟩

/-- Scalar upper-branch closeness to a boundary value immediately supplies a
positive density lower bound at the same height. -/
theorem density_upperBranch_ge_of_close_boundary
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) {x η c : ℝ} (_hc : 0 < c)
    {m₀ : ℂ} (hm₀ : c ≤ m₀.im) (_hη : 0 < η)
    (hclose : ‖upperBranch hN f hs
      ((x : ℂ) + (η : ℂ) * Complex.I) - m₀‖ < c / 2) :
    c / (2 * Real.pi) ≤ density (upperBranch hN f hs
      ((x : ℂ) + (η : ℂ) * Complex.I)) := by
  let m := upperBranch hN f hs ((x : ℂ) + (η : ℂ) * Complex.I)
  have him : |m.im - m₀.im| ≤ ‖m - m₀‖ := by
    simpa using Complex.abs_im_le_norm (m - m₀)
  have himlt : |m.im - m₀.im| < c / 2 :=
    lt_of_le_of_lt him hclose
  have hmlower : c / 2 < m.im := by
    rw [abs_lt] at himlt
    linarith
  unfold density
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [show c / (2 * Real.pi) = (c / 2) / Real.pi by ring]
  exact (div_le_div_iff_of_pos_right hpi).2 hmlower.le

/-- Exact canonical-height consequence of the one scalar inequality still
needed uniformly in `N`.  The test height is `H/N^ξ`; closeness there to a
boundary value of imaginary part at least `c` gives the density lower bound,
and the exact typical-spacing equation then places `N^ξ η_f(x)` below `H`. -/
theorem rpow_mul_cehTypicalSpacing_lt_of_boundary_close
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x ξ H c : ℝ) (hH : 0 < H) (hc : 0 < c)
    {m₀ : ℂ} (hm₀ : c ≤ m₀.im)
    (hclose : ‖upperBranch (by omega) f hs
      ((x : ℂ) + ((H / (N : ℝ) ^ ξ : ℝ) : ℂ) * Complex.I) - m₀‖ < c / 2)
    (hlarge : 1 < (N : ℝ) * (H / (N : ℝ) ^ ξ) *
      (c / (2 * Real.pi))) :
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x < H := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < (N : ℝ) ^ ξ := Real.rpow_pos_of_pos hNpos ξ
  have htest : 0 < H / (N : ℝ) ^ ξ := div_pos hH hpow
  apply rpow_mul_cehTypicalSpacing_lt_of_density_lower hN f hs x ξ H
    (c / (2 * Real.pi)) hH
  · exact density_upperBranch_ge_of_close_boundary (by omega) f hs hc hm₀
      htest hclose
  · exact hlarge

end CEHNative.BlockBand.CEH
