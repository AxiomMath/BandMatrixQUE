module

public import BlockBand.Coarea.Native.BlockBand.Coarea.ProjectiveVolume
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Projective chart integral

This file evaluates the normalization integral of the eigenpair Jacobian lemma.
The radial density is evaluated by the explicit primitive
`(2n)⁻¹ (r² / (1+r²))^n`, and Mathlib's polar decomposition then gives the full
`π^n/n!` chart volume in real dimension `2n`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Filter MeasureTheory Metric Set
open scoped Topology

/-- The elementary primitive used for the projective radial density. -/
def projectiveRadialPrimitive (n : ℕ) (r : ℝ) : ℝ :=
  (1 / (2 * n : ℝ)) * (r ^ 2 / (1 + r ^ 2)) ^ n

/-- Derivative of the projective radial primitive. -/
theorem hasDerivAt_projectiveRadialPrimitive
    (n : ℕ) (hn : 0 < n) (r : ℝ) :
    HasDerivAt (projectiveRadialPrimitive n)
      (r * (r ^ 2) ^ (n - 1) * ((1 + r ^ 2)⁻¹) ^ (n + 1)) r := by
  cases n with
  | zero => omega
  | succ k =>
      have hden : 1 + r ^ 2 ≠ 0 := by positivity
      unfold projectiveRadialPrimitive
      have hquot :=
        ((hasDerivAt_id r).pow 2).div
          ((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)) hden
      have hpow := hquot.pow (k + 1)
      have hmul := (hasDerivAt_const r (1 / (2 * (k + 1) : ℝ))).mul hpow
      convert hmul using 1
      · funext x
        push_cast
        rfl
      · have hcancel :
            (1 + r ^ 2)⁻¹ ^ k * (1 + r ^ 2) ^ k = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hden, one_pow]
        have hcancel' (x : ℝ) :
            x * (1 + r ^ 2)⁻¹ ^ k * (1 + r ^ 2) ^ k = x := by
          rw [mul_assoc, hcancel, mul_one]
        simp
        field_simp [pow_succ]
        linear_combination
          -1 * (r * r ^ (k * 2) + 2 * r ^ 3 * r ^ (k * 2) +
            r ^ 5 * r ^ (k * 2)) * hcancel

/-- The derivative-friendly form of the radial density agrees with the polar form. -/
theorem projectiveRadialDensity_eq
    (n : ℕ) (hn : 0 < n) (r : ℝ) :
    r * (r ^ 2) ^ (n - 1) * ((1 + r ^ 2)⁻¹) ^ (n + 1) =
      r ^ (2 * n - 1) * ((1 + r ^ 2)⁻¹) ^ (n + 1) := by
  cases n with
  | zero => omega
  | succ k =>
      simp only [Nat.succ_sub_one]
      congr 1
      rw [pow_two, mul_pow]
      have hexp : 2 * (k + 1) - 1 = k * 2 + 1 := by omega
      rw [hexp, pow_succ]
      ring

/-- At infinity the substitution `u = r² / (1 + r²)` tends to the endpoint `1`. -/
theorem tendsto_projectiveRadialPrimitive
    (n : ℕ) :
    Tendsto (projectiveRadialPrimitive n) atTop
      (𝓝 (1 / (2 * n : ℝ))) := by
  have hsquare : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hden : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop := by
    exact tendsto_atTop_add_const_left atTop 1 hsquare
  have hinv : Tendsto (fun r : ℝ => 1 / (1 + r ^ 2)) atTop (𝓝 0) :=
    hden.const_div_atTop 1
  have hsub : Tendsto (fun r : ℝ => 1 - 1 / (1 + r ^ 2)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hquot :
      Tendsto (fun r : ℝ => r ^ 2 / (1 + r ^ 2)) atTop (𝓝 1) := by
    apply hsub.congr'
    filter_upwards with r
    have hne : 1 + r ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  unfold projectiveRadialPrimitive
  simpa using tendsto_const_nhds.mul (hquot.pow n)

/-- The radial integral after the substitution `u = r² / (1 + r²)`.

This is the improper real integral complementing `projectiveRadialFactor`:
the explicit primitive sends the endpoints `0` and `+∞` to `0` and `1/(2n)`. -/
theorem projectiveRadialIntegral
    (n : ℕ) (hn : 0 < n) :
    (∫ r : ℝ in Ioi 0,
        r ^ (2 * n - 1) * ((1 + r ^ 2)⁻¹) ^ (n + 1)) =
      1 / (2 * n : ℝ) := by
  let g' : ℝ → ℝ :=
    fun r => r * (r ^ 2) ^ (n - 1) * ((1 + r ^ 2)⁻¹) ^ (n + 1)
  have hFTC :
      (∫ r : ℝ in Ioi 0, g' r) =
        1 / (2 * n : ℝ) - projectiveRadialPrimitive n 0 :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun r _ => hasDerivAt_projectiveRadialPrimitive n hn r)
      (fun r hr => by
        dsimp [g']
        have hr0 : 0 ≤ r := hr.le
        positivity)
      (tendsto_projectiveRadialPrimitive n)
  rw [show projectiveRadialPrimitive n 0 = 0 by
    unfold projectiveRadialPrimitive
    norm_num [zero_pow hn.ne']] at hFTC
  simp only [sub_zero] at hFTC
  rw [← hFTC]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  exact (projectiveRadialDensity_eq n hn r).symm

/-- Real-valued form of the even-dimensional unit-ball volume used in the polar
decomposition. -/
theorem projectiveEvenBallVolume_real
    (n : ℕ) (hn : 0 < n) :
    volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * n))) 1) =
      Real.pi ^ n / n.factorial := by
  rw [measureReal_def, projectiveEvenBallVolume n hn,
    ENNReal.toReal_ofReal]
  positivity

/-- Full projective-chart normalization in real dimension `2n`.

This is the chart-density integral of the eigenpair Jacobian lemma.  Lebesgue measure is Mathlib's Euclidean `volume`, and the
integrand is written with a natural power to avoid any real-power convention. -/
theorem projectiveChartIntegral
    (n : ℕ) (hn : 0 < n) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * n)),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ (n + 1)) =
      Real.pi ^ n / n.factorial := by
  rw [projectiveChartIntegral_eq_radial n hn]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [projectiveRadialIntegral n hn, projectiveEvenBallVolume_real n hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-- The constant in the eigenpair Jacobian, written in the complex dimension `d`.  Thus the affine projective chart has `d - 1` complex (equivalently
`2(d-1)` real) coordinates and total density `π^(d-1)/(d-1)!`.

The hypothesis `1 < d` is the case of positive chart dimension;
the zero-dimensional endpoint `d = 1` is a separate one-point integral. -/
theorem eigenpairProjectiveChartNormalization
    (d : ℕ) (hd : 1 < d) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * (d - 1))),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ d) =
      Real.pi ^ (d - 1) / (d - 1).factorial := by
  have hpos : 0 < d - 1 := Nat.sub_pos_of_lt hd
  simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : d ≠ 0))] using
    projectiveChartIntegral (d - 1) hpos

end CoareaNative.BlockBand
