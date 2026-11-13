module

public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairCoordinates
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Projective-chart normalization constants

This file isolates the exact beta integral and even-dimensional Euclidean volume
constants in the normalization of the eigenpair Jacobian.  If the projective chart has complex dimension `n = d - 1`, its radial
calculation uses `B(n,1) = 1/n`, while the angular constant is the volume
`π^n / n!` of the real `2n`-dimensional unit ball.

Mathlib supplies both the Euclidean polar-integration bridge and the beta integral, but
does not currently expose their composition with the projective substitution
`u = r² / (1 + r²)`.  Consequently the final equality
`∫ z : Fin n → ℂ, (1 + ‖z‖ ^ 2) ^ (-(n + 1)) = π^n / n!`
is not asserted here (it is `projectiveChartIntegral`).  The declarations below give
its special-function, radial decomposition, and measure normalizations; only the
one-dimensional substitution is left to the chart-integral file.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Metric Set

/-- The beta integral occurring after the radial substitution
`u = r² / (1 + r²)` is `B(n,1) = 1/n`.

The hypothesis `0 < n` is the condition `d ≥ 2`; the zero-dimensional
projective chart (`d = 1`) is handled separately by the empty-coordinate integral. -/
theorem projectiveRadialBetaIntegral
    (n : ℕ) (hn : 0 < n) :
    Complex.betaIntegral (n : ℂ) 1 = 1 / (n : ℂ) := by
  apply Complex.betaIntegral_eval_one_right
  norm_num
  exact_mod_cast hn

/-- The preceding beta value written out as the exact interval integral used after the
projective radial change of variables. -/
theorem projectiveRadialBetaIntervalIntegral
    (n : ℕ) (hn : 0 < n) :
    (∫ u : ℝ in 0..1, (u : ℂ) ^ ((n : ℂ) - 1) *
      (1 - (u : ℂ)) ^ ((1 : ℂ) - 1)) = 1 / (n : ℂ) := by
  simpa only [Complex.betaIntegral] using projectiveRadialBetaIntegral n hn

/-- Including the Jacobian `r dr = dt/2`, the one-dimensional radial beta factor is
`1/(2n)`.  This is the radial factor which multiplies the area of `S^(2n-1)`. -/
theorem projectiveRadialFactor
    (n : ℕ) (hn : 0 < n) :
    (1 / 2 : ℂ) * Complex.betaIntegral (n : ℂ) 1 =
      1 / (2 * n : ℕ) := by
  rw [projectiveRadialBetaIntegral n hn]
  push_cast
  field_simp

/-- Exact Euclidean polar decomposition of the projective-chart density.

This is the Mathlib formulation of the coordinate bridge from the integral over
`ℝ^(2n)` to the radial integral.  After rewriting the radial integral by
`u = r² / (1 + r²)`, `projectiveRadialFactor` evaluates it. -/
theorem projectiveChartIntegral_eq_radial
    (n : ℕ) (hn : 0 < n) :
    (∫ z : EuclideanSpace ℝ (Fin (2 * n)),
        ((1 + ‖z‖ ^ 2)⁻¹) ^ (n + 1)) =
      (2 * n) •
        volume.real (ball (0 : EuclideanSpace ℝ (Fin (2 * n))) 1) •
          ∫ r : ℝ in Ioi 0,
            r ^ (2 * n - 1) • ((1 + r ^ 2)⁻¹) ^ (n + 1) := by
  let _ : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    (MeasureTheory.integral_fun_norm_addHaar
      (E := EuclideanSpace ℝ (Fin (2 * n))) volume
      (fun r : ℝ => ((1 + r ^ 2)⁻¹) ^ (n + 1)))

/-- The angular normalization is encoded by the exact volume of the unit ball in real
dimension `2n`: `π^n/n!`.

There are no asymptotic
parameters or probabilistic normalizations in this identity. -/
theorem projectiveEvenBallVolume
    (n : ℕ) (hn : 0 < n) :
    volume (ball (0 : EuclideanSpace ℝ (Fin (2 * n))) 1) =
      ENNReal.ofReal (Real.pi ^ n / n.factorial) := by
  let _ : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  simpa using
    (InnerProductSpace.volume_ball_of_dim_even
      (E := EuclideanSpace ℝ (Fin (2 * n))) (k := n) (by simp) 0 1)

/-- Equivalently, the total spherical measure in real dimension `2n` is `2n` times
`π^n/n!`.  Together with `projectiveRadialFactor`, this is the formal constant
cancellation behind the projective-chart integral. -/
theorem projectiveEvenSphereMass
    (n : ℕ) (hn : 0 < n) :
    volume.toSphere
        (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * n))) 1)) =
      (2 * n : ℕ) * ENNReal.ofReal (Real.pi ^ n / n.factorial) := by
  let _ : Nonempty (Fin (2 * n)) := Fin.pos_iff_nonempty.mp (by omega)
  rw [Measure.toSphere_apply_univ, projectiveEvenBallVolume n hn]
  simp

end CoareaNative.BlockBand
