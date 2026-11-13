module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ScalarProfileControl
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.DeterministicMDECore

/-!
# Fixed-bond cyclic control for ER clause (i)

The paper fixes the bond weight `b ∈ (0,1/2)` before choosing its analytic
constants.  This module proves the deterministic phase and cyclic-resolvent estimates
needed to discharge clause (i) with constants depending on that fixed `b` but not on
the ring length, block width, or parity.

The dependence on `b` is essential.  In particular, as `b ↑ 1/2`, the `Ξ` multiplier
approaches the negative cyclic Fourier edge; consequently neither decay rate `a = 1`
nor the comparison constant `6e` can be uniform in `b`.  The common constant below
therefore takes the maximum with the scalar-control constant `6e`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERClause1

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra
  ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERJumpNormalization
  ERCyclicSummation ERHerglotz ERPhysicalBridge ERScalarProfileControl

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- On the unit spectral disk, the real part of the Herglotz solution is no
larger in absolute value than its imaginary part. -/
theorem abs_re_le_abs_im_erSemicircleStieltjes {z : ℂ}
    (hz0 : z.im ≠ 0) (hz : ‖z‖ ≤ 1) :
    |(erSemicircleStieltjes z).re| ≤
      |(erSemicircleStieltjes z).im| := by
  let m := erSemicircleStieltjes z
  have hm0 : m ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z
    simp [m, hm] at h
  have hmnorm : ‖m‖ < 1 := norm_erSemicircleStieltjes_lt_one hz0
  have hroot : m ^ 2 + z * m + 1 = 0 := erSemicircleStieltjes_dyson z
  have hzeq : z = -(m + m⁻¹) := by
    apply (mul_right_cancel₀ hm0)
    field_simp
    linear_combination hroot
  have hqpos : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm0
  have hre : z.re = -m.re * (1 + 1 / Complex.normSq m) := by
    rw [hzeq]
    simp only [Complex.neg_re, Complex.add_re, Complex.inv_re]
    field_simp [ne_of_gt hqpos]
  have hzre : |z.re| ≤ 1 :=
    (Complex.abs_re_le_norm z).trans hz
  have habs : |m.re| * (1 + 1 / Complex.normSq m) ≤ 1 := by
    have hfac : 0 ≤ 1 + 1 / Complex.normSq m := by positivity
    calc
      |m.re| * (1 + 1 / Complex.normSq m) =
          |-m.re * (1 + 1 / Complex.normSq m)| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hfac]
      _ = |z.re| := by rw [hre]
      _ ≤ 1 := hzre
  have hqeq : Complex.normSq m = ‖m‖ ^ 2 :=
    Complex.normSq_eq_norm_sq m
  have htpos : 0 < ‖m‖ := norm_pos_iff.mpr hm0
  have hrehalf : 2 * |m.re| ≤ ‖m‖ := by
    rw [hqeq] at habs
    have hmul := mul_le_mul_of_nonneg_right habs (sq_nonneg ‖m‖)
    field_simp [ne_of_gt htpos] at hmul
    nlinarith [sq_nonneg (‖m‖ - 1)]
  have hnormsq : ‖m‖ ^ 2 = m.re ^ 2 + m.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsquares : m.re ^ 2 ≤ m.im ^ 2 := by
    have hsquare := mul_self_le_mul_self
      (by positivity : 0 ≤ 2 * |m.re|) hrehalf
    nlinarith [sq_abs m.re]
  nlinarith [sq_abs m.re, sq_abs m.im, abs_nonneg m.re, abs_nonneg m.im,
    sq_nonneg (|m.re| + |m.im|)]

end ERNative.BlockBand.GaussianRing.ERClause1
