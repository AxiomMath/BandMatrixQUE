module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneUniformFirstExit
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventStability

/-!
# CEH mixed-pairing assembly at source spectral points

The published local-ETH interface places each of the two energies in the
shrinking window `|x-E₀| ≤ N^(β-1)`, while the spectral height is exactly
`N^ξ η_f(x)`.  This module records the dimension-free perturbation estimate
which turns entrywise closeness to one boundary MDE vector into the strict CEH
mixed-pairing inequality.  It also connects that inequality to the
`regularizationCoefficient` from the two-resolvent API.

The estimates are unconditional algebraic consequences of the checked-in
interfaces.  No two-energy modulus or observable bound is added as an input.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Set
open scoped BigOperators ComplexConjugate

/-- The two source-window restrictions imply the exact pair-energy separation
`|x-y| ≤ 2 N^(β-1)`. -/
theorem abs_sub_le_two_mul_rpow_of_sourceWindow
    {N : ℕ} {β E₀ x y : ℝ}
    (hx : |x - E₀| ≤ (N : ℝ) ^ (β - 1))
    (hy : |y - E₀| ≤ (N : ℝ) ^ (β - 1)) :
    |x - y| ≤ 2 * (N : ℝ) ^ (β - 1) := by
  have htri : |x - y| ≤ |x - E₀| + |y - E₀| := by
    calc
      |x - y| = |(x - E₀) - (y - E₀)| := by ring_nf
      _ ≤ |x - E₀| + |y - E₀| := abs_sub _ _
  linarith

/-- Exact zero-height Ward normalization at a positive-density real scalar MDE
solution.  This is the boundary value around which the theta-one perturbation
is performed. -/
theorem scaledPairing_boundary_eq_one
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s x : ℝ} (hs : 0 < s) {m : ℂ}
    (hm : IsSolution f s (x : ℂ) m) :
    scaledPairing s (entry f s (x : ℂ) m) (entry f s (x : ℂ) m) = 1 := by
  have hh : 0 < effectiveHeight s (x : ℂ) m := by
    simp only [effectiveHeight, Complex.ofReal_im, zero_add]
    exact mul_pos hs hm.2
  have hward := averageReal_normSq_eq_im_div_effectiveHeight hN f hh hm
  have heff : effectiveHeight s (x : ℂ) m = s * m.im := by
    simp [effectiveHeight]
  rw [heff] at hward
  unfold scaledPairing
  have havg : (average (fun i => entry f s (x : ℂ) m i *
      star (entry f s (x : ℂ) m i))).re =
      averageReal (fun i => ‖entry f s (x : ℂ) m i‖ ^ 2) := by
    unfold average averageReal
    have hsum : (∑ i, entry f s (x : ℂ) m i *
        star (entry f s (x : ℂ) m i)) =
        ((∑ i, ‖entry f s (x : ℂ) m i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      exact Complex.mul_conj' _
    rw [hsum]
    norm_cast
  rw [havg, hward]
  field_simp [hs.ne', hm.2.ne']

/-- Dimension-free perturbation of a normalized mixed pairing.  If both MDE
entry vectors are uniformly `δ`-close to one boundary vector bounded by `B`,
the normalized mixed average moves by at most `2Bδ+δ²`. -/
theorem norm_average_mul_star_sub_le_of_uniform_close
    {N : ℕ} (hN : 0 < N) (q₀ q₁ q₂ : Fin N → ℂ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ B)
    (hq₁ : ∀ i, ‖q₁ i - q₀ i‖ ≤ δ)
    (hq₂ : ∀ i, ‖q₂ i - q₀ i‖ ≤ δ) :
    ‖average (fun i => q₁ i * star (q₂ i)) -
      average (fun i => q₀ i * star (q₀ i))‖ ≤
        2 * B * δ + δ ^ 2 := by
  have hpoint (i : Fin N) :
      ‖q₁ i * star (q₂ i) - q₀ i * star (q₀ i)‖ ≤
        2 * B * δ + δ ^ 2 := by
    have hid : q₁ i * star (q₂ i) - q₀ i * star (q₀ i) =
        (q₁ i - q₀ i) * star (q₂ i - q₀ i) +
        (q₁ i - q₀ i) * star (q₀ i) +
        q₀ i * star (q₂ i - q₀ i) := by
      have hstar : star (q₂ i - q₀ i) =
          star (q₂ i) - star (q₀ i) :=
        map_sub (starRingEnd ℂ) _ _
      rw [hstar]
      ring
    rw [hid]
    calc
      ‖(q₁ i - q₀ i) * star (q₂ i - q₀ i) +
          (q₁ i - q₀ i) * star (q₀ i) +
          q₀ i * star (q₂ i - q₀ i)‖ ≤
        ‖(q₁ i - q₀ i) * star (q₂ i - q₀ i) +
          (q₁ i - q₀ i) * star (q₀ i)‖ +
          ‖q₀ i * star (q₂ i - q₀ i)‖ := norm_add_le _ _
      _ ≤
        ‖(q₁ i - q₀ i) * star (q₂ i - q₀ i)‖ +
          ‖(q₁ i - q₀ i) * star (q₀ i)‖ +
          ‖q₀ i * star (q₂ i - q₀ i)‖ := by
        have hn := norm_add_le
          ((q₁ i - q₀ i) * star (q₂ i - q₀ i))
          ((q₁ i - q₀ i) * star (q₀ i))
        linarith
      _ = ‖q₁ i - q₀ i‖ * ‖q₂ i - q₀ i‖ +
          ‖q₁ i - q₀ i‖ * ‖q₀ i‖ +
          ‖q₀ i‖ * ‖q₂ i - q₀ i‖ := by
        simp only [norm_mul, norm_star]
      _ ≤ δ * δ + δ * B + B * δ := by
        gcongr
        · exact hq₁ i
        · exact hq₂ i
        · exact hq₁ i
        · exact hq₀ i
        · exact hq₀ i
        · exact hq₂ i
      _ = 2 * B * δ + δ ^ 2 := by ring
  have havg_sub : average (fun i => q₁ i * star (q₂ i)) -
      average (fun i => q₀ i * star (q₀ i)) =
      average (fun i => q₁ i * star (q₂ i) -
        q₀ i * star (q₀ i)) := by
    unfold average
    rw [← sub_div, Finset.sum_sub_distrib]
  rw [havg_sub]
  calc
    ‖average (fun i => q₁ i * star (q₂ i) -
        q₀ i * star (q₀ i))‖ ≤
      averageReal (fun i => ‖q₁ i * star (q₂ i) -
        q₀ i * star (q₀ i)‖) := norm_average_le hN _
    _ ≤ averageReal (fun _ : Fin N => 2 * B * δ + δ ^ 2) := by
      unfold averageReal
      gcongr with i
      exact hpoint i
    _ = 2 * B * δ + δ ^ 2 := by
      unfold averageReal
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr hN.ne']

/-- Strict mixed-pairing lower bound from the exact boundary Ward identity and
the explicit perturbation budget. -/
theorem scaledPairing_gt_half_of_uniform_close
    {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    (q₀ q₁ q₂ : Fin N → ℂ) {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hward : scaledPairing s q₀ q₀ = 1)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ B)
    (hq₁ : ∀ i, ‖q₁ i - q₀ i‖ ≤ δ)
    (hq₂ : ∀ i, ‖q₂ i - q₀ i‖ ≤ δ)
    (hbudget : s * (2 * B * δ + δ ^ 2) < 1 / 2) :
    1 / 2 < scaledPairing s q₁ q₂ := by
  have hnorm := norm_average_mul_star_sub_le_of_uniform_close
    hN q₀ q₁ q₂ hB hδ hq₀ hq₁ hq₂
  have hre : |(average (fun i => q₁ i * star (q₂ i)) -
      average (fun i => q₀ i * star (q₀ i))).re| ≤
      2 * B * δ + δ ^ 2 :=
    (Complex.abs_re_le_norm _).trans hnorm
  have hlower := neg_le_of_abs_le hre
  have hscaled := mul_le_mul_of_nonneg_left hlower hs.le
  unfold scaledPairing at hward ⊢
  rw [Complex.sub_re] at hscaled
  nlinarith

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.External.CEH

open Matrix
open CEHNative.BlockBand.CEH

/-- The strict mixed-pairing inequality forces the CEH cutoff
coefficient (whose transition value is `1/2`) to be exactly one. -/
theorem regularizationCoefficient_eq_one_of_scaled_pairing
    {N : ℕ} {lambda : ℝ} {s : ℝ} (hsqrt : lambda ^ 2 = s)
    (M₁plus M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hpair : 1 / 2 < (s * NTrace (M₁plus * M₂minus)).re) :
    regularizationCoefficient (lambda : ℂ) M₁plus M₂minus = 1 := by
  unfold regularizationCoefficient
  apply cehTheta_of_pos
  rw [show ((lambda : ℂ) ^ 2) = (s : ℂ) by exact_mod_cast hsqrt]
  exact sub_pos.mpr hpair

/-- At theta one the off-diagonal part of the exact CEH `s₂²` definition
vanishes identically.  Any uniform upper bound must therefore control precisely
the displayed base and ordinary-stability terms; no hidden off-term remains. -/
theorem sTwoSq_one_eq {N : ℕ} (lambda : ℂ)
    (M₁plus M₂plus Areg : Matrix (Fin N) (Fin N) ℂ) :
    sTwoSq 1 lambda M₁plus M₂plus Areg =
      let Γ₁ := gammaMatrix M₁plus
      let Γ₂ := gammaMatrix M₂plus
      (NTrace (Γ₁ * Areg * Γ₂ * Aregᴴ)).re +
        ‖lambda‖ ^ 2 *
          ‖NTrace (M₁plus * Areg * Γ₂) *
            NTrace (Γ₁ * Aregᴴ * M₂plus) /
              stabilityDenominator lambda (NTrace (M₁plus * M₂plus))‖ := by
  simp [sTwoSq]

end CEHNative.BlockBand.External.CEH
