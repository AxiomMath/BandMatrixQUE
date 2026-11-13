module

public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEMatrixAdapter
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Quantitative CEH bounds for the finite-dimensional Hermitian MDE

The computations of the bounds on the solution `M` of the matrix Dyson equation and on its
density (CEH Lemma 2.2): Ward identities, stability bounds for the ordinary and mixed
denominators, the operator-norm bound and the density bound `ρ ≤ (π √s)⁻¹`. The estimates are
uniform in the Hermitian deformation; consequently an explicit polynomial deformation bound is
accepted by the final package but is not used by any estimate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- Exact scalar Ward identity, solved for the averaged squared norm. -/
theorem averageReal_normSq_eq_im_div_effectiveHeight {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hh : 0 < effectiveHeight s z m) (hm : IsSolution f s z m) :
    averageReal (fun i => ‖entry f s z m i‖ ^ 2) =
      m.im / effectiveHeight s z m := by
  have hid := imaginaryPart_identity hN f s z m hm
  apply (eq_div_iff hh.ne').2
  nlinarith

/-- Every scalar resolvent entry is bounded by the reciprocal effective height. -/
theorem norm_entry_le_inv_effectiveHeight {N : ℕ} (f : DeformationSpectrum N)
    {s : ℝ} {z m : ℂ} (hh : 0 < effectiveHeight s z m) (i : Fin N) :
    ‖entry f s z m i‖ ≤ (effectiveHeight s z m)⁻¹ := by
  let d : ℂ := (f i : ℂ) - z - (s : ℂ) * m
  have hd : d ≠ 0 := denominator_ne_zero f hh i
  have habs : |d.im| ≤ ‖d‖ := Complex.abs_im_le_norm d
  have hdim : d.im = - effectiveHeight s z m := by
    simp [d, effectiveHeight]
    ring
  have hdimeq : |d.im| = effectiveHeight s z m := by
    rw [hdim, abs_neg, abs_of_pos hh]
  have hdnorm : effectiveHeight s z m ≤ ‖d‖ := by simpa [hdimeq] using habs
  unfold entry
  change ‖d⁻¹‖ ≤ (effectiveHeight s z m)⁻¹
  rw [norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le hh hdnorm

/-- CEH's first bound is an equality in the scalar spectral representation. -/
theorem averageReal_normSq_ceh_identity {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) :
    averageReal (fun i => ‖entry f s z
      (upperBranch hN f hs z) i‖ ^ 2) =
      (Real.pi * density (upperBranch hN f hs z)) /
        (z.im + s * (Real.pi * density (upperBranch hN f hs z))) := by
  have hm := upperBranch_isSolution hN f hs hz
  have hh : 0 < effectiveHeight s z (upperBranch hN f hs z) := by
    unfold effectiveHeight
    nlinarith [hm.2]
  rw [averageReal_normSq_eq_im_div_effectiveHeight hN f hh hm]
  unfold density effectiveHeight
  field_simp [Real.pi_ne_zero]

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix Set
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-- An entry with an optional adjoint, used to name all four CEH constellations. -/
def adjointedEntry {N : ℕ} (takeAdjoint : Bool) (f : DeformationSpectrum N)
    (s : ℝ) (z m : ℂ) (i : Fin N) : ℂ :=
  if takeAdjoint then star (entry f s z m i) else entry f s z m i

/-- Stability denominator for any of the four choices of adjoints. -/
def fourAdjointDenominator {N : ℕ} (a₁ a₂ : Bool)
    (f : DeformationSpectrum N) (s : ℝ) (z₁ m₁ z₂ m₂ : ℂ) : ℂ :=
  1 - (s : ℂ) * average (fun i =>
    adjointedEntry a₁ f s z₁ m₁ i * adjointedEntry a₂ f s z₂ m₂ i)

/-- Reciprocal arithmetic-mean inequality in the two-variable form used below. -/
theorem inv_average_le_average_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((a + b) / 2)⁻¹ ≤ (a⁻¹ + b⁻¹) / 2 := by
  rw [inv_le_comm₀ (by positivity) (by positivity)]
  field_simp [ha.ne', hb.ne']
  nlinarith [sq_nonneg (a - b)]

/-- Uniform reverse-triangle estimate for every adjoint constellation. -/
theorem norm_fourAdjointDenominator_ge {N : ℕ} (hN : 0 < N)
    (a₁ a₂ : Bool) (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ) :
    1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) ≤
      ‖fourAdjointDenominator a₁ a₂ f s z₁ m₁ z₂ m₂‖ := by
  let A := average (fun i =>
    adjointedEntry a₁ f s z₁ m₁ i * adjointedEntry a₂ f s z₂ m₂ i)
  have hadj (a : Bool) (z m : ℂ) (i : Fin N) :
      ‖adjointedEntry a f s z m i‖ = ‖entry f s z m i‖ := by
    cases a <;> simp [adjointedEntry]
  have haverage : ‖A‖ ≤
      (averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2 := by
    have h := norm_average_mul_le hN
      (adjointedEntry a₁ f s z₁ m₁) (adjointedEntry a₂ f s z₂ m₂)
    simpa only [A, hadj] using h
  have hnorm : ‖(s : ℂ) * A‖ ≤ s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) := by
    rw [norm_mul]
    simp [abs_of_nonneg hs]
    gcongr
  calc
    1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)
        ≤ 1 - ‖(s : ℂ) * A‖ := sub_le_sub_left hnorm 1
    _ ≤ ‖(1 : ℂ) - (s : ℂ) * A‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) ((s : ℂ) * A)
    _ = ‖fourAdjointDenominator a₁ a₂ f s z₁ m₁ z₂ m₂‖ := rfl

/-- Source-shaped mixed inverse estimate in terms of its positive Ward margin. -/
theorem norm_fourAdjointDenominator_inv_le {N : ℕ} (hN : 0 < N)
    (a₁ a₂ : Bool) (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ)
    (hmargin : 0 < 1 - s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)) :
    ‖(fourAdjointDenominator a₁ a₂ f s z₁ m₁ z₂ m₂)⁻¹‖ ≤
      (1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2))⁻¹ := by
  rw [norm_inv]
  simpa [one_div] using one_div_le_one_div_of_le hmargin
    (norm_fourAdjointDenominator_ge hN a₁ a₂ f hs z₁ m₁ z₂ m₂)

/-- No adjoints: the `M₁M₂` constellation. -/
theorem norm_denominator_noAdj_noAdj_inv_le {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ) (hmargin : 0 < 1 - s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)) :
    ‖(fourAdjointDenominator false false f s z₁ m₁ z₂ m₂)⁻¹‖ ≤
      (1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2))⁻¹ :=
  norm_fourAdjointDenominator_inv_le hN false false f hs z₁ m₁ z₂ m₂ hmargin

/-- Adjoint on the second factor: the `M₁M₂*` constellation. -/
theorem norm_denominator_noAdj_adj_inv_le {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ) (hmargin : 0 < 1 - s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)) :
    ‖(fourAdjointDenominator false true f s z₁ m₁ z₂ m₂)⁻¹‖ ≤
      (1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2))⁻¹ :=
  norm_fourAdjointDenominator_inv_le hN false true f hs z₁ m₁ z₂ m₂ hmargin

/-- Adjoint on the first factor: the `M₁*M₂` constellation. -/
theorem norm_denominator_adj_noAdj_inv_le {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ) (hmargin : 0 < 1 - s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)) :
    ‖(fourAdjointDenominator true false f s z₁ m₁ z₂ m₂)⁻¹‖ ≤
      (1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2))⁻¹ :=
  norm_fourAdjointDenominator_inv_le hN true false f hs z₁ m₁ z₂ m₂ hmargin

/-- Adjoints on both factors: the `M₁*M₂*` constellation. -/
theorem norm_denominator_adj_adj_inv_le {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ) (hmargin : 0 < 1 - s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)) :
    ‖(fourAdjointDenominator true true f s z₁ m₁ z₂ m₂)⁻¹‖ ≤
      (1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2))⁻¹ :=
  norm_fourAdjointDenominator_inv_le hN true true f hs z₁ m₁ z₂ m₂ hmargin

/-- CEH's source-shaped two-body inverse estimate, uniformly for all four
adjoint constellations. -/
theorem upperBranch_fourAdjoint_inverse_ceh_bound {N : ℕ} (hN : 0 < N)
    (a₁ a₂ : Bool) (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖(fourAdjointDenominator a₁ a₂ f s z₁ (upperBranch hN f hs z₁)
      z₂ (upperBranch hN f hs z₂))⁻¹‖ ≤
      1 + (Real.pi * s / 2) *
        (density (upperBranch hN f hs z₁) / z₁.im +
          density (upperBranch hN f hs z₂) / z₂.im) := by
  let m₁ := upperBranch hN f hs z₁
  let m₂ := upperBranch hN f hs z₂
  have hm₁ := upperBranch_isSolution hN f hs hz₁
  have hm₂ := upperBranch_isSolution hN f hs hz₂
  have hcontract₁ := variance_mul_average_normSq_lt_one hN f hs hz₁ hm₁
  have hcontract₂ := variance_mul_average_normSq_lt_one hN f hs hz₂ hm₂
  have hmargin : 0 < 1 - s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) := by
    dsimp only [m₁, m₂] at *
    linarith
  have hinv := norm_fourAdjointDenominator_inv_le hN a₁ a₂ f hs.le
    z₁ m₁ z₂ m₂ hmargin
  have hA₁ := averageReal_normSq_ceh_identity hN f hs hz₁
  have hA₂ := averageReal_normSq_ceh_identity hN f hs hz₂
  dsimp only [m₁, m₂] at hinv hA₁ hA₂ ⊢
  rw [hA₁, hA₂] at hinv
  have hd₁ : 0 < z₁.im + s * (Real.pi *
      density (upperBranch hN f hs z₁)) := by
    have hp := (upperBranch_isSolution hN f hs hz₁).2
    have hpi : Real.pi * density (upperBranch hN f hs z₁) =
        (upperBranch hN f hs z₁).im := by
      simp [density]
      field_simp [Real.pi_ne_zero]
    rw [hpi]
    positivity
  have hd₂ : 0 < z₂.im + s * (Real.pi *
      density (upperBranch hN f hs z₂)) := by
    have hp := (upperBranch_isSolution hN f hs hz₂).2
    have hpi : Real.pi * density (upperBranch hN f hs z₂) =
        (upperBranch hN f hs z₂).im := by
      simp [density]
      field_simp [Real.pi_ne_zero]
    rw [hpi]
    positivity
  have hρ₁ : 0 ≤ density (upperBranch hN f hs z₁) :=
    (div_nonneg (upperBranch_isSolution hN f hs hz₁).2.le Real.pi_pos.le)
  have hρ₂ : 0 ≤ density (upperBranch hN f hs z₂) :=
    (div_nonneg (upperBranch_isSolution hN f hs hz₂).2.le Real.pi_pos.le)
  have hrewrite :
      1 - s *
        ((Real.pi * density (upperBranch hN f hs z₁) /
            (z₁.im + s * (Real.pi * density (upperBranch hN f hs z₁))) +
          Real.pi * density (upperBranch hN f hs z₂) /
            (z₂.im + s * (Real.pi * density (upperBranch hN f hs z₂)))) / 2) =
      (z₁.im / (z₁.im + s * (Real.pi *
          density (upperBranch hN f hs z₁))) +
        z₂.im / (z₂.im + s * (Real.pi *
          density (upperBranch hN f hs z₂)))) / 2 := by
    field_simp [hd₁.ne', hd₂.ne']
    ring
  rw [hrewrite] at hinv
  refine hinv.trans ((inv_average_le_average_inv
    (div_pos hz₁ hd₁) (div_pos hz₂ hd₂)).trans ?_)
  field_simp [hz₁.ne', hz₂.ne', hd₁.ne', hd₂.ne']
  ring_nf
  exact le_rfl

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix Set
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-- Real parts commute with a nonempty normalized finite average. -/
theorem average_re {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ) :
    (average a).re = averageReal (fun i => (a i).re) := by
  have hresum : (∑ i, a i).re = ∑ i, (a i).re := by
    exact map_sum Complex.reAddGroupHom (fun i => a i) Finset.univ
  unfold average averageReal
  simp only [Complex.div_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, Complex.normSq_natCast]
  rw [hresum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Finite-dimensional Jensen inequality for the normalized real average. -/
theorem sq_averageReal_le_averageReal_sq {N : ℕ} (_hN : 0 < N)
    (a : Fin N → ℝ) :
    averageReal a ^ 2 ≤ averageReal (fun i => a i ^ 2) := by
  unfold averageReal
  have h := sum_div_card_sq_le_sum_sq_div_card
    (s := Finset.univ) (f := a)
  simpa using h

/-- Exact real part underlying the ordinary CEH stability estimate. -/
theorem stabilityDenominator_re_eq {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ) :
    (stabilityDenominator f s z m).re =
      1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) +
        2 * s * averageReal (fun i => (entry f s z m i).im ^ 2) := by
  unfold stabilityDenominator
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [average_re hN]
  have hpoint :
      averageReal (fun i => (entry f s z m i ^ 2).re) =
        averageReal (fun i => ‖entry f s z m i‖ ^ 2) -
          2 * averageReal (fun i => (entry f s z m i).im ^ 2) := by
    have hf : (fun i => (entry f s z m i ^ 2).re) =
        fun i => ‖entry f s z m i‖ ^ 2 -
          2 * (entry f s z m i).im ^ 2 := by
      funext i
      rw [Complex.sq_norm]
      simp only [pow_two, Complex.mul_re]
      simp [Complex.normSq_apply]
      ring
    rw [hf]
    unfold averageReal
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hpoint]
  ring

/-- The full ordinary CEH stability bound, with explicit constants.

This retains the substantive `2 s ⟨(Im M)²⟩` contribution instead of merely
using nonvanishing or the bare-height term. -/
theorem stabilityDenominator_full_lower_bound {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s) {z m : ℂ}
    (hm : m = average (entry f s z m)) :
    1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) +
        2 * s * m.im ^ 2 ≤
      ‖stabilityDenominator f s z m‖ := by
  have hjensen := sq_averageReal_le_averageReal_sq hN
    (fun i => (entry f s z m i).im)
  have hmim : m.im =
      averageReal (fun i => (entry f s z m i).im) :=
    (congrArg Complex.im hm).trans (average_im hN _)
  rw [← hmim] at hjensen
  have hre := stabilityDenominator_re_eq hN f s z m
  calc
    1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) +
          2 * s * m.im ^ 2
        ≤ 1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) +
          2 * s * averageReal (fun i => (entry f s z m i).im ^ 2) := by
            gcongr
    _ = (stabilityDenominator f s z m).re := hre.symm
    _ ≤ |(stabilityDenominator f s z m).re| := le_abs_self _
    _ ≤ ‖stabilityDenominator f s z m‖ :=
      Complex.abs_re_le_norm _

/-- Upper-branch stability bound with constants `1` and `2π²`:
`|1-s⟨M²⟩| ≥ η/(η+sπρ) + 2π²sρ²`. -/
theorem upperBranch_stability_full_ceh_bound {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 0 < z.im) :
    z.im / (z.im + s * (Real.pi *
        density (upperBranch hN f hs z))) +
      2 * Real.pi ^ 2 * s * density (upperBranch hN f hs z) ^ 2 ≤
      ‖stabilityDenominator f s z (upperBranch hN f hs z)‖ := by
  let m := upperBranch hN f hs z
  have hm := upperBranch_isSolution hN f hs hz
  have hh : effectiveHeight s z m ≠ 0 := by
    unfold effectiveHeight
    nlinarith [hm.2]
  have hfull := stabilityDenominator_full_lower_bound hN f hs.le hm.1
  have hbase :
      1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) =
        z.im / effectiveHeight s z m := by
    have hid := imaginaryPart_identity hN f s z m hm
    apply (eq_div_iff hh).2
    unfold effectiveHeight at hid ⊢
    ring_nf at hid ⊢
    linear_combination s * hid
  rw [hbase] at hfull
  have hpi : Real.pi * density m = m.im := by
    simp [density, m]
    field_simp [Real.pi_ne_zero]
  dsimp only [m] at hfull hpi ⊢
  rw [hpi]
  unfold density
  convert hfull using 1
  simp [effectiveHeight]
  field_simp [Real.pi_ne_zero]

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open scoped ComplexConjugate

/-- The Ward identity only uses the Dyson equation, not a choice of half-plane. -/
theorem algebraic_imaginaryPart_identity {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ)
    (hm : m = average (entry f s z m)) :
    m.im = effectiveHeight s z m *
      averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
  calc
    m.im = averageReal (fun i => (entry f s z m i).im) :=
      (congrArg Complex.im hm).trans (average_im hN _)
    _ = averageReal
        (fun i => effectiveHeight s z m * ‖entry f s z m i‖ ^ 2) := by
      congr 1
      funext i
      exact entry_im_eq_height_mul_normSq f s z m i
    _ = effectiveHeight s z m *
        averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
      unfold averageReal
      rw [← Finset.mul_sum]
      ring

/-- The Ward contraction is quantitative in either open half-plane. -/
theorem variance_mul_average_normSq_lt_one_of_sameSign {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ} (_hs : 0 < s)
    (hm : m = average (entry f s z m))
    (hsign : (0 < z.im ∧ 0 < m.im) ∨ (z.im < 0 ∧ m.im < 0)) :
    s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) < 1 := by
  let A := averageReal (fun i => ‖entry f s z m i‖ ^ 2)
  have hA : 0 ≤ A := by
    unfold A averageReal
    positivity
  have hid := algebraic_imaginaryPart_identity hN f s z m hm
  change m.im = (z.im + s * m.im) * A at hid
  have hApos : 0 < A := by
    apply lt_of_le_of_ne hA
    intro hzero
    rw [hzero.symm] at hid
    rcases hsign with hsign | hsign <;> linarith
  rcases hsign with ⟨hz, hmpos⟩ | ⟨hz, hmneg⟩
  · by_contra h
    have hge : 1 ≤ s * A := le_of_not_gt h
    have hzmul : 0 < z.im * A := mul_pos hz hApos
    have hmterm : m.im ≤ m.im * (s * A) :=
      (le_mul_iff_one_le_right hmpos).2 hge
    nlinarith [hid]
  · by_contra h
    have hge : 1 ≤ s * A := le_of_not_gt h
    have hzmul : z.im * A < 0 := mul_neg_of_neg_of_pos hz hApos
    have hmterm : m.im * (s * A) ≤ m.im := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hmneg.le (sub_nonneg.mpr hge)]
    nlinarith [hid]

/-- Reverse-triangle quantitative bound for the ordinary stability denominator. -/
theorem norm_stabilityDenominator_ge {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s) (z m : ℂ) :
    1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) ≤
      ‖stabilityDenominator f s z m‖ := by
  let A := average (fun i => entry f s z m i ^ 2)
  have haverage :
      ‖A‖ ≤ averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
    calc
      ‖A‖ ≤ averageReal (fun i => ‖entry f s z m i ^ 2‖) := by
        exact norm_average_le hN (fun i => entry f s z m i ^ 2)
      _ = averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
        congr 2
        funext i
        exact norm_pow _ _
  have hsabs : ‖(s : ℂ) * A‖ ≤ |s| *
      averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
    rw [norm_mul]
    simp
    gcongr
  calc
    1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2)
        ≤ 1 - ‖(s : ℂ) * A‖ := by
          rw [sub_le_sub_iff_left]
          simpa [abs_of_nonneg hs] using hsabs
    _ ≤ ‖(1 : ℂ) - (s : ℂ) * A‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) ((s : ℂ) * A)
    _ = ‖stabilityDenominator f s z m‖ := rfl

/-- The quantitative stability margin is exactly the ratio of bare to
self-consistent height. -/
theorem one_sub_variance_mul_average_eq_height_ratio {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hm : m = average (entry f s z m))
    (hh : effectiveHeight s z m ≠ 0) :
    1 - s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) =
      z.im / effectiveHeight s z m := by
  have hid := algebraic_imaginaryPart_identity hN f s z m hm
  apply (eq_div_iff hh).2
  unfold effectiveHeight at hid ⊢
  ring_nf at hid ⊢
  linear_combination s * hid

/-- Quantitative reverse-triangle bound for CEH's conjugated mixed denominator. -/
theorem norm_mixedStabilityDenominator_ge {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 ≤ s)
    (z₁ m₁ z₂ m₂ : ℂ) :
    1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) ≤
      ‖mixedStabilityDenominator f s z₁ m₁ z₂ m₂‖ := by
  let A := average (fun i =>
    entry f s z₁ m₁ i * star (entry f s z₂ m₂ i))
  have haverage : ‖A‖ ≤
      (averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2 := by
    have h := norm_average_mul_le hN (entry f s z₁ m₁)
      (fun i => star (entry f s z₂ m₂ i))
    simpa [A] using h
  have hnorm : ‖(s : ℂ) * A‖ ≤ s *
      ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) := by
    rw [norm_mul]
    simp [abs_of_nonneg hs]
    gcongr
  calc
    1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2)
        ≤ 1 - ‖(s : ℂ) * A‖ := sub_le_sub_left hnorm 1
    _ ≤ ‖(1 : ℂ) - (s : ℂ) * A‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) ((s : ℂ) * A)
    _ = ‖mixedStabilityDenominator f s z₁ m₁ z₂ m₂‖ := rfl

/-- A positive quantitative lower bound for mixed stability in either half-plane. -/
theorem mixedStabilityDenominator_quantitative_of_sameSign {N : ℕ}
    (hN : 0 < N) (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ m₁ z₂ m₂ : ℂ}
    (hm₁ : m₁ = average (entry f s z₁ m₁))
    (hm₂ : m₂ = average (entry f s z₂ m₂))
    (hsign₁ : (0 < z₁.im ∧ 0 < m₁.im) ∨ (z₁.im < 0 ∧ m₁.im < 0))
    (hsign₂ : (0 < z₂.im ∧ 0 < m₂.im) ∨ (z₂.im < 0 ∧ m₂.im < 0)) :
    0 < 1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) ∧
      1 - s * ((averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2) ≤
        ‖mixedStabilityDenominator f s z₁ m₁ z₂ m₂‖ := by
  have h₁ := variance_mul_average_normSq_lt_one_of_sameSign
    hN f hs hm₁ hsign₁
  have h₂ := variance_mul_average_normSq_lt_one_of_sameSign
    hN f hs hm₂ hsign₂
  constructor
  · linarith
  · exact norm_mixedStabilityDenominator_ge hN f hs.le z₁ m₁ z₂ m₂

/-- Upper-branch quantitative mixed stability, including the conjugated CEH case. -/
theorem upperBranch_mixedStability_quantitative {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    0 < 1 - s * ((averageReal (fun i => ‖entry f s z₁
        (upperBranch hN f hs z₁) i‖ ^ 2) +
      averageReal (fun i => ‖entry f s z₂
        (upperBranch hN f hs z₂) i‖ ^ 2)) / 2) ∧
    1 - s * ((averageReal (fun i => ‖entry f s z₁
        (upperBranch hN f hs z₁) i‖ ^ 2) +
      averageReal (fun i => ‖entry f s z₂
        (upperBranch hN f hs z₂) i‖ ^ 2)) / 2) ≤
      ‖mixedStabilityDenominator f s z₁ (upperBranch hN f hs z₁)
        z₂ (upperBranch hN f hs z₂)‖ := by
  have hm₁ := upperBranch_isSolution hN f hs hz₁
  have hm₂ := upperBranch_isSolution hN f hs hz₂
  exact mixedStabilityDenominator_quantitative_of_sameSign hN f hs
    hm₁.1 hm₂.1 (Or.inl ⟨hz₁, hm₁.2⟩) (Or.inl ⟨hz₂, hm₂.2⟩)

/-- Lower-branch quantitative mixed stability, obtained without an existence certificate. -/
theorem lowerBranch_mixedStability_quantitative {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im < 0) (hz₂ : z₂.im < 0) :
    0 < 1 - s * ((averageReal (fun i => ‖entry f s z₁
        (lowerBranch hN f hs z₁) i‖ ^ 2) +
      averageReal (fun i => ‖entry f s z₂
        (lowerBranch hN f hs z₂) i‖ ^ 2)) / 2) ∧
    1 - s * ((averageReal (fun i => ‖entry f s z₁
        (lowerBranch hN f hs z₁) i‖ ^ 2) +
      averageReal (fun i => ‖entry f s z₂
        (lowerBranch hN f hs z₂) i‖ ^ 2)) / 2) ≤
      ‖mixedStabilityDenominator f s z₁ (lowerBranch hN f hs z₁)
        z₂ (lowerBranch hN f hs z₂)‖ := by
  have hm₁ := lowerBranch_isLowerSolution hN f hs hz₁
  have hm₂ := lowerBranch_isLowerSolution hN f hs hz₂
  exact mixedStabilityDenominator_quantitative_of_sameSign hN f hs
    hm₁.1 hm₂.1 (Or.inr ⟨hz₁, hm₁.2⟩) (Or.inr ⟨hz₂, hm₂.2⟩)

/-- Quantitative ordinary stability on the upper branch. -/
theorem upperBranch_stability_quantitative {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 0 < z.im) :
    0 < 1 - s * averageReal (fun i =>
        ‖entry f s z (upperBranch hN f hs z) i‖ ^ 2) ∧
      1 - s * averageReal (fun i =>
        ‖entry f s z (upperBranch hN f hs z) i‖ ^ 2) ≤
      ‖stabilityDenominator f s z (upperBranch hN f hs z)‖ := by
  have hm := upperBranch_isSolution hN f hs hz
  constructor
  · have h := variance_mul_average_normSq_lt_one_of_sameSign hN f hs hm.1
      (Or.inl ⟨hz, hm.2⟩)
    linarith
  · exact norm_stabilityDenominator_ge hN f hs.le z (upperBranch hN f hs z)

/-- Quantitative ordinary stability on the conjugated lower branch. -/
theorem lowerBranch_stability_quantitative {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : z.im < 0) :
    0 < 1 - s * averageReal (fun i =>
        ‖entry f s z (lowerBranch hN f hs z) i‖ ^ 2) ∧
      1 - s * averageReal (fun i =>
        ‖entry f s z (lowerBranch hN f hs z) i‖ ^ 2) ≤
      ‖stabilityDenominator f s z (lowerBranch hN f hs z)‖ := by
  have hm := lowerBranch_isLowerSolution hN f hs hz
  constructor
  · have h := variance_mul_average_normSq_lt_one_of_sameSign hN f hs hm.1
      (Or.inr ⟨hz, hm.2⟩)
    linarith
  · exact norm_stabilityDenominator_ge hN f hs.le z (lowerBranch hN f hs z)

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- Unitary spectral transport preserves the operator norm. -/
theorem norm_spectralLift {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (d : Fin N → ℂ) :
    ‖spectralLift hF d‖ = ‖d‖ := by
  unfold spectralLift
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

/-- Exact CEH operator-norm bound for the Hermitian branch. -/
theorem norm_hermitianMDEBranch_le {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 0 < z.im) :
    ‖hermitianMDEBranch hF hs z‖ ≤
      (z.im + s * (Real.pi *
        localETHMDEDensity (hermitianMDEBranch hF hs z)))⁻¹ := by
  let m := upperBranch hN (hermitianSpectrum hF) hs z
  have hm := upperBranch_isSolution hN (hermitianSpectrum hF) hs hz
  have hh : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  rw [localETHMDEDensity_eq_density hF hN hs hz]
  have hpi : Real.pi * density m = m.im := by
    simp [density, m]
    field_simp [Real.pi_ne_zero]
  rw [hpi, hermitianMDEBranch, dite_eq_left hN,
    hermitianMDEMean_of_im_pos hF hN hs hz, norm_spectralLift]
  change ‖entry (hermitianSpectrum hF) s z m‖ ≤ (effectiveHeight s z m)⁻¹
  rw [pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hh.le)]
  intro i
  exact norm_entry_le_inv_effectiveHeight (hermitianSpectrum hF) hh i

/-- The averaged squared norm is bounded by the reciprocal squared effective height. -/
theorem averageReal_normSq_le_inv_sq_effectiveHeight {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hh : 0 < effectiveHeight s z m) :
    averageReal (fun i => ‖entry f s z m i‖ ^ 2) ≤
      (effectiveHeight s z m)⁻¹ ^ 2 := by
  unfold averageReal
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  apply (div_le_iff₀ hNr).2
  calc
    ∑ i, ‖entry f s z m i‖ ^ 2 ≤
        ∑ _i : Fin N, (effectiveHeight s z m)⁻¹ ^ 2 := by
          gcongr with i
          exact norm_entry_le_inv_effectiveHeight f hh i
    _ = (effectiveHeight s z m)⁻¹ ^ 2 * (N : ℝ) := by simp [mul_comm]

/-- Schwarz consequence used in the CEH density bound, in squared form. -/
theorem variance_mul_im_sq_le_one {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) {m : ℂ} (hm : IsSolution f s z m) :
    s * m.im ^ 2 ≤ 1 := by
  have hh : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    nlinarith [hm.2]
  have hid := imaginaryPart_identity hN f s z m hm
  have havg := averageReal_normSq_le_inv_sq_effectiveHeight hN f hh
  have hmle : m.im ≤ (effectiveHeight s z m)⁻¹ := by
    calc
      m.im = effectiveHeight s z m *
          averageReal (fun i => ‖entry f s z m i‖ ^ 2) := hid
      _ ≤ effectiveHeight s z m * ((effectiveHeight s z m)⁻¹ ^ 2) := by
        gcongr
      _ = (effectiveHeight s z m)⁻¹ := by field_simp [hh.ne']
  have hseff : s * m.im ≤ effectiveHeight s z m := by
    unfold effectiveHeight
    linarith
  have hmprod : s * m.im ^ 2 ≤ m.im * effectiveHeight s z m := by
    nlinarith [hm.2]
  have hmheight : m.im * effectiveHeight s z m ≤ 1 := by
    calc
      m.im * effectiveHeight s z m = effectiveHeight s z m * m.im := by ring
      _ ≤ effectiveHeight s z m * (effectiveHeight s z m)⁻¹ :=
        mul_le_mul_of_nonneg_left hmle hh.le
      _ = 1 := by field_simp [hh.ne']
  exact hmprod.trans hmheight

/-- Exact source-shaped density bound `ρ ≤ (π √s)⁻¹`. -/
theorem density_le_inv_pi_sqrt {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) {m : ℂ} (hm : IsSolution f s z m) :
    density m ≤ (Real.pi * Real.sqrt s)⁻¹ := by
  have hsq := variance_mul_im_sq_le_one hN f hs hz hm
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hmle : m.im ≤ (Real.sqrt s)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hsqrt]
    have hnonneg : 0 ≤ m.im * Real.sqrt s := mul_nonneg hm.2.le hsqrt.le
    apply (sq_le_sq₀ hnonneg zero_le_one).mp
    rw [mul_pow, Real.sq_sqrt hs.le, one_pow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
  unfold density
  rw [inv_eq_one_div, div_le_div_iff₀ Real.pi_pos (mul_pos Real.pi_pos hsqrt)]
  have hmul : m.im * Real.sqrt s ≤ 1 := (le_div_iff₀ hsqrt).mp (by simpa [one_div] using hmle)
  nlinarith [Real.pi_pos]

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- Spectral transport is complex-linear. -/
theorem spectralLift_smul {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (c : ℂ) (d : Fin N → ℂ) :
    spectralLift hF (fun i => c * d i) = c • spectralLift hF d := by
  unfold spectralLift
  rw [← map_smul]
  apply congrArg (Unitary.conjStarAlgAut ℂ (LocalETHMatrix N) hF.eigenvectorUnitary)
  ext i j
  simp [Matrix.diagonal, smul_eq_mul]

/-- Spectral transport commutes with conjugate transpose. -/
theorem star_spectralLift {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (d : Fin N → ℂ) :
    star (spectralLift hF d) = spectralLift hF (fun i => star (d i)) := by
  unfold spectralLift
  rw [← map_star]
  apply congrArg (Unitary.conjStarAlgAut ℂ (LocalETHMatrix N) hF.eigenvectorUnitary)
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, Matrix.star_apply]
  · simp [Matrix.diagonal, Matrix.star_apply, hij, Ne.symm hij]

/-- The matrix imaginary-part Ward identity, transported from every scalar entry. -/
theorem imPart_hermitianMDEBranch_eq {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 0 < z.im) :
    localETHImPart (hermitianMDEBranch hF hs z) =
      ((effectiveHeight s z (upperBranch hN (hermitianSpectrum hF) hs z) : ℝ) : ℂ) •
        (star (hermitianMDEBranch hF hs z) * hermitianMDEBranch hF hs z) := by
  let f := hermitianSpectrum hF
  let m := upperBranch hN f hs z
  rw [hermitianMDEBranch, dite_eq_left hN,
    hermitianMDEMean_of_im_pos hF hN hs hz]
  have him := smul_imPart_spectralLift hF 1 (entry f s z m)
  have him' : localETHImPart (spectralLift hF
      (entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z))) =
      spectralLift hF (fun i => ((entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z) i).im : ℂ)) := by
    simpa [f, m] using him
  rw [him', star_spectralLift]
  dsimp [f, m] at *
  have hmul :
      spectralLift hF (fun i =>
        (starRingEnd ℂ) (entry (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) i)) *
        spectralLift hF
          (entry (hermitianSpectrum hF) s z
            (upperBranch hN (hermitianSpectrum hF) hs z)) =
      spectralLift hF (fun i =>
        (starRingEnd ℂ) (entry (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) i) *
        entry (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) i) := by
    unfold spectralLift
    rw [← map_mul]
    apply congrArg (Unitary.conjStarAlgAut ℂ (LocalETHMatrix N) hF.eigenvectorUnitary)
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal, Matrix.mul_apply]
    · simp [Matrix.diagonal, Matrix.mul_apply, hij]
  rw [hmul]
  change spectralLift hF (fun i => ((entry _ _ _ _ i).im : ℂ)) =
    (effectiveHeight s z (upperBranch hN (hermitianSpectrum hF) hs z) : ℂ) •
      spectralLift hF (fun i =>
        (starRingEnd ℂ) (entry (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) i) *
        entry (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) i)
  rw [← spectralLift_smul]
  apply congrArg (spectralLift hF)
  funext i
  rw [entry_im_eq_height_mul_normSq]
  push_cast
  rw [Complex.conj_mul']

/-- Normalized-trace form of the Ward identity (`⟨|M|²⟩`). -/
theorem normalizedTrace_star_mul_hermitianMDEBranch {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    Conventions.normalizedTrace
      (star (hermitianMDEBranch hF hs z) * hermitianMDEBranch hF hs z) =
      (averageReal (fun i => ‖entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z) i‖ ^ 2) : ℂ) := by
  rw [hermitianMDEBranch, dite_eq_left hN,
    hermitianMDEMean_of_im_pos hF hN hs hz, star_spectralLift]
  rw [normalizedTrace_spectralLift_mul]
  unfold average averageReal
  have hsum : (∑ i, star (entry (hermitianSpectrum hF) s z
      (upperBranch hN (hermitianSpectrum hF) hs z) i) *
      entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z) i) =
      ∑ i, ((‖entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z) i‖ ^ 2 : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    change (starRingEnd ℂ) (entry (hermitianSpectrum hF) s z
      (upperBranch hN (hermitianSpectrum hF) hs z) i) *
      entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z) i =
      ((‖entry (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z) i‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.conj_mul']
    norm_cast
  rw [hsum]
  apply Complex.ext <;> simp

/-- Matrix normalized-trace Ward identity with its exact effective-height factor. -/
theorem matrix_imaginaryPart_Ward_identity {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 0 < z.im) :
    ((upperBranch hN (hermitianSpectrum hF) hs z).im : ℂ) =
      (effectiveHeight s z (upperBranch hN (hermitianSpectrum hF) hs z) : ℂ) *
        Conventions.normalizedTrace
          (star (hermitianMDEBranch hF hs z) * hermitianMDEBranch hF hs z) := by
  rw [normalizedTrace_star_mul_hermitianMDEBranch hF hN hs hz]
  exact_mod_cast imaginaryPart_identity hN (hermitianSpectrum hF) s z
    (upperBranch hN (hermitianSpectrum hF) hs z)
    (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz)

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix Set
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-- CEH Lemma 2.2's normalized Hilbert–Schmidt estimate, here as an equality.
The normalized Hilbert–Schmidt square is the normalized trace of `MᴴM`. -/
theorem normalizedHilbertSchmidt_ceh_identity {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    Conventions.normalizedTrace
        (star (hermitianMDEBranch hF hs z) * hermitianMDEBranch hF hs z) =
      ((Real.pi * localETHMDEDensity (hermitianMDEBranch hF hs z)) /
        (z.im + s * (Real.pi *
          localETHMDEDensity (hermitianMDEBranch hF hs z))) : ℂ) := by
  rw [normalizedTrace_star_mul_hermitianMDEBranch hF hN hs hz]
  rw [localETHMDEDensity_eq_density hF hN hs hz]
  exact_mod_cast averageReal_normSq_ceh_identity hN
    (hermitianSpectrum hF) hs hz

/-- Source-shaped quantitative stability bound
`η / (η + s πρ) ≤ |1 - s⟨M²⟩|`. -/
theorem upperBranch_stability_height_ratio {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    z.im / (z.im + s * (Real.pi *
      localETHMDEDensity (hermitianMDEBranch hF hs z))) ≤
      ‖stabilityDenominator (hermitianSpectrum hF) s z
        (upperBranch hN (hermitianSpectrum hF) hs z)‖ := by
  let m := upperBranch hN (hermitianSpectrum hF) hs z
  have hm := upperBranch_isSolution hN (hermitianSpectrum hF) hs hz
  have hh : effectiveHeight s z m ≠ 0 := by
    unfold effectiveHeight
    nlinarith [hm.2]
  rw [localETHMDEDensity_eq_density hF hN hs hz]
  have hpi : Real.pi * density m = m.im := by
    simp [density, m]
    field_simp [Real.pi_ne_zero]
  rw [hpi]
  change z.im / effectiveHeight s z m ≤
    ‖stabilityDenominator (hermitianSpectrum hF) s z m‖
  rw [← one_sub_variance_mul_average_eq_height_ratio hN
    (hermitianSpectrum hF) hm.1 hh]
  exact norm_stabilityDenominator_ge hN (hermitianSpectrum hF) hs.le z m

/-- A proposition collecting the exact finite-dimensional quantitative content
of CEH Lemma 2.2 at an upper-half-plane spectral parameter. -/
def CEHMDEQuantitativePackage {N : ℕ} (hN : 0 < N)
    {F : LocalETHMatrix N} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    (z : ℂ) : Prop :=
  localETHImPart (hermitianMDEBranch hF hs z) =
      (effectiveHeight s z
        (upperBranch hN (hermitianSpectrum hF) hs z) : ℂ) •
        (star (hermitianMDEBranch hF hs z) * hermitianMDEBranch hF hs z) ∧
  Conventions.normalizedTrace
      (star (hermitianMDEBranch hF hs z) * hermitianMDEBranch hF hs z) =
    ((Real.pi * localETHMDEDensity (hermitianMDEBranch hF hs z)) /
      (z.im + s * (Real.pi *
        localETHMDEDensity (hermitianMDEBranch hF hs z))) : ℂ) ∧
  ‖hermitianMDEBranch hF hs z‖ ≤
    (z.im + s * (Real.pi *
      localETHMDEDensity (hermitianMDEBranch hF hs z)))⁻¹ ∧
  localETHMDEDensity (hermitianMDEBranch hF hs z) ≤
    (Real.pi * Real.sqrt s)⁻¹ ∧
  z.im / (z.im + s * (Real.pi *
      localETHMDEDensity (hermitianMDEBranch hF hs z))) ≤
    ‖stabilityDenominator (hermitianSpectrum hF) s z
      (upperBranch hN (hermitianSpectrum hF) hs z)‖ ∧
  z.im / (z.im + s * (Real.pi *
      localETHMDEDensity (hermitianMDEBranch hF hs z))) +
      2 * Real.pi ^ 2 * s *
        localETHMDEDensity (hermitianMDEBranch hF hs z) ^ 2 ≤
    ‖stabilityDenominator (hermitianSpectrum hF) s z
      (upperBranch hN (hermitianSpectrum hF) hs z)‖

/-- The complete quantitative package is uniform in the Hermitian deformation.
The source's polynomial deformation hypothesis is made explicit, although none
of these global upper-half-plane estimates consumes it. -/
theorem cehMDEQuantitativePackage {N : ℕ} (hN : 0 < N)
    (κ C : ℝ) {s : ℝ} (hs : 0 < s) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (_hbound : LocalETHDeformationBound κ C s F)
    {z : ℂ} (hz : 0 < z.im) :
    CEHMDEQuantitativePackage hN hF hs z := by
  refine ⟨imPart_hermitianMDEBranch_eq hF hN hs hz,
    normalizedHilbertSchmidt_ceh_identity hF hN hs hz,
    norm_hermitianMDEBranch_le hF hN hs hz, ?_, ?_, ?_⟩
  · rw [localETHMDEDensity_eq_density hF hN hs hz]
    exact density_le_inv_pi_sqrt hN (hermitianSpectrum hF) hs hz
      (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz)
  · exact upperBranch_stability_height_ratio hF hN hs hz
  · rw [localETHMDEDensity_eq_density hF hN hs hz]
    exact upperBranch_stability_full_ceh_bound hN
      (hermitianSpectrum hF) hs hz

/-- Strip/window form of the package.  The energy window and polynomial
deformation quantifiers are explicit; the bounds are stronger than a
regular-window assertion because they hold at every positive height. -/
theorem cehMDEQuantitativePackage_on_window {N : ℕ} (hN : 0 < N)
    (κ C E₀ r : ℝ) {s : ℝ} (hs : 0 < s) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hbound : LocalETHDeformationBound κ C s F)
    {x η : ℝ} (_hx : x ∈ Ioo (E₀ - r) (E₀ + r)) (hη : 0 < η) :
    CEHMDEQuantitativePackage hN hF hs
      ((x : ℂ) + (η : ℂ) * Complex.I) := by
  apply cehMDEQuantitativePackage hN κ C hs hF hbound
  simp
  exact hη

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix Set

/-- The explicit right side of CEH's two-body stability inverse estimate. -/
def mixedInverseControl (s : ℝ) (z₁ z₂ m₁ m₂ : ℂ) : ℝ :=
  1 + (Real.pi * s / 2) * (density m₁ / z₁.im + density m₂ / z₂.im)

/-- Named `M₁M₂` specialization of the source-shaped mixed inverse bound. -/
theorem upperBranch_noAdj_noAdj_inverse_ceh_bound {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖(fourAdjointDenominator false false f s z₁ (upperBranch hN f hs z₁)
      z₂ (upperBranch hN f hs z₂))⁻¹‖ ≤
      mixedInverseControl s z₁ z₂
        (upperBranch hN f hs z₁) (upperBranch hN f hs z₂) := by
  exact upperBranch_fourAdjoint_inverse_ceh_bound hN false false f hs hz₁ hz₂

/-- Named `M₁M₂*` specialization of the source-shaped mixed inverse bound. -/
theorem upperBranch_noAdj_adj_inverse_ceh_bound {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖(fourAdjointDenominator false true f s z₁ (upperBranch hN f hs z₁)
      z₂ (upperBranch hN f hs z₂))⁻¹‖ ≤
      mixedInverseControl s z₁ z₂
        (upperBranch hN f hs z₁) (upperBranch hN f hs z₂) := by
  exact upperBranch_fourAdjoint_inverse_ceh_bound hN false true f hs hz₁ hz₂

/-- Named `M₁*M₂` specialization of the source-shaped mixed inverse bound. -/
theorem upperBranch_adj_noAdj_inverse_ceh_bound {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖(fourAdjointDenominator true false f s z₁ (upperBranch hN f hs z₁)
      z₂ (upperBranch hN f hs z₂))⁻¹‖ ≤
      mixedInverseControl s z₁ z₂
        (upperBranch hN f hs z₁) (upperBranch hN f hs z₂) := by
  exact upperBranch_fourAdjoint_inverse_ceh_bound hN true false f hs hz₁ hz₂

/-- Named `M₁*M₂*` specialization of the source-shaped mixed inverse bound. -/
theorem upperBranch_adj_adj_inverse_ceh_bound {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    ‖(fourAdjointDenominator true true f s z₁ (upperBranch hN f hs z₁)
      z₂ (upperBranch hN f hs z₂))⁻¹‖ ≤
      mixedInverseControl s z₁ z₂
        (upperBranch hN f hs z₁) (upperBranch hN f hs z₂) := by
  exact upperBranch_fourAdjoint_inverse_ceh_bound hN true true f hs hz₁ hz₂

/-- From a regular-boundary-window hypothesis to the unconditional positive-strip package.
It draws no new conclusion at height zero. -/
theorem cehMDEQuantitativePackage_of_regularBoundaryWindow {N : ℕ}
    (hN : 0 < N) (κ C E₀ r c K : ℝ) {s : ℝ} (hs : 0 < s)
    {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (hbound : LocalETHDeformationBound κ C s F)
    (_hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    {x η : ℝ} (hx : x ∈ Ioo (E₀ - r) (E₀ + r)) (hη : 0 < η) :
    CEHMDEQuantitativePackage hN hF hs
      ((x : ℂ) + (η : ℂ) * Complex.I) :=
  cehMDEQuantitativePackage_on_window hN κ C E₀ r hs hF
    hbound hx hη

/-- The unconditional finite-dimensional CEH MDE foundation, collected.

The branch and uniqueness fields include `N = 0`. Analyticity and quantitative
trace estimates are stated conditional on `0 < N`, which is the exact
non-vacuous dimension hypothesis. The window field concerns positive height
only and asserts no boundary value at `η = 0`. -/
structure CEHMDEFoundation {N : ℕ} (F : LocalETHMatrix N)
    (hF : F.IsHermitian) (s : ℝ) (hs : 0 < s) : Prop where
  branch : IsLocalETHMDEBranch s F
    (hermitianMDEBranch hF hs)
  unique : ∀ z : ℂ, z.im ≠ 0 →
    ∃! M : LocalETHMatrix N, IsLocalETHMDESolution s F z M
  analytic_upper : ∀ _hN : 0 < N, ∀ z : ℂ, 0 < z.im →
    ∀ i j : Fin N,
      AnalyticAt ℂ (fun w => hermitianMDEBranch hF hs w i j) z
  analytic_lower : ∀ _hN : 0 < N, ∀ z : ℂ, z.im < 0 →
    ∀ i j : Fin N,
      AnalyticAt ℂ (fun w => hermitianMDEBranch hF hs w i j) z
  quantitative : ∀ hN : 0 < N, ∀ κ C : ℝ,
    LocalETHDeformationBound κ C s F →
    ∀ z : ℂ, 0 < z.im →
      CEHMDEQuantitativePackage hN hF hs z
  regularWindowAdapter : ∀ hN : 0 < N, ∀ κ C E₀ r : ℝ,
    LocalETHDeformationBound κ C s F →
    ∀ x η : ℝ, x ∈ Ioo (E₀ - r) (E₀ + r) → 0 < η →
      CEHMDEQuantitativePackage hN hF hs
        ((x : ℂ) + (η : ℂ) * Complex.I)
  regularBoundaryWindowAdapter : ∀ hN : 0 < N,
    ∀ κ C E₀ r c K : ℝ, LocalETHDeformationBound κ C s F →
    LocalETHRegularBoundaryWindow s (hermitianMDEBranch hF hs) E₀ r c K →
    ∀ x η : ℝ, x ∈ Ioo (E₀ - r) (E₀ + r) → 0 < η →
      CEHMDEQuantitativePackage hN hF hs
        ((x : ℂ) + (η : ℂ) * Complex.I)

/-- All clauses of `CEHMDEFoundation` follow from Hermiticity and positive
variance, without a given solution, branch, or regularity certificate. -/
theorem cehMDEFoundation {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) :
    CEHMDEFoundation F hF s hs := by
  refine ⟨hermitianMDEBranch_isLocalETHMDEBranch hF hs,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact existsUnique_isLocalETHMDESolution hF hs hz
  · intro hN z hz i j
    exact analyticAt_hermitianMDEBranch_apply_of_im_pos hF hN hs hz i j
  · intro hN z hz i j
    exact analyticAt_hermitianMDEBranch_apply_of_im_neg hF hN hs hz i j
  · intro hN κ C hbound z hz
    exact cehMDEQuantitativePackage hN κ C hs hF hbound hz
  · intro hN κ C E₀ r hbound x η hx hη
    exact cehMDEQuantitativePackage_on_window hN κ C E₀ r hs hF
      hbound hx hη
  · intro hN κ C E₀ r c K hbound hregular x η hx hη
    exact cehMDEQuantitativePackage_of_regularBoundaryWindow hN
      κ C E₀ r c K hs hF hbound hregular hx hη

end CEHNative.BlockBand.CEH
