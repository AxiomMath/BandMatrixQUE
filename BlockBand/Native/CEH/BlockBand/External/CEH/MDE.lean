module

public import BlockBand.Native.CEH.BlockBand.Published.LocalETHInput
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Finite-dimensional scalar MDE foundations for CEH

This module isolates the deterministic scalar Dyson equation behind CEH (2.4).
The deformation is represented by its real eigenvalues; no regularity, limiting
empirical measure, or pre-packaged MDE solution is assumed.  The normalization is

`Mᵢ(z) = (fᵢ - z - s m(z))⁻¹`,  `m(z) = N⁻¹ ∑ᵢ Mᵢ(z)`.

The lemmas below record the exact finite-dimensional algebra used in CEH Lemma 2.2,
the typical-spacing construction, and the boundary-to-strip adapter.  In particular,
all regular-window consequences take their boundary hypotheses explicitly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

/-- The diagonal (spectral) presentation of a finite-dimensional Hermitian deformation. -/
abbrev DeformationSpectrum (N : ℕ) := Fin N → ℝ

/-- Normalized complex average.  The `N = 0` value is deliberately zero. -/
def average {N : ℕ} (a : Fin N → ℂ) : ℂ :=
  (∑ i, a i) / (N : ℂ)

/-- Normalized real average.  The `N = 0` value is deliberately zero. -/
def averageReal {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  (∑ i, a i) / (N : ℝ)

/-- The diagonal entries of the scalar-MDE resolvent associated with a proposed mean `m`. -/
def entry {N : ℕ} (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ) (i : Fin N) : ℂ :=
  ((f i : ℂ) - z - (s : ℂ) * m)⁻¹

/-- The CEH scalar Dyson equation with the upper-half-plane sign convention. -/
def IsSolution {N : ℕ} (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ) : Prop :=
  m = average (entry f s z m) ∧ 0 < m.im

/-- The positive-height quantity occurring in every scalar MDE denominator. -/
def effectiveHeight (s : ℝ) (z m : ℂ) : ℝ := z.im + s * m.im

/-- CEH self-consistent density in the upper half-plane. -/
def density (m : ℂ) : ℝ := m.im / Real.pi

/-- The scalar version of the diagonal matrix `Γ = Im M / Im m`. -/
def gamma {N : ℕ} (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ) (i : Fin N) : ℝ :=
  (entry f s z m i).im / m.im

/-- The usual scalar stability denominator `1 - s ⟨M²⟩`. -/
def stabilityDenominator {N : ℕ} (f : DeformationSpectrum N)
    (s : ℝ) (z m : ℂ) : ℂ :=
  1 - (s : ℂ) * average (fun i => entry f s z m i ^ 2)

/-- The mixed CEH stability denominator. -/
def mixedStabilityDenominator {N : ℕ} (f : DeformationSpectrum N)
    (s : ℝ) (z₁ m₁ z₂ m₂ : ℂ) : ℂ :=
  1 - (s : ℂ) * average (fun i => entry f s z₁ m₁ i * star (entry f s z₂ m₂ i))

/-- Imaginary parts commute with the normalized finite average. -/
theorem average_im {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ) :
    (average a).im = averageReal (fun i => (a i).im) := by
  have himsum : (∑ i, a i).im = ∑ i, (a i).im := by
    exact map_sum Complex.imAddGroupHom (fun i => a i) Finset.univ
  unfold average averageReal
  simp only [Complex.div_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, Complex.normSq_natCast]
  rw [himsum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

theorem average_const_mul {N : ℕ} (c : ℂ) (a : Fin N → ℂ) :
    average (fun i => c * a i) = c * average a := by
  unfold average
  rw [← Finset.mul_sum]
  ring

@[simp] theorem entry_im {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    (z m : ℂ) (i : Fin N) :
    (entry f s z m i).im =
      effectiveHeight s z m / Complex.normSq ((f i : ℂ) - z - (s : ℂ) * m) := by
  simp [entry, effectiveHeight, Complex.inv_im]
  ring

/-- Every entry has the Herglotz sign as soon as the effective height is positive. -/
theorem entry_im_pos {N : ℕ} (f : DeformationSpectrum N) {s : ℝ}
    {z m : ℂ} (hheight : 0 < effectiveHeight s z m) (i : Fin N) :
    0 < (entry f s z m i).im := by
  rw [entry_im]
  exact div_pos hheight (Complex.normSq_pos.mpr <| by
    intro h
    have him := congrArg Complex.im h
    have hh := hheight
    unfold effectiveHeight at hh
    simp at him
    linarith)

/-- Denominators cannot vanish in the Herglotz regime. -/
theorem denominator_ne_zero {N : ℕ} (f : DeformationSpectrum N) {s : ℝ}
    {z m : ℂ} (hheight : 0 < effectiveHeight s z m) (i : Fin N) :
    (f i : ℂ) - z - (s : ℂ) * m ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hh := hheight
  unfold effectiveHeight at hh
  simp at him
  linarith

/-- Entry analyticity for any analytic scalar mean.  Applied to the unique
implicit MDE mean, this is the entrywise analyticity assertion used in CEH. -/
theorem analyticAt_entry {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    (m : ℂ → ℂ) {z : ℂ} (i : Fin N) (hm : AnalyticAt ℂ m z)
    (hne : (f i : ℂ) - z - (s : ℂ) * m z ≠ 0) :
    AnalyticAt ℂ (fun w => entry f s w (m w) i) z := by
  unfold entry
  apply AnalyticAt.inv
  · fun_prop
  · simpa using hne

/-- Entry continuity, in the form needed for boundary limits. -/
theorem continuousAt_entry {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    (m : ℂ → ℂ) {z : ℂ} (i : Fin N) (hm : ContinuousAt m z)
    (hne : (f i : ℂ) - z - (s : ℂ) * m z ≠ 0) :
    ContinuousAt (fun w => entry f s w (m w) i) z := by
  unfold entry
  fun_prop

/-- Entrywise Ward identity, before normalized averaging. -/
theorem entry_im_eq_height_mul_normSq {N : ℕ} (f : DeformationSpectrum N)
    (s : ℝ) (z m : ℂ) (i : Fin N) :
    (entry f s z m i).im = effectiveHeight s z m * ‖entry f s z m i‖ ^ 2 := by
  rw [entry_im]
  rw [← Complex.sq_norm]
  simp [entry, div_eq_mul_inv]

/-- `Γ` is pointwise positive for an upper-half-plane solution at positive variance. -/
theorem gamma_pos {N : ℕ} (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hs : 0 ≤ s) (hz : 0 < z.im) (hm : 0 < m.im) (i : Fin N) :
    0 < gamma f s z m i := by
  exact div_pos (entry_im_pos f (by simp [effectiveHeight]; positivity) i) hm

/-- The normalized trace of `Γ` is one, stated directly from the MDE equation. -/
theorem average_gamma_eq_one {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hm : IsSolution f s z m) : averageReal (gamma f s z m) = 1 := by
  rcases hm with ⟨heq, hmpos⟩
  have him : m.im = averageReal (fun i => (entry f s z m i).im) :=
    (congrArg Complex.im heq).trans (average_im hN _)
  rw [averageReal]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : ∑ i, gamma f s z m i = (N : ℝ) := by
    simp only [gamma]
    have hentries : ∑ i, (entry f s z m i).im = (N : ℝ) * m.im := by
      unfold averageReal at him
      field_simp at him
      nlinarith
    rw [← Finset.sum_div, hentries]
    field_simp
  rw [hsum]
  exact div_self hNr

/-- Exact averaged imaginary-part/Ward identity.

This is the finite-dimensional identity omitted in the proof of CEH Lemma 2.2:
`Im m = (Im z + s Im m) ⟨|M|²⟩`. -/
theorem imaginaryPart_identity {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z m : ℂ)
    (hm : IsSolution f s z m) :
    m.im = effectiveHeight s z m *
      averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
  rcases hm with ⟨heq, hmpos⟩
  calc
    m.im = averageReal (fun i => (entry f s z m i).im) :=
      (congrArg Complex.im heq).trans (average_im hN _)
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

/-- The averaged squared resolvent lies strictly below `1/s` at positive height. -/
theorem variance_mul_average_normSq_lt_one {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 < z.im) (hm : IsSolution f s z m) :
    s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) < 1 := by
  have hid := imaginaryPart_identity hN f s z m hm
  have hmpos := hm.2
  have havg : 0 ≤ averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
    unfold averageReal
    positivity
  have heff : 0 < effectiveHeight s z m := by
    unfold effectiveHeight
    positivity
  have havgpos : 0 < averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
    nlinarith [hid]
  unfold effectiveHeight at hid
  by_contra h
  have hge : 1 ≤ s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) :=
    le_of_not_gt h
  have hcontra : m.im > m.im := calc
    m.im = z.im * averageReal (fun i => ‖entry f s z m i‖ ^ 2) +
        m.im * (s * averageReal (fun i => ‖entry f s z m i‖ ^ 2)) := by
          nlinarith [hid]
    _ > m.im := by nlinarith
  exact (lt_irrefl _ hcontra)

/-- Norm of a normalized complex average is bounded by the normalized average of norms. -/
theorem norm_average_le {N : ℕ} (hN : 0 < N) (a : Fin N → ℂ) :
    ‖average a‖ ≤ averageReal (fun i => ‖a i‖) := by
  unfold average averageReal
  rw [norm_div, norm_natCast]
  gcongr
  exact norm_sum_le _ _

/-- A useful mixed-average estimate obtained from `2ab ≤ a²+b²`. -/
theorem norm_average_mul_le {N : ℕ} (hN : 0 < N) (a b : Fin N → ℂ) :
    ‖average (fun i => a i * b i)‖ ≤
      (averageReal (fun i => ‖a i‖ ^ 2) +
        averageReal (fun i => ‖b i‖ ^ 2)) / 2 := by
  calc
    ‖average (fun i => a i * b i)‖
        ≤ averageReal (fun i => ‖a i * b i‖) := norm_average_le hN _
    _ ≤ averageReal (fun i => (‖a i‖ ^ 2 + ‖b i‖ ^ 2) / 2) := by
      unfold averageReal
      gcongr with i
      change ‖a i * b i‖ ≤ (‖a i‖ ^ 2 + ‖b i‖ ^ 2) / 2
      rw [norm_mul]
      nlinarith [sq_nonneg (‖a i‖ - ‖b i‖)]
    _ = (averageReal (fun i => ‖a i‖ ^ 2) +
        averageReal (fun i => ‖b i‖ ^ 2)) / 2 := by
      unfold averageReal
      simp_rw [add_div]
      rw [Finset.sum_add_distrib]
      rw [← Finset.sum_div, ← Finset.sum_div]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp

/-- The scalar CEH stability denominator cannot vanish in the upper half-plane. -/
theorem stabilityDenominator_ne_zero {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (hs : 0 < s) (hz : 0 < z.im) (hm : IsSolution f s z m) :
    stabilityDenominator f s z m ≠ 0 := by
  intro hzero
  have heq : (s : ℂ) * average (fun i => entry f s z m i ^ 2) = 1 := by
    simpa [stabilityDenominator] using (sub_eq_zero.mp hzero).symm
  have hnorm : ‖(s : ℂ) * average (fun i => entry f s z m i ^ 2)‖ < 1 := by
    calc
      _ = s * ‖average (fun i => entry f s z m i ^ 2)‖ := by
        rw [norm_mul]
        simp [abs_of_pos hs]
      _ ≤ s * averageReal (fun i => ‖entry f s z m i ^ 2‖) := by
        gcongr
        exact norm_average_le hN _
      _ = s * averageReal (fun i => ‖entry f s z m i‖ ^ 2) := by
        congr 2
        funext i
        exact norm_pow _ _
      _ < 1 := variance_mul_average_normSq_lt_one hN f hs hz hm
  rw [heq, norm_one] at hnorm
  exact (lt_irrefl _ hnorm)

/-- Mixed stability is nonzero for two upper-half-plane spectral parameters.
The second factor may be conjugated (the CEH two-resolvent denominator) or not
(the uniqueness denominator); both have the same norm estimate. -/
theorem mixed_average_norm_lt_inv {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z₁ m₁ z₂ m₂ : ℂ}
    (hs : 0 < s) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂)
    (conjugateSecond : Bool) :
    s * ‖average (fun i => entry f s z₁ m₁ i *
      if conjugateSecond then star (entry f s z₂ m₂ i) else entry f s z₂ m₂ i)‖ < 1 := by
  let a : Fin N → ℂ := entry f s z₁ m₁
  let b : Fin N → ℂ := fun i =>
    if conjugateSecond then star (entry f s z₂ m₂ i) else entry f s z₂ m₂ i
  have hbound := norm_average_mul_le hN a b
  have hb (i : Fin N) : ‖b i‖ = ‖entry f s z₂ m₂ i‖ := by
    by_cases h : conjugateSecond <;> simp [b, h]
  have h₁ := variance_mul_average_normSq_lt_one hN f hs hz₁ hm₁
  have h₂ := variance_mul_average_normSq_lt_one hN f hs hz₂ hm₂
  have hs0 : 0 ≤ s := hs.le
  calc
    s * ‖average (fun i => entry f s z₁ m₁ i *
        if conjugateSecond then star (entry f s z₂ m₂ i) else entry f s z₂ m₂ i)‖
        = s * ‖average (fun i => a i * b i)‖ := rfl
    _ ≤ s * ((averageReal (fun i => ‖a i‖ ^ 2) +
        averageReal (fun i => ‖b i‖ ^ 2)) / 2) := by gcongr
    _ = (s * averageReal (fun i => ‖entry f s z₁ m₁ i‖ ^ 2) +
        s * averageReal (fun i => ‖entry f s z₂ m₂ i‖ ^ 2)) / 2 := by
      simp only [a, hb]
      ring
    _ < 1 := by linarith

/-- The conjugated mixed stability denominator used by CEH is nonzero. -/
theorem mixedStabilityDenominator_ne_zero {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z₁ m₁ z₂ m₂ : ℂ}
    (hs : 0 < s) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : IsSolution f s z₁ m₁) (hm₂ : IsSolution f s z₂ m₂) :
    mixedStabilityDenominator f s z₁ m₁ z₂ m₂ ≠ 0 := by
  intro hzero
  have heq : (s : ℂ) *
      average (fun i => entry f s z₁ m₁ i * star (entry f s z₂ m₂ i)) = 1 := by
    simpa [mixedStabilityDenominator] using (sub_eq_zero.mp hzero).symm
  have hlt := mixed_average_norm_lt_inv hN f hs hz₁ hz₂ hm₁ hm₂ true
  simp only [ite_true] at hlt
  have hnorm := congrArg norm heq
  simp at hnorm
  rw [abs_of_pos hs] at hnorm
  change s * ‖average (fun i =>
    entry f s z₁ m₁ i * star (entry f s z₂ m₂ i))‖ = 1 at hnorm
  nlinarith

/-- Resolvent difference identity for two proposed scalar means. -/
theorem entry_sub_entry {N : ℕ} (f : DeformationSpectrum N)
    {s : ℝ} {z m₁ m₂ : ℂ} (hs : 0 ≤ s) (hz : 0 < z.im)
    (hm₁ : 0 < m₁.im) (hm₂ : 0 < m₂.im) (i : Fin N) :
    entry f s z m₁ i - entry f s z m₂ i =
      (s : ℂ) * (m₁ - m₂) * entry f s z m₁ i * entry f s z m₂ i := by
  have hh₁ : 0 < effectiveHeight s z m₁ := by
    unfold effectiveHeight
    positivity
  have hh₂ : 0 < effectiveHeight s z m₂ := by
    unfold effectiveHeight
    positivity
  have h₁ := denominator_ne_zero f hh₁ i
  have h₂ := denominator_ne_zero f hh₂ i
  unfold entry
  rw [inv_sub_inv' h₁ h₂]
  ring

/-- Uniqueness of the Herglotz scalar-MDE mean at every positive height.
This uses only the equation and positivity, not a structure field asserting uniqueness. -/
theorem solution_unique {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m₁ m₂ : ℂ}
    (hs : 0 < s) (hz : 0 < z.im)
    (hm₁ : IsSolution f s z m₁) (hm₂ : IsSolution f s z m₂) :
    m₁ = m₂ := by
  have hdiff :
      m₁ - m₂ = (s : ℂ) * (m₁ - m₂) *
        average (fun i => entry f s z m₁ i * entry f s z m₂ i) := by
    calc
      m₁ - m₂ =
          average (entry f s z m₁) - average (entry f s z m₂) := by
            exact congrArg₂ (· - ·) hm₁.1 hm₂.1
      _ = average (fun i => entry f s z m₁ i - entry f s z m₂ i) := by
            unfold average
            rw [Finset.sum_sub_distrib]
            ring
      _ = average (fun i => (s : ℂ) * (m₁ - m₂) *
          entry f s z m₁ i * entry f s z m₂ i) := by
            congr 1
            funext i
            exact entry_sub_entry f hs.le hz hm₁.2 hm₂.2 i
      _ = (s : ℂ) * (m₁ - m₂) *
          average (fun i => entry f s z m₁ i * entry f s z m₂ i) := by
            simpa only [mul_assoc] using
              average_const_mul ((s : ℂ) * (m₁ - m₂))
                (fun i => entry f s z m₁ i * entry f s z m₂ i)
  by_contra hne
  let A : ℂ := average (fun i => entry f s z m₁ i * entry f s z m₂ i)
  have hmul : (m₁ - m₂) * ((s : ℂ) * A) = m₁ - m₂ := by
    calc
      (m₁ - m₂) * ((s : ℂ) * A) = (s : ℂ) * (m₁ - m₂) * A := by ring
      _ = m₁ - m₂ := by exact hdiff.symm
  have hsub : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hne
  have hcoeff : (s : ℂ) * A = 1 := by
    apply (mul_left_cancel₀ hsub)
    simpa using hmul
  have hlt := mixed_average_norm_lt_inv hN f hs hz hz hm₁ hm₂ false
  change s * ‖A‖ < 1 at hlt
  have hnorm := congrArg norm hcoeff
  rw [norm_mul, norm_one] at hnorm
  have hsNorm : ‖(s : ℂ)‖ = s := by simp [abs_of_pos hs]
  rw [hsNorm] at hnorm
  change s * ‖A‖ = 1 at hnorm
  nlinarith

/-!
## Typical spacing
-/

/-- The scalar data needed to construct the CEH typical spacing.

For an MDE branch one takes
`q x η = N η ρ(x+iη)`.  The first three fields are precisely the Stieltjes
continuity, strict height monotonicity, and large-height mass-one limit; the
last field is the energy measurability needed for a measurable selector.
No solution or selector is stored in this structure. -/
structure SpacingRegularity (N : ℕ) (q : ℝ → ℝ → ℝ) : Prop where
  continuous_height : ∀ x, Continuous (q x)
  zero_height : ∀ x, q x 0 = 0
  strictMono_height : ∀ x, StrictMonoOn (q x) (Ioi 0)
  atTop_height : ∀ x, Tendsto (q x) atTop (𝓝 ((N : ℝ) / Real.pi))
  measurable_energy : ∀ η, Measurable (fun x => q x η)

/-- The reason CEH assumes `N ≥ 4`: the mass-one large-height limit
`N / π` lies strictly above one. -/
theorem one_lt_dimension_div_pi {N : ℕ} (hN : 4 ≤ N) :
    1 < (N : ℝ) / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  apply (lt_div_iff₀ hpi).2
  have hfour : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [Real.pi_lt_four]

/-- Existence of the positive CEH typical spacing from the Stieltjes
height regularity, for every dimension `N ≥ 4`. -/
theorem exists_typicalSpacing {N : ℕ} (hN : 4 ≤ N)
    {q : ℝ → ℝ → ℝ} (hq : SpacingRegularity N q) (x : ℝ) :
    ∃ η : ℝ, 0 < η ∧ q x η = 1 := by
  have hlim : 1 < (N : ℝ) / Real.pi := one_lt_dimension_div_pi hN
  have hev : ∀ᶠ η : ℝ in atTop, 1 < q x η :=
    (tendsto_order.1 (hq.atTop_height x)).1 1 hlim
  obtain ⟨A, hA⟩ := (eventually_atTop.1 hev)
  let R : ℝ := max A 1
  have hR : 1 < q x R := hA R (le_max_left _ _)
  have hR0 : 0 ≤ R := le_trans (by norm_num) (le_max_right A 1)
  have hmem : (1 : ℝ) ∈ Set.Icc (q x 0) (q x R) := by
    rw [hq.zero_height x]
    exact ⟨by norm_num, hR.le⟩
  obtain ⟨η, hηmem, hη⟩ :=
    (intermediate_value_Icc hR0 (hq.continuous_height x).continuousOn) hmem
  refine ⟨η, ?_, hη⟩
  have hη0 : η ≠ 0 := by
    intro hz
    subst hz
    rw [hq.zero_height x] at hη
    norm_num at hη
  exact lt_of_le_of_ne hηmem.1 (Ne.symm hη0)

/-- Uniqueness of the positive CEH typical spacing. -/
theorem typicalSpacing_unique {N : ℕ} {q : ℝ → ℝ → ℝ}
    (hq : SpacingRegularity N q) {x η₁ η₂ : ℝ}
    (hη₁ : 0 < η₁) (hη₂ : 0 < η₂)
    (heq₁ : q x η₁ = 1) (heq₂ : q x η₂ = 1) : η₁ = η₂ := by
  exact (hq.strictMono_height x).injOn (by simpa) (by simpa) (heq₁.trans heq₂.symm)

/-- The unique positive typical spacing.  This is defined only from the
proved existence theorem, not supplied as part of an MDE input. -/
noncomputable def typicalSpacing (N : ℕ) (hN : 4 ≤ N)
    (q : ℝ → ℝ → ℝ) (hq : SpacingRegularity N q) (x : ℝ) : ℝ :=
  Classical.choose (exists_typicalSpacing hN hq x)

theorem typicalSpacing_pos (N : ℕ) (hN : 4 ≤ N)
    (q : ℝ → ℝ → ℝ) (hq : SpacingRegularity N q) (x : ℝ) :
    0 < typicalSpacing N hN q hq x :=
  (Classical.choose_spec (exists_typicalSpacing hN hq x)).1

theorem typicalSpacing_equation (N : ℕ) (hN : 4 ≤ N)
    (q : ℝ → ℝ → ℝ) (hq : SpacingRegularity N q) (x : ℝ) :
    q x (typicalSpacing N hN q hq x) = 1 :=
  (Classical.choose_spec (exists_typicalSpacing hN hq x)).2

/-- The typical spacing is measurable in energy.  The proof uses the exact
sublevel identity `{η_f < a} = {1 < q(·,a)}` for `a > 0`. -/
theorem measurable_typicalSpacing (N : ℕ) (hN : 4 ≤ N)
    (q : ℝ → ℝ → ℝ) (hq : SpacingRegularity N q) :
    Measurable (typicalSpacing N hN q hq) := by
  apply measurable_of_Iio
  intro a
  by_cases ha : 0 < a
  · have hset :
        typicalSpacing N hN q hq ⁻¹' Iio a =
          (fun x => q x a) ⁻¹' Ioi 1 := by
      ext x
      simp only [mem_preimage, mem_Iio, mem_Ioi]
      constructor
      · intro heta
        have hmono := hq.strictMono_height x
          (by simpa using typicalSpacing_pos N hN q hq x) (by simpa using ha) heta
        rwa [typicalSpacing_equation N hN q hq x] at hmono
      · intro hqa
        by_contra hn
        have haeta : a ≤ typicalSpacing N hN q hq x := le_of_not_gt hn
        rcases haeta.eq_or_lt with heq | hlt
        · subst a
          rw [typicalSpacing_equation N hN q hq x] at hqa
          exact (lt_irrefl _ hqa)
        · have hmono := hq.strictMono_height x (by simpa using ha)
              (by simpa using typicalSpacing_pos N hN q hq x) hlt
          rw [typicalSpacing_equation N hN q hq x] at hmono
          linarith
    rw [hset]
    exact (hq.measurable_energy a) (measurableSet_Ioi)
  · have hset : typicalSpacing N hN q hq ⁻¹' Iio a = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iio, not_lt, mem_empty_iff_false, iff_false]
      exact le_trans (le_of_not_gt ha) (typicalSpacing_pos N hN q hq x).le
    rw [hset]
    exact MeasurableSet.empty

/-!
## Boundary-to-strip and theta-one consequences
-/

/-- CEH's Heaviside cutoff, with the value at zero fixed to one. -/
def theta (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

/-- Real part of the normalized mixed pairing `s ⟨M₁ M₂*⟩`. -/
def scaledPairing {N : ℕ} (s : ℝ) (M₁ M₂ : Fin N → ℂ) : ℝ :=
  s * (average (fun i => M₁ i * star (M₂ i))).re

/-- Explicit deterministic regular-window hypotheses for the CEH theta-one
adapter.  `boundaryWard` is the zero-height imaginary-part identity, while
`stripError` is the quantitative boundary-to-strip continuity estimate.  The
latter must be proved from the source's derivative/compactness hypotheses; it
is not silently bundled into an MDE solution. -/
structure RegularPairingWindow {N : ℕ} (s ε : ℝ)
    (window : Set ℝ) (boundary : ℝ → Fin N → ℂ)
    (strip : ℝ → ℝ → Fin N → ℂ) : Prop where
  variance_pos : 0 < s
  error_small : ε < 1 / 2
  boundaryWard : ∀ x ∈ window, scaledPairing s (boundary x) (boundary x) = 1
  stripError : ∀ x ∈ window, ∀ y ∈ window, ∀ η ζ : ℝ, 0 ≤ η → 0 ≤ ζ →
    |scaledPairing s (strip x η) (strip y ζ) -
      scaledPairing s (boundary x) (boundary x)| ≤ ε

/-- A regular boundary window propagates the CEH pairing strictly above `1/2`
throughout every height covered by its explicit continuity estimate. -/
theorem scaledPairing_gt_half {N : ℕ} {s ε : ℝ}
    {window : Set ℝ} {boundary : ℝ → Fin N → ℂ}
    {strip : ℝ → ℝ → Fin N → ℂ}
    (h : RegularPairingWindow s ε window boundary strip)
    {x y η ζ : ℝ} (hx : x ∈ window) (hy : y ∈ window)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) :
    1 / 2 < scaledPairing s (strip x η) (strip y ζ) := by
  have herr := h.stripError x hx y hy η ζ hη hζ
  rw [h.boundaryWard x hx] at herr
  have hlower : -ε ≤
      scaledPairing s (strip x η) (strip y ζ) - 1 := neg_le_of_abs_le herr
  nlinarith [h.error_small]

/-- Consequently the CEH cutoff is exactly one, not merely bounded. -/
theorem theta_scaledPairing_sub_half_eq_one {N : ℕ} {s ε : ℝ}
    {window : Set ℝ} {boundary : ℝ → Fin N → ℂ}
    {strip : ℝ → ℝ → Fin N → ℂ}
    (h : RegularPairingWindow s ε window boundary strip)
    {x y η ζ : ℝ} (hx : x ∈ window) (hy : y ∈ window)
    (hη : 0 ≤ η) (hζ : 0 ≤ ζ) :
    theta (scaledPairing s (strip x η) (strip y ζ) - 1 / 2) = 1 := by
  simp only [theta, ite_eq_left_iff]
  intro hneg
  have hpos : 0 < scaledPairing s (strip x η) (strip y ζ) - 1 / 2 := by
    nlinarith [scaledPairing_gt_half h hx hy hη hζ]
  exact (hneg hpos.le).elim

end CEHNative.BlockBand.CEH
