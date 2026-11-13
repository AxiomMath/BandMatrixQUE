module

public import BlockBand.Window.Transfer.BulkWindowRankSum

/-!
# Localization outside the bulk margin

The complementary-rank remainder for `s = Icc lo hi` is bounded by
`N B ((2/d)^Q L^Q + exp(-d²/(32σ²)))` using only monotonicity of the ordered locations and
`L^Q` bounds of the two boundary ranks `lo, hi`, with `e_lo ≤ E-d`, `E+d ≤ e_hi`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BlockBand.Window.Transfer

/-- The Gaussian kernel at a fixed deterministic energy gap: if `|x - E| ≥ d/2` and
`4M/scale ≤ d`, then `h(x) ≤ B exp(-d²/(32σ²))`, `B = scalarKernelPrefactor scale σ`. The
statement is deterministic. -/
theorem scalar_kernel_at_fixed_gap (w : ℝ → ℝ) (hw : Continuous w)
    (hcompact : HasCompactSupport w) (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E sigma M d x : ℝ) (hs : 0 < scale) (hsigma : 0 < sigma) (hd : 0 < d)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M) (hwidth : 4 * (M / scale) ≤ d)
    (hgap : d / 2 ≤ |x - E|) :
    scalarConvolution w scale E sigma x ≤ scalarKernelPrefactor scale sigma *
      Real.exp (-d ^ 2 / (32 * sigma ^ 2)) := by
  have hk := (scalar_convolution_bound_continuous w hw hcompact hunit hw0
    scale E sigma M x hs hsigma hsupp).2.2
  have hg : d / 4 ≤ max (|x - E| - M / scale) 0 :=
    (show d / 4 ≤ |x - E| - M / scale by linarith).trans (le_max_left _ _)
  have hsq : (d / 4) ^ 2 ≤ (max (|x - E| - M / scale) 0) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hg 2
  have hexp : -(max (|x - E| - M / scale) 0) ^ 2 / (2 * sigma ^ 2) ≤
      -d ^ 2 / (32 * sigma ^ 2) := by
    calc
      _ ≤ -(d / 4) ^ 2 / (2 * sigma ^ 2) :=
        div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)
      _ = _ := by field_simp; ring
  calc
    _ ≤ Real.exp (-(max (|x - E| - M / scale) 0) ^ 2 / (2 * sigma ^ 2)) /
        (scale * sigma * Real.sqrt (2 * Real.pi)) := hk
    _ ≤ Real.exp (-d ^ 2 / (32 * sigma ^ 2)) /
        (scale * sigma * Real.sqrt (2 * Real.pi)) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by unfold scalarKernelPrefactor; ring

/-- By monotonicity of the ordered locations, the kernel at every outside rank is dominated by
the kernel at a boundary rank; both sides give the same moment and Gaussian bounds. -/
theorem one_sided_scalar_kernel_domination (w : ℝ → ℝ) (hw : Continuous w)
    (hcompact : HasCompactSupport w) (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (scale E sigma M d x z e Q : ℝ) (hs : 0 < scale) (hsigma : 0 < sigma)
    (hd : 0 < d) (hQ : 0 < Q) (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M)
    (hwidth : 4 * (M / scale) ≤ d)
    (hside : (x ≤ z ∧ e ≤ E - d) ∨ (z ≤ x ∧ E + d ≤ e)) :
    scalarConvolution w scale E sigma x ≤ scalarKernelPrefactor scale sigma *
      ((2 / d) ^ Q * |z - e| ^ Q + Real.exp (-d ^ 2 / (32 * sigma ^ 2))) := by
  have hB : 0 ≤ scalarKernelPrefactor scale sigma := by unfold scalarKernelPrefactor; positivity
  by_cases hclose : |z - e| ≤ d / 2
  · have hgap : d / 2 ≤ |x - E| := by
      rcases hside with ⟨hxz, he⟩ | ⟨hzx, he⟩
      · have hz := (abs_le.mp hclose).2
        have hx : x - E ≤ 0 := by linarith
        rw [abs_of_nonpos hx]
        linarith
      · have hz := (abs_le.mp hclose).1
        have hx : 0 ≤ x - E := by linarith
        rw [abs_of_nonneg hx]
        linarith
    exact (scalar_kernel_at_fixed_gap w hw hcompact hunit hw0 scale E sigma M d x
      hs hsigma hd hsupp hwidth hgap).trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity)) hB)
  · have hratio : 1 ≤ (2 / d) * |z - e| := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hd).mpr
      have := lt_of_not_ge hclose
      linarith
    have hpow : 1 ≤ (2 / d) ^ Q * |z - e| ^ Q := by
      rw [← Real.mul_rpow (by positivity) (abs_nonneg _)]
      exact Real.one_le_rpow hratio hQ.le
    exact (scalarConvolution_uniform w hw hcompact hunit hw0 scale E sigma M x
      hs hsigma hsupp).2.trans (by nlinarith [Real.exp_nonneg (-d ^ 2 / (32 * sigma ^ 2))])

variable {State : Type*} [MeasurableSpace State]

/-- The expected outside kernel, from an `L^Q` moment of a boundary rank and the scalar Gaussian
tail, with integrability. -/
theorem one_sided_original_kernel_expectation (p : BlockBand.Parameters)
    (nu : Measure State) [IsProbabilityMeasure nu]
    (X Z : State → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (rho M E d e Q L : ℝ) (hrho : 0 < rho) (hd : 0 < d) (hQ : 0 < Q) (hL : 0 ≤ L)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M)
    (hwidth : 4 * (M / ((p.N : ℝ) * rho)) ≤ d)
    (hside : ∀ y, (X y ≤ Z y ∧ e ≤ E - d) ∨ (Z y ≤ X y ∧ E + d ≤ e))
    (hLp : eLpNorm (fun y => Z y - e) (ENNReal.ofReal Q) nu ≤ ENNReal.ofReal L) :
    (∫ y, scalarConvolution w ((p.N : ℝ) * rho) E (originalScalarSigma p) (X y) ∂nu) ≤
      scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        ((2 / d) ^ Q * L ^ Q + Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2))) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hsigma := originalScalarSigma_pos p
  let B := scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p)
  let tail := Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2))
  have hB : 0 ≤ B := by unfold B scalarKernelPrefactor; positivity
  have hmoment := terminal_moment_of_Lq nu Z hZ e Q L hQ hL hLp
  have hInt := integrable_original_scalar_kernel p nu X hX w hw hcompact hunit hw0 rho M E hrho hsupp
  have hMajor := ((hmoment.1.const_mul ((2 / d) ^ Q)).add (integrable_const tail)).const_mul B
  calc
    _ ≤ ∫ y, B * ((2 / d) ^ Q * |Z y - e| ^ Q + tail) ∂nu :=
      integral_mono hInt hMajor fun y =>
        one_sided_scalar_kernel_domination w hw hcompact hunit hw0 ((p.N : ℝ) * rho)
          E (originalScalarSigma p) M d (X y) (Z y) e Q (mul_pos hN hrho) hsigma
          hd hQ hsupp hwidth (hside y)
    _ = B * ((2 / d) ^ Q * (∫ y, |Z y - e| ^ Q ∂nu) + tail) := by
      rw [integral_const_mul, integral_add (hmoment.1.const_mul _) (integrable_const tail),
        integral_const_mul, integral_const]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_left
      (mul_le_mul_of_nonneg_left hmoment.2
        (Real.rpow_nonneg (show 0 ≤ (2 : ℝ) / d from div_nonneg (by norm_num) hd.le) Q)) tail) hB

/-- The complementary-rank remainder is bounded through two deterministic bulk boundary ranks,
using monotonicity of the ordered locations and their `L^Q` moments. The bound is independent of
the observables and of `ε`, and needs neither outside-rank moments nor a lower bound on `n/W`. -/
theorem outside_remainder_two_boundary_moments (p : BlockBand.Parameters)
    (nu : Measure State) [IsProbabilityMeasure nu]
    (X : Fin p.N → State → ℝ) (hX : ∀ i, Measurable (X i))
    (hmono : ∀ y, Monotone (fun i => X i y))
    (lo hi : Fin p.N) (elo ehi : ℝ)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (rho M E d Q L : ℝ) (hrho : 0 < rho) (hd : 0 < d) (hQ : 0 < Q) (hL : 0 ≤ L)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M)
    (hwidth : 4 * (M / ((p.N : ℝ) * rho)) ≤ d)
    (helo : elo ≤ E - d) (hehi : E + d ≤ ehi)
    (hLplo : eLpNorm (fun y => X lo y - elo) (ENNReal.ofReal Q) nu ≤ ENNReal.ofReal L)
    (hLphi : eLpNorm (fun y => X hi y - ehi) (ENNReal.ofReal Q) nu ≤ ENNReal.ofReal L) :
    outsideWindowRemainder p nu X w rho E (Finset.Icc lo hi) ≤
      (p.N : ℝ) * scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
        ((2 / d) ^ Q * L ^ Q + Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2))) := by
  classical
  let s := Finset.Icc lo hi
  let B := scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
    ((2 / d) ^ Q * L ^ Q + Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2)))
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hsigma := originalScalarSigma_pos p
  have hB : 0 ≤ B := by unfold B scalarKernelPrefactor; positivity
  have hbound (i : Fin p.N) (hout : i ∈ sᶜ) :
      (∫ y, scalarConvolution w ((p.N : ℝ) * rho) E (originalScalarSigma p) (X i y) ∂nu) ≤ B := by
    have hor : i < lo ∨ hi < i := by
      simpa only [s, Finset.mem_compl, Finset.mem_Icc, not_and_or, not_le] using hout
    rcases hor with hlow | hhigh
    · exact one_sided_original_kernel_expectation p nu (X i) (X lo) (hX i) (hX lo)
        w hw hcompact hunit hw0 rho M E d elo Q L hrho hd hQ hL hsupp hwidth
        (fun y => Or.inl ⟨hmono y hlow.le, helo⟩) hLplo
    · exact one_sided_original_kernel_expectation p nu (X i) (X hi) (hX i) (hX hi)
        w hw hcompact hunit hw0 rho M E d ehi Q L hrho hd hQ hL hsupp hwidth
        (fun y => Or.inr ⟨hmono y hhigh.le, hehi⟩) hLphi
  calc
    _ = ∑ i ∈ sᶜ, ∫ y, scalarConvolution w ((p.N : ℝ) * rho)
        E (originalScalarSigma p) (X i y) ∂nu :=
      integral_finsetSum sᶜ (fun i hout =>
        integrable_original_scalar_kernel p nu (X i) (hX i) w hw hcompact hunit hw0 rho M E hrho hsupp)
    _ ≤ ∑ i ∈ sᶜ, B := Finset.sum_le_sum fun i hout => hbound i hout
    _ = (sᶜ.card : ℝ) * B := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (p.N : ℝ) * B := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show (sᶜ).card ≤ p.N from by
        simpa only [Fintype.card_fin] using Finset.card_le_univ sᶜ)) hB
    _ = _ := by unfold B; ring

end BlockBand.Window.Transfer
