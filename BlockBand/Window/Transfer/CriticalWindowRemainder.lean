module

public import BlockBand.Window.Transfer.OutsideMarginWindowLocalization
public import BlockBand.Asymptotics.CriticalSequence
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The critical window remainder

Along critical sequences: `a_{n,W}/√n → 1` and the deterministic majorant
`boundaryRankRemainder → 0` along every `CriticalSequence` with `τ > 0` (any `Q > 1`), plus the
induced decay of the outside expectation. `τ > 0` enters only in the limits.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open Filter Topology

namespace BlockBand.Window.Transfer

/-- The refined-count scale `a_{n,W} = √n + n/W + W^{2/5} log(2W)`. -/
noncomputable def refinedRankScale (p : BlockBand.Parameters) : ℝ :=
  Real.sqrt (p.n : ℝ) + (p.n : ℝ) / (p.W : ℝ) +
    (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * (p.W : ℝ))

/-- The algebra of the ratio `a_{n,W}/√n`. -/
theorem refined_scale_ratio_eq (n W : ℝ) (hn : 0 < n) (hW : 0 < W) :
    (Real.sqrt n + n / W + W ^ (2 / 5 : ℝ) * Real.log (2 * W)) / Real.sqrt n =
      1 + Real.sqrt (n / W) / Real.sqrt W +
        (Real.log (2 * W) / W ^ (1 / 10 : ℝ)) / Real.sqrt (n / W) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hpower : W ^ (1 / 10 : ℝ) * W ^ (2 / 5 : ℝ) = Real.sqrt W := by
    rw [← Real.rpow_add hW, Real.sqrt_eq_rpow]
    norm_num
  have htwo : (n / W) / Real.sqrt n = Real.sqrt (n / W) / Real.sqrt W := by
    rw [Real.sqrt_div hn.le]
    field_simp
    nlinarith [Real.sq_sqrt hn.le, Real.sq_sqrt hW.le]
  have hthree : W ^ (2 / 5 : ℝ) * Real.log (2 * W) / Real.sqrt n =
      (Real.log (2 * W) / W ^ (1 / 10 : ℝ)) / Real.sqrt (n / W) := by
    rw [Real.sqrt_div hn.le]
    have hpowpos := Real.rpow_pos_of_pos hW (1 / 10 : ℝ)
    field_simp
    have hprod := congrArg (fun x : ℝ => Real.log (2 * W) * x) hpower
    nlinarith
  rw [add_div, add_div, div_self hsn.ne', htwo, hthree]

/-- `a_{n,W}/√n → 1` along every critical sequence with ratio `τ > 0`. -/
theorem critical_refined_scale_ratio_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau)
    (htau : 0 < tau) (b : ℝ) (hb : 0 < b) (hbhalf : b < 1 / 2) :
    Tendsto (fun j => refinedRankScale (s.parameters b hb hbhalf j) /
      Real.sqrt (s.n j : ℝ)) atTop (𝓝 1) := by
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hWpos (j) : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hnpos (j) : (0 : ℝ) < s.n j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) (s.n_ge_four j))
  have hRootRatio := Real.continuous_sqrt.continuousAt.tendsto.comp s.ratio_tendsto
  have hInvRoot : Tendsto (fun j => (Real.sqrt (s.W j : ℝ))⁻¹) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)).comp hW
    apply hh.congr
    intro j
    simp only [Function.comp_apply, Real.rpow_neg (hWpos j).le, Real.sqrt_eq_rpow]
  have hSmall := hRootRatio.mul hInvRoot
  have hLog := (isLittleO_log_rpow_atTop (r := 1 / 10) (by norm_num)).tendsto_div_nhds_zero.comp hW
  have hInvPower := (tendsto_rpow_neg_atTop (y := 1 / 10) (by norm_num)).comp hW
  have hLogTwo : Tendsto (fun j => Real.log (2 * (s.W j : ℝ)) / (s.W j : ℝ) ^ (1 / 10 : ℝ))
      atTop (𝓝 0) := by
    have hh := (hInvPower.const_mul (Real.log 2)).add hLog
    simp only [mul_zero, zero_add] at hh
    apply hh.congr
    intro j
    simp only [Function.comp_apply]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (hWpos j).ne', add_div,
      Real.rpow_neg (hWpos j).le]
    ring
  have hLast := hLogTwo.div hRootRatio (Real.sqrt_pos.mpr htau).ne'
  have hTotal := ((tendsto_const_nhds (x := (1 : ℝ))).add hSmall).add hLast
  simp only [mul_zero, zero_div, add_zero] at hTotal
  apply hTotal.congr
  intro j
  unfold refinedRankScale
  change 1 + Real.sqrt ((s.n j : ℝ) / (s.W j : ℝ)) * (Real.sqrt (s.W j : ℝ))⁻¹ +
    (Real.log (2 * (s.W j : ℝ)) / (s.W j : ℝ) ^ (1 / 10 : ℝ)) /
      Real.sqrt ((s.n j : ℝ) / (s.W j : ℝ)) = _
  rw [← div_eq_mul_inv]
  exact (refined_scale_ratio_eq (s.n j : ℝ) (s.W j : ℝ) (hnpos j) (hWpos j)).symm

/-- `√n ≤ a_{n,W}`. -/
theorem refined_rank_scale_ge_sqrt (p : BlockBand.Parameters) :
    Real.sqrt (p.n : ℝ) ≤ refinedRankScale p := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hlog : 0 ≤ Real.log (2 * (p.W : ℝ)) := Real.log_nonneg (by linarith)
  unfold refinedRankScale
  have hratio : 0 ≤ (p.n : ℝ) / (p.W : ℝ) := div_nonneg hn hW.le
  have hterm : 0 ≤ (p.W : ℝ) ^ (2 / 5 : ℝ) * Real.log (2 * (p.W : ℝ)) := by positivity
  linarith

/-- `√n/N → 0` along every critical sequence (using only `W → ∞` and `n ≥ 4`; no positive ratio
is needed). -/
theorem critical_small_rank_scale_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau) :
    Tendsto (fun j => Real.sqrt (s.n j : ℝ) / ((s.n j : ℝ) * (s.W j : ℝ)))
      atTop (𝓝 0) := by
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hInvW := tendsto_inv_atTop_zero.comp hW
  apply squeeze_zero (fun j => by positivity) _ hInvW
  intro j
  have hn : (0 : ℝ) < s.n j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) (s.n_ge_four j))
  have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hn1 : (1 : ℝ) ≤ s.n j := by exact_mod_cast (Nat.le_trans (by norm_num : 1 ≤ 4) (s.n_ge_four j))
  have hroot : Real.sqrt (s.n j : ℝ) ≤ (s.n j : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr hn1)
  rw [div_mul_eq_div_div]
  have hratio : Real.sqrt (s.n j : ℝ) / (s.n j : ℝ) ≤ 1 := (div_le_one hn).mpr hroot
  simpa only [one_div, Function.comp_apply] using div_le_div_of_nonneg_right hratio hWj.le

/-- Factorization of the polynomial remainder `(N/√n)(a/N)^Q` at a positive rank scale `a`. -/
theorem polynomial_rank_payment_eq (p : BlockBand.Parameters) (a Q : ℝ) (ha : 0 < a) :
    ((p.N : ℝ) / Real.sqrt (p.n : ℝ)) * (a / (p.N : ℝ)) ^ Q =
      (a / Real.sqrt (p.n : ℝ)) ^ Q * (Real.sqrt (p.n : ℝ) / (p.N : ℝ)) ^ (Q - 1) := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hs : 0 < Real.sqrt (p.n : ℝ) := Real.sqrt_pos.mpr hn
  have hfactor : a / (p.N : ℝ) =
      (a / Real.sqrt (p.n : ℝ)) * (Real.sqrt (p.n : ℝ) / (p.N : ℝ)) := by field_simp
  rw [hfactor, Real.mul_rpow (by positivity) (by positivity),
    Real.rpow_sub (div_pos hs hN), Real.rpow_one]
  field_simp

/-- The rare-crossing part of the boundary-rank remainder tends to zero for every fixed `Q > 1`
along critical sequences with `τ > 0`, at the refined scale. -/
theorem critical_polynomial_remainder_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau)
    (htau : 0 < tau) (b : ℝ) (hb : 0 < b) (hbhalf : b < 1 / 2) (Q : ℝ) (hQ : 1 < Q) :
    Tendsto (fun j =>
      ((s.parameters b hb hbhalf j).N : ℝ) / Real.sqrt (s.n j : ℝ) *
        (refinedRankScale (s.parameters b hb hbhalf j) / ((s.parameters b hb hbhalf j).N : ℝ)) ^ Q)
      atTop (𝓝 0) := by
  have hRatio := (critical_refined_scale_ratio_tendsto s htau b hb hbhalf).rpow_const (p := Q) (Or.inl (by norm_num))
  have hSmall := (critical_small_rank_scale_tendsto s).rpow_const_nhds_zero (sub_pos.mpr hQ)
  have hh := hRatio.mul hSmall
  simp only [Real.one_rpow, mul_zero] at hh
  apply hh.congr
  intro j
  have hn : (0 : ℝ) < s.n j := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4) (s.n_ge_four j))
  have ha : 0 < refinedRankScale (s.parameters b hb hbhalf j) :=
    (Real.sqrt_pos.mpr hn).trans_le (refined_rank_scale_ge_sqrt (s.parameters b hb hbhalf j))
  simpa only [BlockBand.Parameters.N, BlockBand.CriticalSequence.parameters, Nat.cast_mul] using
    (polynomial_rank_payment_eq (s.parameters b hb hbhalf j) _ Q ha).symm

/-- The Gaussian tail at a fixed gap `d`, multiplied by `N/√n`, at the physical scalar variance
(a finite inequality). -/
theorem fixed_gap_gaussian_remainder_payment (p : BlockBand.Parameters) (d : ℝ) (hd : 0 < d) :
    ((p.N : ℝ) / Real.sqrt (p.n : ℝ)) *
      Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2)) ≤
        (32 * p.c / d ^ 2) * (Real.sqrt (p.n : ℝ) / (p.N : ℝ)) := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hs : 0 < Real.sqrt (p.n : ℝ) := Real.sqrt_pos.mpr hn
  have hg := original_variance_gaussian_rank_payment p 2 1 (Real.sqrt (p.n : ℝ))
    ((p.N : ℝ) * d) d (by norm_num) (by norm_num) (mul_pos hN hd) le_rfl
    (by field_simp; norm_num)
  norm_num only [one_pow, div_one, Real.rpow_two, Real.rpow_one] at hg
  calc
    _ ≤ ((p.N : ℝ) / Real.sqrt (p.n : ℝ)) *
        ((16 * p.c * 2) * (Real.sqrt (p.n : ℝ) / ((p.N : ℝ) * d)) ^ 2) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by field_simp; ring

/-- The normalized Gaussian tail tends to zero along every critical sequence (using only
`W → ∞` and `n ≥ 4`). -/
theorem critical_gaussian_remainder_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau)
    (b : ℝ) (hb : 0 < b) (hbhalf : b < 1 / 2) (d : ℝ) (hd : 0 < d) :
    Tendsto (fun j => ((s.parameters b hb hbhalf j).N : ℝ) / Real.sqrt (s.n j : ℝ) *
      Real.exp (-d ^ 2 / (32 * originalScalarSigma (s.parameters b hb hbhalf j) ^ 2)))
      atTop (𝓝 0) := by
  have hh := (critical_small_rank_scale_tendsto s).const_mul (32 * (1 - 2 * b) / d ^ 2)
  simp only [mul_zero] at hh
  apply squeeze_zero (fun j => by positivity) _ hh
  intro j
  simpa only [BlockBand.Parameters.N, BlockBand.Parameters.c,
    BlockBand.CriticalSequence.parameters, Nat.cast_mul] using
    fixed_gap_gaussian_remainder_payment (s.parameters b hb hbhalf j) d hd

/-- The deterministic boundary majorant at the refined scale; it does not depend on the
observables or on `ε`. -/
noncomputable def boundaryRankRemainder (p : BlockBand.Parameters) (rho d D Q : ℝ) : ℝ :=
  (p.N : ℝ) * scalarKernelPrefactor ((p.N : ℝ) * rho) (originalScalarSigma p) *
    ((2 / d) ^ Q * (D * refinedRankScale p / (p.N : ℝ)) ^ Q +
      Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2)))

/-- The boundary majorant splits into a polynomial boundary-moment term and a scalar Gaussian
term. -/
theorem boundary_rank_remainder_eq (p : BlockBand.Parameters) (rho d D Q : ℝ)
    (hrho : 0 < rho) (hd : 0 < d) (hD : 0 ≤ D) :
    boundaryRankRemainder p rho d D Q =
      (rho * Real.sqrt (2 * Real.pi) * Real.sqrt p.c)⁻¹ *
        ((2 * D / d) ^ Q * (((p.N : ℝ) / Real.sqrt (p.n : ℝ)) *
          (refinedRankScale p / (p.N : ℝ)) ^ Q) +
          ((p.N : ℝ) / Real.sqrt (p.n : ℝ)) *
            Real.exp (-d ^ 2 / (32 * originalScalarSigma p ^ 2))) := by
  have ha : 0 ≤ refinedRankScale p := (Real.sqrt_nonneg _).trans (refined_rank_scale_ge_sqrt p)
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  unfold boundaryRankRemainder
  rw [original_scalar_prefactor p rho hrho]
  have hp : (2 / d) ^ Q * (D * refinedRankScale p / (p.N : ℝ)) ^ Q =
      (2 * D / d) ^ Q * (refinedRankScale p / (p.N : ℝ)) ^ Q := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  rw [hp]
  ring

/-- The two-boundary majorant tends to zero for every fixed `Q > 1` along critical sequences with
`τ > 0`. -/
theorem critical_boundary_rank_remainder_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau)
    (htau : 0 < tau) (b : ℝ) (hb : 0 < b) (hbhalf : b < 1 / 2)
    (rho d D Q : ℝ) (hrho : 0 < rho) (hd : 0 < d) (hD : 0 ≤ D) (hQ : 1 < Q) :
    Tendsto (fun j => boundaryRankRemainder (s.parameters b hb hbhalf j) rho d D Q)
      atTop (𝓝 0) := by
  have hpoly := (critical_polynomial_remainder_tendsto s htau b hb hbhalf Q hQ).const_mul ((2 * D / d) ^ Q)
  have hgauss := critical_gaussian_remainder_tendsto s b hb hbhalf d hd
  have hh := (hpoly.add hgauss).const_mul
    ((rho * Real.sqrt (2 * Real.pi) * Real.sqrt (1 - 2 * b))⁻¹)
  simp only [mul_zero, zero_add] at hh
  apply hh.congr
  intro j
  simpa only [BlockBand.Parameters.c, BlockBand.CriticalSequence.parameters] using
    (boundary_rank_remainder_eq (s.parameters b hb hbhalf j) rho d D Q hrho hd hD).symm

/-- `1/N → 0` along every critical sequence (no lower bound on `n/W` is needed). -/
theorem critical_inverse_dimension_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau) :
    Tendsto (fun j => 1 / ((s.n j : ℝ) * (s.W j : ℝ))) atTop (𝓝 0) := by
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hh := tendsto_inv_atTop_zero.comp hW
  apply squeeze_zero (fun j => by positivity) _ hh
  intro j
  have hn1 : (1 : ℝ) ≤ s.n j := by exact_mod_cast (Nat.le_trans (by norm_num : 1 ≤ 4) (s.n_ge_four j))
  have hWj : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hdim : (s.W j : ℝ) ≤ (s.n j : ℝ) * (s.W j : ℝ) := by nlinarith
  simpa only [Function.comp_apply, one_div] using one_div_le_one_div_of_le hWj hdim

/-- The support-width condition holds eventually along every critical sequence, for fixed `M`. -/
theorem critical_support_width_eventually {tau : ℝ} (s : BlockBand.CriticalSequence tau)
    (b : ℝ) (hb : 0 < b) (hbhalf : b < 1 / 2) (rho M d : ℝ)
    (_hrho : 0 < rho) (hd : 0 < d) :
    ∀ᶠ j in atTop, 4 * (M / (((s.parameters b hb hbhalf j).N : ℝ) * rho)) ≤ d := by
  have hh := (critical_inverse_dimension_tendsto s).const_mul (4 * M / rho)
  simp only [mul_zero] at hh
  have hev := hh.eventually_le_const hd
  apply hev.mono
  intro j hj
  simpa only [BlockBand.Parameters.N, BlockBand.CriticalSequence.parameters, Nat.cast_mul,
    div_mul_eq_div_div] using (show 4 * (M / (((s.n j : ℝ) * (s.W j : ℝ)) * rho)) ≤ d from by
      convert hj using 1; ring)

open MeasureTheory ProbabilityTheory

/-- The complementary-rank expectation (independent of the observables) tends to zero along
critical sequences, from two boundary moments, monotonicity of the ordered ranks and the refined
scale. The state spaces and probability measures may vary with `j`. (For the physical model the
boundary moments come from the refined count.) -/
theorem critical_actual_outside_remainder_tendsto {tau : ℝ} (s : BlockBand.CriticalSequence tau)
    (htau : 0 < tau) (b : ℝ) (hb : 0 < b) (hbhalf : b < 1 / 2)
    (State : ℕ → Type*) [∀ j, MeasurableSpace (State j)]
    (nu : (j : ℕ) → Measure (State j)) (hprob : ∀ j, IsProbabilityMeasure (nu j))
    (X : (j : ℕ) → Fin (s.parameters b hb hbhalf j).N → State j → ℝ)
    (hX : ∀ j i, Measurable (X j i)) (hmono : ∀ j y, Monotone (fun i => X j i y))
    (lo hi : (j : ℕ) → Fin (s.parameters b hb hbhalf j).N) (elo ehi : ℕ → ℝ)
    (w : ℝ → ℝ) (hw : Continuous w) (hcompact : HasCompactSupport w)
    (hunit : ∫ y, w y = 1) (hw0 : ∀ y, 0 ≤ w y)
    (rho M E d D Q : ℝ) (hrho : 0 < rho) (hd : 0 < d) (hD : 0 ≤ D) (hQ : 1 < Q)
    (hsupp : ∀ y, w y ≠ 0 → |y| ≤ M)
    (helo : ∀ j, elo j ≤ E - d) (hehi : ∀ j, E + d ≤ ehi j)
    (hLplo : ∀ j, eLpNorm (fun y => X j (lo j) y - elo j) (ENNReal.ofReal Q) (nu j) ≤
      ENNReal.ofReal (D * refinedRankScale (s.parameters b hb hbhalf j) /
        ((s.parameters b hb hbhalf j).N : ℝ)))
    (hLphi : ∀ j, eLpNorm (fun y => X j (hi j) y - ehi j) (ENNReal.ofReal Q) (nu j) ≤
      ENNReal.ofReal (D * refinedRankScale (s.parameters b hb hbhalf j) /
        ((s.parameters b hb hbhalf j).N : ℝ))) :
    Tendsto (fun j => outsideWindowRemainder (s.parameters b hb hbhalf j) (nu j)
      (X j) w rho E (Finset.Icc (lo j) (hi j))) atTop (𝓝 0) := by
  have hnonneg (j) : 0 ≤ outsideWindowRemainder (s.parameters b hb hbhalf j) (nu j)
      (X j) w rho E (Finset.Icc (lo j) (hi j)) := by
    let : IsProbabilityMeasure (nu j) := hprob j
    exact (outside_window_remainder_integrable_nonneg (s.parameters b hb hbhalf j) (nu j)
      (X j) (hX j) w hw hcompact hunit hw0 rho M E hrho hsupp _).2
  have hmajor := critical_boundary_rank_remainder_tendsto s htau b hb hbhalf rho d D Q hrho hd hD hQ
  apply squeeze_zero' (Eventually.of_forall hnonneg) _ hmajor
  apply (critical_support_width_eventually s b hb hbhalf rho M d hrho hd).mono
  intro j hj
  let : IsProbabilityMeasure (nu j) := hprob j
  have ha : 0 ≤ refinedRankScale (s.parameters b hb hbhalf j) :=
    (Real.sqrt_nonneg _).trans (refined_rank_scale_ge_sqrt _)
  exact outside_remainder_two_boundary_moments (s.parameters b hb hbhalf j) (nu j)
    (X j) (hX j) (hmono j) (lo j) (hi j) (elo j) (ehi j) w hw hcompact hunit hw0
    rho M E d Q (D * refinedRankScale (s.parameters b hb hbhalf j) /
      ((s.parameters b hb hbhalf j).N : ℝ)) hrho hd (lt_trans (by norm_num) hQ)
    (by positivity) hsupp hj (helo j) (hehi j) (hLplo j) (hLphi j)

end BlockBand.Window.Transfer
