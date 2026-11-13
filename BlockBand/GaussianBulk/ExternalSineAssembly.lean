module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineRescale

/-!
# The Laplace clause of the external-source sine-kernel theorem

`ExternalSineKernel` is the first conjunct of `Internal.Contracts.Inputs.ExternalSine`: the
kernel asymptotic (a continuous kernel converging, after a real gauge, to the sine kernel) and
the mean density. `externalSine_of_kernel` derives the full statement `ExternalSine` from it and
the factorial-count theorem `PSSS.SourceContract`.

Law: `deformedGUELaw N t F hF` (`F + √t G_N`, Johansson coordinates at `S = t/N`). Uniformity of the
Laplace clause: for fixed `A, tLo ≤ tHi, v, [ELo, EHi]`, a nonnegative `f ∈ C_c(ℝ)` and `δ > 0`,
one `N₀` serves every `N ≥ N₀`, Hermitian `F` with `‖F‖ ≤ N^A` (Euclidean operator norm),
`t ∈ [tLo, tHi]`, `E ∈ [ELo, EHi]` and boundary MDE solution `M` with `Im⟨M⟩ ≥ v`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Set Finset Filter
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator

/-- The kernel and mean-density clauses of the external-source sine-kernel theorem: the first
conjunct of `Internal.Contracts.Inputs.ExternalSine`. -/
def ExternalSineKernel : Prop :=
  ∀ (A tLo tHi v ELo EHi L : ℝ), 0 < tLo → tLo ≤ tHi → 0 < v →
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian), ‖F‖ ≤ (N : ℝ) ^ A →
      ∀ (t : ℝ≥0), (t : ℝ) ∈ Icc tLo tHi → ∀ E ∈ Icc ELo EHi,
      ∀ M : Matrix (Fin N) (Fin N) ℂ, IsBoundaryMDE (t : ℝ) F E M →
        v ≤ (CEH.normalizedTrace M).im →
        ∃ (Kern : ℝ → ℝ → ℂ) (h : ℝ → ℝ), Continuous (Function.uncurry Kern) ∧
          (∀ k : ℕ, k ≤ N → deformedFactorialCorrelation N t F hF k =
            volume.withDensity (fun x : Fin k → ℝ =>
              ENNReal.ofReal (Matrix.det (fun i j => Kern (x i) (x j))).re)) ∧
          (∀ ξ ∈ Icc (-L) L, ∀ ζ ∈ Icc (-L) L,
            ‖Complex.exp (-(h ξ : ℂ)) *
                Kern (E + ξ / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi)))
                  (E + ζ / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi))) *
                Complex.exp (h ζ : ℂ) / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi)) -
              (sineKernel ξ ζ : ℂ)‖ ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ∧
          ‖Kern E E / (N : ℝ) - ((CEH.normalizedTrace M).im / Real.pi : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 2)

/-- One order `k < K₁`: the finite term is within `ε (2L)^k` of the sine term, given entrywise
closeness `η` of the gauged rescaled kernel to the sine kernel on `[-L, L]` and the
determinant tolerance `η ↦ ε` at order `k`. -/
theorem term_close {k : ℕ} (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ x, x ∉ Icc (-L) L → f x = 0)
    (Kern : ℝ → ℝ → ℂ) (hKc : Continuous (Function.uncurry Kern)) (h : ℝ → ℝ) (E s : ℝ)
    (ε η : ℝ)
    (hdet : ∀ (A : Matrix (Fin k) (Fin k) ℂ) (B : Matrix (Fin k) (Fin k) ℝ),
      (∀ i j, |B i j| ≤ 1) → (∀ i j, ‖A i j - (B i j : ℂ)‖ ≤ η) → ‖A.det - (B.det : ℂ)‖ ≤ ε)
    (hasym : ∀ ξ ∈ Icc (-L) L, ∀ ζ ∈ Icc (-L) L,
      ‖Complex.exp (-(h ξ : ℂ)) * Kern (E + ξ / s) (E + ζ / s) * Complex.exp (h ζ : ℂ) /
          (s : ℂ) - (sineKernel ξ ζ : ℂ)‖ ≤ η) :
    |(∫ ξ : Fin k → ℝ, (∏ j, laplaceWeight f (ξ j)) *
        max ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re) 0) - sineTerm f k| ≤
      ε * (2 * L) ^ k := by
  set u : (Fin k → ℝ) → ℝ := fun ξ => (∏ j, laplaceWeight f (ξ j)) *
    max ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re) 0 with hu
  set w : (Fin k → ℝ) → ℝ := fun x => Matrix.det (fun i j : Fin k =>
    sineKernel (x i) (x j)) * ∏ i : Fin k, (1 - Real.exp (-f (x i))) with hw
  have hφ0 := laplaceWeight_nonneg hf
  have hφ1 := laplaceWeight_le_one (⇑f)
  have hφs : ∀ y, y ∉ Icc (-L) L → laplaceWeight f y = 0 := fun y hy => by
    simp [laplaceWeight, hsupp y hy]
  -- integrability of `u` (continuous, supported in the box)
  have hucont : Continuous u := by
    refine (continuous_finsetProd _ fun j _ =>
      (continuous_laplaceWeight (map_continuous f)).comp (continuous_apply j)).mul ?_
    exact (continuous_const.mul (Complex.continuous_re.comp
      (continuous_microKernel_det Kern hKc E s))).max continuous_const
  have hprod0 : ∀ ξ : Fin k → ℝ, ξ ∉ box k L → ∏ j, laplaceWeight f (ξ j) = 0 := by
    intro ξ hξ
    obtain ⟨i, hi⟩ : ∃ i, ξ i ∉ Icc (-L) L := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hξ ((mem_box_iff ξ).mpr hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hφs _ hi)
  have hu_int : Integrable u volume := by
    refine hucont.integrable_of_hasCompactSupport (HasCompactSupport.intro (K := box k L) isCompact_Icc ?_)
    intro ξ hξ
    simp only [hu, hprod0 ξ hξ, zero_mul]
  have hw_int : Integrable w volume := (sineTerm_nonneg_le f hf hL hsupp k).1
  have hind_int : Integrable ((box k L).indicator (1 : (Fin k → ℝ) → ℝ)) volume :=
    (integral_le_box hL _ ((measurable_one.indicator (measurableSet_box k L)).aestronglyMeasurable)
      (fun x => by by_cases hx : x ∈ box k L <;> simp [hx]) (fun x => le_rfl)).1
  -- pointwise estimate
  have hpt : ∀ ξ, |u ξ - w ξ| ≤ ε * (box k L).indicator 1 ξ := by
    intro ξ
    by_cases hξ : ξ ∈ box k L
    · rw [indicator_of_mem hξ, Pi.one_apply, mul_one]
      have hξi := (mem_box_iff ξ).mp hξ
      set Amat : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i j =>
        Complex.exp (-((h (ξ i) : ℝ) : ℂ)) * microKernel Kern E s ξ i j *
          Complex.exp ((h (ξ j) : ℝ) : ℂ) / (s : ℂ) with hA
      have hclose := hdet Amat (sineMatrix ξ) (fun i j => Real.abs_sinc_le_one _)
        (fun i j => hasym (ξ i) (hξi i) (ξ j) (hξi j))
      have hAdet : Amat.det = (((s⁻¹) ^ k : ℝ) : ℂ) * (microKernel Kern E s ξ).det := by
        rw [hA, det_gauge_div (microKernel Kern E s ξ) (fun i => ((h (ξ i) : ℝ) : ℂ)) (s : ℂ)]
        push_cast
        rfl
      have hre : |(s⁻¹) ^ k * (microKernel Kern E s ξ).det.re - (sineMatrix ξ).det| ≤ ε := by
        have h1 := (Complex.abs_re_le_norm (Amat.det - ((sineMatrix ξ).det : ℂ))).trans hclose
        rwa [Complex.sub_re, hAdet, Complex.re_ofReal_mul, Complex.ofReal_re] at h1
      have hsd := sineMatrix_det_nonneg ξ
      have hmax : |max ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re) 0 - (sineMatrix ξ).det| ≤ ε := by
        have := abs_max_sub_max_le_abs ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re)
          (sineMatrix ξ).det 0
        rw [max_eq_left hsd] at this
        exact this.trans hre
      have huw : u ξ - w ξ = (∏ j, laplaceWeight f (ξ j)) *
          (max ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re) 0 - (sineMatrix ξ).det) := by
        rw [show (sineMatrix ξ).det = Matrix.det (fun i j => sineKernel (ξ i) (ξ j)) from rfl]
        simp only [hu, hw, laplaceWeight]
        ring
      have hP0 : 0 ≤ ∏ j, laplaceWeight f (ξ j) := Finset.prod_nonneg fun j _ => hφ0 _
      have hP1 : ∏ j, laplaceWeight f (ξ j) ≤ 1 :=
        Finset.prod_le_one₀ (fun j _ => hφ0 _) fun j _ => hφ1 _
      rw [huw, abs_mul, abs_of_nonneg hP0]
      calc _ ≤ 1 * ε := mul_le_mul hP1 hmax (abs_nonneg _) zero_le_one
        _ = ε := one_mul ε
    · rw [indicator_of_notMem hξ, mul_zero]
      have hu0 : u ξ = 0 := by simp only [hu, hprod0 ξ hξ, zero_mul]
      have hw0 : w ξ = 0 := by
        have := hprod0 ξ hξ
        simp only [laplaceWeight] at this
        simp only [hw, this, mul_zero]
      rw [hu0, hw0, sub_zero, abs_zero]
  have hsine : sineTerm f k = ∫ x, w x := rfl
  rw [hsine, ← integral_sub hu_int hw_int]
  calc |∫ ξ, (u ξ - w ξ)| ≤ ∫ ξ, |u ξ - w ξ| := abs_integral_le_integral_abs
    _ ≤ ∫ ξ, ε * (box k L).indicator 1 ξ :=
        integral_mono (hu_int.sub hw_int).abs (hind_int.const_mul ε) hpt
    _ = ε * (2 * L) ^ k := by
        rw [integral_const_mul, integral_indicator_one (measurableSet_box k L),
          volume_real_box k hL]

/-- The Laplace clause from the kernel and density clauses and PSSS. Fixed
`A, tLo ≤ tHi, v > 0, [ELo, EHi]`, nonnegative `f ∈ C_c(ℝ)`, `δ > 0`; then `N₀`; uniformly
in `N ≥ N₀`, `‖F‖ ≤ N^A`, `t ∈ [tLo, tHi]`, `E ∈ [ELo, EHi]`, boundary MDE `M`, `Im⟨M⟩ ≥ v`,
law `deformedGUELaw N t F hF`, unfolding density `ρ = Im⟨M⟩/π`. -/
theorem laplaceClause_of_kernel (source : PSSS.SourceContract.{0}) (hK : ExternalSineKernel)
    (A tLo tHi v ELo EHi : ℝ) (htLo : 0 < tLo) (htle : tLo ≤ tHi) (hv : 0 < v)
    (f : CompactlySupportedContinuousMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian), ‖F‖ ≤ (N : ℝ) ^ A →
      ∀ (t : ℝ≥0), (t : ℝ) ∈ Icc tLo tHi → ∀ E ∈ Icc ELo EHi,
      ∀ M : Matrix (Fin N) (Fin N) ℂ, IsBoundaryMDE (t : ℝ) F E M →
        v ≤ (CEH.normalizedTrace M).im →
        |unfoldedLaplace N t F hF E ((CEH.normalizedTrace M).im / Real.pi) f -
          sineLaplaceFunctional f| ≤ δ := by
  -- support radius of `f`
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
    f.hasCompactSupport.isCompact.isBounded
  set L : ℝ := max R 0 with hL_def
  have hL : 0 ≤ L := le_max_right _ _
  have hsupp : ∀ x, x ∉ Icc (-L) L → f x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxt
    apply hx
    have h1 := hR hxt
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    exact abs_le.mp (h1.trans (le_max_left _ _))
  -- PSSS constant and the tail
  obtain ⟨Cp, hCp, hcount⟩ := deformedGUELaw_factorialCount_le source
  set q : ℝ := Cp / Real.sqrt tLo * (2 * L / (v / Real.pi)) with hq
  have hq0 : 0 ≤ q := by positivity
  set Q : ℝ := max q (2 * L) with hQ
  have hQ0 : 0 ≤ Q := le_trans hq0 (le_max_left _ _)
  set g : ℕ → ℝ := fun k => 2 * (Q ^ k / (k.factorial : ℝ)) with hg_def
  have hg : Summable g := (Real.summable_pow_div_factorial Q).mul_left 2
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℕ, ∑' k, g (k + K1) < δ / 2 :=
    ((tendsto_sum_nat_add g).eventually (gt_mem_nhds (half_pos hδ))).exists
  -- head tolerance
  set S0 : ℝ := ∑' k : ℕ, (2 * L) ^ k / (k.factorial : ℝ) with hS0_def
  have hS0sum : Summable (fun k : ℕ => (2 * L) ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial (2 * L)
  have hS0 : 0 ≤ S0 := tsum_nonneg fun k => by positivity
  set ε' : ℝ := δ / (2 * (S0 + 1)) with hε'_def
  have hε' : 0 < ε' := by positivity
  have hεS : ε' * S0 ≤ δ / 2 := by
    have h1 : S0 / (S0 + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc ε' * S0 = δ / 2 * (S0 / (S0 + 1)) := by rw [hε'_def]; field_simp
      _ ≤ δ / 2 * 1 := by gcongr
      _ = δ / 2 := mul_one _
  obtain ⟨η, hη, hηK⟩ := exists_pos_forall_lt (fun k η => ∀ (A : Matrix (Fin k) (Fin k) ℂ)
      (B : Matrix (Fin k) (Fin k) ℝ), (∀ i j, |B i j| ≤ 1) →
        (∀ i j, ‖A i j - (B i j : ℂ)‖ ≤ η) → ‖A.det - (B.det : ℂ)‖ ≤ ε')
    (fun _ _ _ _ hle hP A B hB hAB => hP A B hB fun i j => (hAB i j).trans hle)
    (fun k => exists_det_close k ε' hε') K1
  -- clause (a) at the support radius
  obtain ⟨C₀, N₀, hK'⟩ := hK A tLo tHi v ELo EHi L htLo htle hv
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2) ≤ η := by
    have h0 : Tendsto (fun N : ℕ => C₀ * (N : ℝ) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have h1 := ((tendsto_rpow_neg_atTop (y := 1 / 2) (by norm_num)).comp
        tendsto_natCast_atTop_atTop).const_mul C₀
      rw [mul_zero] at h1
      refine h1.congr fun N => ?_
      simp only [Function.comp_apply]
      congr 2
      ring
    exact eventually_atTop.mp (h0.eventually (ge_mem_nhds hη))
  refine ⟨max (max N₀ N₁) (K1 + 1), ?_⟩
  intro N hN F hF hFn t ht E hE M hM hvM
  have hN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNK : K1 + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := by omega
  obtain ⟨Kern, h, hKc, hcorr, hasym, -⟩ := hK' N hN₀ F hF hFn t ht E hE M hM hvM
  set ρ : ℝ := (CEH.normalizedTrace M).im / Real.pi with hρ_def
  have hρv : v / Real.pi ≤ ρ := div_le_div_of_nonneg_right hvM Real.pi_pos.le
  have hρ : 0 < ρ := lt_of_lt_of_le (div_pos hv Real.pi_pos) hρv
  set s : ℝ := (N : ℝ) * ρ with hs_def
  have hs : 0 < s := mul_pos (by exact_mod_cast hNpos) hρ
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le htLo ht.1
  have htpos' : 0 < t := by exact_mod_cast htpos
  have hasym' : ∀ ξ ∈ Icc (-L) L, ∀ ζ ∈ Icc (-L) L,
      ‖Complex.exp (-(h ξ : ℂ)) * Kern (E + ξ / s) (E + ζ / s) * Complex.exp (h ζ : ℂ) /
          (s : ℂ) - (sineKernel ξ ζ : ℂ)‖ ≤ η := by
    intro ξ hξ ζ hζ
    refine le_trans (le_of_eq ?_) ((hasym ξ hξ ζ hζ).trans (hN₁ N hN₁'))
    congr 3
    rw [hs_def, hρ_def]
    push_cast
    rfl
  set T : ℕ → ℝ := fun k => ∫ x, unfoldedObservable s E (laplaceWeight f) x
    ∂deformedFactorialCorrelation N t F hF k with hT_def
  set a : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / (k.factorial : ℝ) * T k with ha_def
  set b : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / (k.factorial : ℝ) * sineTerm f k with hb_def
  have hTzero : ∀ k, N < k → T k = 0 := by
    intro k hk
    have : IsEmpty (Fin k ↪ Fin N) := Function.Embedding.isEmpty_of_card_lt (by simpa using hk)
    simp only [hT_def, deformedFactorialCorrelation, Finset.univ_eq_empty, Finset.sum_empty,
      integral_zero_measure]
  have ha0 : ∀ k ∉ range (N + 1), a k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [ha_def, hTzero k (by omega), mul_zero]
  have hLap : unfoldedLaplace N t F hF E ρ f = ∑' k, a k := by
    rw [unfoldedLaplace_eq_sum N t F hF E ρ f (map_continuous f) hf, tsum_eq_sum ha0]
  have ha : Summable a := summable_of_ne_finset_zero ha0
  have hb : Summable b := summable_sineSeries f hf hL hsupp
  have hTb : ∀ k, 0 ≤ T k ∧ T k ≤ q ^ k := by
    intro k
    obtain ⟨h0, h1⟩ := integral_unfoldedObservable_le hcount N hNpos t htpos' F hF E ρ hρ f
      (map_continuous f) hf L hL hsupp k
    refine ⟨h0, h1.trans (pow_le_pow_left₀ (by positivity) ?_ k)⟩
    have hsq : Real.sqrt tLo ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
    have hsq0 : 0 < Real.sqrt tLo := Real.sqrt_pos.mpr htLo
    have hvpi : 0 < v / Real.pi := div_pos hv Real.pi_pos
    rw [hq]
    gcongr
  set c : ℕ → ℝ := fun k => ε' * ((2 * L) ^ k / (k.factorial : ℝ)) +
    (if K1 ≤ k then g k else 0) with hc_def
  have hcomp : ∀ k, |a k - b k| ≤ c k := by
    intro k
    have hab : a k - b k = (-1 : ℝ) ^ k / (k.factorial : ℝ) * (T k - sineTerm f k) := by
      simp only [ha_def, hb_def]
      ring
    have habs : |(-1 : ℝ) ^ k / (k.factorial : ℝ)| = 1 / (k.factorial : ℝ) := by
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
    rw [hab, abs_mul, habs]
    have hfac : 0 < (k.factorial : ℝ) := by positivity
    by_cases hk : K1 ≤ k
    · have hd : |T k - sineTerm f k| ≤ 2 * Q ^ k := by
        obtain ⟨-, h0, h1⟩ := sineTerm_nonneg_le f hf hL hsupp k
        obtain ⟨t0, t1⟩ := hTb k
        have hq' : q ^ k ≤ Q ^ k := pow_le_pow_left₀ hq0 (le_max_left _ _) k
        have hL' : (2 * L) ^ k ≤ Q ^ k := pow_le_pow_left₀ (by positivity) (le_max_right _ _) k
        rw [abs_le]
        constructor <;> linarith
      simp only [hc_def, hk, ↓reduceIte, hg_def]
      calc 1 / (k.factorial : ℝ) * |T k - sineTerm f k| ≤ 1 / (k.factorial : ℝ) * (2 * Q ^ k) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = 2 * (Q ^ k / (k.factorial : ℝ)) := by ring
        _ ≤ ε' * ((2 * L) ^ k / (k.factorial : ℝ)) + 2 * (Q ^ k / (k.factorial : ℝ)) :=
            le_add_of_nonneg_left (by positivity)
    · have hkN : k ≤ N := by omega
      have hkK : k < K1 := by omega
      have hTk : T k = ∫ ξ : Fin k → ℝ, (∏ j, laplaceWeight f (ξ j)) *
          max ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re) 0 := by
        simp only [hT_def]
        rw [hcorr k hkN]
        exact integral_withDensity_rescale Kern hKc E s hs (laplaceWeight f)
      have hd := term_close f hf hL hsupp Kern hKc h E s ε' η (hηK k hkK) hasym'
      rw [← hTk] at hd
      simp only [hc_def, hk, ↓reduceIte, add_zero]
      calc 1 / (k.factorial : ℝ) * |T k - sineTerm f k| ≤
            1 / (k.factorial : ℝ) * (ε' * (2 * L) ^ k) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = ε' * ((2 * L) ^ k / (k.factorial : ℝ)) := by ring
  have hite_sum : Summable (fun k : ℕ => if K1 ≤ k then g k else 0) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> simp [hg0 k])
      (fun k => by split_ifs <;> simp [hg0 k]) hg
  have hc_sum : Summable c := (hS0sum.mul_left ε').add hite_sum
  have hab_sum : Summable (fun k => |a k - b k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hcomp hc_sum
  have htail : ∑' k : ℕ, (if K1 ≤ k then g k else 0) = ∑' k, g (k + K1) := by
    rw [← hite_sum.sum_add_tsum_nat_add K1]
    have h0 : ∑ i ∈ range K1, (if K1 ≤ i then g i else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [Finset.mem_range] at hi
        simp [not_le.mpr hi]
    rw [h0, zero_add]
    exact tsum_congr fun k => by simp
  rw [hLap, sineLaplaceFunctional_eq_tsum, ← ha.tsum_sub hb]
  calc |∑' k, (a k - b k)| ≤ ∑' k, |a k - b k| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun k => a k - b k)
          (by simpa only [Real.norm_eq_abs] using hab_sum)
    _ ≤ ∑' k, c k := hab_sum.tsum_le_tsum hcomp hc_sum
    _ = ε' * S0 + ∑' k, g (k + K1) := by
        rw [hc_def, (hS0sum.mul_left ε').tsum_add hite_sum, tsum_mul_left, htail]
    _ ≤ δ / 2 + δ / 2 := add_le_add hεS hK1.le
    _ = δ := by ring

/-- The external-source sine-kernel theorem (all three clauses) from its kernel and density
clauses and the factorial-count theorem. -/
theorem externalSine_of_kernel (source : PSSS.SourceContract.{0}) (hK : ExternalSineKernel) :
    ExternalSine := by
  intro A tLo tHi v ELo EHi L htLo htle hv
  exact ⟨hK A tLo tHi v ELo EHi L htLo htle hv, fun f hf δ hδ =>
    laplaceClause_of_kernel source hK A tLo tHi v ELo EHi htLo htle hv f hf δ hδ⟩

end BlockBand.GaussianBulk
