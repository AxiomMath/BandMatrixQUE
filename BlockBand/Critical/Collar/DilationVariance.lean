module

public import BlockBand.Critical.Collar.DilationVariance.Resolvent
public import BlockBand.Critical.Collar.DilationVariance.HilbertSchmidt
public import BlockBand.Critical.Collar.DilationVariance.Jets

/-!
# Dilation and its exact matrix variance

**Law.** `t` is a standard real Cauchy variable: `stdCauchy = ProbabilityTheory.cauchyMeasure 0 1`
(density `1/(π(1+t²))`, `integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul`).
Expectations of matrices are entrywise Bochner integrals; every integrability needed is
*concluded*, not assumed.

**Domain.** Arbitrary finite index type `ι` (the dimension is `Fintype.card ι`), `Xh`
Hermitian, `Y ⪰ 0` (`Matrix.PosSemidef`, no commutation with `Xh`, `X = Xh - iY` not assumed
normal), `z : ℂ` with `η = Im z > 0` (`z = ξ + iη`, `ξ = Re z`).
`R = absorbedResolvent Xh Y z = (z - Xh + iY)⁻¹`,
`R_t = dilationResolvent Xh Y z t = (z - Xh - tY)⁻¹`.

**Norms.** `‖·‖` on matrices is the Euclidean operator norm (`Matrix.Norms.L2Operator`); the
trace is the unnormalized `Matrix.trace`; `g = dissipationWeight Xh Y z = 4 (Im z) Re Tr RᴴYR`
(`Tr RᴴYR ≥ 0` is real, `trace_absorbed_conj_nonneg`).

**Results.**
* (i)   `isCauchyMatrixMean_dilationResolvent` (in `Resolvent`): `E_t R_t = R`.
* (ii)  `isCauchyMatrixMean_variance_left`: `E_t (R_t - R)ᴴ(R_t - R) = η⁻¹ RᴴYR`.
* (iii) `isCauchyMatrixMean_variance_right`: `E_t (R_t - R)(R_t - R)ᴴ = η⁻¹ RYRᴴ`.
* (iv)  `dilation_trace_pow_variance_le` (explicit constant, every `W > 0`, every `k : ℕ`) and
        `dilation_trace_pow_variance` (quantified form, constant
        `C_{k,c₀,η} = max c₀ 0 · k² η^{-2k}/4`).
* (v)   `dilation_trace_pow_exceptional_phases` (normalized powers `R^k`) and
        `dilation_jet_exceptional_phases` (normalized `z`-jets
        `resolventJet k R = (-1)^k k! R^{k+1}`, the `k`-th `z`-derivative of the resolvent,
        see `DilationVariance.Jets`); `dilation_iteratedDeriv_exceptional_phases` states it
        with `iteratedDeriv`, and `dilation_jet_exceptional_phases_neg` /
        `dilation_trace_pow_exceptional_phases_neg` for the reflected phase `R_{-t}`.
* Uniformity: in (iv), (v) the hypothesis is `η ≤ Im z`, so the constants are uniform over
  `Im z ≥ η` (they are monotone in `η⁻¹`, `coeff_le_of_le`).
* Bridges: `one_sub_conjTranspose_mul_scattering` (`I - rᴴr = 4η RᴴYR` for
  `r = I - 2iη(z - X)⁻¹`), `re_trace_one_sub_conjTranspose_mul_scattering` (`Re Tr = g`),
  `stdCauchy_map_neg` (`stdCauchy.map Neg.neg = stdCauchy`), `stdCauchy_preimage_neg`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace BlockBand.Critical.Collar

universe u

section Fixed

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xh Y : Matrix ι ι ℂ} {z : ℂ}

/-- The dissipation weight `g = 4η Tr RᴴYR` (`η = Im z`, real part taken; the
trace is real and nonnegative by `trace_absorbed_conj_nonneg`). -/
def dissipationWeight (Xh Y : Matrix ι ι ℂ) (z : ℂ) : ℝ :=
  4 * z.im * (trace ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z)).re

/-- `Tr RᴴYR ≥ 0` in the complex order (hence real). -/
theorem trace_absorbed_conj_nonneg (hY : Y.PosSemidef) :
    0 ≤ trace ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z) :=
  (hY.conjTranspose_mul_mul_same _).trace_nonneg

theorem dissipationWeight_nonneg (hY : Y.PosSemidef) (hz : 0 < z.im) :
    0 ≤ dissipationWeight Xh Y z := by
  have h := (RCLike.nonneg_iff.mp (trace_absorbed_conj_nonneg (Xh := Xh) (z := z) hY)).1
  unfold dissipationWeight
  have : (0 : ℝ) ≤ 4 * z.im := by positivity
  exact mul_nonneg this h

/-- Mean squared Hilbert–Schmidt distance: `t ↦ ‖R_t - R‖²_HS` is Cauchy-integrable and
`E_t ‖R_t - R‖²_HS = η⁻¹ Re Tr RᴴYR` (trace of part (ii)). -/
theorem hsSq_dilation_sub_mean (hXh : Xh.IsHermitian) (hY : Y.PosSemidef) (hz : 0 < z.im) :
    Integrable (fun t => hsSq (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z))
        stdCauchy ∧
      ∫ t, hsSq (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z) ∂stdCauchy =
        z.im⁻¹ *
          (trace ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z)).re := by
  have hv := isCauchyMatrixMean_variance_left hXh hY hz
  have hfun : (fun t => hsSq (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)) =
      fun t => ∑ j, (((dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)ᴴ *
        (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)) j j).re := by
    funext t
    exact hsSq_eq_sum_re_diag _
  have hint : ∀ j, Integrable (fun t => (((dilationResolvent Xh Y z t -
      absorbedResolvent Xh Y z)ᴴ * (dilationResolvent Xh Y z t -
        absorbedResolvent Xh Y z)) j j).re) stdCauchy := fun j => (hv j j).1.re
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun j _ => hint j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hint j]
  have hj : ∀ j, ∫ t, (((dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)ᴴ *
      (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)) j j).re ∂stdCauchy =
      z.im⁻¹ * (((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z) j j).re := by
    intro j
    have h := integral_re (hv j j).1
    simp only [RCLike.re_to_complex] at h
    rw [h, (hv j j).2, Matrix.smul_apply, smul_eq_mul, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul]
  simp_rw [hj]
  rw [← Finset.mul_sum, trace, Complex.re_sum]
  rfl

/-- **Part (iv), explicit form.** For every `k : ℕ`, every
`D` and every `W > 0` (no relation between `W` and the dimension is needed here),
`t ↦ |W⁻¹ Tr D(R_t^k - R^k)|²` is Cauchy-integrable and
`E_t |W⁻¹ Tr D(R_t^k - R^k)|² ≤ (card ι / W) ‖D‖² (k² η^{-2k} / 4) (g / W)`. -/
theorem dilation_trace_pow_variance_le (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) (D : Matrix ι ι ℂ) (k : ℕ) {W : ℝ} (hW : 0 < W) :
    Integrable (fun t => ‖(W : ℂ)⁻¹ *
        trace (D * (dilationResolvent Xh Y z t ^ k - absorbedResolvent Xh Y z ^ k))‖ ^ 2)
        stdCauchy ∧
      ∫ t, ‖(W : ℂ)⁻¹ *
          trace (D * (dilationResolvent Xh Y z t ^ k - absorbedResolvent Xh Y z ^ k))‖ ^ 2
          ∂stdCauchy ≤
        ((Fintype.card ι : ℝ) / W) * ‖D‖ ^ 2 * ((k : ℝ) ^ 2 * (z.im⁻¹) ^ (2 * k) / 4) *
          (dissipationWeight Xh Y z / W) := by
  set R := absorbedResolvent Xh Y z
  set η := z.im
  set T := (trace (Rᴴ * Y * R)).re
  have hη : 0 < η := hz
  set K : ℝ := (W⁻¹) ^ 2 * (Fintype.card ι : ℝ) * ‖D‖ ^ 2 * ((k : ℝ) * (η⁻¹) ^ (k - 1)) ^ 2
  have hK : 0 ≤ K := by positivity
  have hpt : ∀ t, ‖(W : ℂ)⁻¹ * trace (D * (dilationResolvent Xh Y z t ^ k - R ^ k))‖ ^ 2 ≤
      K * hsSq (dilationResolvent Xh Y z t - R) := by
    intro t
    have hnW : ‖(W : ℂ)⁻¹‖ = W⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hW.le]
    have htr := norm_trace_mul_sq_le D (dilationResolvent Xh Y z t ^ k - R ^ k)
    have hpow := hsNorm_pow_sub_pow_le (dilationResolvent Xh Y z t) R (inv_nonneg.mpr hη.le)
      (norm_dilationResolvent_le hXh hY hz t) (norm_absorbedResolvent_le hXh hY hz) k
    have hpow2 : hsSq (dilationResolvent Xh Y z t ^ k - R ^ k) ≤
        ((k : ℝ) * (η⁻¹) ^ (k - 1)) ^ 2 * hsSq (dilationResolvent Xh Y z t - R) := by
      rw [← hsNorm_sq, ← hsNorm_sq, ← mul_pow]
      exact pow_le_pow_left₀ (hsNorm_nonneg _) hpow 2
    rw [norm_mul, hnW, mul_pow]
    calc (W⁻¹) ^ 2 * ‖trace (D * (dilationResolvent Xh Y z t ^ k - R ^ k))‖ ^ 2
        ≤ (W⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ‖D‖ ^ 2 *
            hsSq (dilationResolvent Xh Y z t ^ k - R ^ k)) := by gcongr
      _ ≤ (W⁻¹) ^ 2 * ((Fintype.card ι : ℝ) * ‖D‖ ^ 2 *
            (((k : ℝ) * (η⁻¹) ^ (k - 1)) ^ 2 * hsSq (dilationResolvent Xh Y z t - R))) := by
          gcongr
      _ = K * hsSq (dilationResolvent Xh Y z t - R) := by ring
  have hcont : Continuous (fun t => ‖(W : ℂ)⁻¹ *
      trace (D * (dilationResolvent Xh Y z t ^ k - R ^ k))‖ ^ 2) := by
    have hR := continuous_dilationResolvent hXh hY hz
    fun_prop
  have hhs := hsSq_dilation_sub_mean hXh hY hz
  have hint : Integrable (fun t => ‖(W : ℂ)⁻¹ *
      trace (D * (dilationResolvent Xh Y z t ^ k - R ^ k))‖ ^ 2) stdCauchy := by
    refine Integrable.mono' (hhs.1.const_mul K) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt t
  refine ⟨hint, ?_⟩
  calc ∫ t, ‖(W : ℂ)⁻¹ * trace (D * (dilationResolvent Xh Y z t ^ k - R ^ k))‖ ^ 2
        ∂stdCauchy
      ≤ ∫ t, K * hsSq (dilationResolvent Xh Y z t - R) ∂stdCauchy :=
        integral_mono hint (hhs.1.const_mul K) hpt
    _ = K * (η⁻¹ * T) := by rw [integral_const_mul, hhs.2]
    _ = ((Fintype.card ι : ℝ) / W) * ‖D‖ ^ 2 * ((k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4) *
          (dissipationWeight Xh Y z / W) := by
        simp only [K, dissipationWeight]
        change _ = _ * (4 * η * T / W)
        rcases k with _ | k
        · simp
        · simp only [Nat.add_sub_cancel]
          have hη0 : η ≠ 0 := hη.ne'
          have hW0 : W ≠ 0 := hW.ne'
          have h1 : η ^ 2 * η⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη0, one_pow]
          field_simp
          linear_combination (-((Fintype.card ι : ℝ) * ‖D‖ ^ 2 * η⁻¹ ^ (k * 2) * T)) * h1

/-- Pointwise rewriting of the normalized jet observable in terms of powers. -/
theorem trace_resolventJet_sub (D A B : Matrix ι ι ℂ) (k : ℕ) (W : ℂ) :
    W⁻¹ * trace (D * (resolventJet k A - resolventJet k B)) =
      ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * (W⁻¹ * trace (D * (A ^ (k + 1) - B ^ (k + 1)))) := by
  simp only [resolventJet, ← smul_sub, Matrix.mul_smul, trace_smul, smul_eq_mul]
  ring

end Fixed

/-!
### Chebyshev and union bound
-/

/-- Union bound plus Chebyshev for finitely many complex observables, under any finite
measure: `μ {∃ j, ε ≤ |X_j|} ≤ N B / ε²` if `E|X_j|² ≤ B` for all `j`. -/
theorem measure_exists_le_norm_le {N : ℕ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (X : Fin N → ℝ → ℂ) (hX : ∀ j, Integrable (fun t => ‖X j t‖ ^ 2) μ) {B : ℝ}
    (hB : ∀ j, ∫ t, ‖X j t‖ ^ 2 ∂μ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    μ {t | ∃ j, ε ≤ ‖X j t‖} ≤ ENNReal.ofReal (N * B / ε ^ 2) := by
  have hset : {t | ∃ j, ε ≤ ‖X j t‖} = ⋃ j, {t | ε ^ 2 ≤ ‖X j t‖ ^ 2} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine exists_congr fun j => ?_
    exact (pow_le_pow_iff_left₀ hε.le (norm_nonneg _) two_ne_zero).symm
  have hcheb : ∀ j, μ.real {t | ε ^ 2 ≤ ‖X j t‖ ^ 2} ≤ B / ε ^ 2 := by
    intro j
    have h := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun t => by positivity) (hX j) (ε ^ 2)
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h.trans (hB j)
  rw [hset, ← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  calc μ.real (⋃ j, {t | ε ^ 2 ≤ ‖X j t‖ ^ 2})
      ≤ ∑ j, μ.real {t | ε ^ 2 ≤ ‖X j t‖ ^ 2} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin N, B / ε ^ 2 := Finset.sum_le_sum fun j _ => hcheb j
    _ = N * B / ε ^ 2 := by simp [mul_div_assoc]

/-!
### Quantified forms
-/

/-- Monotonicity of the single-power constant in `η`: if `η ≤ x` then
`k² x^{-2k}/4 ≤ k² η^{-2k}/4`. -/
theorem coeff_le_of_le {η x : ℝ} (hη : 0 < η) (h : η ≤ x) (k : ℕ) :
    (k : ℝ) ^ 2 * (x⁻¹) ^ (2 * k) / 4 ≤ (k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4 := by
  have hx : 0 ≤ x⁻¹ := inv_nonneg.mpr (hη.le.trans h)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx (inv_anti₀ hη h) _) (by positivity)

/-- **Part (iv).** Quantifier order: for every power `k : ℕ`
(`k = 0` is trivially included), every `c₀` and every `η > 0` there
is `C = C_{k,c₀,η} ≥ 0` such that for every `W > 0`, every finite index type `ι` with
`card ι ≤ c₀ W`, every Hermitian `Xh`, every `Y ⪰ 0`, every `z` with `Im z ≥ η`
(any `ξ = Re z`; uniform over `Im z ≥ η`)
and every `D` with Euclidean operator norm `‖D‖ ≤ 1`:
`t ↦ |W⁻¹ Tr D(R_t^k - R^k)|²` is integrable for the standard Cauchy law and
`E_t |W⁻¹ Tr D(R_t^k - R^k)|² ≤ C g / W`, `g = 4 (Im z) Re Tr RᴴYR` (≥ 4η Re Tr RᴴYR when `η ≤ Im z`).
Uniformity: `C = max c₀ 0 · k² η^{-2k} / 4` depends only on `(k, c₀, η)`. -/
theorem dilation_trace_pow_variance (k : ℕ) (c₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
      ∀ (Xh Y D : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
        ‖D‖ ≤ 1 →
        Integrable (fun t => ‖(W : ℂ)⁻¹ *
            trace (D * (dilationResolvent Xh Y z t ^ k - absorbedResolvent Xh Y z ^ k))‖ ^ 2)
            stdCauchy ∧
          ∫ t, ‖(W : ℂ)⁻¹ *
              trace (D * (dilationResolvent Xh Y z t ^ k - absorbedResolvent Xh Y z ^ k))‖ ^ 2
              ∂stdCauchy ≤ C * dissipationWeight Xh Y z / W := by
  refine ⟨max c₀ 0 * ((k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4), by positivity, ?_⟩
  intro W hW ι _ _ hcard Xh Y D z hXh hY hzη hD
  have hz : 0 < z.im := lt_of_lt_of_le hη hzη
  obtain ⟨hint, hle⟩ := dilation_trace_pow_variance_le hXh hY hz D k hW
  refine ⟨hint, hle.trans ?_⟩
  have hg := dissipationWeight_nonneg (Xh := Xh) hY hz
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (coeff_le_of_le hη hzη k)
    (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hW.le) (sq_nonneg _))) (div_nonneg hg hW.le)).trans ?_
  have hcw : (Fintype.card ι : ℝ) / W ≤ max c₀ 0 :=
    ((div_le_iff₀ hW).mpr hcard).trans (le_max_left _ _)
  have hD2 : ‖D‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hD
  have hA : 0 ≤ (k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4 := by
    have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
    positivity
  calc ((Fintype.card ι : ℝ) / W) * ‖D‖ ^ 2 * ((k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4) *
        (dissipationWeight Xh Y z / W)
      ≤ max c₀ 0 * 1 * ((k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4) *
        (dissipationWeight Xh Y z / W) := by gcongr
    _ = max c₀ 0 * ((k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4) * dissipationWeight Xh Y z / W := by
        ring

/-- Auxiliary constant `∑_{k ≤ m} k² η^{-2k} / 4`, dominating each single-power constant. -/
def jetConstant (m : ℕ) (η : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4

theorem jetConstant_nonneg (m : ℕ) {η : ℝ} (hη : 0 < η) : 0 ≤ jetConstant m η := by
  unfold jetConstant
  have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  positivity

theorem le_jetConstant {m k : ℕ} (hk : k ≤ m) {η : ℝ} (hη : 0 < η) :
    (k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4 ≤ jetConstant m η := by
  unfold jetConstant
  have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  exact Finset.single_le_sum (f := fun k : ℕ => (k : ℝ) ^ 2 * (η⁻¹) ^ (2 * k) / 4)
    (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- **Part (v), normalized resolvent powers.** Quantifier
order: for every maximal order `m`, list length `N`, `c₀` and `η > 0` there is `C ≥ 0`
(depending only on `m, N, c₀, η`) such that for every `W > 0`, every finite `ι` with
`card ι ≤ c₀ W`, every Hermitian `Xh`, `Y ⪰ 0`, `z` with `Im z ≥ η`, every list
`(D_j, k_j)_{j < N}` with `‖D_j‖ ≤ 1` (Euclidean operator norm) and `k_j ≤ m`, and every
`ε > 0`, the Cauchy mass of the phase set where some normalized power moves by at least `ε`,
`{t | ∃ j, ε ≤ |W⁻¹ Tr D_j(R_t^{k_j} - R^{k_j})|}`, is at most `C g / (W ε²)`
(`g = 4 (Im z) Re Tr RᴴYR` (≥ 4η Re Tr RᴴYR when `η ≤ Im z`)). The set `{≥ ε}` contains the exceptional set `{> ε}`.
Constant: `C = N · max c₀ 0 · ∑_{k ≤ m} k² η^{-2k}/4`. -/
theorem dilation_trace_pow_exceptional_phases (m N : ℕ) (c₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
      ∀ (Xh Y : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
      ∀ (D : Fin N → Matrix ι ι ℂ) (k : Fin N → ℕ), (∀ j, ‖D j‖ ≤ 1) → (∀ j, k j ≤ m) →
      ∀ ε : ℝ, 0 < ε →
        stdCauchy {t | ∃ j, ε ≤ ‖(W : ℂ)⁻¹ *
            trace (D j * (dilationResolvent Xh Y z t ^ k j -
              absorbedResolvent Xh Y z ^ k j))‖} ≤
          ENNReal.ofReal (C * dissipationWeight Xh Y z / (W * ε ^ 2)) := by
  refine ⟨N * (max c₀ 0 * jetConstant m η), by
    have := jetConstant_nonneg m hη
    positivity, ?_⟩
  intro W hW ι _ _ hcard Xh Y z hXh hY hzη D k hD hk ε hε
  have hz : 0 < z.im := lt_of_lt_of_le hη hzη
  have hg := dissipationWeight_nonneg (Xh := Xh) hY hz
  have hcw : (Fintype.card ι : ℝ) / W ≤ max c₀ 0 :=
    ((div_le_iff₀ hW).mpr hcard).trans (le_max_left _ _)
  have hbound : ∀ j, ∫ t, ‖(W : ℂ)⁻¹ * trace (D j * (dilationResolvent Xh Y z t ^ k j -
      absorbedResolvent Xh Y z ^ k j))‖ ^ 2 ∂stdCauchy ≤
      max c₀ 0 * jetConstant m η * (dissipationWeight Xh Y z / W) := by
    intro j
    have h := (dilation_trace_pow_variance_le hXh hY hz (D j) (k j) hW).2
    refine h.trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (coeff_le_of_le hη hzη (k j)) (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hW.le) (sq_nonneg _))) (div_nonneg hg hW.le)).trans ?_
    have hD2 : ‖D j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hD j)
    have hA : 0 ≤ ((k j : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ (2 * k j) / 4 := by
      have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
      positivity
    have hgW : 0 ≤ dissipationWeight Xh Y z / W := div_nonneg hg hW.le
    calc ((Fintype.card ι : ℝ) / W) * ‖D j‖ ^ 2 * (((k j : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ (2 * k j) / 4) *
          (dissipationWeight Xh Y z / W)
        ≤ max c₀ 0 * 1 * jetConstant m η * (dissipationWeight Xh Y z / W) := by
          gcongr
          exact le_jetConstant (hk j) hη
      _ = max c₀ 0 * jetConstant m η * (dissipationWeight Xh Y z / W) := by ring
  have h := measure_exists_le_norm_le (μ := stdCauchy)
    (fun j t => (W : ℂ)⁻¹ * trace (D j * (dilationResolvent Xh Y z t ^ k j -
      absorbedResolvent Xh Y z ^ k j)))
    (fun j => (dilation_trace_pow_variance_le hXh hY hz (D j) (k j) hW).1) hbound hε
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  field_simp

/-- **Part (v), normalized `z`-jets.** Same quantifiers as
`dilation_trace_pow_exceptional_phases`, with the observables
`W⁻¹ Tr D_j(∂_z^{k_j} R_t - ∂_z^{k_j} R)`, where `∂_z^k R = resolventJet k R = (-1)^k k! R^{k+1}`
(`iteratedDeriv_resolvent_eq_resolventJet` in `DilationVariance.Jets` identifies this with the
`k`-th complex derivative in `z` of `z ↦ (z - X)⁻¹`, for both `R` and `R_t`). Constant:
`C = N · (m!)² · max c₀ 0 · ∑_{k ≤ m+1} k² η^{-2k}/4`. -/
theorem dilation_jet_exceptional_phases (m N : ℕ) (c₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
      ∀ (Xh Y : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
      ∀ (D : Fin N → Matrix ι ι ℂ) (k : Fin N → ℕ), (∀ j, ‖D j‖ ≤ 1) → (∀ j, k j ≤ m) →
      ∀ ε : ℝ, 0 < ε →
        stdCauchy {t | ∃ j, ε ≤ ‖(W : ℂ)⁻¹ *
            trace (D j * (resolventJet (k j) (dilationResolvent Xh Y z t) -
              resolventJet (k j) (absorbedResolvent Xh Y z)))‖} ≤
          ENNReal.ofReal (C * dissipationWeight Xh Y z / (W * ε ^ 2)) := by
  refine ⟨N * ((m.factorial : ℝ) ^ 2 * (max c₀ 0 * jetConstant (m + 1) η)), by
    have := jetConstant_nonneg (m + 1) hη
    positivity, ?_⟩
  intro W hW ι _ _ hcard Xh Y z hXh hY hzη D k hD hk ε hε
  have hz : 0 < z.im := lt_of_lt_of_le hη hzη
  have hg := dissipationWeight_nonneg (Xh := Xh) hY hz
  have hcw : (Fintype.card ι : ℝ) / W ≤ max c₀ 0 :=
    ((div_le_iff₀ hW).mpr hcard).trans (le_max_left _ _)
  set X : Fin N → ℝ → ℂ := fun j t => (W : ℂ)⁻¹ * trace (D j *
    (resolventJet (k j) (dilationResolvent Xh Y z t) -
      resolventJet (k j) (absorbedResolvent Xh Y z))) with hXdef
  have hXeq : ∀ j t, ‖X j t‖ ^ 2 = ((k j).factorial : ℝ) ^ 2 * ‖(W : ℂ)⁻¹ *
      trace (D j * (dilationResolvent Xh Y z t ^ (k j + 1) -
        absorbedResolvent Xh Y z ^ (k j + 1)))‖ ^ 2 := by
    intro j t
    simp only [X, trace_resolventJet_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul, Complex.norm_natCast, mul_pow]
  have hint : ∀ j, Integrable (fun t => ‖X j t‖ ^ 2) stdCauchy := by
    intro j
    simp_rw [hXeq]
    exact (dilation_trace_pow_variance_le hXh hY hz (D j) (k j + 1) hW).1.const_mul _
  have hbound : ∀ j, ∫ t, ‖X j t‖ ^ 2 ∂stdCauchy ≤
      (m.factorial : ℝ) ^ 2 * (max c₀ 0 * jetConstant (m + 1) η) *
        (dissipationWeight Xh Y z / W) := by
    intro j
    simp_rw [hXeq]
    rw [integral_const_mul]
    have h := (dilation_trace_pow_variance_le hXh hY hz (D j) (k j + 1) hW).2
    replace h := h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (coeff_le_of_le hη hzη (k j + 1)) (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hW.le) (sq_nonneg _))) (div_nonneg hg hW.le))
    have hD2 : ‖D j‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hD j)
    have hA : 0 ≤ ((k j + 1 : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ (2 * (k j + 1)) / 4 := by
      have : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
      positivity
    have hgW : 0 ≤ dissipationWeight Xh Y z / W := div_nonneg hg hW.le
    have hfac : ((k j).factorial : ℝ) ^ 2 ≤ (m.factorial : ℝ) ^ 2 := by
      have : ((k j).factorial : ℝ) ≤ m.factorial := by
        exact_mod_cast Nat.factorial_le (hk j)
      gcongr
    have hE : ∫ t, ‖(W : ℂ)⁻¹ * trace (D j * (dilationResolvent Xh Y z t ^ (k j + 1) -
        absorbedResolvent Xh Y z ^ (k j + 1)))‖ ^ 2 ∂stdCauchy ≤
        max c₀ 0 * jetConstant (m + 1) η * (dissipationWeight Xh Y z / W) := by
      refine h.trans ?_
      calc ((Fintype.card ι : ℝ) / W) * ‖D j‖ ^ 2 *
            (((k j + 1 : ℕ) : ℝ) ^ 2 * (η⁻¹) ^ (2 * (k j + 1)) / 4) *
            (dissipationWeight Xh Y z / W)
          ≤ max c₀ 0 * 1 * jetConstant (m + 1) η * (dissipationWeight Xh Y z / W) := by
            gcongr
            exact le_jetConstant (Nat.succ_le_succ (hk j)) hη
        _ = max c₀ 0 * jetConstant (m + 1) η * (dissipationWeight Xh Y z / W) := by ring
    have hE0 : 0 ≤ ∫ t, ‖(W : ℂ)⁻¹ * trace (D j * (dilationResolvent Xh Y z t ^ (k j + 1) -
        absorbedResolvent Xh Y z ^ (k j + 1)))‖ ^ 2 ∂stdCauchy :=
      integral_nonneg fun t => by positivity
    calc ((k j).factorial : ℝ) ^ 2 * ∫ t, ‖(W : ℂ)⁻¹ * trace (D j *
          (dilationResolvent Xh Y z t ^ (k j + 1) -
            absorbedResolvent Xh Y z ^ (k j + 1)))‖ ^ 2 ∂stdCauchy
        ≤ (m.factorial : ℝ) ^ 2 *
          (max c₀ 0 * jetConstant (m + 1) η * (dissipationWeight Xh Y z / W)) :=
          mul_le_mul hfac hE hE0 (by positivity)
      _ = (m.factorial : ℝ) ^ 2 * (max c₀ 0 * jetConstant (m + 1) η) *
          (dissipationWeight Xh Y z / W) := by ring
  have h := measure_exists_le_norm_le (μ := stdCauchy) X hint hbound hε
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  field_simp

/-- **The dilation variance lemma, bundled.** Conjunction of
(i)–(iii) (`isCauchyMatrixMean_dilationResolvent`, `isCauchyMatrixMean_variance_left`,
`isCauchyMatrixMean_variance_right`: entrywise integrability and exact entrywise means, for
every finite `ι`, Hermitian `Xh`, `Y ⪰ 0`, `Im z > 0`), (iv) (`dilation_trace_pow_variance`)
and (v) (`dilation_jet_exceptional_phases`, normalized `z`-jets). Law: standard real Cauchy
`stdCauchy`; norms: Euclidean operator norm on `D`; `g = dissipationWeight`. -/
theorem t22_dilation_variance :
    (∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (Xh Y : Matrix ι ι ℂ) (z : ℂ),
        Xh.IsHermitian → Y.PosSemidef → 0 < z.im →
        IsCauchyMatrixMean (dilationResolvent Xh Y z) (absorbedResolvent Xh Y z) ∧
        IsCauchyMatrixMean
          (fun t => (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)ᴴ *
            (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z))
          ((z.im : ℂ)⁻¹ • ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z)) ∧
        IsCauchyMatrixMean
          (fun t => (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z) *
            (dilationResolvent Xh Y z t - absorbedResolvent Xh Y z)ᴴ)
          ((z.im : ℂ)⁻¹ • (absorbedResolvent Xh Y z * Y * (absorbedResolvent Xh Y z)ᴴ))) ∧
    (∀ (k : ℕ) (c₀ η : ℝ), 0 < η →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
        ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
        ∀ (Xh Y D : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
          ‖D‖ ≤ 1 →
          Integrable (fun t => ‖(W : ℂ)⁻¹ *
              trace (D * (dilationResolvent Xh Y z t ^ k - absorbedResolvent Xh Y z ^ k))‖ ^ 2)
              stdCauchy ∧
            ∫ t, ‖(W : ℂ)⁻¹ *
                trace (D * (dilationResolvent Xh Y z t ^ k - absorbedResolvent Xh Y z ^ k))‖ ^ 2
                ∂stdCauchy ≤ C * dissipationWeight Xh Y z / W) ∧
    (∀ (m N : ℕ) (c₀ η : ℝ), 0 < η →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
        ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
        ∀ (Xh Y : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
        ∀ (D : Fin N → Matrix ι ι ℂ) (k : Fin N → ℕ), (∀ j, ‖D j‖ ≤ 1) → (∀ j, k j ≤ m) →
        ∀ ε : ℝ, 0 < ε →
          stdCauchy {t | ∃ j, ε ≤ ‖(W : ℂ)⁻¹ *
              trace (D j * (resolventJet (k j) (dilationResolvent Xh Y z t) -
                resolventJet (k j) (absorbedResolvent Xh Y z)))‖} ≤
            ENNReal.ofReal (C * dissipationWeight Xh Y z / (W * ε ^ 2))) :=
  ⟨fun _ _ _ _ _ _ hXh hY hz => ⟨isCauchyMatrixMean_dilationResolvent hXh hY hz,
      isCauchyMatrixMean_variance_left hXh hY hz, isCauchyMatrixMean_variance_right hXh hY hz⟩,
    fun k c₀ η hη => dilation_trace_pow_variance.{u} k c₀ η hη,
    fun m N c₀ η hη => dilation_jet_exceptional_phases.{u} m N c₀ η hη⟩

/-!
### Addenda: derivative form, scattering bridge, phase symmetry
-/

/-- **Part (v), derivative form.** Same quantifiers and constant as
`dilation_jet_exceptional_phases`, with the jets written as iterated complex
derivatives in `z`: `∂_z^{k_j} R_t = iteratedDeriv (k j) (w ↦ R_t(w)) z` and
`∂_z^{k_j} R = iteratedDeriv (k j) (w ↦ R(w)) z` (identified with `resolventJet` by
`iteratedDeriv_dilationResolvent` / `iteratedDeriv_absorbedResolvent`). -/
theorem dilation_iteratedDeriv_exceptional_phases (m N : ℕ) (c₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
      ∀ (Xh Y : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
      ∀ (D : Fin N → Matrix ι ι ℂ) (k : Fin N → ℕ), (∀ j, ‖D j‖ ≤ 1) → (∀ j, k j ≤ m) →
      ∀ ε : ℝ, 0 < ε →
        stdCauchy {t | ∃ j, ε ≤ ‖(W : ℂ)⁻¹ *
            trace (D j * (iteratedDeriv (k j) (fun w => dilationResolvent Xh Y w t) z -
              iteratedDeriv (k j) (fun w => absorbedResolvent Xh Y w) z))‖} ≤
          ENNReal.ofReal (C * dissipationWeight Xh Y z / (W * ε ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := dilation_jet_exceptional_phases.{u} m N c₀ η hη
  refine ⟨C, hC0, fun W hW ι _ _ hcard Xh Y z hXh hY hzη D k hD hk ε hε => ?_⟩
  have hz : 0 < z.im := lt_of_lt_of_le hη hzη
  simp only [iteratedDeriv_dilationResolvent hXh hY hz,
    iteratedDeriv_absorbedResolvent hXh hY hz]
  exact hC W hW ι hcard Xh Y z hXh hY hzη D k hD hk ε hε

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xh Y : Matrix ι ι ℂ} {z : ℂ}

/-- **Scattering bridge for `g`.** For `X = Xh - iY` (`Xh` Hermitian, `Y ⪰ 0`) and `z` with
`η = Im z > 0`, the matrix `r = I - 2iη (z - X)⁻¹` satisfies `I - rᴴ r = 4η RᴴYR` with
`R = (z - Xh + iY)⁻¹ = absorbedResolvent Xh Y z`. Plain matrices. -/
theorem one_sub_conjTranspose_mul_scattering (hXh : Xh.IsHermitian) (hY : Y.PosSemidef)
    (hz : 0 < z.im) :
    let r : Matrix ι ι ℂ := 1 - ((2 * z.im : ℝ) * Complex.I) •
      (z • (1 : Matrix ι ι ℂ) - (Xh - Complex.I • Y))⁻¹
    1 - rᴴ * r = ((4 * z.im : ℝ) : ℂ) •
      ((absorbedResolvent Xh Y z)ᴴ * Y * absorbedResolvent Xh Y z) := by
  intro r
  set R := absorbedResolvent Xh Y z
  have hR : (z • (1 : Matrix ι ι ℂ) - (Xh - Complex.I • Y))⁻¹ = R :=
    (absorbedResolvent_eq Xh Y z).symm
  have hw := (absorbedResolvent_ward hXh hY hz).1
  set a : ℂ := ((2 * z.im : ℝ) * Complex.I)
  have hstar : star a = -a := by
    simp only [a, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hr : r = 1 - a • R := by simp only [r, hR, a]
  have hrH : rᴴ = 1 + a • Rᴴ := by
    rw [hr, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hstar, neg_smul,
      sub_neg_eq_add]
  rw [hrH, hr]
  have hexp : (1 + a • Rᴴ) * (1 - a • R) =
      1 + a • (Rᴴ - R) - (a * a) • (Rᴴ * R) := by
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    module
  rw [hexp, hw, smul_add, smul_smul, smul_smul]
  have h1 : a * ((2 * z.im : ℝ) * Complex.I) = a * a := rfl
  have h2 : a * (2 * Complex.I) = -(((4 * z.im : ℝ) : ℂ)) := by
    simp only [a]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h1, h2, neg_smul]
  abel

/-- `Re Tr (I - rᴴ r) = g` (`dissipationWeight`), for the same `r`. -/
theorem re_trace_one_sub_conjTranspose_mul_scattering (hXh : Xh.IsHermitian)
    (hY : Y.PosSemidef) (hz : 0 < z.im) :
    let r : Matrix ι ι ℂ := 1 - ((2 * z.im : ℝ) * Complex.I) •
      (z • (1 : Matrix ι ι ℂ) - (Xh - Complex.I • Y))⁻¹
    (trace (1 - rᴴ * r)).re = dissipationWeight Xh Y z := by
  intro r
  rw [one_sub_conjTranspose_mul_scattering hXh hY hz, trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, dissipationWeight]

end Bridge

/-- **Measure-level symmetry of the standard Cauchy law:** `t ↦ -t` preserves `stdCauchy`. -/
theorem stdCauchy_map_neg : stdCauchy.map Neg.neg = stdCauchy := by
  have hmeas := ProbabilityTheory.measurable_cauchyPDF 0 1
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  simp only [stdCauchy, ProbabilityTheory.cauchyMeasure_of_scale_ne_zero 0 one_ne_zero]
  rw [withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_neg hs), ← lintegral_indicator hs,
    ← lintegral_neg_eq_self]
  congr 1
  funext x
  by_cases hx : x ∈ s
  · have hx' : -x ∈ Neg.neg ⁻¹' s := by simpa using hx
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem hx]
    simp [ProbabilityTheory.cauchyPDF, ProbabilityTheory.cauchyPDFReal]
  · have hx' : -x ∉ Neg.neg ⁻¹' s := by simpa using hx
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]

/-- Set form of the symmetry: `stdCauchy (-S) = stdCauchy S` for every set `S`. -/
theorem stdCauchy_preimage_neg (S : Set ℝ) : stdCauchy (Neg.neg ⁻¹' S) = stdCauchy S := by
  have h := (MeasurableEquiv.neg ℝ).map_apply (μ := stdCauchy) S
  change stdCauchy.map Neg.neg S = stdCauchy (Neg.neg ⁻¹' S) at h
  rw [← h, stdCauchy_map_neg]

/-- **Part (v) for the reflected phase `R_{-t}`.** Same quantifiers and constant as
`dilation_jet_exceptional_phases`, for the observables built from
`R_{-t} = (z - Xh + tY)⁻¹`; follows from `stdCauchy_preimage_neg`. -/
theorem dilation_jet_exceptional_phases_neg (m N : ℕ) (c₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
      ∀ (Xh Y : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
      ∀ (D : Fin N → Matrix ι ι ℂ) (k : Fin N → ℕ), (∀ j, ‖D j‖ ≤ 1) → (∀ j, k j ≤ m) →
      ∀ ε : ℝ, 0 < ε →
        stdCauchy {t | ∃ j, ε ≤ ‖(W : ℂ)⁻¹ *
            trace (D j * (resolventJet (k j) (dilationResolvent Xh Y z (-t)) -
              resolventJet (k j) (absorbedResolvent Xh Y z)))‖} ≤
          ENNReal.ofReal (C * dissipationWeight Xh Y z / (W * ε ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := dilation_jet_exceptional_phases.{u} m N c₀ η hη
  refine ⟨C, hC0, fun W hW ι _ _ hcard Xh Y z hXh hY hzη D k hD hk ε hε => ?_⟩
  exact (stdCauchy_preimage_neg _).trans_le (hC W hW ι hcard Xh Y z hXh hY hzη D k hD hk ε hε)

/-- Reflected-phase version of `dilation_trace_pow_exceptional_phases` (powers). -/
theorem dilation_trace_pow_exceptional_phases_neg (m N : ℕ) (c₀ η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℝ, 0 < W →
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι], (Fintype.card ι : ℝ) ≤ c₀ * W →
      ∀ (Xh Y : Matrix ι ι ℂ) (z : ℂ), Xh.IsHermitian → Y.PosSemidef → η ≤ z.im →
      ∀ (D : Fin N → Matrix ι ι ℂ) (k : Fin N → ℕ), (∀ j, ‖D j‖ ≤ 1) → (∀ j, k j ≤ m) →
      ∀ ε : ℝ, 0 < ε →
        stdCauchy {t | ∃ j, ε ≤ ‖(W : ℂ)⁻¹ *
            trace (D j * (dilationResolvent Xh Y z (-t) ^ k j -
              absorbedResolvent Xh Y z ^ k j))‖} ≤
          ENNReal.ofReal (C * dissipationWeight Xh Y z / (W * ε ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := dilation_trace_pow_exceptional_phases.{u} m N c₀ η hη
  refine ⟨C, hC0, fun W hW ι _ _ hcard Xh Y z hXh hY hzη D k hD hk ε hε => ?_⟩
  exact (stdCauchy_preimage_neg _).trans_le (hC W hW ι hcard Xh Y z hXh hY hzη D k hD hk ε hε)

end BlockBand.Critical.Collar
