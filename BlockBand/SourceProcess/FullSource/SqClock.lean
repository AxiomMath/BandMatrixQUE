module

public import BlockBand.SourceProcess.FullSource.SqBulk
public import BlockBand.SourceProcess.FullSource.Main

/-!
# `clockSquare`: the clock square from the tag squares

The clock is the sum of the tags, `Y_j^1 = Σ_{k<j} Y_{j;k}`, and
`Tr(Σ_{k∈s}Y_k)² ≤ |s| Σ_k Tr Y_k²` for Hermitian `Y_k` (`re_trace_sum_sq_le`, Hilbert–Schmidt
AM–GM). With `E Tr Y_{j;k}² = W E h_{j;k} ≤ CW(j+1)` (`TagSqBulk`):
`E Tr(Y_j^1)² ≤ j · j · CW(j+1) ≤ CW(j+1)³`.
* `clockSquare_of_tagSq`: `ClockSquareBulk` from `TagSqBulk`;
* `sqBirthMoments_of`: `SqBirthMoments` (`k ≥ 1` from `FullSourceEstimates.moments`, `k = 0`
  from `GaussianAbsorptionContract`);
* `clockSquareBulk_holds`: `ClockSquareBulk` from the Gaussian inputs and `FullSourceEstimates`.

This gives the full clock moments, with `H_j ≤ C(j+1)³`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PathScalar BlockBand.Transmission.PassiveLayer
open scoped ENNReal

/-- `Re Tr(Σ_{k∈s}Y_k)² ≤ |s| Σ_{k∈s} Re Tr Y_k²` for Hermitian `Y_k`. -/
theorem re_trace_sum_sq_le {ι n : Type*} [Fintype n] (s : Finset ι)
    (Y : ι → Matrix n n ℂ) (hY : ∀ i, (Y i).IsHermitian) :
    ((∑ i ∈ s, Y i) * (∑ i ∈ s, Y i)).trace.re ≤ s.card * ∑ i ∈ s, (Y i * Y i).trace.re := by
  rw [Finset.sum_mul_sum, Matrix.trace_sum, Complex.re_sum]
  have h : ∀ i ∈ s, ∀ l ∈ s, (Y i * Y l).trace.re ≤
      ((Y i * Y i).trace.re + (Y l * Y l).trace.re) / 2 := by
    intro i _ l _
    have := (Complex.re_le_norm _).trans (norm_trace_mul_le_amgm (Y i) (Y l))
    rwa [(hY i).eq, (hY l).eq] at this
  calc ∑ i ∈ s, ((∑ l ∈ s, Y i * Y l).trace).re
      = ∑ i ∈ s, ∑ l ∈ s, (Y i * Y l).trace.re := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.trace_sum, Complex.re_sum]
    _ ≤ ∑ i ∈ s, ∑ l ∈ s, ((Y i * Y i).trace.re + (Y l * Y l).trace.re) / 2 :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun l hl => h i hi l hl
    _ = s.card * ∑ i ∈ s, (Y i * Y i).trace.re := by
        simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.sum_div, ← Finset.mul_sum]
        ring

variable {W : ℕ}

theorem clock_eq_sum_tags (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    (boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω =
      ∑ k ∈ Finset.range j, tagResponse b E W j k ω := by
  rw [show (boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω =
      (boundaryToInterior b E W j ω)ᴴ * (∑ k ∈ Finset.range j, tagProjection W j k) *
        boundaryToInterior b E W j ω by rw [sum_tagProjection, Matrix.mul_one],
    Matrix.mul_sum, Matrix.sum_mul]
  rfl

/-- The pointwise clock-square bound: `|Tr(Y^1)²| ≤ j W Σ_k h_{j;k}`. -/
theorem enorm_clockSq_le (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    ‖(((boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω) ^ 2).trace‖ₑ ≤
      ENNReal.ofReal (j * W * ∑ k ∈ Finset.range j, tagSq b E W j k ω) := by
  set U := boundaryToInterior b E W j ω
  have hreal := trace_factor_eq_re (Uᴴ * U)
  rw [(Matrix.isHermitian_conjTranspose_mul_self U).eq, ← sq] at hreal
  rw [hreal, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ (((Uᴴ * U) ^ 2).trace).re := by
    have := trace_factor_re_nonneg (Uᴴ * U)
    rwa [(Matrix.isHermitian_conjTranspose_mul_self U).eq, ← sq] at this
  rw [abs_of_nonneg h0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hY : ∀ k, (tagResponse b E W j k ω).IsHermitian := fun k => by
    rw [tagResponse_eq_factor]; exact Matrix.isHermitian_conjTranspose_mul_self _
  have h := re_trace_sum_sq_le (Finset.range j) (fun k => tagResponse b E W j k ω) hY
  rw [← clock_eq_sum_tags, ← sq, Finset.card_range] at h
  refine h.trans (le_of_eq ?_)
  have hW : ∀ k, (tagResponse b E W j k ω * tagResponse b E W j k ω).trace.re =
      W * tagSq b E W j k ω := by
    intro k
    rcases Nat.eq_zero_or_pos W with h0 | hpos
    · subst h0
      have : (tagResponse b E 0 j k ω * tagResponse b E 0 j k ω) = 0 := Subsingleton.elim _ _
      simp [this]
    · rw [tagSq]; field_simp
  simp only [hW, ← Finset.mul_sum]
  ring

/-- **`ClockSquareBulk` from the tag squares.** -/
theorem clockSquare_of_tagSq (h : TagSqBulk) : ClockSquareBulk := by
  intro b hb0 hb κ T hκ
  obtain ⟨C, W₀, hC0, hC⟩ := h b hb0 hb κ T hκ
  refine ⟨C, W₀, fun W hW E hE j hj => ?_⟩
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hjW : 0 ≤ (j : ℝ) * W := mul_nonneg hj0 hW0
  calc ∫⁻ ω, ‖(((boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω) ^ 2).trace‖ₑ
        ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (j * W * ∑ k ∈ Finset.range j, tagSq b E W j k ω)
          ∂growthPathLaw W b := lintegral_mono fun ω => enorm_clockSq_le b E j ω
    _ = ∑ k ∈ Finset.range j, ENNReal.ofReal (j * W) *
          ∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω) ∂growthPathLaw W b := by
        have e1 : ∀ k ∈ Finset.range j, ENNReal.ofReal (j * W) *
            ∫⁻ ω, ENNReal.ofReal (tagSq b E W j k ω) ∂growthPathLaw W b =
            ∫⁻ ω, ENNReal.ofReal (j * W) * ENNReal.ofReal (tagSq b E W j k ω) ∂growthPathLaw W b :=
          fun k _ => (lintegral_const_mul _ (measurable_tagSq b E j k).ennreal_ofReal).symm
        rw [Finset.sum_congr rfl e1, ← lintegral_finsetSum _ fun k _ =>
          ((measurable_tagSq b E j k).ennreal_ofReal).const_mul _]
        refine lintegral_congr fun ω => ?_
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun k _ =>
          mul_nonneg hjW (tagSq_nonneg b E j k ω)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ENNReal.ofReal_mul hjW]
    _ ≤ ∑ _k ∈ Finset.range j, ENNReal.ofReal (j * W) * ENNReal.ofReal (C * ((j : ℝ) + 1)) :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
          (hC W hW E hE j k (Finset.mem_range.1 hk) hj) zero_le
    _ = ENNReal.ofReal (j * (j * W * (C * ((j : ℝ) + 1)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_mul hjW,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hj0]
    _ ≤ ENNReal.ofReal (C * W * ((j : ℝ) + 1) ^ 3) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (j : ℝ) * j ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
        have h2 : 0 ≤ C * W * ((j : ℝ) + 1) := by positivity
        calc (j : ℝ) * (j * W * (C * ((j : ℝ) + 1))) = (j * j) * (C * W * ((j : ℝ) + 1)) := by
              ring
          _ ≤ ((j : ℝ) + 1) ^ 2 * (C * W * ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_right h1 h2
          _ = C * W * ((j : ℝ) + 1) ^ 3 := by ring

/-- **Births of the tag square.** -/
theorem sqBirthMoments_of (hFS : FullSourceEstimates) (hGA : GaussianAbsorptionContract) :
    SqBirthMoments := by
  intro b hb0 hb κ hκ q hq
  obtain ⟨CD, WD, hD⟩ := hFS.moments b hb0 hb κ hκ ((4 * q : ℕ) : ℝ)
    (by exact_mod_cast (show 1 ≤ 4 * q by omega))
  obtain ⟨B0, W0, hB0, h0⟩ := birth_sq_zero hGA hb0 hb hκ hq
  refine ⟨max B0 ((max CD 0) ^ (4 * q)), max (max WD W0) 1, le_max_of_le_left hB0,
    fun W hW E hE k => ?_⟩
  have hWD : WD ≤ W := le_trans (by simp) hW
  have hW0 : W0 ≤ W := le_trans (by simp) hW
  have hW1 : 1 ≤ W := le_trans (by simp) hW
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (h0 W hW0 E hE).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · refine (birth_sq_succ hb0 hb hE1 hE2 hW1 hk hq (le_max_right CD 0) fun XX hXX =>
      (hD W hWD E hE XX hXX).2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))).trans ?_
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **`ClockSquareBulk`** from the Gaussian inputs and `FullSourceEstimates`. -/
theorem clockSquareBulk_holds (hFS : FullSourceEstimates) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hSR : ScalarRecursionContract) : ClockSquareBulk :=
  clockSquare_of_tagSq (tagSqBulk_of hFS (passiveMeanStep_holds (passiveBounds_holds hGA hLp))
    (passiveFluctuationStep_holds hGA hLp) (superexpExit_of hSR) (sqBirthMoments_of hFS hGA)
    (tagPropagationBulk_holds hFS hGA hLp hSR))

/-- **`FullSourceMomentsContract`** from the Gaussian inputs and
the one-layer hypothesis `FullSourceEstimates`. -/
theorem fullSourceMoments_of_estimates (hFS : FullSourceEstimates)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : FullSourceMomentsContract :=
  fullSourceMoments_of_clockSquare hFS hGA hLp hSR (clockSquareBulk_holds hFS hGA hLp hSR)

/-- **`FullSourceMomentsBulk`** from the Gaussian inputs and `FullSourceEstimates`. -/
theorem fullSourceMomentsBulk_of_estimates (hFS : FullSourceEstimates)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : FullSourceMomentsBulk :=
  fullSourceMomentsBulk_of hFS hGA hLp hSR (clockSquareBulk_holds hFS hGA hLp hSR)

end BlockBand.SourceProcess.FullSource
