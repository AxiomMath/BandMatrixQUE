module

public import BlockBand.Endpoints.Sine.LocalMassFlatClock
public import BlockBand.Endpoints.Sine.LocalMassFlatSubseq

/-!
# The ratio `Z/M` is close to one on the matched-lead path

Steps 1 and 3 of the proof of the local-mass flatness theorem. The paper bounds
`E|Z/M - 1| ≤ (E|Z-M|²)^{1/2}(EM^{-2})^{1/2} ≤ C√τ` for every joint subsequential limit
`(Z, M)`; we prove the prelimit form for the bounded test `min(|x - 1|, 1)`, which is all that
Step 4 uses (only bounded continuous tests are transferred by the microscopic tag comparison):

`lmf_pathRatio_eventually`: fixed `0 < b < 1/2`, bulk `E`, `T₀ > 0`; there is `C ≥ 0` such that
for every `τ ∈ (0,T₀]`, every `ClockSequence` (`r_j/W_j → τ`, energies `E_j → E`) and every
`ε > 0`, eventually
`E_{path,h} r⁻¹ Σ_{K<r} min(|Z_{r;K}/M_r - 1|, 1) ≤ C√τ + ε` (`lmf_ratioDefect`).

Proof (no inverse moment before the limit): for `λ, t > 0`, pointwise,
`min(|Z/M - 1|, 1) ≤ (λ/2)(Z-M)² + (1/(2λ) + t²)(max(M,t))^{-2}` (`lmf_min_ratio_le`), then
`(Z-M)² ≤ 2(Z-d)² + 2(M-d)²`; the tagged averages come from the tagged convex-order theorem
(`LmfTaggedFlat`, `p = 1`), the bounded test `(max(M,t))^{-2}` is controlled by the limiting
inverse moment of the clock small-ball lemma and tightness from the negative-clock theorem
(`lmf_eventually_invSq_le`); finally `λ = τ^{-1/2}` and `t, η → 0`.
Hypotheses: `NegativeClockContract`, `ClockSmallBallContract` and `LmfTaggedFlat` (explicit
binders).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal

/-- The averaged ratio defect `E_{path,h} r⁻¹ Σ_{K<r} min(|Z_{r;K}/M_r - 1|, 1)` at energy `e`. -/
def lmf_ratioDefect (b e : ℝ) (W r : ℕ) : ℝ :=
  ∫ x, (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1
    ∂probedClockLaw W b

/-!
## The pointwise inequality
-/

/-- `min(|Z/M - 1|, 1) ≤ (λ/2)(Z-M)² + (1/(2λ) + t²)(max(M,t))^{-2}` for `λ, t > 0`. -/
theorem lmf_min_ratio_le (Z M lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    min |Z / M - 1| 1 ≤
      lam / 2 * (Z - M) ^ 2 + (1 / (2 * lam) + t ^ 2) * ((max M t) ^ 2)⁻¹ := by
  rcases lt_or_ge t M with hM | hM
  · have hM0 : 0 < M := ht.trans hM
    rw [max_eq_left hM.le]
    have h1 : |Z / M - 1| = |Z - M| * M⁻¹ := by
      rw [div_sub_one hM0.ne', abs_div, abs_of_pos hM0, div_eq_mul_inv]
    have h2 : |Z - M| * M⁻¹ ≤ lam / 2 * (Z - M) ^ 2 + 1 / (2 * lam) * (M ^ 2)⁻¹ := by
      rw [← sq_abs (Z - M), ← inv_pow]
      have e : lam / 2 * |Z - M| ^ 2 + 1 / (2 * lam) * (M⁻¹) ^ 2 - |Z - M| * M⁻¹ =
          (lam * |Z - M| - M⁻¹) ^ 2 / (2 * lam) := by
        field_simp
        ring
      have : 0 ≤ (lam * |Z - M| - M⁻¹) ^ 2 / (2 * lam) := by positivity
      linarith
    have h3 : 0 ≤ t ^ 2 * (M ^ 2)⁻¹ := by positivity
    calc min |Z / M - 1| 1 ≤ |Z / M - 1| := min_le_left _ _
      _ ≤ _ := by rw [h1]; nlinarith
  · rw [max_eq_right hM]
    have h0 : 0 ≤ lam / 2 * (Z - M) ^ 2 := by positivity
    have h1 : t ^ 2 * (t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 ht.ne')
    have h2 : 0 ≤ 1 / (2 * lam) * (t ^ 2)⁻¹ := by positivity
    calc min |Z / M - 1| 1 ≤ 1 := min_le_right _ _
      _ ≤ _ := by nlinarith

/-- The averaged pointwise bound, `r > 0`:
`r⁻¹Σ_K min(|Z_K/M - 1|, 1) ≤ λ r⁻¹Σ_K(Z_K-d)² + λ(M-d)² + (1/(2λ)+t²)(max(M,t))^{-2}`. -/
theorem lmf_avg_min_ratio_le {r : ℕ} (hr : 0 < r) (Z : Fin r → ℝ) (M d lam t : ℝ)
    (hlam : 0 < lam) (ht : 0 < t) :
    (r : ℝ)⁻¹ * ∑ K, min |Z K / M - 1| 1 ≤
      lam * ((r : ℝ)⁻¹ * ∑ K, (Z K - d) ^ 2) + lam * (M - d) ^ 2 +
        (1 / (2 * lam) + t ^ 2) * ((max M t) ^ 2)⁻¹ := by
  have hr' : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have hK : ∀ K, min |Z K / M - 1| 1 ≤ lam * (Z K - d) ^ 2 + (lam * (M - d) ^ 2 +
      (1 / (2 * lam) + t ^ 2) * ((max M t) ^ 2)⁻¹) := by
    intro K
    have h := lmf_min_ratio_le (Z K) M lam t hlam ht
    have : (Z K - M) ^ 2 ≤ 2 * (Z K - d) ^ 2 + 2 * (M - d) ^ 2 := by
      nlinarith [sq_nonneg (Z K - d + (M - d))]
    nlinarith
  calc (r : ℝ)⁻¹ * ∑ K, min |Z K / M - 1| 1
      ≤ (r : ℝ)⁻¹ * ∑ K : Fin r, (lam * (Z K - d) ^ 2 + (lam * (M - d) ^ 2 +
          (1 / (2 * lam) + t ^ 2) * ((max M t) ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun K _ => hK K) (by positivity)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, mul_add, ← mul_assoc ((r : ℝ)⁻¹) (r : ℝ),
        inv_mul_cancel₀ hr'.ne', one_mul]
      ring

/-!
## One width: the ratio defect is bounded by the three expectations
-/

theorem lmf_sum_rev_range {r : ℕ} (g : ℕ → ℝ≥0∞) :
    ∑ K : Fin r, g (r - 1 - K.val) = ∑ k ∈ Finset.range r, g k := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun K => by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega

/-- **One width.** For `λ, t > 0` and every `d`:
`E[defect] ≤ λ r⁻¹Σ_{k<r} E|Z_{r;k} - d|² + λ E|M_r - d|² + (1/(2λ)+t²) E(max(M_r,t))^{-2}`
(the first two as lower integrals in `ℝ≥0∞`). -/
theorem lmf_ratioDefect_le (b e : ℝ) (W r : ℕ) (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (d : ℝ) :
    ENNReal.ofReal (lmf_ratioDefect b e W r) ≤
      ENNReal.ofReal lam * (((r : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range r,
          ∫⁻ x, ENNReal.ofReal (|lmf_tagResponseClock b e W r k x - d| ^ (2 * 1))
            ∂probedClockLaw W b) +
      ENNReal.ofReal lam * ∫⁻ x, ENNReal.ofReal (|lmf_meanClock b e W r x - d| ^ (2 * 1))
          ∂probedClockLaw W b +
      ENNReal.ofReal ((1 / (2 * lam) + t ^ 2) *
          ∫ x, lmf_invSqTest t ht (lmf_meanClock b e W r x) ∂probedClockLaw W b) := by
  have := lmf_isProbabilityMeasure_probedClockLaw W b
  set P := probedClockLaw W b
  set c : ℝ := 1 / (2 * lam) + t ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hMm : Measurable (fun x => lmf_meanClock b e W r x) :=
    lmf_measurable_meanClock_of b W r (measurable_const (a := e)) measurable_id
  have hZm : ∀ K : Fin r, Measurable (fun x => lmf_tagClock b e W r K x) := fun K =>
    lmf_measurable_tagClock_of b W r K (measurable_const (a := e)) measurable_id
  have hLm : Measurable (fun x => (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) :=
    measurable_const.mul (Finset.measurable_sum _ fun K _ =>
      ((continuous_abs.measurable.comp (((hZm K).div hMm).sub measurable_const)).min
        measurable_const))
  have hL0 : ∀ x, 0 ≤ (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1 := fun x =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun K _ => le_min (abs_nonneg _) zero_le_one)
  have hL1 : ∀ x, (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1 ≤ 1 := by
    intro x
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · have hr' : (0 : ℝ) < r := Nat.cast_pos.2 hr
      calc (r : ℝ)⁻¹ * ∑ K : Fin r,
            min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1
          ≤ (r : ℝ)⁻¹ * ∑ _K : Fin r, (1 : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun K _ => min_le_right _ _)
              (by positivity)
        _ = 1 := by simp [hr'.ne']
  have hfm : Measurable (fun x => lmf_invSqTest t ht (lmf_meanClock b e W r x)) :=
    (lmf_invSqTest t ht).continuous.measurable.comp hMm
  have hfint : Integrable (fun x => lmf_invSqTest t ht (lmf_meanClock b e W r x)) P := by
    refine Integrable.of_bound hfm.aestronglyMeasurable ((t ^ 2)⁻¹) (Eventually.of_forall ?_)
    intro x
    rw [Real.norm_eq_abs, lmf_invSqTest_apply, abs_of_nonneg (by positivity)]
    exact inv_anti₀ (pow_pos ht 2) (pow_le_pow_left₀ ht.le (le_max_right _ t) 2)
  -- the defect as a lower integral
  have hLint : Integrable (fun x => (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) P := by
    refine Integrable.of_bound hLm.aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hL0 x)]
    exact hL1 x
  unfold lmf_ratioDefect
  rw [ofReal_integral_eq_lintegral_ofReal hLint (Eventually.of_forall hL0)]
  -- the last term as a lower integral
  have hlast : ENNReal.ofReal (c * ∫ x, lmf_invSqTest t ht (lmf_meanClock b e W r x) ∂P) =
      ∫⁻ x, ENNReal.ofReal (c * lmf_invSqTest t ht (lmf_meanClock b e W r x)) ∂P := by
    rw [← integral_const_mul]
    exact ofReal_integral_eq_lintegral_ofReal (hfint.const_mul c)
      (Eventually.of_forall fun x => mul_nonneg hc0 (lmf_invSqTest_nonneg t ht _))
  rw [hlast]
  -- pointwise bound
  have hmZ : ∀ k, Measurable (fun x => ENNReal.ofReal
      (|lmf_tagResponseClock b e W r k x - d| ^ (2 * 1))) := fun k =>
    ENNReal.measurable_ofReal.comp
      (((lmf_measurable_tagResponseClock b e W r k).sub measurable_const).abs.pow_const _)
  have hF₁ : Measurable (fun x => ((r : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range r,
      ENNReal.ofReal (|lmf_tagResponseClock b e W r k x - d| ^ (2 * 1))) :=
    measurable_const.mul (Finset.measurable_sum _ fun k _ => hmZ k)
  have hF₂ : Measurable (fun x => ENNReal.ofReal (|lmf_meanClock b e W r x - d| ^ (2 * 1))) :=
    ENNReal.measurable_ofReal.comp ((hMm.sub measurable_const).abs.pow_const _)
  have hpt : ∀ x, ENNReal.ofReal ((r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) ≤
      (ENNReal.ofReal lam * (((r : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range r,
          ENNReal.ofReal (|lmf_tagResponseClock b e W r k x - d| ^ (2 * 1))) +
        ENNReal.ofReal lam * ENNReal.ofReal (|lmf_meanClock b e W r x - d| ^ (2 * 1))) +
        ENNReal.ofReal (c * lmf_invSqTest t ht (lmf_meanClock b e W r x)) := by
    intro x
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    have hr' : (0 : ℝ) < r := Nat.cast_pos.2 hr
    have h := lmf_avg_min_ratio_le hr (fun K => lmf_tagClock b e W r K x)
      (lmf_meanClock b e W r x) d lam t hlam ht
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ (le_of_eq ?_))
    · refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ ?_)
      · rw [ENNReal.ofReal_mul hlam.le]
        gcongr
        refine le_of_eq ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hr',
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg (fun K _ => sq_nonneg _)]
        congr 1
        rw [← lmf_sum_rev_range]
        refine Finset.sum_congr rfl fun K _ => ?_
        rw [lmf_tagClock_eq, mul_one, sq_abs]
      · rw [ENNReal.ofReal_mul hlam.le, mul_one, sq_abs]
    · rw [lmf_invSqTest_apply]
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_add_left (show Measurable (fun x => ENNReal.ofReal lam *
      (((r : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range r,
          ENNReal.ofReal (|lmf_tagResponseClock b e W r k x - d| ^ (2 * 1))) +
        ENNReal.ofReal lam * ENNReal.ofReal (|lmf_meanClock b e W r x - d| ^ (2 * 1))) from
      (hF₁.const_mul _).add (hF₂.const_mul _)),
    lintegral_add_left (hF₁.const_mul _), lintegral_const_mul _ hF₁, lintegral_const_mul _ hF₂,
    lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hmZ k),
    lintegral_finsetSum _ fun k _ => hmZ k]

/-!
## Along a clock sequence
-/

/-- The final choice of parameters: `λ = σ⁻¹`, `η ≤ εσ/(3(4+σ²))`, `t² = ε/(3(C₂+1))`. -/
theorem lmf_final_arith (A C₂ σ ε η t : ℝ) (hσ : 0 < σ) (hε : 0 < ε) (hη1 : η ≤ 1) (hη : η * (4 + σ ^ 2) ≤ ε * σ / 3)
    (ht : t ^ 2 * (C₂ + 1) = ε / 3) :
    2 * σ⁻¹ * (A * σ ^ 2 + η) + (1 / (2 * σ⁻¹) + t ^ 2) * (C₂ + η) ≤
      (2 * A + C₂ / 2) * σ + ε := by
  have e1 : 2 * σ⁻¹ * (A * σ ^ 2 + η) + (1 / (2 * σ⁻¹) + t ^ 2) * (C₂ + η) =
      (2 * A + C₂ / 2) * σ + η * (4 + σ ^ 2) / (2 * σ) + t ^ 2 * (C₂ + η) := by
    field_simp
    ring
  rw [e1]
  have h1 : η * (4 + σ ^ 2) / (2 * σ) ≤ ε / 6 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : t ^ 2 * (C₂ + η) ≤ ε / 3 := by
    rw [← ht]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
  linarith

/-- **Step 1 at the prelimit level** (with Step 3). Fixed
`0 < b < 1/2`, bulk `E`, `T₀ > 0`: one `C ≥ 0` such that for every `τ ∈ (0,T₀]`, every clock
sequence (`r_j/W_j → τ`, energies `E_j → E`) and every `ε > 0`, eventually
`E_{path,h} r⁻¹ Σ_K min(|Z_{r;K}/M_r - 1|, 1) ≤ C√τ + ε`. -/
theorem lmf_pathRatio_eventually (hNeg : NegativeClockContract)
    (hSmall : ClockSmallBallContract) (hTag : LmfTaggedFlat)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ) (hE : -2 < E) (hE' : E < 2) (T₀ : ℝ)
    (hT₀ : 0 < T₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ T₀ → ∀ s : ClockSequence τ E, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, lmf_ratioDefect b (s.energy j) (s.W j) (s.n j) ≤ C * Real.sqrt τ + ε := by
  obtain ⟨C₁, hC₁⟩ := hTag b hb hb' E hE hE' T₀ hT₀ 1 one_pos
  obtain ⟨C₂, hC₂0, hC₂⟩ := lmf_eventually_invSq_le hNeg hSmall b hb hb' E hE hE' T₀ hT₀
  set A := max C₁ 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  refine ⟨2 * A + C₂ / 2, by positivity, fun τ hτ hτT s ε hε => ?_⟩
  obtain ⟨hZ, hM⟩ := hC₁ τ hτ hτT s
  set σ := Real.sqrt τ with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hτ
  have hτσ : τ = σ ^ 2 := (Real.sq_sqrt hτ.le).symm
  set η : ℝ := min 1 (ε * σ / (3 * (4 + σ ^ 2))) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη : η * (4 + σ ^ 2) ≤ ε * σ / 3 := by
    have := min_le_right 1 (ε * σ / (3 * (4 + σ ^ 2)))
    rw [← hηdef, le_div_iff₀ (by positivity)] at this
    linarith
  set t : ℝ := Real.sqrt (ε / (3 * (C₂ + 1))) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have ht2 : t ^ 2 * (C₂ + 1) = ε / 3 := by
    rw [htdef, Real.sq_sqrt (by positivity)]
    field_simp
  -- eventual bounds on the three expectations
  have hlt : ENNReal.ofReal (C₁ * τ ^ 1) < ENNReal.ofReal (A * τ + η) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have : C₁ * τ ≤ A * τ := mul_le_mul_of_nonneg_right (le_max_left _ _) hτ.le
    rw [pow_one]
    linarith
  have hZ' := eventually_lt_of_limsup_lt (lt_of_le_of_lt hZ hlt)
  have hM' := eventually_lt_of_limsup_lt (lt_of_le_of_lt hM hlt)
  have hD := hC₂ τ hτ hτT s (lmf_measurable_scaledClock b s) (lmf_measurable_rescaledClock b s)
    t ht η hη0
  filter_upwards [hZ', hM', hD] with j hZj hMj hDj
  have hmean : ∀ x, lmf_meanClock b (s.energy j) (s.W j) (s.n j) x = rescaledClock b s j x :=
    lmf_meanClock_eq_rescaledClock b s j
  have key := lmf_ratioDefect_le b (s.energy j) (s.W j) (s.n j) σ⁻¹ t (inv_pos.2 hσ) ht
    (dStar b)
  simp_rw [hmean] at key
  have hc0 : 0 ≤ 1 / (2 * σ⁻¹) + t ^ 2 := by positivity
  have hbound : ENNReal.ofReal (lmf_ratioDefect b (s.energy j) (s.W j) (s.n j)) ≤
      ENNReal.ofReal (2 * σ⁻¹ * (A * σ ^ 2 + η) + (1 / (2 * σ⁻¹) + t ^ 2) * (C₂ + η)) := by
    have hR : ENNReal.ofReal (2 * σ⁻¹ * (A * σ ^ 2 + η) + (1 / (2 * σ⁻¹) + t ^ 2) * (C₂ + η)) =
        ENNReal.ofReal σ⁻¹ * ENNReal.ofReal (A * τ + η) +
          ENNReal.ofReal σ⁻¹ * ENNReal.ofReal (A * τ + η) +
          ENNReal.ofReal ((1 / (2 * σ⁻¹) + t ^ 2) * (C₂ + η)) := by
      rw [← hτσ, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    rw [hR]
    refine key.trans (add_le_add (add_le_add ?_ ?_) ?_)
    · gcongr
    · gcongr
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hDj hc0)
  have hfin := lmf_final_arith A C₂ σ ε η t hσ hε hη1 hη ht2
  have hpos : 0 ≤ 2 * σ⁻¹ * (A * σ ^ 2 + η) + (1 / (2 * σ⁻¹) + t ^ 2) * (C₂ + η) := by
    positivity
  have := (ENNReal.ofReal_le_ofReal_iff hpos).1 hbound
  linarith

end BlockBand.Endpoints
