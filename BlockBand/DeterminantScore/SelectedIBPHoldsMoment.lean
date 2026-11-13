module

public import BlockBand.DeterminantScore.SelectedIBPBounds
public import BlockBand.DeterminantScore.GUENormTailProofMoment
public import BlockBand.DeterminantScore.PhysicalColumnInner

/-!
# The fixed-exterior tail of `Tr G R_η`: expectation term and gradient moment

Item (4) of `WeightedTrace.SelectedResolventStatement` (`SelectedResolvent.SelectedIBPStatement`),
following the proof of the physical real-loop proposition at deterministic exterior data:
`R = (K + G - iη)⁻¹`, `G ~ GUE_ι(t)`, `d = |ι|`, `t d ≤ 1`, a reference `m` with `|m| ≤ 2` and the
averaged local law in the form `P(ℓ/η < |Tr R - d m|) ≤ β` (`ℓ/η ≤ d`).

* `one_add_pow_le`, **`lintegral_one_add_norm_pow_le`**: `E (1 + ‖G‖)^k ≤ yConst k` when
  `t (|ι| + 1) ≤ 2` (from `GUENormTail.gueNormMoment_le`).
* `norm_trace_res_le`: `|Tr R| ≤ d/η`; `sqrt_hsNorm_res_le`: `√t ‖R‖_HS ≤ √(tτ/η)` if
  `|Tr R| ≤ τ` (Ward identity `eta_mul_hsNorm_res_sq`).
* **`norm_expect_le`**: `t |E[(Tr R)² - (d m)²]| ≤ 5ℓ/η + 5` if `d β ≤ η²`.
* **`lintegral_grad_pow_le`**: for `a > 0` with `3 ≤ a² η³` and `β ≤ ηⁿ`,
  `E (√t ‖R - RGR‖_HS)ⁿ ≤ aⁿ (yConst n + yConst (2n) + 1)` (good/bad split at the local-law
  event; on the bad event `y^n ≤ Λⁿ + y^{2n}/Λⁿ`).
* **`section_tail`**: from `Inputs.GaussianLpGradient` (through `SelectedIBP.traceGRes_tail`), an
  absolute `C₀` such that for every deterministic centre `q` with `|t (d m)² - q| ≤ σ` and
  threshold `B ≥ u + 5ℓ/η + 5 + σ`:
  `P(B < |Tr(G R) + q|) ≤ (C₀ √n M/u)ⁿ`, `M = a (yConst n + yConst (2n) + 1)^{1/n}`.

The only input is `Inputs.GaussianLpGradient` (`section_tail`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedIBPHolds

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open BlockBand.DeterminantScore.SelectedIBP
open scoped NNReal ENNReal Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-!
## Moments of `1 + ‖G‖`
-/

/-- The moment constant `2^k (1 + C_k 2^{k/2})` of `1 + ‖G‖`. -/
def yConst (k : ℕ) : ℝ := 2 ^ k * (1 + GUENormTail.gueMomentConst k * 2 ^ ((k : ℝ) / 2))

theorem yConst_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ yConst k := by
  have hq : (0 : ℝ) < k := by exact_mod_cast hk
  have := GUENormTail.gueMomentConst_nonneg hq
  unfold yConst; positivity

theorem one_add_pow_le (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ k ≤ 2 ^ k * (1 + y ^ k) := by
  have hyk : 0 ≤ y ^ k := pow_nonneg hy k
  rcases le_total y 1 with h | h
  · calc (1 + y) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + y ^ k) := le_mul_of_one_le_right (by positivity) (by linarith)
  · calc (1 + y) ^ k ≤ (2 * y) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * y ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + y ^ k) := by
          have : (0 : ℝ) ≤ 2 ^ k := by positivity
          nlinarith

/-- **Moments of `1 + ‖G‖`** (operator norm): `E_{GUE_ι(t)} (1 + ‖G‖)^k ≤ yConst k` when
`t (|ι| + 1) ≤ 2`, `k ≥ 1`. -/
theorem lintegral_one_add_norm_pow_le {k : ℕ} (hk : 1 ≤ k) (t : ℝ≥0)
    (ht : (t : ℝ) * (Fintype.card ι + 1) ≤ 2) :
    ∫⁻ G, ENNReal.ofReal ((1 + ‖G‖) ^ k) ∂gueMeasure ι t ≤ ENNReal.ofReal (yConst k) := by
  have hq : (0 : ℝ) < k := by exact_mod_cast hk
  have hC := GUENormTail.gueMomentConst_nonneg hq
  have hmom := GUENormTail.gueNormMoment_le hq ι t
  have hnm : Measurable fun G : Matrix ι ι ℂ => ‖G‖ := continuous_norm.measurable
  have hprob := PhysicalColumn.isProbabilityMeasure_gue ι t
  have hpt : ∀ G : Matrix ι ι ℂ, ENNReal.ofReal ((1 + ‖G‖) ^ k) ≤
      ENNReal.ofReal (2 ^ k) + ENNReal.ofReal (2 ^ k) * ENNReal.ofReal (‖G‖ ^ (k : ℝ)) := by
    intro G
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity), Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := one_add_pow_le k (norm_nonneg G)
    linarith
  have hb : ((t : ℝ) * (Fintype.card ι + 1)) ^ ((k : ℝ) / 2) ≤ 2 ^ ((k : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) ht (by positivity)
  calc ∫⁻ G, ENNReal.ofReal ((1 + ‖G‖) ^ k) ∂gueMeasure ι t
      ≤ ∫⁻ G, (ENNReal.ofReal (2 ^ k) +
          ENNReal.ofReal (2 ^ k) * ENNReal.ofReal (‖G‖ ^ (k : ℝ))) ∂gueMeasure ι t :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ k) + ENNReal.ofReal (2 ^ k) *
          ∫⁻ G, ENNReal.ofReal (‖G‖ ^ (k : ℝ)) ∂gueMeasure ι t := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (hnm.pow_const _).ennreal_ofReal]
    _ ≤ ENNReal.ofReal (2 ^ k) + ENNReal.ofReal (2 ^ k) *
          ENNReal.ofReal (GUENormTail.gueMomentConst k * 2 ^ ((k : ℝ) / 2)) := by
        gcongr
        exact hmom.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb hC))
    _ = ENNReal.ofReal (yConst k) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        unfold yConst; ring_nf

/-!
## Deterministic resolvent bounds
-/

/-- `|Tr R| ≤ |ι|/η`. -/
theorem norm_trace_res_le {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ}
    (hη : 0 < η) : ‖(res K η G).trace‖ ≤ Fintype.card ι / η := by
  simp only [Matrix.trace, Matrix.diag]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun a _ => norm_res_apply_le hKG hη.ne' a a).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, abs_of_pos hη, div_eq_mul_inv]

/-- **Ward bound**: if `|Tr R| ≤ τ`, then `√t ‖R‖_HS ≤ √(tτ/η)`. -/
theorem sqrt_hsNorm_res_le {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ}
    (hη : 0 < η) (t : ℝ≥0) {τ : ℝ} (hτ : ‖(res K η G).trace‖ ≤ τ) :
    Real.sqrt t * hsNorm (res K η G) ≤ Real.sqrt ((t : ℝ) * τ / η) := by
  have hw := eta_mul_hsNorm_res_sq hKG hη.ne'
  have hs0 := hsNorm_nonneg (res K η G)
  have h1 : Real.sqrt t * hsNorm (res K η G) = Real.sqrt ((t : ℝ) * hsNorm (res K η G) ^ 2) := by
    rw [Real.sqrt_mul (NNReal.coe_nonneg t), Real.sqrt_sq hs0]
  rw [h1]
  refine Real.sqrt_le_sqrt ?_
  have h2 : hsNorm (res K η G) ^ 2 ≤ τ / η := by
    rw [le_div_iff₀ hη]
    have := Complex.im_le_norm (res K η G).trace
    nlinarith
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg t)

theorem continuous_hsNorm : Continuous (hsNorm : Matrix ι ι ℂ → ℝ) := by
  unfold hsNorm
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun a _ => continuous_finsetSum _
    fun b _ => ((continuous_apply b).comp (continuous_apply a)).norm.pow 2)

theorem measurable_trace_res (K : Matrix ι ι ℂ) (η : ℝ) :
    Measurable fun G : Matrix ι ι ℂ => (res K η G).trace :=
  continuous_id.matrix_trace.measurable.comp (measurable_res K η)

/-- The local-law failure set `{ℓ/η < |Tr R - d m|}` at deterministic data. -/
def resBad (K : Matrix ι ι ℂ) (η ℓ : ℝ) (m : ℂ) : Set (Matrix ι ι ℂ) :=
  {G | ℓ / η < ‖(res K η G).trace - (Fintype.card ι : ℂ) * m‖}

theorem measurableSet_resBad (K : Matrix ι ι ℂ) (η ℓ : ℝ) (m : ℂ) :
    MeasurableSet (resBad K η ℓ m) :=
  measurableSet_lt measurable_const (((measurable_trace_res K η).sub measurable_const).norm)

/-!
## The expectation term
-/

/-- **The expectation term**: for Hermitian `K`, `0 < η ≤ 1`, `t |ι| ≤ 1`,
`|m| ≤ 2`, `0 ≤ ℓ`, `ℓ/η ≤ |ι|` and `P(resBad) ≤ β`, `|ι| β ≤ η²`:
`t |E[(Tr R)² - (|ι| m)²]| ≤ 5ℓ/η + 5`. -/
theorem norm_expect_le {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (t : ℝ≥0) (htd : (t : ℝ) * Fintype.card ι ≤ 1) {m : ℂ} (hm : ‖m‖ ≤ 2)
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ / η ≤ Fintype.card ι) {β : ℝ} (hβ0 : 0 ≤ β)
    (hBad : gueMeasure ι t (resBad K η ℓ m) ≤ ENNReal.ofReal β)
    (hβ2 : (Fintype.card ι : ℝ) * β ≤ η ^ 2) :
    (t : ℝ) * ‖∫ G, ((res K η G).trace ^ 2 - ((Fintype.card ι : ℂ) * m) ^ 2) ∂gueMeasure ι t‖ ≤
      5 * ℓ / η + 5 := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set c : ℂ := (Fintype.card ι : ℂ) * m with hc
  have hcn : ‖c‖ ≤ 2 * d := by
    rw [hc, norm_mul, Complex.norm_natCast]; nlinarith [norm_nonneg m]
  set S := resBad K η ℓ m
  have hS := measurableSet_resBad K η ℓ m
  have hS' : MeasurableSet (gueLin t ⁻¹' S) := (continuous_gueLin t).measurable hS
  set f : Matrix ι ι ℂ → ℂ := fun G => (res K η G).trace ^ 2 - c ^ 2 with hf
  have hfm : Measurable f := ((measurable_trace_res K η).pow_const 2).sub measurable_const
  set g : (GCoord ι → ℝ) → ℝ := fun x =>
    5 * d * (ℓ / η) + (gueLin t ⁻¹' S).indicator (fun _ => 5 * d ^ 2 / η ^ 2) x with hg
  have hgi : Integrable g (stdGauss ι) :=
    (integrable_const _).add ((integrable_const _).indicator hS')
  have hpt : ∀ x, ‖f (gueLin t x)‖ ≤ g x := by
    intro x
    have hKG : (K + gueLin t x).IsHermitian := hK.add (isHermitian_gueLin t x)
    have hR := norm_trace_res_le hKG hη
    rw [← hd] at hR
    set r := (res K η (gueLin t x)).trace
    have hfe : f (gueLin t x) = (r - c) * ((r - c) + 2 * c) := by rw [hf]; ring
    by_cases hx : gueLin t x ∈ S
    · rw [hg]; dsimp only; rw [Set.indicator_of_mem (show x ∈ gueLin t ⁻¹' S from hx)]
      have h1 : ‖f (gueLin t x)‖ ≤ ‖r‖ ^ 2 + ‖c‖ ^ 2 := by
        rw [hf]; dsimp only
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_pow, norm_pow]
      have hη2 : 0 < η ^ 2 := by positivity
      have h2 : ‖r‖ ^ 2 ≤ d ^ 2 / η ^ 2 := by
        rw [← div_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hR 2
      have h3 : ‖c‖ ^ 2 ≤ 4 * d ^ 2 / η ^ 2 := by
        have : ‖c‖ ^ 2 ≤ (2 * d) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcn 2
        have hq : (2 * d) ^ 2 ≤ 4 * d ^ 2 / η ^ 2 := by
          rw [le_div_iff₀ hη2]
          have : η ^ 2 ≤ 1 := pow_le_one₀ hη.le hη1
          nlinarith [sq_nonneg d]
        linarith
      have h4 : 0 ≤ 5 * d * (ℓ / η) := by positivity
      have : d ^ 2 / η ^ 2 + 4 * d ^ 2 / η ^ 2 = 5 * d ^ 2 / η ^ 2 := by ring
      linarith
    · rw [hg]; dsimp only; rw [Set.indicator_of_notMem (show x ∉ gueLin t ⁻¹' S from hx), add_zero, hfe,
        norm_mul]
      have hb : ‖r - c‖ ≤ ℓ / η := by
        have := hx; simp only [S, resBad, Set.mem_ofPred_eq, not_lt] at this; exact this
      have h2 : ‖(r - c) + 2 * c‖ ≤ 5 * d := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_two]
        linarith
      calc ‖r - c‖ * ‖(r - c) + 2 * c‖ ≤ (ℓ / η) * (5 * d) :=
            mul_le_mul hb h2 (norm_nonneg _) (by positivity)
        _ = 5 * d * (ℓ / η) := by ring
  have hint : ∫ G, f G ∂gueMeasure ι t = ∫ x, f (gueLin t x) ∂stdGauss ι := by
    rw [gueMeasure_eq_map_gueLin, integral_map (continuous_gueLin t).aemeasurable
      hfm.aestronglyMeasurable]
  have hE : ‖∫ G, f G ∂gueMeasure ι t‖ ≤ ∫ x, g x ∂stdGauss ι := by
    rw [hint]; exact norm_integral_le_of_norm_le hgi (ae_of_all _ hpt)
  have hP : (stdGauss ι).real (gueLin t ⁻¹' S) ≤ β := by
    rw [measureReal_def, ← Measure.map_apply (continuous_gueLin t).measurable hS,
      ← gueMeasure_eq_map_gueLin]
    exact ENNReal.toReal_le_of_le_ofReal hβ0 hBad
  have hgint : ∫ x, g x ∂stdGauss ι =
      5 * d * (ℓ / η) + (stdGauss ι).real (gueLin t ⁻¹' S) * (5 * d ^ 2 / η ^ 2) := by
    rw [hg, integral_add (integrable_const _) ((integrable_const _).indicator hS'),
      integral_const, integral_indicator_const _ hS']
    simp only [probReal_univ, smul_eq_mul, one_mul]
  rw [hgint] at hE
  have hP0 : 0 ≤ (stdGauss ι).real (gueLin t ⁻¹' S) := measureReal_nonneg
  have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have hη2 : 0 < η ^ 2 := by positivity
  have k1 : (t : ℝ) * (5 * d * (ℓ / η)) ≤ 5 * ℓ / η := by
    have : (t : ℝ) * (5 * d * (ℓ / η)) = 5 * (ℓ / η) * ((t : ℝ) * d) := by ring
    rw [this, mul_div_assoc]
    have : 0 ≤ 5 * (ℓ / η) := by positivity
    nlinarith
  have k2 : (t : ℝ) * ((stdGauss ι).real (gueLin t ⁻¹' S) * (5 * d ^ 2 / η ^ 2)) ≤ 5 := by
    have e : (t : ℝ) * ((stdGauss ι).real (gueLin t ⁻¹' S) * (5 * d ^ 2 / η ^ 2)) =
        5 * ((t : ℝ) * d) * (d * (stdGauss ι).real (gueLin t ⁻¹' S)) / η ^ 2 := by ring
    rw [e, div_le_iff₀ hη2]
    have hdP : d * (stdGauss ι).real (gueLin t ⁻¹' S) ≤ η ^ 2 :=
      (mul_le_mul_of_nonneg_left hP hd0).trans hβ2
    have h0 : 0 ≤ d * (stdGauss ι).real (gueLin t ⁻¹' S) := mul_nonneg hd0 hP0
    have h5 : 0 ≤ 5 * ((t : ℝ) * d) := by positivity
    calc 5 * ((t : ℝ) * d) * (d * (stdGauss ι).real (gueLin t ⁻¹' S))
        ≤ 5 * 1 * η ^ 2 := mul_le_mul (by linarith) hdP h0 (by norm_num)
      _ = 5 * η ^ 2 := by ring
  calc (t : ℝ) * ‖∫ G, f G ∂gueMeasure ι t‖
      ≤ (t : ℝ) * (5 * d * (ℓ / η) +
          (stdGauss ι).real (gueLin t ⁻¹' S) * (5 * d ^ 2 / η ^ 2)) :=
        mul_le_mul_of_nonneg_left hE ht0
    _ ≤ 5 * ℓ / η + 5 := by rw [mul_add]; linarith

/-!
## The gradient moment
-/

theorem continuous_gradField {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : η ≠ 0)
    (t : ℝ≥0) :
    Continuous fun x : GCoord ι → ℝ => Real.sqrt t * hsNorm (gradMat K η (gueLin t x)) := by
  have hR := continuous_res hK hη t
  have hB : Continuous fun x : GCoord ι → ℝ => gradMat K η (gueLin t x) := by
    unfold gradMat
    exact hR.sub ((hR.matrix_mul (continuous_gueLin t)).matrix_mul hR)
  exact continuous_const.mul (continuous_hsNorm.comp hB)

/-- **Pointwise gradient bound**: if `|Tr R| ≤ τ` and `0 < η ≤ 1`,
`√t ‖R - RGR‖_HS ≤ √(tτ/η) (1 + ‖G‖)/η`. -/
theorem grad_le {K G : Matrix ι ι ℂ} (hKG : (K + G).IsHermitian) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (t : ℝ≥0) {τ : ℝ} (hτ : ‖(res K η G).trace‖ ≤ τ) :
    Real.sqrt t * hsNorm (gradMat K η G) ≤ Real.sqrt ((t : ℝ) * τ / η) * ((1 + ‖G‖) / η) := by
  have hGop : ∀ v, ‖T G v‖ ≤ ‖G‖ * ‖v‖ := fun v => by
    rw [Matrix.l2_opNorm_def]
    exact ContinuousLinearMap.le_opNorm (LinearMap.toContinuousLinearMap (T G)) v
  have h1 := hsNorm_gradMat_le hKG hη.ne' (norm_nonneg G) hGop
  rw [abs_of_pos hη] at h1
  have h2 := sqrt_hsNorm_res_le hKG hη t hτ
  have h3 : 1 + ‖G‖ / η ≤ (1 + ‖G‖) / η := by
    rw [add_div]
    have : 1 ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
    linarith
  have hs0 := hsNorm_nonneg (res K η G)
  have hst : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have h4 : 0 ≤ 1 + ‖G‖ / η := by positivity
  calc Real.sqrt t * hsNorm (gradMat K η G)
      ≤ Real.sqrt t * (hsNorm (res K η G) * (1 + ‖G‖ / η)) :=
        mul_le_mul_of_nonneg_left h1 hst
    _ = (Real.sqrt t * hsNorm (res K η G)) * (1 + ‖G‖ / η) := by ring
    _ ≤ Real.sqrt ((t : ℝ) * τ / η) * ((1 + ‖G‖) / η) :=
        mul_le_mul h2 h3 h4 (Real.sqrt_nonneg _)

/-- **The gradient moment**: for Hermitian `K`, `0 < η ≤ 1`, `|ι| ≥ 1`,
`t |ι| ≤ 1`, `|m| ≤ 2`, `ℓ/η ≤ |ι|`, `P(resBad) ≤ β ≤ ηⁿ` and `a > 0` with `3 ≤ a² η³`:
`E (√t ‖R - RGR‖_HS)ⁿ ≤ aⁿ (yConst n + yConst (2n) + 1)` (standard coordinates). -/
theorem lintegral_grad_pow_le {n : ℕ} (hn : 1 ≤ n) {K : Matrix ι ι ℂ} (hK : K.IsHermitian)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (t : ℝ≥0) (hd1 : 1 ≤ (Fintype.card ι : ℝ))
    (htd : (t : ℝ) * Fintype.card ι ≤ 1) {m : ℂ} (hm : ‖m‖ ≤ 2) {ℓ : ℝ}
    (hℓ : ℓ / η ≤ Fintype.card ι) {β : ℝ} (hβ0 : 0 ≤ β)
    (hBad : gueMeasure ι t (resBad K η ℓ m) ≤ ENNReal.ofReal β) (hβ1 : β ≤ η ^ n) {a : ℝ}
    (ha : 0 < a) (ha3 : 3 ≤ a ^ 2 * η ^ 3) :
    ∫⁻ x, ENNReal.ofReal ((Real.sqrt t * hsNorm (gradMat K η (gueLin t x))) ^ n) ∂stdGauss ι ≤
      ENNReal.ofReal (a ^ n * (yConst n + yConst (2 * n) + 1)) := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have ht1 : (t : ℝ) * (Fintype.card ι + 1) ≤ 2 := by
    rw [← hd]
    have : (t : ℝ) ≤ (t : ℝ) * d := le_mul_of_one_le_right ht0 hd1
    nlinarith
  set Λ : ℝ := 1 / (η ^ 4 * a) with hΛ
  have hΛ0 : 0 < Λ := by positivity
  set S := resBad K η ℓ m
  have hS := measurableSet_resBad K η ℓ m
  have hS' : MeasurableSet (gueLin t ⁻¹' S) := (continuous_gueLin t).measurable hS
  set g : (GCoord ι → ℝ) → ℝ := fun x => Real.sqrt t * hsNorm (gradMat K η (gueLin t x))
  set Y : (GCoord ι → ℝ) → ℝ := fun x => 1 + ‖gueLin t x‖
  have hY0 : ∀ x, 0 ≤ Y x := fun x => by positivity
  have hpt : ∀ x, ENNReal.ofReal (g x ^ n) ≤
      ENNReal.ofReal (a ^ n * Y x ^ n) + (gueLin t ⁻¹' S).indicator
        (fun _ => ENNReal.ofReal (Λ ^ n)) x + ENNReal.ofReal (a ^ n * Y x ^ (2 * n)) := by
    intro x
    have hKG : (K + gueLin t x).IsHermitian := hK.add (isHermitian_gueLin t x)
    have hg0 : 0 ≤ g x := mul_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _)
    -- the global bound `g ≤ Y/η²`
    have hgall : g x ≤ Y x / η ^ 2 := by
      have h := grad_le hKG hη hη1 t (norm_trace_res_le hKG hη)
      have hs : Real.sqrt ((t : ℝ) * (Fintype.card ι / η) / η) ≤ 1 / η := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / η)]
        refine Real.sqrt_le_sqrt ?_
        rw [← hd]
        have e : (t : ℝ) * (d / η) / η = ((t : ℝ) * d) / η ^ 2 := by ring
        rw [e, div_pow, one_pow]
        exact div_le_div_of_nonneg_right htd (by positivity)
      calc g x ≤ Real.sqrt ((t : ℝ) * (Fintype.card ι / η) / η) * ((1 + ‖gueLin t x‖) / η) := h
        _ ≤ 1 / η * ((1 + ‖gueLin t x‖) / η) :=
            mul_le_mul_of_nonneg_right hs (by positivity)
        _ = Y x / η ^ 2 := by simp only [Y]; ring
    have hn0 : 0 ≤ ENNReal.ofReal (a ^ n * Y x ^ n) := zero_le
    by_cases hx : gueLin t x ∈ S
    · rw [Set.indicator_of_mem (show x ∈ gueLin t ⁻¹' S from hx)]
      set w := Y x / η ^ 2
      have hw0 : 0 ≤ w := by positivity
      have hgw : g x ^ n ≤ w ^ n := pow_le_pow_left₀ hg0 hgall n
      rcases le_or_gt w Λ with hwΛ | hwΛ
      · have : g x ^ n ≤ Λ ^ n := hgw.trans (pow_le_pow_left₀ hw0 hwΛ n)
        calc ENNReal.ofReal (g x ^ n) ≤ ENNReal.ofReal (Λ ^ n) := ENNReal.ofReal_le_ofReal this
          _ ≤ _ := le_add_right (le_add_left le_rfl)
      · have hw1 : 1 ≤ w / Λ := by rw [le_div_iff₀ hΛ0]; linarith
        have e : w * (w / Λ) = a * Y x ^ 2 := by
          simp only [w, hΛ]; field_simp
        have : g x ^ n ≤ a ^ n * Y x ^ (2 * n) := by
          calc g x ^ n ≤ w ^ n := hgw
            _ ≤ w ^ n * (w / Λ) ^ n := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hw1)
            _ = (w * (w / Λ)) ^ n := (mul_pow _ _ _).symm
            _ = a ^ n * Y x ^ (2 * n) := by rw [e, mul_pow, ← pow_mul, mul_comm 2 n]
        calc ENNReal.ofReal (g x ^ n) ≤ ENNReal.ofReal (a ^ n * Y x ^ (2 * n)) :=
              ENNReal.ofReal_le_ofReal this
          _ ≤ _ := le_add_left le_rfl
    · rw [Set.indicator_of_notMem (show x ∉ gueLin t ⁻¹' S from hx), add_zero]
      have hb : ‖(res K η (gueLin t x)).trace - (Fintype.card ι : ℂ) * m‖ ≤ ℓ / η := by
        have := hx; simp only [S, resBad, Set.mem_ofPred_eq, not_lt] at this; exact this
      have hτ : ‖(res K η (gueLin t x)).trace‖ ≤ 3 * d := by
        have hcm : ‖(Fintype.card ι : ℂ) * m‖ ≤ 2 * d := by
          rw [norm_mul, Complex.norm_natCast, ← hd]; nlinarith [norm_nonneg m]
        have := norm_le_norm_sub_add (res K η (gueLin t x)).trace ((Fintype.card ι : ℂ) * m)
        linarith
      have h := grad_le hKG hη hη1 t hτ
      have hs : Real.sqrt ((t : ℝ) * (3 * d) / η) ≤ a * η := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ a * η)]
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_iff₀ hη]
        have e : (a * η) ^ 2 * η = a ^ 2 * η ^ 3 := by ring
        rw [e]
        nlinarith
      have hga : g x ≤ a * Y x := by
        calc g x ≤ Real.sqrt ((t : ℝ) * (3 * d) / η) * ((1 + ‖gueLin t x‖) / η) := h
          _ ≤ a * η * ((1 + ‖gueLin t x‖) / η) := mul_le_mul_of_nonneg_right hs (by positivity)
          _ = a * Y x := by simp only [Y]; field_simp
      have : g x ^ n ≤ a ^ n * Y x ^ n := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hg0 hga n
      calc ENNReal.ofReal (g x ^ n) ≤ ENNReal.ofReal (a ^ n * Y x ^ n) :=
            ENNReal.ofReal_le_ofReal this
        _ ≤ _ := le_add_right le_rfl
  -- integrate
  have hYm : ∀ k : ℕ, Measurable fun x => ENNReal.ofReal (a ^ n * Y x ^ k) := fun k =>
    (measurable_const.mul ((measurable_const.add
      (continuous_norm.measurable.comp (continuous_gueLin t).measurable)).pow_const k)).ennreal_ofReal
  have hmap : ∀ k : ℕ, 1 ≤ k → ∫⁻ x, ENNReal.ofReal (a ^ n * Y x ^ k) ∂stdGauss ι ≤
      ENNReal.ofReal (a ^ n) * ENNReal.ofReal (yConst k) := by
    intro k hk
    have e : ∀ x, ENNReal.ofReal (a ^ n * Y x ^ k) =
        ENNReal.ofReal (a ^ n) * ENNReal.ofReal ((1 + ‖gueLin t x‖) ^ k) := fun x =>
      ENNReal.ofReal_mul (by positivity)
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right ?_ _
    have hf : Measurable fun G : Matrix ι ι ℂ => ENNReal.ofReal ((1 + ‖G‖) ^ k) :=
      ((measurable_const.add continuous_norm.measurable).pow_const k).ennreal_ofReal
    have := lintegral_one_add_norm_pow_le (ι := ι) hk t ht1
    rw [gueMeasure_eq_map_gueLin, lintegral_map hf (continuous_gueLin t).measurable] at this
    exact this
  have hind : ∫⁻ x, (gueLin t ⁻¹' S).indicator (fun _ => ENNReal.ofReal (Λ ^ n)) x ∂stdGauss ι ≤
      ENNReal.ofReal (Λ ^ n) * ENNReal.ofReal β := by
    rw [lintegral_indicator_const hS', ← Measure.map_apply (continuous_gueLin t).measurable hS,
      ← gueMeasure_eq_map_gueLin]
    exact mul_le_mul_right hBad _
  have hΛβ : Λ ^ n * β ≤ a ^ n := by
    have h1 : Λ * η ≤ a := by
      rw [hΛ, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith
    calc Λ ^ n * β ≤ Λ ^ n * η ^ n := mul_le_mul_of_nonneg_left hβ1 (by positivity)
      _ = (Λ * η) ^ n := (mul_pow _ _ _).symm
      _ ≤ a ^ n := pow_le_pow_left₀ (by positivity) h1 n
  have hy1 := yConst_nonneg hn
  have hy2 := yConst_nonneg (show 1 ≤ 2 * n by omega)
  calc ∫⁻ x, ENNReal.ofReal (g x ^ n) ∂stdGauss ι
      ≤ ∫⁻ x, (ENNReal.ofReal (a ^ n * Y x ^ n) + (gueLin t ⁻¹' S).indicator
          (fun _ => ENNReal.ofReal (Λ ^ n)) x + ENNReal.ofReal (a ^ n * Y x ^ (2 * n)))
          ∂stdGauss ι := lintegral_mono hpt
    _ = ∫⁻ x, ENNReal.ofReal (a ^ n * Y x ^ n) ∂stdGauss ι +
          ∫⁻ x, (gueLin t ⁻¹' S).indicator (fun _ => ENNReal.ofReal (Λ ^ n)) x ∂stdGauss ι +
          ∫⁻ x, ENNReal.ofReal (a ^ n * Y x ^ (2 * n)) ∂stdGauss ι := by
        have hm2 : Measurable fun x => ENNReal.ofReal (a ^ n * Y x ^ n) +
            (gueLin t ⁻¹' S).indicator (fun _ => ENNReal.ofReal (Λ ^ n)) x := by
          exact (hYm n).add (measurable_const.indicator hS')
        rw [lintegral_add_left hm2, lintegral_add_left (hYm n)]
    _ ≤ ENNReal.ofReal (a ^ n) * ENNReal.ofReal (yConst n) +
          ENNReal.ofReal (Λ ^ n) * ENNReal.ofReal β +
          ENNReal.ofReal (a ^ n) * ENNReal.ofReal (yConst (2 * n)) :=
        add_le_add (add_le_add (hmap n hn) hind) (hmap (2 * n) (by omega))
    _ = ENNReal.ofReal (a ^ n * yConst n + Λ ^ n * β + a ^ n * yConst (2 * n)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (a ^ n * (yConst n + yConst (2 * n) + 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith

/-- **The gradient `L^n` bound**: under the hypotheses of `lintegral_grad_pow_le`,
`‖√t ‖R - RGR‖_HS‖_{L^n} ≤ a (yConst n + yConst (2n) + 1)^{1/n}`. -/
theorem eLpNorm_grad_le {n : ℕ} (hn : 1 ≤ n) {K : Matrix ι ι ℂ} (hK : K.IsHermitian)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (t : ℝ≥0) (hd1 : 1 ≤ (Fintype.card ι : ℝ))
    (htd : (t : ℝ) * Fintype.card ι ≤ 1) {m : ℂ} (hm : ‖m‖ ≤ 2) {ℓ : ℝ}
    (hℓ : ℓ / η ≤ Fintype.card ι) {β : ℝ} (hβ0 : 0 ≤ β)
    (hBad : gueMeasure ι t (resBad K η ℓ m) ≤ ENNReal.ofReal β) (hβ1 : β ≤ η ^ n) {a : ℝ}
    (ha : 0 < a) (ha3 : 3 ≤ a ^ 2 * η ^ 3) :
    eLpNorm (fun x => Real.sqrt t * hsNorm (gradMat K η (gueLin t x))) (ENNReal.ofReal n)
        (stdGauss ι) ≤
      ENNReal.ofReal (a * (yConst n + yConst (2 * n) + 1) ^ ((n : ℝ)⁻¹)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ : 0 ≤ yConst n + yConst (2 * n) + 1 := by
    have := yConst_nonneg hn
    have := yConst_nonneg (show 1 ≤ 2 * n by omega)
    linarith
  have hmom := lintegral_grad_pow_le hn hK hη hη1 t hd1 htd hm hℓ hβ0 hBad hβ1 ha ha3
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; omega) ENNReal.ofReal_ne_top
    (continuous_gradField hK hη.ne' t).aestronglyMeasurable, ENNReal.toReal_ofReal hn0.le]
  have e : ∀ x : GCoord ι → ℝ,
      ‖Real.sqrt t * hsNorm (gradMat K η (gueLin t x))‖ₑ ^ (n : ℝ) =
        ENNReal.ofReal ((Real.sqrt t * hsNorm (gradMat K η (gueLin t x))) ^ n) := by
    intro x
    have h0 : 0 ≤ Real.sqrt t * hsNorm (gradMat K η (gueLin t x)) :=
      mul_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _)
    rw [Real.enorm_eq_ofReal h0, ENNReal.ofReal_rpow_of_nonneg h0 hn0.le, Real.rpow_natCast]
  simp only [e]
  calc (∫⁻ x, ENNReal.ofReal ((Real.sqrt t * hsNorm (gradMat K η (gueLin t x))) ^ n)
          ∂stdGauss ι) ^ (1 / (n : ℝ))
      ≤ ENNReal.ofReal (a ^ n * (yConst n + yConst (2 * n) + 1)) ^ (1 / (n : ℝ)) :=
        ENNReal.rpow_le_rpow hmom (by positivity)
    _ = ENNReal.ofReal (a * (yConst n + yConst (2 * n) + 1) ^ ((n : ℝ)⁻¹)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          Real.mul_rpow (by positivity) hQ, Real.pow_rpow_inv_natCast ha.le (by omega)]

/-!
## The fixed-exterior tail
-/

/-- **The fixed-exterior tail of `Tr G R_η`.** From `Inputs.GaussianLpGradient` (through
`SelectedIBP.traceGRes_tail`): an absolute `C₀ > 0` such that for every `n ≥ 1`, finite `ι`
(`d = |ι| ≥ 1`), Hermitian `K`, `0 < η ≤ 1`, `t` with `t d ≤ 1`, reference `|m| ≤ 2`, local-law
loss `0 ≤ ℓ`, `ℓ/η ≤ d`, failure bound `P(resBad) ≤ β` with `β ≤ ηⁿ`, `d β ≤ η²`, scale `a > 0`,
`3 ≤ a² η³`, and every deterministic centre `q` with `|t (d m)² - q| ≤ σ` and threshold
`B ≥ u + (5ℓ/η + 5) + σ` (`u > 0`):
`GUE_ι(t){B < |Tr(G R) + q|} ≤ (C₀ √n M/u)ⁿ`, `M = a (yConst n + yConst (2n) + 1)^{1/n}`. -/
theorem section_tail (hLp : BlockBand.Internal.Contracts.Inputs.GaussianLpGradient) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 1 ≤ n → ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (K : Matrix ι ι ℂ), K.IsHermitian → ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ t : ℝ≥0,
      1 ≤ (Fintype.card ι : ℝ) → (t : ℝ) * Fintype.card ι ≤ 1 → ∀ m : ℂ, ‖m‖ ≤ 2 →
      ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ / η ≤ Fintype.card ι → ∀ β : ℝ, 0 ≤ β →
      gueMeasure ι t (resBad K η ℓ m) ≤ ENNReal.ofReal β → β ≤ η ^ n →
      (Fintype.card ι : ℝ) * β ≤ η ^ 2 → ∀ a : ℝ, 0 < a → 3 ≤ a ^ 2 * η ^ 3 →
      ∀ (u σ B : ℝ) (q : ℂ), 0 < u →
      ‖(t : ℂ) * ((Fintype.card ι : ℂ) * m) ^ 2 - q‖ ≤ σ → u + (5 * ℓ / η + 5) + σ ≤ B →
      gueMeasure ι t {G | B < ‖(G * res K η G).trace + q‖} ≤
        ENNReal.ofReal ((C₀ * Real.sqrt n *
          (a * (yConst n + yConst (2 * n) + 1) ^ ((n : ℝ)⁻¹)) / u) ^ (n : ℝ)) := by
  obtain ⟨C₀, hC₀, htail⟩ := traceGRes_tail hLp
  refine ⟨C₀, hC₀, fun n hn ι _ _ K hK η hη hη1 t hd1 htd m hm ℓ hℓ0 hℓ β hβ0 hBad hβ1 hβ2 a ha
    ha3 u σ B q hu hσ hB => ?_⟩
  have hQ : 0 ≤ yConst n + yConst (2 * n) + 1 := by
    have := yConst_nonneg hn
    have := yConst_nonneg (show 1 ≤ 2 * n by omega)
    linarith
  have hM0 : 0 ≤ a * (yConst n + yConst (2 * n) + 1) ^ ((n : ℝ)⁻¹) :=
    mul_nonneg ha.le (Real.rpow_nonneg hQ _)
  have hgrad := eLpNorm_grad_le hn hK hη hη1 t hd1 htd hm hℓ hβ0 hBad hβ1 ha ha3
  have h := htail n (by exact_mod_cast hn) ι K hK η hη.ne' t ((Fintype.card ι : ℂ) * m) u _
    hu hM0 hgrad
  refine (measure_mono fun G hG => ?_).trans h
  simp only [Set.mem_ofPred_eq] at hG ⊢
  have hE := norm_expect_le hK hη hη1 t htd hm hℓ0 hℓ hβ0 hBad hβ2
  have e : (G * res K η G).trace + q = ((G * res K η G).trace +
      (t : ℂ) * ((Fintype.card ι : ℂ) * m) ^ 2) - ((t : ℂ) * ((Fintype.card ι : ℂ) * m) ^ 2 - q) := by
    ring
  rw [e] at hG
  have := norm_sub_le ((G * res K η G).trace + (t : ℂ) * ((Fintype.card ι : ℂ) * m) ^ 2)
    ((t : ℂ) * ((Fintype.card ι : ℂ) * m) ^ 2 - q)
  linarith

end BlockBand.DeterminantScore.SelectedIBPHolds
