module

public import BlockBand.Critical.Herglotz.SmoothCutoff

/-!
# Smooth versus sharp cutoffs of the canonical series

The canonical series is a limit of sharp symmetric cutoffs `cauchyTruncation r ξ R z`
(`|x_j| ≤ R`); the smooth cutoff is `smoothCauchy r ξ L z = π⁻¹ Σ_j χ_L(x_j) g_j g_j^* / (x_j - z)`.
The two differ only through points with `L < |x_j| < L + 1`, whose expected Gaussian mass is
`O(r)` while `|x_j - z|⁻¹ = O(1/L)`. Law: `Ξ` a decorated sine process
(`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`.

* `smoothCauchy`, `cutoffBump` (`ψ_L = χ_L - χ_{L-2}`), `euclidMark` (`Σ_k |g_k|²`).
* `norm_cauchyTruncation_sub_smoothCauchy_le` — deterministic comparison for every locally
  finite `ξ` with `∫ ψ_L(x) Σ_k |g_k|² dξ < ∞`, uniformly in `z` with `|x - z| ≥ d` for `|x| > L`.
* `tendsto_measure_smoothSharp` — smooth versus sharp cutoffs: for every bounded `K ⊆ ℂ` and `ε > 0`,
  `P(∃ z ∈ K, ∃ i j, ε ≤ |cauchyTruncation_L(z)_ij - smoothCauchy_L(z)_ij|) → 0` as `L → ∞`.
* `IsCanonicalCauchy.tendsto_smoothCauchy_locallyUniform`,
  `IsCanonicalCauchy.tendstoInMeasure_smoothCauchy_real` — the smooth cutoffs converge to `𝖢_r`
  locally uniformly in probability on compact `K ⊆ {Im z > 0}` and in probability at real points.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-- Smooth cutoff `π⁻¹ Σ_j χ_L(x_j) g_j g_j^* / (x_j - z)` of the canonical Cauchy series, entrywise
(Lean's `0⁻¹ = 0` at a real pole). -/
def smoothCauchy (r : ℕ) (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (L : ℝ) (z : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ∫ p, ((smoothCutoff L p.1 : ℝ) : ℂ) *
    (((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (p.2 i * conj (p.2 j))) ∂ξ.measure

/-- The boundary bump `ψ_L = χ_L - χ_{L-2}` (`= χ_L` on `|x| ≥ L - 1`, `0` on `|x| ≤ L - 2`). -/
def cutoffBump (L x : ℝ) : ℝ := smoothCutoff L x - smoothCutoff (L - 2) x

/-- Euclidean squared norm of the mark, `Σ_k |g_k|²`. -/
def euclidMark (g : Fin r → ℂ) : ℝ := ∑ k, ‖g k‖ ^ 2

theorem euclidMark_nonneg (g : Fin r → ℂ) : 0 ≤ euclidMark g :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_euclidMark : Continuous (euclidMark (r := r)) := by
  unfold euclidMark; fun_prop

theorem norm_mul_norm_le_euclidMark (g : Fin r → ℂ) (i j : Fin r) :
    ‖g i‖ * ‖g j‖ ≤ euclidMark g := by
  have hi : ‖g i‖ ^ 2 ≤ euclidMark g :=
    Finset.single_le_sum (f := fun k => ‖g k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hj : ‖g j‖ ^ 2 ≤ euclidMark g :=
    Finset.single_le_sum (f := fun k => ‖g k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖g i‖ - ‖g j‖)]

theorem integrable_euclidMark_sq :
    Integrable (fun g => euclidMark g ^ 2) (circularVectorLaw (Fin r)) := by
  have h4 (k : Fin r) : Integrable (fun g : Fin r → ℂ => ‖g k‖ ^ 4) (circularVectorLaw (Fin r)) :=
    (memLp_circularVectorLaw_apply (p := ((4 : ℕ) : ℝ≥0∞)) (by simp) k).integrable_norm_pow
      (by norm_num)
  have hs : Integrable (fun g : Fin r → ℂ => (Fintype.card (Fin r) : ℝ) *
      ∑ k, ‖g k‖ ^ 4) (circularVectorLaw (Fin r)) :=
    (integrable_finsetSum _ fun k _ => h4 k).const_mul _
  refine hs.mono' ((continuous_euclidMark.pow 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖g k‖ ^ 2)
  simp only [Finset.card_univ] at this
  unfold euclidMark
  convert this using 3
  ring

theorem integral_euclidMark :
    ∫ g, euclidMark g ∂circularVectorLaw (Fin r) = r := by
  classical
  have h2 (k : Fin r) : Integrable (fun g : Fin r → ℂ => ‖g k‖ ^ 2) (circularVectorLaw (Fin r)) :=
    (memLp_circularVectorLaw_apply (p := ((2 : ℕ) : ℝ≥0∞)) (by simp) k).integrable_norm_pow
      (by norm_num)
  have h1 (k : Fin r) : ∫ g, ‖g k‖ ^ 2 ∂circularVectorLaw (Fin r) = 1 := by
    have h := integral_circularVectorLaw_mul_conj (ι := Fin r) k k
    simp only [ite_true] at h
    have : (fun g : Fin r → ℂ => g k * conj (g k)) =
        fun g => ((‖g k‖ ^ 2 : ℝ) : ℂ) := by
      funext g; rw [Complex.mul_conj']; push_cast; rfl
    rw [this, integral_complex_ofReal] at h
    exact_mod_cast h
  unfold euclidMark
  rw [integral_finsetSum _ fun k _ => h2 k]
  simp [h1]

theorem cutoffBump_nonneg (L x : ℝ) : 0 ≤ cutoffBump L x :=
  sub_nonneg.2 (smoothCutoff_mono (by linarith) x)

theorem continuous_cutoffBump (L : ℝ) : Continuous (cutoffBump L) :=
  (continuous_smoothCutoff L).sub (continuous_smoothCutoff _)

theorem hasCompactSupport_cutoffBump (L : ℝ) : HasCompactSupport (cutoffBump L) :=
  (hasCompactSupport_smoothCutoff L).sub (hasCompactSupport_smoothCutoff _)

/-- `|χ_L(x) - 1_{|x| ≤ L}| ≤ ψ_L(x)`, and the left side vanishes for `|x| ≤ L`. -/
theorem abs_smoothCutoff_sub_indicator_le (L x : ℝ) :
    |smoothCutoff L x - (if |x| ≤ L then 1 else 0)| ≤ cutoffBump L x := by
  by_cases hx : |x| ≤ L
  · rw [ite_eq_left hx, smoothCutoff_eq_one hx, sub_self, abs_zero]
    exact cutoffBump_nonneg L x
  · rw [ite_eq_right hx, sub_zero, abs_of_nonneg (smoothCutoff_nonneg L x), cutoffBump,
      smoothCutoff_eq_zero (L := L - 2) (by rw [not_le] at hx; linarith), sub_zero]

/-- `∫ ψ_L ≤ 6` (`0 ≤ ψ_L ≤ 1`, and `ψ_L = 0` off `L - 2 ≤ |x| ≤ L + 1`). -/
theorem integral_cutoffBump_le (L : ℝ) : ∫ x, cutoffBump L x ≤ 6 := by
  set A : Set ℝ := Icc (L - 2) (L + 1) ∪ Icc (-(L + 1)) (-(L - 2)) with hA
  have hAm : MeasurableSet A := measurableSet_Icc.union measurableSet_Icc
  have hAv : volume.real A ≤ 6 := by
    have h1 := measureReal_union_le (μ := volume) (Icc (L - 2) (L + 1))
      (Icc (-(L + 1)) (-(L - 2)))
    rw [Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)] at h1
    linarith
  have hbound (x : ℝ) : cutoffBump L x ≤ A.indicator 1 x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx, Pi.one_apply, cutoffBump]
      linarith [smoothCutoff_le_one L x, smoothCutoff_nonneg (L - 2) x]
    · rw [indicator_of_notMem hx]
      have hx' : |x| < L - 2 ∨ L + 1 < |x| := by
        simp only [hA, mem_union, mem_Icc, not_or, not_and_or, not_le] at hx
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          rcases hx.1 with h | h
          · left; exact h
          · right; exact h
        · rw [abs_of_nonpos h0]
          rcases hx.2 with h | h
          · right; linarith
          · left; linarith
      rcases hx' with h | h
      · rw [cutoffBump, smoothCutoff_eq_one (L := L) (by linarith),
          smoothCutoff_eq_one (L := L - 2) h.le, sub_self]
      · rw [cutoffBump, smoothCutoff_eq_zero h.le, smoothCutoff_eq_zero (L := L - 2)
          (by linarith), sub_self]
  have hi : Integrable (A.indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff hAm).2 (integrableOn_const (by
      exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2
        ⟨measure_Icc_lt_top, measure_Icc_lt_top⟩) |>.ne))
  calc ∫ x, cutoffBump L x ≤ ∫ x, A.indicator 1 x :=
        integral_mono ((continuous_cutoffBump L).integrable_of_hasCompactSupport
          (hasCompactSupport_cutoffBump L)) hi hbound
    _ = volume.real A := integral_indicator_one hAm
    _ ≤ 6 := hAv

/-- **Deterministic smooth/sharp comparison.** For a locally finite point measure `ξ` on
`ℝ × ℂ^r` with `∫ ψ_L(x) Σ_k |g_k|² dξ < ∞`, and `z ∈ ℂ` with `|x - z| ≥ d > 0` whenever
`|x| > L`: `|cauchyTruncation_L(z)_ij - smoothCauchy_L(z)_ij| ≤ (π d)⁻¹ ∫ ψ_L(x) Σ_k |g_k|² dξ`.
(If the sharp integrand is not `ξ`-integrable both sides of the difference are `0`.) -/
theorem norm_cauchyTruncation_sub_smoothCauchy_le (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ)))
    (L : ℝ) (z : ℂ) {d : ℝ} (hd : 0 < d) (hdist : ∀ x : ℝ, L < |x| → d ≤ ‖(x : ℂ) - z‖)
    (hint : Integrable (fun p : ℝ × (Fin r → ℂ) => cutoffBump L p.1 * euclidMark p.2) ξ.measure)
    (i j : Fin r) :
    ‖cauchyTruncation r ξ L z i j - smoothCauchy r ξ L z i j‖ ≤
      (Real.pi * d)⁻¹ * ∫ p, cutoffBump L p.1 * euclidMark p.2 ∂ξ.measure := by
  set F : ℝ × (Fin r → ℂ) → ℂ := fun p =>
    ((Real.pi : ℂ) * ((p.1 : ℂ) - z))⁻¹ * (p.2 i * conj (p.2 j)) with hF
  set e : ℝ → ℝ := fun x => if |x| ≤ L then 1 else 0 with he
  have hFm : Measurable F := by
    simp only [hF]
    fun_prop
  have hT : cauchyTruncation r ξ L z i j = ∫ p, ((e p.1 : ℝ) : ℂ) * F p ∂ξ.measure := by
    unfold cauchyTruncation
    have hms : MeasurableSet {p : ℝ × (Fin r → ℂ) | |p.1| ≤ L} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [← integral_indicator hms]
    congr 1
    funext p
    simp only [indicator, mem_ofPred_eq, he]
    split_ifs <;> simp [hF]
  have hS : smoothCauchy r ξ L z i j = ∫ p, (((e p.1 : ℝ) : ℂ) * F p +
      ((smoothCutoff L p.1 - e p.1 : ℝ) : ℂ) * F p) ∂ξ.measure := by
    unfold smoothCauchy
    congr 1
    funext p
    push_cast
    ring
  have hpi := Real.pi_pos
  have hG (p : ℝ × (Fin r → ℂ)) : ‖((smoothCutoff L p.1 - e p.1 : ℝ) : ℂ) * F p‖ ≤
      (Real.pi * d)⁻¹ * (cutoffBump L p.1 * euclidMark p.2) := by
    by_cases hp : |p.1| ≤ L
    · have : smoothCutoff L p.1 - e p.1 = 0 := by
        simp [he, hp, smoothCutoff_eq_one hp]
      rw [this, Complex.ofReal_zero, zero_mul, norm_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (cutoffBump_nonneg _ _) (euclidMark_nonneg _))
    · have hd' := hdist p.1 (lt_of_not_ge hp)
      have hpos : 0 < ‖(p.1 : ℂ) - z‖ := hd.trans_le hd'
      have h1 : |smoothCutoff L p.1 - e p.1| ≤ cutoffBump L p.1 := by
        have := abs_smoothCutoff_sub_indicator_le L p.1
        simpa [he] using this
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hF, norm_mul, norm_inv, norm_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_conj]
      have h2 : (Real.pi * ‖(p.1 : ℂ) - z‖)⁻¹ ≤ (Real.pi * d)⁻¹ :=
        inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hd' hpi.le)
      have h3 := norm_mul_norm_le_euclidMark p.2 i j
      calc |smoothCutoff L p.1 - e p.1| * ((Real.pi * ‖(p.1 : ℂ) - z‖)⁻¹ *
            (‖p.2 i‖ * ‖p.2 j‖))
          ≤ cutoffBump L p.1 * ((Real.pi * d)⁻¹ * euclidMark p.2) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (by positivity) (by positivity))
              (by positivity) (cutoffBump_nonneg _ _)
        _ = _ := by ring
  have hGi : Integrable (fun p : ℝ × (Fin r → ℂ) =>
      ((smoothCutoff L p.1 - e p.1 : ℝ) : ℂ) * F p) ξ.measure := by
    refine (hint.const_mul (Real.pi * d)⁻¹).mono' ?_ (Filter.Eventually.of_forall hG)
    have hem : Measurable e := by
      simp only [he]
      exact Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
        measurable_const measurable_const
    exact ((Complex.measurable_ofReal.comp (((continuous_smoothCutoff L).measurable.sub hem).comp
      measurable_fst)).mul hFm).aestronglyMeasurable
  have hB0 : 0 ≤ (Real.pi * d)⁻¹ * ∫ p, cutoffBump L p.1 * euclidMark p.2 ∂ξ.measure :=
    mul_nonneg (by positivity) (integral_nonneg fun p =>
      mul_nonneg (cutoffBump_nonneg _ _) (euclidMark_nonneg _))
  by_cases hA : Integrable (fun p : ℝ × (Fin r → ℂ) => ((e p.1 : ℝ) : ℂ) * F p) ξ.measure
  · rw [hT, hS, integral_add hA hGi, sub_add_cancel_left, norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    exact integral_mono hGi.norm (hint.const_mul _) hG
  · have hS0 : ¬ Integrable (fun p : ℝ × (Fin r → ℂ) => ((e p.1 : ℝ) : ℂ) * F p +
        ((smoothCutoff L p.1 - e p.1 : ℝ) : ℂ) * F p) ξ.measure := fun hc =>
      hA (by
        convert hc.sub hGi using 1
        funext p
        simp only [Pi.sub_apply]
        ring)
    rw [hT, hS, integral_undef hA, integral_undef hS0, sub_zero, norm_zero]
    exact hB0

/-- **C3: smooth and sharp cutoffs agree in probability, uniformly on bounded sets.** Law:
`Ξ`
decorated sine on `(Ω, P)` (`IsDecoratedSineProcess`).
For every `K ⊆ ℂ` with
`‖z‖ ≤ R₀` on `K` (no condition on `Im z`; real points allowed) and every `ε > 0`, the outer
probability `P(∃ z ∈ K, ∃ i j, ε ≤ |cauchyTruncation_L(z)_ij - smoothCauchy_L(z)_ij|)` tends to
`0` as `L → ∞`.
Quantitatively it is `≤ 6 r / (ε π (L - R₀))` for `L > R₀`
(Markov, `E ∫ ψ_L Σ_k |g_k|² dΞ = r ∫ ψ_L ≤ 6 r`).
-/
theorem tendsto_measure_smoothSharp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {K : Set ℂ} {R₀ : ℝ} (hK : ∀ z ∈ K, ‖z‖ ≤ R₀) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun L : ℝ => P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖}) atTop (𝓝 0) := by
  have := h.prob
  have hpi := Real.pi_pos
  have hbound : ∀ L : ℝ, R₀ < L → P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖} ≤
      ENNReal.ofReal (6 * r / (ε * Real.pi * (L - R₀))) := by
    intro L hL
    have hd : 0 < L - R₀ := sub_pos.2 hL
    obtain ⟨hae, -, hi, hE, -, -⟩ := productTest_moments h (continuous_cutoffBump L)
      (hasCompactSupport_cutoffBump L) (cutoffBump_nonneg L) continuous_euclidMark
      euclidMark_nonneg integrable_euclidMark_sq
    rw [integral_euclidMark] at hE
    set X := fun ω => ∫ p, cutoffBump L p.1 * euclidMark p.2 ∂(Ξ ω).measure with hX
    set N := {ω | ¬ Integrable (fun p : ℝ × (Fin r → ℂ) => cutoffBump L p.1 * euclidMark p.2)
      (Ξ ω).measure} with hN
    have hN0 : P N = 0 := ae_iff.1 hae
    set c := ε * Real.pi * (L - R₀) with hc
    have hc0 : 0 < c := by positivity
    have hincl : {ω | ∃ z ∈ K, ∃ i j : Fin r,
        ε ≤ ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖} ⊆
        N ∪ {ω | c ≤ X ω} := by
      rintro ω ⟨z, hz, i, j, hij⟩
      by_cases hω : ω ∈ N
      · exact Or.inl hω
      refine Or.inr ?_
      have hint : Integrable (fun p : ℝ × (Fin r → ℂ) => cutoffBump L p.1 * euclidMark p.2)
          (Ξ ω).measure := by
        simpa [hN] using hω
      have hdist (x : ℝ) (hx : L < |x|) : L - R₀ ≤ ‖(x : ℂ) - z‖ := by
        have h1 := norm_sub_norm_le (x : ℂ) z
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        linarith [hK z hz]
      have hle := norm_cauchyTruncation_sub_smoothCauchy_le (Ξ ω) L z hd hdist hint i j
      have h2 := hij.trans hle
      show c ≤ X ω
      rw [hc]
      have hpd : 0 < Real.pi * (L - R₀) := by positivity
      have : ε * (Real.pi * (L - R₀)) ≤ X ω := by
        rw [← le_div_iff₀ hpd, div_eq_inv_mul]
        exact h2
      linarith
    have hX0 : 0 ≤ᵐ[P] X := Filter.Eventually.of_forall fun ω =>
      integral_nonneg fun p => mul_nonneg (cutoffBump_nonneg _ _) (euclidMark_nonneg _)
    have hmk := mul_meas_ge_le_integral_of_nonneg hX0 hi c
    rw [hE] at hmk
    have hψ := integral_cutoffBump_le L
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hreal : P.real {ω | c ≤ X ω} ≤ 6 * r / c := by
      rw [le_div_iff₀' hc0]
      nlinarith
    calc P {ω | ∃ z ∈ K, ∃ i j : Fin r,
          ε ≤ ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖}
        ≤ P N + P {ω | c ≤ X ω} := (measure_mono hincl).trans (measure_union_le _ _)
      _ = ENNReal.ofReal (P.real {ω | c ≤ X ω}) := by
          rw [hN0, zero_add, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (6 * r / (ε * Real.pi * (L - R₀))) := ENNReal.ofReal_le_ofReal hreal
  have hg : Tendsto (fun L : ℝ => ENNReal.ofReal (6 * r / (ε * Real.pi * (L - R₀)))) atTop
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    refine tendsto_const_nhds.div_atTop ?_
    refine Tendsto.const_mul_atTop (by positivity) ?_
    exact tendsto_atTop_add_const_right _ (-R₀) tendsto_id
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Filter.Eventually.of_forall fun _ => bot_le)
    ((eventually_gt_atTop R₀).mono hbound)

/-- **Smooth cutoffs converge to `𝖢_r` locally uniformly in probability** (from
`tendsto_measure_smoothSharp` and the `locallyUniform` field of `IsCanonicalCauchy`). For every
realization `IsCanonicalCauchy r P Ξ C`, compact `K ⊆ {Im z > 0}` and `ε > 0`:
`P(∃ z ∈ K, ∃ i j, ε ≤ |smoothCauchy_L(z)_ij - C(z)_ij|) → 0` as `L → ∞` (outer measure). -/
theorem IsCanonicalCauchy.tendsto_smoothCauchy_locallyUniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    {C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ} (hC : IsCanonicalCauchy r P Ξ C) {K : Set ℂ}
    (hKc : IsCompact K) (hKs : K ⊆ {z : ℂ | 0 < z.im}) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun L : ℝ => P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖smoothCauchy r (Ξ ω) L z i j - C ω z i j‖}) atTop (𝓝 0) := by
  obtain ⟨R₀, hR₀⟩ := hKc.isBounded.exists_norm_le
  have h1 := hC.locallyUniform K hKc hKs (ε / 2) (half_pos hε)
  have h2 := tendsto_measure_smoothSharp hC.decorated hR₀ (half_pos hε)
  have hle (L : ℝ) : P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖smoothCauchy r (Ξ ω) L z i j - C ω z i j‖} ≤
      P {ω | ∃ z ∈ K, ∃ i j : Fin r, ε / 2 ≤ ‖cauchyTruncation r (Ξ ω) L z i j - C ω z i j‖} +
      P {ω | ∃ z ∈ K, ∃ i j : Fin r,
        ε / 2 ≤ ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖} := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    rintro ω ⟨z, hz, i, j, hij⟩
    have htri : ‖smoothCauchy r (Ξ ω) L z i j - C ω z i j‖ ≤
        ‖cauchyTruncation r (Ξ ω) L z i j - C ω z i j‖ +
          ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖ := by
      have := norm_sub_le (cauchyTruncation r (Ξ ω) L z i j - C ω z i j)
        (cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j)
      simpa using this
    by_cases ha : ε / 2 ≤ ‖cauchyTruncation r (Ξ ω) L z i j - C ω z i j‖
    · exact Or.inl ⟨z, hz, i, j, ha⟩
    · exact Or.inr ⟨z, hz, i, j, by linarith⟩
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun _ => bot_le) hle

/-- **Smooth cutoffs converge to `𝖢_r` in probability at real points** (from
`tendsto_measure_smoothSharp` and the `boundary` field of `IsCanonicalCauchy`). For every
realization, real `x` and entry `(i, j)`: `smoothCauchy_L(x)_ij → C(x)_ij` in `P`-probability as `L → ∞`. -/
theorem IsCanonicalCauchy.tendstoInMeasure_smoothCauchy_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    {C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ} (hC : IsCanonicalCauchy r P Ξ C) (x : ℝ)
    (i j : Fin r) :
    TendstoInMeasure P (fun L ω => smoothCauchy r (Ξ ω) L x i j) atTop
      (fun ω => C ω x i j) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have h1 := (tendstoInMeasure_iff_dist.1 (hC.boundary x i j)) (ε / 2) (half_pos hε)
  have hK : ∀ z ∈ ({(x : ℂ)} : Set ℂ), ‖z‖ ≤ |x| := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz, Complex.norm_real, Real.norm_eq_abs]
  have h2 := tendsto_measure_smoothSharp hC.decorated hK (half_pos hε)
  have hle (L : ℝ) : P {ω | ε ≤ dist (smoothCauchy r (Ξ ω) L x i j) (C ω x i j)} ≤
      P {ω | ε / 2 ≤ dist (cauchyTruncation r (Ξ ω) L x i j) (C ω x i j)} +
      P {ω | ∃ z ∈ ({(x : ℂ)} : Set ℂ), ∃ i' j' : Fin r,
        ε / 2 ≤ ‖cauchyTruncation r (Ξ ω) L z i' j' - smoothCauchy r (Ξ ω) L z i' j'‖} := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    simp only [mem_ofPred_eq, dist_eq_norm] at hω ⊢
    have htri : ‖smoothCauchy r (Ξ ω) L x i j - C ω x i j‖ ≤
        ‖cauchyTruncation r (Ξ ω) L x i j - C ω x i j‖ +
          ‖cauchyTruncation r (Ξ ω) L x i j - smoothCauchy r (Ξ ω) L x i j‖ := by
      have := norm_sub_le (cauchyTruncation r (Ξ ω) L x i j - C ω x i j)
        (cauchyTruncation r (Ξ ω) L x i j - smoothCauchy r (Ξ ω) L x i j)
      simpa using this
    by_cases ha : ε / 2 ≤ ‖cauchyTruncation r (Ξ ω) L x i j - C ω x i j‖
    · exact Or.inl ha
    · exact Or.inr ⟨x, rfl, i, j, by linarith⟩
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun _ => bot_le) hle

end BlockBand.Critical.Herglotz
