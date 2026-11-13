module

public import BlockBand.Critical.Herglotz.ExistenceOdd

/-!
# Existence of `𝖢_r`: every decorated sine process carries a canonical Cauchy series

The canonical Cauchy series of a decorated sine process exists locally uniformly in
probability; its boundary values are obtained by first isolating a finite pole interval and then
taking the same tail limit. At `z = 0` no pole occurs almost surely.

**Main result.** `exists_isCanonicalCauchy : IsDecoratedSineProcess r P Ξ → ∃ C,
IsCanonicalCauchy r P Ξ C`, on the same probability space and for the same `Ξ`.

Construction. Let `G = {ω | IsTailFinite (Ξ ω)}` (full measure, `ae_isTailFinite`) and let `A`
be the limit in probability of the odd sums (`exists_tendstoInMeasure_oddSum`). Then
`C ω z = 1_G(ω) (π⁻¹ ∫ kern(x, z) g g^* dΞ(ω) + A(ω))` (`canonCauchy`). For `ω ∈ G`, the
`kern`-integral converges absolutely for every `z ∈ ℂ` (real `z` included, Lean's `0⁻¹ = 0` at a
pole) and is continuous on `{Im z > 0}` (dominated convergence). For `|z| ≤ R` and `L ≥ 2R + 2`,
`|smoothCauchy_L(z) - C(z)| ≤ 4 R π⁻¹ T_L + |A_L - A|` (`ofReal_norm_smoothCauchy_sub_le`), with
the escaped tail `T_L → 0` in probability (`tendsto_measure_tailSum`); the sharp cutoffs follow
from the smooth-to-sharp comparison `tendsto_measure_smoothSharp`. The same bound gives both
`locallyUniform` and `boundary`.

Law: `Ξ` decorated sine (`IsDecoratedSineProcess`), marks `γ = circularVectorLaw (Fin r)`.
No hypothesis beyond the definition is used. The existence of a decorated sine process itself
is proved separately, as `DecoratedSine.exists_isDecoratedSineProcess`.
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

/-- The absolutely convergent part `π⁻¹ Σ_j kern(x_j, z) (g_j)_i conj((g_j)_j)`. -/
def kernSum (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (z : ℂ) (i j : Fin r) : ℂ :=
  ∫ p, (Real.pi : ℂ)⁻¹ * kern p.1 z * entryMark i j p.2 ∂ξ.measure

/-- The canonical Cauchy series built from `Ξ` and a choice `A` of the odd-sum limits:
`C ω z i j = 1_G(ω) (kernSum (Ξ ω) z i j + A i j ω)`, `G` the tail-finite event. -/
def canonCauchy {Ω : Type*} (Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ)))
    (A : Fin r → Fin r → Ω → ℂ) (ω : Ω) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => {ω | IsTailFinite (Ξ ω)}.indicator (fun ω => kernSum (Ξ ω) z i j + A i j ω) ω

theorem measurable_kern (z : ℂ) : Measurable fun x : ℝ => kern x z :=
  ((Complex.measurable_ofReal.sub measurable_const).inv).sub
    (Complex.measurable_ofReal.comp continuous_oddTail.measurable)

theorem measurable_kernIntegrand (z : ℂ) (i j : Fin r) :
    Measurable fun p : ℝ × (Fin r → ℂ) => (Real.pi : ℂ)⁻¹ * kern p.1 z * entryMark i j p.2 :=
  (measurable_const.mul ((measurable_kern z).comp measurable_fst)).mul
    ((continuous_entryMark i j).measurable.comp measurable_snd)

/-- The bound `|π⁻¹ k q| ≤ π⁻¹ B w₀ (1 + Σ|g_k|²)` from `|k| ≤ B w₀` and `|q| ≤ Σ|g_k|²`. -/
theorem norm_kernIntegrand_le {k : ℂ} {B w e : ℝ} (hk : ‖k‖ ≤ B * w) {q : ℂ} (hq : ‖q‖ ≤ e) :
    ‖(Real.pi : ℂ)⁻¹ * k * q‖ ≤ Real.pi⁻¹ * B * (w * (1 + e)) := by
  have hpi : ‖(Real.pi : ℂ)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_mul, norm_mul, hpi]
  have hB : 0 ≤ B * w := (norm_nonneg k).trans hk
  have h1 : ‖k‖ * ‖q‖ ≤ B * w * (1 + e) := by
    calc ‖k‖ * ‖q‖ ≤ B * w * e := mul_le_mul hk hq (norm_nonneg _) hB
      _ ≤ B * w * (1 + e) := by nlinarith
  have hpi0 : 0 ≤ Real.pi⁻¹ := (inv_pos.2 Real.pi_pos).le
  calc Real.pi⁻¹ * ‖k‖ * ‖q‖ = Real.pi⁻¹ * (‖k‖ * ‖q‖) := by ring
    _ ≤ Real.pi⁻¹ * (B * w * (1 + e)) := by gcongr
    _ = _ := by ring

/-- On a tail-finite configuration the `kern`-integrand is integrable for every `z ∈ ℂ`. -/
theorem integrable_kernIntegrand {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))} (hξ : IsTailFinite ξ)
    (z : ℂ) (i j : Fin r) :
    Integrable (fun p : ℝ × (Fin r → ℂ) => (Real.pi : ℂ)⁻¹ * kern p.1 z * entryMark i j p.2)
      ξ.measure := by
  obtain ⟨δ, hδ, hb⟩ := ae_norm_kernReg_le hξ z
  refine integrable_of_le_tailWeight hξ (measurable_kernIntegrand z i j).aestronglyMeasurable
    (c := Real.pi⁻¹ * kernBound ‖z‖ δ) ?_
  filter_upwards [hb 0 le_rfl zero_le_one] with p hp
  rw [kernReg_zero] at hp
  have := norm_kernIntegrand_le hp (norm_entryMark_le i j p.2)
  linarith

/-- **Measurability** of `ω ↦ 1_G(ω) kernSum (Ξ ω) z i j` for every `z ∈ ℂ` (real `z` included):
pointwise limit of the continuous regularized integrands `kernReg (1/(n+1))`. -/
theorem measurable_indicator_kernSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) (z : ℂ)
    (i j : Fin r) :
    Measurable ({ω | IsTailFinite (Ξ ω)}.indicator fun ω => kernSum (Ξ ω) z i j) := by
  refine measurable_indicator_integral h.measurable (measurableSet_isTailFinite h)
    (F := fun n p => (Real.pi : ℂ)⁻¹ * kernReg (1 / ((n : ℝ) + 1)) p.1 z * entryMark i j p.2)
    (fun n => (continuous_const.mul ((continuous_kernReg (by positivity) z).comp
      continuous_fst)).mul ((continuous_entryMark i j).comp continuous_snd))
    (fun p => ((tendsto_const_nhds.mul (tendsto_kernReg p.1 z)).mul tendsto_const_nhds))
    fun ω hω => ?_
  obtain ⟨δ, hδ, hb⟩ := ae_norm_kernReg_le (show IsTailFinite (Ξ ω) from hω) z
  refine ⟨fun p => Real.pi⁻¹ * kernBound ‖z‖ δ * (tailWeight p.1 * (1 + euclidMark p.2)),
    (IsTailFinite.integrable hω).const_mul _, fun n => ?_⟩
  have hε0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hε1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  filter_upwards [hb _ hε0 hε1] with p hp
  exact norm_kernIntegrand_le hp (norm_entryMark_le i j p.2)

/-- **Continuity on the open upper half-plane** of `z ↦ kernSum ξ z i j`, for every tail-finite
`ξ` (dominated convergence; `|x - z| ≥ Im z` for real `x`). -/
theorem continuousOn_kernSum {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))} (hξ : IsTailFinite ξ)
    (i j : Fin r) : ContinuousOn (fun z => kernSum ξ z i j) {z : ℂ | 0 < z.im} := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  set ρ : ℝ := min 1 (z₀.im / 2) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (half_pos hz₀')
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_of_dominated (bound := fun p => Real.pi⁻¹ * kernBound (‖z₀‖ + 1) ρ *
      (tailWeight p.1 * (1 + euclidMark p.2)))
    (Eventually.of_forall fun z => (measurable_kernIntegrand z i j).aestronglyMeasurable) ?_
    (hξ.integrable.const_mul _) (Eventually.of_forall fun p => ?_)
  · filter_upwards [Metric.ball_mem_nhds z₀ hρ0] with z hz
    refine Eventually.of_forall fun p => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hzR : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_insert' z z₀
      linarith [min_le_left 1 (z₀.im / 2)]
    have him : ρ ≤ z.im := by
      have h1 := Complex.abs_im_le_norm (z - z₀)
      rw [Complex.sub_im] at h1
      have h2 := min_le_right 1 (z₀.im / 2)
      have h3 : |z.im - z₀.im| < ρ := lt_of_le_of_lt h1 hz
      rw [abs_lt] at h3
      linarith
    have hdist : ρ ≤ ‖(p.1 : ℂ) - z‖ := by
      have h1 := Complex.abs_im_le_norm ((p.1 : ℂ) - z)
      rw [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg, abs_of_pos (hρ0.trans_le him)]
        at h1
      linarith
    have hk := norm_kernReg_le le_rfl zero_le_one hzR hρ0 (x := p.1) (Or.inr hdist)
    rw [kernReg_zero] at hk
    exact norm_kernIntegrand_le hk (norm_entryMark_le i j p.2)
  · have hne : (p.1 : ℂ) - z₀ ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      rw [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
      linarith
    have hc : ContinuousAt (fun z : ℂ => kern p.1 z) z₀ :=
      ((continuousAt_const.sub continuousAt_id).inv₀ hne).sub continuousAt_const
    exact (continuousAt_const.mul hc).mul continuousAt_const

/-- **Deterministic comparison of the smooth cutoff with `kernSum + a`.** For tail-finite `ξ`,
`|z| ≤ R`, `L ≥ 2R + 2` and any `a ∈ ℂ`:
`|smoothCauchy_L(z)_ij - (kernSum(z)_ij + a)| ≤ 4 R π⁻¹ T_L(ξ) + |oddSum_L ij - a|` (in `ℝ≥0∞`). -/
theorem ofReal_norm_smoothCauchy_sub_le {ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (hξ : IsTailFinite ξ) {z : ℂ} {R L : ℝ} (hR : ‖z‖ ≤ R) (hL : 2 * R + 2 ≤ L) (i j : Fin r)
    (a : ℂ) :
    ENNReal.ofReal ‖smoothCauchy r ξ L z i j - (kernSum ξ z i j + a)‖ ≤
      ENNReal.ofReal (Real.pi⁻¹ * (4 * R)) * tailSum ξ L + ENNReal.ofReal ‖oddSum ξ L i j - a‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hR
  have hpi0 : 0 ≤ Real.pi⁻¹ := (inv_pos.2 Real.pi_pos).le
  set f : ℝ × (Fin r → ℂ) → ℂ := fun p => (Real.pi : ℂ)⁻¹ * kern p.1 z * entryMark i j p.2
    with hf
  have hfi : Integrable f ξ.measure := integrable_kernIntegrand hξ z i j
  set g1 : ℝ × (Fin r → ℂ) → ℂ := fun p => ((smoothCutoff L p.1 : ℝ) : ℂ) * f p with hg1
  have hg1m : AEStronglyMeasurable g1 ξ.measure :=
    ((Complex.measurable_ofReal.comp ((continuous_smoothCutoff L).measurable.comp
      measurable_fst)).mul (measurable_kernIntegrand z i j)).aestronglyMeasurable
  have hg1i : Integrable g1 ξ.measure := hfi.mono hg1m (Eventually.of_forall fun p => by
    rw [hg1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothCutoff_nonneg L p.1)]
    exact mul_le_of_le_one_left (norm_nonneg _) (smoothCutoff_le_one L p.1))
  set g2 : ℝ × (Fin r → ℂ) → ℂ := fun p => ((oddWeight L p.1 : ℝ) : ℂ) * entryMark i j p.2
    with hg2
  have hg2i : Integrable g2 ξ.measure := by
    refine integrable_of_le_tailWeight hξ (((Complex.measurable_ofReal.comp
      ((continuous_oddWeight L).measurable.comp measurable_fst)).mul
      ((continuous_entryMark i j).measurable.comp measurable_snd)).aestronglyMeasurable)
      (c := Real.pi⁻¹ * (1 + (L + 1) ^ 2)) (Eventually.of_forall fun p => ?_)
    have hχ : smoothCutoff L p.1 ≤ (1 + (L + 1) ^ 2) * tailWeight p.1 := by
      by_cases hx : |p.1| ≤ L + 1
      · exact (smoothCutoff_le_one L p.1).trans (one_le_mul_tailWeight hx)
      · rw [smoothCutoff_eq_zero (not_le.1 hx).le]
        exact mul_nonneg (by positivity) (tailWeight_pos _).le
    have hw : |oddWeight L p.1| ≤ Real.pi⁻¹ * smoothCutoff L p.1 := by
      unfold oddWeight
      rw [abs_mul, abs_mul, abs_of_nonneg hpi0, abs_of_nonneg (smoothCutoff_nonneg L p.1)]
      exact mul_le_of_le_one_right (mul_nonneg hpi0 (smoothCutoff_nonneg L p.1))
        (abs_oddTail_le_one p.1)
    rw [hg2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he := norm_entryMark_le i j p.2
    have he0 := euclidMark_nonneg p.2
    have hw0 := (tailWeight_pos p.1).le
    calc |oddWeight L p.1| * ‖entryMark i j p.2‖ ≤
          (Real.pi⁻¹ * ((1 + (L + 1) ^ 2) * tailWeight p.1)) * euclidMark p.2 := by
          refine mul_le_mul (hw.trans (by gcongr)) he (norm_nonneg _)
            (mul_nonneg hpi0 (mul_nonneg (by positivity) hw0))
      _ ≤ Real.pi⁻¹ * (1 + (L + 1) ^ 2) * (tailWeight p.1 * (1 + euclidMark p.2)) := by
          have : 0 ≤ Real.pi⁻¹ * (1 + (L + 1) ^ 2) * tailWeight p.1 := by positivity
          nlinarith
  have hS : smoothCauchy r ξ L z i j = ∫ p, g1 p ∂ξ.measure + oddSum ξ L i j := by
    rw [oddSum, ← integral_add hg1i hg2i]
    unfold smoothCauchy
    congr 1
    funext p
    simp only [hg1, hg2, hf, oddWeight, inv_pi_mul_sub_eq, entryMark]
    push_cast
    ring
  have hdiff : smoothCauchy r ξ L z i j - (kernSum ξ z i j + a) =
      ∫ p, (g1 p - f p) ∂ξ.measure + (oddSum ξ L i j - a) := by
    rw [hS, integral_sub hg1i hfi, kernSum]
    ring
  have hpt (p : ℝ × (Fin r → ℂ)) : ‖g1 p - f p‖ ≤ Real.pi⁻¹ * (4 * R) *
      ((1 - smoothCutoff L p.1) * tailWeight p.1 * euclidMark p.2) := by
    have heq : g1 p - f p = (((smoothCutoff L p.1 - 1 : ℝ) : ℂ)) * f p := by
      simp only [hg1]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (one_sub_smoothCutoff_nonneg L p.1)]
    by_cases hx : |p.1| ≤ L
    · rw [smoothCutoff_eq_one hx, sub_self, zero_mul]
      have := euclidMark_nonneg p.2
      have := (tailWeight_pos p.1).le
      simp
    · have hk := norm_kern_le_of_far hR (x := p.1) (by linarith [not_le.1 hx])
      have hfp : ‖f p‖ ≤ Real.pi⁻¹ * (4 * R) * (tailWeight p.1 * euclidMark p.2) := by
        have hpi : ‖(Real.pi : ℂ)⁻¹‖ = Real.pi⁻¹ := by
          rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        simp only [hf]
        rw [norm_mul, norm_mul, hpi]
        have he := norm_entryMark_le i j p.2
        have hw0 := (tailWeight_pos p.1).le
        have h0 : 0 ≤ Real.pi⁻¹ * (4 * R * tailWeight p.1) := by positivity
        calc Real.pi⁻¹ * ‖kern p.1 z‖ * ‖entryMark i j p.2‖ ≤
            Real.pi⁻¹ * (4 * R * tailWeight p.1) * euclidMark p.2 := by gcongr
          _ = _ := by ring
      have h1 := one_sub_smoothCutoff_nonneg L p.1
      calc (1 - smoothCutoff L p.1) * ‖f p‖ ≤
          (1 - smoothCutoff L p.1) * (Real.pi⁻¹ * (4 * R) * (tailWeight p.1 * euclidMark p.2)) :=
            mul_le_mul_of_nonneg_left hfp h1
        _ = _ := by ring
  rw [hdiff]
  refine (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans ?_
  rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine add_le_add ?_ le_rfl
  refine (ENNReal.ofReal_le_ofReal (norm_integral_le_lintegral_norm _)).trans
    (ENNReal.ofReal_toReal_le.trans ?_)
  unfold tailSum
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun p => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hpt p)

/-- **Smooth cutoffs converge to `canonCauchy` in probability, uniformly on bounded sets.** Law:
`Ξ` decorated sine (`IsDecoratedSineProcess`); `A i j` limits in probability of the odd
sums. For `K ⊆ ℂ` with `|z| ≤ R` on `K` (real points allowed) and `ε > 0`:
`P(∃ z ∈ K, ∃ i j, ε ≤ |smoothCauchy_L(z)_ij - C(z)_ij|) → 0` as `L → ∞` (outer measure). -/
theorem tendsto_measure_smoothCauchy_canonCauchy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {A : Fin r → Fin r → Ω → ℂ}
    (hA : ∀ i j, TendstoInMeasure P (fun L ω => oddSum (Ξ ω) L i j) atTop (A i j))
    {K : Set ℂ} {R : ℝ} (hK : ∀ z ∈ K, ‖z‖ ≤ R) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun L : ℝ => P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖}) atTop (𝓝 0) := by
  have := h.prob
  set R' : ℝ := max R 0 + 1 with hR'
  have hR'0 : 0 < R' := by positivity
  have hK' : ∀ z ∈ K, ‖z‖ ≤ R' := fun z hz => (hK z hz).trans (by
    rw [hR']; linarith [le_max_left R 0])
  set c : ℝ := Real.pi⁻¹ * (4 * R') with hc
  have hc0 : 0 < c := by positivity
  set G := {ω | IsTailFinite (Ξ ω)} with hG
  have hGc : P Gᶜ = 0 := by
    have := ae_isTailFinite h
    rwa [ae_iff] at this
  set T : ℝ → Set Ω := fun L => {ω | ENNReal.ofReal (ε / 2 / c) ≤ tailSum (Ξ ω) L} with hT
  set O : ℝ → Fin r × Fin r → Set Ω := fun L ij =>
    {ω | ε / 2 ≤ dist (oddSum (Ξ ω) L ij.1 ij.2) (A ij.1 ij.2 ω)} with hO
  have hincl : ∀ L : ℝ, 2 * R' + 2 ≤ L → {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖} ⊆
      Gᶜ ∪ T L ∪ ⋃ ij, O L ij := by
    intro L hL ω ⟨z, hz, i, j, hij⟩
    by_cases hω : ω ∈ G
    swap
    · exact Or.inl (Or.inl hω)
    have hb := ofReal_norm_smoothCauchy_sub_le (hω : IsTailFinite (Ξ ω)) (hK' z hz) hL i j
      (A i j ω)
    have hCeq : canonCauchy Ξ A ω z i j = kernSum (Ξ ω) z i j + A i j ω := by
      simp only [canonCauchy]
      exact indicator_of_mem (s := {ω | IsTailFinite (Ξ ω)}) hω _
    rw [← hCeq] at hb
    by_cases hO' : ε / 2 ≤ ‖oddSum (Ξ ω) L i j - A i j ω‖
    · refine Or.inr (mem_iUnion.2 ⟨(i, j), ?_⟩)
      simpa [hO, dist_eq_norm] using hO'
    · refine Or.inl (Or.inr ?_)
      have hO'' := le_of_lt (not_le.1 hO')
      have h1 : ENNReal.ofReal ε ≤ ENNReal.ofReal c * tailSum (Ξ ω) L +
          ENNReal.ofReal (ε / 2) := by
        refine (ENNReal.ofReal_le_ofReal hij).trans (hb.trans ?_)
        exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hO'')
      have h2 : ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal c * tailSum (Ξ ω) L := by
        have he : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
        rw [he] at h1
        exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1
      show ENNReal.ofReal (ε / 2 / c) ≤ tailSum (Ξ ω) L
      have h3 : ENNReal.ofReal (ε / 2) = ENNReal.ofReal c * ENNReal.ofReal (ε / 2 / c) := by
        rw [← ENNReal.ofReal_mul hc0.le]; congr 1; field_simp
      rw [h3] at h2
      exact (ENNReal.mul_le_mul_iff_right (by simpa using hc0) ENNReal.ofReal_ne_top).1 h2
  have hbound : ∀ᶠ L : ℝ in atTop, P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖} ≤
      P (T L) + ∑ ij : Fin r × Fin r, P (O L ij) := by
    filter_upwards [eventually_ge_atTop (2 * R' + 2)] with L hL
    refine (measure_mono (hincl L hL)).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine add_le_add ((measure_union_le _ _).trans ?_) (measure_iUnion_fintype_le _ _)
    rw [hGc, zero_add]
  have hTlim : Tendsto (fun L => P (T L)) atTop (𝓝 0) :=
    tendsto_measure_tailSum h (by simpa using div_pos (half_pos hε) hc0) ENNReal.ofReal_ne_top
  have hOlim : Tendsto (fun L => ∑ ij : Fin r × Fin r, P (O L ij)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _ij : Fin r × Fin r, (0 : ℝ≥0∞) by simp]
    exact tendsto_finsetSum _ fun ij _ =>
      (tendstoInMeasure_iff_dist.1 (hA ij.1 ij.2)) (ε / 2) (half_pos hε)
  have hsum := hTlim.add hOlim
  rw [add_zero] at hsum
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) hbound

/-- **Sharp cutoffs converge to `canonCauchy` in probability, uniformly on bounded sets**
(previous theorem with `tendsto_measure_smoothSharp`). Same law and hypotheses. -/
theorem tendsto_measure_cauchyTruncation_canonCauchy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))}
    (h : IsDecoratedSineProcess r P Ξ) {A : Fin r → Fin r → Ω → ℂ}
    (hA : ∀ i j, TendstoInMeasure P (fun L ω => oddSum (Ξ ω) L i j) atTop (A i j))
    {K : Set ℂ} {R : ℝ} (hK : ∀ z ∈ K, ‖z‖ ≤ R) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun L : ℝ => P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖cauchyTruncation r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖}) atTop (𝓝 0) := by
  have h1 := tendsto_measure_smoothCauchy_canonCauchy h hA hK (half_pos hε)
  have h2 := tendsto_measure_smoothSharp h hK (half_pos hε)
  have hle (L : ℝ) : P {ω | ∃ z ∈ K, ∃ i j : Fin r,
      ε ≤ ‖cauchyTruncation r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖} ≤
      P {ω | ∃ z ∈ K, ∃ i j : Fin r,
        ε / 2 ≤ ‖smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖} +
      P {ω | ∃ z ∈ K, ∃ i j : Fin r,
        ε / 2 ≤ ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖} := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    rintro ω ⟨z, hz, i, j, hij⟩
    have htri : ‖cauchyTruncation r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖ ≤
        ‖smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖ +
          ‖cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j‖ := by
      have := norm_add_le (smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j)
        (cauchyTruncation r (Ξ ω) L z i j - smoothCauchy r (Ξ ω) L z i j)
      rwa [add_comm, sub_add_sub_cancel] at this
    by_cases ha : ε / 2 ≤ ‖smoothCauchy r (Ξ ω) L z i j - canonCauchy Ξ A ω z i j‖
    · exact Or.inl ⟨z, hz, i, j, ha⟩
    · exact Or.inr ⟨z, hz, i, j, by linarith⟩
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
    (fun _ => zero_le) hle

/-- **`canonCauchy` is a realization of `𝖢_r`.** Law: `Ξ` decorated sine on `(Ω, P)`
(`IsDecoratedSineProcess`); `A i j` any limits in probability of the odd sums. -/
theorem isCanonicalCauchy_canonCauchy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {A : Fin r → Fin r → Ω → ℂ} (hAm : ∀ i j, Measurable (A i j))
    (hA : ∀ i j, TendstoInMeasure P (fun L ω => oddSum (Ξ ω) L i j) atTop (A i j)) :
    IsCanonicalCauchy r P Ξ (canonCauchy Ξ A) where
  decorated := h
  measurable z i j := by
    have heq : (fun ω => canonCauchy Ξ A ω z i j) =
        fun ω => {ω | IsTailFinite (Ξ ω)}.indicator (fun ω => kernSum (Ξ ω) z i j) ω +
          {ω | IsTailFinite (Ξ ω)}.indicator (A i j) ω := by
      funext ω
      simp only [canonCauchy]
      exact congrFun (indicator_add {ω | IsTailFinite (Ξ ω)} (fun ω => kernSum (Ξ ω) z i j)
        (A i j)) ω
    rw [heq]
    exact (measurable_indicator_kernSum h z i j).add
      ((hAm i j).indicator (measurableSet_isTailFinite h))
  continuousOn ω := by
    by_cases hω : IsTailFinite (Ξ ω)
    · have heq : canonCauchy Ξ A ω = fun z => fun i j => kernSum (Ξ ω) z i j + A i j ω := by
        funext z i j
        simp only [canonCauchy]
        exact indicator_of_mem (s := {ω | IsTailFinite (Ξ ω)}) hω _
      rw [heq]
      exact continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
        (continuousOn_kernSum hω i j).add continuousOn_const
    · have heq : canonCauchy Ξ A ω = fun _ => 0 := by
        funext z i j
        simp only [canonCauchy]
        exact indicator_of_notMem (s := {ω | IsTailFinite (Ξ ω)}) hω _
      rw [heq]
      exact continuousOn_const
  locallyUniform K hKc _ ε hε := by
    obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
    exact tendsto_measure_cauchyTruncation_canonCauchy h hA hR hε
  boundary x i j := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hK : ∀ z ∈ ({(x : ℂ)} : Set ℂ), ‖z‖ ≤ ‖(x : ℂ)‖ := fun z hz => by
      rw [mem_singleton_iff.1 hz]
    have h1 := tendsto_measure_cauchyTruncation_canonCauchy h hA hK hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => zero_le)
      fun L => measure_mono fun ω hω => ⟨x, rfl, i, j, ?_⟩
    simpa [dist_eq_norm] using hω

/-- **Existence of `𝖢_r`.** For every decorated sine process `Ξ` on `(Ω, P)`
(`IsDecoratedSineProcess`: unit-intensity sine process with independent standard
circular Gaussian marks in `ℂ^r`) there is `C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ` on the same
probability space with `IsCanonicalCauchy r P Ξ C`: the limit exists locally uniformly in
probability, with boundary values at real points. No hypothesis beyond the definition. -/
theorem exists_isCanonicalCauchy {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) :
    ∃ C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ, IsCanonicalCauchy r P Ξ C := by
  choose A hAm hA using fun (ij : Fin r × Fin r) => exists_tendstoInMeasure_oddSum h ij.1 ij.2
  exact ⟨canonCauchy Ξ (fun i j => A (i, j)), isCanonicalCauchy_canonCauchy h
    (fun i j => hAm (i, j)) (fun i j => hA (i, j))⟩

end BlockBand.Critical.Herglotz
