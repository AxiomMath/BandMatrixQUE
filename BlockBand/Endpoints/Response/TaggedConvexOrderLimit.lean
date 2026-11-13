module

public import BlockBand.Endpoints.Response.TaggedConvexOrderFlat

/-!
# The limiting-law clauses of the tagged convex order

* `tco_moment_tendsto` (generic, measures on `ℝ`): weak convergence `μ_i → ν` (bounded continuous
  tests) and `sup_i E_{μ_i} x^{2m} ≤ C` (eventually) give `x^m ∈ L¹(ν)` and
  `E_{μ_i} x^m → E_ν x^m` (truncation at level `R`, error `≤ C/R` on both sides).
* `tco_limitLaw_of_along`: the limiting-law clauses `TcoLimitLawClauses` along a tagged sequence
  from the prelimit convex comparison.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal BoundedContinuousFunction

/-!
## Moments under weak convergence
-/

/-- The truncation `max(-R, min(R, x^m))`, a bounded continuous function. -/
def tco_trunc (m : ℕ) (R : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max (-R) (min R (x ^ m)), by fun_prop⟩ (2 * |R|) (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : ∀ z : ℝ, |max (-R) (min R z)| ≤ |R| := fun z => by
        rw [abs_le]; constructor
        · exact (neg_le_neg (le_abs_self R)).trans (le_max_left _ _) |>.trans' le_rfl
        · exact max_le (by linarith [neg_abs_le R, le_abs_self R]) ((min_le_left _ _).trans
            (le_abs_self R))
      calc |max (-R) (min R (x ^ m)) - max (-R) (min R (y ^ m))|
          ≤ |max (-R) (min R (x ^ m))| + |max (-R) (min R (y ^ m))| := abs_sub _ _
        _ ≤ 2 * |R| := by linarith [h1 (x ^ m), h1 (y ^ m)])

theorem tco_trunc_apply (m : ℕ) (R x : ℝ) : tco_trunc m R x = max (-R) (min R (x ^ m)) := rfl

theorem tco_abs_sub_trunc_le (m : ℕ) {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x ^ m - tco_trunc m R x| ≤ x ^ (2 * m) / R := by
  rw [tco_trunc_apply]
  have hsq : x ^ (2 * m) = |x ^ m| ^ 2 := by rw [sq_abs, ← pow_mul, mul_comm]
  rw [hsq, le_div_iff₀ hR]
  rcases le_or_gt |x ^ m| R with h | h
  · have h' := abs_le.1 h
    rw [min_eq_right h'.2, max_eq_right h'.1, sub_self, abs_zero, zero_mul]
    positivity
  · rcases le_or_gt 0 (x ^ m) with h0 | h0
    · rw [abs_of_nonneg h0] at h
      rw [min_eq_left h.le, max_eq_right (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg h0]
      nlinarith
    · rw [abs_of_neg h0] at h
      rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith),
        abs_of_neg h0]
      nlinarith

theorem tco_integrable_of_lintegral_pow {μ : Measure ℝ} [IsFiniteMeasure μ] (m : ℕ) {C : ℝ}
    (hC : ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ ≤ ENNReal.ofReal C) :
    Integrable (fun x : ℝ => x ^ (2 * m)) μ ∧ Integrable (fun x : ℝ => x ^ m) μ := by
  have h0 : ∀ x : ℝ, 0 ≤ x ^ (2 * m) := fun x => by rw [pow_mul]; positivity
  have hI : Integrable (fun x : ℝ => x ^ (2 * m)) μ := by
    refine ⟨(continuous_pow _).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_of_nonneg (h0 _)]
    exact hC.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  refine ((hI.add (integrable_const 1))).mono' (continuous_pow _).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  simp only [Pi.add_apply]
  rcases le_or_gt |x| 1 with h | h
  · have : |x| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg x) h
    linarith [h0 x]
  · have : |x| ^ m ≤ |x| ^ (2 * m) := pow_le_pow_right₀ h.le (by omega)
    rw [pow_abs, (even_two_mul m).pow_abs] at this
    rw [pow_abs]; linarith

theorem tco_abs_integral_sub_trunc_le {μ : Measure ℝ} [IsFiniteMeasure μ] (m : ℕ) {C R : ℝ}
    (hR : 0 < R) (hC : ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ ≤ ENNReal.ofReal C) (hC0 : 0 ≤ C) :
    |∫ x, x ^ m ∂μ - ∫ x, tco_trunc m R x ∂μ| ≤ C / R := by
  obtain ⟨h2m, hm⟩ := tco_integrable_of_lintegral_pow m hC
  have h0 : ∀ x : ℝ, 0 ≤ x ^ (2 * m) := fun x => by rw [pow_mul]; positivity
  have hint2 : ∫ x, x ^ (2 * m) ∂μ ≤ C := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0)
      (continuous_pow _).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hC0 hC
  rw [← integral_sub hm ((tco_trunc m R).integrable μ)]
  calc |∫ x, (x ^ m - tco_trunc m R x) ∂μ| ≤ ∫ x, |x ^ m - tco_trunc m R x| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, x ^ (2 * m) / R ∂μ :=
        integral_mono (hm.sub ((tco_trunc m R).integrable μ)).abs (h2m.div_const R)
          (tco_abs_sub_trunc_le m hR)
    _ = (∫ x, x ^ (2 * m) ∂μ) / R := integral_div R _
    _ ≤ C / R := div_le_div_of_nonneg_right hint2 hR.le

/-- Moments under weak convergence with uniform higher moments. -/
theorem tco_moment_tendsto {μ : ℕ → Measure ℝ} {ν : Measure ℝ}
    (hμ : ∀ i, IsProbabilityMeasure (μ i)) [IsProbabilityMeasure ν]
    (hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂μ i) atTop (𝓝 (∫ x, f x ∂ν)))
    (m : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᶠ i in atTop, ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ i ≤ ENNReal.ofReal C) :
    Integrable (fun x : ℝ => x ^ m) ν ∧
      Tendsto (fun i => ∫ x, x ^ m ∂μ i) atTop (𝓝 (∫ x, x ^ m ∂ν)) := by
  have h0 : ∀ x : ℝ, 0 ≤ x ^ (2 * m) := fun x => by rw [pow_mul]; positivity
  -- the bound passes to the limit
  have hν : ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂ν ≤ ENNReal.ofReal C := by
    have hmin : ∀ M : ℕ, ∫⁻ x, ENNReal.ofReal (min (x ^ (2 * m)) M) ∂ν ≤ ENNReal.ofReal C := by
      intro M
      let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
        ⟨fun x => min (x ^ (2 * m)) M, by fun_prop⟩ M (fun x y => by
          simp only [ContinuousMap.coe_mk, Real.dist_eq]
          have hx := min_le_right (x ^ (2 * m)) (M : ℝ)
          have hy := min_le_right (y ^ (2 * m)) (M : ℝ)
          have hx0 : 0 ≤ min (x ^ (2 * m)) (M : ℝ) := le_min (h0 x) (Nat.cast_nonneg M)
          have hy0 : 0 ≤ min (y ^ (2 * m)) (M : ℝ) := le_min (h0 y) (Nat.cast_nonneg M)
          rw [abs_le]; constructor <;> linarith)
      have hf0 : ∀ x, 0 ≤ f x := fun x => le_min (h0 x) (Nat.cast_nonneg M)
      have hlim := hweak f
      have hle : ∀ᶠ i in atTop, ∫ x, f x ∂μ i ≤ C := by
        filter_upwards [hC] with i hi
        have := hμ i
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) f.continuous.aestronglyMeasurable]
        refine ENNReal.toReal_le_of_le_ofReal hC0 ((lintegral_mono fun x => ?_).trans hi)
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
      have hfν : ∫ x, f x ∂ν ≤ C := le_of_tendsto hlim hle
      show ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal C
      rw [← ofReal_integral_eq_lintegral_ofReal (f.integrable ν) (ae_of_all _ hf0)]
      exact ENNReal.ofReal_le_ofReal hfν
    have hsup : ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂ν =
        ⨆ M : ℕ, ∫⁻ x, ENNReal.ofReal (min (x ^ (2 * m)) M) ∂ν := by
      rw [← lintegral_iSup]
      · refine lintegral_congr fun x => ?_
        refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
        obtain ⟨M, hM⟩ := exists_nat_ge (x ^ (2 * m))
        exact le_iSup_of_le M (by rw [min_eq_left hM])
      · intro M; exact ENNReal.measurable_ofReal.comp (by fun_prop)
      · intro M M' hMM' x
        exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hMM'))
    rw [hsup]
    exact iSup_le hmin
  obtain ⟨-, hmν⟩ := tco_integrable_of_lintegral_pow m hν
  refine ⟨hmν, ?_⟩
  rw [Metric.tendsto_atTop]
  intro η hη
  set R : ℝ := 3 * (C + 1) / η
  have hR : 0 < R := by positivity
  have hg := hweak (tco_trunc m R)
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N₁, hN₁⟩ := hg (η / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hC
  refine ⟨max N₁ N₂, fun i hi => ?_⟩
  have := hμ i
  have e1 := tco_abs_integral_sub_trunc_le m hR (hN₂ i (le_of_max_le_right hi)) hC0
  have e2 := tco_abs_integral_sub_trunc_le m hR hν hC0
  have e3 := hN₁ i (le_of_max_le_left hi)
  rw [Real.dist_eq] at e3 ⊢
  have hCR : C / R < η / 3 := by
    rw [div_lt_iff₀ hR]
    simp only [R]
    field_simp
    nlinarith
  calc |∫ x, x ^ m ∂μ i - ∫ x, x ^ m ∂ν|
      ≤ |∫ x, x ^ m ∂μ i - ∫ x, tco_trunc m R x ∂μ i| +
        |∫ x, tco_trunc m R x ∂μ i - ∫ x, tco_trunc m R x ∂ν| +
        |∫ x, x ^ m ∂ν - ∫ x, tco_trunc m R x ∂ν| := by
          have := abs_sub_le (∫ x, x ^ m ∂μ i) (∫ x, tco_trunc m R x ∂μ i) (∫ x, x ^ m ∂ν)
          have := abs_sub_le (∫ x, tco_trunc m R x ∂μ i) (∫ x, tco_trunc m R x ∂ν)
            (∫ x, x ^ m ∂ν)
          rw [abs_sub_comm (∫ x, tco_trunc m R x ∂ν)] at this
          linarith
    _ < η := by linarith

/-!
## The limiting-law clauses along a tagged sequence
-/

theorem tco_gbmExpect_neg (D0 d t : ℝ) (φ : ℝ[X]) :
    tco_gbmExpect D0 d t (-φ) = -tco_gbmExpect D0 d t φ := by
  unfold tco_gbmExpect
  simp only [eval_neg]
  exact integral_neg _

theorem tco_tagSequence_s_le {s τ E : ℝ} (σ : TcoTagSequence s τ E) : s ≤ τ :=
  le_of_tendsto_of_tendsto σ.tag_tendsto σ.ratio_tendsto (Eventually.of_forall fun j =>
    div_le_div_of_nonneg_right (by exact_mod_cast (σ.tag_lt j).le) (Nat.cast_nonneg _))

/-- The limiting-law clauses of the tagged convex order theorem from the prelimit comparison (the
backward comparison and the initial value). -/
theorem tco_limitLaw_of_along (hMom : FullSourceMomentsEnergyUniformContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {s τ : ℝ}
    (σ : TcoTagSequence s τ E) (hcomp : TcoConvexComparisonAlong b σ) :
    TcoLimitLawClauses b σ := by
  intro ψ ν hψ hν hweak
  set μ : ℕ → Measure ℝ := fun i => (probedClockLaw (σ.W (ψ i)) b).map (tco_tagZ b σ (ψ i))
  have hZm : ∀ i, Measurable (tco_tagZ b σ (ψ i)) := fun i => tco_measurable_tagClock _ _ _ _ _
  have hμ : ∀ i, IsProbabilityMeasure (μ i) := fun i => by
    have := tco_isProbabilityMeasure_probedClockLaw (σ.W (ψ i)) b
    exact (Measure.isProbabilityMeasure_map_iff (hZm i).aemeasurable).2 this
  have hint_map : ∀ i (g : ℝ → ℝ), Continuous g →
      ∫ x, g x ∂μ i = ∫ x, g (tco_tagZ b σ (ψ i) x) ∂probedClockLaw (σ.W (ψ i)) b :=
    fun i g hg => integral_map (hZm i).aemeasurable hg.aestronglyMeasurable
  have hweak' : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂μ i) atTop (𝓝 (∫ x, f x ∂ν)) := by
    intro f
    simp_rw [hint_map _ f f.continuous]
    exact hweak f
  obtain ⟨κ, hκ, hκE⟩ := tco_bulk_margin hE1 hE2
  have hψt := hψ.tendsto_atTop
  have hmom : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in atTop, ∫⁻ x, ENNReal.ofReal (x ^ (2 * m)) ∂μ i ≤ ENNReal.ofReal C := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨1, zero_le_one, Eventually.of_forall fun i => ?_⟩
      have := hμ i
      simp
    obtain ⟨C, W₀, hC0, hC⟩ := tco_tag_pow_bound hMom hb hb' hκ (τ + 1) (m := 2 * m) (by omega)
    refine ⟨C, hC0, ?_⟩
    have e1 := (σ.width_tendsto.comp hψt).eventually_ge_atTop W₀
    have e2 := (σ.energy_tendsto.comp hψt) hκE
    have e3 := (σ.ratio_tendsto.comp hψt) (Iio_mem_nhds (show τ < τ + 1 by linarith))
    filter_upwards [e1, e2, e3] with i h1 h2 h3
    simp only [μ]
    rw [lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * m)))
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)) (hZm i)]
    have hW : (0 : ℝ) < σ.W (ψ i) := by exact_mod_cast σ.W_pos _
    have h3' : (σ.n (ψ i) : ℝ) ≤ (τ + 1) * σ.W (ψ i) := by
      have : (σ.n (ψ i) : ℝ) / σ.W (ψ i) < τ + 1 := h3
      rw [div_lt_iff₀ hW] at this; exact this.le
    exact hC _ h1 _ h2 _ h3' _ (σ.tag_lt _)
  have hmc : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) ν ∧
      Tendsto (fun i => ∫ x, x ^ m ∂μ i) atTop (𝓝 (∫ x, x ^ m ∂ν)) := fun m => by
    obtain ⟨C, hC0, hC⟩ := hmom m
    exact tco_moment_tendsto hμ hweak' m hC0 hC
  have hpoly : ∀ φ : ℝ[X], Integrable (fun x => φ.eval x) ν ∧
      Tendsto (fun i => ∫ x, φ.eval (tco_tagZ b σ (ψ i) x) ∂probedClockLaw (σ.W (ψ i)) b)
        atTop (𝓝 (∫ x, φ.eval x ∂ν)) := by
    intro φ
    set S := Finset.range (φ.natDegree + 1)
    have heval : (fun x => φ.eval x) = fun x => ∑ m ∈ S, φ.coeff m * x ^ m := by
      funext x; exact eval_eq_sum_range x
    have hintν : Integrable (fun x => φ.eval x) ν := by
      rw [heval]
      exact integrable_finsetSum _ fun m _ => (hmc m).1.const_mul _
    refine ⟨hintν, ?_⟩
    have hev : ∀ᶠ i in atTop, ∀ m ∈ S, Integrable (fun x : ℝ => x ^ m) (μ i) := by
      rw [eventually_all_finset]
      intro m _
      obtain ⟨C, -, hC⟩ := hmom m
      filter_upwards [hC] with i hi
      have := hμ i
      exact (tco_integrable_of_lintegral_pow m hi).2
    have hlim : Tendsto (fun i => ∑ m ∈ S, φ.coeff m * ∫ x, x ^ m ∂μ i) atTop
        (𝓝 (∑ m ∈ S, φ.coeff m * ∫ x, x ^ m ∂ν)) :=
      tendsto_finsetSum _ fun m _ => (hmc m).2.const_mul _
    have hν_eq : ∫ x, φ.eval x ∂ν = ∑ m ∈ S, φ.coeff m * ∫ x, x ^ m ∂ν := by
      rw [heval, integral_finsetSum _ fun m _ => (hmc m).1.const_mul _]
      simp_rw [integral_const_mul]
    rw [hν_eq]
    refine hlim.congr' ?_
    filter_upwards [hev] with i hi
    rw [← hint_map i _ (Polynomial.continuous φ), heval,
      integral_finsetSum _ fun m hm => (hi m hm).const_mul _]
    simp_rw [integral_const_mul]
  have hsτ : 0 ≤ τ - s := by linarith [tco_tagSequence_s_le σ]
  have hD0 := tco_transportD0_nonneg hb hE1 hE2
  have hconv : ∀ φ : ℝ[X], ConvexOn ℝ (Set.Ici 0) (fun x => φ.eval x) →
      ∫ x, φ.eval x ∂ν ≤ tco_gbmExpect (transportD0 b E) (dStar b) (τ - s) φ := by
    intro φ hφ
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hc := hψt.eventually (hcomp φ hφ δ hδ)
    exact le_of_tendsto (hpoly φ).2 hc
  refine ⟨fun φ hφ => ⟨(hpoly φ).1, hconv φ hφ⟩, ?_, fun m => ⟨(hmc m).1, ?_⟩⟩
  · have hX : ConvexOn ℝ (Set.Ici 0) (fun x => (X : ℝ[X]).eval x) := by
      convert convexOn_id (convex_Ici (0 : ℝ)) using 1
      all_goals first | infer_instance | (funext x; simp)
    have hnX : ConvexOn ℝ (Set.Ici 0) (fun x => (-X : ℝ[X]).eval x) := by
      convert (concaveOn_id (convex_Ici (0 : ℝ))).neg using 1
      all_goals first | infer_instance | (funext x; simp)
    have h1 := hconv X hX
    have h2 := hconv (-X) hnX
    rw [tco_gbmExpect_neg, tco_gbmExpect_X _ _ _ hD0 hsτ] at h2
    rw [tco_gbmExpect_X _ _ _ hD0 hsτ] at h1
    simp only [eval_X, eval_neg] at h1 h2
    rw [integral_neg] at h2
    linarith
  · have h := (hmc m).2
    simp_rw [hint_map _ (fun x : ℝ => x ^ m) (continuous_pow m)] at h
    exact h

end BlockBand.Endpoints
