module

public import BlockBand.Endpoints.Sine.MicroscopicTagPort
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The interior clock is not small, and the ports carry vanishing mass

Law: the path law `growthPathLaw W b` times an independent `h ~ CN(0, I_{2W})`
(`Clocks.probedClockLaw`), along a critical sequence `n_j/W_j → τ > 0`, path length `r_j = n_j - 3`,
at the microscopic energies `e_j(u) = E + u/(N_jρ(E))`, `|u| ≤ R₀`.

* `portFraction_le_pointwise`, `integral_portFraction_le` (Markov): pointwise
  `a_port ≤ v + 1{h*Y^{int}h/W² ≤ t} + ‖h‖²/(η²W²vt)`, `η = Im z_b(e)`, hence
  `E a_port ≤ v + P(h*Y^{int}h/W² ≤ t) + 2/(η²Wvt)`.
* `portFraction_uniform`: taking the width limit and then `t ↓ 0` gives `E a_port → 0`, uniformly:
  `sup_{|u| ≤ R₀} E a_port(e_j(u)) → 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal BoundedContinuousFunction

/-!
## Generic facts
-/

theorem isProbabilityMeasure_probedClockLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (probedClockLaw W b) := by
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  unfold probedClockLaw; infer_instance

/-- **Prokhorov on `ℝ`**: a tight sequence of probability measures has a subsequential limit
in the sense `IsSubsequentialLimit`.
-/
theorem exists_isSubsequentialLimit_of_tight (ν : ℕ → Measure ℝ)
    (hν : ∀ m, IsProbabilityMeasure (ν m)) (hT : IsTightSeq ν) :
    ∃ μ : Measure ℝ, IsSubsequentialLimit ν μ := by
  let P : ℕ → ProbabilityMeasure ℝ := fun m => ⟨ν m, hν m⟩
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases htop : ε = ⊤
    · refine ⟨∅, isCompact_empty, fun μ _ => ?_⟩
      rw [htop]; exact le_top
    · obtain ⟨R, hR⟩ := hT ε.toReal (ENNReal.toReal_pos hε.ne' htop)
      refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
      rintro μ ⟨_, ⟨m, rfl⟩, rfl⟩
      have hset : (Set.Icc (-R) R)ᶜ = {x : ℝ | R < |x|} := by
        ext x
        simp only [mem_compl_iff, mem_Icc, Set.mem_ofPred_eq]
        constructor
        · intro h; by_contra h'; exact h (abs_le.1 (not_lt.1 h'))
        · rintro h ⟨h1, h2⟩; exact absurd (abs_le.2 ⟨h1, h2⟩) (not_le.2 h)
      change ν m (Set.Icc (-R) R)ᶜ ≤ ε
      rw [hset]
      exact (hR m).trans (le_of_eq (ENNReal.ofReal_toReal htop))
  have hcomp := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨a, -, ψ, hψ, hlim⟩ := hcomp.tendsto_subseq (x := P) fun m => subset_closure ⟨m, rfl⟩
  refine ⟨(a : Measure ℝ), inferInstance, ψ, hψ, fun f => ?_⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim) f

/-- A continuous `[0,1]`-valued test equal to `1` on `(-∞, t]` and `0` on `[2t, ∞)`. -/
def lowerTailTest (t : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => max 0 (min 1 (2 - x / t)), by fun_prop⟩ 1 (by
      intro x y
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]
      constructor <;>
      · have := le_max_left 0 (min 1 (2 - x / t))
        have := le_max_left 0 (min 1 (2 - y / t))
        have : max 0 (min 1 (2 - x / t)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
        have : max 0 (min 1 (2 - y / t)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
        linarith)

theorem lowerTailTest_apply (t x : ℝ) : lowerTailTest t x = max 0 (min 1 (2 - x / t)) := rfl

theorem lowerTailTest_nonneg (t x : ℝ) : 0 ≤ lowerTailTest t x := le_max_left _ _

theorem lowerTailTest_le_one (t x : ℝ) : lowerTailTest t x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem indicator_le_lowerTailTest {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (Set.Iic t).indicator (fun _ => (1 : ℝ)) x ≤ lowerTailTest t x := by
  by_cases hx : x ≤ t
  · rw [Set.indicator_of_mem (Set.mem_Iic.2 hx), lowerTailTest_apply]
    have : x / t ≤ 1 := (div_le_one ht).2 hx
    rw [min_eq_left (by linarith)]; exact le_max_right _ _
  · rw [Set.indicator_of_notMem (by simpa using hx)]; exact lowerTailTest_nonneg _ _

theorem lowerTailTest_le_indicator {t : ℝ} (ht : 0 < t) (x : ℝ) :
    lowerTailTest t x ≤ (Set.Iic (2 * t)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ≤ 2 * t
  · rw [Set.indicator_of_mem (Set.mem_Iic.2 hx)]; exact lowerTailTest_le_one _ _
  · rw [Set.indicator_of_notMem (by simpa using hx), lowerTailTest_apply]
    have : 2 < x / t := (lt_div_iff₀ ht).2 (by linarith)
    rw [max_eq_left]; exact (min_le_right _ _).trans (by linarith)

theorem measureReal_Iic_le_integral_lowerTailTest (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) : (μ (Set.Iic t)).toReal ≤ ∫ x, lowerTailTest t x ∂μ := by
  rw [← measureReal_def, ← integral_indicator_one measurableSet_Iic]
  refine integral_mono ((integrable_const (μ := μ) (1 : ℝ)).indicator measurableSet_Iic)
    ((lowerTailTest t).integrable μ) fun x => ?_
  exact indicator_le_lowerTailTest ht x

theorem integral_lowerTailTest_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {t : ℝ} (ht : 0 < t) :
    ∫ x, lowerTailTest t x ∂μ ≤ (μ (Set.Iic (2 * t))).toReal := by
  rw [← measureReal_def, ← integral_indicator_one measurableSet_Iic]
  refine integral_mono ((lowerTailTest t).integrable μ)
    ((integrable_const (μ := μ) (1 : ℝ)).indicator measurableSet_Iic) fun x => ?_
  exact lowerTailTest_le_indicator ht x

/-!
## Microscopic energies
-/

theorem semicircleDensity_pos {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  have : 0 < 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_pos.2 this
  positivity

theorem abs_microEnergy_sub_le (p : Parameters) {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    {u R₀ : ℝ} (hu : |u| ≤ R₀) :
    |microEnergy p E u - E| ≤ R₀ / (p.W * Parameters.semicircleDensity E) := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast (show 1 ≤ p.n by have := p.n_ge_four; omega)
  have hN : (p.N : ℝ) = p.n * p.W := by simp [Parameters.N]
  have hR : 0 ≤ R₀ := (abs_nonneg u).trans hu
  rw [microEnergy, add_sub_cancel_left, hN, abs_div,
    abs_of_pos (show (0 : ℝ) < p.n * p.W * Parameters.semicircleDensity E by positivity)]
  calc |u| / (p.n * p.W * Parameters.semicircleDensity E)
      ≤ R₀ / (p.n * p.W * Parameters.semicircleDensity E) :=
        div_le_div_of_nonneg_right hu (by positivity)
    _ ≤ R₀ / (p.W * Parameters.semicircleDensity E) := by
        apply div_le_div_of_nonneg_left hR (by positivity)
        have h := mul_le_mul_of_nonneg_right hn (mul_pos hW hρ).le
        linarith [h]

/-!
## The lower tail of the interior clock
-/

theorem measurable_interiorLeadMass (b e : ℝ) (W r : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => interiorLeadMass b e W r x) :=
  Finset.measurable_sum _ fun i _ =>
    measurable_leadPositionMass_of b W r (Sum.inl i) measurable_const measurable_id

theorem measurable_portLeadMass (b e : ℝ) (W r : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => portLeadMass b e W r x) :=
  Finset.measurable_sum _ fun i _ =>
    measurable_leadPositionMass_of b W r (Sum.inr i) measurable_const measurable_id

/-- Uniform lower tail of the interior clock, from `NegativeClockContract`. -/
theorem interiorClock_lowerTail (hNeg : NegativeClockContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {τ : ℝ} (hτ : 0 < τ)
    (s : CriticalSequence τ) (R₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ᶠ j in atTop, ∀ u ∈ Set.Icc (-R₀) R₀,
      probedClockLaw (s.W j) b {x | interiorLeadMass b (microEnergy (s.parameters b hb hb' j) E u)
          (s.W j) (s.n j - 3) x / (s.W j : ℝ) ^ 2 ≤ t} ≤ ENNReal.ofReal ε := by
  have hρ := semicircleDensity_pos hE1 hE2
  by_contra H
  push Not at H
  have H' : ∀ m : ℕ, ∃ᶠ j in atTop, ∃ u ∈ Set.Icc (-R₀) R₀, ENNReal.ofReal ε <
      probedClockLaw (s.W j) b {x | interiorLeadMass b (microEnergy (s.parameters b hb hb' j) E u)
          (s.W j) (s.n j - 3) x / (s.W j : ℝ) ^ 2 ≤ 1 / ((m : ℝ) + 1)} :=
    fun m => H _ (by positivity)
  obtain ⟨φ, hφ, hφP⟩ := extraction_forall_of_frequently H'
  choose u hu hP using hφP
  have hWφ : Tendsto (fun m => ((s.W (φ m) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (s.width_tendsto.comp hφ.tendsto_atTop)
  
  let s' : ClockSequence τ E :=
    { n := fun m => s.n (φ m) - 3
      W := fun m => s.W (φ m)
      energy := fun m => microEnergy (s.parameters b hb hb' (φ m)) E (u m)
      W_pos := fun m => s.W_pos _
      width_tendsto := s.width_tendsto.comp hφ.tendsto_atTop
      ratio_tendsto := by
        have h1 := s.ratio_tendsto.comp hφ.tendsto_atTop
        have h2 : Tendsto (fun m => (3 : ℝ) / (s.W (φ m) : ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop hWφ
        have h3 := h1.sub h2
        rw [sub_zero] at h3
        refine h3.congr fun m => ?_
        have h4 := s.n_ge_four (φ m)
        have hW0 : (s.W (φ m) : ℝ) ≠ 0 := by exact_mod_cast (s.W_pos _).ne'
        simp only [Function.comp_apply]
        rw [Nat.cast_sub (by omega : 3 ≤ s.n (φ m))]
        field_simp
        push_cast; ring
      energy_tendsto := by
        have hb0 : Tendsto (fun m => |R₀| / ((s.W (φ m) : ℝ) * Parameters.semicircleDensity E))
            atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (hWφ.atTop_mul_const hρ)
        have : Tendsto (fun m => microEnergy (s.parameters b hb hb' (φ m)) E (u m) - E)
            atTop (𝓝 0) := by
          refine squeeze_zero_norm (fun m => ?_) hb0
          rw [Real.norm_eq_abs]
          refine abs_microEnergy_sub_le _ hρ ?_
          exact abs_le.2 ⟨by linarith [(hu m).1, le_abs_self R₀], (hu m).2.trans (le_abs_self _)⟩
        simpa using this.add_const E }
  let ν : ℕ → Measure ℝ := fun m => clockLaw (s'.W m) b (scaledClock b s' m)
  have hX : ∀ m, Measurable (scaledClock b s' m) := by
    intro m
    have : scaledClock b s' m = fun x => interiorLeadMass b (s'.energy m) (s'.W m) (s'.n m) x /
        ((s'.W m : ℕ) : ℝ) ^ 2 := by
      funext x; rw [scaledClock, interiorLeadMass_eq_quadForm]
    rw [this]
    exact (measurable_interiorLeadMass _ _ _ _).div_const _
  have hνP : ∀ m, IsProbabilityMeasure (ν m) := by
    intro m
    have := isProbabilityMeasure_probedClockLaw (s'.W m) b
    exact (Measure.isProbabilityMeasure_map_iff (hX m).aemeasurable).2 inferInstance
  have hνIic : ∀ m t, ν m (Set.Iic t) = probedClockLaw (s.W (φ m)) b
      {x | interiorLeadMass b (microEnergy (s.parameters b hb hb' (φ m)) E (u m))
        (s.W (φ m)) (s.n (φ m) - 3) x / (s.W (φ m) : ℝ) ^ 2 ≤ t} := by
    intro m t
    change (probedClockLaw (s'.W m) b).map (scaledClock b s' m) (Set.Iic t) = _
    rw [Measure.map_apply (hX m) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, scaledClock,
      interiorLeadMass_eq_quadForm]
    rfl
  obtain ⟨μ, hμ⟩ := exists_isSubsequentialLimit_of_tight ν hνP
    (hNeg.tight b hb hb' E hE1 hE2 τ hτ s')
  -- the negative clock: the limit has no mass at or below zero
  set β : ℝ := min b (1 / 2 - b) / 2 with hβ
  set κ : ℝ := (2 - |E|) / 2 with hκ
  have hβ0 : 0 < β := by rw [hβ]; have := lt_min hb (by linarith : (0:ℝ) < 1 / 2 - b); linarith
  have hβ1 : β < 1 / 4 := by
    rw [hβ]
    have h1 := min_le_left b (1 / 2 - b); have h2 := min_le_right b (1 / 2 - b)
    linarith
  have hEabs : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  obtain ⟨C, hC⟩ := hNeg.negative β κ τ 1 hβ0 hβ1 hκ0 hτ one_pos
  have hbI : b ∈ Set.Icc β (1 / 2 - β) := by
    rw [hβ]
    have h1 := min_le_left b (1 / 2 - b); have h2 := min_le_right b (1 / 2 - b)
    have h3 := lt_min hb (by linarith : (0:ℝ) < 1 / 2 - b)
    constructor <;> linarith
  have hEI : E ∈ bulkInterval κ := by
    rw [bulkInterval, hκ]
    constructor <;> linarith [le_abs_self E, neg_abs_le E]
  have hev : ∀ᶠ m in atTop, s'.energy m ∈ bulkInterval κ := by
    have hmem : Set.Icc (-2 + κ) (2 - κ) ∈ 𝓝 E := by
      apply Icc_mem_nhds <;> rw [hκ] <;> linarith [le_abs_self E, neg_abs_le E]
    exact s'.energy_tendsto hmem
  have h0 := (hC b hbI E hEI τ hτ le_rfl s' hev μ hμ).1
  -- but every `(-∞, 2t]` carries mass at least `ε`
  obtain ⟨hμP, ψ, hψ, hlim⟩ := hμ
  have hlarge : ∀ t : ℝ, 0 < t → ENNReal.ofReal ε ≤ μ (Set.Iic (2 * t)) := by
    intro t ht
    have hconv := hlim (lowerTailTest t)
    have hlow : ∀ᶠ k in atTop, ε ≤ ∫ x, lowerTailTest t x ∂ν (ψ k) := by
      have hk : ∀ᶠ k in atTop, 1 / ((ψ k : ℝ) + 1) ≤ t := by
        have : Tendsto (fun k => 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 0) := by
          have h1 : Tendsto (fun k => ((ψ k : ℕ) : ℝ) + 1) atTop atTop :=
            tendsto_atTop_add_const_right _ 1
              (tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop)
          have h2 := h1.inv_tendsto_atTop
          exact h2.congr fun k => by simp [one_div]
        exact (this.eventually (gt_mem_nhds ht)).mono fun k hk => hk.le
      filter_upwards [hk] with k hk
      have := hνP (ψ k)
      refine le_trans ?_ (measureReal_Iic_le_integral_lowerTailTest (ν (ψ k)) ht)
      have hP' := hP (ψ k)
      rw [← hνIic] at hP'
      have hmono : ν (ψ k) (Set.Iic (1 / ((ψ k : ℝ) + 1))) ≤ ν (ψ k) (Set.Iic t) :=
        measure_mono (Set.Iic_subset_Iic.2 hk)
      have := hP'.le.trans hmono
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 this
    have hle : ε ≤ ∫ x, lowerTailTest t x ∂μ := ge_of_tendsto hconv hlow
    have := hle.trans (integral_lowerTailTest_le μ ht)
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 this
  have hinter : (⋂ m : ℕ, Set.Iic (2 * (1 / ((m : ℝ) + 1)))) = Set.Iic 0 := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro hx
      by_contra hpos
      push Not at hpos
      obtain ⟨m, hm⟩ := exists_nat_gt (2 / x)
      have := hx m
      have hm' : 2 / x < (m : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hpos] at hm'
      have : 2 * (1 / ((m : ℝ) + 1)) < x := by
        rw [mul_one_div, div_lt_iff₀ (by positivity)]; linarith
      linarith
    · intro hx m; have : 0 ≤ 2 * (1 / ((m : ℝ) + 1)) := by positivity
      linarith
  have htend := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun m : ℕ => Set.Iic (2 * (1 / ((m : ℝ) + 1))))
    (fun m => measurableSet_Iic.nullMeasurableSet)
    (fun m m' hmm' => Set.Iic_subset_Iic.2 (by
      have : (m : ℝ) + 1 ≤ (m' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmm' 1
      have h1 : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) this
      linarith))
    ⟨0, measure_ne_top _ _⟩
  rw [hinter, h0] at htend
  have hge : ENNReal.ofReal ε ≤ 0 :=
    ge_of_tendsto htend (Eventually.of_forall fun m => hlarge _ (by positivity))
  have : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  exact absurd hge (not_le.2 this)

/-!
## The mass of the auxiliary ports
-/

/-- The normalized port mass `a_port = h*Y^{port}h / h*Y^{all}h` (`0` on the null event
`h*Y^{all}h = 0`). -/
def portFraction (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  portLeadMass b e W r x / totalLeadMass b e W r x

theorem portFraction_nonneg (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ portFraction b e W r x :=
  div_nonneg (portLeadMass_nonneg _ _ _) (by
    rw [totalLeadMass_eq]; linarith [portLeadMass_nonneg b e (r := r) x,
      interiorLeadMass_nonneg b e (r := r) x])

theorem portFraction_le_one (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    portFraction b e W r x ≤ 1 := by
  unfold portFraction
  rw [totalLeadMass_eq]
  have h1 := portLeadMass_nonneg b e (r := r) x
  have h2 := interiorLeadMass_nonneg b e (r := r) x
  rcases eq_or_lt_of_le (add_nonneg h2 h1) with h | h
  · rw [← h, div_zero]; exact zero_le_one
  · rw [div_le_one h]; linarith

theorem measurable_portFraction (b e : ℝ) (W r : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => portFraction b e W r x) := by
  unfold portFraction
  have : (fun x => totalLeadMass b e W r x) =
      fun x => interiorLeadMass b e W r x + portLeadMass b e W r x := by
    funext x; exact totalLeadMass_eq b e x
  simp_rw [this]
  exact (measurable_portLeadMass b e W r).div
    ((measurable_interiorLeadMass b e W r).add (measurable_portLeadMass b e W r))

/-- Markov bound for the port fraction, pointwise: if `a_port > v` while the interior clock
exceeds `t`, then the port clock exceeds `vt`. -/
theorem portFraction_le_pointwise {b e : ℝ} {W r : ℕ} (hW : 0 < W)
    (hη : 0 < (boundaryZ b e).im) {v t : ℝ} (hv : 0 < v) (ht : 0 < t)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) (h : Fin 2 × Fin W → ℂ) :
    portFraction b e W r (ω, h) ≤ v +
      {x : GrowthPath W × (Fin 2 × Fin W → ℂ) |
        interiorLeadMass b e W r x / (W : ℝ) ^ 2 ≤ t}.indicator
        (fun _ => (1 : ℝ)) (ω, h) +
      vecNormSq h / ((boundaryZ b e).im ^ 2 * (W : ℝ) ^ 2 * v * t) := by
  set η := (boundaryZ b e).im
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hq : 0 ≤ vecNormSq h / (η ^ 2 * (W : ℝ) ^ 2 * v * t) :=
    div_nonneg (vecNormSq_nonneg h) (by positivity)
  have hind0 : 0 ≤ {x : GrowthPath W × (Fin 2 × Fin W → ℂ) |
      interiorLeadMass b e W r x / (W : ℝ) ^ 2 ≤ t}.indicator (fun _ => (1 : ℝ)) (ω, h) :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have ha1 := portFraction_le_one b e W r (ω, h)
  by_cases hav : portFraction b e W r (ω, h) ≤ v
  · linarith
  by_cases hI : interiorLeadMass b e W r (ω, h) / (W : ℝ) ^ 2 ≤ t
  · rw [Set.indicator_of_mem (show (ω, h) ∈ {x : GrowthPath W × (Fin 2 × Fin W → ℂ) |
      interiorLeadMass b e W r x / (W : ℝ) ^ 2 ≤ t} from hI)]
    linarith
  push Not at hav hI
  set P := portLeadMass b e W r (ω, h)
  set I := interiorLeadMass b e W r (ω, h)
  have hP0 : 0 ≤ P := portLeadMass_nonneg _ _ _
  have hI0 : 0 ≤ I := interiorLeadMass_nonneg _ _ _
  have hT : 0 < I + P := by
    rcases eq_or_lt_of_le (add_nonneg hI0 hP0) with h0 | h0
    · exfalso
      have : portFraction b e W r (ω, h) = 0 := by
        unfold portFraction; rw [totalLeadMass_eq, ← h0, div_zero]
      linarith
    · exact h0
  have hfrac : portFraction b e W r (ω, h) = P / (I + P) := by
    unfold portFraction; rw [totalLeadMass_eq]
  rw [hfrac] at hav ha1
  have hPv : v * (I + P) < P := (lt_div_iff₀ hT).1 hav
  have hIt : t * (W : ℝ) ^ 2 < I := (lt_div_iff₀ (by positivity)).1 hI
  have hPbig : v * t * (W : ℝ) ^ 2 < P := by nlinarith
  have hPle := portLeadMass_le (r := r) hη hH h
  have hqbig : 1 < vecNormSq h / (η ^ 2 * (W : ℝ) ^ 2 * v * t) := by
    rw [lt_div_iff₀ (by positivity)]
    have : P * η ^ 2 ≤ vecNormSq h := by
      have := (le_div_iff₀ (by positivity)).1 hPle
      linarith
    nlinarith [sq_nonneg η, sq_pos_of_pos hη]
  rw [hfrac]
  linarith

/-- Markov bound for the port fraction, integrated:
`E a_port ≤ v + P(h*Y^{int}h/W² ≤ t) + 2/(η²Wvt)`. -/
theorem integral_portFraction_le {b e : ℝ} {W r : ℕ} (hW : 0 < W)
    (hη : 0 < (boundaryZ b e).im) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) :
    ∫ x, portFraction b e W r x ∂probedClockLaw W b ≤ v +
      (probedClockLaw W b {x | interiorLeadMass b e W r x / (W : ℝ) ^ 2 ≤ t}).toReal +
      2 / ((boundaryZ b e).im ^ 2 * W * v * t) := by
  have hP := isProbabilityMeasure_probedClockLaw W b
  have hG := passDeriv_isProbabilityMeasure_growthPathLaw W b
  set η := (boundaryZ b e).im
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set S := {x : GrowthPath W × (Fin 2 × Fin W → ℂ) | interiorLeadMass b e W r x / (W : ℝ) ^ 2 ≤ t}
  have hS : MeasurableSet S :=
    measurableSet_le ((measurable_interiorLeadMass b e W r).div_const _) measurable_const
  have hint1 : Integrable (fun x => portFraction b e W r x) (probedClockLaw W b) := by
    refine Integrable.of_bound (measurable_portFraction b e W r).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (portFraction_nonneg _ _ _ _ _)]
    exact portFraction_le_one _ _ _ _ _
  have hint3 : Integrable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      vecNormSq x.2 / (η ^ 2 * (W : ℝ) ^ 2 * v * t)) (probedClockLaw W b) :=
    ((integrable_vecNormSq_circularVectorLaw (Fin 2 × Fin W)).comp_snd
      (growthPathLaw W b)).div_const _
  have hint2 : Integrable (S.indicator fun _ => (1 : ℝ)) (probedClockLaw W b) :=
    (integrable_const 1).indicator hS
  have hae : ∀ᵐ x ∂probedClockLaw W b, portFraction b e W r x ≤ v + S.indicator (fun _ => 1) x +
      vecNormSq x.2 / (η ^ 2 * (W : ℝ) ^ 2 * v * t) := by
    have := (ae_growthPath_isHermitian W b)
    have h2 : ∀ᵐ x ∂probedClockLaw W b, ∀ k, (x.1.1 k).IsHermitian :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) this
    filter_upwards [h2] with x hx
    exact portFraction_le_pointwise hW hη hv ht hx x.2
  have i12 : Integrable (fun x => v + S.indicator (fun _ => (1 : ℝ)) x) (probedClockLaw W b) :=
    (integrable_const v).add hint2
  have i123 : Integrable (fun x => v + S.indicator (fun _ => (1 : ℝ)) x +
      vecNormSq x.2 / (η ^ 2 * (W : ℝ) ^ 2 * v * t)) (probedClockLaw W b) := i12.add hint3
  have hmono := integral_mono_ae hint1 i123 hae
  rw [integral_add i12 hint3, integral_add (integrable_const v) hint2,
    integral_const, integral_indicator hS, setIntegral_const, integral_div] at hmono
  have hsnd : ∫ x : GrowthPath W × (Fin 2 × Fin W → ℂ), vecNormSq x.2 ∂probedClockLaw W b =
      2 * W := by
    have hmp : MeasurePreserving Prod.snd (probedClockLaw W b)
        (circularVectorLaw (Fin 2 × Fin W)) := measurePreserving_snd
    rw [← integral_map hmp.measurable.aemeasurable measurable_vecNormSq.aestronglyMeasurable,
      hmp.map_eq, integral_vecNormSq_circularVectorLaw]
    simp
  rw [hsnd] at hmono
  simp only [smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one, one_mul,
    mul_one] at hmono
  calc _ ≤ _ := hmono
    _ = _ := by field_simp

/-- Eventually all microscopic energies `e_j(u)`, `|u| ≤ R₀`, lie in a fixed bulk interval
`bulkInterval κ`, `κ = (2 - |E|)/2`. -/
theorem eventually_microEnergy_mem_bulk {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ}
    (hE1 : -2 < E) (hE2 : E < 2) {τ : ℝ} (s : CriticalSequence τ) (R₀ : ℝ) :
    ∀ᶠ j in atTop, ∀ u ∈ Set.Icc (-R₀) R₀,
      microEnergy (s.parameters b hb hb' j) E u ∈ bulkInterval ((2 - |E|) / 2) := by
  have hρ := semicircleDensity_pos hE1 hE2
  have hEabs : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
  have hκ : 0 < (2 - |E|) / 2 := by linarith
  have hWt : Tendsto (fun j => ((s.W j : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  filter_upwards [hWt.eventually_ge_atTop (|R₀| / (Parameters.semicircleDensity E *
    ((2 - |E|) / 2)) + 1)] with j hj u hu
  have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have huabs : |u| ≤ |R₀| :=
    abs_le.2 ⟨by linarith [hu.1, le_abs_self R₀], hu.2.trans (le_abs_self _)⟩
  have h1 := abs_microEnergy_sub_le (s.parameters b hb hb' j) hρ huabs
  have h2 : |R₀| / ((s.parameters b hb hb' j).W * Parameters.semicircleDensity E) ≤
      (2 - |E|) / 2 := by
    change |R₀| / ((s.W j : ℝ) * Parameters.semicircleDensity E) ≤ (2 - |E|) / 2
    rw [div_le_iff₀ (by positivity)]
    have : |R₀| / (Parameters.semicircleDensity E * ((2 - |E|) / 2)) ≤ s.W j := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  have h3 := h1.trans h2
  rw [abs_le] at h3
  rw [bulkInterval]
  constructor <;> linarith [le_abs_self E, neg_abs_le E]

/-- `E a_port → 0`, uniformly in the microscopic energy. -/
theorem portFraction_uniform (hNeg : NegativeClockContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {τ : ℝ} (hτ : 0 < τ)
    (s : CriticalSequence τ) (R₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ u ∈ Set.Icc (-R₀) R₀,
      ∫ x, portFraction b (microEnergy (s.parameters b hb hb' j) E u) (s.W j) (s.n j - 3) x
        ∂probedClockLaw (s.W j) b ≤ ε := by
  obtain ⟨t, ht, hev⟩ := interiorClock_lowerTail hNeg hb hb' hE1 hE2 hτ s R₀
    (ε := ε / 3) (by positivity)
  have hEabs : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
  have hκ : 0 < (2 - |E|) / 2 := by linarith
  set η₀ := PhaseFractional.etaMin b ((2 - |E|) / 2)
  have hη₀ : 0 < η₀ := PhaseFractional.etaMin_pos (by linarith) hκ
  set v := ε / 3
  have hv : 0 < v := by positivity
  have hWt : Tendsto (fun j => ((s.W j : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  filter_upwards [hev, eventually_microEnergy_mem_bulk hb hb' hE1 hE2 s R₀,
    hWt.eventually_ge_atTop (2 / (η₀ ^ 2 * v * t * (ε / 3)) + 1)] with j hj hbulk hWj u hu
  have hW : 0 < s.W j := s.W_pos j
  have hW' : (0 : ℝ) < s.W j := by exact_mod_cast hW
  have hη := PhaseFractional.boundaryZ_im_ge (b := b) (by linarith) hκ (hbulk u hu)
  have hηpos : 0 < (boundaryZ b (microEnergy (s.parameters b hb hb' j) E u)).im :=
    hη₀.trans_le hη
  have hmain := integral_portFraction_le (r := s.n j - 3) hW hηpos hv ht
  have hP := (hj u hu)
  have hPr : (probedClockLaw (s.W j) b {x | interiorLeadMass b
      (microEnergy (s.parameters b hb hb' j) E u) (s.W j) (s.n j - 3) x /
        ((s.W j : ℕ) : ℝ) ^ 2 ≤ t}).toReal ≤ ε / 3 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hP
  have hlast : 2 / ((boundaryZ b (microEnergy (s.parameters b hb hb' j) E u)).im ^ 2 *
      (s.W j : ℝ) * v * t) ≤ ε / 3 := by
    have hη2 : η₀ ^ 2 ≤ (boundaryZ b (microEnergy (s.parameters b hb hb' j) E u)).im ^ 2 :=
      pow_le_pow_left₀ hη₀.le hη 2
    calc 2 / ((boundaryZ b (microEnergy (s.parameters b hb hb' j) E u)).im ^ 2 *
          (s.W j : ℝ) * v * t) ≤ 2 / (η₀ ^ 2 * (s.W j : ℝ) * v * t) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          have := mul_le_mul_of_nonneg_right hη2 (show 0 ≤ (s.W j : ℝ) * v * t by positivity)
          nlinarith
      _ ≤ ε / 3 := by
          rw [div_le_iff₀ (by positivity)]
          have h1 : 2 / (η₀ ^ 2 * v * t * (ε / 3)) ≤ s.W j := by linarith
          rw [div_le_iff₀ (by positivity)] at h1
          nlinarith
  calc _ ≤ v + _ + _ := hmain
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end BlockBand.Endpoints
