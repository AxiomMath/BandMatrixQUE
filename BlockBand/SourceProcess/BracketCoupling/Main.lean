module

public import BlockBand.SourceProcess.BracketCoupling.StoppedSq
public import BlockBand.SourceProcess.RankFree.Main
public import BlockBand.SourceProcess.BracketDef.Interface

/-!
# The stopped bracket coupling: Burkholder and the frame coupling

`stoppedBracketCoupling_holds` proves `StoppedBracketCoupling`.

Measure `driverLaw μ`, augmented filtration, Frobenius norms. With `R = traceProc X₁ + traceProc X₂`
(the dominating trace process, continuous modification `R'`), `σ_R` its closed exit at `L`,
`θ` the closed exit of `‖X₁ - X₂‖` at `√u` and `ρ = σ_R ∧ θ`:

* before `σ_R`, `‖X₁‖² + ‖X₂‖² ≤ L`, so the bracket hypothesis gives `∑_a ‖σ₁_a‖² ≤ C_L` and,
  before `ρ`, `∑_a ‖σ₁_a - σ₂_a‖² ≤ C_L u` (here `C_L ≥ 0` is forced by the hypothesis itself);
  `lintegral_hsSq_stopped_le` gives `E‖ΔY₁‖²_{t∧σ_R} ≤ C_L t`, `E‖ΔY₁ - ΔY₂‖²_{t∧ρ} ≤ C_L u t`,
  and Chebyshev;
* `{σ_R ≤ t} ⊆ {L ≤ R_{t∧σ_R}}`: Markov with `lintegral_stopped_trace_le`;
* `{σ_R > t, θ ≤ t} ⊆ {e^{-ct} u ≤ e^{-c(t∧ρ)}‖X₁ - X₂‖²_{t∧ρ}}`, `c = D₀L²/2`: Markov with
  `lintegral_stopped_distance_le` (the closed-level event, so no limit `v ↓ u` is needed);
* on `{ρ > t}` the stopped and unstopped increments agree; union bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BracketCoupling
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

theorem aemeasurable_hsSq {Ω m n : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [Fintype m]
    [Fintype n] {f : Ω → Matrix m n ℂ} (hf : StronglyMeasurable f) :
    AEMeasurable (fun x => hsSq (f x)) Q := by
  simp only [hsSq_eq]
  exact (hf.norm.measurable.pow_const 2).aemeasurable

theorem chebyshev_hsSq {Ω m n : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [Fintype m]
    [Fintype n] {f : Ω → Matrix m n ℂ} (hf : StronglyMeasurable f) {δ a : ℝ} (hδ : 0 < δ)
    (hI : ∫⁻ x, ENNReal.ofReal (hsSq (f x)) ∂Q ≤ ENNReal.ofReal a) :
    Q {x | δ ≤ hsSq (f x)} ≤ ENNReal.ofReal (a / δ) := by
  rw [ENNReal.ofReal_div_of_pos hδ]
  exact (meas_le_lintegral_div (aemeasurable_hsSq hf) hδ).trans (ENNReal.div_le_div_right hI _)

theorem stoppedBracketCoupling_holds :
    BlockBand.SourceProcess.BracketDef.StoppedBracketCoupling := by
  intro D0 C ι c S _ _ _ _ _ μ _ Naux P D hD0 hP hD ξ₁ ξ₂ hξ₁ hξ₂ hξ₁0 hξ₂0 nb τ col w β hτ hw
    hcol hDcol hξc hwP X₁ X₂ hX₁ hX₂ _ Y₁ Y₂ σ₁ σ₂ hY₁ hY₂ hCL L u δ t hL hu hδ
  set Q := driverLaw (κ := SourceNoise ι) μ
  have hξ₁c : ∀ᵐ x ∂Q, ∀ k i, ξ₁ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hξc k).mono fun x hx i => (hx i).1
  have hξ₂c : ∀ᵐ x ∂Q, ∀ k i, ξ₂ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hξc k).mono fun x hx i => (hx i).2
  have hwβ : ∀ k, ∀ᵐ x ∂Q, ∑ i, ‖w k x i‖ ^ 2 = β k := fun k => (hwP k).mono fun x hx => hx.2
  set cc := D0 * L ^ 2 / 2 with hcc
  set R := fun t x => traceProc X₁ τ col w β t x + traceProc X₂ τ col w β t x
  have hRloc := (locMart_traceProc hD0 hP hD hξ₁ hξ₁0 hτ hw hDcol hξ₁c hwβ hX₁).add
    (locMart_traceProc hD0 hP hD hξ₂ hξ₂0 hτ hw hDcol hξ₂c hwβ hX₂)
  obtain ⟨R', hR'a, hR'c, hRR'⟩ := exists_continuous_modification hRloc.prog.stronglyAdapted
    hRloc.cont
  have hσ := isStoppingTime_exitTimeOf hR'a hR'c L
  have hd₁ := norm_sq_le_traceProc hD0 hP hD hξ₁ hξ₁0 hτ hw hcol hDcol hξ₁c hwβ hX₁
  have hd₂ := norm_sq_le_traceProc hD0 hP hD hξ₂ hξ₂0 hτ hw hcol hDcol hξ₂c hwβ hX₂
  have hR0 : ∀ᵐ x ∂Q, ∀ s, 0 ≤ R s x := by
    filter_upwards [hd₁, hd₂] with x h1 h2 s
    have a := h1 s
    have b := h2 s
    have a' : 0 ≤ ‖X₁ s x‖ ^ 2 := sq_nonneg _
    have b' : 0 ≤ ‖X₂ s x‖ ^ 2 := sq_nonneg _
    show 0 ≤ traceProc X₁ τ col w β s x + traceProc X₂ τ col w β s x
    linarith
  -- before the trace exit, `‖X₁‖² + ‖X₂‖² ≤ L`
  have hσL : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ exitTimeOf R' L x →
      hsSq (X₁ s x) + hsSq (X₂ s x) ≤ L := by
    filter_upwards [hd₁, hd₂, hRR'] with x h1 h2 h3 s hs0 hs
    have h := norm_le_of_le_exitTimeOf (hR'c x) hs0 hs
    rw [h3 s, Real.norm_eq_abs] at h
    rw [hsSq_eq, hsSq_eq]
    linarith [le_abs_self (R s x), h1 s, h2 s]
  -- the trace exit by time `t`
  have hmB : AEMeasurable (stoppedProcess R (exitTimeOf R' L) t) Q :=
    ((hRloc.prog.stronglyAdapted_stoppedProcess hσ t).mono
      ((driverAugmented (κ := SourceNoise ι) μ).le t)).measurable.aemeasurable
  have hB := lintegral_stopped_trace_le hD0 hP hD hξ₁ hξ₂ hξ₁0 hξ₂0 hτ hw hcol hDcol hξ₁c hξ₂c hwβ
    hX₁ hX₂ hσ t
  have PB := (meas_le_lintegral_div hmB hL).trans (ENNReal.div_le_div_right hB _)
  have hexit : ∀ᵐ x ∂Q, exitTimeOf R' L x ≤ (t : WithTop ℝ≥0) →
      L ≤ stoppedProcess R (exitTimeOf R' L) t x := by
    filter_upwards [hRR', hR0] with x h3 hR0 hσT
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hσT)
    have hK' := le_norm_exitTimeOf (hR'c x) hm.symm
    rw [h3 m, Real.norm_eq_abs, abs_of_nonneg (hR0 m)] at hK'
    have hmT : m ≤ t := WithTop.coe_le_coe.1 (hm ▸ hσT)
    rw [stoppedProcess_eq_stopTime, ← hm, stopTime_coe, min_eq_right hmT]
    exact hK'
  constructor
  · -- bound 1: trace exit, distance exit, and the stopped bracket
    have hΔ := isNative_distance hX₁ hX₂
    obtain ⟨Δ', hΔ'a, hΔ'c, hΔΔ'⟩ := exists_continuous_modification hΔ.adapted hΔ.continuous
    have hθ := isStoppingTime_exitTimeOf hΔ'a hΔ'c (Real.sqrt u)
    have hρ := hσ.min hθ
    have hρK : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, 0 < s →
        (s : WithTop ℝ≥0) ≤ min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x) →
        ‖X₁ s x‖ ^ 2 + ‖X₂ s x‖ ^ 2 ≤ L := by
      filter_upwards [hσL] with x hx s hs0 hs
      have := hx s hs0 (hs.trans (min_le_left _ _))
      rwa [hsSq_eq, hsSq_eq] at this
    have hρu : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, 0 < s →
        (s : WithTop ℝ≥0) ≤ min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x) →
        hsSq (X₁ s x - X₂ s x) ≤ u := by
      filter_upwards [hΔΔ'] with x h4 s hs0 hs
      have h := norm_le_of_le_exitTimeOf (hΔ'c x) hs0 (hs.trans (min_le_right _ _))
      rw [h4 s] at h
      rw [hsSq_eq]
      have := pow_le_pow_left₀ (norm_nonneg _) h 2
      rwa [Real.sq_sqrt hu.le] at this
    have hbd : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, 0 < s →
        (s : WithTop ℝ≥0) ≤ min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x) →
        ∑ a, hsSq (σ₁ a s x - σ₂ a s x) ≤ C L * u := by
      filter_upwards [hσL, hρu] with x hx hxu s hs0 hs
      have h := hCL L s x (hx s hs0 (hs.trans (min_le_left _ _)))
      have hC0 : 0 ≤ C L := (Finset.sum_nonneg fun a _ => hsSq_nonneg' _).trans h.1
      exact h.2.trans (mul_le_mul_of_nonneg_left (hxu s hs0 hs) hC0)
    have hYd := isNative_sub hY₁ hY₂
    have hS := lintegral_hsSq_stopped_le hYd hρ hbd t
    have hmd : StronglyMeasurable (fun x => stoppedProcess (fun t x => Y₁ t x - Y₂ t x)
        (fun x => min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x)) t x -
          (Y₁ 0 x - Y₂ 0 x)) :=
      ((hYd.progressive.stronglyAdapted_stoppedProcess hρ t).mono
        ((driverAugmented (κ := SourceNoise ι) μ).le t)).sub
        ((hYd.adapted 0).mono ((driverAugmented (κ := SourceNoise ι) μ).le 0))
    have PC := chebyshev_hsSq hmd hδ hS
    have hA := lintegral_stopped_distance_le hD0 hP hD hξ₁ hξ₂ hξ₁0 hξ₂0 hDcol hξ₁c hξ₂c hX₁ hX₂
      hρ hρK t
    have hZloc := hΔ.locMart_disc (contDiff_normSq (ι := ι) (c := c) (k := 2)) cc
    have hmA : AEMeasurable (stoppedProcess (fun (t : ℝ≥0) x => Real.exp (-cc * t) *
        ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' L x)
          (exitTimeOf Δ' (Real.sqrt u) x)) t) Q :=
      ((hZloc.prog.stronglyAdapted_stoppedProcess hρ t).mono
        ((driverAugmented (κ := SourceNoise ι) μ).le t)).measurable.aemeasurable
    have hpos : 0 < Real.exp (-cc * t) * u := mul_pos (Real.exp_pos _) hu
    have PA : Q {x | Real.exp (-cc * t) * u ≤ stoppedProcess (fun (t : ℝ≥0) x =>
        Real.exp (-cc * t) * ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' L x)
          (exitTimeOf Δ' (Real.sqrt u) x)) t x} ≤
        ENNReal.ofReal (Real.exp (D0 * L ^ 2 * t / 2)) *
          (∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x - ξ₂ x)) ∂Q) / ENNReal.ofReal u := by
      refine (meas_le_lintegral_div hmA hpos).trans ?_
      refine (ENNReal.div_le_div_right hA _).trans (le_of_eq ?_)
      rw [show -cc * (t : ℝ) = -(D0 * L ^ 2 * t / 2) by rw [hcc]; ring, ennreal_div_exp_mul]
    have hincl : {x | δ < hsSq ((Y₁ t x - Y₁ 0 x) - (Y₂ t x - Y₂ 0 x))} ≤ᵐ[Q]
        (({x | L ≤ stoppedProcess R (exitTimeOf R' L) t x} ∪
          {x | Real.exp (-cc * t) * u ≤ stoppedProcess (fun (t : ℝ≥0) x =>
            Real.exp (-cc * t) * ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' L x)
              (exitTimeOf Δ' (Real.sqrt u) x)) t x}) ∪
          {x | δ ≤ hsSq (stoppedProcess (fun t x => Y₁ t x - Y₂ t x)
            (fun x => min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x)) t x -
              (Y₁ 0 x - Y₂ 0 x))} : Set _) := by
      filter_upwards [hexit, hΔΔ'] with x hx h4 hδx
      by_cases hσT : exitTimeOf R' L x ≤ (t : WithTop ℝ≥0)
      · exact Or.inl (Or.inl (hx hσT))
      have hlt : (t : WithTop ℝ≥0) < exitTimeOf R' L x := not_le.1 hσT
      by_cases hθT : exitTimeOf Δ' (Real.sqrt u) x ≤ (t : WithTop ℝ≥0)
      · refine Or.inl (Or.inr ?_)
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hθT)
        have hmT : m ≤ t := WithTop.coe_le_coe.1 (hm ▸ hθT)
        have hmin : min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x) = m := by
          rw [← hm]
          exact min_eq_right ((WithTop.coe_le_coe.2 hmT).trans hlt.le)
        have hu' := le_norm_exitTimeOf (hΔ'c x) hm.symm
        rw [h4 m] at hu'
        have hu2 : u ≤ ‖X₁ m x - X₂ m x‖ ^ 2 := by
          have := pow_le_pow_left₀ (Real.sqrt_nonneg u) hu' 2
          rwa [Real.sq_sqrt hu.le] at this
        show Real.exp (-cc * t) * u ≤ stoppedProcess (fun (t : ℝ≥0) x => Real.exp (-cc * t) *
            ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' L x)
              (exitTimeOf Δ' (Real.sqrt u) x)) t x
        rw [stoppedProcess_eq_stopTime, hmin, stopTime_coe, min_eq_right hmT]
        have hexp : Real.exp (-cc * t) ≤ Real.exp (-cc * m) := by
          refine Real.exp_le_exp.2 ?_
          have : (m : ℝ) ≤ t := hmT
          have hc0 : 0 ≤ cc := by positivity
          nlinarith
        exact mul_le_mul hexp hu2 hu.le (Real.exp_pos _).le
      · right
        have hlt' : (t : WithTop ℝ≥0) <
            min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x) :=
          lt_min hlt (not_le.1 hθT)
        show δ ≤ hsSq (stoppedProcess (fun t x => Y₁ t x - Y₂ t x)
            (fun x => min (exitTimeOf R' L x) (exitTimeOf Δ' (Real.sqrt u) x)) t x -
              (Y₁ 0 x - Y₂ 0 x))
        rw [stoppedProcess_eq_stopTime, stopTime_of_lt hlt',
          show Y₁ t x - Y₂ t x - (Y₁ 0 x - Y₂ 0 x) = Y₁ t x - Y₁ 0 x - (Y₂ t x - Y₂ 0 x) by abel]
        exact le_of_lt hδx
    have P2 : ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂Q) +
        ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L ≤
        2 * ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂Q) +
          ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L :=
      ENNReal.div_le_div_right (le_mul_of_one_le_left zero_le one_le_two) _
    exact (measure_mono_ae hincl).trans ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add (PB.trans P2) PA)) PC))
  · -- bound 2: only the trace exit
    have hb₁ : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ exitTimeOf R' L x →
        ∑ a, hsSq (σ₁ a s x) ≤ C L := by
      filter_upwards [hσL] with x hx s hs0 hs
      exact (hCL L s x (hx s hs0 hs)).1
    have hS := lintegral_hsSq_stopped_le hY₁ hσ hb₁ t
    have hm1 : StronglyMeasurable (fun x => stoppedProcess Y₁ (exitTimeOf R' L) t x - Y₁ 0 x) :=
      ((hY₁.progressive.stronglyAdapted_stoppedProcess hσ t).mono
        ((driverAugmented (κ := SourceNoise ι) μ).le t)).sub
        ((hY₁.adapted 0).mono ((driverAugmented (κ := SourceNoise ι) μ).le 0))
    have PC := chebyshev_hsSq hm1 hδ hS
    have hincl : {x | δ < hsSq (Y₁ t x - Y₁ 0 x)} ≤ᵐ[Q]
        ({x | L ≤ stoppedProcess R (exitTimeOf R' L) t x} ∪
          {x | δ ≤ hsSq (stoppedProcess Y₁ (exitTimeOf R' L) t x - Y₁ 0 x)} : Set _) := by
      filter_upwards [hexit] with x hx hδx
      by_cases hσT : exitTimeOf R' L x ≤ (t : WithTop ℝ≥0)
      · exact Or.inl (hx hσT)
      · right
        show δ ≤ hsSq (stoppedProcess Y₁ (exitTimeOf R' L) t x - Y₁ 0 x)
        rw [stoppedProcess_eq_stopTime, stopTime_of_lt (not_le.1 hσT)]
        exact le_of_lt hδx
    exact (measure_mono_ae hincl).trans ((measure_union_le _ _).trans (add_le_add PB PC))

end BlockBand.SourceProcess.BracketCoupling
