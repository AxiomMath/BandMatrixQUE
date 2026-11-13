module

public import BlockBand.SourceProcess.RankFree.MeanBounds
public import BlockBand.SourceProcess.RankFree.LocMartBound

/-!
# The rank-free coupling `rankFreeCoupling_holds`

`rankFreeCoupling_holds : RankFreeCoupling`: for two born solutions of the finite-source SDE
with the same shared births, `X = ‖V₁ - V₂‖²_HS`, `R = ‖V₁‖²_HS + ‖V₂‖²_HS` and
`B_birth = Σ_k β_k`,
`P{sup_{t ≤ T} X_t > u} ≤ (E R₀ + 2B_birth)/K + e^{D₀K²T/2} E X₀/u`.

Proof. `R = traceProc X₁ + traceProc X₂ ≥ ‖X₁‖² + ‖X₂‖²` is a continuous
nonnegative `LocMart` with zero drift starting below `‖ξ₁‖² + ‖ξ₂‖² + 2B_birth`; `σ` is its first
passage at `K` (on a continuous modification). `Z = e^{-ct}‖X₁ - X₂‖²`, `c = D₀K²/2`, has
nonpositive drift before `σ`; `θ` is the first passage of `‖X₁ - X₂‖` at `√u`. On
`{sup_{t≤T} X_t > u}`, either `σ ≤ T` and `R_{T∧σ} ≥ K`, or `σ > T` and
`Z_{T∧σ∧θ} ≥ e^{-cT}u`. Markov's inequality and the two stopped mean bounds finish.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

theorem ennreal_div_exp_mul (I : ℝ≥0∞) (a u : ℝ) :
    I / ENNReal.ofReal (Real.exp (-a) * u) = ENNReal.ofReal (Real.exp a) * I / ENNReal.ofReal u := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
    neg_neg]
  ring

/-- **The rank-free coupling bound** `RankFreeCoupling` (see the module docstring). -/
theorem rankFreeCoupling_holds : RankFreeCoupling := by
  intro ι c S _ _ _ _ _ μ _ D0 Naux P D hD0 hP hD ξ₁ ξ₂ hξ₁ hξ₂ hξ₁0 hξ₂0 nb τ col w β hτ hw hcol
    hDcol hξc hwP X₁ X₂ hX₁ hX₂ _ K u T hK hu hT
  set Q := driverLaw (κ := SourceNoise ι) μ
  have hξ₁c : ∀ᵐ x ∂Q, ∀ k i, ξ₁ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hξc k).mono fun x hx i => (hx i).1
  have hξ₂c : ∀ᵐ x ∂Q, ∀ k i, ξ₂ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hξc k).mono fun x hx i => (hx i).2
  have hwβ : ∀ k, ∀ᵐ x ∂Q, ∑ i, ‖w k x i‖ ^ 2 = β k := fun k => (hwP k).mono fun x hx => hx.2
  set cc := D0 * K ^ 2 / 2 with hcc
  have hc0 : 0 ≤ cc := by positivity
  set Tn := T.toNNReal
  set R := fun t x => traceProc X₁ τ col w β t x + traceProc X₂ τ col w β t x
  have hRloc := (locMart_traceProc hD0 hP hD hξ₁ hξ₁0 hτ hw hDcol hξ₁c hwβ hX₁).add
    (locMart_traceProc hD0 hP hD hξ₂ hξ₂0 hτ hw hDcol hξ₂c hwβ hX₂)
  obtain ⟨R', hR'a, hR'c, hRR'⟩ := exists_continuous_modification hRloc.prog.stronglyAdapted
    hRloc.cont
  have hσ := isStoppingTime_exitTimeOf hR'a hR'c K
  have hΔ := isNative_distance hX₁ hX₂
  obtain ⟨Δ', hΔ'a, hΔ'c, hΔΔ'⟩ := exists_continuous_modification hΔ.adapted hΔ.continuous
  have hθ := isStoppingTime_exitTimeOf hΔ'a hΔ'c (Real.sqrt u)
  have hρ := hσ.min hθ
  have hd₁ := norm_sq_le_traceProc hD0 hP hD hξ₁ hξ₁0 hτ hw hcol hDcol hξ₁c hwβ hX₁
  have hd₂ := norm_sq_le_traceProc hD0 hP hD hξ₂ hξ₂0 hτ hw hcol hDcol hξ₂c hwβ hX₂
  have hρK : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, 0 < s →
      (s : WithTop ℝ≥0) ≤ min (exitTimeOf R' K x) (exitTimeOf Δ' (Real.sqrt u) x) →
      ‖X₁ s x‖ ^ 2 + ‖X₂ s x‖ ^ 2 ≤ K := by
    filter_upwards [hd₁, hd₂, hRR'] with x h1 h2 h3 s hs0 hs
    have h := norm_le_of_le_exitTimeOf (hR'c x) hs0 (hs.trans (min_le_left _ _))
    rw [h3 s, Real.norm_eq_abs] at h
    linarith [le_abs_self (R s x), h1 s, h2 s]
  have hA := lintegral_stopped_distance_le hD0 hP hD hξ₁ hξ₂ hξ₁0 hξ₂0 hDcol hξ₁c hξ₂c hX₁ hX₂
    hρ hρK Tn
  have hB := lintegral_stopped_trace_le hD0 hP hD hξ₁ hξ₂ hξ₁0 hξ₂0 hτ hw hcol hDcol hξ₁c hξ₂c hwβ
    hX₁ hX₂ hσ Tn
  have hZloc := hΔ.locMart_disc (contDiff_normSq (ι := ι) (c := c) (k := 2)) cc
  have hmA : AEMeasurable (stoppedProcess (fun (t : ℝ≥0) x => Real.exp (-cc * t) *
      ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' K x)
        (exitTimeOf Δ' (Real.sqrt u) x)) Tn) Q :=
    ((hZloc.prog.stronglyAdapted_stoppedProcess hρ Tn).mono
      ((driverAugmented (κ := SourceNoise ι) μ).le Tn)).measurable.aemeasurable
  have hmB : AEMeasurable (stoppedProcess R (exitTimeOf R' K) Tn) Q :=
    ((hRloc.prog.stronglyAdapted_stoppedProcess hσ Tn).mono
      ((driverAugmented (κ := SourceNoise ι) μ).le Tn)).measurable.aemeasurable
  have hincl : {x | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ u < hsSq (X₁ t x - X₂ t x)} ≤ᵐ[Q]
      ({x | K ≤ stoppedProcess R (exitTimeOf R' K) Tn x} ∪
        {x | Real.exp (-cc * Tn) * u ≤ stoppedProcess (fun (t : ℝ≥0) x => Real.exp (-cc * t) *
          ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' K x)
            (exitTimeOf Δ' (Real.sqrt u) x)) Tn x} : Set _) := by
    filter_upwards [hd₁, hd₂, hRR', hΔΔ'] with x h1 h2 h3 h4 hx
    obtain ⟨t, htT, htu⟩ := hx
    rw [hsSq_eq] at htu
    have htn : t ≤ Tn := by
      rw [← Real.toNNReal_coe (r := t)]
      exact Real.toNNReal_le_toNNReal htT
    have hR0 : ∀ s, 0 ≤ R s x := fun s => by
      have a := h1 s
      have b := h2 s
      have a' : 0 ≤ ‖X₁ s x‖ ^ 2 := sq_nonneg _
      have b' : 0 ≤ ‖X₂ s x‖ ^ 2 := sq_nonneg _
      show 0 ≤ traceProc X₁ τ col w β s x + traceProc X₂ τ col w β s x
      linarith
    by_cases hσT : exitTimeOf R' K x ≤ (Tn : WithTop ℝ≥0)
    · left
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hσT)
      have hK' := le_norm_exitTimeOf (hR'c x) hm.symm
      rw [h3 m, Real.norm_eq_abs, abs_of_nonneg (hR0 m)] at hK'
      have hmT : m ≤ Tn := WithTop.coe_le_coe.1 (hm ▸ hσT)
      show K ≤ stoppedProcess R (exitTimeOf R' K) Tn x
      rw [stoppedProcess_eq_stopTime, ← hm, stopTime_coe, min_eq_right hmT]
      exact hK'
    · right
      have hlt : (Tn : WithTop ℝ≥0) < exitTimeOf R' K x := not_le.1 hσT
      have hsq : Real.sqrt u ≤ ‖Δ' t x‖ := by
        rw [h4 t]
        have := Real.sqrt_lt_sqrt hu.le htu
        rw [Real.sqrt_sq (norm_nonneg _)] at this
        exact this.le
      have hθt := exitTimeOf_le hsq
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hθt)
      have hmt : m ≤ t := WithTop.coe_le_coe.1 (hm ▸ hθt)
      have hmT : m ≤ Tn := hmt.trans htn
      have hmin : min (exitTimeOf R' K x) (exitTimeOf Δ' (Real.sqrt u) x) = m := by
        rw [← hm]
        exact min_eq_right ((WithTop.coe_le_coe.2 hmT).trans hlt.le)
      have hu' := le_norm_exitTimeOf (hΔ'c x) hm.symm
      rw [h4 m] at hu'
      have hu2 : u ≤ ‖X₁ m x - X₂ m x‖ ^ 2 := by
        have := pow_le_pow_left₀ (Real.sqrt_nonneg u) hu' 2
        rwa [Real.sq_sqrt hu.le] at this
      show Real.exp (-cc * Tn) * u ≤ stoppedProcess (fun (t : ℝ≥0) x => Real.exp (-cc * t) *
          ‖X₁ t x - X₂ t x‖ ^ 2) (fun x => min (exitTimeOf R' K x)
            (exitTimeOf Δ' (Real.sqrt u) x)) Tn x
      rw [stoppedProcess_eq_stopTime, hmin, stopTime_coe, min_eq_right hmT]
      have hexp : Real.exp (-cc * Tn) ≤ Real.exp (-cc * m) := by
        refine Real.exp_le_exp.2 ?_
        have : (m : ℝ) ≤ Tn := hmT
        nlinarith
      exact mul_le_mul hexp hu2 hu.le (Real.exp_pos _).le
  refine (measure_mono_ae hincl).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · exact (meas_le_lintegral_div hmB hK).trans (ENNReal.div_le_div_right hB _)
  · have hpos : 0 < Real.exp (-cc * Tn) * u := mul_pos (Real.exp_pos _) hu
    refine (meas_le_lintegral_div hmA hpos).trans ?_
    refine (ENNReal.div_le_div_right hA _).trans (le_of_eq ?_)
    rw [show -cc * (Tn : ℝ) = -(D0 * K ^ 2 * T / 2) by
      rw [hcc, Real.coe_toNNReal _ hT]; ring, ennreal_div_exp_mul]

end BlockBand.SourceProcess.RankFree
