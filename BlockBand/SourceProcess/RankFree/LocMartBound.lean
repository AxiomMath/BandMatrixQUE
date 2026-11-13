module

public import BlockBand.SourceProcess.RankFree.LocMart

/-!
# Nonnegative `LocMart`s with nonpositive drift decrease in mean

`LocMart.lintegral_le`: if `Z ≥ 0` is a `LocMart` with `∫_0^t β ≤ 0` for all `t` (a.s.) and
`Z_0` is `𝓖_0`-measurable, then `E Z_t ≤ E Z_0` (lower Lebesgue integrals; no integrability of
`Z_t` assumed). Proof as in `NativeSDE.lintegral_le_of_nonpos_drift` (which needs a full
semimartingale): on `{Z_0 ≤ m}` along the localizing sequence, then Fatou, then `m → ∞`.
`meas_le_lintegral_div`: Markov's inequality in the form used for the rank-free coupling.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z β : ℝ≥0 → Ω → ℝ}

theorem LocMart.setLIntegral_le (h : LocMart Q 𝓖 Z β) (hZ : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ Z t ω)
    (hβ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω ≤ 0)
    (h0 : StronglyMeasurable[𝓖 0] (Z 0)) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A) {B : ℝ}
    (hB : ∀ ω ∈ A, Z 0 ω ≤ B) (t : ℝ≥0) :
    ∫⁻ ω in A, ENNReal.ofReal (Z t ω) ∂Q ≤ ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω) ∂Q := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := h.loc
  have hAm : MeasurableSet A := 𝓖.le 0 _ hA
  have hZ0m : StronglyMeasurable (Z 0) := h0.mono (𝓖.le 0)
  have hZ0int : IntegrableOn (Z 0) A Q := by
    refine Measure.integrableOn_of_bounded (measure_ne_top _ _) hZ0m.aestronglyMeasurable
      (M := max B 0) ?_
    refine (ae_restrict_iff' hAm).2 ?_
    filter_upwards [hZ] with ω hω hωA
    rw [Real.norm_eq_abs, abs_of_nonneg (hω 0)]
    exact (hB ω hωA).trans (le_max_left _ _)
  have hk : ∀ k, ∫⁻ ω in A, ENNReal.ofReal (stoppedProcess Z (τ k) t ω) ∂Q ≤
      ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω) ∂Q := by
    intro k
    obtain ⟨M, hM, hMe⟩ := hmart k
    set N := stoppedProcess (locComp Z β) (τ k) with hNdef
    have hN0 : ∀ ω, N 0 ω = 0 := fun ω => by
      have h0' : stopTime (τ k ω) 0 = 0 := le_antisymm (stopTime_le _ 0) zero_le
      simp [N, stoppedProcess_eq_stopTime, locComp, h0']
    have hNint : Integrable (N t) Q := (hM.integrable t).congr (hMe t)
    have hint0 : ∫ ω in A, N t ω ∂Q = 0 := by
      rw [← integral_congr_ae (ae_restrict_of_ae (hMe t)), ← hM.setIntegral_eq zero_le hA,
        integral_congr_ae (ae_restrict_of_ae (hMe 0))]
      simp [hN0]
    have hpt : ∀ᵐ ω ∂Q, stoppedProcess Z (τ k) t ω ≤ Z 0 ω + N t ω := by
      filter_upwards [hβ] with ω hω
      simp only [N, stoppedProcess_eq_stopTime, locComp]
      linarith [hω (stopTime (τ k ω) t)]
    have hnn : ∀ᵐ ω ∂Q, 0 ≤ Z 0 ω + N t ω := by
      filter_upwards [hpt, hZ] with ω h1 h2
      exact (h2 _).trans h1
    calc ∫⁻ ω in A, ENNReal.ofReal (stoppedProcess Z (τ k) t ω) ∂Q
        ≤ ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω + N t ω) ∂Q :=
          lintegral_mono_ae (ae_restrict_of_ae (hpt.mono fun ω h => ENNReal.ofReal_le_ofReal h))
      _ = ENNReal.ofReal (∫ ω in A, (Z 0 ω + N t ω) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal (hZ0int.add hNint.integrableOn)
            (ae_restrict_of_ae hnn)).symm
      _ = ENNReal.ofReal (∫ ω in A, Z 0 ω ∂Q) := by
          rw [integral_add hZ0int hNint.integrableOn, hint0, add_zero]
      _ = ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω) ∂Q :=
          ofReal_integral_eq_lintegral_ofReal hZ0int (ae_restrict_of_ae (hZ.mono fun ω h => h 0))
  have hmeas : ∀ k, Measurable fun ω => ENNReal.ofReal (stoppedProcess Z (τ k) t ω) := fun k =>
    ENNReal.measurable_ofReal.comp
      ((h.prog.stronglyAdapted_stoppedProcess (hτ k) t).mono (𝓖.le t)).measurable
  calc ∫⁻ ω in A, ENNReal.ofReal (Z t ω) ∂Q
      = ∫⁻ ω in A, liminf (fun k => ENNReal.ofReal (stoppedProcess Z (τ k) t ω)) atTop ∂Q := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hτlim] with ω hω
        refine (Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)).symm
        filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 hω t] with k hk
        rw [stoppedProcess_eq_of_le hk.le]
    _ ≤ liminf (fun k => ∫⁻ ω in A, ENNReal.ofReal (stoppedProcess Z (τ k) t ω) ∂Q) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ ∫⁻ ω in A, ENNReal.ofReal (Z 0 ω) ∂Q :=
        liminf_le_of_frequently_le' (Frequently.of_forall hk)

/-- **Nonnegative `LocMart`s with nonpositive drift decrease in mean.** -/
theorem LocMart.lintegral_le (h : LocMart Q 𝓖 Z β) (hZ : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ Z t ω)
    (hβ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω ≤ 0)
    (h0 : StronglyMeasurable[𝓖 0] (Z 0)) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Z t ω) ∂Q ≤ ∫⁻ ω, ENNReal.ofReal (Z 0 ω) ∂Q := by
  set A : ℕ → Set Ω := fun m => {ω | Z 0 ω ≤ m}
  have hAm : ∀ m, MeasurableSet[𝓖 0] (A m) := fun m => h0.measurable measurableSet_Iic
  have hmono : Monotone A := fun m m' hmm' ω (hω : Z 0 ω ≤ m) =>
    hω.trans (Nat.cast_le.2 hmm')
  have hU : (⋃ m, A m) = univ := by
    refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
    obtain ⟨m, hm⟩ := exists_nat_ge (Z 0 ω)
    exact ⟨m, hm⟩
  have e : ∀ f : Ω → ℝ≥0∞, ∫⁻ ω, f ω ∂Q = ⨆ m, ∫⁻ ω in A m, f ω ∂Q := fun f => by
    rw [← setLIntegral_iUnion_of_directed f hmono.directed_le, hU, Measure.restrict_univ]
  rw [e, e]
  exact iSup_mono fun m => h.setLIntegral_le hZ hβ h0 (hAm m) (fun ω hω => hω) t

omit [IsProbabilityMeasure Q] in
/-- **Markov's inequality** `Q{a ≤ f} ≤ E f⁺ / a`. -/
theorem meas_le_lintegral_div {f : Ω → ℝ} (hf : AEMeasurable f Q) {a : ℝ} (ha : 0 < a) :
    Q {ω | a ≤ f ω} ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂Q) / ENNReal.ofReal a := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 ha).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hf.ennreal_ofReal (ENNReal.ofReal a))
  exact mul_le_mul' le_rfl (measure_mono fun ω (hω : a ≤ f ω) => ENNReal.ofReal_le_ofReal hω)

end BlockBand.SourceProcess.RankFree
