module

public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Exit

/-!
# Optional sampling for martingale modifications and the stopped-product identity

* `integral_mul_sub_stopped_eq_zero`: for `Φ` with a martingale modification and a.s.
  continuous paths, a stopping time `ρ` and bounded `𝓕_ρ`-measurable `ζ`,
  `E[ζ (Φ_t - Φ_{t∧ρ})] = 0` (via the stopping times `ρ_A = ρ 1_A + ∞ 1_{Aᶜ}` and
  `exists_martingale_stoppedProcess`, then conditional expectation given `𝓕_ρ`);
* `integral_mul_stoppedProd`: if moreover `ρ ≤ T` and `Z^ρ` is adapted and bounded, the process
  `K_t = (Φ_t - Φ_{t∧ρ}) Z_{t∧ρ}` satisfies `E[η K_t] = E[η K_r]` for bounded
  `𝓕_r`-measurable `η`, `r ≤ t` (the increment is `Z_ρ (Φ_t - Φ_{t ∧ (ρ ∨ r)})`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  exists_martingale_stoppedProcess)

theorem stopTime_of_le' {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ τ) :
    stopTime τ t = t := by
  unfold stopTime; rw [min_eq_left h, WithTop.untopA_eq_untop WithTop.coe_ne_top,
    WithTop.untop_coe]

theorem stopTime_of_ge {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : τ ≤ t) : stopTime τ t = τ.untopA := by
  unfold stopTime; rw [min_eq_right h]

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

open Classical in
/-- `ρ` on `A`, `∞` off `A`. -/
def restrictStop (ρ : Ω → WithTop ℝ≥0) (A : Set Ω) : Ω → WithTop ℝ≥0 :=
  fun ω => if ω ∈ A then ρ ω else ⊤

theorem isStoppingTime_restrictStop {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ) {A : Set Ω}
    (hA : MeasurableSet[hρ.measurableSpace] A) : IsStoppingTime 𝓕 (restrictStop ρ A) := by
  intro i
  have e : {ω | restrictStop ρ A ω ≤ i} = A ∩ {ω | ρ ω ≤ i} := by
    ext ω
    by_cases h : ω ∈ A
    · simp [restrictStop, h]
    · simpa [restrictStop, h] using (WithTop.coe_lt_top i).not_ge
  rw [e]; exact hA.2 i

theorem martingale_integral_eq {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 Q) (t : ℝ≥0) :
    ∫ ω, M t ω ∂Q = ∫ ω, M 0 ω ∂Q := by
  have := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
  simpa using this.symm

theorem integrable_sub_stopped {Φ : ℝ≥0 → Ω → ℝ} (hΦ : HasMartingaleModification Q 𝓕 Φ)
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Φ t ω) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    (t : ℝ≥0) : Integrable (fun ω => Φ t ω - stoppedProcess Φ ρ t ω) Q := by
  obtain ⟨M, hM, hMΦ⟩ := hΦ
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMΦ hc hρ
  exact ((hM.integrable t).congr (hMΦ t)).sub ((hM'.integrable t).congr (hM'X t))

/-- `∫_A (Φ_t - Φ_{t∧ρ}) = 0` for `A ∈ 𝓕_ρ`. -/
theorem setIntegral_sub_stopped_eq_zero {Φ : ℝ≥0 → Ω → ℝ} (hΦ : HasMartingaleModification Q 𝓕 Φ)
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Φ t ω) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    {A : Set Ω} (hA : MeasurableSet[hρ.measurableSpace] A) (t : ℝ≥0) :
    ∫ ω in A, (Φ t ω - stoppedProcess Φ ρ t ω) ∂Q = 0 := by
  obtain ⟨M, hM, hMΦ⟩ := hΦ
  obtain ⟨M', hM', hM'X⟩ :=
    exists_martingale_stoppedProcess hM hMΦ hc (isStoppingTime_restrictStop hρ hA)
  have hAm : MeasurableSet A := hρ.measurableSpace_le A hA
  have e : A.indicator (fun ω => Φ t ω - stoppedProcess Φ ρ t ω) =
      fun ω => Φ t ω - stoppedProcess Φ (restrictStop ρ A) t ω := by
    funext ω
    by_cases h : ω ∈ A
    · simp [h, restrictStop, stoppedProcess_eq_stopTime]
    · simp [h, restrictStop, stoppedProcess_eq_stopTime,
        BlockBand.SourceProcess.Stochastic.Semimartingale.stopTime_top]
  rw [← integral_indicator hAm, e, integral_sub ((hM.integrable t).congr (hMΦ t))
    ((hM'.integrable t).congr (hM'X t)), ← integral_congr_ae (hMΦ t),
    ← integral_congr_ae (hM'X t), martingale_integral_eq hM, martingale_integral_eq hM',
    integral_congr_ae (hMΦ 0), integral_congr_ae (hM'X 0)]
  have h0 : ∀ τ : WithTop ℝ≥0, stopTime τ 0 = 0 := fun τ =>
    le_antisymm (BlockBand.SourceProcess.Stochastic.Semimartingale.stopTime_le τ 0) zero_le
  simp [stoppedProcess_eq_stopTime, h0]

/-- **Optional sampling:** `E[ζ (Φ_t - Φ_{t∧ρ})] = 0` for bounded `𝓕_ρ`-measurable `ζ`. -/
theorem integral_mul_sub_stopped_eq_zero {Φ : ℝ≥0 → Ω → ℝ}
    (hΦ : HasMartingaleModification Q 𝓕 Φ) (hc : ∀ᵐ ω ∂Q, Continuous fun t => Φ t ω)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ) {ζ : Ω → ℝ}
    (hζ : StronglyMeasurable[hρ.measurableSpace] ζ) {C : ℝ} (hζb : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C)
    (t : ℝ≥0) : ∫ ω, ζ ω * (Φ t ω - stoppedProcess Φ ρ t ω) ∂Q = 0 := by
  set g : Ω → ℝ := fun ω => Φ t ω - stoppedProcess Φ ρ t ω
  have hg : Integrable g Q := integrable_sub_stopped hΦ hc hρ t
  have hm := hρ.measurableSpace_le
  have hζg : Integrable (ζ * g) Q := hg.bdd_mul (hζ.mono hm).aestronglyMeasurable hζb
  have h0 : (0 : Ω → ℝ) =ᵐ[Q] Q[g | hρ.measurableSpace] :=
    ae_eq_condExp_of_forall_setIntegral_eq hm hg (fun _ _ _ => integrableOn_zero)
      (fun s hs _ => by simp [setIntegral_sub_stopped_eq_zero hΦ hc hρ hs t, g])
      aestronglyMeasurable_zero
  have h1 := condExp_mul_of_stronglyMeasurable_left hζ hζg hg
  rw [show (fun ω => ζ ω * g ω) = ζ * g from rfl, ← integral_condExp hm, integral_congr_ae h1]
  have : (fun ω => (ζ * Q[g | hρ.measurableSpace]) ω) =ᵐ[Q] fun _ => (0 : ℝ) := by
    filter_upwards [h0] with ω hω
    simp [← hω]
  rw [integral_congr_ae this]; simp

/-- **The stopped-product identity.** For `ρ ≤ T` and `Z^ρ` adapted and bounded,
`K_t = (Φ_t - Φ_{t∧ρ}) Z_{t∧ρ}` has the martingale identity against bounded `𝓕_r` test
functions. -/
theorem integral_mul_stoppedProd {Φ : ℝ≥0 → Ω → ℝ} (hΦ : HasMartingaleModification Q 𝓕 Φ)
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => Φ t ω) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    {T : ℝ≥0} (hρT : ∀ ω, ρ ω ≤ T) {Z : ℝ≥0 → Ω → ℝ}
    (hZ : ∀ t, StronglyMeasurable[𝓕 t] (stoppedProcess Z ρ t)) {C : ℝ}
    (hZb : ∀ᵐ ω ∂Q, ∀ t, ‖stoppedProcess Z ρ t ω‖ ≤ C) {r t : ℝ≥0} (hrt : r ≤ t) {η : Ω → ℝ}
    (hη : StronglyMeasurable[𝓕 r] η) {Cη : ℝ} (hηb : ∀ᵐ ω ∂Q, ‖η ω‖ ≤ Cη) :
    ∫ ω, η ω * ((Φ t ω - stoppedProcess Φ ρ t ω) * stoppedProcess Z ρ t ω) ∂Q =
      ∫ ω, η ω * ((Φ r ω - stoppedProcess Φ ρ r ω) * stoppedProcess Z ρ r ω) ∂Q := by
  set ξ : Ω → ℝ := fun ω => Z (ρ ω).untopA ω
  have hρr : IsStoppingTime 𝓕 fun ω => max (ρ ω) r := hρ.max_const r
  -- measurability of `ξ` for `𝓕_ρ`
  have hξ : StronglyMeasurable[hρ.measurableSpace] ξ := by
    have hset : ∀ i : ℝ≥0, ∀ B : Set ℝ, ξ ⁻¹' B ∩ {ω | ρ ω ≤ i} =
        (stoppedProcess Z ρ i) ⁻¹' B ∩ {ω | ρ ω ≤ i} := fun i B => by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, stoppedProcess_eq_stopTime, ξ]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [stopTime_of_ge h2], h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by rwa [stopTime_of_ge h2] at h1, h2⟩
    have hmeas : Measurable[hρ.measurableSpace] ξ := by
      intro B hB
      have hi : ∀ i : ℝ≥0, MeasurableSet[𝓕 i] (ξ ⁻¹' B ∩ {ω | ρ ω ≤ i}) := fun i => by
        rw [hset]; exact ((hZ i).measurable hB).inter (hρ i)
      refine ⟨?_, hi⟩
      have e : ξ ⁻¹' B = ξ ⁻¹' B ∩ {ω | ρ ω ≤ T} := by
        ext ω; exact ⟨fun h => ⟨h, hρT ω⟩, fun h => h.1⟩
      rw [e]
      exact (le_iSup (fun t => 𝓕 t) T) _ (hi T)
    exact hmeas.stronglyMeasurable
  -- the increment
  have hinc : ∀ ω, (Φ t ω - stoppedProcess Φ ρ t ω) * stoppedProcess Z ρ t ω -
      (Φ r ω - stoppedProcess Φ ρ r ω) * stoppedProcess Z ρ r ω =
      ξ ω * (Φ t ω - stoppedProcess Φ (fun ω => max (ρ ω) r) t ω) := by
    intro ω
    simp only [stoppedProcess_eq_stopTime, ξ]
    rcases le_or_gt (ρ ω) r with h | h
    · have h' : ρ ω ≤ t := h.trans (WithTop.coe_le_coe.2 hrt)
      rw [stopTime_of_ge h, stopTime_of_ge h', max_eq_right h,
        stopTime_of_ge (WithTop.coe_le_coe.2 hrt), WithTop.untopA_eq_untop WithTop.coe_ne_top,
        WithTop.untop_coe]
      ring
    · rw [stopTime_of_le' h.le, max_eq_left h.le]
      rcases le_or_gt (ρ ω) t with h2 | h2
      · rw [stopTime_of_ge h2]; ring
      · rw [stopTime_of_le' h2.le]; ring
  have hle1 : (isStoppingTime_const 𝓕 r).measurableSpace ≤ hρr.measurableSpace :=
    (isStoppingTime_const 𝓕 r).measurableSpace_mono hρr fun ω => le_max_right _ _
  have hle2 : hρ.measurableSpace ≤ hρr.measurableSpace :=
    hρ.measurableSpace_mono hρr fun ω => le_max_left _ _
  have hηr : StronglyMeasurable[hρr.measurableSpace] η := by
    rw [← IsStoppingTime.measurableSpace_const 𝓕 r] at hη; exact hη.mono hle1
  have hZb' : ∀ᵐ ω ∂Q, ‖ξ ω‖ ≤ C := by
    filter_upwards [hZb] with ω hω
    have := hω T
    rwa [stoppedProcess_eq_stopTime, stopTime_of_ge (hρT ω)] at this
  have hK : ∀ s : ℝ≥0, Integrable (fun ω => η ω *
      ((Φ s ω - stoppedProcess Φ ρ s ω) * stoppedProcess Z ρ s ω)) Q := fun s => by
    have h1 := (integrable_sub_stopped hΦ hc hρ s).bdd_mul
      ((hZ s).mono (𝓕.le s)).aestronglyMeasurable (by filter_upwards [hZb] with ω hω using hω s)
    have h2 := h1.bdd_mul (hη.mono (𝓕.le r)).aestronglyMeasurable hηb
    refine h2.congr (ae_of_all _ fun ω => ?_)
    simp only; ring
  rw [← sub_eq_zero, ← integral_sub (hK t) (hK r)]
  have e : (fun ω => η ω * ((Φ t ω - stoppedProcess Φ ρ t ω) * stoppedProcess Z ρ t ω) -
      η ω * ((Φ r ω - stoppedProcess Φ ρ r ω) * stoppedProcess Z ρ r ω)) =
      fun ω => (η ω * ξ ω) * (Φ t ω - stoppedProcess Φ (fun ω => max (ρ ω) r) t ω) := by
    funext ω; rw [← mul_sub, hinc ω]; ring
  rw [e]
  refine integral_mul_sub_stopped_eq_zero hΦ hc hρr (hηr.mul (hξ.mono hle2)) (C := Cη * C) ?_ t
  filter_upwards [hηb, hZb'] with ω h1 h2
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
