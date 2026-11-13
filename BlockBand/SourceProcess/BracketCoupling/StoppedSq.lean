module

public import BlockBand.SourceProcess.RankFree.MeanBounds
public import BlockBand.SourceProcess.RankFree.LocMartBound

/-!
# Stopped mean-square bound for zero-drift Itô processes

* `locMart_affine`: the deterministic process `a - M t` is a `LocMart` with drift `-M`.
* `isNative_sub`: the difference of two zero-drift Itô processes is one, with diffusion
  `σ₁ - σ₂`.
* `lintegral_hsSq_stopped_le`: if `Y` is a zero-drift Itô process and `ρ` an augmented
  stopping time with `∑_a ‖σ_a(s)‖²_HS ≤ M` for `0 < s ≤ ρ` (a.s.), then
  `E ‖Y_{t∧ρ} - Y_0‖²_HS ≤ M t` (lower integral; any real `M`).
  Route: `‖Y - Y_0‖²` is a `LocMart` with drift `∑_a ‖σ_a‖²` (RankFree's `locMart_disc` at rate `0`,
  `sdeGenerator_normSq`); add `M t - M s` and stop at `ρ ∧ t`: the result is nonnegative with
  nonpositive drift, so `LocMart.lintegral_le` bounds its mean by its initial value `M t`.
  No Itô isometry for stopped integrals is needed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BracketCoupling
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.RankFree
open scoped NNReal ENNReal

section Affine

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The deterministic process `a - M t` is a `LocMart` with drift `-M`. -/
theorem locMart_affine (a M : ℝ) :
    LocMart Q 𝓖 (fun (t : ℝ≥0) (_ : Ω) => a - M * t) (fun _ _ => -M) := by
  refine ⟨fun i => ?_, ae_of_all _ fun _ => by fun_prop, ae_of_all _ fun _ _ => ?_,
    fun _ _ => ⊤, fun _ => isStoppingTime_top_const, ae_of_all _ fun _ => tendsto_const_nhds,
    fun _ => ⟨0, martingale_zero ℝ 𝓖 Q, fun t => ae_of_all _ fun ω => ?_⟩⟩
  · have hc : Continuous fun p : Set.Iic i => a - M * ((p : ℝ≥0) : ℝ) := by fun_prop
    exact hc.stronglyMeasurable.comp_measurable measurable_fst
  · exact integrableOn_const (by simp)
  · simp [locComp, stoppedProcess_eq_stopTime, stopTime_top]
    ring

end Affine

section Native

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]

omit [MeasurableSpace S] [Fintype κ] in
theorem stopTime_min_self (r : WithTop ℝ≥0) (t : ℝ≥0) :
    stopTime (min r (t : WithTop ℝ≥0)) t = stopTime r t := by
  unfold stopTime
  rw [min_comm r, ← min_assoc, min_self]

/-- The difference of two zero-drift Itô processes. -/
theorem isNative_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Y₁ Y₂ : ℝ≥0 → DriverSample S κ → E}
    {σ₁ σ₂ : κ → ℝ≥0 → DriverSample S κ → E}
    (h₁ : IsNativeItoProcess μ Y₁ (fun _ _ => 0) σ₁)
    (h₂ : IsNativeItoProcess μ Y₂ (fun _ _ => 0) σ₂) :
    IsNativeItoProcess μ (fun t x => Y₁ t x - Y₂ t x) (fun _ _ => 0)
      (fun a t x => σ₁ a t x - σ₂ a t x) := by
  have h := (h₁.prod h₂).map_clm
    (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)
  convert h using 1
  · funext t x; simp
  · funext t x; simp
  · funext a t x; simp

variable {m n : Type*} [Fintype m] [Fintype n]

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

theorem hsSq_nonneg' (V : Matrix m n ℂ) : 0 ≤ hsSq V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Stopped mean-square bound.** For a zero-drift Itô process `Y` and a stopping time `ρ`
before which `∑_a ‖σ_a‖²_HS ≤ M`, `E ‖Y_{t∧ρ} - Y_0‖²_HS ≤ M t`. -/
theorem lintegral_hsSq_stopped_le {Y : ℝ≥0 → DriverSample S κ → Matrix m n ℂ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Matrix m n ℂ}
    (hY : IsNativeItoProcess μ Y (fun _ _ => 0) σ) {ρ : DriverSample S κ → WithTop ℝ≥0}
    (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ) {M : ℝ}
    (hb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ∑ a, hsSq (σ a s x) ≤ M) (t : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (hsSq (stoppedProcess Y ρ t x - Y 0 x)) ∂driverLaw (κ := κ) μ ≤
      ENNReal.ofReal (M * t) := by
  set Q := driverLaw (κ := κ) μ
  set 𝓖 := driverAugmented (κ := κ) μ
  by_cases hM : M < 0
  · have h0 : ∀ᵐ x ∂Q, hsSq (stoppedProcess Y ρ t x - Y 0 x) = 0 := by
      filter_upwards [hb] with x hx
      have hρ0 : ρ x = 0 := by
        by_contra hne
        obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ≥0, 0 < s ∧ (s : WithTop ℝ≥0) ≤ ρ x := by
          by_cases ht : ρ x = ⊤
          · exact ⟨1, one_pos, ht ▸ le_top⟩
          · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
            refine ⟨r, pos_iff_ne_zero.2 fun h0 => hne ?_, hr.le⟩
            rw [← hr, h0, WithTop.coe_zero]
        exact absurd (hx s hs0 hs) (not_le.2 (hM.trans_le
          (Finset.sum_nonneg fun a _ => hsSq_nonneg' _)))
      rw [stoppedProcess_eq_stopTime, hρ0]
      have : stopTime (0 : WithTop ℝ≥0) t = 0 := by
        rw [← WithTop.coe_zero, stopTime_coe, min_eq_right zero_le]
      rw [this, sub_self, hsSq_eq, norm_zero]
      norm_num
    rw [lintegral_congr_ae (h0.mono fun x hx => by rw [hx])]
    simp
  rw [not_lt] at hM
  have hC : StronglyMeasurable[𝓖 0] (fun x => -Y 0 x) := (hY.adapted 0).neg
  have hZ := (hY.add_const hC).locMart_disc (contDiff_normSq (ι := m) (c := n) (k := 2)) 0
  have hZ' : LocMart Q 𝓖 (fun t x => ‖Y t x - Y 0 x‖ ^ 2) (fun s x => ∑ a, ‖σ a s x‖ ^ 2) := by
    convert hZ using 1
    · funext t x; simp [sub_eq_add_neg]
    · funext s x
      simp [sdeGenerator_normSq, reInner_self]
  have hρ' : IsStoppingTime 𝓖 (fun x => min (ρ x) (t : WithTop ℝ≥0)) :=
    hρ.min (isStoppingTime_const 𝓖 t)
  have hW := (hZ'.add (locMart_affine (Q := Q) (𝓖 := 𝓖) (M * t) M)).stop hρ'
  have hle : ∀ x (s : ℝ≥0), stopTime (min (ρ x) (t : WithTop ℝ≥0)) s ≤ t := fun x s =>
    WithTop.coe_le_coe.1 ((stopTime_le_self _ s).trans (min_le_right _ _))
  have hnn : ∀ᵐ x ∂Q, ∀ s, 0 ≤ stoppedProcess (fun r x => ‖Y r x - Y 0 x‖ ^ 2 +
      (M * t - M * r)) (fun x => min (ρ x) (t : WithTop ℝ≥0)) s x := by
    refine ae_of_all _ fun x s => ?_
    rw [stoppedProcess_eq_stopTime]
    have h1 : ((stopTime (min (ρ x) (t : WithTop ℝ≥0)) s : ℝ≥0) : ℝ) ≤ t := hle x s
    have h2 : 0 ≤ M * t - M * (stopTime (min (ρ x) (t : WithTop ℝ≥0)) s : ℝ) := by
      nlinarith
    positivity
  have hβ : ∀ᵐ x ∂Q, ∀ s : ℝ≥0, ∫ r in Ioc (0 : ℝ) s, switchAfter
      (fun x => min (ρ x) (t : WithTop ℝ≥0)) (fun s x => ∑ a, ‖σ a s x‖ ^ 2 + -M)
        r.toNNReal x ≤ 0 := by
    filter_upwards [hb] with x hx s
    refine setIntegral_nonpos measurableSet_Ioc fun r hr => ?_
    simp only [switchAfter]
    split_ifs with h
    · have := hx r.toNNReal (Real.toNNReal_pos.2 hr.1) (h.trans (min_le_left _ _))
      simp only [hsSq_eq] at this
      linarith
    · exact le_rfl
  have hmain := hW.lintegral_le hnn hβ (hW.prog.stronglyAdapted 0) t
  have hz : ∀ x, stoppedProcess (fun r x => ‖Y r x - Y 0 x‖ ^ 2 +
      (M * t - M * r)) (fun x => min (ρ x) (t : WithTop ℝ≥0)) 0 x = M * t := fun x => by
    rw [stoppedProcess_eq_stopTime, le_antisymm (stopTime_le _ 0) zero_le]
    simp
  simp only [hz, lintegral_const, measure_univ, mul_one] at hmain
  refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hmain
  rw [stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, stopTime_min_self, hsSq_eq]
  have h1 : ((stopTime (ρ x) t : ℝ≥0) : ℝ) ≤ t := stopTime_le _ t
  have h2 : 0 ≤ M * t - M * (stopTime (ρ x) t : ℝ) := by nlinarith
  linarith

end Native

end BlockBand.SourceProcess.BracketCoupling
