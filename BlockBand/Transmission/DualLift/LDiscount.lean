module

public import BlockBand.Transmission.DualLift.LMart

/-!
# The discounted supermartingale bound along the lift

Setting: `(LΩ S, L𝓖 μ, LP μ)`, `D₀ > 0`, `IsLiftStart μ ξ`, a `LiftFamily μ D₀ ξ`. If `G` is
measurable, `C²` on `flatU`, `G ≥ 0` and `L₁G ≤ cG` on `flatStrip` (`c ≥ 0`), then for every
`L𝓖 μ`-stopping time `θ`, `T`, and `A ∈ L𝓖 μ 0` on which `G(π ξ) ≤ B`:
`∫_A e^{−c(T∧θ)} G(Yf n (T∧θ)) dP ≤ ∫_A G(π ξ) dP` (`lintegral_discount_le`); Markov form
`measure_discount_le` for a start with `G(π ξ) ≤ B` everywhere.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
  BlockBand.Transmission.Dual.Exists.SolFamily
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- **Discounted supermartingale bound** at a stopping time, on an `𝓖₀`-event. -/
theorem lintegral_discount_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ)
    {G : (Fin 2 → ℝ) → ℝ} (hGm : Measurable G) (hG : ContDiffOn ℝ 2 G flatU)
    (hG0 : ∀ y ∈ flatStrip, 0 ≤ G y) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y ∈ flatStrip, L₁ D0 G y ≤ c * G y) {θ : LΩ S → WithTop ℝ≥0}
    (hθ : IsStoppingTime (L𝓖 μ) θ) (T : ℝ≥0) {A : Set (LΩ S)} (hA : MeasurableSet[L𝓖 μ 0] A)
    {B : ℝ} (hB : ∀ ω ∈ A, G (liftProj (ξ ω)) ≤ B) :
    Measurable (fun ω => exp (-c * (min (T : WithTop ℝ≥0) (θ ω)).untopA) *
      G (F.Yf n (min (T : WithTop ℝ≥0) (θ ω)).untopA ω)) ∧
    ∫⁻ ω in A, ENNReal.ofReal (exp (-c * (min (T : WithTop ℝ≥0) (θ ω)).untopA) *
      G (F.Yf n (min (T : WithTop ℝ≥0) (θ ω)).untopA ω)) ∂LP μ ≤
      ∫⁻ ω in A, ENNReal.ofReal (G (liftProj (ξ ω))) ∂LP μ := by
  have H1 := F.isCSM_G hD0 hξ n hGm hG
  have H2 := SemimartingaleIto.semimartingaleItoFormula_holds 1 (LΩ S) (LP μ) (L𝓖 μ) _ _ _ H1
    univ isOpen_univ (Eventually.of_forall fun _ _ => mem_univ _) (discount c)
    ((contDiff_lyapFun _ c contDiff_shift1).continuous.measurable)
    (contDiff_lyapFun _ c contDiff_shift1).contDiffOn
  have H3 := Semimartingale.stoppedSemimartingale_holds 1 (LΩ S) (LP μ) (L𝓖 μ) _ _ _ H2 θ hθ
  have hβ : ∀ᵐ ω ∂LP μ, ∀ s : ℝ≥0, switchAfter θ (fun t ω (_ : Fin 1) => itoDrift (discount c)
      (fun _ => G (F.Yf n t ω)) t (fun _ => switchOff (F.e n)
        (fun t ω => L₁ D0 G (F.Yf n t ω)) t ω) (Matrix.of fun (_ _ : Fin 1) =>
          itoBracket (fun q : ℝ × (Fin 2 → ℝ) => G q.2) (F.Yf n t ω) t
            (switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω))) s ω 0 ≤ 0 := by
    refine Eventually.of_forall fun ω s => ?_
    unfold switchAfter
    split_ifs
    · dsimp only
      rw [itoDrift_discount]
      refine mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le ?_
      have hy := F.Yf_mem_strip hξ n s ω
      unfold switchOff
      split_ifs
      · nlinarith [hc _ hy, hG0 _ hy]
      · nlinarith [hG0 _ hy]
    · exact le_rfl
  have hZ : ∀ᵐ ω ∂LP μ, ∀ t, 0 ≤ stoppedProcess (fun (t : ℝ≥0) (ω : LΩ S) (_ : Fin 1) =>
      discount c ((t : ℝ), fun _ => G (F.Yf n t ω))) θ t ω 0 := by
    refine Eventually.of_forall fun ω t => ?_
    simp only [stoppedProcess, discount_apply]
    exact mul_nonneg (exp_pos _).le (hG0 _ (F.Yf_mem_strip hξ n _ ω))
  have h0 : ∀ ω, (min ((0 : ℝ≥0) : WithTop ℝ≥0) (θ ω)).untopA = 0 := fun ω => by
    rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]; rfl
  have h := lintegral_le_of_nonpos_drift H3 hβ hZ hA (B := B) (fun ω hω => by
      simp only [stoppedProcess, discount_apply, h0, F.Yf_zero, NNReal.coe_zero, mul_zero,
        exp_zero, one_mul]
      exact hB ω hω) T
  have hm : Measurable fun ω => stoppedProcess (fun (t : ℝ≥0) (ω : LΩ S) (_ : Fin 1) =>
      discount c ((t : ℝ), fun _ => G (F.Yf n t ω))) θ T ω 0 :=
    (measurable_pi_apply 0).comp (((H3.adapted T).mono ((L𝓖 μ).le T)).measurable)
  simp only [stoppedProcess, discount_apply] at hm
  refine ⟨hm, ?_⟩
  simp only [stoppedProcess, discount_apply] at h
  refine h.trans (le_of_eq ?_)
  simp only [h0, F.Yf_zero, NNReal.coe_zero, mul_zero, exp_zero, one_mul]

/-- **Markov form of the discounted bound** (start with `G(π ξ) ≤ B` everywhere). -/
theorem measure_discount_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ)
    {G : (Fin 2 → ℝ) → ℝ} (hGm : Measurable G) (hG : ContDiffOn ℝ 2 G flatU)
    (hG0 : ∀ y ∈ flatStrip, 0 ≤ G y) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ y ∈ flatStrip, L₁ D0 G y ≤ c * G y) {θ : LΩ S → WithTop ℝ≥0}
    (hθ : IsStoppingTime (L𝓖 μ) θ) (T : ℝ≥0) {B : ℝ} (hB : ∀ ω, G (liftProj (ξ ω)) ≤ B)
    (A : Set (LΩ S)) (b : ℝ)
    (hA : ∀ ω ∈ A, b ≤ exp (-c * (min (T : WithTop ℝ≥0) (θ ω)).untopA) *
      G (F.Yf n (min (T : WithTop ℝ≥0) (θ ω)).untopA ω)) :
    ENNReal.ofReal b * LP μ A ≤ ENNReal.ofReal B := by
  obtain ⟨hm, hle⟩ := F.lintegral_discount_le hD0 hξ n hGm hG hG0 hc0 hc hθ T
    MeasurableSet.univ (B := B) fun ω _ => hB ω
  rw [Measure.restrict_univ] at hle
  have hB' : ∫⁻ ω, ENNReal.ofReal (G (liftProj (ξ ω))) ∂LP μ ≤ ENNReal.ofReal B := by
    calc _ ≤ ∫⁻ _, ENNReal.ofReal B ∂LP μ := lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hB ω)
      _ = ENNReal.ofReal B := by simp
  refine le_trans ?_ (((mul_meas_ge_le_lintegral₀ hm.ennreal_ofReal.aemeasurable
    (ENNReal.ofReal b)).trans hle).trans hB')
  exact mul_le_mul_right (measure_mono fun ω hω => ENNReal.ofReal_le_ofReal (hA ω hω)) _

end LiftFamily

end BlockBand.Transmission.DualLift
