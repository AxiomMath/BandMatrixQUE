module

public import BlockBand.Transmission.DualLift.LLyap
public import BlockBand.Transmission.Dual.ExistsBoundary

/-!
# The boundary estimates along the lift

The estimates behind the corner limit at `p = 1` (as in `ExistsBoundary`), at boundary starts
and random starts. `Sp n t = S(Yf n t)`, `hitS n ε` the first time `Sp n ≤ ε`. All statements
are restricted to an event `A ∈ L𝓖 μ 0` on which the start is controlled (take `A = univ` for a
deterministic start); this covers unbounded random starts.
* `L₁_tot_U`: `L₁ S = 0` on `flatU`.
* `integral_Sp_stop` (optional stopping): `∫_A S(Yf n (T ∧ σ)) = ∫_A S(π ξ)` if `S(π ξ) ≤ B` on
  `A`.
* `measure_noHit_le` (**estimate A**, Lyapunov `g`): for `n > max 1 (1/ε)`,
  `e^{−(D₀/2)T} ε log(1+n²) · P(A ∩ good ∩ {e_n < hitS n ε, e_n < T}) ≤ B` if `g(π ξ) ≤ B` on
  `A`.

Estimate B, `P(A ∩ {hitS n ε < T, S ≥ a at some s ∈ [hitS, T]}) ≤ ε/a`, is proved in the sibling
module (`LiftFamily.measure_upcross_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

/-- **`𝒟₁ S = 0`** on `flatU`. -/
theorem L₁_tot_U (D0 : ℝ) {y : Fin 2 → ℝ} (hy : y ∈ flatU) : L₁ D0 tot y = 0 := by
  have hd : ∀ w, fderiv ℝ tot w = totCLM := fun w => totCLM.fderiv
  have hdd : fderiv ℝ (fderiv ℝ tot) y = 0 := by
    rw [show fderiv ℝ tot = fun _ => totCLM from funext hd]; exact fderiv_const_apply _
  rw [L₁_eq, hd, hdd, flatDrift_one_zero, flatDrift_one_one]
  have hs : y 0 + y 1 ≠ 0 := hy.1.ne'
  have htot : ∀ v : Fin 2 → ℝ, totCLM v = v 0 + v 1 := fun v => rfl
  simp only [htot, Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  have h00 : ∀ u v : Fin 2 → ℝ, (0 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ) u v = 0 :=
    fun _ _ => rfl
  rw [h00, h00]
  field_simp
  ring

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ}

namespace LiftFamily

variable (F : LiftFamily μ D0 ξ)

/-- `S` along the `n`-th flat path. -/
def Sp (n : ℕ) (t : ℝ≥0) (ω : LΩ S) : ℝ := tot (F.Yf n t ω)

theorem continuous_Sp (n : ℕ) (ω : LΩ S) : Continuous fun t => F.Sp n t ω :=
  contDiff_tot.continuous.comp (F.continuous_Yf n ω)

theorem measurable_Sp (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) (t : ℝ≥0) :
    Measurable[L𝓖 μ t] (F.Sp n t) :=
  contDiff_tot.continuous.measurable.comp (F.measurable_Yf hD0 hξ n t)

theorem Sp_pos (hξ : IsLiftStart μ ξ) (n : ℕ) (t : ℝ≥0) (ω : LΩ S) : 0 < F.Sp n t ω :=
  (F.Yf_mem_strip hξ n t ω).2.2.2

/-- The first time `S ≤ ε` along the `n`-th path. -/
def hitS (n : ℕ) (ε : ℝ) : LΩ S → WithTop ℝ≥0 := hitLe (F.Sp n) ε

theorem isStoppingTime_hitS (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) (ε : ℝ) :
    IsStoppingTime (L𝓖 μ) (F.hitS n ε) :=
  isStoppingTime_hitLe (F.measurable_Sp hD0 hξ n)
    (fun ω t => SolFamily.tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω) t)
    (fun ω => (F.continuous_Sp n ω).lowerSemicontinuous) ε

omit [IsProbabilityMeasure μ] in
theorem measurable_tot_start (hξ : IsLiftStart μ ξ) :
    Measurable fun ω => tot (liftProj (ξ ω)) :=
  (contDiff_tot.continuous.comp contDiff_liftProj.continuous).measurable.comp
    (hξ.meas.mono ((L𝓖 μ).le 0)).measurable

/-- **Optional stopping for `S`**, on a `𝓖₀`-event. -/
theorem integral_Sp_stop (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ)
    {σ : LΩ S → WithTop ℝ≥0} (hσ : IsStoppingTime (L𝓖 μ) σ) (T : ℝ≥0) {A : Set (LΩ S)}
    (hA : MeasurableSet[L𝓖 μ 0] A) {B : ℝ} (hB : ∀ ω ∈ A, tot (liftProj (ξ ω)) ≤ B) :
    IntegrableOn (fun ω => F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω) A (LP μ) ∧
      ∫ ω in A, F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω ∂LP μ =
        ∫ ω in A, tot (liftProj (ξ ω)) ∂LP μ := by
  have hAm : MeasurableSet A := (L𝓖 μ).le 0 _ hA
  obtain ⟨M, hM, hMX⟩ := F.hasMart_G hD0 hξ n measurable_tot (contDiff_tot.contDiffOn.of_le
    (by simp)) ((continuous_const (y := (0 : ℝ))).continuousOn.congr fun y hy =>
      L₁_tot_U D0 hy)
  have hX : (fun (t : ℝ≥0) (ω : LΩ S) => tot (F.Yf n t ω) - tot (F.Yf n 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t ω => L₁ D0 tot (F.Yf n t ω)) s.toNNReal ω) =
      fun t ω => F.Sp n t ω - tot (liftProj (ξ ω)) := by
    funext t ω
    have h0 : ∀ s : ℝ, switchOff (F.e n) (fun t ω => L₁ D0 tot (F.Yf n t ω)) s.toNNReal ω = 0 :=
      fun s => by unfold switchOff; split_ifs <;> simp [L₁_tot_U D0 (F.Yf_mem_flatU hξ n _ ω)]
    simp only [h0, integral_zero, sub_zero, F.Yf_zero, Sp]
  rw [hX] at hMX
  obtain ⟨M', hM', hM'e⟩ := Semimartingale.exists_martingale_stoppedProcess hM hMX
    (Eventually.of_forall fun ω => (F.continuous_Sp n ω).sub continuous_const) hσ
  have hT := hM'e T
  have h0 := hM'e 0
  have hstop : ∀ ω, stoppedProcess (fun t ω => F.Sp n t ω - tot (liftProj (ξ ω))) σ T ω =
      F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω - tot (liftProj (ξ ω)) := fun ω => rfl
  have hint : Integrable (fun ω => F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω -
      tot (liftProj (ξ ω))) (LP μ) :=
    (hM'.integrable T).congr (hT.trans (Eventually.of_forall hstop))
  have htotA : IntegrableOn (fun ω => tot (liftProj (ξ ω))) A (LP μ) := by
    refine Measure.integrableOn_of_bounded (M := max B 0) (measure_ne_top _ _)
      (measurable_tot_start hξ).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hAm).2 (Eventually.of_forall fun ω hω => ?_)
    have hpos : 0 < tot (liftProj (ξ ω)) := lS_pos (hξ.mem ω)
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact (hB ω hω).trans (le_max_left _ _)
  have hint' : IntegrableOn (fun ω => F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω) A (LP μ) :=
    (hint.integrableOn.add htotA).congr_fun (fun ω _ => by simp) hAm
  refine ⟨hint', ?_⟩
  have e1 : ∫ ω in A, M' 0 ω ∂LP μ = ∫ ω in A, M' T ω ∂LP μ :=
    hM'.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) hA
  have e2 : ∫ ω in A, M' 0 ω ∂LP μ = 0 := by
    rw [setIntegral_congr_ae hAm (h0.mono fun ω hω _ => hω)]
    have : ∀ ω, stoppedProcess (fun t ω => F.Sp n t ω - tot (liftProj (ξ ω))) σ 0 ω = 0 :=
      fun ω => by
        simp only [stoppedProcess, Sp]
        rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]
        simp [F.Yf_zero]
    simp only [this, integral_zero]
  rw [setIntegral_congr_ae hAm (hT.mono fun ω hω _ => hω)] at e1
  have e3 : ∫ ω in A, (F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω -
      tot (liftProj (ξ ω))) ∂LP μ = 0 := by
    rw [← e2, e1]; rfl
  rw [integral_sub hint' htotA] at e3
  linarith

/-- **Estimate A**: the Lyapunov bound before the first visit to `{S ≤ ε}`. -/
theorem measure_noHit_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hn1 : 1 < (n : ℝ)) (hnε : 1 / ε < n) (T : ℝ≥0) {A : Set (LΩ S)}
    (hA : MeasurableSet[L𝓖 μ 0] A) {B : ℝ} (hB : ∀ ω ∈ A, liftLyap (liftProj (ξ ω)) ≤ B) :
    ENNReal.ofReal (exp (-(D0 / 2) * T) * (ε * Real.log (1 + n * n))) *
      LP μ (A ∩ F.good ∩ {ω | F.e n ω < F.hitS n ε ω ∧ F.e n ω < T}) ≤ ENNReal.ofReal B := by
  have hAm : MeasurableSet A := (L𝓖 μ).le 0 _ hA
  obtain ⟨hm, hle⟩ := F.lintegral_discount_le hD0 hξ n measurable_liftLyap contDiffOn_liftLyap
    (fun _ hy => liftLyap_nonneg hy) (by positivity : 0 ≤ D0 / 2)
    (fun _ hy => L₁_liftLyap_le hD0.le hy) (F.isStoppingTime_hitS hD0 hξ n ε) T hA hB
  have hB' : ∫⁻ ω in A, ENNReal.ofReal (liftLyap (liftProj (ξ ω))) ∂LP μ ≤ ENNReal.ofReal B := by
    calc _ ≤ ∫⁻ _ in A, ENNReal.ofReal B ∂LP μ :=
          setLIntegral_mono' hAm fun ω hω => ENNReal.ofReal_le_ofReal (hB ω hω)
      _ = ENNReal.ofReal B * LP μ A := by simp
      _ ≤ ENNReal.ofReal B * 1 := by gcongr; exact prob_le_one
      _ = ENNReal.ofReal B := mul_one _
  set b := exp (-(D0 / 2) * T) * (ε * Real.log (1 + n * n))
  have hMk := mul_meas_ge_le_lintegral₀ (μ := (LP μ).restrict A)
    hm.ennreal_ofReal.aemeasurable (ENNReal.ofReal b)
  refine le_trans ?_ ((hMk.trans hle).trans hB')
  refine mul_le_mul_right ?_ _
  rw [Measure.restrict_apply' hAm]
  refine measure_mono fun ω hω => ⟨?_, hω.1.1⟩
  obtain ⟨⟨-, hω⟩, h1, h2⟩ := hω
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
  have hmT : m ≤ T := by rw [← hm] at h2; exact (WithTop.coe_lt_coe.1 h2).le
  have hle' : (m : WithTop ℝ≥0) ≤ min (T : WithTop ℝ≥0) (F.hitS n ε ω) :=
    le_min (WithTop.coe_le_coe.2 hmT) (hm ▸ h1.le)
  obtain ⟨s, hs'⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left (T : WithTop ℝ≥0) (F.hitS n ε ω)))
  have hs := hs'.symm
  have hsT : s ≤ T := by
    have := min_le_left (T : WithTop ℝ≥0) (F.hitS n ε ω); rw [hs] at this
    exact WithTop.coe_le_coe.1 this
  have hms : m ≤ s := by rw [hs] at hle'; exact WithTop.coe_le_coe.1 hle'
  show ENNReal.ofReal b ≤ ENNReal.ofReal _
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hs]
  show b ≤ exp (-(D0 / 2) * (s : ℝ)) * liftLyap (F.Yf n s ω)
  have hY : F.Yf n s ω = liftProj (F.X n m ω) := by
    rw [F.Yf_of_good hω, Zp, F.X_eq_of_e_le n hm.symm hms]
  have hnorm : (n : ℝ) ≤ ‖F.X n m ω‖ := le_norm_exitTimeOf (F.continuous_X n ω) hm.symm
  have hS : ε ≤ lS (F.X n m ω) := by
    have := (lt_hitLe (V := F.Sp n) (hm ▸ h1)).le
    rwa [Sp, F.Yf_of_good hω] at this
  have hg := liftLyap_ge_of_norm ((F.good_spec hω).1 n m) hε0 hn1 hnε hnorm hS
  rw [hY]
  have he : exp (-(D0 / 2) * T) ≤ exp (-(D0 / 2) * (s : ℝ)) :=
    exp_le_exp.2 (by nlinarith [NNReal.coe_le_coe.2 hsT])
  have hl0 : 0 ≤ Real.log (1 + n * n) := Real.log_nonneg (by nlinarith)
  exact mul_le_mul he hg (by positivity) (exp_pos _).le

end LiftFamily

end BlockBand.Transmission.DualLift
