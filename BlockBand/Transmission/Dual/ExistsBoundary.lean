module

public import BlockBand.Transmission.Dual.ExistsLyapGen
public import BlockBand.Transmission.Dual.Hitting
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain

/-!
# `exists_` at `p = 1`: the two boundary estimates

Measure `P₁`, filtration `𝓖₁`, a `SolFamily D₀ z` with `z ∈ 𝒞₁`, `D₀ > 0`;
`Sp n t = S(Yf n t)` with `S = x + y`; `hitS n ε` is the first time `Sp n ≤ ε`.

* `integral_Sp_stop` (optional stopping for the bounded martingale `S`):
  `E[Sp n (T ∧ σ)] = S(z)` for every `𝓖₁`-stopping time `σ`.
* `measure_noHit_le` (**estimate A**, the Lyapunov function `g`):
  `e^{−D₀T} ε n · P(e_n < hitS n ε, e_n < T) ≤ g(z)` for `0 < ε ≤ 1`. Before `hitS n ε` the path
  has `S > ε`, and at the exit time `‖X_n‖ ≥ n`, where `g ≥ ε n` (`lyapG_toFlat_ge`).
* `measure_upcross_le` (**estimate B**, no return from `{S ≤ ε}` to `{S ≥ a}`):
  `P(hitS n ε < T, ∃ s ≤ T, hitS n ε ≤ s, a ≤ Sp n s) ≤ ε/a` for `0 < ε`, `0 < a`.
No continuous-time martingale convergence is needed: the corner limit at `p = 1` uses only that
`S` gets below every `ε` before the explosion (A) and does not come back to `a` afterwards (B).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.NativeSDE
open scoped NNReal ENNReal

variable {D0 : ℝ} {z : Fin 2 → ℝ}

namespace SolFamily

variable (F : SolFamily D0 z)

/-- `S` along the `n`-th path. -/
def Sp (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : ℝ := tot (F.Yf n t ω)

theorem continuous_Sp (n : ℕ) (ω : Ω₁) : Continuous fun t => F.Sp n t ω :=
  contDiff_tot.continuous.comp (F.continuous_Yf n ω)

theorem measurable_Yf (n : ℕ) (t : ℝ≥0) : Measurable[𝓖₁ t] (F.Yf n t) :=
  contDiff_toFlat.continuous.measurable.comp ((F.strong n).sol.1.adapted t).measurable

theorem measurable_Sp (n : ℕ) (t : ℝ≥0) : Measurable[𝓖₁ t] (F.Sp n t) :=
  contDiff_tot.continuous.measurable.comp (F.measurable_Yf n t)

theorem Sp_pos (n : ℕ) (t : ℝ≥0) (ω : Ω₁) : 0 < F.Sp n t ω := tot_pos (F.Yf_mem n t ω)

theorem tendsto_nhdsGE_of_continuous {V : ℝ≥0 → ℝ} (hV : Continuous V) (t : ℝ≥0) :
    Tendsto V (𝓝[≥] t) (𝓝 (V t)) :=
  hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- The first time `S ≤ ε` along the `n`-th path. -/
def hitS (n : ℕ) (ε : ℝ) : Ω₁ → WithTop ℝ≥0 := hitLe (F.Sp n) ε

theorem isStoppingTime_hitS (n : ℕ) (ε : ℝ) : IsStoppingTime 𝓖₁ (F.hitS n ε) :=
  isStoppingTime_hitLe (F.measurable_Sp n)
    (fun ω t => tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω) t)
    (fun ω => (F.continuous_Sp n ω).lowerSemicontinuous) ε

/-- **Optional stopping for `S`.** -/
theorem integral_Sp_stop (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (n : ℕ)
    {σ : Ω₁ → WithTop ℝ≥0} (hσ : IsStoppingTime 𝓖₁ σ) (T : ℝ≥0) :
    Integrable (fun ω => F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω) P₁ ∧
      ∫ ω, F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω ∂P₁ = tot z := by
  obtain ⟨M, hM, hMX⟩ := F.hasMart_G hD0 n measurable_tot (contDiff_tot.contDiffOn.of_le
    (by simp)) (continuousOn_L₁_tot D0)
  have hX : (fun (t : ℝ≥0) (ω : Ω₁) => tot (F.Yf n t ω) - tot (F.Yf n 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, switchOff (F.e n) (fun t ω => L₁ D0 tot (F.Yf n t ω)) s.toNNReal ω) =
      fun t ω => F.Sp n t ω - tot z := by
    funext t ω
    have h0 : ∀ s : ℝ, switchOff (F.e n) (fun t ω => L₁ D0 tot (F.Yf n t ω)) s.toNNReal ω = 0 :=
      fun s => by unfold switchOff; split_ifs <;> simp [L₁_tot D0 (F.Yf_mem n _ ω)]
    simp only [h0, integral_zero, sub_zero, F.Yf_zero hz, Sp]
  rw [hX] at hMX
  obtain ⟨M', hM', hM'e⟩ := Semimartingale.exists_martingale_stoppedProcess hM hMX
    (Eventually.of_forall fun ω => (F.continuous_Sp n ω).sub continuous_const) hσ
  have hT := hM'e T
  have h0 := hM'e 0
  have hint : Integrable (fun ω => F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω - tot z) P₁ :=
    (hM'.integrable T).congr (hT.trans (Eventually.of_forall fun ω => rfl))
  have hint' : Integrable (fun ω => F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω) P₁ :=
    (hint.add (integrable_const (tot z))).congr (Eventually.of_forall fun ω => by simp)
  refine ⟨hint', ?_⟩
  have e1 : ∫ ω, M' T ω ∂P₁ = ∫ ω, M' 0 ω ∂P₁ := by
    simpa using (hM'.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ).symm
  have e2 : ∫ ω, M' 0 ω ∂P₁ = 0 := by
    rw [integral_congr_ae h0]
    have : ∀ ω, stoppedProcess (fun t ω => F.Sp n t ω - tot z) σ 0 ω = 0 := fun ω => by
      simp only [stoppedProcess, Sp]
      rw [min_eq_left (by rw [WithTop.coe_zero]; exact bot_le)]
      simp [F.Yf_zero hz]
    simp only [this, integral_zero]
  rw [integral_congr_ae hT] at e1
  have e3 : ∫ ω, (F.Sp n (min (T : WithTop ℝ≥0) (σ ω)).untopA ω - tot z) ∂P₁ = 0 := by
    rw [← e2, ← e1]; rfl
  rw [integral_sub hint' (integrable_const _)] at e3
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at e3
  linarith

/-- **Estimate A**: the Lyapunov bound before the first visit to `{S ≤ ε}`. -/
theorem measure_noHit_le (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (n : ℕ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (T : ℝ≥0) :
    ENNReal.ofReal (exp (-D0 * T) * (ε * n)) *
      P₁ {ω | F.e n ω < F.hitS n ε ω ∧ F.e n ω < T} ≤ ENNReal.ofReal (lyapG z) := by
  refine F.measure_discount_le hD0 hz n measurable_lyapG contDiffOn_lyapG
    (fun _ hy => lyapG_nonneg hy) hD0.le (fun _ hy => L₁_lyapG_le hD0.le hy)
    (F.isStoppingTime_hitS n ε) T _ _ fun ω hω => ?_
  obtain ⟨h1, h2⟩ := hω
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
  have hmT : m ≤ T := by rw [← hm] at h2; exact (WithTop.coe_lt_coe.1 h2).le
  have hle : (m : WithTop ℝ≥0) ≤ min (T : WithTop ℝ≥0) (F.hitS n ε ω) :=
    le_min (WithTop.coe_le_coe.2 hmT) (hm ▸ h1.le)
  obtain ⟨s, hs'⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left (T : WithTop ℝ≥0) (F.hitS n ε ω)))
  have hs := hs'.symm
  have hsT : s ≤ T := by
    have := min_le_left (T : WithTop ℝ≥0) (F.hitS n ε ω); rw [hs] at this
    exact WithTop.coe_le_coe.1 this
  have hms : m ≤ s := by rw [hs] at hle; exact WithTop.coe_le_coe.1 hle
  rw [hs]
  show exp (-D0 * T) * (ε * n) ≤ exp (-D0 * (s : ℝ)) * lyapG (F.Yf n s ω)
  have hY : F.Yf n s ω = toFlat (F.X n m ω) := by rw [Yf, F.X_eq_of_e_le n hm.symm hms]
  have hnorm : (n : ℝ) ≤ ‖F.X n m ω‖ := le_norm_exitTimeOf (F.continuous_X n ω) hm.symm
  have hS : ε ≤ tot (toFlat (F.X n m ω)) :=
    (lt_hitLe (V := F.Sp n) (hm ▸ h1)).le
  have hg := lyapG_toFlat_ge (Nat.cast_nonneg n) hnorm hε0.le hε1 hS
  rw [hY]
  have he : exp (-D0 * T) ≤ exp (-D0 * (s : ℝ)) :=
    exp_le_exp.2 (by nlinarith [NNReal.coe_le_coe.2 hsT])
  exact mul_le_mul he hg (by positivity) (exp_pos _).le

/-- `−S` after `hitS n ε`, `0` before. -/
def postV (n : ℕ) (ε : ℝ) (t : ℝ≥0) (ω : Ω₁) : ℝ :=
  if F.hitS n ε ω ≤ t then -F.Sp n t ω else 0

/-- The first time at or after `hitS n ε` with `S ≥ a`. -/
def hitUp (n : ℕ) (ε a : ℝ) : Ω₁ → WithTop ℝ≥0 := hitLe (F.postV n ε) (-a)

theorem postV_of_le (n : ℕ) (ε : ℝ) {t : ℝ≥0} {ω : Ω₁} (h : F.hitS n ε ω ≤ t) :
    F.postV n ε t ω = -F.Sp n t ω := ite_eq_left h

theorem postV_of_lt (n : ℕ) (ε : ℝ) {t : ℝ≥0} {ω : Ω₁} (h : (t : WithTop ℝ≥0) < F.hitS n ε ω) :
    F.postV n ε t ω = 0 := ite_eq_right (not_le.2 h)

theorem postV_rightCont (n : ℕ) (ε : ℝ) (ω : Ω₁) (t : ℝ≥0) :
    Tendsto (fun u => F.postV n ε u ω) (𝓝[≥] t) (𝓝 (F.postV n ε t ω)) := by
  by_cases h : F.hitS n ε ω ≤ t
  · have he : (fun u => F.postV n ε u ω) =ᶠ[𝓝[≥] t] fun u => -F.Sp n u ω :=
      eventually_nhdsWithin_of_forall fun u hu =>
        F.postV_of_le n ε (h.trans (WithTop.coe_le_coe.2 hu))
    rw [F.postV_of_le n ε h]
    exact (tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω).neg t).congr' he.symm
  · have hlt : (t : WithTop ℝ≥0) < F.hitS n ε ω := not_le.1 h
    have he : (fun u => F.postV n ε u ω) =ᶠ[𝓝 t] fun _ => F.postV n ε t ω := by
      filter_upwards [(isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hlt] with u hu
      rw [F.postV_of_lt n ε hu, F.postV_of_lt n ε hlt]
    exact tendsto_const_nhds.congr' (he.filter_mono nhdsWithin_le_nhds).symm

theorem postV_lsc (n : ℕ) (ε : ℝ) (ω : Ω₁) : LowerSemicontinuous fun u => F.postV n ε u ω := by
  intro t y hy
  have hy' : y < F.postV n ε t ω := hy
  show ∀ᶠ u in 𝓝 t, y < F.postV n ε u ω
  by_cases h : F.hitS n ε ω ≤ t
  · rw [F.postV_of_le n ε h] at hy'
    have h0 : y < 0 := hy'.trans (neg_lt_zero.2 (F.Sp_pos n t ω))
    filter_upwards [((F.continuous_Sp n ω).neg.continuousAt (x := t)).eventually
      (lt_mem_nhds hy')] with u hu
    by_cases hu' : F.hitS n ε ω ≤ u
    · rw [F.postV_of_le n ε hu']; exact hu
    · rw [F.postV_of_lt n ε (not_le.1 hu')]; exact h0
  · have hlt : (t : WithTop ℝ≥0) < F.hitS n ε ω := not_le.1 h
    rw [F.postV_of_lt n ε hlt] at hy'
    filter_upwards [(isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hlt] with u hu
    rw [F.postV_of_lt n ε hu]; exact hy'

theorem isStoppingTime_hitUp (n : ℕ) (ε a : ℝ) : IsStoppingTime 𝓖₁ (F.hitUp n ε a) :=
  isStoppingTime_hitLe (fun t => Measurable.ite ((F.isStoppingTime_hitS n ε).measurableSet_le t)
    (F.measurable_Sp n t).neg measurable_const) (fun ω t => F.postV_rightCont n ε ω t)
    (F.postV_lsc n ε) (-a)

/-- **Estimate B**: after reaching `{S ≤ ε}`, the path reaches `{S ≥ a}` with probability
at most `ε / a`. -/
theorem measure_upcross_le (hD0 : 0 < D0) (hz : z ∈ flatChamber 1) (n : ℕ) {ε a : ℝ}
    (hε : 0 < ε) (ha : 0 < a) (T : ℝ≥0) :
    P₁ {ω | F.hitS n ε ω < T ∧ ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧ a ≤ F.Sp n s ω} ≤
      ENNReal.ofReal (ε / a) := by
  have hτs := F.isStoppingTime_hitS n ε
  obtain ⟨hiρ, eρ⟩ := F.integral_Sp_stop hD0 hz n (F.isStoppingTime_hitUp n ε a) T
  obtain ⟨hiτ, eτ⟩ := F.integral_Sp_stop hD0 hz n hτs T
  set A : Set Ω₁ := {ω | F.hitS n ε ω < T} with hAdef
  have hA : MeasurableSet A := 𝓖₁.le T _ (hτs.measurableSet_lt T)
  have hρτ : ∀ ω, F.hitS n ε ω ≤ F.hitUp n ε a ω := fun ω => by
    refine le_iInf₂ fun u hu => ?_
    by_contra hc
    have : F.postV n ε u ω = 0 := F.postV_of_lt n ε (not_le.1 hc)
    linarith
  have hc : ∀ ω ∈ Aᶜ, F.Sp n (min (T : WithTop ℝ≥0) (F.hitUp n ε a ω)).untopA ω =
      F.Sp n (min (T : WithTop ℝ≥0) (F.hitS n ε ω)).untopA ω := fun ω hω => by
    have h1 : (T : WithTop ℝ≥0) ≤ F.hitS n ε ω := not_lt.1 hω
    rw [min_eq_left h1, min_eq_left (h1.trans (hρτ ω))]
  have hAeq : ∫ ω in A, F.Sp n (min (T : WithTop ℝ≥0) (F.hitUp n ε a ω)).untopA ω ∂P₁ =
      ∫ ω in A, F.Sp n (min (T : WithTop ℝ≥0) (F.hitS n ε ω)).untopA ω ∂P₁ := by
    have h1 := integral_add_compl hA hiρ
    have h2 := integral_add_compl hA hiτ
    rw [setIntegral_congr_fun hA.compl hc] at h1
    linarith
  have hAle : ∫ ω in A, F.Sp n (min (T : WithTop ℝ≥0) (F.hitS n ε ω)).untopA ω ∂P₁ ≤ ε := by
    refine (setIntegral_mono_on (g := fun _ => ε) hiτ.integrableOn integrableOn_const hA
      fun ω hω => ?_).trans ?_
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (show F.hitS n ε ω < T from hω))
      rw [← hm, min_eq_right (hm ▸ (show F.hitS n ε ω < T from hω).le)]
      exact hitLe_attained (fun t => tendsto_nhdsGE_of_continuous (F.continuous_Sp n ω) t)
        hm.symm
    · rw [setIntegral_const, smul_eq_mul]
      have : P₁.real A ≤ 1 := measureReal_le_one
      nlinarith [measureReal_nonneg (μ := P₁) (s := A)]
  set f : Ω₁ → ℝ := A.indicator fun ω => F.Sp n (min (T : WithTop ℝ≥0) (F.hitUp n ε a ω)).untopA ω
  have hf0 : 0 ≤ᵐ[P₁] f := Eventually.of_forall fun ω => by
    simp only [f, Set.indicator]; split_ifs
    · exact (F.Sp_pos n _ ω).le
    · exact le_rfl
  have hMk := mul_meas_ge_le_integral_of_nonneg hf0 (hiρ.indicator hA) a
  rw [integral_indicator hA, hAeq] at hMk
  have hsub : {ω | F.hitS n ε ω < T ∧ ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧ a ≤ F.Sp n s ω} ⊆
      {ω | a ≤ f ω} := by
    rintro ω ⟨hωA, s, hsT, hτs', has⟩
    have hV : F.postV n ε s ω ≤ -a := by rw [F.postV_of_le n ε hτs']; linarith
    have hρs : F.hitUp n ε a ω ≤ s := iInf₂_le s hV
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hρs)
    have hmT : (m : WithTop ℝ≥0) ≤ T := hm ▸ hρs.trans (WithTop.coe_le_coe.2 hsT)
    have hVm : F.postV n ε m ω ≤ -a :=
      hitLe_attained (fun t => F.postV_rightCont n ε ω t) hm.symm
    have hτm : F.hitS n ε ω ≤ m := by
      by_contra hc
      have : F.postV n ε m ω = 0 := F.postV_of_lt n ε (not_le.1 hc)
      linarith
    show a ≤ A.indicator _ ω
    rw [Set.indicator_of_mem (show ω ∈ A from hωA), ← hm, min_eq_right hmT]
    rw [F.postV_of_le n ε hτm] at hVm
    show a ≤ F.Sp n m ω
    linarith
  have hreal : P₁.real {ω | F.hitS n ε ω < T ∧ ∃ s : ℝ≥0, s ≤ T ∧ F.hitS n ε ω ≤ s ∧
      a ≤ F.Sp n s ω} ≤ ε / a := by
    rw [le_div_iff₀ ha]
    have := measureReal_mono (μ := P₁) hsub (measure_ne_top _ _)
    nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top P₁ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end SolFamily

end BlockBand.Transmission.Dual.Exists
