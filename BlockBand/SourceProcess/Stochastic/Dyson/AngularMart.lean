module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularBounds
public import BlockBand.SourceProcess.Stochastic.Dyson.MMTools
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse

/-!
# Martingales of the augmented Dyson state (from the Itô and stopping contracts)

* `zeroDrift_stopped` (generic): for a continuous semimartingale `Y` and a `C²` function `g` with
  identically zero Itô drift along `Y`, and a stopping time `ρ` with `g(Y^ρ)` a.s. bounded on
  bounded time intervals, `g(Y^ρ)` has a martingale modification, is adapted and a.s. continuous.
  Proof: contracts (a1) (`semimartingaleItoFormula_holds`), (a2)
  (`stoppedSemimartingale_holds`) and removal of the localization by domination.
* `phi_mart`: `Φ_u = e^{c_θ u} h(θ·W_u)` (`W = λ - ∫ b(λ)`) is a martingale;
* `pfun_mart`: `(Φ (f(X) - ∫ 𝒜 f))^{σ_n}` is a martingale (gap stop `σ_n`, `n > 0`).
Both use non-collision (b1).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_le stopTime_zero
  stoppedProcess_eq_stopTime)

/-- **Zero-drift functions of a semimartingale, stopped, are martingales (modification form).** -/
theorem zeroDrift_stopped {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (H : IsContinuousSemimartingale Q 𝓕 Y β α) {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ 2 g)
    (hzero : ∀ t ω, itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) (Y t ω) t (β t ω) (α t ω) = 0)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    (hbd : ∀ T, ∃ C, ∀ᵐ ω ∂Q, ∀ r ≤ T, |stoppedProcess (fun t ω => g (Y t ω)) ρ r ω| ≤ C) :
    HasMartingaleModification Q 𝓕 (stoppedProcess (fun t ω => g (Y t ω)) ρ) ∧
      (∀ t, StronglyMeasurable[𝓕 t] (stoppedProcess (fun t ω => g (Y t ω)) ρ t)) ∧
      ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (fun t ω => g (Y t ω)) ρ t ω := by
  have hI := SemimartingaleIto.semimartingaleItoFormula_holds d Ω Q 𝓕 Y β α H Set.univ
    isOpen_univ (ae_of_all _ fun _ _ => mem_univ _) (fun p => g p.2)
    (hg.continuous.measurable.comp measurable_snd) (hg.comp contDiff_snd).contDiffOn
  have hS := Semimartingale.stoppedSemimartingale_holds 1 Ω Q 𝓕 _ _ _ hI ρ hρ
  set Z := stoppedProcess (fun t ω => g (Y t ω)) ρ with hZdef
  have hZ0 : ∀ ω, Z 0 ω = g (Y 0 ω) := fun ω => by
    simp only [Z, stoppedProcess_eq_stopTime, stopTime_zero]
  refine ⟨?_, fun t => ?_, ?_⟩
  · obtain ⟨τ, -, hτlim, hloc⟩ := hS.localizing
    set X : ℝ≥0 → Ω → ℝ := fun t ω => Z t ω - g (Y 0 ω)
    have hcomp : smCompensated (stoppedProcess (fun t ω (_ : Fin 1) =>
        (fun p : ℝ × (Fin d → ℝ) => g p.2) ((t : ℝ), Y t ω)) ρ)
        (switchAfter ρ fun t ω (_ : Fin 1) => itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2)
          (Y t ω) t (β t ω) (α t ω)) 0 = X := by
      funext t ω
      simp only [smCompensated, switchAfter, hzero, X, Z, stoppedProcess_eq_stopTime,
        stopTime_zero]
      have : ∀ s : ℝ, ((if ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ ω then fun _ : Fin 1 => (0 : ℝ)
          else 0) 0) = 0 := fun s => by split_ifs <;> rfl
      simp only [this, integral_zero, sub_zero]
    have hX : HasMartingaleModification Q 𝓕 X := by
      refine hasMartingaleModification_of_localized hτlim (fun n => ?_) (fun T => ?_)
      · have := (hloc n).1 0; rwa [hcomp] at this
      · obtain ⟨C, hC⟩ := hbd T
        refine ⟨C + C, ?_⟩
        filter_upwards [hC] with ω hω r hr
        have h0 := hω 0 zero_le
        rw [hZ0] at h0
        calc |X r ω| ≤ |Z r ω| + |g (Y 0 ω)| := abs_sub _ _
          _ ≤ C + C := add_le_add (hω r hr) h0
    have hm0 : StronglyMeasurable[𝓕 0] fun ω => g (Y 0 ω) :=
      hg.continuous.comp_stronglyMeasurable (H.adapted 0)
    obtain ⟨C, hC⟩ := hbd 0
    have hint : Integrable (fun ω => g (Y 0 ω)) Q := by
      refine Integrable.of_bound (hm0.mono (𝓕.le 0)).aestronglyMeasurable C ?_
      filter_upwards [hC] with ω hω
      have := hω 0 le_rfl; rwa [hZ0, ← Real.norm_eq_abs] at this
    have hconst : HasMartingaleModification Q 𝓕 (fun _ ω => g (Y 0 ω)) := by
      refine ⟨fun _ ω => g (Y 0 ω), ⟨fun t => hm0.mono (𝓕.mono zero_le), fun i j _ => ?_⟩,
        fun _ => ae_of_all _ fun _ => rfl⟩
      show Q[fun ω => g (Y 0 ω) | 𝓕 i] =ᵐ[Q] fun ω => g (Y 0 ω)
      rw [condExp_of_stronglyMeasurable (𝓕.le i) (hm0.mono (𝓕.mono zero_le)) hint]
    refine Dyson.hasMM_congr (Dyson.hasMM_add hX hconst) fun t => ae_of_all _ fun ω => ?_
    simp [X]
  · exact (continuous_apply 0).comp_stronglyMeasurable (hS.adapted t)
  · filter_upwards [hS.continuous] with ω hω
    exact (continuous_apply 0).comp hω

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

omit [IsProbabilityMeasure Q] in
theorem isStoppingTime_sigma (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (s : ℝ≥0) (n : ℕ) :
    IsStoppingTime (shiftFiltration 𝓖 s) (gapStop N (fun t ω => F ω + G t ω) s n) :=
  isStoppingTime_gapStop (continuous_hermBM_add hG F) (measurable_hermBM_add hG hF) s n

/-- **The exponential martingale** `Φ = e^{c_θ u} h(θ·λ_u - ∫_0^u θ·b(λ))`. -/
theorem phi_mart (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (hFh : ∀ ω, (F ω).IsHermitian)
    (hb1 : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω))
    {s : ℝ≥0} (hs : 0 < s) (q : Fin N → ℂ) (θ : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1) :
    HasMartingaleModification Q (shiftFiltration 𝓖 s)
        (fun u ω => Phi h θ (Yplus θ f (Yst N q G F s) u ω)) ∧
      (∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t]
        fun ω => Phi h θ (Yplus θ f (Yst N q G F s) t ω)) ∧
      ∀ᵐ ω ∂Q, Continuous fun t => Phi h θ (Yplus θ f (Yst N q G F s) t ω) := by
  have H := zeroDrift_stopped (isContinuousSemimartingale_Yplus hG hF hFh hb1 hs q θ hf)
    (contDiff_Phi hh θ) (fun t ω => itoDrift_Phi θ f _ hh t) isStoppingTime_top_const
    (fun T => ⟨Real.exp (cθ θ * T), ae_of_all _ fun ω r hr => by
      rw [stoppedProcess_top]; exact Phi_bound hb θ f _ hr ω⟩)
  rwa [stoppedProcess_top] at H

/-- **The stopped product martingale** `(Φ (f(X) - ∫ 𝒜 f))^{σ_n}`. -/
theorem pfun_mart (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (hFh : ∀ ω, (F ω).IsHermitian)
    (hb1 : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω))
    {s : ℝ≥0} (hs : 0 < s) (q : Fin N → ℂ) (θ : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    HasMartingaleModification Q (shiftFiltration 𝓖 s) (stoppedProcess
        (fun u ω => Pfun h θ f (Yplus θ f (Yst N q G F s) u ω))
        (gapStop N (fun t ω => F ω + G t ω) s n)) ∧
      (∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t] (stoppedProcess
        (fun u ω => Pfun h θ f (Yplus θ f (Yst N q G F s) u ω))
        (gapStop N (fun t ω => F ω + G t ω) s n) t)) ∧
      ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess
        (fun u ω => Pfun h θ f (Yplus θ f (Yst N q G F s) u ω))
        (gapStop N (fun t ω => F ω + G t ω) s n) t ω := by
  obtain ⟨Kf, hKf0, hKf⟩ := exists_f_bound hf q
  obtain ⟨Ka, hKa0, hKa⟩ := exists_angGen_bound hf q hn
  refine zeroDrift_stopped (isContinuousSemimartingale_Yplus hG hF hFh hb1 hs q θ hf)
    (contDiff_Pfun hh θ hf) (fun t ω => itoDrift_Pfun θ _ hh hf t) (isStoppingTime_sigma hG hF s n)
    (fun T => ⟨Real.exp (cθ θ * T) * (Kf + Ka * T), ?_⟩)
  filter_upwards [hb1] with ω hω r hr
  rw [stoppedProcess_eq_stopTime]
  unfold Pfun
  rw [abs_mul]
  exact mul_le_mul (Phi_bound hb θ f _ ((stopTime_le _ r).trans hr) ω)
    (g2_stop_bound hG hFh hs hω q θ hKf hKa0 hKa hr) (abs_nonneg _) (Real.exp_pos _).le

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
