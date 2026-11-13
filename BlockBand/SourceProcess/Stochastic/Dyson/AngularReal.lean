module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularPhase

/-!
# Real martingale identities for the exponential test processes

With `Ms = (f(X) - ∫𝒜f)^{σ_n}`:
* `Hyp.ms_props`: `Ms` has a martingale modification, is adapted, and is a.s. bounded on bounded
  time intervals;
* `Hyp.testMart_Zre`: `e^{c_θ u} h(θ·λ_u - ∫θ·b)` has the test-function martingale identity;
* `Hyp.testMart_ZreMs`: so has `e^{c_θ u} h(⋯) Ms_u`. Before `σ_n` this is the stopped Itô
  product (`pfun_mart`); after `σ_n` it is the optional-sampling identity
  `integral_mul_stoppedProd` with the bounded stopping time `σ_n ∧ T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  stopTime_le)

theorem stopTime_min_of_le {τ : WithTop ℝ≥0} {u T : ℝ≥0} (h : u ≤ T) :
    stopTime (min τ T) u = stopTime τ u := by
  unfold stopTime
  congr 1
  rw [min_left_comm, min_eq_left (WithTop.coe_le_coe.2 h), min_comm]

theorem stopTime_min_eq (τ : WithTop ℝ≥0) (u T : ℝ≥0) :
    stopTime (min τ T) u = stopTime τ (min u T) := by
  unfold stopTime
  congr 1
  rw [WithTop.coe_min, min_comm τ, ← min_assoc]

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

/-- The gap stop `σ_n`. -/
abbrev sig (N : ℕ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n : ℕ) : Ω → WithTop ℝ≥0 := gapStop N (fun t ω => F ω + G t ω) s n

theorem Hyp.ms_props (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) :
    HasMartingaleModification Q (shiftFiltration 𝓖 s)
        (stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n)) ∧
      (∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t]
        (stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) t)) ∧
      ∀ T : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ r ≤ T,
        |stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω| ≤ C := by
  have e : stoppedProcess (fun u ω => Pfun Real.cos 0 f (Yplus 0 f (Yst N q G F s) u ω))
      (sig N G F s n) = stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) := by
    funext u ω; simp only [stoppedProcess_eq_stopTime, Pfun_zero_Yplus]
  obtain ⟨h1, h2, -⟩ := pfun_mart H.hG H.hF H.hFh H.hb1 H.hs q 0 H.hf trig_cos
    (fun x => Real.abs_cos_le_one x) H.hn
  rw [e] at h1 h2
  refine ⟨h1, h2, fun T => ?_⟩
  obtain ⟨Kf, -, hKf⟩ := exists_f_bound H.hf q
  obtain ⟨Ka, hKa0, hKa⟩ := exists_angGen_bound H.hf q H.hn
  refine ⟨Kf + Ka * T, ?_⟩
  filter_upwards [H.hb1] with ω hω r hr
  have := g2_stop_bound H.hG H.hFh H.hs hω q 0 hKf hKa0 hKa hr
  rwa [g2_Yplus] at this

theorem Hyp.testMart_Zre (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ)
    {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1) :
    TestMart Q (shiftFiltration 𝓖 s)
      (fun u ω => Real.exp (cθ θ * u) * h (phase θ (Yst N q G F s) u ω)) := by
  have := (phi_mart (f := f) H.hG H.hF H.hFh H.hb1 H.hs q θ H.hf hh hb).1
  simp only [Phi_Yplus] at this
  exact testMart_of_hasMM this

theorem Hyp.testMart_ZreMs (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ)
    {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1) :
    TestMart Q (shiftFiltration 𝓖 s)
      (fun u ω => Real.exp (cθ θ * u) * h (phase θ (Yst N q G F s) u ω) *
        stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) u ω) := by
  set Y := Yst N q G F s
  set σ := sig N G F s n
  set Φ : ℝ≥0 → Ω → ℝ := fun u ω => Phi h θ (Yplus θ f Y u ω)
  set Ms := stoppedProcess (Mt f Y) σ
  obtain ⟨hΦ, hΦad, hΦc⟩ := phi_mart (f := f) H.hG H.hF H.hFh H.hb1 H.hs q θ H.hf hh hb
  obtain ⟨hP, -, -⟩ := pfun_mart H.hG H.hF H.hFh H.hb1 H.hs q θ H.hf hh hb H.hn
  obtain ⟨-, hMsad, hMsb⟩ := H.ms_props q
  have hσ : IsStoppingTime (shiftFiltration 𝓖 s) σ := isStoppingTime_sigma H.hG H.hF s n
  have eΦ : ∀ u ω, Φ u ω = Real.exp (cθ θ * u) * h (phase θ Y u ω) := fun u ω => Phi_Yplus ..
  -- integrability
  have hint : ∀ t, Integrable (fun ω => Φ t ω * Ms t ω) Q := fun t => by
    obtain ⟨C, hC⟩ := hMsb t
    refine ((testMart_of_hasMM hΦ).1 t).mul_bdd (c := C) ?_ ?_
    · exact ((hMsad t).mono ((shiftFiltration 𝓖 s).le t)).aestronglyMeasurable
    · filter_upwards [hC] with ω hω; rw [Real.norm_eq_abs]; exact hω t le_rfl
  refine ⟨fun t => (hint t).congr (ae_of_all _ fun ω => by simp only [eΦ]),
    fun r t hrt η hη C hC => ?_⟩
  -- horizon `T = t` and the bounded stopping time `ρ = σ ∧ t`
  set ρ : Ω → WithTop ℝ≥0 := fun ω => min (σ ω) t
  have hρ : IsStoppingTime (shiftFiltration 𝓖 s) ρ := hσ.min_const t
  obtain ⟨CZ, hCZ⟩ := hMsb t
  have hZad : ∀ u, StronglyMeasurable[shiftFiltration 𝓖 s u] (stoppedProcess (Mt f Y) ρ u) :=
    fun u => by
      have e : stoppedProcess (Mt f Y) ρ u = Ms (min u t) := by
        funext ω; simp only [stoppedProcess_eq_stopTime, Ms, ρ, stopTime_min_eq]
      rw [e]; exact (hMsad _).mono ((shiftFiltration 𝓖 s).mono (min_le_left _ _))
  have hZb : ∀ᵐ ω ∂Q, ∀ u, ‖stoppedProcess (Mt f Y) ρ u ω‖ ≤ CZ := by
    filter_upwards [hCZ] with ω hω u
    rw [stoppedProcess_eq_stopTime, stopTime_min_eq, Real.norm_eq_abs]
    exact hω _ (min_le_right _ _)
  have hdec : ∀ u ≤ t, ∀ ω, Φ u ω * Ms u ω = stoppedProcess (fun u ω =>
      Pfun h θ f (Yplus θ f Y u ω)) σ u ω +
      (Φ u ω - stoppedProcess Φ ρ u ω) * stoppedProcess (Mt f Y) ρ u ω := by
    intro u hu ω
    simp only [stoppedProcess_eq_stopTime, Ms, ρ, stopTime_min_of_le hu, Pfun, Φ, g2_Yplus]
    ring
  have hK := integral_mul_stoppedProd hΦ hΦc hρ (fun ω => min_le_right _ _) hZad hZb hrt hη hC
  have hPt := (testMart_of_hasMM hP).2 r t hrt η hη C hC
  have hi : ∀ u, Integrable (fun ω => η ω * stoppedProcess (fun u ω =>
      Pfun h θ f (Yplus θ f Y u ω)) σ u ω) Q := fun u =>
    ((testMart_of_hasMM hP).1 u).bdd_mul (hη.mono ((shiftFiltration 𝓖 s).le r)).aestronglyMeasurable hC
  have hiK : ∀ u, Integrable (fun ω => η ω * ((Φ u ω - stoppedProcess Φ ρ u ω) *
      stoppedProcess (Mt f Y) ρ u ω)) Q := fun u => by
    have h1 := (integrable_sub_stopped hΦ hΦc hρ u).bdd_mul
      ((hZad u).mono ((shiftFiltration 𝓖 s).le u)).aestronglyMeasurable
      (by filter_upwards [hZb] with ω hω using hω u)
    refine (h1.bdd_mul (hη.mono ((shiftFiltration 𝓖 s).le r)).aestronglyMeasurable hC).congr
      (ae_of_all _ fun ω => ?_)
    simp only; ring
  have hsplit : ∀ u ≤ t, ∫ ω, η ω * (Real.exp (cθ θ * u) * h (phase θ Y u ω) * Ms u ω) ∂Q =
      ∫ ω, η ω * stoppedProcess (fun u ω => Pfun h θ f (Yplus θ f Y u ω)) σ u ω ∂Q +
      ∫ ω, η ω * ((Φ u ω - stoppedProcess Φ ρ u ω) * stoppedProcess (Mt f Y) ρ u ω) ∂Q := by
    intro u hu
    rw [← integral_add (hi u) (hiK u)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    rw [← eΦ, hdec u hu ω]; ring
  show ∫ ω, η ω * (Real.exp (cθ θ * t) * h (phase θ Y t ω) * Ms t ω) ∂Q =
    ∫ ω, η ω * (Real.exp (cθ θ * r) * h (phase θ Y r ω) * Ms r ω) ∂Q
  rw [hsplit t le_rfl, hsplit r hrt, hPt, hK]

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
