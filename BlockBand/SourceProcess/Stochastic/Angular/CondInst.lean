module

public import BlockBand.SourceProcess.Stochastic.Angular.CondMart
public import BlockBand.SourceProcess.Stochastic.Angular.CondFourier
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularStrong

/-!
# Complex angular martingale problem: orthogonality hypotheses and the strong solution

Under `CondHyp`, with `Y = Yst N 0 G F s` and `Ms = Mc^{σ_n}`:
* `CondHyp.zrems`: the analogue of `testMart_ZreMs` (stopped Itô product before `σ_n`, the
  optional-sampling identity `integral_mul_stoppedProd` after it);
* **`CondHyp.ohyp`**: `OHyp Q (𝓖_{s+·}) Y Ms`, so the orthogonality chain applies
  (`OHyp.orth_sigma`);
* **`CondHyp.aesm_lam`**: the analogue of `aesm_lam` (Euler scheme) under the
  a.s.-simple hypothesis of `GenericConditioning` instead of `0 < s` and clause (b1): each `λ_v`
  is a.e. `𝓖_s ⊔ σ(W)`-measurable. This allows `s = 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.SourceProcess.Stochastic.Dyson.Angular
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime rgrid)

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
  {s : ℝ≥0} {n : ℕ} {φ A : (Fin (N * N) → ℝ) → ℝ}

/-- `e^{c_θ u} h(phase) Ms_u` has the test-function martingale identity. -/
theorem CondHyp.zrems [IsProbabilityMeasure Q] (H : CondHyp Q 𝓖 G F s n φ A) (θ : Fin N → ℝ)
    {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1) :
    TestMart Q (shiftFiltration 𝓖 s)
      (fun u ω => Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω) *
        stoppedProcess (Mc φ A G F s) (sig N G F s n) u ω) := by
  set Y := Yst N 0 G F s
  set σ := sig N G F s n
  set Φ : ℝ≥0 → Ω → ℝ := fun u ω => Real.exp (cθ θ * u) * h (phase θ Y u ω) with hΦdef
  set Ms := stoppedProcess (Mc φ A G F s) σ
  obtain ⟨hΦ, -, hΦc⟩ := H.phic_mart θ hh hb
  obtain ⟨hP, -⟩ := H.pcond_mart θ hh hb
  obtain ⟨hMsad, hMsb⟩ := H.ms_props
  have hσ : IsStoppingTime (shiftFiltration 𝓖 s) σ := isStoppingTime_sigma H.hG H.hF s n
  have hint : ∀ t, Integrable (fun ω => Φ t ω * Ms t ω) Q := fun t => by
    obtain ⟨C, hC⟩ := hMsb t
    refine ((testMart_of_hasMM hΦ).1 t).mul_bdd (c := C) ?_ ?_
    · exact ((hMsad t).mono ((shiftFiltration 𝓖 s).le t)).aestronglyMeasurable
    · filter_upwards [hC] with ω hω; rw [Real.norm_eq_abs]; exact hω t le_rfl
  refine ⟨hint, fun r t hrt η hη C hC => ?_⟩
  set ρ : Ω → WithTop ℝ≥0 := fun ω => min (σ ω) t
  have hρ : IsStoppingTime (shiftFiltration 𝓖 s) ρ := hσ.min_const t
  obtain ⟨CZ, hCZ⟩ := hMsb t
  have hZad : ∀ u, StronglyMeasurable[shiftFiltration 𝓖 s u]
      (stoppedProcess (Mc φ A G F s) ρ u) := fun u => by
    have e : stoppedProcess (Mc φ A G F s) ρ u = Ms (min u t) := by
      funext ω; simp only [stoppedProcess_eq_stopTime, Ms, ρ, stopTime_min_eq]
    rw [e]; exact (hMsad _).mono ((shiftFiltration 𝓖 s).mono (min_le_left _ _))
  have hZb : ∀ᵐ ω ∂Q, ∀ u, ‖stoppedProcess (Mc φ A G F s) ρ u ω‖ ≤ CZ := by
    filter_upwards [hCZ] with ω hω u
    rw [stoppedProcess_eq_stopTime, stopTime_min_eq, Real.norm_eq_abs]
    exact hω _ (min_le_right _ _)
  have hdec : ∀ u ≤ t, ∀ ω, Φ u ω * Ms u ω =
      stoppedProcess (fun u ω => Φ u ω * Mc φ A G F s u ω) σ u ω +
      (Φ u ω - stoppedProcess Φ ρ u ω) * stoppedProcess (Mc φ A G F s) ρ u ω := by
    intro u hu ω
    simp only [stoppedProcess_eq_stopTime, Ms, ρ, stopTime_min_of_le hu]
    ring
  have hK := integral_mul_stoppedProd hΦ hΦc hρ (fun ω => min_le_right _ _) hZad hZb hrt hη hC
  have hPt := (testMart_of_hasMM hP).2 r t hrt η hη C hC
  have hi : ∀ u, Integrable (fun ω => η ω *
      stoppedProcess (fun u ω => Φ u ω * Mc φ A G F s u ω) σ u ω) Q := fun u =>
    ((testMart_of_hasMM hP).1 u).bdd_mul
      (hη.mono ((shiftFiltration 𝓖 s).le r)).aestronglyMeasurable hC
  have hiK : ∀ u, Integrable (fun ω => η ω * ((Φ u ω - stoppedProcess Φ ρ u ω) *
      stoppedProcess (Mc φ A G F s) ρ u ω)) Q := fun u => by
    have h1 := (integrable_sub_stopped hΦ hΦc hρ u).bdd_mul
      ((hZad u).mono ((shiftFiltration 𝓖 s).le u)).aestronglyMeasurable
      (by filter_upwards [hZb] with ω hω using hω u)
    refine (h1.bdd_mul (hη.mono ((shiftFiltration 𝓖 s).le r)).aestronglyMeasurable hC).congr
      (ae_of_all _ fun ω => ?_)
    simp only; ring
  have hsplit : ∀ u ≤ t, ∫ ω, η ω * (Φ u ω * Ms u ω) ∂Q =
      ∫ ω, η ω * stoppedProcess (fun u ω => Φ u ω * Mc φ A G F s u ω) σ u ω ∂Q +
      ∫ ω, η ω * ((Φ u ω - stoppedProcess Φ ρ u ω) *
        stoppedProcess (Mc φ A G F s) ρ u ω) ∂Q := by
    intro u hu
    rw [← integral_add (hi u) (hiK u)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only
    rw [hdec u hu ω]; ring
  show ∫ ω, η ω * (Φ t ω * Ms t ω) ∂Q = ∫ ω, η ω * (Φ r ω * Ms r ω) ∂Q
  rw [hsplit t le_rfl, hsplit r hrt, hPt, hK]

theorem CondHyp.adapted_phase [IsProbabilityMeasure Q] (H : CondHyp Q 𝓖 G F s n φ A)
    (θ : Fin N → ℝ) (u : ℝ≥0) :
    StronglyMeasurable[shiftFiltration 𝓖 s u] fun ω => phase θ (Yst N 0 G F s) u ω := by
  have hZ := (isContinuousSemimartingale_Zc H.hG H.hF H.hFh H.hs θ (A := fun _ => 0)
    measurable_const continuousOn_const).adapted u
  have e : (fun ω => phase θ (Yst N 0 G F s) u ω) =
      fun ω => yfun (thLam θ) 0 (Zc θ (fun _ => 0) G F s u ω) :=
    funext fun ω => (phase_Zc H.hG H.hFh θ _ s u ω).symm
  rw [e]
  exact ((measurable_yfun (measurable_thLam θ) 0).comp hZ.measurable).stronglyMeasurable

/-- Continuity of the eigenvalue drift along a simple path. -/
theorem continuous_drift_lam {Q' : Measure Ω} (hG : IsHermitianBrownian Q' 𝓖 N G)
    (hFh : ∀ ω, (F ω).IsHermitian) {ω : Ω}
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) (i : Fin N) :
    Continuous fun r : ℝ => dysonDrift N (lamOf (Yst N 0 G F s r.toNNReal ω)) i := by
  have hc := (continuous_apply 0).comp (continuous_condVd_path hG hFh hω (Pi.single i 1)
    (A := fun _ => 0) continuousOn_const)
  refine hc.congr fun r => ?_
  simp [condVd, Pi.single_apply, lam_ycd_eq hG hFh]

theorem CondHyp.phase_eq_Wd (H : CondHyp Q 𝓖 G F s n φ A) (θ : Fin N → ℝ) :
    ∀ᵐ ω ∂Q, ∀ u, phase θ (Yst N 0 G F s) u ω = Wd θ (Yst N 0 G F s) u ω := by
  filter_upwards [H.hs] with ω hω u
  exact phase_eq_Wd_of (fun u i => (continuous_drift_lam H.hG H.hFh hω i).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self) θ u

/-- **The hypotheses of the orthogonality chain hold.** -/
theorem CondHyp.ohyp [IsProbabilityMeasure Q] (H : CondHyp Q 𝓖 G F s n φ A) :
    OHyp Q (shiftFiltration 𝓖 s) (Yst N 0 G F s)
      (stoppedProcess (Mc φ A G F s) (sig N G F s n)) where
  zre θ _ _ hh hb := testMart_of_hasMM (H.phic_mart θ hh hb).1
  zrems θ _ _ hh hb := H.zrems θ hh hb
  ms_props := H.ms_props
  adapted_phase := H.adapted_phase
  phase_eq_Wd := H.phase_eq_Wd

/-!
### The strong-solution step
-/

theorem euler_lam_tendsto' {Q' : Measure Ω} (hG : IsHermitianBrownian Q' 𝓖 N G)
    (hFh : ∀ ω, (F ω).IsHermitian) {ω : Ω}
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) (v : ℝ≥0) :
    Tendsto (fun K : ℕ => euler N (fun j => Wp (Yst N 0 G F s) (rgrid 0 v K j).toNNReal ω)
      ((v : ℝ) / (K + 1)) (K + 1)) atTop (𝓝 (lamOf (Yst N 0 G F s v ω))) := by
  set lam : ℝ → Fin N → ℝ := fun r => lamOf (Yst N 0 G F s r.toNNReal ω)
  have hlamE : ∀ r, lam r = dysonEigenvalue N (F ω + G (s + r.toNNReal) ω) := fun r => by
    simp only [lam, Yst, lamOf_dysonState]
  have hlam : Continuous lam := by
    refine continuous_pi fun i => ?_
    simp only [hlamE]
    exact (continuous_dysonEigenvalue i).comp ((continuous_hermBM_add hG F ω).comp
      (continuous_const.add continuous_real_toNNReal))
  have hd : ∀ r ∈ Icc (0 : ℝ) v, ∀ i j, i ≠ j → lam r i ≠ lam r j := fun r _ i j hij => by
    rw [hlamE]; exact (hω _).injective.ne hij
  have hbc : Continuous fun r => bv N (lam r) :=
    continuous_pi fun i => continuous_drift_lam hG hFh hω i
  have h := euler_tendsto (lam := lam) (W := fun r => Wp (Yst N 0 G F s) r.toNNReal ω)
    (u := v) v.2 hlam.continuousOn hd hbc.continuousOn
    (fun r hr i => Wp_eq 0 r hr.1 ω i)
  simpa [lam] using h

/-- **Strong solution**: `λ(F + G_{s+v})` is a.e. `𝓖_s ⊔ σ(W)`-measurable, for any `s`. -/
theorem CondHyp.aesm_lam (H : CondHyp Q 𝓖 G F s n φ A) (v : ℝ≥0) :
    AEStronglyMeasurable[sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)]
      (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) Q := by
  have hW : ∀ t, Measurable[sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)]
      (Wp (Yst N 0 G F s) t) := fun t =>
    (comap_measurable (Wp (Yst N 0 G F s) t)).mono
      (le_sup_of_le_right (le_iSup (fun t => MeasurableSpace.comap (Wp (Yst N 0 G F s) t)
        inferInstance) t)) le_rfl
  have hE : ∀ K : ℕ, AEStronglyMeasurable[sigB (shiftFiltration 𝓖 s 0) (Yst N 0 G F s)]
      (fun ω => euler N (fun j => Wp (Yst N 0 G F s) (rgrid 0 v K j).toNNReal ω)
        ((v : ℝ) / (K + 1)) (K + 1)) Q := fun K =>
    (measurable_euler (w := fun j => Wp (Yst N 0 G F s) (rgrid 0 v K j).toNNReal)
      (fun j => hW _) _ _).stronglyMeasurable.aestronglyMeasurable
  refine Semimartingale.aestronglyMeasurable_of_tendsto_ae_sub hE ?_
  filter_upwards [H.hs] with ω hω
  have := euler_lam_tendsto' H.hG H.hFh hω v
  rwa [Yst, lamOf_dysonState] at this

end BlockBand.SourceProcess.Stochastic.ComplexAngular
