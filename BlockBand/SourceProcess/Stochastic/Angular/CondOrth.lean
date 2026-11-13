module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularSigma

/-!
# Complex angular martingale problem: the orthogonality chain for an abstract martingale

`OHyp` collects the facts used by the orthogonality chain, for a driving path `Wp Y` and a process
`Ms`; this file derives from them the Gaussian increments of `W` (`OHyp.E1`), the orthogonality of
the eigenvalue noise and the angular martingale (`OHyp.E2`), and the factorization and
orthogonality of future exponential functionals (`OHyp.F1`, `OHyp.F2`). The fields of `OHyp` are:

* `OHyp.zre`, `OHyp.zrems`: `e^{c_θ u} h(phase_θ)` and `e^{c_θ u} h(phase_θ) Ms_u`
  (`h = cos, sin`) have the test-function martingale identity;
* `OHyp.ms_props`: `Ms` is adapted and a.s. bounded on bounded time intervals;
* `OHyp.adapted_phase`, `OHyp.phase_eq_Wd`: the phase is adapted and a.s. equal to `θ·W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.SourceProcess.Stochastic.Dyson.Angular

/-- **The six facts used by the orthogonality chain**, for a driving path `Wp Y` and a
process `Ms`. -/
structure OHyp {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (Ms : ℝ≥0 → Ω → ℝ) : Prop where
  zre : ∀ (θ : Fin N → ℝ) {h h' : ℝ → ℝ}, Trig h h' → (∀ x, |h x| ≤ 1) →
    TestMart Q 𝓕 (fun u ω => Real.exp (cθ θ * u) * h (phase θ Y u ω))
  zrems : ∀ (θ : Fin N → ℝ) {h h' : ℝ → ℝ}, Trig h h' → (∀ x, |h x| ≤ 1) →
    TestMart Q 𝓕 (fun u ω => Real.exp (cθ θ * u) * h (phase θ Y u ω) * Ms u ω)
  ms_props : (∀ t, StronglyMeasurable[𝓕 t] (Ms t)) ∧
    ∀ T : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ r ≤ T, |Ms r ω| ≤ C
  adapted_phase : ∀ (θ : Fin N → ℝ) (u : ℝ≥0),
    StronglyMeasurable[𝓕 u] fun ω => phase θ Y u ω
  phase_eq_Wd : ∀ θ : Fin N → ℝ, ∀ᵐ ω ∂Q, ∀ u, phase θ Y u ω = Wd θ Y u ω

/-- `D_u = Ms_u - Ms_0`. -/
def Dq {Ω : Type} (Ms : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ := Ms u ω - Ms 0 ω

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {Y : ℝ≥0 → Ω → Fin (N + N) → ℝ} {Ms : ℝ≥0 → Ω → ℝ}

theorem OHyp.testMartC_Z (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) :
    TestMartC Q (𝓕) (fun u ω => ((Real.exp (cθ θ * u) : ℝ) : ℂ) *
      cexp ((phase θ (Y) u ω : ℂ) * I)) := by
  have h := testMartC_of_re_im (H.zre θ trig_cos fun x => Real.abs_cos_le_one x)
    (H.zre θ trig_sin fun x => Real.abs_sin_le_one x)
  convert h using 3 with u ω
  rw [Complex.exp_mul_I]; push_cast; ring

theorem OHyp.testMartC_ZMs (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) :
    TestMartC Q (𝓕) (fun u ω => ((Real.exp (cθ θ * u) : ℝ) : ℂ) *
      cexp ((phase θ (Y) u ω : ℂ) * I) *
        ((Ms u ω : ℝ) : ℂ)) := by
  have h := testMartC_of_re_im (H.zrems θ trig_cos fun x => Real.abs_cos_le_one x)
    (H.zrems θ trig_sin fun x => Real.abs_sin_le_one x)
  convert h using 3 with u ω
  rw [Complex.exp_mul_I]; push_cast; ring

theorem OHyp.adapted_test (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) {r : ℝ≥0}
    {ζ : Ω → ℂ} (hζ : StronglyMeasurable[𝓕 r] ζ) (c : ℝ) :
    StronglyMeasurable[𝓕 r] fun ω =>
      ζ ω * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(phase θ (Y) r ω : ℂ) * I) := by
  have hp := H.adapted_phase θ r
  have : Continuous fun x : ℝ => cexp (-(x : ℂ) * I) := by fun_prop
  exact (hζ.mul stronglyMeasurable_const).mul (this.comp_stronglyMeasurable hp)

/-- **Gaussian increments of `W`, independent of the past.** -/
theorem OHyp.E1 (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) {r t : ℝ≥0}
    (hrt : r ≤ t) {ζ : Ω → ℂ} (hζ : StronglyMeasurable[𝓕 r] ζ) {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    ∫ ω, ζ ω * cexp (((Wd θ (Y) t ω - Wd θ (Y) r ω : ℝ) : ℂ) * I) ∂Q =
      (∫ ω, ζ ω ∂Q) * ((Real.exp (-(cθ θ * ((t : ℝ) - r))) : ℝ) : ℂ) := by
  set c := cθ θ * (t : ℝ)
  set η : Ω → ℂ := fun ω => ζ ω * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(phase θ (Y) r ω : ℂ) * I)
  have hη := H.adapted_test θ hζ c
  have hηb : ∀ᵐ ω ∂Q, ‖η ω‖ ≤ C * Real.exp (-c) := hC.mono fun ω h => norm_test h c _
  have key := (H.testMartC_Z θ).2 r t hrt η hη _ hηb
  calc ∫ ω, ζ ω * cexp (((Wd θ (Y) t ω - Wd θ (Y) r ω : ℝ) : ℂ) * I) ∂Q
      = ∫ ω, η ω * (((Real.exp (cθ θ * t) : ℝ) : ℂ) * cexp ((phase θ (Y) t ω : ℂ) * I)) ∂Q := by
        refine integral_congr_ae ?_
        filter_upwards [H.phase_eq_Wd θ] with ω hω
        simp only [η, c]
        rw [← hω t, ← hω r, ← cexp_combine (phase θ (Y) t ω)
          (phase θ (Y) r ω) (cθ θ * t)]
        ring
    _ = ∫ ω, η ω * (((Real.exp (cθ θ * r) : ℝ) : ℂ) * cexp ((phase θ (Y) r ω : ℂ) * I)) ∂Q := key
    _ = ∫ ω, ζ ω * ((Real.exp (-(cθ θ * ((t : ℝ) - r))) : ℝ) : ℂ) ∂Q := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [η, c, Complex.ofReal_exp]
        rw [mul_assoc, mul_assoc]
        congr 1
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1; push_cast; ring
    _ = _ := integral_mul_const _ _

/-- **Orthogonality of the eigenvalue noise and the angular martingale.** -/
theorem OHyp.E2 (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) {r t : ℝ≥0}
    (hrt : r ≤ t) {ζ : Ω → ℂ} (hζ : StronglyMeasurable[𝓕 r] ζ) {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    ∫ ω, ζ ω * cexp (((Wd θ (Y) t ω - Wd θ (Y) r ω : ℝ) : ℂ) * I) *
      ((Ms t ω -
        Ms r ω : ℝ) : ℂ) ∂Q = 0 := by
  set c := cθ θ * (t : ℝ)
  set η : Ω → ℂ := fun ω => ζ ω * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(phase θ (Y) r ω : ℂ) * I)
  set Z : ℝ≥0 → Ω → ℂ := fun u ω => ((Real.exp (cθ θ * u) : ℝ) : ℂ) * cexp ((phase θ (Y) u ω : ℂ) * I)
  have hη := H.adapted_test θ hζ c
  have hηb : ∀ᵐ ω ∂Q, ‖η ω‖ ≤ C * Real.exp (-c) := hC.mono fun ω h => norm_test h c _
  obtain ⟨hMsad, hMsb⟩ := H.ms_props
  obtain ⟨CM, hCM⟩ := hMsb r
  have hη2 : StronglyMeasurable[𝓕 r] fun ω => η ω * ((Ms r ω : ℝ) : ℂ) :=
    hη.mul (Complex.continuous_ofReal.comp_stronglyMeasurable (hMsad r))
  have hη2b : ∀ᵐ ω ∂Q, ‖η ω * ((Ms r ω : ℝ) : ℂ)‖ ≤ C * Real.exp (-c) * CM := by
    filter_upwards [hηb, hCM] with ω h1 h2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul h1 (h2 r le_rfl) (abs_nonneg _) ((norm_nonneg _).trans h1)
  have k1 := (H.testMartC_ZMs θ).2 r t hrt η hη _ hηb
  have k2 := (H.testMartC_Z θ).2 r t hrt _ hη2 _ hη2b
  have i1 : ∀ u, Integrable (fun ω => η ω * (Z u ω * ((Ms u ω : ℝ) : ℂ))) Q := fun u =>
    ((H.testMartC_ZMs θ).1 u).bdd_mul
      (hη.mono ((𝓕).le r)).aestronglyMeasurable hηb |>.congr
      (ae_of_all _ fun ω => by simp only [Z]; ring)
  have i2 : ∀ u, Integrable (fun ω => η ω * ((Ms r ω : ℝ) : ℂ) * Z u ω) Q := fun u =>
    ((H.testMartC_Z θ).1 u).bdd_mul
      (hη2.mono ((𝓕).le r)).aestronglyMeasurable hη2b
  have e : (fun ω => ζ ω * cexp (((Wd θ (Y) t ω - Wd θ (Y) r ω : ℝ) : ℂ) * I) *
      ((Ms t ω - Ms r ω : ℝ) : ℂ)) =ᵐ[Q]
      fun ω => η ω * (Z t ω * ((Ms t ω : ℝ) : ℂ)) - η ω * ((Ms r ω : ℝ) : ℂ) * Z t ω := by
    filter_upwards [H.phase_eq_Wd θ] with ω hω
    simp only [η, Z, c]
    rw [← hω t, ← hω r, ← cexp_combine (phase θ (Y) t ω)
      (phase θ (Y) r ω) (cθ θ * t)]
    push_cast; ring
  rw [integral_congr_ae e, integral_sub (i1 t) (i2 t)]
  have k1' : ∫ ω, η ω * (Z t ω * ((Ms t ω : ℝ) : ℂ)) ∂Q = ∫ ω, η ω * (Z r ω * ((Ms r ω : ℝ) : ℂ)) ∂Q := by
    simpa only [Z, mul_assoc] using k1
  rw [k1', show (∫ ω, η ω * ((Ms r ω : ℝ) : ℂ) * Z t ω ∂Q) = ∫ ω, η ω * ((Ms r ω : ℝ) : ℂ) * Z r ω ∂Q
    from k2, ← integral_sub (i1 r) (i2 r)]
  have : (fun ω => η ω * (Z r ω * ((Ms r ω : ℝ) : ℂ)) -
      η ω * ((Ms r ω : ℝ) : ℂ) * Z r ω) =
      fun _ => (0 : ℂ) := funext fun ω => by ring
  rw [this]; simp

theorem OHyp.adapted_Wd (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) (u : ℝ≥0) :
    StronglyMeasurable[𝓕 u] fun ω => Wd θ (Y) u ω :=
  Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.mul (H.adapted_phase (Pi.single i 1) u)

theorem OHyp.sm_expInc (H : OHyp Q 𝓕 Y Ms) (θ : Fin N → ℝ) {r a : ℝ≥0}
    (hra : r ≤ a) : StronglyMeasurable[𝓕 a] fun ω =>
      cexp (((Wd θ (Y) a ω - Wd θ (Y) r ω : ℝ) : ℂ) * I) := by
  have h1 := H.adapted_Wd θ a
  have h2 := (H.adapted_Wd θ r).mono ((𝓕).mono hra)
  have : Continuous fun x : ℝ => cexp ((x : ℂ) * I) := by fun_prop
  exact this.comp_stronglyMeasurable (h1.sub h2)

theorem OHyp.sm_psum (H : OHyp Q 𝓕 Y Ms) (J : Finset ℝ≥0)
    (θ : ℝ≥0 → Fin N → ℝ) (r : ℝ≥0) :
    StronglyMeasurable fun ω => cexp ((psum (Y) J θ r ω : ℂ) * I) := by
  have : Continuous fun x : ℝ => cexp ((x : ℂ) * I) := by fun_prop
  refine this.comp_stronglyMeasurable (Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_)
  exact ((H.adapted_Wd (θ j) j).mono ((𝓕).le j)).sub
    ((H.adapted_Wd (θ j) r).mono ((𝓕).le r))

/-- Future exponential functionals of `W` factor out of `𝓕_r`. -/
theorem OHyp.F1 (H : OHyp Q 𝓕 Y Ms) (J : Finset ℝ≥0) :
    ∀ r : ℝ≥0, (∀ j ∈ J, r ≤ j) → ∀ θ : ℝ≥0 → Fin N → ℝ, ∃ γ : ℂ, ∀ ζ : Ω → ℂ,
      StronglyMeasurable[𝓕 r] ζ → ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) →
        ∫ ω, ζ ω * cexp ((psum (Y) J θ r ω : ℂ) * I) ∂Q = γ * ∫ ω, ζ ω ∂Q := by
  induction J using Finset.induction_on_min with
  | empty => exact fun r _ θ => ⟨1, fun ζ _ _ _ => by simp [psum]⟩
  | insert a J hlt ih =>
    intro r hr θ
    have ha : a ∉ J := fun h => lt_irrefl a (hlt a h)
    obtain ⟨γ, hγ⟩ := ih a (fun j hj => (hlt j hj).le) θ
    have hra : r ≤ a := hr a (Finset.mem_insert_self a J)
    set Θ := ∑ j ∈ insert a J, θ j
    refine ⟨γ * ((Real.exp (-(cθ Θ * ((a : ℝ) - r))) : ℝ) : ℂ), fun ζ hζ C hC => ?_⟩
    have hζ' := (hζ.mono ((𝓕).mono hra)).mul (H.sm_expInc Θ hra)
    have hC' : ∀ᵐ ω ∂Q, ‖ζ ω * cexp (((Wd Θ (Y) a ω -
        Wd Θ (Y) r ω : ℝ) : ℂ) * I)‖ ≤ C := hC.mono fun ω h => by
      rw [norm_mul, norm_cexp_mul_I, mul_one]; exact h
    have e : ∀ ω, ζ ω * cexp ((psum (Y) (insert a J) θ r ω : ℂ) * I) =
        (ζ ω * cexp (((Wd Θ (Y) a ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I)) *
          cexp ((psum (Y) J θ a ω : ℂ) * I) := fun ω => by
      rw [psum_insert _ ha, Complex.ofReal_add, add_mul, Complex.exp_add]; ring
    simp_rw [e]
    rw [hγ (fun ω => ζ ω * cexp (((Wd Θ (Y) a ω -
        Wd Θ (Y) r ω : ℝ) : ℂ) * I)) hζ' C hC', H.E1 Θ hra hζ hC]; ring

/-- The stopped angular martingale is orthogonal to future exponentials of `W`. -/
theorem OHyp.F2 [IsProbabilityMeasure Q] (H : OHyp Q 𝓕 Y Ms) (J : Finset ℝ≥0) :
    ∀ r : ℝ≥0, (∀ j ∈ J, r ≤ j) → ∀ θ : ℝ≥0 → Fin N → ℝ, ∀ ζ : Ω → ℂ,
      StronglyMeasurable[𝓕 r] ζ → ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) → ∀ u : ℝ≥0,
        ∫ ω, ζ ω * cexp ((psum (Y) J θ r ω : ℂ) * I) *
          ((Ms u ω -
            Ms (min u r) ω : ℝ) : ℂ) ∂Q = 0 := by
  obtain ⟨hMsad, hMsb⟩ := H.ms_props
  -- the two-time increment lemma
  have key : ∀ r a : ℝ≥0, r ≤ a → ∀ Θ : Fin N → ℝ, ∀ ζ : Ω → ℂ,
      StronglyMeasurable[𝓕 r] ζ → ∀ C, (∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) → ∀ u : ℝ≥0,
      ∫ ω, ζ ω * cexp (((Wd Θ (Y) a ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I) *
        ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) ∂Q = 0 := by
    intro r a hra Θ ζ hζ C hC u
    rcases le_total u r with hur | hru
    · simp [min_eq_left hur, min_eq_left (hur.trans hra)]
    rcases le_total a u with hau | hua
    · rw [min_eq_right hau, min_eq_right hru]; exact H.E2 Θ hra hζ hC
    · rw [min_eq_left hua, min_eq_right hru]
      have hζ' : StronglyMeasurable[𝓕 u] fun ω => ζ ω *
          cexp (((Wd Θ (Y) u ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I) *
            ((Ms u ω - Ms r ω : ℝ) : ℂ) := by
        refine ((hζ.mono ((𝓕).mono hru)).mul (H.sm_expInc Θ hru)).mul ?_
        exact Complex.continuous_ofReal.comp_stronglyMeasurable
          ((hMsad u).sub ((hMsad r).mono ((𝓕).mono hru)))
      obtain ⟨CM, hCM⟩ := hMsb u
      have hC' : ∀ᵐ ω ∂Q, ‖ζ ω * cexp (((Wd Θ (Y) u ω -
          Wd Θ (Y) r ω : ℝ) : ℂ) * I) * ((Ms u ω - Ms r ω : ℝ) : ℂ)‖ ≤ C * (CM + CM) := by
        filter_upwards [hC, hCM] with ω h1 h2
        rw [norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 u le_rfl) (h2 r hru)))
          (abs_nonneg _) ((norm_nonneg _).trans h1)
      have e : ∀ ω, ζ ω * cexp (((Wd Θ (Y) a ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I)
          * ((Ms u ω - Ms r ω : ℝ) : ℂ) = (ζ ω * cexp (((Wd Θ (Y) u ω -
            Wd Θ (Y) r ω : ℝ) : ℂ) * I) * ((Ms u ω - Ms r ω : ℝ) : ℂ)) *
          cexp (((Wd Θ (Y) a ω - Wd Θ (Y) u ω : ℝ) : ℂ) * I) := fun ω => by
        rw [show ((Wd Θ (Y) a ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I =
          ((Wd Θ (Y) u ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I +
            ((Wd Θ (Y) a ω - Wd Θ (Y) u ω : ℝ) : ℂ) * I by push_cast; ring,
          Complex.exp_add]; ring
      simp_rw [e]
      rw [H.E1 Θ hua hζ' hC', H.E2 Θ hru hζ hC, zero_mul]
  induction J using Finset.induction_on_min with
  | empty =>
    intro r _ θ ζ hζ C hC u
    have := key r (max u r) (le_max_right _ _) 0 ζ hζ C hC u
    simpa [psum, Wd, min_eq_left (le_max_left u r)] using this
  | insert a J hlt ih =>
    intro r hr θ ζ hζ C hC u
    have ha : a ∉ J := fun h => lt_irrefl a (hlt a h)
    have hra : r ≤ a := hr a (Finset.mem_insert_self a J)
    set Θ := ∑ j ∈ insert a J, θ j
    set ζ' : Ω → ℂ := fun ω => ζ ω *
      cexp (((Wd Θ (Y) a ω - Wd Θ (Y) r ω : ℝ) : ℂ) * I)
    have hζ' : StronglyMeasurable[𝓕 a] ζ' :=
      (hζ.mono ((𝓕).mono hra)).mul (H.sm_expInc Θ hra)
    have hC' : ∀ᵐ ω ∂Q, ‖ζ' ω‖ ≤ C := hC.mono fun ω h => by
      simp only [ζ']; rw [norm_mul, norm_cexp_mul_I, mul_one]; exact h
    obtain ⟨CM, hCM⟩ := hMsb u
    have hD : StronglyMeasurable[𝓕 a] fun ω =>
        ζ' ω * ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) :=
      hζ'.mul (Complex.continuous_ofReal.comp_stronglyMeasurable
        (((hMsad _).mono ((𝓕).mono (min_le_right _ _))).sub
          ((hMsad _).mono ((𝓕).mono ((min_le_right _ _).trans hra)))))
    have hDb : ∀ᵐ ω ∂Q, ‖ζ' ω * ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ)‖ ≤ C * (CM + CM) := by
      filter_upwards [hC', hCM] with ω h1 h2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 _ (min_le_left _ _))
        (h2 _ (min_le_left _ _)))) (abs_nonneg _) ((norm_nonneg _).trans h1)
    obtain ⟨γ, hγ⟩ := H.F1 J a (fun j hj => (hlt j hj).le) θ
    have hsm : ∀ v, AEStronglyMeasurable (fun ω => ((Ms v ω : ℝ) : ℂ)) Q := fun v =>
      (Complex.continuous_ofReal.comp_stronglyMeasurable
        ((hMsad v).mono ((𝓕).le v))).aestronglyMeasurable
    have hPs := (H.sm_psum J θ a).aestronglyMeasurable (μ := Q)
    have hz' := (hζ'.mono ((𝓕).le a)).aestronglyMeasurable (μ := Q)
    have i1 : Integrable (fun ω => ζ' ω * cexp ((psum (Y) J θ a ω : ℂ) * I) *
        ((Ms u ω - Ms (min u a) ω : ℝ) : ℂ)) Q := by
      refine integrable_bdd ((hz'.mul hPs).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hMsad u).mono ((𝓕).le u)).aestronglyMeasurable.sub
          ((hMsad _).mono ((𝓕).le _)).aestronglyMeasurable))) (C := C * (CM + CM)) ?_
      filter_upwards [hC', hCM] with ω h1 h2
      rw [norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 u le_rfl) (h2 _ (min_le_left _ _))))
        (abs_nonneg _) ((norm_nonneg _).trans h1)
    have i2 : Integrable (fun ω => ζ' ω * cexp ((psum (Y) J θ a ω : ℂ) * I) *
        ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ)) Q := by
      refine integrable_bdd ((hz'.mul hPs).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((hMsad _).mono ((𝓕).le _)).aestronglyMeasurable.sub
          ((hMsad _).mono ((𝓕).le _)).aestronglyMeasurable))) (C := C * (CM + CM)) ?_
      filter_upwards [hC', hCM] with ω h1 h2
      rw [norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul h1 ((abs_sub _ _).trans (add_le_add (h2 _ (min_le_left _ _))
        (h2 _ (min_le_left _ _)))) (abs_nonneg _) ((norm_nonneg _).trans h1)
    have e : ∀ ω, ζ ω * cexp ((psum (Y) (insert a J) θ r ω : ℂ) * I) *
        ((Ms u ω - Ms (min u r) ω : ℝ) : ℂ) =
        ζ' ω * cexp ((psum (Y) J θ a ω : ℂ) * I) * ((Ms u ω - Ms (min u a) ω : ℝ) : ℂ) +
        ζ' ω * cexp ((psum (Y) J θ a ω : ℂ) * I) *
          ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) := fun ω => by
      simp only [ζ']
      rw [psum_insert _ ha, Complex.ofReal_add, add_mul, Complex.exp_add]; push_cast; ring
    simp_rw [e]
    rw [integral_add i1 i2, ih a (fun j hj => (hlt j hj).le) θ ζ' hζ' C hC' u, zero_add]
    have e2 : ∀ ω, ζ' ω * cexp ((psum (Y) J θ a ω : ℂ) * I) *
        ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ) = (ζ' ω *
          ((Ms (min u a) ω - Ms (min u r) ω : ℝ) : ℂ)) *
          cexp ((psum (Y) J θ a ω : ℂ) * I) := fun ω => by ring
    simp_rw [e2]
    rw [hγ _ hD _ hDb, key r a hra Θ ζ hζ C hC u, mul_zero]

end BlockBand.SourceProcess.Stochastic.ComplexAngular
