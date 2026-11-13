module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularReal

/-!
# Independent Gaussian increments of `W` and their orthogonality to the angular martingale

* `Hyp.E1`: `E[ζ e^{iθ·(W_t - W_r)}] = e^{-|θ|²(t-r)/(2N)} E[ζ]` (Lévy: the eigenvalue noise is a
  Brownian motion for `𝓕`);
* `Hyp.E2`: `E[ζ e^{iθ·(W_t - W_r)} (Ms_t - Ms_r)] = 0` (the eigenvalue noise and the angular
  martingale are orthogonal: zero `λ`–`X` covariance).
Proof: the complex martingales `Z = e^{c_θ u + iθ·W_u}` and `Z · Ms`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

theorem cexp_combine (a b c : ℝ) :
    ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(b : ℂ) * I) * (((Real.exp c : ℝ) : ℂ) * cexp (a * I)) =
      cexp (((a - b : ℝ) : ℂ) * I) := by
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1; push_cast; ring

theorem norm_test {ζ : ℂ} {C : ℝ} (hζ : ‖ζ‖ ≤ C) (c b : ℝ) :
    ‖ζ * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(b : ℂ) * I)‖ ≤ C * Real.exp (-c) := by
  rw [norm_mul, norm_mul, show -(b : ℂ) * I = ((-b : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_one]
  exact mul_le_mul_of_nonneg_right hζ (Real.exp_pos _).le

theorem Hyp.testMartC_Z (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) :
    TestMartC Q (shiftFiltration 𝓖 s) (fun u ω => ((Real.exp (cθ θ * u) : ℝ) : ℂ) *
      cexp ((phase θ (Yst N q G F s) u ω : ℂ) * I)) := by
  have h := testMartC_of_re_im (H.testMart_Zre q θ trig_cos fun x => Real.abs_cos_le_one x)
    (H.testMart_Zre q θ trig_sin fun x => Real.abs_sin_le_one x)
  convert h using 3 with u ω
  rw [Complex.exp_mul_I]; push_cast; ring

theorem Hyp.testMartC_ZMs (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) :
    TestMartC Q (shiftFiltration 𝓖 s) (fun u ω => ((Real.exp (cθ θ * u) : ℝ) : ℂ) *
      cexp ((phase θ (Yst N q G F s) u ω : ℂ) * I) *
        ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) u ω : ℝ) : ℂ)) := by
  have h := testMartC_of_re_im (H.testMart_ZreMs q θ trig_cos fun x => Real.abs_cos_le_one x)
    (H.testMart_ZreMs q θ trig_sin fun x => Real.abs_sin_le_one x)
  convert h using 3 with u ω
  rw [Complex.exp_mul_I]; push_cast; ring

theorem Hyp.adapted_test (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) {r : ℝ≥0}
    {ζ : Ω → ℂ} (hζ : StronglyMeasurable[shiftFiltration 𝓖 s r] ζ) (c : ℝ) :
    StronglyMeasurable[shiftFiltration 𝓖 s r] fun ω =>
      ζ ω * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(phase θ (Yst N q G F s) r ω : ℂ) * I) := by
  have hp := H.adapted_phase q θ r
  have : Continuous fun x : ℝ => cexp (-(x : ℂ) * I) := by fun_prop
  exact (hζ.mul stronglyMeasurable_const).mul (this.comp_stronglyMeasurable hp)

/-- **Gaussian increments of `W`, independent of the past.** -/
theorem Hyp.E1 (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) {r t : ℝ≥0}
    (hrt : r ≤ t) {ζ : Ω → ℂ} (hζ : StronglyMeasurable[shiftFiltration 𝓖 s r] ζ) {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    ∫ ω, ζ ω * cexp (((Wd θ (Yst N q G F s) t ω - Wd θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) ∂Q =
      (∫ ω, ζ ω ∂Q) * ((Real.exp (-(cθ θ * ((t : ℝ) - r))) : ℝ) : ℂ) := by
  set c := cθ θ * (t : ℝ)
  set η : Ω → ℂ := fun ω => ζ ω * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(phase θ (Yst N q G F s) r ω : ℂ) * I)
  have hη := H.adapted_test q θ hζ c
  have hηb : ∀ᵐ ω ∂Q, ‖η ω‖ ≤ C * Real.exp (-c) := hC.mono fun ω h => norm_test h c _
  have key := (H.testMartC_Z q θ).2 r t hrt η hη _ hηb
  calc ∫ ω, ζ ω * cexp (((Wd θ (Yst N q G F s) t ω - Wd θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) ∂Q
      = ∫ ω, η ω * (((Real.exp (cθ θ * t) : ℝ) : ℂ) * cexp ((phase θ (Yst N q G F s) t ω : ℂ) * I)) ∂Q := by
        refine integral_congr_ae ?_
        filter_upwards [H.phase_eq_Wd q θ] with ω hω
        simp only [η, c]
        rw [← hω t, ← hω r, ← cexp_combine (phase θ (Yst N q G F s) t ω)
          (phase θ (Yst N q G F s) r ω) (cθ θ * t)]
        ring
    _ = ∫ ω, η ω * (((Real.exp (cθ θ * r) : ℝ) : ℂ) * cexp ((phase θ (Yst N q G F s) r ω : ℂ) * I)) ∂Q := key
    _ = ∫ ω, ζ ω * ((Real.exp (-(cθ θ * ((t : ℝ) - r))) : ℝ) : ℂ) ∂Q := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only [η, c, Complex.ofReal_exp]
        rw [mul_assoc, mul_assoc]
        congr 1
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1; push_cast; ring
    _ = _ := integral_mul_const _ _

/-- **Orthogonality of the eigenvalue noise and the angular martingale.** -/
theorem Hyp.E2 (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) {r t : ℝ≥0}
    (hrt : r ≤ t) {ζ : Ω → ℂ} (hζ : StronglyMeasurable[shiftFiltration 𝓖 s r] ζ) {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    ∫ ω, ζ ω * cexp (((Wd θ (Yst N q G F s) t ω - Wd θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) *
      ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) t ω -
        stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) ∂Q = 0 := by
  set c := cθ θ * (t : ℝ)
  set η : Ω → ℂ := fun ω => ζ ω * ((Real.exp (-c) : ℝ) : ℂ) * cexp (-(phase θ (Yst N q G F s) r ω : ℂ) * I)
  set Z : ℝ≥0 → Ω → ℂ := fun u ω => ((Real.exp (cθ θ * u) : ℝ) : ℂ) * cexp ((phase θ (Yst N q G F s) u ω : ℂ) * I)
  have hη := H.adapted_test q θ hζ c
  have hηb : ∀ᵐ ω ∂Q, ‖η ω‖ ≤ C * Real.exp (-c) := hC.mono fun ω h => norm_test h c _
  obtain ⟨-, hMsad, hMsb⟩ := H.ms_props (f := f) q
  obtain ⟨CM, hCM⟩ := hMsb r
  have hη2 : StronglyMeasurable[shiftFiltration 𝓖 s r] fun ω => η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) :=
    hη.mul (Complex.continuous_ofReal.comp_stronglyMeasurable (hMsad r))
  have hη2b : ∀ᵐ ω ∂Q, ‖η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ)‖ ≤ C * Real.exp (-c) * CM := by
    filter_upwards [hηb, hCM] with ω h1 h2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul h1 (h2 r le_rfl) (abs_nonneg _) ((norm_nonneg _).trans h1)
  have k1 := (H.testMartC_ZMs (f := f) q θ).2 r t hrt η hη _ hηb
  have k2 := (H.testMartC_Z q θ).2 r t hrt _ hη2 _ hη2b
  have i1 : ∀ u, Integrable (fun ω => η ω * (Z u ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) u ω : ℝ) : ℂ))) Q := fun u =>
    ((H.testMartC_ZMs (f := f) q θ).1 u).bdd_mul
      (hη.mono ((shiftFiltration 𝓖 s).le r)).aestronglyMeasurable hηb |>.congr
      (ae_of_all _ fun ω => by simp only [Z]; ring)
  have i2 : ∀ u, Integrable (fun ω => η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) * Z u ω) Q := fun u =>
    ((H.testMartC_Z q θ).1 u).bdd_mul
      (hη2.mono ((shiftFiltration 𝓖 s).le r)).aestronglyMeasurable hη2b
  have e : (fun ω => ζ ω * cexp (((Wd θ (Yst N q G F s) t ω - Wd θ (Yst N q G F s) r ω : ℝ) : ℂ) * I) *
      ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) t ω - stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ)) =ᵐ[Q]
      fun ω => η ω * (Z t ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) t ω : ℝ) : ℂ)) - η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) * Z t ω := by
    filter_upwards [H.phase_eq_Wd q θ] with ω hω
    simp only [η, Z, c]
    rw [← hω t, ← hω r, ← cexp_combine (phase θ (Yst N q G F s) t ω)
      (phase θ (Yst N q G F s) r ω) (cθ θ * t)]
    push_cast; ring
  rw [integral_congr_ae e, integral_sub (i1 t) (i2 t)]
  have k1' : ∫ ω, η ω * (Z t ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) t ω : ℝ) : ℂ)) ∂Q = ∫ ω, η ω * (Z r ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ)) ∂Q := by
    simpa only [Z, mul_assoc] using k1
  rw [k1', show (∫ ω, η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) * Z t ω ∂Q) = ∫ ω, η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) * Z r ω ∂Q
    from k2, ← integral_sub (i1 r) (i2 r)]
  have : (fun ω => η ω * (Z r ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ)) -
      η ω * ((stoppedProcess (Mt f (Yst N q G F s)) (sig N G F s n) r ω : ℝ) : ℂ) * Z r ω) =
      fun _ => (0 : ℂ) := funext fun ω => by ring
  rw [this]; simp

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
