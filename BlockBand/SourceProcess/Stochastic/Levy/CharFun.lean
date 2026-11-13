module
public import BlockBand.SourceProcess.Stochastic.Levy.Martingale
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Lévy's characterization: the conditional characteristic function

For a continuous semimartingale `M` in `ℝ^d` with characteristics `(0, I)` on an arbitrary
filtered probability space, `s ≤ t`, `A ∈ 𝓖_s` and `u ∈ ℝ^d`:

* `setIntegral_cos_increment`: `∫_A cos⟨u, M_t - M_s⟩ = Q(A) e^{-|u|²(t-s)/2}`;
* `setIntegral_sin_increment`: `∫_A sin⟨u, M_t - M_s⟩ = 0`;
* `setIntegral_cexp_increment`: `∫_A exp(i⟨u, M_t - M_s⟩) = Q(A) e^{-|u|²(t-s)/2}`;
* `condExp_cexp_increment`: `E[exp(i⟨u, M_t - M_s⟩) | 𝓖_s] = e^{-|u|²(t-s)/2}` a.s.

Proof: the weights `1_A cos⟨u, M_s⟩`, `1_A sin⟨u, M_s⟩` are `𝓖_s`-measurable and bounded by
one, so `integral_mul_levyProc` (for `θ = 0` and `θ = π/2`) and the addition formulas give
`e^{|u|²t/2} ∫_A cos⟨u, M_t - M_s⟩ = e^{|u|²s/2} ∫_A cos 0` and the sine analogue.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

universe u

variable {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {M : ℝ≥0 → Ω → Fin d → ℝ}

/-- `⟨u, x⟩`. -/
def pairing (u x : Fin d → ℝ) : ℝ := ∑ i, u i * x i

theorem pairing_sub (u x y : Fin d → ℝ) : pairing u (x - y) = pairing u x - pairing u y := by
  simp [pairing, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem pairing_zero (u : Fin d → ℝ) : pairing u 0 = 0 := by simp [pairing]

theorem continuous_pairing (u : Fin d → ℝ) : Continuous (pairing u) := by
  unfold pairing; fun_prop

omit [MeasurableSpace Ω] in
theorem levyProc_zero_eq (u : Fin d → ℝ) (t : ℝ≥0) (ω : Ω) :
    levyProc u 0 M t ω = Real.exp (sqNorm u / 2 * t) * Real.cos (pairing u (M t ω)) := by
  simp [levyProc, levyPhi, pairing]

omit [MeasurableSpace Ω] in
theorem levyProc_pi_div_two_eq (u : Fin d → ℝ) (t : ℝ≥0) (ω : Ω) :
    levyProc u (Real.pi / 2) M t ω =
      Real.exp (sqNorm u / 2 * t) * Real.sin (pairing u (M t ω)) := by
  simp [levyProc, levyPhi, pairing, Real.cos_sub_pi_div_two]

theorem integrable_mul_levyProc (hM : ∀ t, StronglyMeasurable[𝓖 t] (M t)) (u : Fin d → ℝ)
    (θ : ℝ) {g : Ω → ℝ} (hg : StronglyMeasurable g) (hgb : ∀ ω, |g ω| ≤ 1) (r : ℝ≥0) :
    Integrable (fun ω => g ω * levyProc u θ M r ω) Q := by
  refine Integrable.of_bound (hg.mul ((measurable_levyProc hM u θ r).mono
    (𝓖.le r))).aestronglyMeasurable (Real.exp (sqNorm u / 2 * r)) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hgb ω) |>.trans (abs_levyProc_le u θ M le_rfl ω)

/-- The two weights `1_A cos⟨u, M_s⟩` and `1_A sin⟨u, M_s⟩`. -/
theorem weight_props (hM : ∀ t, StronglyMeasurable[𝓖 t] (M t)) (u : Fin d → ℝ) {s : ℝ≥0}
    {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) (f : ℝ → ℝ) (hf : Continuous f)
    (hfb : ∀ x, |f x| ≤ 1) :
    StronglyMeasurable[𝓖 s] (A.indicator fun ω => f (pairing u (M s ω))) ∧
      ∀ ω, |A.indicator (fun ω => f (pairing u (M s ω))) ω| ≤ 1 := by
  refine ⟨(((hf.comp (continuous_pairing u)).comp_stronglyMeasurable (hM s))).indicator hA,
    fun ω => ?_⟩
  by_cases h : ω ∈ A
  · rw [indicator_of_mem h]; exact hfb _
  · rw [indicator_of_notMem h]; simp

/-- The combined identity behind both set integrals: for `ε = ±1` and the pair of weights
`(g₁, g₂)`, the integral of `g₁ φ₀(r) + ε g₂ φ_{π/2}(r)` does not depend on `r ∈ {s, t}`. -/
theorem integral_pair_eq (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    (u : Fin d → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A)
    (θ₁ θ₂ : ℝ) (f₁ f₂ : ℝ → ℝ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hb₁ : ∀ x, |f₁ x| ≤ 1) (hb₂ : ∀ x, |f₂ x| ≤ 1) (ε : ℝ) :
    ∫ ω, (A.indicator (fun ω => f₁ (pairing u (M s ω))) ω * levyProc u θ₁ M t ω +
        ε * (A.indicator (fun ω => f₂ (pairing u (M s ω))) ω * levyProc u θ₂ M t ω)) ∂Q =
      ∫ ω, (A.indicator (fun ω => f₁ (pairing u (M s ω))) ω * levyProc u θ₁ M s ω +
        ε * (A.indicator (fun ω => f₂ (pairing u (M s ω))) ω * levyProc u θ₂ M s ω)) ∂Q := by
  obtain ⟨hg₁, hg₁b⟩ := weight_props hM.adapted u hA f₁ hf₁ hb₁
  obtain ⟨hg₂, hg₂b⟩ := weight_props hM.adapted u hA f₂ hf₂ hb₂
  have hi := fun θ g (hg : StronglyMeasurable[𝓖 s] g) hgb r =>
    integrable_mul_levyProc (Q := Q) hM.adapted u θ (hg.mono (𝓖.le s)) hgb r
  rw [integral_add (hi θ₁ _ hg₁ hg₁b t) ((hi θ₂ _ hg₂ hg₂b t).const_mul ε),
    integral_add (hi θ₁ _ hg₁ hg₁b s) ((hi θ₂ _ hg₂ hg₂b s).const_mul ε),
    integral_const_mul, integral_const_mul,
    integral_mul_levyProc hM u θ₁ hst hg₁ hg₁b, integral_mul_levyProc hM u θ₂ hst hg₂ hg₂b]

theorem measurableSet_of_filtration {s : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    MeasurableSet A := 𝓖.le s A hA

/-- **Cosine part.** `∫_A cos⟨u, M_t - M_s⟩ dQ = Q(A) e^{-|u|²(t-s)/2}`. -/
theorem setIntegral_cos_increment
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    (u : Fin d → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Real.cos (pairing u (M t ω - M s ω)) ∂Q =
      Q.real A * Real.exp (-(sqNorm u / 2 * ((t : ℝ) - s))) := by
  have h := integral_pair_eq hM u hst hA 0 (Real.pi / 2) Real.cos Real.sin Real.continuous_cos
    Real.continuous_sin Real.abs_cos_le_one Real.abs_sin_le_one 1
  have hpt : ∀ r : ℝ≥0, ∀ ω, A.indicator (fun ω => Real.cos (pairing u (M s ω))) ω *
      levyProc u 0 M r ω + 1 * (A.indicator (fun ω => Real.sin (pairing u (M s ω))) ω *
        levyProc u (Real.pi / 2) M r ω) = Real.exp (sqNorm u / 2 * r) *
      A.indicator (fun ω => Real.cos (pairing u (M r ω - M s ω))) ω := fun r ω => by
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, levyProc_zero_eq, levyProc_pi_div_two_eq, pairing_sub,
        Real.cos_sub]
      ring
    · simp [indicator_of_notMem hω]
  simp only [hpt, integral_const_mul, integral_indicator (measurableSet_of_filtration hA),
    sub_self, pairing_zero, Real.cos_zero, setIntegral_const, smul_eq_mul, mul_one] at h
  calc ∫ ω in A, Real.cos (pairing u (M t ω - M s ω)) ∂Q
      = Real.exp (-(sqNorm u / 2 * t)) * (Real.exp (sqNorm u / 2 * t) *
          ∫ ω in A, Real.cos (pairing u (M t ω - M s ω)) ∂Q) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-(sqNorm u / 2 * t)) * (Real.exp (sqNorm u / 2 * s) * Q.real A) := by rw [h]
    _ = _ := by
        rw [show -(sqNorm u / 2 * ((t : ℝ) - s)) = -(sqNorm u / 2 * t) + sqNorm u / 2 * s by ring,
          Real.exp_add]
        ring

/-- **Sine part.** `∫_A sin⟨u, M_t - M_s⟩ dQ = 0`. -/
theorem setIntegral_sin_increment
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    (u : Fin d → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Real.sin (pairing u (M t ω - M s ω)) ∂Q = 0 := by
  have h := integral_pair_eq hM u hst hA (Real.pi / 2) 0 Real.cos Real.sin Real.continuous_cos
    Real.continuous_sin Real.abs_cos_le_one Real.abs_sin_le_one (-1)
  have hpt : ∀ r : ℝ≥0, ∀ ω, A.indicator (fun ω => Real.cos (pairing u (M s ω))) ω *
      levyProc u (Real.pi / 2) M r ω + -1 * (A.indicator (fun ω => Real.sin (pairing u (M s ω))) ω *
        levyProc u 0 M r ω) = Real.exp (sqNorm u / 2 * r) *
      A.indicator (fun ω => Real.sin (pairing u (M r ω - M s ω))) ω := fun r ω => by
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, levyProc_zero_eq, levyProc_pi_div_two_eq, pairing_sub,
        Real.sin_sub]
      ring
    · simp [indicator_of_notMem hω]
  simp only [hpt, integral_const_mul, integral_indicator (measurableSet_of_filtration hA),
    sub_self, pairing_zero, Real.sin_zero, integral_zero, mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (Real.exp_pos _).ne'

/-- **Lévy: set-integral form of the conditional characteristic function.** -/
theorem setIntegral_cexp_increment
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    (u : Fin d → ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, Complex.exp ((pairing u (M t ω - M s ω) : ℂ) * Complex.I) ∂Q =
      ((Q.real A * Real.exp (-(sqNorm u / 2 * ((t : ℝ) - s))) : ℝ) : ℂ) := by
  have hmeas : Measurable fun ω => pairing u (M t ω - M s ω) :=
    (continuous_pairing u).measurable.comp
      (((hM.adapted t).mono (𝓖.le t)).measurable.sub ((hM.adapted s).mono (𝓖.le s)).measurable)
  have hm : ∀ f : ℝ → ℝ, Continuous f → (∀ x, |f x| ≤ 1) →
      Integrable (fun ω => f (pairing u (M t ω - M s ω))) (Q.restrict A) := fun f hf hfb =>
    Integrable.of_bound (hf.measurable.comp hmeas).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfb _)
  have e : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) =
      ((Real.cos x : ℝ) : ℂ) + ((Real.sin x : ℝ) : ℂ) * Complex.I := fun x => by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp_rw [e]
  rw [integral_add (hm _ Real.continuous_cos Real.abs_cos_le_one).ofReal
      ((hm _ Real.continuous_sin Real.abs_sin_le_one).ofReal.mul_const _),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, setIntegral_cos_increment hM u hst hA,
    setIntegral_sin_increment hM u hst hA]
  simp

/-- **Lévy: conditional characteristic function.** For `s ≤ t`,
`E[exp(i⟨u, M_t - M_s⟩) | 𝓖_s] = exp(-|u|²(t-s)/2)` `Q`-a.s. -/
theorem condExp_cexp_increment
    (hM : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) (fun _ _ => 1))
    (u : Fin d → ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    Q[fun ω => Complex.exp ((pairing u (M t ω - M s ω) : ℂ) * Complex.I) | 𝓖 s] =ᵐ[Q]
      fun _ => ((Real.exp (-(sqNorm u / 2 * ((t : ℝ) - s))) : ℝ) : ℂ) := by
  have hmeas : Measurable fun ω => pairing u (M t ω - M s ω) :=
    (continuous_pairing u).measurable.comp
      (((hM.adapted t).mono (𝓖.le t)).measurable.sub ((hM.adapted s).mono (𝓖.le s)).measurable)
  have hint : Integrable (fun ω => Complex.exp ((pairing u (M t ω - M s ω) : ℂ) * Complex.I)) Q :=
    Integrable.of_bound ((by fun_prop : Continuous fun x : ℝ =>
      Complex.exp ((x : ℂ) * Complex.I)).measurable.comp hmeas).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) hint
    (fun _ _ _ => integrableOn_const (by simp)) (fun A hA _ => ?_)
    stronglyMeasurable_const.aestronglyMeasurable).symm
  rw [setIntegral_cexp_increment hM u hst hA, setIntegral_const]
  simp [Measure.real, Complex.real_smul, mul_comm]

end BlockBand.SourceProcess.Stochastic.Levy
