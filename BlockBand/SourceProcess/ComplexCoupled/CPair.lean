module

public import BlockBand.SourceProcess.ComplexCoupled.Close

/-!
# Complex stopped martingales from an Itô pair

For an Itô process `Z = (F, H)` in `ℂ × ℂ` with zero drift and diffusion `φ = (φ₁, φ₂)`, and
an augmented stopping time `τ` such that every stopped functional integrand of `φ` is a native
integrand, there are complex `𝓖`-martingales `N` with `N_t = (F - F₀)^τ_t` a.s.
(`exists_martingale_fst`) and `N_t = ((F - F₀)(H - H₀) - ∫_0^· Σ_a φ₁φ₂)^τ_t` a.s.
(`exists_martingale_mul`). Route: the real coordinates `(Re F, Im F, Re H, Im H)` and
`hmm_coord`, `hmm_coord_pair`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale

/-- The four real coordinates `(Re z₁, Im z₁, Re z₂, Im z₂)`. -/
def c4 : ℂ × ℂ →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi fun i => ![Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ),
    Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ),
    Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ),
    Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)] i

theorem c4_apply (z : ℂ × ℂ) :
    c4 z 0 = z.1.re ∧ c4 z 1 = z.1.im ∧ c4 z 2 = z.2.re ∧ c4 z 3 = z.2.im := by
  simp [c4]

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ] {μ : Measure S} [IsProbabilityMeasure μ]
  {Z : ℝ≥0 → DriverSample S κ → ℂ × ℂ} {φ : κ → ℝ≥0 → DriverSample S κ → ℂ × ℂ}
  {τ : DriverSample S κ → WithTop ℝ≥0}

omit [MeasurableSpace S] [Fintype κ] in
theorem smCompensated_c4 (Z : ℝ≥0 → DriverSample S κ → ℂ × ℂ) (i : Fin 4) (t : ℝ≥0)
    (x : DriverSample S κ) :
    smCompensated (fun t x => c4 (Z t x)) (fun _ _ => c4 0) i t x =
      c4 (Z t x) i - c4 (Z 0 x) i := by
  simp [smCompensated]

omit [IsProbabilityMeasure μ] in
theorem coord_c4 (hG : ∀ (ℓ : ℂ × ℂ →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ φ))) (i : Fin 4) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand (coordFun i)
      (fun a t x => c4 (φ a t x)))) :=
  hG ((coordFun i).comp c4) T

/-- **The stopped first component.** -/
theorem exists_martingale_fst (hZ : IsNativeItoProcess μ Z (fun _ _ => 0) φ)
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (hG : ∀ (ℓ : ℂ × ℂ →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ φ))) :
    ∃ N : ℝ≥0 → DriverSample S κ → ℂ, Martingale N (driverAugmented (κ := κ) μ)
      (driverLaw (κ := κ) μ) ∧ ∀ t, N t =ᵐ[driverLaw (κ := κ) μ]
        stoppedProcess (fun t x => (Z t x).1 - (Z 0 x).1) τ t := by
  have hW := hZ.map_clm c4
  have h0 := hmm_coord hW hτ 0 (coord_c4 hG 0)
  have h1 := hmm_coord hW hτ 1 (coord_c4 hG 1)
  refine exists_martingale_re_im (hmm_congr h0 fun t => ae_of_all _ fun x => ?_)
    (hmm_congr h1 fun t => ae_of_all _ fun x => ?_) <;>
  simp only [stoppedProcess, smCompensated_c4 Z] <;> simp [c4]

/-- **The stopped compensated product.** -/
theorem exists_martingale_mul (hZ : IsNativeItoProcess μ Z (fun _ _ => 0) φ)
    (hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ)
    (hG : ∀ (ℓ : ℂ × ℂ →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ φ))) :
    ∃ N : ℝ≥0 → DriverSample S κ → ℂ, Martingale N (driverAugmented (κ := κ) μ)
      (driverLaw (κ := κ) μ) ∧ ∀ t, N t =ᵐ[driverLaw (κ := κ) μ]
        stoppedProcess (fun t x => ((Z t x).1 - (Z 0 x).1) * ((Z t x).2 - (Z 0 x).2) -
          ∫ s in Ioc (0 : ℝ) t, ∑ a, (φ a s.toNNReal x).1 * (φ a s.toNNReal x).2) τ t := by
  have hW := hZ.map_clm c4
  have hP := fun i j => hmm_coord_pair hW hτ i j (coord_c4 hG i) (coord_c4 hG j)
  obtain ⟨τn, -, hτl, hloc⟩ := hW.localizing
  have hI := ae_integrableOn_covOf hτl hloc
  set f : ℝ≥0 → DriverSample S κ → ℝ → ℂ := fun _ x s =>
    ∑ a, (φ a s.toNNReal x).1 * (φ a s.toNNReal x).2
  have hfre : ∀ x s, (f 0 x s).re = (∑ a, c4 (φ a s.toNNReal x) 0 * c4 (φ a s.toNNReal x) 2) -
      ∑ a, c4 (φ a s.toNNReal x) 1 * c4 (φ a s.toNNReal x) 3 := fun x s => by
    simp [f, c4, Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib]
  have hfim : ∀ x s, (f 0 x s).im = (∑ a, c4 (φ a s.toNNReal x) 0 * c4 (φ a s.toNNReal x) 3) +
      ∑ a, c4 (φ a s.toNNReal x) 1 * c4 (φ a s.toNNReal x) 2 := fun x s => by
    simp [f, c4, Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib]
  refine exists_martingale_re_im (hmm_congr (hmm_sub (hP 0 2) (hP 1 3)) fun t => ?_)
    (hmm_congr (hmm_add (hP 0 3) (hP 1 2)) fun t => ?_)
  · filter_upwards [hI] with x hx
    set r := stopTime (τ x) t
    have h02 := hx r 0 2
    have h13 := hx r 1 3
    have hint : IntegrableOn (f 0 x) (Ioc 0 r) :=
      (Integrable.re_im_iff (𝕜 := ℂ)).1
        ⟨(h02.sub h13).congr_fun (fun s _ => (hfre x s).symm) measurableSet_Ioc,
          ((hx r 0 3).add (hx r 1 2)).congr_fun (fun s _ => (hfim x s).symm) measurableSet_Ioc⟩
    simp only [stoppedProcess_eq_stopTime, smCompensated_c4 Z]
    have hc := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at hc
    rw [Complex.sub_re, ← hc]
    simp only [hfre, f]
    rw [integral_sub h02 h13]
    simp only [c4_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im]
    ring
  · filter_upwards [hI] with x hx
    set r := stopTime (τ x) t
    have h02 := hx r 0 2
    have h13 := hx r 1 3
    have hint : IntegrableOn (f 0 x) (Ioc 0 r) :=
      (Integrable.re_im_iff (𝕜 := ℂ)).1
        ⟨(h02.sub h13).congr_fun (fun s _ => (hfre x s).symm) measurableSet_Ioc,
          ((hx r 0 3).add (hx r 1 2)).congr_fun (fun s _ => (hfim x s).symm) measurableSet_Ioc⟩
    simp only [stoppedProcess_eq_stopTime, smCompensated_c4 Z]
    have hc := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at hc
    rw [Complex.sub_im, ← hc]
    simp only [hfim, f]
    rw [integral_add (hx r 0 3) (hx r 1 2)]
    simp only [c4_apply, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    ring

end BlockBand.SourceProcess.ComplexCoupled
