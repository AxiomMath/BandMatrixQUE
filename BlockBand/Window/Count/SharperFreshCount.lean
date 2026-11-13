module

public import BlockBand.Window.Count.Statement
public import BlockBand.Window.Count.FactorialMoments
public import BlockBand.Window.Count.SpectralSmoothing
public import BlockBand.Window.Count.SmoothingAssembly

/-!
# The sharper fresh count: reduction to two single-block Gaussian estimates

The sharper fresh count `SharperFreshCountStatement`,
`‖N_-(A+F-e) - E_A N_-(A+F-e)‖_p ≤ C W^{1/3}` for `A ~ GUE_W(c/W)`, is reduced here to two
single-block Gaussian estimates, stated as the propositions below (both are proved; see
`sharperFreshCount_holds`):

* `GueWindowFactorialBound`: the single-block case of the PSSS count theorem:
  `E_A (N_{A+F}([-η,η]))_r ≤ (C/√c · W · 2η)^r`, one absolute `C > 0` before `c, W, F, η, r`.
  This is exactly the PSSS source bound (`NativeInputs.psss`) for the normalized block
  `A/√c ~ GUE_W(1/W)`, deformation `F/√c`, interval `[-η/√c, η/√c]`; it requires the
  identification of `gueMeasure` with a `PSSS.BlockGUE.Law` (one block of size `W`).
* `GueSpectralLpGradient`: the Gaussian `L^p` Poincaré inequality applied to
  `X = Tr f(A+F)`: `‖X - EX‖_p ≤ C√p ‖(c/W · Tr f'(A+F)^2)^{1/2}‖_p` for
  `C^1` bounded `f` with bounded `f'`, one `C` before `p, c, W, F, f`. It is
  `Inputs.GaussianLpGradient` (one absolute `C`, factor `√p`) composed with the real
  coordinates of `gueMeasure` (`commonCircularIncrementLaw` is a pushforward of a real
  Gaussian product) plus the trace-derivative identity `D Tr f(M)[K] = Tr f'(M) K`, which
  gives the weighted gradient `(c/W) Σ_j f'(λ_j)^2` exactly.

`sharperFreshCount_of_gueBounds` proves `SharperFreshCountStatement` from these two
propositions: `f_η` smooth step, `|N_- - X_η| ≤ N([-η,η])`, `Tr|f_η'|² ≤ (K/η)² N([-η,η])`,
factorial-to-ordinary moments, the `L^p` assembly, and `η = W^{-2/3}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

/-!
## `gueMeasure` is a probability measure
-/

theorem continuous_circularBrownianCoordinates' {ι : Type*} :
    Continuous (circularBrownianCoordinates (ι := ι)) := by
  unfold circularBrownianCoordinates
  fun_prop

theorem continuous_gueSample' {ι : Type*} (t : ℝ≥0) :
    Continuous (gueSample (ι := ι) t) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gueSample, Matrix.of_apply]
  exact continuous_const.mul ((continuous_apply _).add
    (Complex.continuous_conj.comp (continuous_apply _)))

instance isProbabilityMeasure_gueMeasure' {ι : Type*} [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure commonCircularIncrementLaw
  infer_instance

/-!
## The two single-block Gaussian estimates
-/

/-- Single-block window count: the single-block case of the PSSS count theorem used in the sharper
fresh count. Law `gueMeasure (Fin W) (c/W)`. One absolute `C > 0` first; then every `c > 0`,
`W ≥ 1`, deterministic Hermitian `F` (no norm bound), `η > 0` and order `r ≥ 1`:
`E (N_{A+F}([-η,η]))_r ≤ (C/√c · W · 2η)^r`. Source: `NativeInputs.psss` (PSSS), after the
identification of `A/√c` with a one-block `PSSS.BlockGUE.Law`. -/
def GueWindowFactorialBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ W : ℕ, 0 < W →
    ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ η : ℝ, 0 < η → ∀ r : ℕ, 1 ≤ r →
      (∫ A, ((windowCount η (A + F)).descFactorial r : ℝ)
          ∂gueMeasure (Fin W) (Real.toNNReal (c / W))) ≤
        (C / Real.sqrt c * W * (2 * η)) ^ r

/-- Spectral Gaussian `L^p` gradient bound. Law `gueMeasure (Fin W) (c/W)` (real Hilbert space of
Hermitian matrices, covariance `(c/W) I`). One `C ≥ 0` first; then every `p ≥ 1`, `c > 0`, `W ≥ 1`,
deterministic Hermitian `F`, and `C^1` function `f` with `f, f'` bounded:
`‖Tr f(A+F) - E Tr f(A+F)‖_p ≤ C√p ‖(c/W · Tr f'(A+F)^2)^{1/2}‖_p`. Source:
`Inputs.GaussianLpGradient` plus the trace-derivative identity. -/
def GueSpectralLpGradient : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ, 1 ≤ p → ∀ c : ℝ, 0 < c → ∀ W : ℕ, 0 < W →
    ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
      (∃ B : ℝ, ∀ x, |f x| ≤ B) → (∃ B : ℝ, ∀ x, |deriv f x| ≤ B) →
      eLpNorm (fun A => spectralSum f (A + F) -
          ∫ A', spectralSum f (A' + F) ∂gueMeasure (Fin W) (Real.toNNReal (c / W)))
          (ENNReal.ofReal p) (gueMeasure (Fin W) (Real.toNNReal (c / W))) ≤
        ENNReal.ofReal (C * Real.sqrt p) *
          eLpNorm (fun A => Real.sqrt (c / W * spectralSum (fun x => deriv f x ^ 2) (A + F)))
            (ENNReal.ofReal p) (gueMeasure (Fin W) (Real.toNNReal (c / W)))

/-!
## Arithmetic of the choice `η = W^{-2/3}`
-/

theorem sqrt_term_le {c W u K0 A0 Kf p : ℝ} (hc : 0 < c) (hu : 1 ≤ u) (hW : W = u ^ 3)
    (hK0 : 0 ≤ K0) (hp : 1 ≤ p) (hKf : Kf ≤ A0 * u) (hKf0 : 0 ≤ Kf) :
    Real.sqrt (c / W) * (K0 / (u ^ 2)⁻¹) * Real.sqrt (4 * (p + 1) * Kf) ≤
      K0 * Real.sqrt (c * (4 * (p + 1) * A0)) * u := by
  have hu0 : 0 < u := by linarith
  have hA0 : 0 ≤ A0 * u := hKf0.trans hKf
  have hA0' : 0 ≤ A0 := by
    by_contra h; have h' := lt_of_not_ge h; nlinarith
  have h1 : Real.sqrt (c / W) * Real.sqrt (4 * (p + 1) * Kf) ≤
      Real.sqrt (c * (4 * (p + 1) * A0)) / u := by
    rw [← Real.sqrt_mul (by rw [hW]; positivity)]
    calc Real.sqrt (c / W * (4 * (p + 1) * Kf))
        ≤ Real.sqrt (c / W * (4 * (p + 1) * (A0 * u))) := by
          apply Real.sqrt_le_sqrt
          have : 0 ≤ c / W := by rw [hW]; positivity
          gcongr
      _ = Real.sqrt (c * (4 * (p + 1) * A0) / u ^ 2) := by
          congr 1; rw [hW]; field_simp
      _ = Real.sqrt (c * (4 * (p + 1) * A0)) / u := by
          rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hu0.le]
  calc Real.sqrt (c / W) * (K0 / (u ^ 2)⁻¹) * Real.sqrt (4 * (p + 1) * Kf)
      = K0 * u ^ 2 * (Real.sqrt (c / W) * Real.sqrt (4 * (p + 1) * Kf)) := by
        rw [div_inv_eq_mul]; ring
    _ ≤ K0 * u ^ 2 * (Real.sqrt (c * (4 * (p + 1) * A0)) / u) := by gcongr
    _ = K0 * Real.sqrt (c * (4 * (p + 1) * A0)) * u := by field_simp

/-!
## The reduction
-/

/-- The sharper fresh count from the two single-block estimates. Law `gueMeasure (Fin W) (c/W)`; for
every `c > 0` and real `p ≥ 1` there is `C`, then for every `W ≥ 1`, deterministic Hermitian `F` (no
norm bound) and real `e`: `‖N_-(A+F-e) - E_A N_-(A+F-e)‖_p ≤ C W^{1/3}`. Constant
`C = 4(p+1)A₀ + 8A₀ + C_g √p K₀ √(c·4(p+1)A₀)`, `A₀ = 1 + 2C_PSSS/√c`, `K₀` the absolute smooth-step
derivative bound. Dependencies: exactly `GueWindowFactorialBound` and `GueSpectralLpGradient`. -/
theorem sharperFreshCount_of_gueBounds (h1 : GueWindowFactorialBound)
    (h2 : GueSpectralLpGradient) : SharperFreshCountStatement := by
  obtain ⟨C1, hC1, hfac⟩ := h1
  obtain ⟨Cg, hCg, hgrad⟩ := h2
  obtain ⟨K0, hK0, hK⟩ := stepFn_deriv_bound
  intro c hc p hp
  set A0 : ℝ := 1 + 2 * C1 / Real.sqrt c with hA0
  have hA0one : 1 ≤ A0 := by
    have : 0 ≤ 2 * C1 / Real.sqrt c := by positivity
    linarith
  refine ⟨4 * (p + 1) * A0 + 4 * (1 + 1) * A0 +
    Cg * Real.sqrt p * (K0 * Real.sqrt (c * (4 * (p + 1) * A0))), ?_⟩
  intro W hW F hF e μ
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_gueMeasure' _
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  set u : ℝ := (W : ℝ) ^ (1 / 3 : ℝ) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow (by exact_mod_cast hW) (by norm_num)
  have hu0 : 0 < u := by linarith
  have hu3 : (W : ℝ) = u ^ 3 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hWpos.le]; norm_num
  set η : ℝ := (u ^ 2)⁻¹ with hηdef
  have hη : 0 < η := by positivity
  have hWη : (W : ℝ) * η = u := by rw [hu3, hηdef]; field_simp
  set F' : Matrix (Fin W) (Fin W) ℂ := F - (e : ℂ) • 1 with hF'def
  have hF' : F'.IsHermitian := by
    refine hF.sub ?_
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hAF : ∀ A : Matrix (Fin W) (Fin W) ℂ, A + F - (e : ℂ) • 1 = A + F' := fun A =>
    add_sub_assoc _ _ _
  simp only [hAF]
  -- the factorial constant
  set Kf : ℝ := max 1 (C1 / Real.sqrt c * W * (2 * η)) with hKfdef
  have hKf1 : 1 ≤ Kf := le_max_left _ _
  have hKfA : Kf ≤ A0 * u := by
    apply max_le
    · nlinarith
    · have : C1 / Real.sqrt c * W * (2 * η) = (2 * C1 / Real.sqrt c) * (W * η) := by ring
      rw [this, hWη, hA0]
      have : 0 ≤ 2 * C1 / Real.sqrt c := by positivity
      nlinarith
  -- measurability
  have hadd : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => A + F') :=
    measurable_id.add_const _
  have hYc : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => windowCount η (A + F')) :=
    (measurable_windowCount η).comp hadd
  have hYm : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => (windowCount η (A + F') : ℝ)) :=
    measurable_from_nat.comp hYc
  have hNm : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => (negativeCount (A + F') : ℝ)) := by
    simp_rw [negativeCount_cast]; exact (measurable_spectralSum measurable_negInd).comp hadd
  have hXm : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => spectralSum (stepFn η) (A + F')) :=
    (measurable_spectralSum (continuous_stepFn η).measurable).comp hadd
  have hGm : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ =>
      Real.sqrt (c / W * spectralSum (fun x => deriv (stepFn η) x ^ 2) (A + F'))) :=
    (((measurable_spectralSum ((measurable_deriv _).pow_const 2)).comp hadd).const_mul _).sqrt
  -- integrability (bounded by `W`)
  have hNint : Integrable (fun A : Matrix (Fin W) (Fin W) ℂ => (negativeCount (A + F') : ℝ)) μ := by
    refine Integrable.of_bound hNm.aestronglyMeasurable ((W : ℝ) * |1|)
      (Filter.Eventually.of_forall fun A => ?_)
    rw [Real.norm_eq_abs, negativeCount_cast]
    have := abs_spectralSum_le (g := negInd) (B := 1)
      (fun x => by unfold negInd; split_ifs <;> simp) (A + F')
    simpa using this
  have hXint : Integrable (fun A : Matrix (Fin W) (Fin W) ℂ => spectralSum (stepFn η) (A + F')) μ := by
    refine Integrable.of_bound hXm.aestronglyMeasurable ((W : ℝ) * |1|)
      (Filter.Eventually.of_forall fun A => ?_)
    rw [Real.norm_eq_abs]
    have := abs_spectralSum_le (g := stepFn η) (B := 1)
      (fun x => by rw [abs_of_nonneg (stepFn_nonneg _ _)]; exact stepFn_le_one _ _) (A + F')
    simpa using this
  -- the count moments
  have hYq : ∀ q : ℝ, 1 ≤ q → eLpNorm (fun A => (windowCount η (A + F') : ℝ))
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (4 * (q + 1) * Kf) := fun q hq =>
    count_eLpNorm_le_of_factorial μ _ hYc W
      (fun A => by simpa using windowCount_le_card η (A + F')) Kf hKf1
      (fun r hr => (hfac c hc W hW F' hF' η hη r hr).trans
        (pow_le_pow_left₀ (by positivity) (le_max_right _ _) r)) q hq
  have hY1 : eLpNorm (fun A => (windowCount η (A + F') : ℝ)) 1 μ ≤
      ENNReal.ofReal (4 * (1 + 1) * Kf) := by
    have := hYq 1 le_rfl
    rwa [ENNReal.ofReal_one] at this
  -- the gradient bound
  have hX := hgrad p hp c hc W hW F' hF' (stepFn η) (contDiff_stepFn η)
    ⟨1, fun x => by rw [abs_of_nonneg (stepFn_nonneg _ _)]; exact stepFn_le_one _ _⟩
    ⟨K0 / η, hK η hη⟩
  -- pointwise gradient domination
  have hG : ∀ A : Matrix (Fin W) (Fin W) ℂ,
      Real.sqrt (c / W * spectralSum (fun x => deriv (stepFn η) x ^ 2) (A + F')) ≤
        Real.sqrt (c / W) * (K0 / η) * Real.sqrt (windowCount η (A + F') : ℝ) := by
    intro A
    have hS := spectralSum_derivSq_le hη (hK η hη) (A + F')
    calc Real.sqrt (c / W * spectralSum (fun x => deriv (stepFn η) x ^ 2) (A + F'))
        ≤ Real.sqrt (c / W * ((K0 / η) ^ 2 * windowCount η (A + F'))) := by
          apply Real.sqrt_le_sqrt
          have : 0 ≤ c / W := by positivity
          gcongr
      _ = Real.sqrt (c / W) * (K0 / η) * Real.sqrt (windowCount η (A + F') : ℝ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
          ring
  have key := centered_le_of_smoothing μ hp
    (fun A => (negativeCount (A + F') : ℝ)) (fun A => spectralSum (stepFn η) (A + F'))
    (fun A => (windowCount η (A + F') : ℝ))
    (fun A => Real.sqrt (c / W * spectralSum (fun x => deriv (stepFn η) x ^ 2) (A + F')))
    hNm.aestronglyMeasurable hXm.aestronglyMeasurable hYm.aestronglyMeasurable
    hGm.aestronglyMeasurable hNint hXint
    (fun A => abs_negativeCount_sub_le hη (A + F')) (fun A => by positivity)
    (fun A => Real.sqrt_nonneg _) (Real.sqrt (c / W) * (K0 / η)) (by positivity) hG
    (4 * (1 + 1) * Kf) (4 * (p + 1) * Kf) (Cg * Real.sqrt p) (by positivity) (by positivity)
    (by positivity) hY1 (hYq p hp) hX
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hs := sqrt_term_le (c := c) (W := W) (u := u) (K0 := K0) (A0 := A0) (Kf := Kf) (p := p)
    hc hu1 hu3 hK0 hp hKfA (by linarith)
  have hp1 : (0 : ℝ) ≤ 4 * (p + 1) := by linarith
  have hb1 : 4 * (p + 1) * Kf ≤ 4 * (p + 1) * A0 * u := by
    rw [mul_assoc (4 * (p + 1)) A0]; exact mul_le_mul_of_nonneg_left hKfA hp1
  have hb2 : 4 * (1 + 1) * Kf ≤ 4 * (1 + 1) * A0 * u := by
    rw [mul_assoc (4 * (1 + 1)) A0]; exact mul_le_mul_of_nonneg_left hKfA (by norm_num)
  have hb3 : Cg * Real.sqrt p * (Real.sqrt (c / W) * (K0 / η) * Real.sqrt (4 * (p + 1) * Kf)) ≤
      Cg * Real.sqrt p * (K0 * Real.sqrt (c * (4 * (p + 1) * A0)) * u) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [hηdef] using hs
  nlinarith [hb1, hb2, hb3]

end BlockBand.Window.Count
