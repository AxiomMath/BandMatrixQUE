module

public import BlockBand.SourceProcess.Stochastic.Angular.Random
public import BlockBand.SourceProcess.Stochastic.Angular.Restart
public import BlockBand.SourceProcess.Stochastic.Angular.Cross
public import BlockBand.SourceProcess.Stochastic.Angular.Laplacian

/-!
# Complex angular martingale problem: assembly

* `complexAngularContract_of`: the complex angular martingale problem from the two propositions
  `ArrayLaplacian N r` and `GenericConditioning N`, through
  `deterministicAngular_of` (selection independence, regularity of `arrayFn`),
  `simpleSpectrumAngular_of_deterministic` (random tests) and
  `complexAngularMartingaleProblem_of_simple` (`s > 0` by non-collision, `s = 0` by modification).
* `lambda_form`: the corollary `E[Λ (f₀(Z_{u∧σ}) - f₀(Z_0) - ∫ 𝒜 f₀)] = 0` for a
  deterministic phase-invariant `C²` test and a bounded multiplier measurable for
  `𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)` (the random test `Λ • f₀`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular

/-- **The complex angular martingale problem from `ArrayLaplacian` and `GenericConditioning`.** -/
theorem complexAngularContract_of (hL : ∀ N r, ArrayLaplacian N r)
    (hC : ∀ N, GenericConditioning N) : ComplexAngularContract :=
  ⟨fun N r => complexAngularMartingaleProblem_of_simple
    (simpleSpectrumAngular_of_deterministic (deterministicAngular_of (hL N r) (hC N)))⟩

variable {N r : ℕ}

/-- `ArrayLaplacian` from its Laplacian half (the covariation half is `arrayFn_cross`). -/
theorem arrayLaplacian_of_diag (h : ArrayLaplacianDiag N r) : ArrayLaplacian N r :=
  fun V f₀ hf hp y hy => ⟨h V f₀ hf hp y hy, fun i => arrayFn_cross V hf hp hy i⟩

/-- **The complex angular martingale problem from `ArrayLaplacianDiag` and
`GenericConditioning`.** -/
theorem complexAngularContract_of_diag (hL : ∀ N r, ArrayLaplacianDiag N r)
    (hC : ∀ N, GenericConditioning N) : ComplexAngularContract :=
  complexAngularContract_of (fun N r => arrayLaplacian_of_diag (hL N r)) hC

theorem complexAngularGenerator_smul {f₀ : AngularArray N r → ℝ} (hf : ContDiff ℝ 2 f₀) (c : ℝ)
    (lam : Fin N → ℝ) (Z : AngularArray N r) :
    complexAngularGenerator N r lam (c • f₀) Z = c * complexAngularGenerator N r lam f₀ Z := by
  have hd : Differentiable ℝ f₀ := hf.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f₀) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : fderiv ℝ (c • f₀) = c • fderiv ℝ f₀ := by
    funext x; exact fderiv_const_smul (hd x) c
  have h2 : fderiv ℝ (c • fderiv ℝ f₀) Z = c • fderiv ℝ (fderiv ℝ f₀) Z :=
    fderiv_const_smul (hdd Z) c
  have hp : ∀ i j, pairTerm (c • f₀) i j Z = c * pairTerm f₀ i j Z := fun i j => by
    simp only [pairTerm, h1, h2, Pi.smul_apply, _root_.smul_apply, smul_eq_mul]; ring
  simp only [gen_eq_sum, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The multiplier form**: a bounded multiplier `Λ` measurable for
`𝓖_s ⊔ σ(λ(H_{s+v}) : v ≥ 0)` times a deterministic phase-invariant `C²` test. -/
theorem lambda_form (h : ComplexAngularContract) {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    {ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ} (hev : IsEigenSelection N ev)
    (s : ℝ≥0) (V : Matrix (Fin N) (Fin r) ℂ) {n : ℕ} (hn : 0 < n)
    {f₀ : AngularArray N r → ℝ} (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀)
    {Λ : Ω → ℝ} (hΛ : Measurable[𝓖 s ⊔ eigenPathSigma N F G s] Λ) {CΛ : ℝ}
    (hΛb : ∀ ω, |Λ ω| ≤ CΛ) (u : ℝ≥0) :
    Integrable (fun ω => Λ ω * angVar F G ev s V n (fun _ => f₀) u ω) Q ∧
      ∫ ω, Λ ω * angVar F G ev s V n (fun _ => f₀) u ω ∂Q = 0 := by
  obtain ⟨ω₀, -⟩ := (ae_of_all Q (fun _ => trivial) : ∀ᵐ _ ∂Q, True).exists
  have hCΛ : 0 ≤ CΛ := (abs_nonneg _).trans (hΛb ω₀)
  have key := h.angular N r Ω Q 𝓖 G F hG hF hFh ev hev s V n hn (fun ω => Λ ω • f₀)
    (fun ω => hf.const_smul (Λ ω)) (fun ω θ hθ Z => by simp [hp θ hθ Z])
    (fun Z => hΛ.mul_const (f₀ Z)) (fun R => ?_) u
  · have e : angVar F G ev s V n (fun ω => Λ ω • f₀) u =
        fun ω => Λ ω * angVar F G ev s V n (fun _ => f₀) u ω := by
      funext ω
      simp only [angVar, stoppedProcess, complexAngularGenerator_smul hf, Pi.smul_apply,
        smul_eq_mul, integral_const_mul]
      ring
    rw [← e]; exact key
  · obtain ⟨C, hC0, hC⟩ := exists_C2_bound hf R
    have hd : Differentiable ℝ f₀ := hf.differentiable (by norm_num)
    have hdd : Differentiable ℝ (fderiv ℝ f₀) :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    refine ⟨CΛ * C, fun ω Z hZ => ?_⟩
    obtain ⟨h0, h1, h2⟩ := hC Z hZ
    have e1 : fderiv ℝ (Λ ω • f₀) = Λ ω • fderiv ℝ f₀ := by
      funext x; exact fderiv_const_smul (hd x) _
    have e2 : fderiv ℝ (Λ ω • fderiv ℝ f₀) Z = Λ ω • fderiv ℝ (fderiv ℝ f₀) Z :=
      fderiv_const_smul (hdd Z) _
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul (hΛb ω) h0 (abs_nonneg _) hCΛ
    · rw [e1, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hΛb ω) h1 (norm_nonneg _) hCΛ
    · rw [e1, e2]
      refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [Real.norm_eq_abs]
      exact mul_le_mul (hΛb ω) h2 (ContinuousLinearMap.opNorm_nonneg _) hCΛ

end BlockBand.SourceProcess.Stochastic.ComplexAngular
