module

public import BlockBand.Critical.RelativeVectors.CrossRow

/-!
# The generator difference of a tested backward function

`generatorDiff_backward_le`: for the tested backward function `g = ∫ φ(π(M · + Ξ)) dP`
(`TestedSetting`; `g` of class `C²` and label-phase invariant), at one time `σ` of the flow with
eigenvalues `λ = λ(H_σ)`, `ℓ ≥ 1`, any array `z`, any window `J` with `|z_iq|² ≤ B` on `J` and
`|z_iq| ≤ Z`, and any per-label bounds `X_i` of the quadratic forms of
`Δ_i = Σ_{|i-j| ≥ ℓ} c_ij(z_jz_j^* - I_r)`:
`|𝒜g(z) - 𝓛_ref g(z)| ≤ 2r²K₂ Σ_i X_i ∫τ_i + K₂ Σ_{m',q',m,q} ∫ crossBoundFun
  + Σ_i |β̂_i - β_i| (½K₁|z_i| ∫√τ_i + ½ r K₂ ∫τ_i)`
(diagonal error `diagError_backward_le`, cross error `crossError_backward_le`, Ornstein–Uhlenbeck
floor error `floorError_backward_le`, through the exact identity `generator_diff_eq`).

Also `reference_charFun_invariant`: the reference covariance identity, in the
characteristic-functional form of `IsReferenceFlow.covariance`, gives
`E[exp(-¼Σ_q‖M^*w_q‖²) e^{i Re⟨w,Ξ⟩}] = exp(-¼Σ_q‖w_q‖²)`, i.e. `MG + Ξ` (with `G ~ γ`
independent) has the characteristic function of the standard circular Gaussian.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

variable {N r k : ℕ}

section Backward

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Ω → Matrix (Fin N) (Fin N) ℂ} {Ξ : Ω → Fin N → Fin r → ℂ}
  {φ : (Fin k → Fin r → ℂ) → ℝ}

/-- **The generator difference of a tested backward function.** See the module docstring. -/
theorem generatorDiff_backward_le (ι : Fin k → Fin N) {K₀ K₁ K₂ : ℝ}
    (hS : TestedSetting P M Ξ φ K₀ K₁ K₂)
    (hg : ContDiff ℝ 2 (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P))
    (hinv : ∀ u : Fin N → ℂ, (∀ i, ‖u i‖ = 1) → ∀ z,
      (∫ ω, φ (testProj ι (arrayMul (M ω) (phaseCLM u z) + Ξ ω)) ∂P) =
        ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P)
    (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ωf : FlowSample N) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (σ : ℝ) (z : Fin N → Fin r → ℂ) (J : Finset (Fin N)) {B Z : ℝ} (hB : 0 ≤ B) (hZ : 0 ≤ Z)
    (hzJ : ∀ i ∈ J, ∀ q, ‖z i q‖ ^ 2 ≤ B) (hz : ∀ i q, ‖z i q‖ ≤ Z) (X : Fin N → ℝ)
    (hX : ∀ i (p : Fin r → ℂ), |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ωf σ) i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        X i * nsq p) :
    |complexAngularGenerator N r (flowEigenvalue F a ωf σ)
        (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z -
      referenceArrayGenerator F a b₀ ωf ℓ σ
        (fun z => ∫ ω, φ (testProj ι (arrayMul (M ω) z + Ξ ω)) ∂P) z| ≤
      2 * (r : ℝ) ^ 2 * K₂ * ∑ i, X i * ∫ ω, tau (fun m => M ω (ι m) i) ∂P +
        K₂ * ∑ m', ∑ _q' : Fin r, ∑ m, ∑ _q : Fin r,
          ∫ ω, crossBoundFun ι (flowEigenvalue F a ωf σ) ℓ J B Z (M ω) m m' ∂P +
        ∑ i, |refDamping F a b₀ ωf ℓ σ i - longCoupling F a ωf ℓ σ i| *
          (1 / 2 * K₁ * ‖z i‖ * ∫ ω, Real.sqrt (tau (fun m => M ω (ι m) i)) ∂P +
            1 / 2 * r * K₂ * ∫ ω, tau (fun m => M ω (ι m) i) ∂P) := by
  rw [generator_diff_eq F a b₀ ωf hℓ σ]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact diagError_backward_le ι hS _ ℓ z X hX
  · exact crossError_backward_le ι hS hg hinv _ ℓ z J hB hZ hzJ hz
  · exact floorError_backward_le ι hS _ _ z

end Backward

/-!
## The reference flow preserves the circular Gaussian, characteristic-function form
-/

theorem l2Norm_sq (v : Fin N → ℂ) : l2Norm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  unfold l2Norm; rw [Real.sq_sqrt (by positivity)]

/-- `w^*(MM^*)w = ‖M^*w‖²`. -/
theorem quad_mul_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    (star w ⬝ᵥ ((A * Aᴴ) *ᵥ w)).re = l2Norm (Aᴴ *ᵥ w) ^ 2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    show star w ᵥ* A = star (Aᴴ *ᵥ w) by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
  rw [l2Norm_sq, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- **A standard circular Gaussian initial condition is mapped to a standard circular Gaussian.**
If `(M, Ξ)` satisfies the reference covariance identity in the characteristic-functional form of
`IsReferenceFlow.covariance` (for one pair of times), then for every `w`, with
`h(M) = exp(-¼ Σ_q ‖M^*w_q‖²)` (the characteristic function of `MG`, `G ~ γ` independent),
`E[h(M) e^{i Re⟨w, Ξ⟩}] = exp(-¼ Σ_q ‖w_q‖²)`, the characteristic function of `γ`. The
identification of the law of `MG + Ξ` as `γ` is `map_reference_gaussian_eq`. -/
theorem reference_charFun_invariant {Ωa : Type*} [MeasurableSpace Ωa] (Pa : Measure Ωa)
    [IsProbabilityMeasure Pa] (A : Ωa → Matrix (Fin N) (Fin N) ℂ)
    (Ξa : Ωa → Fin N → Fin r → ℂ)
    (hcov : ∀ h : Matrix (Fin N) (Fin N) ℂ → ℝ, Measurable h → (∃ C, ∀ M, |h M| ≤ C) →
      ∀ w : Fin N → Fin r → ℂ,
        ∫ ω', (h (A ω') : ℂ) * Complex.exp (Complex.I *
            (∑ i, ∑ q, (star (w i q) * Ξa ω' i q).re : ℝ)) ∂Pa =
          ∫ ω', (h (A ω') * Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
            (star (fun i => w i q) ⬝ᵥ ((1 - A ω' * (A ω')ᴴ) *ᵥ fun i => w i q)).re) : ℂ) ∂Pa)
    (w : Fin N → Fin r → ℂ) :
    ∫ ω', (Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm ((A ω')ᴴ *ᵥ fun i => w i q) ^ 2) : ℂ) *
        Complex.exp (Complex.I * (∑ i, ∑ q, (star (w i q) * Ξa ω' i q).re : ℝ)) ∂Pa =
      (Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm (fun i => w i q) ^ 2) : ℂ) := by
  have hmeas : Measurable fun M : Matrix (Fin N) (Fin N) ℂ =>
      Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm (Mᴴ *ᵥ fun i => w i q) ^ 2) := by
    refine Real.continuous_exp.measurable.comp ?_
    refine (continuous_const.mul (continuous_finsetSum _ fun q _ => ?_)).measurable
    have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => Mᴴ *ᵥ (fun i => w i q) :=
      continuous_id.matrix_conjTranspose.matrix_mulVec continuous_const
    unfold l2Norm
    exact (Continuous.sqrt (continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp hc).norm).pow 2)).pow 2
  have hbd : ∃ C, ∀ M : Matrix (Fin N) (Fin N) ℂ,
      |Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm (Mᴴ *ᵥ fun i => w i q) ^ 2)| ≤ C := by
    refine ⟨1, fun M => ?_⟩
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have : 0 ≤ ∑ q : Fin r, l2Norm (Mᴴ *ᵥ fun i => w i q) ^ 2 := by positivity
    linarith
  rw [hcov _ hmeas hbd w]
  have hpt : ∀ ω', Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm ((A ω')ᴴ *ᵥ fun i => w i q) ^ 2) *
      Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
        (star (fun i => w i q) ⬝ᵥ ((1 - A ω' * (A ω')ᴴ) *ᵥ fun i => w i q)).re) =
      Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm (fun i => w i q) ^ 2) := by
    intro ω'
    rw [← Real.exp_add]
    congr 1
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re,
      quad_mul_conjTranspose, l2Norm_sq (fun i => w i q), dotProduct, Complex.re_sum]
    have : ∑ i, (star (fun i => w i q) i * w i q).re = ∑ i, ‖w i q‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj', ← Complex.ofReal_pow,
        Complex.ofReal_re]
    rw [this]
    ring
  simp_rw [← Complex.ofReal_mul, hpt]
  rw [integral_const]
  simp

end BlockBand.Critical.RelativeVectors
