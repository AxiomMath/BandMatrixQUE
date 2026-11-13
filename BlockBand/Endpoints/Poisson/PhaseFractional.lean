module

public import BlockBand.Endpoints.Poisson.PhaseFractionalCore

/-!
# The phase fractional-inverse lemma

We bound fractional moments of the projected inverse `v*(I - tÛV)⁻¹ v` over the fresh collar.
Steps 1–5 refer to the proof of the phase fractional-inverse lemma in the paper.

**Law and domain.** The fresh collar `collarLaw W b`, with `U = collarScattering b e s ν` (height
`0 ≤ ν ≤ ν₀`, shift `|s| ≤ s₀`; `s = ν = 0` is the main case) on the two `W`-dimensional ports
`α = Fin 2 × Fin W`, `Û = U ⊕ 0` on `α ⊕ β`, `β` an arbitrary finite complement. `V` is a
deterministic unitary on `α ⊕ β` (independent of the collar), `v` a unit vector,
`V_θ = V exp(iθ v v*) = V (I + (e^{iθ} - 1) v v*)`, `r_θ = P V_θ P` its port compression.

**Hypothesis.** `d(r_θ) ≤ d₁` for every `θ` (`d` through `(z_b - X)⁻¹ = (I - r)/(2iη)`,
`scatteringDistance`), and `g(r_θ) ≤ G` for every `θ`; the collar kernel theorem then gives the
common kernel bound `M = C(1 + G)`. `CollarKernelContract` is an explicit hypothesis. The
kernel-bound form of the lemma at a radial regulator `t < 1`, for an arbitrary common bound `M`
on `E_U 𝒫(t U r_θ)`, is `lintegral_fullQuad_rpow_le_of_kernel`.

**Conclusion (main content: the radial, `t`-uniform clause).**
`E_U |v*(I - tÛV)⁻¹ v|^p ≤ C_p (1 + G + 2W(1 - t²))` for every `t ∈ (τ, 1)`, with `τ` and
`C_p` independent of `W`, `e`, `V`, `v`; here `I - tÛV` is always invertible (`tÛV` is a strict
contraction). The boundary clause `E_U |v*(I - ÛV)⁻¹ v|^p ≤ C_p (1 + G)` follows from it by
Fatou along `t ↑ 1`.

**Boundary convention.** At `t = 1` the inverse is Mathlib's (`A⁻¹ = 0` when `det A = 0`), so
the boundary integrand is `0` on the event `{det(I - ÛV) = 0}`; off that event it is the radial
limit. The boundary clause therefore agrees with the paper's boundary quantity only on the
complement of that event, which is empty for `ν > 0` and collarLaw-null for `ν = 0`
(real-analyticity of the determinant in the Gaussian variables; this is not used). The
radial clause carries the full content and involves no convention.

**Quantifiers/uniformity.** `b ∈ (0,1/2)`, `κ > 0` first; then `d₁, s₀, ν₀ > 0`, `τ < 1` and
`W₀`; then `p ∈ (0,1)` and `C_p`; uniformly in `W ≥ W₀`, `e ∈ bulkInterval κ`, `s, ν`, the
complement `β`, `V`, `v` and `G`. Expectations are lower Lebesgue integrals.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

universe u

open MeasureTheory Matrix Filter Set
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts (Critical.poissonKernel)
open scoped ComplexOrder ComplexConjugate ENNReal Topology

/-!
## Linearity of the expected kernel
-/

theorem integrable_quadForm {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] {μ : Measure Ω}
    {F : Ω → Matrix κ κ ℂ} (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) (u : κ → ℂ) :
    Integrable (fun ω => star u ⬝ᵥ (F ω *ᵥ u)) μ := by
  simp only [dotProduct, mulVec]
  exact integrable_finsetSum _ fun x _ => ((integrable_finsetSum _ fun y _ =>
    (hF x y).mul_const _)).const_mul _

theorem integral_quadForm {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] {μ : Measure Ω}
    {F : Ω → Matrix κ κ ℂ} (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) (u : κ → ℂ) :
    ∫ ω, star u ⬝ᵥ (F ω *ᵥ u) ∂μ = star u ⬝ᵥ (matrixExpect μ F *ᵥ u) := by
  simp only [dotProduct, mulVec, matrixExpect, Matrix.of_apply]
  rw [integral_finsetSum _ fun x _ => ((integrable_finsetSum _ fun y _ =>
    (hF x y).mul_const _)).const_mul _]
  congr 1; ext x
  rw [integral_const_mul, integral_finsetSum _ fun y _ => (hF x y).mul_const _]
  congr 2; ext y
  rw [integral_mul_const]

theorem re_quad_le_of_posSemidef {κ : Type*} [Fintype κ] [DecidableEq κ] {E : Matrix κ κ ℂ}
    {M : ℝ} (h : (((M : ℝ) : ℂ) • (1 : Matrix κ κ ℂ) - E).PosSemidef) (u : κ → ℂ) :
    (star u ⬝ᵥ (E *ᵥ u)).re ≤ M * quadNorm u := by
  have := h.dotProduct_mulVec_nonneg u
  rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    star_dotProduct_self_eq] at this
  have h2 := (Complex.nonneg_iff.mp this).1
  simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h2
  linarith

/-!
## One kernel step: the full kernel bounded by the collar kernel
-/

section Kernel

variable {W : ℕ} {β : Type u} [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem collarHat_mul (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ) (t : ℝ) :
    (t : ℂ) • (collarHat (β := β) U * V) =
      fromBlocks ((t : ℂ) • (U * V.toBlocks₁₁)) ((t : ℂ) • (U * V.toBlocks₁₂)) 0 0 := by
  conv_lhs => rw [← fromBlocks_toBlocks V]
  rw [collarHat, fromBlocks_multiply, fromBlocks_smul]
  simp

/-- The expected full kernel along `v` is bounded by twice the expected collar kernel along the
port component plus twice the complement norm (Step 3). -/
theorem lintegral_kernel_le {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im) (hν : 0 ≤ ν)
    {V : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ} (hV : Vᴴ * V = 1)
    {v : (Fin 2 × Fin W) ⊕ β → ℂ} (hv : star v ⬝ᵥ v = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hint : CollarKernelIntegrable b e s ν 1 (cayleyInv b e ((t : ℂ) • V.toBlocks₁₁))) :
    ∫⁻ ω, ENNReal.ofReal (2 * (fullQuad t (collarScattering b e s ν ω) V v).re - 1)
        ∂collarLaw W b ≤
      ENNReal.ofReal (2 * ((star (v ∘ Sum.inl) ⬝ᵥ (expectedCollarKernel b e s ν 1
        (cayleyInv b e ((t : ℂ) • V.toBlocks₁₁)) *ᵥ (v ∘ Sum.inl))).re +
          quadNorm (v ∘ Sum.inr))) := by
  have := isProbabilityMeasure_collarLaw W b
  have hr : IsContraction V.toBlocks₁₁ := isContraction_toBlocks₁₁ (isContraction_of_unitary hV)
  have htr : IsStrictContraction ((t : ℂ) • V.toBlocks₁₁) := hr.smul_strict ht0 ht1
  have hold : oldScattering b e (cayleyInv b e ((t : ℂ) • V.toBlocks₁₁)) =
      (t : ℂ) • V.toBlocks₁₁ := oldScattering_cayleyInv hη htr.isUnit_det
  set F : CollarSample W → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fun ω =>
    poissonKernel (((1 : ℝ) : ℂ) • (collarScattering b e s ν ω *
      oldScattering b e (cayleyInv b e ((t : ℂ) • V.toBlocks₁₁)))) with hF
  have hFeq : ∀ ω, F ω = portKernel ((t : ℂ) • (collarScattering b e s ν ω * V.toBlocks₁₁)) := by
    intro ω
    simp only [hF]
    rw [hold, Complex.ofReal_one, one_smul, mul_smul_comm]
    rfl
  set u₁ := v ∘ Sum.inl
  set u₂ := v ∘ Sum.inr
  have hgi1 : Integrable (fun ω => 2 * (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re) (collarLaw W b) :=
    (integrable_quadForm hint u₁).re.const_mul 2
  have hgi : Integrable (fun ω => 2 * (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re + 2 * quadNorm u₂)
      (collarLaw W b) := hgi1.add (integrable_const _)
  -- pointwise, on the almost sure set of Hermitian samples
  have hpt : ∀ᵐ ω ∂collarLaw W b,
      2 * (fullQuad t (collarScattering b e s ν ω) V v).re - 1 ≤
        2 * (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re + 2 * quadNorm u₂ ∧
      0 ≤ 2 * (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re + 2 * quadNorm u₂ := by
    filter_upwards [ae_collar_hermitian W b] with ω hω
    have hU := isContraction_collarScattering (s := s) hη hν hω.1 hω.2
    have ha : IsStrictContraction ((t : ℂ) • (collarScattering b e s ν ω * V.toBlocks₁₁)) :=
      (hU.mul hr).smul_strict ht0 ht1
    have hfull : IsContraction (fromBlocks ((t : ℂ) • (collarScattering b e s ν ω *
        V.toBlocks₁₁)) ((t : ℂ) • (collarScattering b e s ν ω * V.toBlocks₁₂)) 0
        (0 : Matrix β β ℂ)) := by
      rw [← collarHat_mul]
      exact (((isContraction_fromBlocks_zero hU).mul
        (isContraction_of_unitary hV)).smul_strict ht0 ht1).isContraction
    have h1 := two_re_quad_fromBlocks_le ha.isUnit_det hfull v
    rw [← collarHat_mul, ← fullQuad, quadNorm_eq_one hv, ← hFeq] at h1
    refine ⟨by linarith, ?_⟩
    have h2 := two_re_quad_sub_nonneg ha.isUnit_det ha.isContraction u₁
    have h3 := quad_portKernel ((t : ℂ) • (collarScattering b e s ν ω * V.toBlocks₁₁)) u₁
    rw [← hFeq] at h3
    have h4 : (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re = 2 * (resolventQuad ((t : ℂ) •
        (collarScattering b e s ν ω * V.toBlocks₁₁)) u₁).re - quadNorm u₁ := by
      rw [h3, star_dotProduct_self_eq, resolventQuad]
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.ofReal_re]
      ring
    have := quadNorm_nonneg u₂
    nlinarith
  calc ∫⁻ ω, ENNReal.ofReal (2 * (fullQuad t (collarScattering b e s ν ω) V v).re - 1)
        ∂collarLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re + 2 * quadNorm u₂)
          ∂collarLaw W b := by
        apply lintegral_mono_ae
        filter_upwards [hpt] with ω hω
        exact ENNReal.ofReal_le_ofReal hω.1
    _ = ENNReal.ofReal (∫ ω, (2 * (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re + 2 * quadNorm u₂)
          ∂collarLaw W b) := by
        rw [ofReal_integral_eq_lintegral_ofReal hgi]
        filter_upwards [hpt] with ω hω
        exact hω.2
    _ = _ := by
        congr 1
        have hI : ∫ ω, (star u₁ ⬝ᵥ (F ω *ᵥ u₁)).re ∂collarLaw W b =
            (star u₁ ⬝ᵥ (matrixExpect (collarLaw W b) F *ᵥ u₁)).re := by
          have := integral_re (integrable_quadForm hint u₁)
          simp only [RCLike.re_to_complex] at this
          rw [this, integral_quadForm hint u₁]
        rw [integral_add hgi1 (integrable_const _),
          integral_const_mul, hI, integral_const, probReal_univ, one_smul]
        simp only [expectedCollarKernel, hF]
        ring

end Kernel

/-!
## The lemma with a common kernel bound `M` (radial regulator `t`)
-/

section KernelBound

variable {W : ℕ} {β : Type u} [Fintype β] [DecidableEq β]

theorem twistedV_unitary {V : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ}
    (hV : Vᴴ * V = 1) {v : (Fin 2 × Fin W) ⊕ β → ℂ} (hv : star v ⬝ᵥ v = 1) (θ : ℝ) :
    (twistedV V v θ)ᴴ * twistedV V v θ = 1 := by
  rw [twistedV, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV,
    Matrix.one_mul, rankOneTwist_unitary hv (norm_exp_mul_I θ)]

/-- The expected kernel at the Cayley inverse of `t r` is `E_U 𝒫(t U r)`. -/
theorem expectedCollarKernel_cayleyInv {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im)
    {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hr : IsUnit (1 - r).det) :
    expectedCollarKernel b e s ν 1 (cayleyInv b e r) =
      matrixExpect (collarLaw W b) (fun ω => Critical.poissonKernel (collarScattering b e s ν ω * r)) := by
  rw [expectedCollarKernel, oldScattering_cayleyInv hη hr, Complex.ofReal_one]
  simp only [one_smul]

theorem collarKernelIntegrable_cayleyInv {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im)
    {r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hr : IsUnit (1 - r).det) :
    CollarKernelIntegrable b e s ν 1 (cayleyInv b e r) ↔
      ∀ x y, Integrable (fun ω => Critical.poissonKernel (collarScattering b e s ν ω * r) x y)
        (collarLaw W b) := by
  rw [CollarKernelIntegrable, oldScattering_cayleyInv hη hr, Complex.ofReal_one]
  simp only [one_smul]

/-- **The phase fractional-inverse lemma, kernel-bound form** (Steps 1–4, radial regulator
`0 ≤ t < 1`). Law: `collarLaw W b`; `U = collarScattering b e s ν`
(`η = Im z_b > 0`, `ν ≥ 0`); `V` unitary on `(Fin 2 × Fin W) ⊕ β`; `‖v‖ = 1`. Hypothesis: for
every twist angle `θ`, the entries of `𝒫(t U r_θ)` are integrable and the common kernel bound
`E_U 𝒫(t U r_θ) ⪯ M I` holds (`r_θ = P V_θ P`). Conclusion:
`E_U |v*(I - tÛV)⁻¹v|^p ≤ C_p max(M, 1)`, `C_p = 2 phaseConst p` (lower integral).
The factor `max(M,1)` is needed: Step 3 bounds `E_U[2 Re q_θ - 1]` by `2(M‖Pv‖² + ‖P^⊥v‖²)`,
and absorbing the second term into `CM` requires `M` bounded below (for `v ∈ Ran P^⊥` the left
side equals `1`). In the application `M = C(1 + g)`, so `max(M,1) ≤ max(C,1)(1 + g)`. -/
theorem lintegral_fullQuad_rpow_le_of_kernel {b e s ν : ℝ} (hη : 0 < (boundaryZ b e).im)
    (hν : 0 ≤ ν) {V : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ} (hV : Vᴴ * V = 1)
    {v : (Fin 2 × Fin W) ⊕ β → ℂ} (hv : star v ⬝ᵥ v = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {M : ℝ}
    (hM : ∀ θ : ℝ,
      (∀ x y, Integrable (fun ω => Critical.poissonKernel ((t : ℂ) •
        (collarScattering b e s ν ω * (twistedV V v θ).toBlocks₁₁)) x y) (collarLaw W b)) ∧
      (((M : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        matrixExpect (collarLaw W b) (fun ω => Critical.poissonKernel ((t : ℂ) •
          (collarScattering b e s ν ω * (twistedV V v θ).toBlocks₁₁)))).PosSemidef) :
    ∫⁻ ω, ENNReal.ofReal (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p) ∂collarLaw W b ≤
      phaseConst p * ENNReal.ofReal (2 * max M 1) := by
  have := isProbabilityMeasure_collarLaw W b
  apply lintegral_fullQuad_rpow_le (collarLaw W b) (measurable_collarScattering b e s ν W)
    _ hV hv ht0 ht1 hp0 hp1
  · intro θ
    have hVθ := twistedV_unitary hV hv θ
    have hr : IsContraction (twistedV V v θ).toBlocks₁₁ :=
      isContraction_toBlocks₁₁ (isContraction_of_unitary hVθ)
    have hu := (hr.smul_strict ht0 ht1).isUnit_det
    obtain ⟨hI, hP⟩ := hM θ
    simp only [← mul_smul_comm] at hI hP
    have hint := (collarKernelIntegrable_cayleyInv hη hu).mpr hI
    refine (lintegral_kernel_le hη hν hVθ hv ht0 ht1 hint).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [expectedCollarKernel_cayleyInv hη hu]
    have h1 := re_quad_le_of_posSemidef hP (v ∘ Sum.inl)
    have h2 := quadNorm_sum v
    rw [quadNorm_eq_one hv] at h2
    have h3 := quadNorm_nonneg (v ∘ Sum.inl)
    have h4 := quadNorm_nonneg (v ∘ Sum.inr)
    have h5 : M ≤ max M 1 := le_max_left _ _
    have h6 : 1 ≤ max M 1 := le_max_right _ _
    nlinarith
  · filter_upwards [ae_collar_hermitian W b] with ω hω
    exact isContraction_collarScattering (s := s) hη hν hω.1 hω.2

end KernelBound

/-!
## Removing the radial factor (Step 5)
-/

theorem continuousAt_inv_one_sub_smul {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℂ} (h : IsUnit (1 - A).det) :
    ContinuousAt (fun t : ℝ => (1 - (t : ℂ) • A)⁻¹) 1 := by
  have hc : Continuous (fun t : ℝ => (1 : Matrix κ κ ℂ) - (t : ℂ) • A) :=
    continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)
  have hdet : ((1 : Matrix κ κ ℂ) - (((1 : ℝ) : ℂ)) • A).det ≠ 0 := by
    rw [Complex.ofReal_one, one_smul]; exact h.ne_zero
  have heq : (fun t : ℝ => (1 - (t : ℂ) • A)⁻¹) =
      fun t : ℝ => ((1 - (t : ℂ) • A).det)⁻¹ • (1 - (t : ℂ) • A).adjugate := by
    funext t; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [heq]
  exact (hc.matrix_det.continuousAt.inv₀ hdet).smul hc.matrix_adjugate.continuousAt

theorem continuousAt_resolventQuad_smul {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℂ} (h : IsUnit (1 - A).det) (v : κ → ℂ) :
    ContinuousAt (fun t : ℝ => resolventQuad ((t : ℂ) • A) v) 1 := by
  have hq : Continuous fun M : Matrix κ κ ℂ => star v ⬝ᵥ (M *ᵥ v) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact hq.continuousAt.comp (continuousAt_inv_one_sub_smul h)

/-!
## The phase fractional-inverse lemma
-/

/-- **The phase fractional-inverse lemma.** Fixed first: `0 < b < 1/2`, `κ > 0`. Then: a scalar threshold `d₁ > 0` (`= d_*/4`), the collar
height/shift ranges `ν₀, s₀ > 0`, a radial threshold `τ < 1`, and `W₀`. Then `p ∈ (0,1)` and
`C_p ≥ 0`. Uniformly in `W ≥ W₀`, `e ∈ bulkInterval κ`, `|s| ≤ s₀`, `0 ≤ ν ≤ ν₀`, the finite
complement `β` of the two `W`-dimensional ports, the unitary `V` on `(Fin 2 × Fin W) ⊕ β`, the
unit vector `v`, and `G`: if every rank-one twist `V_θ = V exp(iθvv*)` has `d(r_θ) ≤ d₁` (the
scalar condition) and `g(r_θ) ≤ G` (so the common kernel bound is `M = C(1 + G)`), then, over
the fresh collar `collarLaw W b`,
* (radial, the main content) `E_U |v*(I - tÛV)⁻¹v|^p ≤ C_p (1 + G + 2W(1 - t²))` for every
  `t ∈ (τ, 1)`, uniformly in `t`;
* (boundary, by Fatou) `E_U |v*(I - ÛV)⁻¹v|^p ≤ C_p (1 + G)`, `Û = [[U, 0], [0, 0]]`, with
  Mathlib's inverse: the integrand is `0` on `{det(I - ÛV) = 0}` (empty for `ν > 0`,
  collarLaw-null for `ν = 0`; this null-set fact is not used).
Expectations are lower Lebesgue integrals (so the bound includes finiteness). -/
theorem phase_fractional_inverse (hK : CollarKernelContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (d₁ s₀ ν₀ τ : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 < s₀ ∧ 0 < ν₀ ∧ 0 ≤ τ ∧ τ < 1 ∧
      ∀ p : ℝ, 0 < p → p < 1 → ∃ Cp : ℝ, 0 ≤ Cp ∧
        ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Icc (-s₀) s₀,
        ∀ ν ∈ Icc 0 ν₀, ∀ (β : Type u) [Fintype β] [DecidableEq β]
          (V : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ), Vᴴ * V = 1 →
        ∀ v : (Fin 2 × Fin W) ⊕ β → ℂ, star v ⬝ᵥ v = 1 → ∀ G : ℝ,
          (∀ θ : ℝ, scatteringDistance b e (twistedV V v θ).toBlocks₁₁ ≤ d₁) →
          (∀ θ : ℝ, conductance (twistedV V v θ).toBlocks₁₁ ≤ G) →
          (∀ t ∈ Ioo τ 1, ∫⁻ ω, ENNReal.ofReal
              (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p) ∂collarLaw W b ≤
            ENNReal.ofReal (Cp * (1 + G + (1 - t ^ 2) * (2 * W)))) ∧
          ∫⁻ ω, ENNReal.ofReal (‖star v ⬝ᵥ ((1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 *
              V)⁻¹ *ᵥ v)‖ ^ p) ∂collarLaw W b ≤ ENNReal.ofReal (Cp * (1 + G)) := by
  obtain ⟨dstar, C, s₀, ν₀, W₀, hd, hs₀, hν₀, hB⟩ := hK b hb0 hb1 κ hκ
  have hb1' : b < 1 := by linarith
  have hηm := etaMin_pos hb1' hκ
  set τ : ℝ := max 0 (1 - etaMin b κ * dstar / 2) with hτ
  have hτ1 : τ < 1 := max_lt one_pos (by nlinarith)
  refine ⟨dstar / 4, s₀, ν₀, τ, W₀, by positivity, hs₀, hν₀, le_max_left _ _, hτ1, ?_⟩
  intro p hp0 hp1
  have hfin := phaseConst_lt_top hp0 hp1
  refine ⟨(phaseConst p).toReal * 2 * max C 1, by positivity, ?_⟩
  intro W hW hW₀ e he s hs ν hν β _ _ V hV v hv G hd₁ hG
  have hη := boundaryZ_im_pos hb1' hκ he
  have hηge := boundaryZ_im_ge hb1' hκ he
  have hG0 : 0 ≤ G := by
    have hr0 : IsContraction (twistedV V v 0).toBlocks₁₁ :=
      isContraction_toBlocks₁₁ (isContraction_of_unitary (twistedV_unitary hV hv 0))
    exact (conductance_nonneg hr0).trans (hG 0)
  have hcard : (Fintype.card (Fin 2 × Fin W) : ℝ) = 2 * W := by
    simp [Fintype.card_prod]
  have hconv : ∀ x : ℝ, 0 ≤ x →
      phaseConst p * ENNReal.ofReal (2 * (max C 1 * x)) =
        ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 * x) := by
    intro x hx
    conv_lhs => rw [← ENNReal.ofReal_toReal hfin.ne]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    congr 1; ring
  -- the radial bound
  have hrad : ∀ t ∈ Ioo τ 1, ∫⁻ ω, ENNReal.ofReal
      (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p) ∂collarLaw W b ≤
      ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 * (1 + G + (1 - t ^ 2) * (2 * W))) := by
    intro t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht.1.le
    have ht1 := ht.2
    have htη : (1 - t) / (2 * (boundaryZ b e).im) ≤ dstar / 4 := by
      have h1 : 1 - t ≤ etaMin b κ * dstar / 2 := by
        have := (le_max_right 0 (1 - etaMin b κ * dstar / 2)).trans ht.1.le
        linarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hx1 : 1 ≤ 1 + G + (1 - t ^ 2) * (2 * W) := by
      have : 0 ≤ (1 - t ^ 2) * (2 * W) := mul_nonneg (by nlinarith) (by positivity)
      linarith
    set M : ℝ := max C 1 * (1 + G + (1 - t ^ 2) * (2 * W)) with hM
    have hM1 : 1 ≤ M := by
      have h1 : 1 ≤ max C 1 := le_max_right _ _
      nlinarith
    have key := lintegral_fullQuad_rpow_le_of_kernel (M := M) (W := W) hη hν.1 hV hv ht0 ht1
      hp0 hp1 (fun θ => by
        have hVθ := twistedV_unitary hV hv θ
        have hr : IsContraction (twistedV V v θ).toBlocks₁₁ :=
          isContraction_toBlocks₁₁ (isContraction_of_unitary hVθ)
        have hst := hr.smul_strict ht0 ht1
        have hu := hst.isUnit_det
        obtain ⟨hI, -, hcond⟩ := hB.strict W hW hW₀ e he s hs ν hν _
          (neg_imPart_cayleyInv_posDef hη hst)
        have hdist : matchedDistance b e (cayleyInv b e ((t : ℂ) • (twistedV V v θ).toBlocks₁₁))
            ≤ dstar / 2 := by
          rw [matchedDistance_cayleyInv hη hu]
          have := scatteringDistance_smul_le hη hr ht1.le
          linarith [hd₁ θ]
        have hP := hcond hdist
        rw [oldScattering_cayleyInv hη hu, expectedCollarKernel_cayleyInv hη hu] at hP
        rw [collarKernelIntegrable_cayleyInv hη hu] at hI
        have hg := conductance_smul_le hr ht0 ht1.le
        have hg0 := conductance_nonneg hst.isContraction
        rw [hcard] at hg
        have hCM : C * (1 + conductance ((t : ℂ) • (twistedV V v θ).toBlocks₁₁)) ≤ M := by
          have h1 : C ≤ max C 1 := le_max_left _ _
          have h2 : 1 + conductance ((t : ℂ) • (twistedV V v θ).toBlocks₁₁) ≤
              1 + G + (1 - t ^ 2) * (2 * W) := by linarith [hG θ]
          have h3 : 0 ≤ max C 1 := by positivity
          calc C * (1 + conductance ((t : ℂ) • (twistedV V v θ).toBlocks₁₁))
              ≤ max C 1 * (1 + conductance ((t : ℂ) • (twistedV V v θ).toBlocks₁₁)) :=
                mul_le_mul_of_nonneg_right h1 (by linarith)
            _ ≤ M := mul_le_mul_of_nonneg_left h2 h3
        refine ⟨by simpa only [mul_smul_comm] using hI, ?_⟩
        simp only [mul_smul_comm] at hP
        have hsplit : ((M : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            matrixExpect (collarLaw W b) (fun ω => Critical.poissonKernel ((t : ℂ) •
              (collarScattering b e s ν ω * (twistedV V v θ).toBlocks₁₁))) =
            (((M - C * (1 + conductance ((t : ℂ) • (twistedV V v θ).toBlocks₁₁)) : ℝ) : ℂ) •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) +
            ((((C * (1 + conductance ((t : ℂ) • (twistedV V v θ).toBlocks₁₁)) : ℝ) : ℂ) •
              (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) -
            matrixExpect (collarLaw W b) (fun ω => Critical.poissonKernel ((t : ℂ) •
              (collarScattering b e s ν ω * (twistedV V v θ).toBlocks₁₁)))) := by
          rw [Complex.ofReal_sub, sub_smul]; abel
        rw [hsplit]
        refine PosSemidef.add ?_ hP
        apply PosSemidef.smul PosSemidef.one
        exact_mod_cast sub_nonneg.mpr hCM)
    rw [max_eq_left hM1] at key
    rw [hM, hconv _ (by linarith)] at key
    exact key
  refine ⟨fun t ht => by simpa [mul_assoc] using hrad t ht, ?_⟩
  -- the boundary bound: Fatou along the radial limit `t ↑ 1`
  have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 *
      (1 + G + (1 - t ^ 2) * (2 * W)))) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 * (1 + G)))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun t : ℝ => ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 *
        (1 + G + (1 - t ^ 2) * (2 * W)))) := ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using hc.tendsto 1
  have hpt : ∀ ω, ENNReal.ofReal (‖star v ⬝ᵥ ((1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 *
      V)⁻¹ *ᵥ v)‖ ^ p) ≤ liminf (fun t : ℝ => ENNReal.ofReal
        (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p)) (𝓝[<] 1) := by
    intro ω
    set A := collarHat (β := β) (collarScattering b e s ν ω) * V with hA
    by_cases hu : IsUnit (1 - A).det
    · have hc := continuousAt_resolventQuad_smul hu v
      have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal
          (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p)) (𝓝[<] 1)
          (𝓝 (ENNReal.ofReal (‖resolventQuad (((1 : ℝ) : ℂ) • A) v‖ ^ p))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        have : ContinuousAt (fun t : ℝ => ENNReal.ofReal (‖resolventQuad ((t : ℂ) • A) v‖ ^ p))
            1 := by
          apply ENNReal.continuous_ofReal.continuousAt.comp
          apply ContinuousAt.rpow_const (continuous_norm.continuousAt.comp hc)
          right; exact hp0.le
        exact this.tendsto
      rw [h1.liminf_eq, Complex.ofReal_one, one_smul, resolventQuad, hA, collarHat]
    · have h0 : star v ⬝ᵥ ((1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 * V)⁻¹ *ᵥ v) = 0 := by
        rw [← collarHat, ← hA, nonsing_inv_apply_not_isUnit _ hu]
        simp
      rw [h0, norm_zero, Real.zero_rpow hp0.ne', ENNReal.ofReal_zero]
      exact zero_le
  calc ∫⁻ ω, ENNReal.ofReal (‖star v ⬝ᵥ ((1 - fromBlocks (collarScattering b e s ν ω) 0 0 0 *
          V)⁻¹ *ᵥ v)‖ ^ p) ∂collarLaw W b
      ≤ ∫⁻ ω, liminf (fun t : ℝ => ENNReal.ofReal
          (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p)) (𝓝[<] 1) ∂collarLaw W b :=
        lintegral_mono hpt
    _ ≤ liminf (fun t : ℝ => ∫⁻ ω, ENNReal.ofReal
          (‖fullQuad t (collarScattering b e s ν ω) V v‖ ^ p) ∂collarLaw W b) (𝓝[<] 1) := by
        apply lintegral_liminf_le
        intro t
        exact ENNReal.measurable_ofReal.comp
          (((measurable_fullQuad (measurable_collarScattering b e s ν W) t V v).norm).pow_const p)
    _ ≤ liminf (fun t : ℝ => ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 *
          (1 + G + (1 - t ^ 2) * (2 * W)))) (𝓝[<] 1) := by
        exact liminf_le_liminf (by
          filter_upwards [Ioo_mem_nhdsLT hτ1] with t ht
          exact hrad t ht)
    _ = ENNReal.ofReal ((phaseConst p).toReal * 2 * max C 1 * (1 + G)) := hlim.liminf_eq

end BlockBand.Endpoints.PhaseFractional
