module

public import BlockBand.SourceProcess.Stochastic.Angular.Basic

/-!
# Complex angular martingale problem: phase equivariance of the generator

For unimodular phases `θ` let `T_θ Z = (θ_i z_i)_i` (`phaseCLE`). If `f ∘ T_θ = f`, then
* `fderiv_phase`, `fderiv2_phase`: `Df(T Z)[T W] = Df(Z)[W]` and
  `D²f(T Z)[T W, T W'] = D²f(Z)[W, W']` (no differentiability needed: `T` is a linear iso);
* `pairRotX_phase`, `pairRotY_phase`: with `e^{iα} = θ_j θ̄_i`,
  `X(TZ) = T(cos α XZ + sin α YZ)`, `Y(TZ) = T(cos α YZ - sin α XZ)`, `A²(TZ) = T(A²Z)`;
* **`complexAngularGenerator_phase`**: `𝒜 f (θ·Z) = 𝒜 f (Z)` for every phase-invariant `f`
  (any couplings), and `complexAngularGenerator_ev`: the generator does not see the selection.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular

variable {N r : ℕ}

/-- The real-linear phase map `T_θ Z = (θ_i z_i)_i` for nonvanishing `θ`. -/
def phaseLE (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) :
    AngularArray N r ≃ₗ[ℝ] AngularArray N r where
  toFun Z := fun i a => θ i * Z i a
  invFun Z := fun i a => (θ i)⁻¹ * Z i a
  map_add' Z W := by funext i a; simp [mul_add]
  map_smul' c Z := by funext i a; simp [Complex.real_smul, mul_left_comm]
  left_inv Z := by funext i a; simp [← mul_assoc, inv_mul_cancel₀ (hθ i)]
  right_inv Z := by funext i a; simp [← mul_assoc, mul_inv_cancel₀ (hθ i)]

/-- `T_θ` as a continuous linear equivalence. -/
def phaseCLE (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) : AngularArray N r ≃L[ℝ] AngularArray N r :=
  (phaseLE θ hθ).toContinuousLinearEquiv

@[simp] theorem phaseCLE_apply (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) (Z : AngularArray N r) :
    phaseCLE θ hθ Z = fun i a => θ i * Z i a := rfl

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E ≃L[ℝ] E) {f : E → ℝ}

theorem fderiv_phase (hf : ∀ Z, f (T Z) = f Z) (Z W : E) :
    fderiv ℝ f (T Z) (T W) = fderiv ℝ f Z W := by
  have h := T.comp_right_fderiv (f := f) (x := Z)
  rw [show f ∘ T = f from funext hf] at h
  rw [h]; rfl

theorem fderiv_phase' (hf : ∀ Z, f (T Z) = f Z) (Z : E) :
    fderiv ℝ f (T Z) = T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) (fderiv ℝ f Z) := by
  ext x
  rw [ContinuousLinearEquiv.arrowCongr_apply, ← fderiv_phase T hf Z, T.apply_symm_apply]
  rfl

theorem fderiv2_phase (hf : ∀ Z, f (T Z) = f Z) (Z W W' : E) :
    fderiv ℝ (fderiv ℝ f) (T Z) (T W) (T W') = fderiv ℝ (fderiv ℝ f) Z W W' := by
  set Φ := T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have h1 : fderiv ℝ f ∘ T = Φ ∘ fderiv ℝ f := funext fun Z => fderiv_phase' T hf Z
  have h2 := T.comp_right_fderiv (f := fderiv ℝ f) (x := Z)
  have h3 := Φ.comp_fderiv (f := fderiv ℝ f) (x := Z)
  rw [h1, h3] at h2
  have := congrArg (fun L => L W (T W')) h2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at this
  rw [← this]
  simp [Φ, ContinuousLinearEquiv.arrowCongr_apply]

end Deriv

/-!
### The rotation fields under phases
-/

section Fields

variable (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0)

theorem pairRotX_phase {i j : Fin N} (hij : i ≠ j) (hi : θ i * conj (θ i) = 1)
    (hj : θ j * conj (θ j) = 1) (Z : AngularArray N r) :
    pairRotX i j (phaseCLE θ hθ Z) = phaseCLE θ hθ
      ((θ j * conj (θ i)).re • pairRotX i j Z + (θ j * conj (θ i)).im • pairRotY i j Z) := by
  have hw := Complex.re_add_im (θ j * conj (θ i))
  have hwc : ((θ j * conj (θ i)).re : ℂ) - ((θ j * conj (θ i)).im : ℂ) * Complex.I =
      conj (θ j) * θ i := by
    have := congrArg conj hw
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj] at this
    linear_combination this
  funext k a
  simp only [pairRotX, pairRotY, phaseCLE_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
  by_cases hki : k = i
  · subst hki; simp only [ite_true, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(θ k) * Z j a) * hw - Z j a * θ j * hi
  · by_cases hkj : k = j
    · subst hkj; simp only [hki, ite_false, ite_true, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (θ k * Z i a) * hwc + Z i a * θ i * hj
    · simp [hki, hkj]

theorem pairRotY_phase {i j : Fin N} (hij : i ≠ j) (hi : θ i * conj (θ i) = 1)
    (hj : θ j * conj (θ j) = 1) (Z : AngularArray N r) :
    pairRotY i j (phaseCLE θ hθ Z) = phaseCLE θ hθ
      ((θ j * conj (θ i)).re • pairRotY i j Z - (θ j * conj (θ i)).im • pairRotX i j Z) := by
  have hw := Complex.re_add_im (θ j * conj (θ i))
  have hwc : ((θ j * conj (θ i)).re : ℂ) - ((θ j * conj (θ i)).im : ℂ) * Complex.I =
      conj (θ j) * θ i := by
    have := congrArg conj hw
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj] at this
    linear_combination this
  funext k a
  simp only [pairRotX, pairRotY, phaseCLE_apply, Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
  by_cases hki : k = i
  · subst hki; simp only [ite_true, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(θ k) * Complex.I * Z j a) * hw - Complex.I * θ j * Z j a * hi +
      θ k * ((θ j * conj (θ k)).im : ℂ) * Z j a * Complex.I_sq
  · by_cases hkj : k = j
    · subst hkj; simp only [hki, ite_false, ite_true, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (-(θ k) * Complex.I * Z i a) * hwc - Complex.I * θ i * Z i a * hj -
        θ k * ((θ k * conj (θ i)).im : ℂ) * Z i a * Complex.I_sq
    · simp [hki, hkj]

theorem pairRotX_sq_phase {i j : Fin N} (hij : i ≠ j) (Z : AngularArray N r) :
    pairRotX i j (pairRotX i j (phaseCLE θ hθ Z)) =
      phaseCLE θ hθ (pairRotX i j (pairRotX i j Z)) := by
  funext k a
  by_cases hki : k = i
  · subst hki; simp [pairRotX, hij.symm]
  · by_cases hkj : k = j
    · subst hkj; simp [pairRotX, hki]
    · simp [pairRotX, hki, hkj]

theorem pairRotY_sq_phase {i j : Fin N} (hij : i ≠ j) (Z : AngularArray N r) :
    pairRotY i j (pairRotY i j (phaseCLE θ hθ Z)) =
      phaseCLE θ hθ (pairRotY i j (pairRotY i j Z)) := by
  funext k a
  by_cases hki : k = i
  · subst hki; simp [pairRotY, hij.symm]; ring
  · by_cases hkj : k = j
    · subst hkj; simp [pairRotY, hki]; ring
    · simp [pairRotY, hki, hkj]

end Fields

/-- **Phase equivariance of the complex angular generator**: for a phase-invariant
`f`, `𝒜 f (θ·Z) = 𝒜 f (Z)` for unimodular `θ`, with any couplings `lam`. -/
theorem complexAngularGenerator_phase {f : AngularArray N r → ℝ} (hf : IsPhaseInvariant f)
    (lam : Fin N → ℝ) (θ : Fin N → ℂ) (hθ : ∀ i, ‖θ i‖ = 1) (Z : AngularArray N r) :
    complexAngularGenerator N r lam f (fun i a => θ i * Z i a) =
      complexAngularGenerator N r lam f Z := by
  have hθ0 : ∀ i, θ i ≠ 0 := fun i h => by simpa [h] using hθ i
  have hθc : ∀ i, θ i * conj (θ i) = 1 := fun i => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ i]; norm_num
  set T := phaseCLE (r := r) θ hθ0
  have hT : ∀ Z, f (T Z) = f Z := fun Z => hf θ hθ Z
  have hZ : (fun i a => θ i * Z i a) = T Z := rfl
  rw [hZ]
  unfold complexAngularGenerator
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
  congr 1
  rw [pairRotX_sq_phase θ hθ0 hij, pairRotY_sq_phase θ hθ0 hij,
    pairRotX_phase θ hθ0 hij (hθc i) (hθc j), pairRotY_phase θ hθ0 hij (hθc i) (hθc j),
    fderiv2_phase T hT,
    fderiv2_phase T hT, fderiv_phase T hT, fderiv_phase T hT]
  set c := (θ j * conj (θ i)).re
  set s := (θ j * conj (θ i)).im
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have h1 : Complex.normSq (θ j * conj (θ i)) = 1 := by
      rw [Complex.normSq_mul, Complex.normSq_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, hθ i, hθ j]; norm_num
    rw [Complex.normSq_apply] at h1
    linear_combination h1
  set B := fderiv ℝ (fderiv ℝ f) Z
  simp only [map_add, map_sub, map_smul, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  linear_combination (B (pairRotX i j Z) (pairRotX i j Z) +
    B (pairRotY i j Z) (pairRotY i j Z)) * hcs

/-- **The generator does not see the selection** (at simple Hermitian `H`). -/
theorem complexAngularGenerator_ev {f : AngularArray N r → ℝ} (hf : IsPhaseInvariant f)
    (lam : Fin N → ℝ) {ev ev' : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ}
    (hev : IsEigenSelection N ev) (hev' : IsEigenSelection N ev')
    {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hs : HasSimpleSpectrum N H)
    (V : Matrix (Fin N) (Fin r) ℂ) :
    complexAngularGenerator N r lam f (angularArray V (ev H)) =
      complexAngularGenerator N r lam f (angularArray V (ev' H)) := by
  obtain ⟨θ, hθ, he⟩ := exists_phase_ev hev hev' hH hs V
  rw [he, complexAngularGenerator_phase hf lam θ hθ]

end BlockBand.SourceProcess.Stochastic.ComplexAngular
