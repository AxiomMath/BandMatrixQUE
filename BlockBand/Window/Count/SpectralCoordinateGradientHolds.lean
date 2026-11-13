module

public import BlockBand.Window.Count.SpectralCoordinateLimit
public import BlockBand.Window.Count.SpectralGradientTransfer

/-!
# The trace gradient in GUE coordinates

Proves `SpectralCoordinateGradient`: the gradient of `x ↦ Tr f(gueCoordMap W t x + F)` in the real
Gaussian coordinates has squared norm `t Tr f'(H)²`.

*Setting.* `W ≥ 1`, `t ≥ 0`, Hermitian `F`, `f : ℝ → ℝ` of class `C¹` (the bounded-derivative
hypothesis of the definition is not needed). Coordinates `x : ((Fin W × Fin W) × Fin 2) → ℝ`,
`H(x) = gueCoordMap W t x + F`, `φ(x) = Tr f(H(x))` (as a complex number).

*Result.* `φ` is `C¹` (`SpectralCalculus.contDiff_spectralSum`), with
`∂_{(a,b),0} φ = √t Re G_ab` and `∂_{(a,b),1} φ = √t Im G_ab` where `G = f'(H(x))`
(`re_trace_mul_gueCoordMap`); hence `Σ_i |∂_i φ|² = t Σ_{a,b} |G_ab|² = t Tr G² =
t Σ_j f'(λ_j)²` (`sum_coef_sq`), i.e. the unit-covariance weighted gradient norm is
`(t Tr f'(H)²)^{1/2}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open BlockBand.Window.Count.SpectralCalculus
open scoped NNReal ComplexConjugate

namespace SpectralCoordinate

/-- `gueCoordMap W t` as a real linear map. -/
def gueCoordLin (W : ℕ) (t : ℝ≥0) :
    (((Fin W × Fin W) × Fin 2) → ℝ) →ₗ[ℝ] Matrix (Fin W) (Fin W) ℂ where
  toFun := gueCoordMap W t
  map_add' x y := by
    ext a b
    apply Complex.ext <;>
    simp [gueCoordMap, gueSample, circularBrownianCoordinates, Complex.div_ofReal_re,
      Complex.div_ofReal_im] <;> ring
  map_smul' c x := by
    ext a b
    apply Complex.ext <;>
    simp [gueCoordMap, gueSample, circularBrownianCoordinates, Complex.div_ofReal_re,
      Complex.div_ofReal_im] <;> ring

theorem gueCoordLin_apply (W : ℕ) (t : ℝ≥0) (x : ((Fin W × Fin W) × Fin 2) → ℝ) :
    gueCoordLin W t x = gueCoordMap W t x := rfl

theorem isHermitian_gueCoordMap (W : ℕ) (t : ℝ≥0) (x : ((Fin W × Fin W) × Fin 2) → ℝ) :
    (gueCoordMap W t x).IsHermitian := by
  ext a b
  simp only [gueCoordMap, gueSample, Matrix.conjTranspose_apply, Matrix.of_apply,
    star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- The coordinate gradient coefficients `√t Re G_ab`, `√t Im G_ab`. -/
def coef {W : ℕ} (t : ℝ≥0) (G : Matrix (Fin W) (Fin W) ℂ) (j : (Fin W × Fin W) × Fin 2) : ℝ :=
  Real.sqrt t * (if j.2 = 0 then (G j.1.1 j.1.2).re else (G j.1.1 j.1.2).im)

theorem sum_coef_mul {W : ℕ} (t : ℝ≥0) (G : Matrix (Fin W) (Fin W) ℂ)
    (v : ((Fin W × Fin W) × Fin 2) → ℝ) :
    ∑ j, coef t G j * v j =
      ∑ a, ∑ b, (Real.sqrt t * (G a b).re * v ((a, b), 0) +
        Real.sqrt t * (G a b).im * v ((a, b), 1)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.sum_univ_two]
  simp [coef, mul_assoc]

/-- `Re(√(t/2)(z̄ X + z X̄)) = √t (Re z v₀ + Im z v₁)` for `X = (v₀ + i v₁)/√2`. -/
theorem re_term (t : ℝ≥0) (z : ℂ) (v₀ v₁ : ℝ) :
    ((Real.sqrt ((t : ℝ) / 2) : ℂ) * (star z * (((v₀ : ℂ) + (v₁ : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ))) +
      (Real.sqrt ((t : ℝ) / 2) : ℂ) *
        (z * conj (((v₀ : ℂ) + (v₁ : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)))).re =
      Real.sqrt t * z.re * v₀ + Real.sqrt t * z.im * v₁ := by
  have hs : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t / Real.sqrt 2 :=
    Real.sqrt_div' _ zero_le_two
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  simp [Complex.div_ofReal_re, Complex.div_ofReal_im, hs]
  field_simp
  rw [hsq]
  ring

/-- Coordinate derivatives: for Hermitian `G`,
`Re Tr(G · gueCoordMap W t v) = Σ_j coef t G j · v_j`. -/
theorem re_trace_mul_gueCoordMap {W : ℕ} (t : ℝ≥0) {G : Matrix (Fin W) (Fin W) ℂ}
    (hG : G.IsHermitian) (v : ((Fin W × Fin W) × Fin 2) → ℝ) :
    (trace (G * gueCoordMap W t v)).re = ∑ j, coef t G j * v j := by
  set X : (Fin W × Fin W) → ℂ := circularBrownianCoordinates v with hX
  set c : ℂ := (Real.sqrt ((t : ℝ) / 2) : ℂ)
  have htr : trace (G * gueCoordMap W t v) =
      ∑ a, ∑ b, (c * (G a b * X (b, a)) + c * (G a b * conj (X (a, b)))) := by
    simp only [trace, diag, Matrix.mul_apply, gueCoordMap, gueSample, Matrix.of_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hswap : ∑ a, ∑ b, c * (G a b * X (b, a)) = ∑ a, ∑ b, c * (star (G a b) * X (a, b)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hG.apply b a]
  rw [htr]
  simp only [Finset.sum_add_distrib]
  rw [hswap, ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, Complex.re_sum]
  rw [sum_coef_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact re_term t (G a b) (v ((a, b), 0)) (v ((a, b), 1))

/-- `Σ_j coef_j² = t Re Tr(G²)` for Hermitian `G`. -/
theorem sum_coef_sq {W : ℕ} (t : ℝ≥0) {G : Matrix (Fin W) (Fin W) ℂ} (hG : G.IsHermitian) :
    ∑ j, coef t G j ^ 2 = t * (trace (G * G)).re := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [trace, diag, Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.sum_univ_two, ← hG.apply b a]
  simp only [coef, Fin.isValue, ↓reduceIte, one_ne_zero, mul_pow, Real.sq_sqrt t.coe_nonneg,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

end SpectralCoordinate

open SpectralCoordinate in
/-- `SpectralCoordinateGradient` holds (the trace gradient identity used in the sharper fresh
count). For `W ≥ 1`, `t ≥ 0`, Hermitian `F` and `C¹` `f`, the function
`x ↦ Tr f(gueCoordMap W t x + F)` on `((Fin W × Fin W) × Fin 2) → ℝ` is `C¹` and its
unit-covariance weighted gradient norm is `(t Tr f'(gueCoordMap W t x + F)²)^{1/2}` at every
`x`. -/
theorem spectralCoordinateGradient_holds : SpectralCoordinateGradient := by
  intro W _ t F hF f hf _
  set L := gueCoordLin W t with hL
  have hH : ∀ x, (L x + F).IsHermitian := fun x => (isHermitian_gueCoordMap W t x).add hF
  have hψ := contDiff_spectralSum L F hH hf
  refine ⟨Complex.ofRealCLM.contDiff.comp hψ, fun x => ?_⟩
  have hd := hasFDerivAt_spectralSum L F hH hf x
  have hφ : HasFDerivAt (fun x => (spectralSum f (gueCoordMap W t x + F) : ℂ))
      (Complex.ofRealCLM.comp (traceDeriv L (deriv f) (L x + F))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hd
  unfold BlockBand.Internal.Contracts.Inputs.weightedGradientNorm
  rw [hφ.fderiv]
  congr 1
  set G := (hH x).cfc (deriv f) with hGdef
  have hG : G.IsHermitian := isHermitian_cfc (hH x) (deriv f)
  have hGd : ∀ v, traceDeriv L (deriv f) (L x + F) v = (trace (G * gueCoordMap W t v)).re := by
    intro v
    rw [traceDeriv, fcalc_eq (hH x), trCLM_apply]
    rfl
  have hcoef : ∀ i, (traceDeriv L (deriv f) (L x + F)) (Pi.single i 1) = coef t G i := by
    intro i
    rw [hGd, re_trace_mul_gueCoordMap t hG]
    simp [Pi.single_apply]
  calc ∑ i, ((1 : ℝ≥0) : ℝ) *
        ‖(Complex.ofRealCLM.comp (traceDeriv L (deriv f) (L x + F))) (Pi.single i 1)‖ ^ 2
      = ∑ i, coef t G i ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
          Real.norm_eq_abs, sq_abs, hcoef, NNReal.coe_one, one_mul]
    _ = t * (trace (G * G)).re := sum_coef_sq t hG
    _ = t * spectralSum (fun y => deriv f y ^ 2) (gueCoordMap W t x + F) := by
        change _ = t * spectralSum (fun y => deriv f y ^ 2) (L x + F)
        rw [hGdef, cfc_mul_cfc (hH x), re_trace_cfc (hH x), spectralSum_eq (hH x)]
        simp only [pow_two]

end BlockBand.Window.Count
