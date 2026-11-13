module

public import BlockBand.Critical.RelativeVectors.GenDiffBound
public import BlockBand.Critical.RelativeVectors.Statement
public import BlockBand.Critical.Herglotz.GaussianMoments

/-!
# Equilibration of the reference flow

Law: `gaussianMarkLaw N r` (`N` independent standard circular Gaussian vectors in `ℂ^r`,
`E|g_iq|² = 1`); auxiliary probability space `(Ωa, Pa)` carrying the reference propagator `A`
and the reference noise `Ξa`. Norm: the Euclidean norm `√(arrayNormSq ·)` of `ℂ^{N×r}`.

1. `charFun_gaussianMarkLaw`: `∫ exp(i Σ Re(conj w_iq g_iq)) dγ = exp(-¼ Σ_q ‖w_q‖²)`;
   `strongDual_apply_eq`: every real-linear functional is `x ↦ Σ Re(conj w_iq x_iq)`.
2. `map_reference_gaussian_eq`: under the characteristic-functional form of the reference
   covariance identity (the `hcov` hypothesis of `reference_charFun_invariant`), the law of
   `AG + Ξa` (`G ~ γ` independent of `(A, Ξa)`) is `γ` (`Measure.ext_of_charFunDual`).
3. `lipschitz_of_isArrayC2Bounded`: `|f x - f y| ≤ C‖x - y‖₂`.
4. `reference_equilibration`: if `‖A v‖₂ ≤ ρ‖v‖₂` and `f` is bounded, continuous and
   `L`-Lipschitz for `‖·‖₂`, then `|E f(Az + Ξa) - ∫ f dγ| ≤ Lρ(‖z‖₂ + √(Nr))`, uniformly in `z`,
   `N`, `r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {N r : ℕ}

theorem isProbabilityMeasure_circularVectorLaw' (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw
  infer_instance

attribute [local instance] isProbabilityMeasure_circularVectorLaw'

instance isProbabilityMeasure_gaussianMarkLaw (k r : ℕ) :
    IsProbabilityMeasure (gaussianMarkLaw k r) := by
  unfold gaussianMarkLaw
  infer_instance

theorem integral_gaussianReal_exp_mul (v : ℝ≥0) (a : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)) ∂gaussianReal 0 v) =
      Complex.exp (-((v : ℂ) * (a : ℂ) ^ 2) / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := v) a
  rw [charFun_apply_real] at h
  simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc, neg_div] using h

/-- Characteristic function of the standard circular Gaussian vector. -/
theorem charFun_circularVectorLaw (v : Fin r → ℂ) :
    ∫ g, Complex.exp (Complex.I * ((∑ q, (star (v q) * g q).re : ℝ) : ℂ))
        ∂circularVectorLaw (Fin r) =
      (Real.exp (-(1 / 4 : ℝ) * ∑ q, ‖v q‖ ^ 2) : ℂ) := by
  unfold circularVectorLaw
  have hφ : Measurable (fun (x : Fin r × Fin 2 → ℝ) (c : Fin r) =>
      (x (c, 0) : ℂ) + (x (c, 1) : ℂ) * Complex.I) := by fun_prop
  have hcont : Continuous fun g : Fin r → ℂ =>
      Complex.exp (Complex.I * ((∑ q, (star (v q) * g q).re : ℝ) : ℂ)) := by fun_prop
  rw [integral_map hφ.aemeasurable hcont.aestronglyMeasurable]
  set c : Fin r × Fin 2 → ℝ := fun p => if p.2 = 0 then (v p.1).re else (v p.1).im with hc
  have hpt : ∀ x : Fin r × Fin 2 → ℝ,
      Complex.exp (Complex.I * ((∑ q, (star (v q) *
        ((x (q, 0) : ℂ) + (x (q, 1) : ℂ) * Complex.I)).re : ℝ) : ℂ)) =
      ∏ p, Complex.exp (Complex.I * ((c p * x p : ℝ) : ℂ)) := by
    intro x
    rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum, Fintype.sum_prod_type]
    congr 3
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Fin.sum_univ_two]
    simp [hc, Complex.mul_re, Complex.mul_im]
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (f := fun p y => Complex.exp (Complex.I * ((c p * y : ℝ) : ℂ)))]
  simp_rw [integral_gaussianReal_exp_mul, ← Complex.exp_sum, Complex.ofReal_exp]
  congr 1
  rw [Fintype.sum_prod_type]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fin.sum_univ_two]
  have hn : ((‖v q‖ : ℝ) : ℂ) ^ 2 = ((v q).re : ℂ) ^ 2 + ((v q).im : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  simp only [hc, Fin.isValue, ite_true, one_ne_zero, ite_false]
  rw [hn]
  ring

/-- **Item 1.** Characteristic function of the product circular Gaussian law on arrays. -/
theorem charFun_gaussianMarkLaw (w : Fin N → Fin r → ℂ) :
    ∫ g, Complex.exp (Complex.I * ((∑ i, ∑ q, (star (w i q) * g i q).re : ℝ) : ℂ))
        ∂gaussianMarkLaw N r =
      (Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r, l2Norm (fun i => w i q) ^ 2) : ℂ) := by
  unfold gaussianMarkLaw
  have hpt : ∀ g : Fin N → Fin r → ℂ,
      Complex.exp (Complex.I * ((∑ i, ∑ q, (star (w i q) * g i q).re : ℝ) : ℂ)) =
        ∏ i, Complex.exp (Complex.I * ((∑ q, (star (w i q) * g i q).re : ℝ) : ℂ)) := by
    intro g
    rw [← Complex.exp_sum, ← Finset.mul_sum, ← Complex.ofReal_sum]
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (f := fun i (y : Fin r → ℂ) =>
    Complex.exp (Complex.I * ((∑ q, (star (w i q) * y q).re : ℝ) : ℂ)))]
  simp_rw [charFun_circularVectorLaw]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp_rw [l2Norm_sq]
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- The coefficient array `w_iq = L(e_iq) + i L(i e_iq)` of a real-linear functional. -/
def dualArray (L : StrongDual ℝ (Fin N → Fin r → ℂ)) : Fin N → Fin r → ℂ :=
  fun i q => (L (Pi.single i (Pi.single q 1)) : ℂ) +
    (L (Pi.single i (Pi.single q Complex.I)) : ℂ) * Complex.I

theorem strongDual_apply_eq (L : StrongDual ℝ (Fin N → Fin r → ℂ)) (x : Fin N → Fin r → ℂ) :
    L x = ∑ i, ∑ q, (star (dualArray L i q) * x i q).re := by
  classical
  have hx : x = ∑ i, ∑ q, ((x i q).re • (Pi.single i (Pi.single q 1) : Fin N → Fin r → ℂ) +
      (x i q).im • (Pi.single i (Pi.single q Complex.I) : Fin N → Fin r → ℂ)) := by
    funext i' q'
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, ite_apply,
      Pi.zero_apply, smul_ite, smul_zero, ite_add_ite, add_zero]
    rw [Fintype.sum_eq_single i' fun j hj => by simp [Ne.symm hj]]
    simp only [ite_true, Finset.sum_ite_eq, Finset.mem_univ]
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  conv_lhs => rw [hx]
  simp only [map_sum, map_add, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q _ => ?_
  simp [dualArray, Complex.mul_re]
  ring

/-- **Item 3.** Euclidean Lipschitz bound from the derivative bound. -/
theorem lipschitz_of_isArrayC2Bounded {C : ℝ} {f : (Fin N → Fin r → ℂ) → ℝ}
    (hf : IsArrayC2Bounded C f) (x y : Fin N → Fin r → ℂ) :
    |f x - f y| ≤ C * Real.sqrt (arrayNormSq (x - y)) := by
  have hd : Differentiable ℝ f := hf.contDiff.differentiable (by norm_num)
  set g : ℝ → ℝ := fun t => f (y + t • (x - y)) with hgdef
  have hg : ∀ t, HasDerivAt g (fderiv ℝ f (y + t • (x - y)) (x - y)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact (hd _).hasFDerivAt.comp_hasDerivAt t h1
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := g)
    (C := C * Real.sqrt (arrayNormSq (x - y)))
    (fun t _ => (hg t).hasDerivWithinAt) (fun t _ => by
      rw [Real.norm_eq_abs]; exact hf.deriv_bound _ _)
  simpa [hgdef] using this

theorem measurable_arrayMul_comp {Ωa : Type*} [MeasurableSpace Ωa]
    {A : Ωa → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) {Z : Ωa → Fin N → Fin r → ℂ}
    (hZ : Measurable Z) : Measurable fun ω => arrayMul (A ω) (Z ω) := by
  unfold arrayMul
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun q =>
    Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul
    ((measurable_pi_apply q).comp ((measurable_pi_apply j).comp hZ))

theorem continuous_charKernel (w : Fin N → Fin r → ℂ) :
    Continuous fun x : Fin N → Fin r → ℂ =>
      Complex.exp (Complex.I * ((∑ i, ∑ q, (star (w i q) * x i q).re : ℝ) : ℂ)) := by
  fun_prop

theorem norm_exp_I_mul_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

/-- `Re⟨w, Mz⟩ = Re⟨M^*w, z⟩` columnwise. -/
theorem pairing_arrayMul (M : Matrix (Fin N) (Fin N) ℂ) (w z : Fin N → Fin r → ℂ) :
    ∑ i, ∑ q, (star (w i q) * arrayMul M z i q).re =
      ∑ j, ∑ q, (star ((Mᴴ *ᵥ fun i => w i q) j) * z j q).re := by
  have hL : ∀ i q, (star (w i q) * arrayMul M z i q).re =
      ∑ j, (star (w i q) * M i j * z j q).re := by
    intro i q; simp only [arrayMul, Finset.mul_sum, Complex.re_sum, mul_assoc]
  have hR : ∀ j q, (star ((Mᴴ *ᵥ fun i => w i q) j) * z j q).re =
      ∑ i, (star (w i q) * M i j * z j q).re := by
    intro j q
    simp only [Matrix.mulVec, dotProduct, conjTranspose_apply, star_sum, star_mul', star_star,
      Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring_nf
  simp_rw [hL, hR]
  calc ∑ i, ∑ q, ∑ j, (star (w i q) * M i j * z j q).re
      = ∑ i, ∑ j, ∑ q, (star (w i q) * M i j * z j q).re :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ q, (star (w i q) * M i j * z j q).re := Finset.sum_comm
    _ = ∑ j, ∑ q, ∑ i, (star (w i q) * M i j * z j q).re :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- **Item 2.** `MG + Ξ ~ γ` for `G ~ γ` independent of `(M, Ξ)`. -/
theorem map_reference_gaussian_eq {Ωa : Type*} [MeasurableSpace Ωa] (Pa : Measure Ωa)
    [IsProbabilityMeasure Pa] (A : Ωa → Matrix (Fin N) (Fin N) ℂ)
    (Ξa : Ωa → Fin N → Fin r → ℂ) (hA : Measurable A) (hΞ : Measurable Ξa)
    (hcov : ∀ h : Matrix (Fin N) (Fin N) ℂ → ℝ, Measurable h → (∃ C, ∀ M, |h M| ≤ C) →
      ∀ w : Fin N → Fin r → ℂ,
        ∫ ω', (h (A ω') : ℂ) * Complex.exp (Complex.I *
            (∑ i, ∑ q, (star (w i q) * Ξa ω' i q).re : ℝ)) ∂Pa =
          ∫ ω', (h (A ω') * Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
            (star (fun i => w i q) ⬝ᵥ ((1 - A ω' * (A ω')ᴴ) *ᵥ fun i => w i q)).re) : ℂ) ∂Pa) :
    (Pa.prod (gaussianMarkLaw N r)).map (fun p => arrayMul (A p.1) p.2 + Ξa p.1) =
      gaussianMarkLaw N r := by
  have hF : Measurable fun p : Ωa × (Fin N → Fin r → ℂ) => arrayMul (A p.1) p.2 + Ξa p.1 :=
    (measurable_arrayMul_comp (hA.comp measurable_fst) measurable_snd).add
      (hΞ.comp measurable_fst)
  have : IsProbabilityMeasure ((Pa.prod (gaussianMarkLaw N r)).map
      (fun p => arrayMul (A p.1) p.2 + Ξa p.1)) :=
    (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance
  refine Measure.ext_of_charFunDual ?_
  funext L
  have hcL : Continuous fun v : Fin N → Fin r → ℂ => Complex.exp (↑(L v) * Complex.I) := by
    fun_prop
  rw [charFunDual_apply, charFunDual_apply, integral_map hF.aemeasurable
    hcL.aestronglyMeasurable]
  set w := dualArray L
  have hcf : ∀ x, Complex.exp (↑(L x) * Complex.I) =
      Complex.exp (Complex.I * ((∑ i, ∑ q, (star (w i q) * x i q).re : ℝ) : ℂ)) := by
    intro x; rw [strongDual_apply_eq L x, mul_comm]
  simp_rw [hcf]
  rw [charFun_gaussianMarkLaw, ← reference_charFun_invariant Pa A Ξa hcov w]
  have hint : Integrable (fun p : Ωa × (Fin N → Fin r → ℂ) => Complex.exp (Complex.I *
      ((∑ i, ∑ q, (star (w i q) * (arrayMul (A p.1) p.2 + Ξa p.1) i q).re : ℝ) : ℂ)))
      (Pa.prod (gaussianMarkLaw N r)) := by
    refine Integrable.of_bound ((continuous_charKernel w).measurable.comp hF).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_exp_I_mul_ofReal]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hpt : ∀ g : Fin N → Fin r → ℂ, Complex.exp (Complex.I *
      ((∑ i, ∑ q, (star (w i q) * (arrayMul (A ω) g + Ξa ω) i q).re : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((∑ j, ∑ q,
          (star (((A ω)ᴴ *ᵥ fun i => w i q) j) * g j q).re : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((∑ i, ∑ q, (star (w i q) * Ξa ω i q).re : ℝ) : ℂ)) := by
    intro g
    have hs : ∑ i, ∑ q, (star (w i q) * (arrayMul (A ω) g + Ξa ω) i q).re =
        ∑ j, ∑ q, (star (((A ω)ᴴ *ᵥ fun i => w i q) j) * g j q).re +
          ∑ i, ∑ q, (star (w i q) * Ξa ω i q).re := by
      rw [← pairing_arrayMul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Pi.add_apply, Pi.add_apply, mul_add, Complex.add_re]
    rw [hs, Complex.ofReal_add, mul_add, Complex.exp_add]
  simp only [hpt]
  rw [integral_mul_const]
  have h1 := charFun_gaussianMarkLaw (N := N) (r := r)
    (fun j q => ((A ω)ᴴ *ᵥ fun i => w i q) j)
  rw [h1]

/-!
## Euclidean norm of arrays
-/

theorem arrayNormSq_nonneg (z : Fin N → Fin r → ℂ) : 0 ≤ arrayNormSq z := by
  unfold arrayNormSq; positivity

theorem continuous_arrayNormSq : Continuous fun z : Fin N → Fin r → ℂ => arrayNormSq z := by
  unfold arrayNormSq; fun_prop

theorem arrayNormSq_eq_sum_l2Norm (y : Fin N → Fin r → ℂ) :
    arrayNormSq y = ∑ q, l2Norm (fun i => y i q) ^ 2 := by
  simp_rw [l2Norm_sq]; unfold arrayNormSq; rw [Finset.sum_comm]

/-- Columnwise contraction: `‖Mx‖₂² ≤ ρ²‖x‖₂²` on arrays. -/
theorem arrayNormSq_arrayMul_le {M : Matrix (Fin N) (Fin N) ℂ} {ρ : ℝ}
    (hM : ∀ v : Fin N → ℂ, l2Norm (M *ᵥ v) ≤ ρ * l2Norm v) (x : Fin N → Fin r → ℂ) :
    arrayNormSq (arrayMul M x) ≤ ρ ^ 2 * arrayNormSq x := by
  rw [arrayNormSq_eq_sum_l2Norm, arrayNormSq_eq_sum_l2Norm, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have h := hM (fun j => x j q)
  have h0 : 0 ≤ l2Norm (M *ᵥ fun j => x j q) := Real.sqrt_nonneg _
  have : (fun i => arrayMul M x i q) = M *ᵥ fun j => x j q := rfl
  rw [this, ← mul_pow]
  exact pow_le_pow_left₀ h0 h 2

theorem sqrt_arrayNormSq_arrayMul_le {M : Matrix (Fin N) (Fin N) ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hM : ∀ v : Fin N → ℂ, l2Norm (M *ᵥ v) ≤ ρ * l2Norm v) (x : Fin N → Fin r → ℂ) :
    Real.sqrt (arrayNormSq (arrayMul M x)) ≤ ρ * Real.sqrt (arrayNormSq x) := by
  calc Real.sqrt (arrayNormSq (arrayMul M x)) ≤ Real.sqrt (ρ ^ 2 * arrayNormSq x) :=
        Real.sqrt_le_sqrt (arrayNormSq_arrayMul_le hM x)
    _ = ρ * Real.sqrt (arrayNormSq x) := by
        rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ]

theorem sqrt_arrayNormSq_eq_norm (x : Fin N → Fin r → ℂ) :
    Real.sqrt (arrayNormSq x) = ‖(WithLp.toLp 2 (fun p : Fin N × Fin r => x p.1 p.2) :
      EuclideanSpace ℂ (Fin N × Fin r))‖ := by
  rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
  rfl

/-- Euclidean triangle inequality on arrays. -/
theorem sqrt_arrayNormSq_sub_le (x y : Fin N → Fin r → ℂ) :
    Real.sqrt (arrayNormSq (x - y)) ≤ Real.sqrt (arrayNormSq x) + Real.sqrt (arrayNormSq y) := by
  rw [sqrt_arrayNormSq_eq_norm, sqrt_arrayNormSq_eq_norm x, sqrt_arrayNormSq_eq_norm y]
  have : (WithLp.toLp 2 (fun p : Fin N × Fin r => (x - y) p.1 p.2) :
      EuclideanSpace ℂ (Fin N × Fin r)) = WithLp.toLp 2 (fun p : Fin N × Fin r => x p.1 p.2) -
        WithLp.toLp 2 (fun p : Fin N × Fin r => y p.1 p.2) := by
    rw [← WithLp.toLp_sub]; rfl
  rw [this]
  exact norm_sub_le _ _

/-!
## Second moments of the product circular Gaussian law
-/

theorem integrable_and_integral_sq_norm_circular (q : Fin r) :
    Integrable (fun g : Fin r → ℂ => ‖g q‖ ^ 2) (circularVectorLaw (Fin r)) ∧
      ∫ g, ‖g q‖ ^ 2 ∂circularVectorLaw (Fin r) = 1 := by
  unfold circularVectorLaw
  have hφ : Measurable (fun (x : Fin r × Fin 2 → ℝ) (c : Fin r) =>
      (x (c, 0) : ℂ) + (x (c, 1) : ℂ) * Complex.I) := by fun_prop
  have hc : Continuous fun g : Fin r → ℂ => ‖g q‖ ^ 2 := by fun_prop
  have hpt : (fun g : Fin r → ℂ => ‖g q‖ ^ 2) ∘ (fun (x : Fin r × Fin 2 → ℝ) (c : Fin r) =>
      (x (c, 0) : ℂ) + (x (c, 1) : ℂ) * Complex.I) =
      fun x => x (q, 0) * x (q, 0) + x (q, 1) * x (q, 1) := by
    funext x
    simp only [Function.comp, Complex.sq_norm, Complex.normSq_add_mul_I]
    ring
  have hi := BlockBand.Critical.Herglotz.integrable_pi_gaussianReal_mul (κ := Fin r × Fin 2)
  constructor
  · rw [integrable_map_measure hc.aestronglyMeasurable hφ.aemeasurable, hpt]
    exact (hi _ _).add (hi _ _)
  · rw [integral_map hφ.aemeasurable hc.aestronglyMeasurable]
    change ∫ x, ((fun g : Fin r → ℂ => ‖g q‖ ^ 2) ∘ (fun (x : Fin r × Fin 2 → ℝ) (c : Fin r) =>
      (x (c, 0) : ℂ) + (x (c, 1) : ℂ) * Complex.I)) x ∂_ = 1
    rw [hpt, integral_add (hi _ _) (hi _ _),
      BlockBand.Critical.Herglotz.integral_pi_gaussianReal_mul,
      BlockBand.Critical.Herglotz.integral_pi_gaussianReal_mul]
    norm_num

theorem integrable_and_integral_sq_norm_gaussianMarkLaw (i : Fin N) (q : Fin r) :
    Integrable (fun g : Fin N → Fin r → ℂ => ‖g i q‖ ^ 2) (gaussianMarkLaw N r) ∧
      ∫ g, ‖g i q‖ ^ 2 ∂gaussianMarkLaw N r = 1 := by
  have hmp := measurePreserving_eval (fun _ : Fin N => circularVectorLaw (Fin r)) i
  have hc : Continuous fun g : Fin r → ℂ => ‖g q‖ ^ 2 := by fun_prop
  obtain ⟨h1, h2⟩ := integrable_and_integral_sq_norm_circular (r := r) q
  unfold gaussianMarkLaw
  constructor
  · have h1' : Integrable (fun y : Fin r → ℂ => ‖y q‖ ^ 2)
        ((Measure.pi fun _ : Fin N => circularVectorLaw (Fin r)).map (Function.eval i)) := by
      rw [hmp.map_eq]; exact h1
    exact (integrable_map_measure hc.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).mp h1'
  · have := integral_map (μ := Measure.pi fun _ : Fin N => circularVectorLaw (Fin r))
      (measurable_pi_apply i).aemeasurable hc.aestronglyMeasurable
    rw [hmp.map_eq] at this
    exact this.symm.trans h2

theorem integrable_arrayNormSq :
    Integrable (fun g : Fin N → Fin r → ℂ => arrayNormSq g) (gaussianMarkLaw N r) := by
  unfold arrayNormSq
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun q _ =>
    (integrable_and_integral_sq_norm_gaussianMarkLaw i q).1

theorem integral_arrayNormSq :
    ∫ g, arrayNormSq g ∂gaussianMarkLaw N r = (N : ℝ) * r := by
  have h := integrable_and_integral_sq_norm_gaussianMarkLaw (N := N) (r := r)
  calc ∫ g, arrayNormSq g ∂gaussianMarkLaw N r =
        ∑ i : Fin N, ∑ q : Fin r, ∫ g, ‖g i q‖ ^ 2 ∂gaussianMarkLaw N r := by
        unfold arrayNormSq
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun q _ => (h i q).1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun q _ => (h i q).1]
    _ = (N : ℝ) * r := by simp [(h _ _).2]

theorem integrable_sqrt_arrayNormSq :
    Integrable (fun g : Fin N → Fin r → ℂ => Real.sqrt (arrayNormSq g)) (gaussianMarkLaw N r) := by
  refine (integrable_arrayNormSq.add (integrable_const 1)).mono'
    (continuous_arrayNormSq.sqrt.aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
  have h0 := arrayNormSq_nonneg g
  nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (arrayNormSq g)]

/-- `E‖G‖₂ ≤ √(E‖G‖₂²) = √(Nr)`. -/
theorem integral_sqrt_arrayNormSq_le :
    ∫ g, Real.sqrt (arrayNormSq g) ∂gaussianMarkLaw N r ≤ Real.sqrt ((N : ℝ) * r) := by
  rcases (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg r) : (0 : ℝ) ≤ N * r).eq_or_lt
    with h | h
  · have hz : ∀ g : Fin N → Fin r → ℂ, arrayNormSq g = 0 := by
      intro g
      rcases mul_eq_zero.mp h.symm with hN | hr
      · have : N = 0 := by exact_mod_cast hN
        subst this; simp [arrayNormSq]
      · have : r = 0 := by exact_mod_cast hr
        subst this; simp [arrayNormSq]
    simp only [hz, Real.sqrt_zero, integral_zero]
    exact Real.sqrt_nonneg _
  · set t := Real.sqrt ((N : ℝ) * r) with htdef
    have ht : 0 < t := Real.sqrt_pos.mpr h
    have ht2 : (N : ℝ) * r = t ^ 2 := (Real.sq_sqrt h.le).symm
    have hpt : ∀ g : Fin N → Fin r → ℂ,
        Real.sqrt (arrayNormSq g) ≤ arrayNormSq g / (2 * t) + t / 2 := by
      intro g
      have h0 := arrayNormSq_nonneg g
      rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
      nlinarith [Real.sq_sqrt h0, sq_nonneg (Real.sqrt (arrayNormSq g) - t),
        Real.sqrt_nonneg (arrayNormSq g)]
    have hi2 : Integrable (fun g : Fin N → Fin r → ℂ => arrayNormSq g / (2 * t) + t / 2)
        (gaussianMarkLaw N r) :=
      (integrable_arrayNormSq.div_const _).add (integrable_const _)
    calc ∫ g, Real.sqrt (arrayNormSq g) ∂gaussianMarkLaw N r
        ≤ ∫ g, (arrayNormSq g / (2 * t) + t / 2) ∂gaussianMarkLaw N r :=
          integral_mono integrable_sqrt_arrayNormSq hi2 hpt
      _ = (N : ℝ) * r / (2 * t) + t / 2 := by
          rw [integral_add (integrable_arrayNormSq.div_const _) (integrable_const _),
            integral_div, integral_arrayNormSq, integral_const]
          simp
      _ = t := by rw [ht2]; field_simp; ring

/-!
## Item 4: equilibration of the reference flow
-/

/-- **Item 4.** Coupling of the terminal law of the reference flow to the product circular
Gaussian law, with bounded-Lipschitz error `Lρ(‖z‖₂ + √(Nr))`. -/
theorem reference_equilibration {Ωa : Type*} [MeasurableSpace Ωa] (Pa : Measure Ωa)
    [IsProbabilityMeasure Pa] (A : Ωa → Matrix (Fin N) (Fin N) ℂ)
    (Ξa : Ωa → Fin N → Fin r → ℂ) (hA : Measurable A) (hΞ : Measurable Ξa)
    (hcov : ∀ h : Matrix (Fin N) (Fin N) ℂ → ℝ, Measurable h → (∃ C, ∀ M, |h M| ≤ C) →
      ∀ w : Fin N → Fin r → ℂ,
        ∫ ω', (h (A ω') : ℂ) * Complex.exp (Complex.I *
            (∑ i, ∑ q, (star (w i q) * Ξa ω' i q).re : ℝ)) ∂Pa =
          ∫ ω', (h (A ω') * Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
            (star (fun i => w i q) ⬝ᵥ ((1 - A ω' * (A ω')ᴴ) *ᵥ fun i => w i q)).re) : ℂ) ∂Pa)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hcontr : ∀ ω' (v : Fin N → ℂ), l2Norm (A ω' *ᵥ v) ≤ ρ * l2Norm v)
    (f : (Fin N → Fin r → ℂ) → ℝ) (hfc : Continuous f) {K L : ℝ} (hfK : ∀ z, |f z| ≤ K)
    (hL : 0 ≤ L) (hfL : ∀ x y, |f x - f y| ≤ L * Real.sqrt (arrayNormSq (x - y)))
    (z : Fin N → Fin r → ℂ) :
    |∫ ω', f (arrayMul (A ω') z + Ξa ω') ∂Pa - ∫ g, f g ∂gaussianMarkLaw N r| ≤
      L * ρ * (Real.sqrt (arrayNormSq z) + Real.sqrt ((N : ℝ) * r)) := by
  have hF : Measurable fun p : Ωa × (Fin N → Fin r → ℂ) => arrayMul (A p.1) p.2 + Ξa p.1 :=
    (measurable_arrayMul_comp (hA.comp measurable_fst) measurable_snd).add
      (hΞ.comp measurable_fst)
  have hFz : Measurable fun ω => arrayMul (A ω) z + Ξa ω :=
    (measurable_arrayMul_comp hA measurable_const).add hΞ
  have hmap := map_reference_gaussian_eq Pa A Ξa hA hΞ hcov
  have hfst : (Pa.prod (gaussianMarkLaw N r)).map Prod.fst = Pa := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : (Pa.prod (gaussianMarkLaw N r)).map Prod.snd = gaussianMarkLaw N r := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h1 : ∫ g, f g ∂gaussianMarkLaw N r =
      ∫ p, f (arrayMul (A p.1) p.2 + Ξa p.1) ∂(Pa.prod (gaussianMarkLaw N r)) := by
    conv_lhs => rw [← hmap]
    rw [integral_map hF.aemeasurable hfc.aestronglyMeasurable]
  have h2 : ∫ ω, f (arrayMul (A ω) z + Ξa ω) ∂Pa =
      ∫ p, f (arrayMul (A p.1) z + Ξa p.1) ∂(Pa.prod (gaussianMarkLaw N r)) := by
    conv_lhs => rw [← hfst]
    exact integral_map measurable_fst.aemeasurable (hfc.measurable.comp hFz).aestronglyMeasurable
  have h3 : ∫ g, Real.sqrt (arrayNormSq g) ∂gaussianMarkLaw N r =
      ∫ p, Real.sqrt (arrayNormSq p.2) ∂(Pa.prod (gaussianMarkLaw N r)) := by
    conv_lhs => rw [← hsnd]
    rw [integral_map measurable_snd.aemeasurable
      continuous_arrayNormSq.sqrt.aestronglyMeasurable]
  have hiz : Integrable (fun p : Ωa × (Fin N → Fin r → ℂ) => f (arrayMul (A p.1) z + Ξa p.1))
      (Pa.prod (gaussianMarkLaw N r)) :=
    Integrable.of_bound (hfc.measurable.comp (hFz.comp measurable_fst)).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hfK _)
  have hiF : Integrable (fun p : Ωa × (Fin N → Fin r → ℂ) => f (arrayMul (A p.1) p.2 + Ξa p.1))
      (Pa.prod (gaussianMarkLaw N r)) :=
    Integrable.of_bound (hfc.measurable.comp hF).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hfK _)
  have hsq : Integrable (fun p : Ωa × (Fin N → Fin r → ℂ) => Real.sqrt (arrayNormSq p.2))
      (Pa.prod (gaussianMarkLaw N r)) := by
    have h := integrable_sqrt_arrayNormSq (N := N) (r := r)
    rw [← hsnd] at h
    exact (integrable_map_measure continuous_arrayNormSq.sqrt.aestronglyMeasurable
      measurable_snd.aemeasurable).mp h
  have hb : ∀ p : Ωa × (Fin N → Fin r → ℂ),
      |f (arrayMul (A p.1) z + Ξa p.1) - f (arrayMul (A p.1) p.2 + Ξa p.1)| ≤
        L * ρ * (Real.sqrt (arrayNormSq z) + Real.sqrt (arrayNormSq p.2)) := by
    intro p
    refine (hfL _ _).trans ?_
    have hsub : arrayMul (A p.1) z + Ξa p.1 - (arrayMul (A p.1) p.2 + Ξa p.1) =
        arrayMul (A p.1) (z - p.2) := by
      funext i q
      simp [arrayMul, mul_sub, Finset.sum_sub_distrib]
    rw [hsub, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((sqrt_arrayNormSq_arrayMul_le hρ (hcontr p.1) _).trans
      (mul_le_mul_of_nonneg_left (sqrt_arrayNormSq_sub_le _ _) hρ)) hL
  rw [h1, h2, ← integral_sub hiz hiF]
  calc |∫ p, (f (arrayMul (A p.1) z + Ξa p.1) - f (arrayMul (A p.1) p.2 + Ξa p.1))
        ∂(Pa.prod (gaussianMarkLaw N r))|
      ≤ ∫ p, |f (arrayMul (A p.1) z + Ξa p.1) - f (arrayMul (A p.1) p.2 + Ξa p.1)|
          ∂(Pa.prod (gaussianMarkLaw N r)) := abs_integral_le_integral_abs
    _ ≤ ∫ p, L * ρ * (Real.sqrt (arrayNormSq z) + Real.sqrt (arrayNormSq p.2))
          ∂(Pa.prod (gaussianMarkLaw N r)) :=
        integral_mono (hiz.sub hiF).abs
          (((integrable_const _).add hsq).const_mul (L * ρ)) hb
    _ = L * ρ * (Real.sqrt (arrayNormSq z) +
          ∫ g, Real.sqrt (arrayNormSq g) ∂gaussianMarkLaw N r) := by
        rw [integral_const_mul, integral_add (integrable_const _) hsq, integral_const, h3]
        simp
    _ ≤ L * ρ * (Real.sqrt (arrayNormSq z) + Real.sqrt ((N : ℝ) * r)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right integral_sqrt_arrayNormSq_le _)
          (mul_nonneg hL hρ)

end BlockBand.Critical.RelativeVectors
