module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFSplit
public import BlockBand.Palm.ReferenceFlowHeat

/-!
# The reference covariance in characteristic-functional form

`rfCovariance_holds`: `RFCovarianceStatement N r` holds for every `N r`.

* `integral_cexp_pi_gaussianReal`: characteristic function of i.i.d. centred real Gaussians on
  any finite index type, `E exp(i Σ_k c_k x_k) = exp(-(v/2) Σ_k c_k²)`.
* `integral_cexp_matCircularLaw`: for the standard circular `N × r` array `G ∼ matCircularLaw`
  and any `u`, `E exp(i Σ_{j,q} Re(conj(u_jq) G_jq)) = exp(-¼ Σ_{j,q} |u_jq|²)`.
* `sum_re_star_arrayMul`: `Σ_{i,q} Re(conj(w_iq) (L G)_iq) = Σ_{j,q} Re(conj((Lᴴ w)_jq) G_jq)`.
* `sum_normSq_arrayMul_conjTranspose`: `Σ_{j,q} |(Lᴴ w)_jq|² = Σ_q Re(w_q^* L Lᴴ w_q)`.
* `rfCovariance_holds`: integrate `G` first (`integral_prod`), then replace `L Lᴴ` by
  `1 - M Mᴴ` on the `P`-a.s. set of the hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.AbstractFlow

open MeasureTheory Matrix ProbabilityTheory
open scoped NNReal

variable {N r : ℕ}

/-- Characteristic function of a finite product of i.i.d. centred real Gaussians. -/
theorem integral_cexp_pi_gaussianReal {σ : Type*} [Fintype σ] (c : σ → ℝ) (v : ℝ≥0) :
    ∫ x, Complex.exp (((∑ k, c k * x k : ℝ) : ℂ) * Complex.I)
        ∂(Measure.pi fun _ : σ => gaussianReal 0 v) =
      ((Real.exp (-((v : ℝ) / 2 * ∑ k, c k ^ 2)) : ℝ) : ℂ) := by
  have e : ∀ x : σ → ℝ, Complex.exp (((∑ k, c k * x k : ℝ) : ℂ) * Complex.I) =
      ∏ k, Complex.exp (((c k : ℝ) : ℂ) * ((x k : ℝ) : ℂ) * Complex.I) := fun x => by
    rw [← Complex.exp_sum]
    congr 1
    simp [Finset.sum_mul]
  simp_rw [e]
  rw [integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun k (y : ℝ) => Complex.exp (((c k : ℝ) : ℂ) * ((y : ℝ) : ℂ) * Complex.I))]
  simp_rw [← charFun_apply_real, charFun_gaussianReal, ← Complex.exp_sum]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The real coefficient vector of `G ↦ Σ_{j,q} Re(conj(u_jq) G_jq)` in the real Gaussian
coordinates of `matCircularLaw`. -/
def circCoeff (u : Fin N → Fin r → ℂ) (k : BlockBand.Palm.ReferenceFlow.CircIdx N r) : ℝ :=
  ![(u k.1.1 k.1.2).re, (u k.1.1 k.1.2).im] k.2

theorem sum_re_star_circSample (u : Fin N → Fin r → ℂ)
    (x : BlockBand.Palm.ReferenceFlow.CircIdx N r → ℝ) :
    ∑ j, ∑ q, (star (u j q) * BlockBand.Palm.ReferenceFlow.circSample N r x j q).re =
      ∑ k, circCoeff u k * x k := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Fin.sum_univ_two, BlockBand.Palm.ReferenceFlow.circSample_apply]
  simp [circCoeff, Complex.mul_re, Complex.mul_im]

theorem sum_circCoeff_sq (u : Fin N → Fin r → ℂ) :
    ∑ k, circCoeff u k ^ 2 = ∑ j, ∑ q, Complex.normSq (u j q) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Fin.sum_univ_two, Complex.normSq_apply]
  simp [circCoeff]
  ring

/-- Characteristic functional of the standard circular array: for `G ∼ matCircularLaw N r`,
`E exp(i Σ_{j,q} Re(conj(u_jq) G_jq)) = exp(-¼ Σ_{j,q} |u_jq|²)`. -/
theorem integral_cexp_matCircularLaw (u : Fin N → Fin r → ℂ) :
    ∫ G, Complex.exp (Complex.I * ((∑ j, ∑ q, (star (u j q) * G j q).re : ℝ) : ℂ))
        ∂BlockBand.Palm.ReferenceFlow.matCircularLaw N r =
      ((Real.exp (-(1 / 4 : ℝ) * ∑ j, ∑ q, Complex.normSq (u j q)) : ℝ) : ℂ) := by
  rw [BlockBand.Palm.ReferenceFlow.integral_matCircularLaw (by fun_prop)]
  simp_rw [sum_re_star_circSample, mul_comm Complex.I]
  rw [BlockBand.Palm.ReferenceFlow.circGauss, BlockBand.Internal.Contracts.Inputs.gaussianProduct,
    integral_cexp_pi_gaussianReal, sum_circCoeff_sq]
  congr 2
  push_cast
  ring

/-- `Σ_{i,q} Re(conj(w_iq) (L G)_iq) = Σ_{j,q} Re(conj((Lᴴ w)_jq) G_jq)`. -/
theorem sum_re_star_arrayMul (L : Matrix (Fin N) (Fin N) ℂ) (w G : Fin N → Fin r → ℂ) :
    ∑ i, ∑ q, (star (w i q) * arrayMul L G i q).re =
      ∑ j, ∑ q, (star (arrayMul Lᴴ w j q) * G j q).re := by
  simp only [← Complex.re_sum]
  congr 1
  simp only [arrayMul, conjTranspose_apply, star_sum, star_mul', star_star, Finset.mul_sum,
    Finset.sum_mul]
  calc _ = ∑ i, ∑ j, ∑ q, L i j * star (w i q) * G j q := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm (β := ℂ)]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_comm (β := ℂ)]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_comm

/-- `Σ_{j,q} |(Lᴴ w)_jq|² = Σ_q Re(w_q^* L Lᴴ w_q)`. -/
theorem sum_normSq_arrayMul_conjTranspose (L : Matrix (Fin N) (Fin N) ℂ)
    (w : Fin N → Fin r → ℂ) :
    ∑ j, ∑ q, Complex.normSq (arrayMul Lᴴ w j q) =
      ∑ q : Fin r, (star (fun i => w i q) ⬝ᵥ ((L * Lᴴ) *ᵥ fun i => w i q)).re := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hv : (fun j => arrayMul Lᴴ w j q) = Lᴴ *ᵥ fun i => w i q := rfl
  have hs : star (fun i => w i q) ᵥ* L = star (Lᴴ *ᵥ fun i => w i q) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [← mulVec_mulVec, dotProduct_mulVec, hs, ← hv]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

/-- `RFCovarianceStatement` holds for all `N r`. -/
theorem rfCovariance_holds :
    ∀ N r, BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.RFCovarianceStatement N r := by
  intro N r Ωd _ P _ M L hM hL hLL h hh hC w
  obtain ⟨C, hC⟩ := hC
  set μG := BlockBand.Palm.ReferenceFlow.matCircularLaw N r
  have hmeasL : Measurable fun p : Ωd × (Fin N → Fin r → ℂ) =>
      (∑ i, ∑ q, (star (w i q) * arrayMul (L p.1) p.2 i q).re : ℝ) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun q _ => ?_
    refine Complex.measurable_re.comp (measurable_const.mul ?_)
    refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.mul ?_ ?_
    · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hL.comp measurable_fst))
    · exact (measurable_pi_apply q).comp ((measurable_pi_apply j).comp measurable_snd)
  have hmeash : Measurable fun p : Ωd × (Fin N → Fin r → ℂ) => (h (M p.1) : ℂ) :=
    Complex.measurable_ofReal.comp (hh.comp (hM.comp measurable_fst))
  have hint : Integrable (fun p : Ωd × (Fin N → Fin r → ℂ) => (h (M p.1) : ℂ) *
      Complex.exp (Complex.I *
        (∑ i, ∑ q, (star (w i q) * arrayMul (L p.1) p.2 i q).re : ℝ))) (P.prod μG) := by
    refine Integrable.of_bound
      (hmeash.mul (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp hmeasL)))).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact hC _
  rw [integral_prod _ hint]
  have hfst := integral_fun_fst (μ := P) (ν := μG) (fun y => (h (M y) : ℂ) *
    ((Real.exp (-(1 / 4 : ℝ) * ∑ q : Fin r,
      (star (fun i => w i q) ⬝ᵥ ((1 - M y * (M y)ᴴ) *ᵥ fun i => w i q)).re) : ℝ) : ℂ))
  rw [hfst, probReal_univ, one_smul]
  refine integral_congr_ae ?_
  filter_upwards [hLL] with y hy
  rw [integral_const_mul]
  simp_rw [sum_re_star_arrayMul]
  rw [integral_cexp_matCircularLaw, sum_normSq_arrayMul_conjTranspose, hy]

end BlockBand.Critical.RelativeVectors.AbstractFlow
