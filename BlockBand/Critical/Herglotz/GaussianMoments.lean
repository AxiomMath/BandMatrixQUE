module

public import Mathlib
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Covariance of the standard circular Gaussian vector

The decorations `g_j` of the canonical Cauchy series are standard circular Gaussian vectors,
`E g gᴴ = I_r`; this is used in `E Im 𝖢_r = I_r`.

* `integral_circularVectorLaw_mul_conj` — for the law `circularVectorLaw ι` (density
  `π^{-d} e^{-‖g‖²}`, defined as the image of independent `N(0, 1/2)` real and imaginary parts),
  `∫ g_a conj(g_b) dγ = δ_ab`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate NNReal

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

/-- Second moments of independent `N(0, 1/2)` coordinates: `E r_p r_q = δ_pq / 2`. -/
theorem integral_pi_gaussianReal_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (p q : κ) :
    ∫ r : κ → ℝ, r p * r q ∂(Measure.pi fun _ : κ => gaussianReal 0 (1 / 2 : ℝ≥0)) =
      if p = q then 1 / 2 else 0 := by
  set μ := Measure.pi fun _ : κ => gaussianReal 0 (1 / 2 : ℝ≥0)
  have hev (k : κ) := measurePreserving_eval (fun _ : κ => gaussianReal 0 (1 / 2 : ℝ≥0)) k
  have hcomp (k : κ) (g : ℝ → ℝ) (hg : Continuous g) :
      ∫ r : κ → ℝ, g (r k) ∂μ = ∫ x, g x ∂gaussianReal 0 (1 / 2 : ℝ≥0) := by
    rw [← (hev k).map_eq, integral_map (measurable_pi_apply k).aemeasurable
      hg.aestronglyMeasurable]
  have hmean (k : κ) : ∫ r : κ → ℝ, r k ∂μ = 0 := by
    rw [hcomp k (fun x => x) continuous_id, integral_id_gaussianReal]
  by_cases hpq : p = q
  · subst hpq
    simp only [ite_true]
    have h1 : ∫ r : κ → ℝ, r p * r p ∂μ = ∫ x : ℝ, x * x ∂gaussianReal 0 (1 / 2 : ℝ≥0) :=
      hcomp p (fun x => x * x) (continuous_id.mul continuous_id)
    rw [h1]
    have hv := variance_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0))
    rw [variance_eq_integral measurable_id.aemeasurable] at hv
    simp only [id, integral_id_gaussianReal, sub_zero] at hv
    have : (fun x : ℝ => x * x) = fun x => x ^ 2 := by funext x; ring
    rw [this, hv]
    norm_num
  · simp only [hpq, ite_false]
    have hind : iIndepFun (fun k (r : κ → ℝ) => r k) μ :=
      iIndepFun_pi (X := fun _ (x : ℝ) => x) fun _ => measurable_id.aemeasurable
    have hpq' := hind.indepFun hpq
    have := hpq'.integral_mul_eq_mul_integral (𝕜 := ℝ)
      (measurable_pi_apply p).aestronglyMeasurable (measurable_pi_apply q).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hmean, zero_mul]

theorem integrable_pi_gaussianReal_mul {κ : Type*} [Fintype κ] (p q : κ) :
    Integrable (fun r : κ → ℝ => r p * r q)
      (Measure.pi fun _ : κ => gaussianReal 0 (1 / 2 : ℝ≥0)) := by
  have hev (k : κ) := measurePreserving_eval (fun _ : κ => gaussianReal 0 (1 / 2 : ℝ≥0)) k
  have hL (k : κ) : MemLp (fun r : κ → ℝ => r k) 2
      (Measure.pi fun _ : κ => gaussianReal 0 (1 / 2 : ℝ≥0)) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) 2).comp_measurePreserving
      (hev k)
    simpa using h
  exact (hL p).integrable_mul (hL q)

/-- **Covariance of the standard circular Gaussian vector**: `∫ g_a conj(g_b) dγ = δ_ab`. -/
theorem integral_circularVectorLaw_mul_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    ∫ g, g a * conj (g b) ∂circularVectorLaw ι = if a = b then 1 else 0 := by
  unfold circularVectorLaw
  set μ := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)
  have hφ : Measurable (fun (r : ι × Fin 2 → ℝ) (c : ι) =>
      (r (c, 0) : ℂ) + (r (c, 1) : ℂ) * Complex.I) := by fun_prop
  rw [integral_map hφ.aemeasurable (by fun_prop)]
  -- expand into real second moments
  have hexp : ∀ r : ι × Fin 2 → ℝ,
      ((r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) *
        conj ((r (b, 0) : ℂ) + (r (b, 1) : ℂ) * Complex.I) =
      ((r (a, 0) * r (b, 0) + r (a, 1) * r (b, 1) : ℝ) : ℂ) +
        ((r (a, 1) * r (b, 0) - r (a, 0) * r (b, 1) : ℝ) : ℂ) * Complex.I := by
    intro r
    apply Complex.ext
    · simp
    · simp; ring
  simp_rw [hexp]
  have hi := integrable_pi_gaussianReal_mul (κ := ι × Fin 2)
  rw [integral_add, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_add (hi _ _) (hi _ _), integral_sub (hi _ _) (hi _ _)]
  · simp only [integral_pi_gaussianReal_mul, Prod.mk.injEq]
    by_cases hab : a = b
    · subst hab; norm_num
    · simp [hab]
  · exact ((hi _ _).add (hi _ _)).ofReal
  · exact (((hi _ _).sub (hi _ _)).ofReal).mul_const _

end BlockBand.Critical.Herglotz
