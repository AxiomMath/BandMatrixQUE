module

public import BlockBand.DeterminantScore.Sector.Coordinates
public import BlockBand.Model.Construction.GaussianCharacteristic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# The coordinate law of `G_m(t)` is `gueMeasure`

Proof: `gueSample t ∘ circularBrownianCoordinates = hermOfCoord ∘ gueCoord t` for an explicit
linear map `gueCoord t` of the standard real Gaussian vector, and the law of `gueCoord t` is
`hermGaussian m t` by equality of characteristic functions (`Measure.ext_of_charFunDual`,
with `gaussianProduct_characteristic`): the covariance of `gueCoord t` is
`diag(hermVariance m t)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal
open BlockBand.Internal.Contracts

variable {m : ℕ}

/-- The real coordinates of `gueSample t (circularBrownianCoordinates r)`. -/
def gueCoord (t : ℝ≥0) (r : ((Fin m × Fin m) × Fin 2) → ℝ) : HermCoord m → ℝ :=
  fun c => if c.1 = c.2 then Real.sqrt t * r ((c.1, c.1), 0)
    else if c.1 < c.2 then Real.sqrt t / 2 * (r ((c.1, c.2), 0) + r ((c.2, c.1), 0))
    else Real.sqrt t / 2 * (r ((c.2, c.1), 1) - r ((c.1, c.2), 1))

theorem continuous_gueCoord (t : ℝ≥0) : Continuous (gueCoord (m := m) t) := by
  refine continuous_pi fun c => ?_
  unfold gueCoord
  split_ifs <;> fun_prop

theorem gueSample_circular (t : ℝ≥0) (r : ((Fin m × Fin m) × Fin 2) → ℝ) :
    CoareaPalm.gueSample t (BlockBand.SourceProcess.circularBrownianCoordinates r) =
      hermOfCoord (gueCoord t r) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h2ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  have hs : ((Real.sqrt ((t : ℝ) / 2) : ℝ) : ℂ) = (Real.sqrt t : ℂ) / (Real.sqrt 2 : ℂ) := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2), ofReal_div]
  ext a b
  simp only [CoareaPalm.gueSample, BlockBand.SourceProcess.circularBrownianCoordinates,
    Matrix.of_apply, hermOfCoord_apply, gueCoord, hs, map_div₀, map_add, map_mul,
    conj_ofReal, conj_I]
  rcases lt_trichotomy a b with h | rfl | h
  · simp only [h.ne, h.ne', ↓reduceIte, h, not_lt_of_gt h]
    field_simp
    push_cast
    linear_combination (-1 / 2 : ℂ) * (((Real.sqrt t : ℂ) * (r ((a, b), 0) : ℂ) +
      (Real.sqrt t : ℂ) * (r ((b, a), 0) : ℂ) + (Real.sqrt t : ℂ) * (r ((a, b), 1) : ℂ) * I -
      (Real.sqrt t : ℂ) * (r ((b, a), 1) : ℂ) * I)) * h2
  · simp only [↓reduceIte]
    field_simp
    push_cast
    linear_combination (-(Real.sqrt t : ℂ) * (r ((a, a), 0) : ℂ)) * h2
  · simp only [h.ne, h.ne', ↓reduceIte, h, not_lt_of_gt h]
    field_simp
    push_cast
    linear_combination (-1 / 2 : ℂ) * (((Real.sqrt t : ℂ) * (r ((a, b), 0) : ℂ) +
      (Real.sqrt t : ℂ) * (r ((b, a), 0) : ℂ) + (Real.sqrt t : ℂ) * (r ((a, b), 1) : ℂ) * I -
      (Real.sqrt t : ℂ) * (r ((b, a), 1) : ℂ) * I)) * h2

/-- Characteristic function of a finite product of centered real Gaussians. -/
theorem charFunDual_gaussianPi {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℝ≥0)
    (L : StrongDual ℝ (σ → ℝ)) :
    charFunDual (Measure.pi fun i => gaussianReal 0 (w i)) L =
      Complex.exp (-((∑ i, (w i : ℝ) * (L (Pi.single i 1)) ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFunDual_apply,
    ← BlockBand.Parameters.gaussianProduct_characteristic w (fun i => L (Pi.single i 1))]
  congr 1
  funext z
  rw [mul_comm]
  congr 3
  have h := LinearMap.pi_apply_eq_sum_univ (L : (σ → ℝ) →ₗ[ℝ] ℝ) z
  have hs : ∀ i : σ, (fun j : σ => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := fun i => by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simp [hji, Ne.symm hji]
  simp only [hs, smul_eq_mul, ContinuousLinearMap.coe_coe] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The coefficients of `Σ_c a_c (gueCoord t r)_c` in the standard Gaussian coordinates. -/
def gueCoeff (t : ℝ≥0) (a : HermCoord m → ℝ) (j : (Fin m × Fin m) × Fin 2) : ℝ :=
  if j.2 = 0 then
    (if j.1.1 = j.1.2 then Real.sqrt t * a (j.1.1, j.1.1)
      else if j.1.1 < j.1.2 then Real.sqrt t / 2 * a j.1
      else Real.sqrt t / 2 * a (j.1.2, j.1.1))
  else
    (if j.1.1 = j.1.2 then 0
      else if j.1.1 < j.1.2 then Real.sqrt t / 2 * a (j.1.2, j.1.1)
      else -(Real.sqrt t / 2 * a j.1))

theorem sum_prod_fin_two (f : (Fin m × Fin m) × Fin 2 → ℝ) :
    ∑ j, f j = ∑ c : Fin m × Fin m, (f (c, 0) + f (c, 1)) := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

theorem sum_swap (f : Fin m × Fin m → ℝ) : ∑ c : Fin m × Fin m, f c.swap = ∑ c, f c :=
  (Equiv.prodComm (Fin m) (Fin m)).sum_comp f

theorem sum_mul_gueCoord (t : ℝ≥0) (a : HermCoord m → ℝ) (r : ((Fin m × Fin m) × Fin 2) → ℝ) :
    ∑ c, a c * gueCoord t r c = ∑ j, gueCoeff t a j * r j := by
  set own : Fin m × Fin m → ℝ := fun c =>
    if c.1 = c.2 then Real.sqrt t * a c * r ((c.1, c.1), 0)
    else if c.1 < c.2 then Real.sqrt t / 2 * a c * r (c, 0)
    else -(Real.sqrt t / 2 * a c * r (c, 1))
  set tr : Fin m × Fin m → ℝ := fun c =>
    if c.1 = c.2 then 0
    else if c.1 < c.2 then Real.sqrt t / 2 * a c * r ((c.2, c.1), 0)
    else Real.sqrt t / 2 * a c * r ((c.2, c.1), 1)
  have h1 : ∀ c, a c * gueCoord t r c = own c + tr c := fun c => by
    simp only [own, tr, gueCoord]
    split_ifs <;> ring
  simp_rw [h1, Finset.sum_add_distrib]
  rw [← sum_swap tr, ← Finset.sum_add_distrib, sum_prod_fin_two]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨p, q⟩ := c
  simp only [own, tr, gueCoeff, Prod.swap_prod_mk]
  rcases lt_trichotomy p q with h | rfl | h
  · simp [h.ne, h.ne', h, not_lt_of_gt h]
  · simp
  · simp [h.ne, h.ne', h, not_lt_of_gt h]
    ring

theorem sum_sq_gueCoeff (t : ℝ≥0) (a : HermCoord m → ℝ) :
    ∑ j, (1 : ℝ) * gueCoeff t a j ^ 2 = ∑ c, (hermVariance m t c : ℝ) * a c ^ 2 := by
  have hst : Real.sqrt (t : ℝ) ^ 2 = t := Real.sq_sqrt (NNReal.coe_nonneg t)
  set D : Fin m × Fin m → ℝ := fun c => if c.1 = c.2 then (t : ℝ) * a c ^ 2 else 0
  set E : Fin m × Fin m → ℝ := fun c => if c.1 = c.2 then 0 else (t : ℝ) / 4 * a c ^ 2
  have h1 : ∀ c : Fin m × Fin m, (1 : ℝ) * gueCoeff t a (c, 0) ^ 2 + 1 * gueCoeff t a (c, 1) ^ 2 =
      D c + E c + E c.swap := fun c => by
    obtain ⟨p, q⟩ := c
    simp only [D, E, gueCoeff, Prod.swap_prod_mk]
    rcases lt_trichotomy p q with h | rfl | h
    · simp only [h.ne, h.ne', h, ↓reduceIte, Fin.isValue, one_ne_zero]
      linear_combination ((a (p, q) ^ 2 + a (q, p) ^ 2) / 4) * hst
    · simp only [↓reduceIte, Fin.isValue, one_ne_zero]
      linear_combination (a (p, p) ^ 2) * hst
    · simp only [h.ne, h.ne', not_lt_of_gt h, ↓reduceIte, Fin.isValue, one_ne_zero]
      linear_combination ((a (p, q) ^ 2 + a (q, p) ^ 2) / 4) * hst
  rw [sum_prod_fin_two]
  simp_rw [h1, Finset.sum_add_distrib]
  rw [sum_swap E, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [D, E, hermVariance]
  split_ifs <;> push_cast <;> ring

instance (t : ℝ≥0) : IsProbabilityMeasure (hermGaussian m t) := by
  unfold hermGaussian Inputs.gaussianProduct
  infer_instance

/-- The law of `gueCoord t` under the standard Gaussian product is `hermGaussian m t`. -/
theorem map_gueCoord (t : ℝ≥0) :
    (Measure.pi fun _ : (Fin m × Fin m) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)).map
      (gueCoord t) = hermGaussian m t := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, integral_map (continuous_gueCoord t).aemeasurable
    (by fun_prop)]
  rw [hermGaussian, Inputs.gaussianProduct, charFunDual_gaussianPi]
  have hL : ∀ r, L (gueCoord t r) =
      ∑ j, gueCoeff t (fun c => L (Pi.single c 1)) j * r j := fun r => by
    rw [← sum_mul_gueCoord]
    have h := LinearMap.pi_apply_eq_sum_univ (L : (HermCoord m → ℝ) →ₗ[ℝ] ℝ) (gueCoord t r)
    have hs : ∀ i : HermCoord m, (fun j : HermCoord m => if i = j then (1 : ℝ) else 0) =
        Pi.single i 1 := fun i => by
      funext j
      rcases eq_or_ne j i with rfl | hji
      · simp
      · simp [hji, Ne.symm hji]
    simp only [hs, smul_eq_mul, ContinuousLinearMap.coe_coe] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [hL]
  have hc := BlockBand.Parameters.gaussianProduct_characteristic
    (fun _ : (Fin m × Fin m) × Fin 2 => (1 : ℝ≥0)) (gueCoeff t fun c => L (Pi.single c 1))
  simp only [NNReal.coe_one] at hc
  rw [sum_sq_gueCoeff] at hc
  rw [← hc]
  congr 1
  funext z
  rw [mul_comm]

theorem continuous_gueSample (t : ℝ≥0) :
    Continuous (CoareaPalm.gueSample (ι := Fin m) t) := by
  refine continuous_matrix fun a b => ?_
  simp only [CoareaPalm.gueSample, Matrix.of_apply]
  fun_prop

theorem continuous_circularBrownianCoordinates :
    Continuous (BlockBand.SourceProcess.circularBrownianCoordinates (ι := Fin m)) := by
  refine continuous_pi fun u => ?_
  simp only [BlockBand.SourceProcess.circularBrownianCoordinates]
  fun_prop

/-- **The coordinate law of `G_m(t)`**:
`hermOfCoord` pushes `hermGaussian m t` forward to the
`CoareaPalm.gueMeasure (Fin m) t`.
-/
theorem map_hermOfCoord_hermGaussian (t : ℝ≥0) :
    (hermGaussian m t).map hermOfCoord = CoareaPalm.gueMeasure (Fin m) t := by
  unfold CoareaPalm.gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  rw [Measure.map_map (continuous_gueSample t).measurable
    continuous_circularBrownianCoordinates.measurable]
  have h : CoareaPalm.gueSample t ∘ BlockBand.SourceProcess.circularBrownianCoordinates =
      hermOfCoord ∘ gueCoord (m := m) t := funext (gueSample_circular t)
  rw [h, ← Measure.map_map continuous_hermOfCoord.measurable (continuous_gueCoord t).measurable,
    map_gueCoord]

end BlockBand.DeterminantScore.Sector
