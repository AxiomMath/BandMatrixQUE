module

public import BlockBand.Endpoints.Sine.CrossingSine
public import BlockBand.Model.Construction.GaussianCharacteristic

/-!
# The two encodings of `GUE_d(t)` agree

**Statement (`guelawBridge_holds : GUELawBridge`).** For every finite index type `ι`, every
`e : ι ≃ Fin N` and every `t : ℝ≥0`, `gueMeasure ι t` (the law of `√(t/2)(X + X*)`, `X` a matrix
of independent standard circular entries, `commonCircularIncrementLaw ι 1`), reindexed along
`e`, is `gueMatrixLaw N t` (the Johansson upper-coordinate product law `coordinateMeasure N t`
pushed through the Hermitian reconstruction `gaussianMatrix`). Both laws live on all complex
`N × N` matrices; no hypothesis on `N`, `t` or `e` is used (`t = 0` gives the Dirac mass at `0`
on both sides).

**Proof.** Every sample of `√(t/2)(X + X*)` is Hermitian, hence is recovered from its upper
real/imaginary coordinates (`upperCoords`) by the Johansson reconstruction. It therefore
suffices to identify the law of the upper coordinates on `UpperPair N → ℝ × ℝ` with the
product `coordinateMeasure N t`, which is done with Mathlib's characteristic-function
criterion for product measures on Banach spaces (`charFunDual_eq_pi_iff`). A continuous
linear test `L` of the upper coordinates of the GUE sample is an explicit linear form
`Σ κ_k r_k` of the underlying standard real Gaussians `r` (`L_upperCoords_sample`), whose
characteristic integral is `exp(-Σ κ_k²/2)` (`gaussianProduct_characteristic`); the variance
`Σ κ_k²` regroups into the diagonal variance `t` and the off-diagonal real/imaginary variances
`t/2` of the Johansson factors (`sum_kappa_sq`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.External
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

namespace GUELaw

variable {ι : Type} {N : ℕ}

/-!
## Upper coordinates and Hermitian reconstruction
-/

/-- Real and imaginary parts of the upper (including diagonal) entries. -/
def upperCoords (A : Matrix (Fin N) (Fin N) ℂ) : Johansson.UpperPair N → ℝ × ℝ :=
  fun q => ((A q.1.1 q.1.2).re, (A q.1.1 q.1.2).im)

theorem measurable_upperCoords : Measurable (upperCoords (N := N)) := by
  apply measurable_pi_iff.mpr
  intro q
  have h : Measurable (fun A : Matrix (Fin N) (Fin N) ℂ => A q.1.1 q.1.2) :=
    (measurable_pi_apply _).comp (measurable_pi_apply _)
  exact (Complex.measurable_re.comp h).prodMk (Complex.measurable_im.comp h)

theorem gaussianMatrixRaw_upperCoords {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    Johansson.gaussianMatrixRaw (upperCoords A) = A := by
  funext i j
  unfold Johansson.gaussianMatrixRaw upperCoords
  by_cases hij : i = j
  · subst hij
    simp only [dite_true]
    exact hA.coe_re_apply_self i
  · by_cases hle : i ≤ j
    · simp only [hij, hle, dite_false, dite_true, Johansson.complexPair]
      exact Complex.re_add_im (A i j)
    · simp only [hij, hle, dite_false, Johansson.complexPair]
      rw [Complex.re_add_im]
      exact hA.apply i j

theorem measurable_gaussianMatrixRaw :
    Measurable (Johansson.gaussianMatrixRaw (N := N)) :=
  measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix

/-!
## The GUE sample in real coordinates
-/

/-- The reindexed GUE sample as a function of the underlying standard real Gaussians. -/
def sample (e : ι ≃ Fin N) (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.reindex e e (gueSample t (circularBrownianCoordinates r))

theorem measurable_circularBrownianCoordinates :
    Measurable (circularBrownianCoordinates (ι := ι)) := by
  apply measurable_pi_iff.mpr
  intro u
  unfold circularBrownianCoordinates
  fun_prop

theorem measurable_gueSample (t : ℝ≥0) :
    Measurable (gueSample (ι := ι) t) := by
  rw [Matrix.measurable_iff]
  intro a b
  unfold gueSample
  simp only [Matrix.of_apply]
  fun_prop

theorem measurable_reindex (e : ι ≃ Fin N) :
    Measurable (fun A : Matrix ι ι ℂ => Matrix.reindex e e A) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

theorem measurable_sample (e : ι ≃ Fin N) (t : ℝ≥0) : Measurable (sample e t) :=
  (measurable_reindex e).comp ((measurable_gueSample t).comp
    measurable_circularBrownianCoordinates)

theorem gueSample_isHermitian (t : ℝ≥0) (X : ι × ι → ℂ) : (gueSample t X).IsHermitian := by
  ext a b
  simp only [gueSample, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_add,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem measurable_upperCoords_sample (e : ι ≃ Fin N) (t : ℝ≥0) :
    Measurable (fun r : (ι × ι) × Fin 2 → ℝ => upperCoords (sample e t r)) :=
  measurable_upperCoords.comp (measurable_sample e t)

theorem sample_isHermitian (e : ι ≃ Fin N) (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ) :
    (sample e t r).IsHermitian :=
  (gueSample_isHermitian t _).submatrix e.symm

/-- The scale `√(t/2)/√2` of each real Gaussian in an upper coordinate. -/
def scale (t : ℝ≥0) : ℝ := Real.sqrt ((t : ℝ) / 2) / Real.sqrt 2

theorem scale_sq (t : ℝ≥0) : scale t ^ 2 = (t : ℝ) / 4 := by
  unfold scale
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)]
  ring

theorem upperCoords_sample (e : ι ≃ Fin N) (t : ℝ≥0) (r : (ι × ι) × Fin 2 → ℝ)
    (q : Johansson.UpperPair N) :
    upperCoords (sample e t r) q =
      (scale t * (r ((e.symm q.1.1, e.symm q.1.2), 0) + r ((e.symm q.1.2, e.symm q.1.1), 0)),
        scale t * (r ((e.symm q.1.1, e.symm q.1.2), 1) -
          r ((e.symm q.1.2, e.symm q.1.1), 1))) := by
  simp only [upperCoords, sample, gueSample, circularBrownianCoordinates, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.of_apply, scale]
  refine Prod.ext ?_ ?_
  · simp [Complex.mul_re, Complex.div_ofReal_re, Complex.div_ofReal_im]
    ring
  · simp [Complex.mul_im, Complex.div_ofReal_re, Complex.div_ofReal_im]
    ring

/-!
## Linear tests of the upper coordinates
-/

/-- The Banach space of upper coordinates. -/
abbrev UpperSpace (N : ℕ) := Johansson.UpperPair N → ℝ × ℝ

theorem L_single (L : StrongDual ℝ (UpperSpace N)) (q : Johansson.UpperPair N) (x y : ℝ) :
    L (Pi.single q (x, y)) =
      x * L (Pi.single q (1, 0)) + y * L (Pi.single q (0, 1)) := by
  have h : (Pi.single q (x, y) : UpperSpace N) =
      x • (Pi.single q (1, 0) : UpperSpace N) + y • (Pi.single q (0, 1) : UpperSpace N) := by
    funext q'
    by_cases hq : q' = q
    · subst hq; simp
    · simp [hq]
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

theorem L_apply (L : StrongDual ℝ (UpperSpace N)) (v : UpperSpace N) :
    L v = ∑ q, ((v q).1 * L (Pi.single q (1, 0)) + (v q).2 * L (Pi.single q (0, 1))) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← L_single]

/-- Real-part coefficient of `L`, extended by `0` below the diagonal. -/
def cA (L : StrongDual ℝ (UpperSpace N)) (i j : Fin N) : ℝ :=
  if h : i ≤ j then L (Pi.single ⟨(i, j), h⟩ (1, 0)) else 0

/-- Imaginary-part coefficient of `L`, extended by `0` below the diagonal. -/
def cB (L : StrongDual ℝ (UpperSpace N)) (i j : Fin N) : ℝ :=
  if h : i ≤ j then L (Pi.single ⟨(i, j), h⟩ (0, 1)) else 0

theorem cA_upper (L : StrongDual ℝ (UpperSpace N)) (q : Johansson.UpperPair N) :
    cA L q.1.1 q.1.2 = L (Pi.single q (1, 0)) := by
  simp [cA, q.2]

theorem cB_upper (L : StrongDual ℝ (UpperSpace N)) (q : Johansson.UpperPair N) :
    cB L q.1.1 q.1.2 = L (Pi.single q (0, 1)) := by
  simp [cB, q.2]

/-- A sum over upper pairs of a function vanishing below the diagonal is the full sum. -/
theorem sum_upper (f : Fin N → Fin N → ℝ) (hf : ∀ i j, ¬ i ≤ j → f i j = 0) :
    ∑ q : Johansson.UpperPair N, f q.1.1 q.1.2 = ∑ i, ∑ j, f i j := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≤ p.2)
    (p := fun p : Fin N × Fin N => p.1 ≤ p.2) (by simp) (fun p => f p.1 p.2),
    Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i ≤ j
  · simp [h]
  · simp [h, hf i j h]

/-- Coefficients of the linear test `L ∘ upperCoords ∘ sample` on the standard Gaussians. -/
def kappa (e : ι ≃ Fin N) (t : ℝ≥0) (L : StrongDual ℝ (UpperSpace N)) :
    (ι × ι) × Fin 2 → ℝ
  | ((a, b), c) => if c = 0 then scale t * (cA L (e a) (e b) + cA L (e b) (e a))
      else scale t * (cB L (e a) (e b) - cB L (e b) (e a))

theorem cA_lower (L : StrongDual ℝ (UpperSpace N)) {i j : Fin N} (h : ¬ i ≤ j) :
    cA L i j = 0 := by
  simp [cA, h]

theorem cB_lower (L : StrongDual ℝ (UpperSpace N)) {i j : Fin N} (h : ¬ i ≤ j) :
    cB L i j = 0 := by
  simp [cB, h]

theorem sum_swap (f g : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, (f i j + g j i) = ∑ i, ∑ j, (f i j + g i j) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => g j i)]

theorem sum_symm_half (f : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j, (f i j + f j i) / 2 = ∑ i, ∑ j, f i j := by
  have h := sum_swap f f
  simp only [← Finset.sum_div] at *
  rw [h]
  simp only [Finset.sum_add_distrib]
  ring

/-- Reindex a sum over `ι × ι` (with a `Fin 2` label) to `Fin N × Fin N`. -/
theorem sum_reindex (e : ι ≃ Fin N) [Fintype ι] (h : (ι × ι) × Fin 2 → ℝ) :
    ∑ k, h k = ∑ i, ∑ j, (h ((e.symm i, e.symm j), 0) + h ((e.symm i, e.symm j), 1)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]

/-- The upper-pair summand of `L ∘ upperCoords ∘ sample`. -/
def pairTerm (e : ι ≃ Fin N) (t : ℝ≥0) (L : StrongDual ℝ (UpperSpace N))
    (r : (ι × ι) × Fin 2 → ℝ) (i j : Fin N) : ℝ :=
  scale t * (r ((e.symm i, e.symm j), 0) + r ((e.symm j, e.symm i), 0)) * cA L i j +
    scale t * (r ((e.symm i, e.symm j), 1) - r ((e.symm j, e.symm i), 1)) * cB L i j

theorem L_upperCoords_sample [Fintype ι] (e : ι ≃ Fin N) (t : ℝ≥0)
    (L : StrongDual ℝ (UpperSpace N)) (r : (ι × ι) × Fin 2 → ℝ) :
    L (upperCoords (sample e t r)) = ∑ k, kappa e t L k * r k := by
  rw [L_apply]
  have h1 : ∀ q : Johansson.UpperPair N,
      ((upperCoords (sample e t r) q).1 * L (Pi.single q (1, 0)) +
        (upperCoords (sample e t r) q).2 * L (Pi.single q (0, 1))) =
        pairTerm e t L r q.1.1 q.1.2 := by
    intro q
    rw [upperCoords_sample, ← cA_upper, ← cB_upper]
    rfl
  rw [Finset.sum_congr rfl fun q _ => h1 q,
    sum_upper _ fun i j h => by simp [pairTerm, cA_lower L h, cB_lower L h], sum_reindex e]
  have h2 : ∀ i j, pairTerm e t L r i j =
      (scale t * cA L i j * r ((e.symm i, e.symm j), 0) +
        scale t * cB L i j * r ((e.symm i, e.symm j), 1)) +
      (scale t * cA L i j * r ((e.symm j, e.symm i), 0) -
        scale t * cB L i j * r ((e.symm j, e.symm i), 1)) := by
    intro i j
    unfold pairTerm
    ring
  simp_rw [h2]
  rw [sum_swap (fun i j => scale t * cA L i j * r ((e.symm i, e.symm j), 0) +
        scale t * cB L i j * r ((e.symm i, e.symm j), 1))
    (fun i j => scale t * cA L j i * r ((e.symm i, e.symm j), 0) -
        scale t * cB L j i * r ((e.symm i, e.symm j), 1))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [kappa, Equiv.apply_symm_apply, ↓reduceIte, one_ne_zero]
  ring

/-- Variance of the `q`-th Johansson factor against the test `L`. -/
def upperVariance (t : ℝ≥0) (L : StrongDual ℝ (UpperSpace N)) (q : Johansson.UpperPair N) :
    ℝ :=
  if q.1.1 = q.1.2 then (t : ℝ) * L (Pi.single q (1, 0)) ^ 2
  else (t : ℝ) / 2 * (L (Pi.single q (1, 0)) ^ 2 + L (Pi.single q (0, 1)) ^ 2)

theorem sum_kappa_sq [Fintype ι] (e : ι ≃ Fin N) (t : ℝ≥0) (L : StrongDual ℝ (UpperSpace N)) :
    ∑ k, kappa e t L k ^ 2 = ∑ q, upperVariance t L q := by
  set w : Fin N → Fin N → ℝ := fun i j => if i = j then (t : ℝ) * cA L i j ^ 2
    else (t : ℝ) / 2 * (cA L i j ^ 2 + cB L i j ^ 2) with hw
  have h1 : ∀ q : Johansson.UpperPair N, upperVariance t L q = w q.1.1 q.1.2 := by
    intro q
    simp only [upperVariance, hw, cA_upper, cB_upper]
  rw [Finset.sum_congr rfl fun q _ => h1 q,
    sum_upper _ fun i j h => by simp [hw, cA_lower L h, cB_lower L h], sum_reindex e,
    ← sum_symm_half w]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [kappa, Equiv.apply_symm_apply, ↓reduceIte, one_ne_zero, mul_pow,
    scale_sq, hw]
  rcases lt_trichotomy i j with h | h | h
  · have hji : ¬ j ≤ i := not_le.mpr h
    rw [cA_lower L hji, cB_lower L hji]; simp only [h.ne, h.ne', ↓reduceIte]
    ring
  · subst h
    simp only [↓reduceIte]
    ring
  · have hij : ¬ i ≤ j := not_le.mpr h
    rw [cA_lower L hij, cB_lower L hij]; simp only [h.ne, h.ne', ↓reduceIte]
    ring

/-!
## Characteristic functions
-/

theorem gaussian_integral_exp (v : ℝ≥0) (c : ℝ) :
    ∫ x, Complex.exp (((x * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 v =
      Complex.exp (-(((v : ℝ) * c ^ 2 : ℝ) : ℂ) / 2) := by
  calc ∫ x, Complex.exp (((x * c : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 v
      = ∫ x, Complex.exp ((c : ℂ) * (x : ℂ) * Complex.I) ∂gaussianReal 0 v := by
        congr 1
        funext x
        push_cast
        ring_nf
    _ = _ := by
        rw [← charFun_apply_real, charFun_gaussianReal]
        congr 1
        push_cast
        ring

theorem isFiniteMeasure_upperEntry (t : ℝ≥0) (q : Johansson.UpperPair N) :
    IsFiniteMeasure (Johansson.upperEntryMeasure t q) := by
  unfold Johansson.upperEntryMeasure
  split_ifs <;> infer_instance

/-- Characteristic function of one Johansson factor against the restriction of `L`. -/
theorem charFunDual_upperEntry (t : ℝ≥0) (L : StrongDual ℝ (UpperSpace N))
    (q : Johansson.UpperPair N) :
    charFunDual (Johansson.upperEntryMeasure t q)
        (L.comp (ContinuousLinearMap.single ℝ (fun _ : Johansson.UpperPair N => ℝ × ℝ) q)) =
      Complex.exp (-((upperVariance t L q : ℝ) : ℂ) / 2) := by
  have hLs : ∀ x y : ℝ,
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : Johansson.UpperPair N => ℝ × ℝ) q))
        (x, y) = x * L (Pi.single q (1, 0)) + y * L (Pi.single q (0, 1)) := by
    intro x y
    exact L_single L q x y
  unfold Johansson.upperEntryMeasure upperVariance
  split_ifs with hq
  · rw [charFunDual_apply, integral_map (by fun_prop)
      (by exact (by fun_prop : Continuous fun v : ℝ × ℝ =>
        Complex.exp (((L.comp (ContinuousLinearMap.single ℝ
          (fun _ : Johansson.UpperPair N => ℝ × ℝ) q)) v : ℂ) * Complex.I)).aestronglyMeasurable)]
    simp_rw [hLs, zero_mul, add_zero]
    exact gaussian_integral_exp t _
  · rw [charFunDual_prod, charFunDual_apply, charFunDual_apply]
    simp_rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, ← ContinuousLinearMap.comp_apply, hLs, zero_mul, add_zero,
      zero_add]
    rw [gaussian_integral_exp, gaussian_integral_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The upper coordinates of the reindexed GUE sample have the Johansson product law. -/
theorem upperCoords_law [Fintype ι] (e : ι ≃ Fin N) (t : ℝ≥0) :
    (Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)).map
        (fun r => upperCoords (sample e t r)) = Johansson.coordinateMeasure N t := by
  have := isFiniteMeasure_upperEntry (N := N) t
  unfold Johansson.coordinateMeasure
  rw [← charFunDual_eq_pi_iff]
  intro L
  rw [charFunDual_apply, integral_map (measurable_upperCoords_sample e t).aemeasurable
    (by exact (by fun_prop : Continuous fun v : UpperSpace N =>
      Complex.exp ((L v : ℂ) * Complex.I)).aestronglyMeasurable)]
  simp_rw [L_upperCoords_sample, charFunDual_upperEntry, ← Complex.exp_sum]
  have hg := BlockBand.Parameters.gaussianProduct_characteristic
    (fun _ : (ι × ι) × Fin 2 => (1 : ℝ≥0)) (kappa e t L)
  simp_rw [mul_comm Complex.I] at hg
  rw [hg]
  congr 1
  simp only [NNReal.coe_one, one_mul, sum_kappa_sq]
  push_cast
  rw [← Finset.sum_neg_distrib, Finset.sum_div]

end GUELaw

open GUELaw in

/-- **The GUE law bridge.** `gueMeasure ι t`, reindexed along `e : ι ≃ Fin N`, is
`gueMatrixLaw N t`, for every finite `ι`, `N`, `e` and `t`. -/
theorem guelawBridge_holds : GUELawBridge := by
  intro ι _ _ N e t
  unfold gueMeasure gueMatrixLaw commonCircularIncrementLaw
  rw [Measure.map_map (measurable_gueSample t) measurable_circularBrownianCoordinates,
    Measure.map_map (measurable_reindex e)
      ((measurable_gueSample t).comp measurable_circularBrownianCoordinates)]
  have hfun : ((fun A : Matrix ι ι ℂ => Matrix.reindex e e A) ∘
      (gueSample t ∘ circularBrownianCoordinates)) =
      Johansson.gaussianMatrixRaw ∘ (fun r => upperCoords (sample e t r)) :=
    funext fun r => (gaussianMatrixRaw_upperCoords (sample_isHermitian e t r)).symm
  rw [hfun, ← Measure.map_map measurable_gaussianMatrixRaw
    (measurable_upperCoords_sample e t), upperCoords_law]
  rfl

end BlockBand.Endpoints
