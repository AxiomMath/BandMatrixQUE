module

public import BlockBand.Internal.Contracts.CoareaPalm
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Dimension-free Gaussian moments of positive quadratic forms

Law: `h ~ CN(0, I_ι)` (`CoareaPalm.circularVectorLaw ι`: `h_a = r_{a,0} + i r_{a,1}`,
`r ~ Π N(0, 1/2)`). Statement (`tco_lintegral_quadForm_pow_le`): for every `m` there is one
constant `c_m`, **independent of the dimension `|ι|`**, with
`E_h (h*Qh)^m ≤ c_m (Tr Q)^m` for every positive semidefinite `Q`. Proof: unitary invariance of
`h` (`tco_circularVectorLaw_map_unitary`; the real rotation induced by a unitary is an isometry
of `EuclideanSpace ℝ (ι × Fin 2)` and `ProbabilityTheory.stdGaussian_map`), the spectral
decomposition `h*Qh = Σ_i λ_i |(U*h)_i|²`, Jensen with weights `λ_i/Tr Q`, and the fixed scalar
moment `E|h_a|^{2m} ≤ 2^{m+1} E x^{2m}`, `x ~ N(0,1/2)`. No hypothesis.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix WithLp
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {ι : Type}

/-!
## Unitary invariance of the circular Gaussian vector
-/

/-- Complexification `r ↦ (r_{a,0} + i r_{a,1})_a` (the map defining `circularVectorLaw`). -/
def tco_cplx (r : ι × Fin 2 → ℝ) : ι → ℂ := fun a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I

/-- Realification `w ↦ (Re w_a, Im w_a)`. -/
def tco_real (w : ι → ℂ) : ι × Fin 2 → ℝ := fun p => if p.2 = 0 then (w p.1).re else (w p.1).im

theorem tco_cplx_real (w : ι → ℂ) : tco_cplx (tco_real w) = w := by
  funext a
  simp [tco_cplx, tco_real]

theorem tco_real_cplx (r : ι × Fin 2 → ℝ) : tco_real (tco_cplx r) = r := by
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases j <;> simp [tco_cplx, tco_real]

theorem tco_continuous_cplx : Continuous (tco_cplx (ι := ι)) := by
  unfold tco_cplx
  fun_prop

theorem tco_sum_sq_real [Fintype ι] (w : ι → ℂ) :
    ∑ p, tco_real w p ^ 2 = ∑ a, Complex.normSq (w a) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [tco_real, Fin.sum_univ_two, Complex.normSq_apply, pow_two]

theorem tco_sum_normSq_unitary [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    ∑ a, Complex.normSq ((U *ᵥ v) a) = ∑ a, Complex.normSq (v a) := by
  have key (w : ι → ℂ) : ((∑ a, Complex.normSq (w a) : ℝ) : ℂ) = star w ⬝ᵥ w := by
    simp [dotProduct, Complex.normSq_eq_conj_mul_self]
  apply Complex.ofReal_injective
  rw [key, key, star_mulVec, dotProduct_mulVec, vecMul_vecMul,
    show Uᴴ * U = 1 from (Matrix.mem_unitaryGroup_iff').1 hU, vecMul_one]

/-- The real rotation induced by `U`. -/
def tco_rot [Fintype ι] (U : Matrix ι ι ℂ) : (ι × Fin 2 → ℝ) →ₗ[ℝ] (ι × Fin 2 → ℝ) where
  toFun r := tco_real (U *ᵥ tco_cplx r)
  map_add' r s := by
    have : tco_cplx (r + s) = tco_cplx r + tco_cplx s := by
      funext a; simp [tco_cplx]; ring
    rw [this, mulVec_add]
    funext p; simp only [tco_real, Pi.add_apply]; split_ifs <;> simp
  map_smul' t r := by
    have : tco_cplx (t • r) = (t : ℂ) • tco_cplx r := by
      funext a; simp [tco_cplx]; ring
    rw [this, mulVec_smul]
    funext p; simp only [tco_real, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

theorem tco_rot_apply [Fintype ι] (U : Matrix ι ι ℂ) (r : ι × Fin 2 → ℝ) :
    tco_rot U r = tco_real (U *ᵥ tco_cplx r) := rfl

theorem tco_sum_sq_rot [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (r : ι × Fin 2 → ℝ) :
    ∑ p, tco_rot U r p ^ 2 = ∑ p, r p ^ 2 := by
  rw [tco_rot_apply, tco_sum_sq_real, tco_sum_normSq_unitary U hU, ← tco_sum_sq_real,
    tco_real_cplx]

/-- The rotation as a linear isometry equivalence of `EuclideanSpace ℝ (ι × Fin 2)`. -/
def tco_rotIso [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ι × Fin 2) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → ℝ)).symm.toLinearMap ∘ₗ tco_rot U ∘ₗ
        (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → ℝ)).toLinearMap
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          Real.norm_eq_abs, sq_abs]
        exact tco_sum_sq_rot U hU _ }
    rfl

/-- The standard product Gaussian on `ι × Fin 2` is invariant under the rotation. -/
theorem tco_pi_std_map_rot [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1).map (tco_rot U) =
      Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1 := by
  set P := Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1
  have hP : P = (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map ofLp := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
      show (ofLp ∘ toLp 2 : (ι × Fin 2 → ℝ) → _) = id from rfl, Measure.map_id]
  have hfun : (tco_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) ∘ ofLp =
      ofLp ∘ tco_rotIso U hU := by
    funext x; rfl
  have hrot_m : Measurable (tco_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  conv_lhs => rw [hP, Measure.map_map hrot_m (by fun_prop), hfun,
    ← Measure.map_map (by fun_prop) (tco_rotIso U hU).continuous.measurable,
    stdGaussian_map]
  exact hP.symm

theorem tco_gaussianReal_half :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (1 / 2) * x) =
      gaussianReal 0 (1 / 2 : ℝ≥0) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt]

theorem tco_pi_half_eq_map [Fintype ι] :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 1).map
        (fun r p => Real.sqrt (1 / 2) * r p) := by
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  simp_rw [tco_gaussianReal_half]

/-- **Unitary invariance of `circularVectorLaw`.** -/
theorem tco_circularVectorLaw_map_unitary [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (circularVectorLaw ι).map (fun h => U *ᵥ h) = circularVectorLaw ι := by
  have hlaw : circularVectorLaw ι =
      (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map tco_cplx := rfl
  have hrot_m : Measurable (tco_rot U : (ι × Fin 2 → ℝ) → (ι × Fin 2 → ℝ)) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hsc_m : Measurable
      (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p) := by fun_prop
  have hU_m : Measurable (fun h : ι → ℂ => U *ᵥ h) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hcomm : (fun h : ι → ℂ => U *ᵥ h) ∘ tco_cplx ∘
      (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p) =
      (tco_cplx ∘ (fun (r : ι × Fin 2 → ℝ) (p : ι × Fin 2) => Real.sqrt (1 / 2) * r p)) ∘
        tco_rot U := by
    funext r
    simp only [Function.comp_apply]
    have hs (s : ι × Fin 2 → ℝ) : tco_cplx (fun p => Real.sqrt (1 / 2) * s p) =
        ((Real.sqrt (1 / 2) : ℝ) : ℂ) • tco_cplx s := by
      funext a; simp [tco_cplx]; ring
    rw [hs, hs, tco_rot_apply, tco_cplx_real, mulVec_smul]
  rw [hlaw, tco_pi_half_eq_map, Measure.map_map tco_continuous_cplx.measurable hsc_m,
    Measure.map_map hU_m (tco_continuous_cplx.measurable.comp hsc_m), hcomm,
    ← Measure.map_map (tco_continuous_cplx.measurable.comp hsc_m) hrot_m,
    tco_pi_std_map_rot U hU]

/-!
## The scalar moment of one coordinate
-/

theorem tco_isProbabilityMeasure_circularVectorLaw [Fintype ι] :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance

theorem tco_integrable_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  have hn :=
    (memLp_id_gaussianReal' (μ := 0) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  refine hn.mono' (by fun_prop) ?_
  filter_upwards with x
  simp only [norm_pow, id_eq]
  exact le_rfl

/-- The fixed scalar constant `M_m = ∫ x^{2m} dN(0,1/2)`. -/
def tco_halfMoment (m : ℕ) : ℝ := ∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 (1 / 2 : ℝ≥0)

theorem tco_halfMoment_nonneg (m : ℕ) : 0 ≤ tco_halfMoment m :=
  integral_nonneg fun x => by
    rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m

theorem tco_lintegral_coord_pow (m : ℕ) [Fintype ι] (p : ι × Fin 2) :
    ∫⁻ r, ENNReal.ofReal (r p ^ (2 * m))
        ∂(Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) =
      ENNReal.ofReal (tco_halfMoment m) := by
  have hmp := measurePreserving_eval (fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) p
  have hc := hmp.lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * m))) (by fun_prop)
  simp only [Function.eval] at hc
  rw [hc, tco_halfMoment, ofReal_integral_eq_lintegral_ofReal (tco_integrable_pow_gaussianReal _ _)
      (ae_of_all _ fun x => by
        simp only [Pi.zero_apply]; rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)]

theorem tco_add_pow_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    (a + b) ^ m ≤ 2 ^ m * (a ^ m + b ^ m) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have h2 : (max a b) ^ m ≤ a ^ m + b ^ m := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ha m]
    · rw [max_eq_left h]; linarith [pow_nonneg hb m]
  calc (a + b) ^ m ≤ (2 * max a b) ^ m := pow_le_pow_left₀ (by positivity) h1 m
    _ = 2 ^ m * (max a b) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (a ^ m + b ^ m) := by gcongr

/-- `E|h_a|^{2m} ≤ 2^{m+1} M_m`, uniformly in the coordinate and in the dimension. -/
theorem tco_lintegral_coord_normSq_pow_le (m : ℕ) [Fintype ι] (a : ι) :
    ∫⁻ h, ENNReal.ofReal (Complex.normSq (h a) ^ m) ∂circularVectorLaw ι ≤
      ENNReal.ofReal (2 ^ m * (2 * tco_halfMoment m)) := by
  unfold circularVectorLaw
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ r : ι × Fin 2 → ℝ,
      ENNReal.ofReal (Complex.normSq ((r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) ^ m) ≤
        ENNReal.ofReal (2 ^ m) *
          (ENNReal.ofReal (r (a, 0) ^ (2 * m)) + ENNReal.ofReal (r (a, 1) ^ (2 * m))) := by
    intro r
    have hn : Complex.normSq ((r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) =
        r (a, 0) ^ 2 + r (a, 1) ^ 2 := by
      simp [Complex.normSq_apply, pow_two]
    rw [hn, pow_mul, pow_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (tco_add_pow_le _ _ (sq_nonneg _) (sq_nonneg _) m)
  calc ∫⁻ r, ENNReal.ofReal
        (Complex.normSq ((r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I) ^ m)
        ∂(Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0))
      ≤ ∫⁻ r, ENNReal.ofReal (2 ^ m) *
          (ENNReal.ofReal (r (a, 0) ^ (2 * m)) + ENNReal.ofReal (r (a, 1) ^ (2 * m)))
        ∂(Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ m) * (ENNReal.ofReal (tco_halfMoment m) +
          ENNReal.ofReal (tco_halfMoment m)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (by fun_prop), tco_lintegral_coord_pow, tco_lintegral_coord_pow]
    _ = ENNReal.ofReal (2 ^ m * (2 * tco_halfMoment m)) := by
        rw [← ENNReal.ofReal_add (tco_halfMoment_nonneg m) (tco_halfMoment_nonneg m),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-!
## The spectral decomposition of the quadratic form
-/

theorem tco_quadForm_eq_sum [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℂ}
    (hQ : Q.IsHermitian) (h : ι → ℂ) :
    quadForm Q h = ∑ i, hQ.eigenvalues i *
      Complex.normSq ((star (hQ.eigenvectorUnitary).1 *ᵥ h) i) := by
  set U : Matrix ι ι ℂ := (hQ.eigenvectorUnitary).1
  have hspec : Q = U * diagonal (RCLike.ofReal ∘ hQ.eigenvalues) * star U := by
    conv_lhs => rw [hQ.spectral_theorem]
    rfl
  set g := star U *ᵥ h
  generalize hDdef : diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hQ.eigenvalues) = D at hspec
  have hdot : star h ⬝ᵥ (Q *ᵥ h) = star g ⬝ᵥ (D *ᵥ g) := by
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    congr 1
    simp only [g, star_mulVec]
    congr 1
    simp [Matrix.star_eq_conjTranspose]
  unfold quadForm
  rw [hdot, ← hDdef]
  simp only [dotProduct, mulVec_diagonal, Function.comp_apply, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : star (g i) * ((hQ.eigenvalues i : ℂ) * g i) =
      ((hQ.eigenvalues i * Complex.normSq (g i) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, RCLike.star_def]
    ring
  rw [show (RCLike.ofReal (hQ.eigenvalues i) : ℂ) = (hQ.eigenvalues i : ℂ) from rfl, e,
    Complex.ofReal_re]

/-- **Dimension-free moments of a positive quadratic form.** For every `m` there is
`c_m ≥ 0` such that, for every finite `ι` and every `Q ⪰ 0`,
`E_h (h*Qh)^m ≤ c_m (Re Tr Q)^m`, `h ~ circularVectorLaw ι`. -/
theorem tco_lintegral_quadForm_pow_le (m : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ),
      Q.PosSemidef → ∫⁻ h, ENNReal.ofReal (quadForm Q h ^ m) ∂circularVectorLaw ι ≤
        ENNReal.ofReal (c * Q.trace.re ^ m) := by
  set κ : ℝ := 2 ^ m * (2 * tco_halfMoment m)
  have hκ : 0 ≤ κ := by have := tco_halfMoment_nonneg m; positivity
  refine ⟨κ + 1, by linarith, ?_⟩
  intro ι _ _ Q hQ
  have hprob := tco_isProbabilityMeasure_circularVectorLaw (ι := ι)
  set lam := hQ.1.eigenvalues
  have hlam : ∀ i, 0 ≤ lam i := hQ.eigenvalues_nonneg
  set S : ℝ := ∑ i, lam i
  have hS : Q.trace.re = S := by
    rw [hQ.1.trace_eq_sum_eigenvalues]; simp [S, lam]
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hlam i
  rw [hS]
  set U : Matrix ι ι ℂ := (hQ.1.eigenvectorUnitary).1
  have hU : star U ∈ Matrix.unitaryGroup ι ℂ := (hQ.1.eigenvectorUnitary)⁻¹.2
  -- Rewrite through the unitary invariance.
  set G : (ι → ℂ) → ℝ≥0∞ := fun g =>
    ENNReal.ofReal ((∑ i, lam i * Complex.normSq (g i)) ^ m)
  have hG : Measurable G := by
    unfold G
    refine ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun i _ => ?_).pow_const m)
    exact measurable_const.mul
      (Complex.continuous_normSq.measurable.comp (measurable_pi_apply i))
  have hstep : ∫⁻ h, ENNReal.ofReal (quadForm Q h ^ m) ∂circularVectorLaw ι =
      ∫⁻ g, G g ∂circularVectorLaw ι := by
    have hmeas : Measurable (fun h : ι → ℂ => star U *ᵥ h) :=
      (Continuous.matrix_mulVec continuous_const continuous_id).measurable
    calc ∫⁻ h, ENNReal.ofReal (quadForm Q h ^ m) ∂circularVectorLaw ι
        = ∫⁻ h, G (star U *ᵥ h) ∂circularVectorLaw ι := by
          refine lintegral_congr fun h => ?_
          simp only [G]; rw [tco_quadForm_eq_sum hQ.1 h]
      _ = ∫⁻ g, G g ∂((circularVectorLaw ι).map (fun h => star U *ᵥ h)) :=
          (lintegral_map hG hmeas).symm
      _ = ∫⁻ g, G g ∂circularVectorLaw ι := by
          rw [tco_circularVectorLaw_map_unitary (star U) hU]
  rw [hstep]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [G, pow_zero, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]
    exact ENNReal.one_le_ofReal.2 (by linarith)
  -- Jensen with weights `λ_i / S`.
  have hjensen : ∀ g : ι → ℂ, (∑ i, lam i * Complex.normSq (g i)) ^ m ≤
      S ^ (m - 1) * ∑ i, lam i * Complex.normSq (g i) ^ m := by
    intro g
    rcases eq_or_lt_of_le hS0 with hS0' | hSpos
    · have hz : ∀ i, lam i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hlam i)).1 hS0'.symm i
          (Finset.mem_univ i)
        exact this
      simp only [hz, zero_mul, Finset.sum_const_zero, zero_pow hm.ne', mul_zero, le_refl]
    · have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ lam i / S := fun i _ =>
        div_nonneg (hlam i) hSpos.le
      have hw1 : ∑ i ∈ (Finset.univ : Finset ι), lam i / S = 1 := by
        rw [← Finset.sum_div, div_self hSpos.ne']
      have hz : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ Complex.normSq (g i) :=
        fun i _ => Complex.normSq_nonneg _
      have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun i => lam i / S)
        (fun i => Complex.normSq (g i)) hw hw1 hz m
      have e1 : ∑ i, lam i / S * Complex.normSq (g i) =
          (∑ i, lam i * Complex.normSq (g i)) / S := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      have e2 : ∑ i, lam i / S * Complex.normSq (g i) ^ m =
          (∑ i, lam i * Complex.normSq (g i) ^ m) / S := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      rw [e1, e2, div_pow] at hj
      have hSm : S ^ m = S * S ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [div_le_div_iff₀ (pow_pos hSpos m) hSpos] at hj
      rw [hSm] at hj
      nlinarith [hj, hSpos]
  calc ∫⁻ g, G g ∂circularVectorLaw ι
      ≤ ∫⁻ g, ENNReal.ofReal (S ^ (m - 1)) *
          ∑ i, ENNReal.ofReal (lam i) * ENNReal.ofReal (Complex.normSq (g i) ^ m)
          ∂circularVectorLaw ι := by
        refine lintegral_mono fun g => ?_
        simp only [G]
        simp_rw [← ENNReal.ofReal_mul (hlam _)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hlam i)
            (pow_nonneg (Complex.normSq_nonneg _) _)),
          ← ENNReal.ofReal_mul (pow_nonneg hS0 _)]
        exact ENNReal.ofReal_le_ofReal (hjensen g)
    _ = ENNReal.ofReal (S ^ (m - 1)) * ∑ i, ENNReal.ofReal (lam i) *
          ∫⁻ g, ENNReal.ofReal (Complex.normSq (g i) ^ m) ∂circularVectorLaw ι := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum']
        · simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        · intro i _
          exact (measurable_const.mul (ENNReal.measurable_ofReal.comp
            ((Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)).pow_const
              m))).aemeasurable
    _ ≤ ENNReal.ofReal (S ^ (m - 1)) * ∑ i, ENNReal.ofReal (lam i) * ENNReal.ofReal κ := by
        gcongr with i
        exact tco_lintegral_coord_normSq_pow_le m i
    _ = ENNReal.ofReal (S ^ m * κ) := by
        simp_rw [← ENNReal.ofReal_mul (hlam _)]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hlam i) hκ),
          ← ENNReal.ofReal_mul (pow_nonneg hS0 _), ← Finset.sum_mul]
        congr 1
        rw [← mul_assoc, ← pow_succ]
        congr 2; omega
    _ ≤ ENNReal.ofReal ((κ + 1) * S ^ m) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [pow_nonneg hS0 m]

end BlockBand.Endpoints
