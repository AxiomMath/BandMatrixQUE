module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.ProjectiveHaar
public import Mathlib.Analysis.Matrix.Order

/-!
# Gaussian quadratic forms: moments, rank-one moments, Laplace bound

* `integral_normSq_pow_circularLawOne`: `E|g₁|^{2n} = n!`.
* `quadForm_eq_diagForm`, `integral_comp_quadForm`: for Hermitian `A` with eigenvalues `λ`,
  `g*Ag` has the law of `Σ_i λ_i |g_i|²` (unitary invariance of the circular law).
* `integral_quadForm_pow_le`, `integrable_quadForm_pow`: for `A ⪰ 0`,
  `E(g*Ag)^r ≤ r! (Re Tr A)^r` (the bound "`E(g*Ag)^r ≤ r!(Tr A)^r`").
* `integral_normSq_dotProduct_pow`: `E|w*g|^{2r} = r! ‖w‖^{2r}` (the exact conditional
  identity `E_a|a*v|^{2r} = r!(v*Yv)^r`, after `a = Lh`).
* `integral_quadForm_pow_swap`: for all square `L, M`,
  `E_h(quadForm (MM*) (Lh))^r = E_g(quadForm (LL*) (Mg))^r` (double averaging), which identifies
  `E_{a~CN(0,Y)}(a*Γa)^r` with `E_g(g*Γ^{1/2}YΓ^{1/2}g)^r` without matrix square roots.
* `integral_exp_neg_quadForm_le`: for `A ⪰ 0`, `s ≥ 0`, `E e^{-s g*Ag} ≤ (1 + s Re Tr A)⁻¹`
  ( /: `∏(1+sa_i)⁻¹ ≤ (1+s)⁻¹` when `Σ a_i = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.ProjectiveHaar
open scoped ENNReal NNReal ComplexOrder Matrix ComplexConjugate

/-!
## One circular coordinate
-/

/-- `∫⁻ |z|^{2n} e^{-c|z|²} dCN(0,1) = n!/(1+c)^{n+1}` for `c > -1`. -/
theorem lintegral_normSq_pow_mul_exp_circularLawOne (n : ℕ) {c : ℝ} (hc : -1 < c) :
    ∫⁻ z, ENNReal.ofReal (Complex.normSq z ^ n * Real.exp (-c * Complex.normSq z))
        ∂circularLawOne =
      ENNReal.ofReal (n.factorial / (1 + c) ^ (n + 1)) := by
  have ha : 0 < 1 + c := by linarith
  rw [circularLawOne_eq, lintegral_withDensity_eq_lintegral_mul _ measurable_circularDensityOne
    (by fun_prop)]
  have hpt : ∀ z : ℂ, (circularDensityOne * fun z =>
      ENNReal.ofReal (Complex.normSq z ^ n * Real.exp (-c * Complex.normSq z))) z =
      ENNReal.ofReal Real.pi⁻¹ *
        ENNReal.ofReal (Complex.normSq z ^ n * Real.exp (-(1 + c) * Complex.normSq z)) := by
    intro z
    simp only [Pi.mul_apply, circularDensityOne]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : Real.exp (-(1 + c) * Complex.normSq z) =
        Real.exp (-Complex.normSq z) * Real.exp (-c * Complex.normSq z) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  simp_rw [hpt]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_normSq_pow_mul_exp n ha,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem lintegral_normSq_pow_circularLawOne (n : ℕ) :
    ∫⁻ z, ENNReal.ofReal (Complex.normSq z ^ n) ∂circularLawOne = ENNReal.ofReal n.factorial := by
  have h := lintegral_normSq_pow_mul_exp_circularLawOne n (c := 0) (by norm_num)
  simpa using h

theorem integrable_normSq_pow_circularLawOne (n : ℕ) :
    Integrable (fun z : ℂ => Complex.normSq z ^ n) circularLawOne := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    pow_nonneg (Complex.normSq_nonneg z) n), lintegral_normSq_pow_circularLawOne]
  exact ENNReal.ofReal_lt_top

/-- `E|g₁|^{2n} = n!`. -/
theorem integral_normSq_pow_circularLawOne (n : ℕ) :
    ∫ z, Complex.normSq z ^ n ∂circularLawOne = n.factorial := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z =>
    pow_nonneg (Complex.normSq_nonneg z) n) (by fun_prop), lintegral_normSq_pow_circularLawOne,
    ENNReal.toReal_ofReal (by positivity)]

/-- `E e^{-c|g₁|²} = (1+c)⁻¹` for `c > -1`. -/
theorem integral_exp_neg_normSq_circularLawOne {c : ℝ} (hc : -1 < c) :
    ∫ z, Real.exp (-c * Complex.normSq z) ∂circularLawOne = (1 + c)⁻¹ := by
  have ha : 0 < 1 + c := by linarith
  have h := lintegral_normSq_pow_mul_exp_circularLawOne 0 hc
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at h
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => by positivity)
    (by fun_prop), h, ENNReal.toReal_ofReal (by positivity), one_div]

/-!
## Spectral reduction of a quadratic form
-/

variable {N : ℕ}

/-- `Σ_i λ_i |g_i|²`. -/
def diagForm (lam : Fin N → ℝ) (g : Fin N → ℂ) : ℝ := ∑ i, lam i * Complex.normSq (g i)

theorem measurable_diagForm (lam : Fin N → ℝ) : Measurable (diagForm lam) := by
  unfold diagForm
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.mul (Complex.continuous_normSq.measurable.comp (measurable_pi_apply i))

theorem diagForm_nonneg {lam : Fin N → ℝ} (h : ∀ i, 0 ≤ lam i) (g : Fin N → ℂ) :
    0 ≤ diagForm lam g :=
  Finset.sum_nonneg fun i _ => mul_nonneg (h i) (Complex.normSq_nonneg _)

theorem quadForm_diagonal (lam : Fin N → ℝ) (w : Fin N → ℂ) :
    quadForm (diagonal fun i => (lam i : ℂ)) w = diagForm lam w := by
  unfold quadForm diagForm
  simp only [mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `quadForm (X* A X) g = quadForm A (X g)`. -/
theorem quadForm_conjTranspose_mul_mul (A X : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) :
    quadForm (Xᴴ * A * X) g = quadForm A (X *ᵥ g) := by
  unfold quadForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

/-- The unitary of the spectral theorem. -/
abbrev gr_specU {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) : Matrix (Fin N) (Fin N) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)

theorem spectral_eq {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    A = gr_specU hA * diagonal (fun i => (hA.eigenvalues i : ℂ)) * (gr_specU hA)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem specU_star_mul {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    (gr_specU hA)ᴴ * gr_specU hA = 1 := Unitary.coe_star_mul_self _

theorem specU_mul_star {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    gr_specU hA * (gr_specU hA)ᴴ = 1 := Unitary.coe_mul_star_self _

theorem specU_star_mem {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    (gr_specU hA)ᴴ ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_conjTranspose]
  exact specU_star_mul hA

/-- `g*Ag = Σ λ_i |(U*g)_i|²`. -/
theorem quadForm_eq_diagForm {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (g : Fin N → ℂ) : quadForm A g = diagForm hA.eigenvalues ((gr_specU hA)ᴴ *ᵥ g) := by
  have h := quadForm_conjTranspose_mul_mul (diagonal fun i => (hA.eigenvalues i : ℂ))
    (gr_specU hA)ᴴ g
  rw [conjTranspose_conjTranspose, ← spectral_eq hA, quadForm_diagonal] at h
  exact h

/-- Law of `g*Ag`: for every measurable `f`, `E f(g*Ag) = E f(Σ λ_i|g_i|²)`. -/
theorem integral_comp_quadForm {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ g, f (quadForm A g) ∂circularVectorLaw (Fin N) =
      ∫ g, f (diagForm hA.eigenvalues g) ∂circularVectorLaw (Fin N) := by
  have hmap := circularVectorLaw_map_unitary (specU_star_mem hA)
  have hm : Measurable fun g : Fin N → ℂ => (gr_specU hA)ᴴ *ᵥ g :=
    (Matrix.toLin' (gr_specU hA)ᴴ).continuous_of_finiteDimensional.measurable
  conv_rhs => rw [← hmap]
  rw [integral_map (f := fun g => f (diagForm hA.eigenvalues g)) hm.aemeasurable
    (hf.comp (measurable_diagForm _)).aestronglyMeasurable]
  simp_rw [quadForm_eq_diagForm hA]

theorem lintegral_comp_quadForm {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f (quadForm A g) ∂circularVectorLaw (Fin N) =
      ∫⁻ g, f (diagForm hA.eigenvalues g) ∂circularVectorLaw (Fin N) := by
  have hmap := circularVectorLaw_map_unitary (specU_star_mem hA)
  have hm : Measurable fun g : Fin N → ℂ => (gr_specU hA)ᴴ *ᵥ g :=
    (Matrix.toLin' (gr_specU hA)ᴴ).continuous_of_finiteDimensional.measurable
  conv_rhs => rw [← hmap]
  rw [lintegral_map (f := fun g => f (diagForm hA.eigenvalues g))
    (hf.comp (measurable_diagForm _)) hm]
  simp_rw [quadForm_eq_diagForm hA]

theorem measurable_quadForm (A : Matrix (Fin N) (Fin N) ℂ) :
    Measurable (quadForm A) := by
  unfold quadForm
  exact Complex.continuous_re.measurable.comp (by fun_prop)

theorem continuous_quadForm' (A : Matrix (Fin N) (Fin N) ℂ) : Continuous (quadForm A) := by
  unfold quadForm
  exact Complex.continuous_re.comp (by fun_prop)

/-!
## Moments of `Σ λ_i |g_i|²`
-/

theorem integrable_normSq_coord_pow (i : Fin N) (n : ℕ) :
    Integrable (fun g : Fin N → ℂ => Complex.normSq (g i) ^ n) (circularVectorLaw (Fin N)) := by
  rw [circularVectorLaw_eq_pi]
  exact integrable_comp_eval (μ := fun _ : Fin N => circularLawOne)
    (f := fun z : ℂ => Complex.normSq z ^ n) (integrable_normSq_pow_circularLawOne n)

theorem integral_normSq_coord_pow (i : Fin N) (n : ℕ) :
    ∫ g, Complex.normSq (g i) ^ n ∂circularVectorLaw (Fin N) = n.factorial := by
  rw [circularVectorLaw_eq_pi]
  rw [integral_comp_eval (μ := fun _ : Fin N => circularLawOne)
    (f := fun z : ℂ => Complex.normSq z ^ n) (by fun_prop)]
  exact integral_normSq_pow_circularLawOne n

/-- Jensen: for `λ ≥ 0`, `S = Σλ`, `x ≥ 0`, `(Σ λ_i x_i)^r ≤ S^{r-1} Σ λ_i x_i^r` (`r ≥ 1`),
written as `S * (Σλx)^r ≤ S^r Σ λ x^r` to avoid `r - 1`. -/
theorem mul_sum_pow_le {lam x : Fin N → ℝ} (hl : ∀ i, 0 ≤ lam i) (hx : ∀ i, 0 ≤ x i) (r : ℕ) :
    (∑ i, lam i) * (∑ i, lam i * x i) ^ r ≤ (∑ i, lam i) ^ r * ∑ i, lam i * x i ^ r := by
  set S := ∑ i, lam i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hl i
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp only [pow_zero, one_mul]
      exact le_of_eq (by
        have : ∀ i, lam i = 0 := fun i =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hl j)).mp h0.symm i (Finset.mem_univ _)
        simp [this])
    · rw [zero_pow hr.ne', zero_mul]
  · have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 ≤ lam i / S := fun i _ => by
      have := hl i; positivity
    have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin N)), lam i / S = 1 := by
      rw [← Finset.sum_div, div_self hpos.ne']
    have hJ := (convexOn_pow r).map_sum_le hw0 hw1 (p := x) fun i _ => Set.mem_Ici.mpr (hx i)
    simp only [smul_eq_mul] at hJ
    have e1 : ∑ i, lam i / S * x i = (∑ i, lam i * x i) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, lam i / S * x i ^ r = (∑ i, lam i * x i ^ r) / S := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, div_pow] at hJ
    have hSr : 0 < S ^ r := pow_pos hpos r
    rw [div_le_div_iff₀ hSr hpos] at hJ
    linarith

theorem diagForm_pow_le {lam : Fin N → ℝ} (hl : ∀ i, 0 ≤ lam i) (r : ℕ) (g : Fin N → ℂ) :
    (∑ i, lam i) * diagForm lam g ^ r ≤
      (∑ i, lam i) ^ r * ∑ i, lam i * Complex.normSq (g i) ^ r :=
  mul_sum_pow_le hl (fun i => Complex.normSq_nonneg (g i)) r

theorem integrable_sum_lam_normSq_pow (lam : Fin N → ℝ) (r : ℕ) :
    Integrable (fun g : Fin N → ℂ => ∑ i, lam i * Complex.normSq (g i) ^ r)
      (circularVectorLaw (Fin N)) :=
  integrable_finsetSum _ fun i _ => (integrable_normSq_coord_pow i r).const_mul _

theorem integral_sum_lam_normSq_pow (lam : Fin N → ℝ) (r : ℕ) :
    ∫ g, ∑ i, lam i * Complex.normSq (g i) ^ r ∂circularVectorLaw (Fin N) =
      (∑ i, lam i) * r.factorial := by
  rw [integral_finsetSum _ fun i _ => (integrable_normSq_coord_pow i r).const_mul _,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_normSq_coord_pow]

theorem integrable_diagForm_pow {lam : Fin N → ℝ} (hl : ∀ i, 0 ≤ lam i) (r : ℕ) :
    Integrable (fun g => diagForm lam g ^ r) (circularVectorLaw (Fin N)) := by
  set S := ∑ i, lam i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hl i
  rcases hS0.eq_or_lt with h0 | hpos
  · have hz : ∀ i, lam i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hl j)).mp h0.symm i (Finset.mem_univ _)
    have : (fun g => diagForm lam g ^ r) = fun _ => (0 : ℝ) ^ r := by
      funext g; simp [diagForm, hz]
    rw [this]; exact integrable_const _
  · refine Integrable.mono' ((integrable_sum_lam_normSq_pow lam r).const_mul (S ^ r / S))
      ((measurable_diagForm lam).pow_const r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (diagForm_nonneg hl g) r)]
    have h := diagForm_pow_le hl r g
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    linarith

/-- `E(Σλ_i|g_i|²)^r ≤ r! (Σλ)^r` for `λ ≥ 0`. -/
theorem integral_diagForm_pow_le {lam : Fin N → ℝ} (hl : ∀ i, 0 ≤ lam i) (r : ℕ) :
    ∫ g, diagForm lam g ^ r ∂circularVectorLaw (Fin N) ≤ r.factorial * (∑ i, lam i) ^ r := by
  set S := ∑ i, lam i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hl i
  rcases hS0.eq_or_lt with h0 | hpos
  · have hz : ∀ i, lam i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hl j)).mp h0.symm i (Finset.mem_univ _)
    have : (fun g => diagForm lam g ^ r) = fun _ => (0 : ℝ) ^ r := by
      funext g; simp [diagForm, hz]
    rw [this, integral_const, ← h0]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · simp [zero_pow hr.ne']
  · have hmono : ∫ g, S * diagForm lam g ^ r ∂circularVectorLaw (Fin N) ≤
        ∫ g, S ^ r * ∑ i, lam i * Complex.normSq (g i) ^ r ∂circularVectorLaw (Fin N) :=
      integral_mono ((integrable_diagForm_pow hl r).const_mul S)
        ((integrable_sum_lam_normSq_pow lam r).const_mul _) fun g => diagForm_pow_le hl r g
    rw [integral_const_mul, integral_const_mul, integral_sum_lam_normSq_pow] at hmono
    have : S * ∫ g, diagForm lam g ^ r ∂circularVectorLaw (Fin N) ≤
        S * (r.factorial * S ^ r) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- `Re Tr A = Σ λ_i` for Hermitian `A`. -/
theorem re_trace_eq_sum_eigenvalues {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

theorem integrable_quadForm_pow {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef) (r : ℕ) :
    Integrable (fun g => quadForm A g ^ r) (circularVectorLaw (Fin N)) := by
  have hm : Measurable fun g => quadForm A g ^ r := (measurable_quadForm A).pow_const r
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have h1 := (integrable_diagForm_pow (fun i => hA.eigenvalues_nonneg i) r).2
  unfold HasFiniteIntegral at h1 ⊢
  have heq := lintegral_comp_quadForm hA.1 (f := fun x => ‖x ^ r‖ₑ) (by fun_prop)
  rw [heq]; exact h1

/-- **`E(g*Ag)^r ≤ r!(Re Tr A)^r`** for `A ⪰ 0`. -/
theorem integral_quadForm_pow_le {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef) (r : ℕ) :
    ∫ g, quadForm A g ^ r ∂circularVectorLaw (Fin N) ≤ r.factorial * A.trace.re ^ r := by
  rw [integral_comp_quadForm hA.1 (f := fun x => x ^ r) (by fun_prop),
    re_trace_eq_sum_eigenvalues hA.1]
  exact integral_diagForm_pow_le (fun i => hA.eigenvalues_nonneg i) r

theorem quadForm_nonneg_of_posSemidef {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (g : Fin N → ℂ) : 0 ≤ quadForm A g := by
  rw [quadForm_eq_diagForm hA.1]
  exact diagForm_nonneg (fun i => hA.eigenvalues_nonneg i) _

/-!
## Rank one: `E|w*g|^{2r} = r!‖w‖^{2r}`
-/

/-- `Σ‖w_i‖²`. -/
def sqNorm (w : Fin N → ℂ) : ℝ := ∑ i, Complex.normSq (w i)

theorem sqNorm_nonneg (w : Fin N → ℂ) : 0 ≤ sqNorm w :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (w i)

theorem quadForm_one (x : Fin N → ℂ) : quadForm 1 x = sqNorm x := by
  unfold quadForm sqNorm
  rw [one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.ofReal_re]

theorem quadForm_conjTranspose_mul_self (X : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) :
    quadForm (Xᴴ * X) g = sqNorm (X *ᵥ g) := by
  have h := quadForm_conjTranspose_mul_mul 1 X g
  rw [Matrix.mul_one] at h
  rw [h, quadForm_one]

/-- The rank-one matrix `ww*`. -/
abbrev rankOne (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := vecMulVec w (star w)

theorem rankOne_eq (w : Fin N → ℂ) :
    rankOne w = (replicateRow (Fin 1) (star w))ᴴ * replicateRow (Fin 1) (star w) := by
  ext i j
  simp [vecMulVec_apply, Matrix.mul_apply, replicateRow_apply]

theorem rankOne_posSemidef (w : Fin N → ℂ) : (rankOne w).PosSemidef := by
  rw [rankOne_eq]; exact posSemidef_conjTranspose_mul_self _

theorem re_conj_mul_self (z : ℂ) : (conj z * z).re = Complex.normSq z := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

theorem star_dotProduct_swap (x y : Fin N → ℂ) : star y ⬝ᵥ x = conj (star x ⬝ᵥ y) := by
  simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem rankOne_mulVec (w g : Fin N → ℂ) : rankOne w *ᵥ g = (star w ⬝ᵥ g) • w := by
  ext i
  simp only [mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Pi.star_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem quadForm_rankOne (w g : Fin N → ℂ) :
    quadForm (rankOne w) g = Complex.normSq (star w ⬝ᵥ g) := by
  unfold quadForm
  rw [rankOne_mulVec, dotProduct_smul, smul_eq_mul, star_dotProduct_swap w g, Complex.mul_conj,
    Complex.ofReal_re]

theorem star_dotProduct_self (w : Fin N → ℂ) : star w ⬝ᵥ w = ((sqNorm w : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, sqNorm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj]

theorem trace_rankOne (w : Fin N → ℂ) : (rankOne w).trace.re = sqNorm w := by
  have : (rankOne w).trace = star w ⬝ᵥ w := by
    simp only [Matrix.trace, diag, vecMulVec_apply, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this, star_dotProduct_self, Complex.ofReal_re]

theorem rankOne_mul_self (w : Fin N → ℂ) :
    rankOne w * rankOne w = ((sqNorm w : ℝ) : ℂ) • rankOne w := by
  rw [vecMulVec_mul_vecMulVec]
  ext i j
  simp only [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
  rw [star_dotProduct_self]; ring

theorem sum_sq_eigenvalues {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    (A * A).trace.re = ∑ i, hA.eigenvalues i ^ 2 := by
  have hs := spectral_eq hA
  have hU := specU_star_mul hA
  have hAA : A * A = gr_specU hA * diagonal (fun i => ((hA.eigenvalues i ^ 2 : ℝ) : ℂ)) *
      (gr_specU hA)ᴴ := by
    conv_lhs => rw [hs]
    calc gr_specU hA * diagonal (fun i => (hA.eigenvalues i : ℂ)) * (gr_specU hA)ᴴ *
          (gr_specU hA * diagonal (fun i => (hA.eigenvalues i : ℂ)) * (gr_specU hA)ᴴ) =
        gr_specU hA * diagonal (fun i => (hA.eigenvalues i : ℂ)) * ((gr_specU hA)ᴴ * gr_specU hA) *
          diagonal (fun i => (hA.eigenvalues i : ℂ)) * (gr_specU hA)ᴴ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU, Matrix.mul_one, Matrix.mul_assoc (gr_specU hA), diagonal_mul_diagonal]
          congr 3
          funext i; push_cast; ring
  rw [hAA, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]

/-- Nonnegative reals with `(Σλ)² = Σλ²`: at most one is nonzero. -/
theorem eq_zero_of_sq_sum {lam : Fin N → ℝ} (hl : ∀ i, 0 ≤ lam i)
    (h : (∑ i, lam i) ^ 2 = ∑ i, lam i ^ 2) {i j : Fin N} (hij : i ≠ j) (hi : 0 < lam i) :
    lam j = 0 := by
  classical
  have hsq : (∑ i, lam i) ^ 2 = ∑ a, ∑ b, lam a * lam b := by
    rw [sq, Finset.sum_mul_sum]
  have hdiag : ∑ a, ∑ b, lam a * lam b = ∑ a, lam a ^ 2 + ∑ a, ∑ b ∈ Finset.univ.erase a,
      lam a * lam b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), sq]
  have hoff : ∑ a, ∑ b ∈ Finset.univ.erase a, lam a * lam b = 0 := by linarith
  have hoff' := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hl a) (hl b))).mp hoff i (Finset.mem_univ _)
  have hij' := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => mul_nonneg (hl i) (hl b))).mp hoff'
    j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)
  rcases mul_eq_zero.mp hij' with h1 | h1
  · linarith
  · exact h1

/-- **`E|w*g|^{2r} = r! ‖w‖^{2r}`** (the exact conditional identity). -/
theorem integral_normSq_dotProduct_pow (w : Fin N → ℂ) (r : ℕ) :
    ∫ g, Complex.normSq (star w ⬝ᵥ g) ^ r ∂circularVectorLaw (Fin N) =
      r.factorial * sqNorm w ^ r := by
  classical
  have hA := rankOne_posSemidef w
  set lam := hA.1.eigenvalues with hlam
  have hl : ∀ i, 0 ≤ lam i := fun i => hA.eigenvalues_nonneg i
  have hsum : ∑ i, lam i = sqNorm w := by
    rw [← re_trace_eq_sum_eigenvalues hA.1, trace_rankOne]
  have hsq : ∑ i, lam i ^ 2 = sqNorm w ^ 2 := by
    rw [← sum_sq_eigenvalues hA.1, rankOne_mul_self, trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul, trace_rankOne, sq]
  have heq : (∑ i, lam i) ^ 2 = ∑ i, lam i ^ 2 := by rw [hsum, hsq]
  have hint : ∫ g, Complex.normSq (star w ⬝ᵥ g) ^ r ∂circularVectorLaw (Fin N) =
      ∫ g, diagForm lam g ^ r ∂circularVectorLaw (Fin N) := by
    simp_rw [← quadForm_rankOne]
    exact integral_comp_quadForm hA.1 (f := fun x => x ^ r) (by fun_prop)
  rw [hint]
  by_cases hall : ∀ i, lam i = 0
  · have h0 : sqNorm w = 0 := by rw [← hsum]; simp [hall]
    have : (fun g => diagForm lam g ^ r) = fun _ => (0 : ℝ) ^ r := by
      funext g; simp [diagForm, hall]
    rw [this, integral_const, h0]
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · simp [zero_pow hr.ne']
  · simp only [not_forall] at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hpos : 0 < lam i₀ := lt_of_le_of_ne (hl i₀) (Ne.symm hi₀)
    have hz : ∀ j, j ≠ i₀ → lam j = 0 := fun j hj => eq_zero_of_sq_sum hl heq (Ne.symm hj) hpos
    have hS : lam i₀ = sqNorm w := by
      rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have : ∑ x ∈ Finset.univ.erase i₀, lam x = 0 :=
        Finset.sum_eq_zero fun j hj => hz j (Finset.ne_of_mem_erase hj)
      rw [this, add_zero]
    have hd : ∀ g, diagForm lam g = lam i₀ * Complex.normSq (g i₀) := by
      intro g
      unfold diagForm
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have : ∑ x ∈ Finset.univ.erase i₀, lam x * Complex.normSq (g x) = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hz j (Finset.ne_of_mem_erase hj), zero_mul]
      rw [this, add_zero]
    simp_rw [hd, mul_pow]
    rw [integral_const_mul, integral_normSq_coord_pow, hS]
    ring

theorem integrable_normSq_dotProduct_pow (w : Fin N → ℂ) (r : ℕ) :
    Integrable (fun g => Complex.normSq (star w ⬝ᵥ g) ^ r) (circularVectorLaw (Fin N)) := by
  simp_rw [← quadForm_rankOne]
  exact integrable_quadForm_pow (rankOne_posSemidef w) r

/-!
## Double averaging
-/

/-- `|x*y|² ≤ ‖x‖²‖y‖²`. -/
theorem normSq_dotProduct_le (x y : Fin N → ℂ) :
    Complex.normSq (star x ⬝ᵥ y) ≤ sqNorm x * sqNorm y := by
  have h1 : ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    simp only [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  have h3 : (∑ i, ‖x i‖ * ‖y i‖) ^ 2 ≤ (∑ i, ‖x i‖ ^ 2) * ∑ i, ‖y i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hn : ∀ z : Fin N → ℂ, sqNorm z = ∑ i, ‖z i‖ ^ 2 := fun z => by
    unfold sqNorm; simp_rw [Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_eq_norm_sq, hn, hn]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h3

theorem star_mulVec_dotProduct_mulVec (L M : Matrix (Fin N) (Fin N) ℂ) (h g : Fin N → ℂ) :
    star (L *ᵥ h) ⬝ᵥ (M *ᵥ g) = star (Mᴴ *ᵥ (L *ᵥ h)) ⬝ᵥ g := by
  rw [dotProduct_mulVec, star_mulVec (Mᴴ), conjTranspose_conjTranspose]

theorem normSq_dotProduct_comm (x y : Fin N → ℂ) :
    Complex.normSq (star x ⬝ᵥ y) = Complex.normSq (star y ⬝ᵥ x) := by
  rw [star_dotProduct_swap x y, Complex.normSq_conj]

theorem measurable_mulVec (L : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun h : Fin N → ℂ => L *ᵥ h :=
  (Matrix.toLin' L).continuous_of_finiteDimensional.measurable

/-- **Double averaging**: `E_h (quadForm (MM*) (Lh))^r = E_g (quadForm (LL*) (Mg))^r` for all
square `L, M` (so `E_{a~CN(0,LL*)}(a*Γa)^r = E_g(g*M*(LL*)Mg)^r` when `MM* = Γ`). -/
theorem integral_quadForm_pow_swap (L M : Matrix (Fin N) (Fin N) ℂ) (r : ℕ) :
    ∫ h, quadForm (M * Mᴴ) (L *ᵥ h) ^ r ∂circularVectorLaw (Fin N) =
      ∫ g, quadForm (L * Lᴴ) (M *ᵥ g) ^ r ∂circularVectorLaw (Fin N) := by
  set μ := circularVectorLaw (Fin N)
  set J : (Fin N → ℂ) → (Fin N → ℂ) → ℝ := fun h g =>
    Complex.normSq (star (L *ᵥ h) ⬝ᵥ (M *ᵥ g)) ^ r with hJ
  have hg : ∀ h, ∫ g, J h g ∂μ = r.factorial * quadForm (M * Mᴴ) (L *ᵥ h) ^ r := by
    intro h
    simp only [hJ, star_mulVec_dotProduct_mulVec]
    rw [integral_normSq_dotProduct_pow]
    congr 2
    have := quadForm_conjTranspose_mul_self Mᴴ (L *ᵥ h)
    rw [conjTranspose_conjTranspose] at this
    exact this.symm
  have hh : ∀ g, ∫ h, J h g ∂μ = r.factorial * quadForm (L * Lᴴ) (M *ᵥ g) ^ r := by
    intro g
    simp only [hJ]
    simp_rw [normSq_dotProduct_comm (L *ᵥ _) (M *ᵥ g), star_mulVec_dotProduct_mulVec]
    rw [integral_normSq_dotProduct_pow]
    congr 2
    have := quadForm_conjTranspose_mul_self Lᴴ (M *ᵥ g)
    rw [conjTranspose_conjTranspose] at this
    exact this.symm
  have hint : Integrable (Function.uncurry J) (μ.prod μ) := by
    have hb : Integrable (fun z : (Fin N → ℂ) × (Fin N → ℂ) =>
        quadForm (Lᴴ * L) z.1 ^ r * quadForm (Mᴴ * M) z.2 ^ r) (μ.prod μ) :=
      (integrable_quadForm_pow (posSemidef_conjTranspose_mul_self L) r).mul_prod
        (integrable_quadForm_pow (posSemidef_conjTranspose_mul_self M) r)
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine (Measurable.pow_const ?_ r).aestronglyMeasurable
      exact Complex.continuous_normSq.measurable.comp (by fun_prop)
    · simp only [Function.uncurry, hJ, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg (Complex.normSq_nonneg _) _), quadForm_conjTranspose_mul_self,
        quadForm_conjTranspose_mul_self, ← mul_pow]
      exact pow_le_pow_left₀ (Complex.normSq_nonneg _) (normSq_dotProduct_le _ _) r
  have hswap := integral_integral_swap hint
  simp_rw [hg, hh, integral_const_mul] at hswap
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  exact mul_left_cancel₀ hf.ne' hswap

/-!
## Laplace transform
-/

theorem prod_one_add_ge {a : Fin N → ℝ} (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i, a i ≤ ∏ i, (1 + a i) := by
  classical
  have key : ∀ s : Finset (Fin N), 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.prod_insert hx]
      have h0 : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i _ => ha i
      nlinarith [ha x]
  exact key Finset.univ

/-- **Laplace bound** `E e^{-s g*Ag} = ∏(1+sλ_i)⁻¹ ≤ (1 + s Re Tr A)⁻¹` for `A ⪰ 0`, `s ≥ 0`. -/
theorem integral_exp_neg_quadForm_le {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫ g, Real.exp (-s * quadForm A g) ∂circularVectorLaw (Fin N) ≤ (1 + s * A.trace.re)⁻¹ := by
  have hl : ∀ i, 0 ≤ hA.1.eigenvalues i := fun i => hA.eigenvalues_nonneg i
  rw [integral_comp_quadForm hA.1 (f := fun x => Real.exp (-s * x)) (by fun_prop),
    re_trace_eq_sum_eigenvalues hA.1]
  have hprod : ∀ g, Real.exp (-s * diagForm hA.1.eigenvalues g) =
      ∏ i, Real.exp (-(s * hA.1.eigenvalues i) * Complex.normSq (g i)) := by
    intro g
    rw [← Real.exp_sum]; congr 1
    unfold diagForm; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hprod]
  rw [circularVectorLaw_eq_pi, integral_fintype_prod_eq_prod
    (f := fun i (z : ℂ) => Real.exp (-(s * hA.1.eigenvalues i) * Complex.normSq z))]
  have hfac : ∀ i, ∫ z, Real.exp (-(s * hA.1.eigenvalues i) * Complex.normSq z)
      ∂circularLawOne = (1 + s * hA.1.eigenvalues i)⁻¹ := fun i =>
    integral_exp_neg_normSq_circularLawOne (by have := mul_nonneg hs (hl i); linarith)
  simp_rw [hfac]
  rw [Finset.prod_inv_distrib, Finset.mul_sum]
  have hpos : 0 < 1 + ∑ i, s * hA.1.eigenvalues i :=
    by have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg hs (hl i); linarith
  exact inv_anti₀ hpos (prod_one_add_ge fun i => mul_nonneg hs (hl i))

end BlockBand.Endpoints.Normalization
