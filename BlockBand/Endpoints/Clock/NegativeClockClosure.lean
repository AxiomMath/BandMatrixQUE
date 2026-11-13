module

public import BlockBand.Endpoints.Clock.CommonPortRatiosLaplace
public import BlockBand.Endpoints.Clock.PhaseResolution
public import BlockBand.Endpoints.Clock.NegativeClockScattering
public import BlockBand.Layers.LayerMeasurability

/-!
# The negative-clock theorem: phase closure, convexity and the finite-width Laplace domination

We prove the finite-width Laplace domination of the negative clock by the closed clocks.

## Definitions

* `closedClock b E W n θ (ω, g) = W⁻² Re g*(A_θ* Y A_θ)g`, `Y = fullClock`, `g ~ CN(0, I_W)`:
  the Gaussian-probe one-input interior clock after closing the far port by `e^{iθ}`, divided
  by `W²` (the phase-resolution lemma, last sentence, and the Robin entrance lemma);
* `closedClockLaw W b E n θ`: its law under `growthPathLaw W b ⊗ CN(0, I_W)`.

## Results

* `negativeClock_phase_laplace` (deterministic, any finite `ι`, any `U`, any `S` with
  `S Sᴴ = I` and `det S₁₀ ≠ 0`, any `[θ₁, θ₂] ⊆ [0, 2π]`, `θ₁ < θ₂`, `σ ≥ 0`, `a = (θ₂-θ₁)/(2π)`):
  `E_h exp(-σ h*Yh) ≤ (θ₂-θ₁)⁻¹ ∫_{θ₁}^{θ₂} E_g exp(-σ a g*A_θ*YA_θ g) dθ`, `Y = UᴴU`. This is the
  inequality `F_Q(I) ≤ a⁻¹ ∫_I F_Q(aA_θA_θ*) dθ/(2π)` after the Gaussian representation
  `F_Q(C) = E_{h'} exp(-σ (Uᴴh')*C(Uᴴh'))` (Sylvester duality, no matrix square root):
  monotonicity uses `∫_I A_θA_θ* dθ/(2π) ⪯ I` (from the phase-resolution identity), convexity is
  Jensen for `exp` (tangent line), then Tonelli.
* `negativeClock_finite_laplace` (the finite path; `0 < b < 1/2`, `|E| < 2`, `W, n ≥ 1`, every
  phase interval as above, `s ≥ 0`): the path expectation of the previous inequality,
  `E e^{-sT_W} ≤ (θ₂-θ₁)⁻¹ ∫_{θ₁}^{θ₂} E e^{-s a W⁻² g*A_θ*YA_θ g} dθ` (lower integral in `θ`),
  where `T_W = W⁻²h*Yh`. The almost-sure hypotheses of the deterministic step (unitarity of
  `𝕊`, invertibility of `t`) are `negativeClock_ae_scattering` (for `n ≥ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Real
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix

namespace NegativeClockClosure

/-!
## 1. Continuity of `A_θ`
-/

section Det

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Stacking `[I ; Γ]`. -/
def stack (Γ : Matrix ι ι ℂ) : Matrix (Fin 2 × ι) ι ℂ :=
  Matrix.of fun p j => ![(1 : Matrix ι ι ℂ), Γ] p.1 p.2 j

theorem phaseA_eq_stack (r' t : Matrix ι ι ℂ) (θ : ℝ) :
    phaseA r' t θ = stack (phaseGamma r' t θ) := rfl

omit [Fintype ι] in
theorem continuous_stack : Continuous (stack (ι := ι)) := by
  refine continuous_pi fun p => continuous_pi fun j => ?_
  rcases p with ⟨i, k⟩
  fin_cases i
  · simp only [stack, Matrix.of_apply]
    exact continuous_const
  · simp only [stack, Matrix.of_apply]
    exact (continuous_apply j).comp (continuous_apply k)

/-- `θ ↦ A_θ` is continuous for a unitary `S` with invertible transmission. -/
theorem continuous_scatteringPhaseA (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hS : S * Sᴴ = 1)
    (ht : IsUnit (transmission S).det) : Continuous (scatteringPhaseA S) :=
  continuous_stack.comp (continuous_phaseGamma (transmission S) (farReflection S)
    (transmission_mul_add_farReflection_mul S hS) ht)

/-!
## 2. `∫_{θ₁}^{θ₂} v*A_θA_θ*v dθ ≤ 2π ‖v‖²`
-/

omit [DecidableEq ι] in
/-- `Re v*Mv` as a double sum. -/
theorem quadForm_eq_sum (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm M v = ∑ x, ∑ y, (star (v x) * M x y * v y).re := by
  unfold quadForm
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, mul_assoc]

/-- Integral of the quadratic form over a full period (the phase-resolution identity). -/
theorem integral_quadForm_phaseA (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hS : S * Sᴴ = 1)
    (ht : IsUnit (transmission S).det) (v : Fin 2 × ι → ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, quadForm (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) v =
      2 * π * quadForm 1 v := by
  have hA := continuous_scatteringPhaseA S hS ht
  have hAA : Continuous fun θ => scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ :=
    hA.matrix_mul hA.matrix_conjTranspose
  have hent : ∀ x y, ∫ θ in (0 : ℝ)..2 * π,
      (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y = ((2 * π : ℝ) : ℂ) * (1 : Matrix _ _ ℂ) x y := by
    intro x y
    have h := phase_resolution_average_general S hS ht x y
    have hπ : (2 * π : ℝ) ≠ 0 := by positivity
    rw [← h, ← mul_assoc, ← Complex.ofReal_mul, one_div, mul_inv_cancel₀ hπ, Complex.ofReal_one,
      one_mul]
  have hcont : ∀ x y, Continuous fun θ =>
      star (v x) * (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y * v y := by
    intro x y
    exact (continuous_const.mul ((continuous_apply y).comp ((continuous_apply x).comp hAA))).mul
      continuous_const
  simp_rw [quadForm_eq_sum]
  rw [intervalIntegral.integral_finsetSum (f := fun x θ => ∑ y, (star (v x) *
    (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y * v y).re) fun x _ => ?_]
  · have : ∀ x, ∫ θ in (0 : ℝ)..2 * π, ∑ y, (star (v x) *
        (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y * v y).re =
        ∑ y, (star (v x) * (((2 * π : ℝ) : ℂ) * (1 : Matrix _ _ ℂ) x y) * v y).re := by
      intro x
      rw [intervalIntegral.integral_finsetSum (f := fun y θ => (star (v x) *
        (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) x y * v y).re) fun y _ =>
        (Complex.continuous_re.comp (hcont x y)).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hre := Complex.reCLM.intervalIntegral_comp_comm
        ((hcont x y).intervalIntegrable (μ := volume) 0 (2 * π))
      simp only [Complex.reCLM_apply] at hre
      rw [hre, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hent]
    simp_rw [this]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show star (v x) * (((2 * π : ℝ) : ℂ) * (1 : Matrix _ _ ℂ) x y) * v y =
      ((2 * π : ℝ) : ℂ) * (star (v x) * (1 : Matrix _ _ ℂ) x y * v y) by ring,
      Complex.re_ofReal_mul]
  · exact (continuous_finsetSum _ fun y _ =>
      Complex.continuous_re.comp (hcont x y)).intervalIntegrable _ _

omit [DecidableEq ι] in
/-- `θ ↦ v*A_θA_θ*v` is nonnegative. -/
theorem quadForm_phaseA_nonneg (A : Matrix (Fin 2 × ι) ι ℂ) (v : Fin 2 × ι → ℂ) :
    0 ≤ quadForm (A * Aᴴ) v :=
  CommonPortRatios.quadForm_nonneg_of_posSemidef (posSemidef_self_mul_conjTranspose A) v

/-- Restriction to a sub-interval of `[0, 2π]`. -/
theorem integral_quadForm_phaseA_le (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hS : S * Sᴴ = 1)
    (ht : IsUnit (transmission S).det) (v : Fin 2 × ι → ℂ) {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁)
    (h12 : θ₁ ≤ θ₂) (h2 : θ₂ ≤ 2 * π) :
    ∫ θ in θ₁..θ₂, quadForm (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) v ≤
      2 * π * quadForm 1 v := by
  have hA := continuous_scatteringPhaseA S hS ht
  have hq : Continuous fun θ => quadForm (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) v :=
    continuous_quadForm.comp ((hA.matrix_mul hA.matrix_conjTranspose).prodMk continuous_const)
  rw [← integral_quadForm_phaseA S hS ht v]
  exact intervalIntegral.integral_mono_interval h0 h12 h2
    (Eventually.of_forall fun θ => quadForm_phaseA_nonneg _ v) (hq.intervalIntegrable _ _)

/-!
## 3. Jensen for `exp` on an interval
-/

/-- `(θ₂-θ₁) exp(-c m) ≤ ∫_{θ₁}^{θ₂} exp(-c q)`, `m` the average of `q` (tangent line at `m`). -/
theorem mul_exp_neg_average_le {q : ℝ → ℝ} (hq : Continuous q) {θ₁ θ₂ : ℝ} (h12 : θ₁ < θ₂)
    (c : ℝ) :
    (θ₂ - θ₁) * Real.exp (-(c * ((θ₂ - θ₁)⁻¹ * ∫ θ in θ₁..θ₂, q θ))) ≤
      ∫ θ in θ₁..θ₂, Real.exp (-(c * q θ)) := by
  set L := θ₂ - θ₁ with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  set Q := ∫ θ in θ₁..θ₂, q θ with hQ
  set m := L⁻¹ * Q with hm
  set e := Real.exp (-(c * m)) with he
  have hpt : ∀ θ, e * (1 + c * m) + (-(e * c)) * q θ ≤ Real.exp (-(c * q θ)) := by
    intro θ
    have h1 := Real.add_one_le_exp (-(c * (q θ - m)))
    have h2 : Real.exp (-(c * q θ)) = e * Real.exp (-(c * (q θ - m))) := by
      rw [he, ← Real.exp_add]; congr 1; ring
    rw [h2]
    have he0 : 0 < e := Real.exp_pos _
    nlinarith
  have hint1 : IntervalIntegrable (fun θ => e * (1 + c * m) + (-(e * c)) * q θ) volume θ₁ θ₂ :=
    (continuous_const.add (continuous_const.mul hq)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun θ => Real.exp (-(c * q θ))) volume θ₁ θ₂ :=
    (Real.continuous_exp.comp (continuous_const.mul hq).neg).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on h12.le hint1 hint2 fun θ _ => hpt θ
  have hcomp : ∫ θ in θ₁..θ₂, (e * (1 + c * m) + (-(e * c)) * q θ) = L * e := by
    rw [intervalIntegral.integral_add (f := fun _ => e * (1 + c * m))
      (g := fun θ => -(e * c) * q θ) intervalIntegrable_const
      ((continuous_const.mul hq).intervalIntegrable _ _), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul, ← hQ, ← hL]
    have : Q = L * m := by rw [hm, ← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul]
    rw [this]; ring
  rw [hcomp] at hmono
  rw [mul_comm]; linarith

/-- **Monotonicity and Jensen, pointwise**: for `v ∈ ℂ^{2W}`, `σ ≥ 0`,
`exp(-σ‖v‖²) ≤ (θ₂-θ₁)⁻¹ ∫_{θ₁}^{θ₂} exp(-σ a v*A_θA_θ*v) dθ`, `a = (θ₂-θ₁)/(2π)`. -/
theorem exp_neg_le_average (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hS : S * Sᴴ = 1)
    (ht : IsUnit (transmission S).det) {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ ≤ 2 * π) {σ : ℝ} (hσ : 0 ≤ σ) (v : Fin 2 × ι → ℂ) :
    Real.exp (-(σ * quadForm 1 v)) ≤
      (θ₂ - θ₁)⁻¹ * ∫ θ in θ₁..θ₂, Real.exp (-(σ * ((θ₂ - θ₁) / (2 * π)) *
        quadForm (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) v)) := by
  have hA := continuous_scatteringPhaseA S hS ht
  set q := fun θ => quadForm (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) v with hqdef
  have hq : Continuous q :=
    continuous_quadForm.comp ((hA.matrix_mul hA.matrix_conjTranspose).prodMk continuous_const)
  set L := θ₂ - θ₁ with hL
  have hL0 : 0 < L := by rw [hL]; linarith
  have hπ : 0 < 2 * π := by positivity
  set a := L / (2 * π) with ha
  have hJ := mul_exp_neg_average_le hq h12 (σ * a)
  have hbound := integral_quadForm_phaseA_le S hS ht v h0 h12.le h2
  set Q := ∫ θ in θ₁..θ₂, q θ with hQ
  have hle : σ * a * (L⁻¹ * Q) ≤ σ * quadForm 1 v := by
    have : a * (L⁻¹ * Q) = Q / (2 * π) := by
      rw [ha]; field_simp
    rw [mul_assoc, this]
    refine mul_le_mul_of_nonneg_left ?_ hσ
    rw [div_le_iff₀ hπ]; linarith
  have h1 : Real.exp (-(σ * quadForm 1 v)) ≤ Real.exp (-(σ * a * (L⁻¹ * Q))) :=
    Real.exp_le_exp.mpr (by linarith)
  refine h1.trans ?_
  rw [le_inv_mul_iff₀ hL0]
  exact hJ

end Det

/-!
## 4. Gaussian representation and Tonelli (one fixed path)
-/

section Probe

/-- A bounded continuous nonnegative-exponent function is integrable. -/
theorem integrable_exp_neg {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) : Integrable (fun x => Real.exp (-f x)) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.comp hf.neg).measurable.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by linarith [h0 x])

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `(√c B)ᴴ(√c B) = c BᴴB` inside the quadratic form. -/
theorem quadForm_sqrt_smul_conjTranspose_mul {c : ℝ} (hc : 0 ≤ c) (B : Matrix m n ℂ)
    (g : n → ℂ) :
    quadForm (((Real.sqrt c : ℂ) • B)ᴴ * ((Real.sqrt c : ℂ) • B)) g =
      c * quadForm (Bᴴ * B) g := by
  have e : ((Real.sqrt c : ℂ) • B)ᴴ * ((Real.sqrt c : ℂ) • B) = ((c : ℝ) : ℂ) • (Bᴴ * B) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [e, CommonPortRatios.quadForm_smul_real]

/-- `(√c B)(√c B)ᴴ = c BBᴴ` inside the quadratic form. -/
theorem quadForm_sqrt_smul_mul_conjTranspose {c : ℝ} (hc : 0 ≤ c) (B : Matrix m n ℂ)
    (h : m → ℂ) :
    quadForm (((Real.sqrt c : ℂ) • B) * ((Real.sqrt c : ℂ) • B)ᴴ) h =
      c * quadForm (B * Bᴴ) h := by
  have e : ((Real.sqrt c : ℂ) • B) * ((Real.sqrt c : ℂ) • B)ᴴ = ((c : ℝ) : ℂ) • (B * Bᴴ) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hc]
  rw [e, CommonPortRatios.quadForm_smul_real]

/-- Scaled Gaussian duality: `E_g exp(-c g*BᴴBg) = E_h exp(-c h*BBᴴh)`, `c ≥ 0`. -/
theorem integral_exp_neg_smul_dual [DecidableEq m] [DecidableEq n] {c : ℝ} (hc : 0 ≤ c) (B : Matrix m n ℂ) :
    ∫ g, Real.exp (-(c * quadForm (Bᴴ * B) g)) ∂circularVectorLaw n =
      ∫ h, Real.exp (-(c * quadForm (B * Bᴴ) h)) ∂circularVectorLaw m := by
  have := integral_exp_neg_quadForm_conjTranspose_mul_self_eq ((Real.sqrt c : ℂ) • B)
  simp_rw [quadForm_sqrt_smul_conjTranspose_mul hc, quadForm_sqrt_smul_mul_conjTranspose hc]
    at this
  exact this

end Probe

section Fubini

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]

/-- The integrand `exp(-c (Uᴴh')*A_θA_θ*(Uᴴh'))` in the variables `(h', θ)`. -/
def probeIntegrand (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (U : Matrix K (Fin 2 × ι) ℂ) (c : ℝ)
    (h' : K → ℂ) (θ : ℝ) : ℝ :=
  Real.exp (-(c * quadForm (scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ) (Uᴴ *ᵥ h')))

omit [DecidableEq K] in
theorem continuous_probeIntegrand (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hS : S * Sᴴ = 1)
    (ht : IsUnit (transmission S).det) (U : Matrix K (Fin 2 × ι) ℂ) (c : ℝ) :
    Continuous (Function.uncurry (probeIntegrand S U c)) := by
  have hA := continuous_scatteringPhaseA S hS ht
  have hAA : Continuous fun θ => scatteringPhaseA S θ * (scatteringPhaseA S θ)ᴴ :=
    hA.matrix_mul hA.matrix_conjTranspose
  have hUv : Continuous fun h' : K → ℂ => Uᴴ *ᵥ h' :=
    Continuous.matrix_mulVec continuous_const continuous_id
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_quadForm.comp
    ((hAA.comp continuous_snd).prodMk (hUv.comp continuous_fst)))).neg

omit [DecidableEq ι] [DecidableEq K] [Fintype ι] in
theorem continuous_conjTranspose_mulVec (U : Matrix K (Fin 2 × ι) ℂ) :
    Continuous fun h' : K → ℂ => Uᴴ *ᵥ h' :=
  Continuous.matrix_mulVec continuous_const continuous_id

/-- First Gaussian representation: `E_h e^{-σh*UᴴUh} = E_{h'} e^{-σ‖Uᴴh'‖²}`. -/
theorem integral_dual_left (U : Matrix K (Fin 2 × ι) ℂ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫ h, Real.exp (-(σ * quadForm (Uᴴ * U) h)) ∂circularVectorLaw (Fin 2 × ι) =
      ∫ h', Real.exp (-(σ * quadForm 1 (Uᴴ *ᵥ h'))) ∂circularVectorLaw K := by
  rw [integral_exp_neg_smul_dual hσ U]
  congr 1; funext h'
  rw [← CommonPortRatios.quadForm_conj, conjTranspose_conjTranspose, Matrix.mul_one]

/-- Second Gaussian representation (Sylvester): `E_g e^{-c g*AᴴUᴴUAg} = E_{h'} probeIntegrand`. -/
theorem integral_dual_right (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (U : Matrix K (Fin 2 × ι) ℂ)
    {c : ℝ} (hc : 0 ≤ c) (θ : ℝ) :
    ∫ g, Real.exp (-(c *
        quadForm ((scatteringPhaseA S θ)ᴴ * (Uᴴ * U) * scatteringPhaseA S θ) g))
        ∂circularVectorLaw ι =
      ∫ h', probeIntegrand S U c h' θ ∂circularVectorLaw K := by
  have e1 : (scatteringPhaseA S θ)ᴴ * (Uᴴ * U) * scatteringPhaseA S θ =
      (U * scatteringPhaseA S θ)ᴴ * (U * scatteringPhaseA S θ) := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, integral_exp_neg_smul_dual hc (U * scatteringPhaseA S θ)]
  congr 1; funext h'
  unfold probeIntegrand
  rw [← CommonPortRatios.quadForm_conj, conjTranspose_conjTranspose, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **One fixed path** (with the Gaussian representation): for `Y = UᴴU`,
`S Sᴴ = I`, `det S₁₀ ≠ 0`, `[θ₁,θ₂] ⊆ [0,2π]`, `θ₁ < θ₂`, `σ ≥ 0`, `a = (θ₂-θ₁)/(2π)`:
`E_h e^{-σh*Yh} ≤ (θ₂-θ₁)⁻¹ ∫_{(θ₁,θ₂]} E_g e^{-σa g*A_θ*YA_θ g} dθ` (`h ~ CN(0,I_{2|ι|})`,
`g ~ CN(0,I_{|ι|})`). -/
theorem negativeClock_phase_laplace (U : Matrix K (Fin 2 × ι) ℂ)
    (S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (hS : S * Sᴴ = 1) (ht : IsUnit (transmission S).det)
    {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ < θ₂) (h2 : θ₂ ≤ 2 * π) {σ : ℝ} (hσ : 0 ≤ σ) :
    ENNReal.ofReal (∫ h, Real.exp (-(σ * quadForm (Uᴴ * U) h)) ∂circularVectorLaw (Fin 2 × ι)) ≤
      ENNReal.ofReal (θ₂ - θ₁)⁻¹ * ∫⁻ θ in Set.Ioc θ₁ θ₂, ENNReal.ofReal
        (∫ g, Real.exp (-(σ * ((θ₂ - θ₁) / (2 * π)) *
          quadForm ((scatteringPhaseA S θ)ᴴ * (Uᴴ * U) * scatteringPhaseA S θ) g))
          ∂circularVectorLaw ι) := by
  have ha0 : 0 ≤ (θ₂ - θ₁) / (2 * π) := div_nonneg (by linarith) (by positivity)
  have hσa : 0 ≤ σ * ((θ₂ - θ₁) / (2 * π)) := mul_nonneg hσ ha0
  have hFc := continuous_probeIntegrand S hS ht U (σ * ((θ₂ - θ₁) / (2 * π)))
  have hFθ : ∀ h', Continuous (probeIntegrand S U (σ * ((θ₂ - θ₁) / (2 * π))) h') :=
    fun h' => hFc.uncurry_left h'
  have hFh : ∀ θ, Continuous fun h' => probeIntegrand S U (σ * ((θ₂ - θ₁) / (2 * π))) h' θ :=
    fun θ => hFc.uncurry_right θ
  have hF0 : ∀ h' θ, 0 ≤ probeIntegrand S U (σ * ((θ₂ - θ₁) / (2 * π))) h' θ :=
    fun _ _ => (Real.exp_pos _).le
  have hUv : Continuous fun h' : K → ℂ => Uᴴ *ᵥ h' := continuous_conjTranspose_mulVec U
  have hint0 : Integrable (fun h' : K → ℂ => Real.exp (-(σ * quadForm 1 (Uᴴ *ᵥ h'))))
      (circularVectorLaw K) := by
    have hc : Continuous fun h' : K → ℂ => Real.exp (-(σ * quadForm 1 (Uᴴ *ᵥ h'))) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_quadForm.comp
        (continuous_const.prodMk hUv))).neg
    refine (integrable_const (1 : ℝ)).mono' hc.measurable.aestronglyMeasurable
      (Eventually.of_forall fun h' => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ quadForm (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (Uᴴ *ᵥ h') := by
      rw [CommonPortRatios.quadForm_one]; positivity
    nlinarith
  have hintθ : ∀ θ, Integrable (fun h' => probeIntegrand S U (σ * ((θ₂ - θ₁) / (2 * π))) h' θ)
      (circularVectorLaw K) := fun θ =>
    (integrable_const (1 : ℝ)).mono' (hFh θ).measurable.aestronglyMeasurable
      (Eventually.of_forall fun h' => by
        unfold probeIntegrand
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by
          have := mul_nonneg hσa (quadForm_phaseA_nonneg (scatteringPhaseA S θ) (Uᴴ *ᵥ h'))
          linarith))
  have hL0 : 0 ≤ (θ₂ - θ₁)⁻¹ := inv_nonneg.mpr (by linarith)
  have hpt : ∀ h', ENNReal.ofReal (Real.exp (-(σ * quadForm 1 (Uᴴ *ᵥ h')))) ≤
      ENNReal.ofReal (θ₂ - θ₁)⁻¹ * ∫⁻ θ in Set.Ioc θ₁ θ₂,
        ENNReal.ofReal (probeIntegrand S U (σ * ((θ₂ - θ₁) / (2 * π))) h' θ) := by
    intro h'
    have hJ := exp_neg_le_average S hS ht h0 h12 h2 hσ (Uᴴ *ᵥ h')
    rw [← ofReal_integral_eq_lintegral_ofReal ((hFθ h').intervalIntegrable θ₁ θ₂).1
        (Eventually.of_forall fun θ => hF0 h' θ), ← intervalIntegral.integral_of_le h12.le,
      ← ENNReal.ofReal_mul hL0]
    exact ENNReal.ofReal_le_ofReal hJ
  rw [integral_dual_left U hσ, ofReal_integral_eq_lintegral_ofReal hint0
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  refine (lintegral_mono hpt).trans ?_
  have hmeas : AEMeasurable (Function.uncurry fun h' θ =>
      ENNReal.ofReal (probeIntegrand S U (σ * ((θ₂ - θ₁) / (2 * π))) h' θ))
      ((circularVectorLaw K).prod (volume.restrict (Set.Ioc θ₁ θ₂))) :=
    (ENNReal.measurable_ofReal.comp hFc.measurable).aemeasurable
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hmeas]
  refine le_of_eq ?_
  congr 1
  refine lintegral_congr fun θ => ?_
  rw [integral_dual_right S U hσa θ, ofReal_integral_eq_lintegral_ofReal (hintθ θ)
    (Eventually.of_forall fun h' => hF0 h' θ)]

end Fubini

end NegativeClockClosure

/-!
## 5. The finite path
-/

section Actual

/-- `A_θ` of the finite path: `[I ; (I - e^{iθ} r')⁻¹ e^{iθ} t]` with `t = 𝕊₁₀`,
`r' = 𝕊₁₁` the blocks of `𝕊 = scatteringMatrix b E W n ω` (the phase-resolution lemma). -/
def closurePhaseA (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) (θ : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  scatteringPhaseA (scatteringMatrix b E W n ω) θ

/-- The Gaussian-probe one-input interior clock after closing the far port by `e^{iθ}`,
divided by `W²`: `W⁻² Re g*(A_θ* Y A_θ)g`, `Y = 𝒰_n*𝒰_n`. -/
def closedClock (b E : ℝ) (W n : ℕ) (θ : ℝ) (x : GrowthPath W × (Fin W → ℂ)) : ℝ :=
  quadForm ((closurePhaseA b E W n x.1 θ)ᴴ * fullClock b E W n x.1 *
    closurePhaseA b E W n x.1 θ) x.2 / (W : ℝ) ^ 2

/-- The law of `closedClock` under the path law and an independent `g ~ CN(0, I_W)`. -/
def closedClockLaw (W : ℕ) (b E : ℝ) (n : ℕ) (θ : ℝ) : Measure ℝ :=
  ((growthPathLaw W b).prod (circularVectorLaw (Fin W))).map (closedClock b E W n θ)

/-- `T_W = W⁻² h*Yh` at width `W`, length `n`, energy `E` (`scaledClock` along a sequence). -/
def probeClock (b E : ℝ) (W n : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  quadForm (fullClock b E W n x.1) x.2 / (W : ℝ) ^ 2

theorem scaledClock_eq_probeClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    scaledClock b s j = probeClock b (s.energy j) (s.W j) (s.n j) := rfl

namespace NegativeClockClosure

theorem measurable_matrix_mul_fun {α l m o : Type*} [MeasurableSpace α] [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)).mul
    ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hg))

theorem measurable_scatteringMatrix (b E : ℝ) (W n : ℕ) :
    Measurable (fun ω : GrowthPath W => scatteringMatrix b E W n ω) := by
  have hc : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • G.toBlocks₂₂) := by
    have hb : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ => G.toBlocks₂₂) :=
      continuous_pi fun x => continuous_pi fun y => by unfold Matrix.toBlocks₂₂; fun_prop
    exact continuous_const.sub (Continuous.smul (f := fun _ => ((2 * etaZ b E : ℝ) : ℂ) *
      Complex.I) continuous_const hb)
  exact hc.measurable.comp (measurable_fullInverse b E W n)

theorem continuous_scatteringBlock {ι : Type*} (a c : Fin 2) :
    Continuous (fun S : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ => scatteringBlock S a c) :=
  continuous_pi fun i => continuous_pi fun j => by unfold scatteringBlock; fun_prop

theorem measurable_closurePhaseA (b E : ℝ) (W n : ℕ) :
    Measurable (fun p : GrowthPath W × ℝ => closurePhaseA b E W n p.1 p.2) := by
  have hS : Measurable (fun p : GrowthPath W × ℝ => (scatteringMatrix b E W n p.1, p.2)) :=
    ((measurable_scatteringMatrix b E W n).comp measurable_fst).prodMk measurable_snd
  have h1 : Continuous (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      (1 : Matrix (Fin W) (Fin W) ℂ) - phase q.2 • farReflection q.1) :=
    continuous_const.sub ((continuous_phase.comp continuous_snd).smul
      ((continuous_scatteringBlock 1 1).comp continuous_fst))
  have h2 : Continuous (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × ℝ =>
      phase q.2 • transmission q.1) :=
    (continuous_phase.comp continuous_snd).smul
      ((continuous_scatteringBlock 1 0).comp continuous_fst)
  have hinv := BlockBand.Layers.measurable_matrix_inv.comp (h1.measurable.comp hS)
  have hΓ := measurable_matrix_mul_fun hinv (h2.measurable.comp hS)
  exact continuous_stack.measurable.comp hΓ

/-- `(ω, θ) ↦ A_θ* Y A_θ` is measurable. -/
theorem measurable_closedMatrix (b E : ℝ) (W n : ℕ) :
    Measurable (fun p : GrowthPath W × ℝ => (closurePhaseA b E W n p.1 p.2)ᴴ *
      fullClock b E W n p.1 * closurePhaseA b E W n p.1 p.2) := by
  have hA := measurable_closurePhaseA b E W n
  have hAH : Measurable (fun p : GrowthPath W × ℝ => (closurePhaseA b E W n p.1 p.2)ᴴ) :=
    (continuous_id.matrix_conjTranspose).measurable.comp hA
  exact measurable_matrix_mul_fun (measurable_matrix_mul_fun hAH
    ((measurable_fullClock b E W n).comp measurable_fst)) hA

theorem measurable_closedClock (b E : ℝ) (W n : ℕ) (θ : ℝ) :
    Measurable (closedClock b E W n θ) := by
  have hM := (measurable_closedMatrix b E W n).comp
    (measurable_id.prodMk measurable_const : Measurable fun ω : GrowthPath W => (ω, θ))
  unfold closedClock
  exact (continuous_quadForm.measurable.comp ((hM.comp measurable_fst).prodMk
    measurable_snd)).div_const _

theorem measurable_probeClock (b E : ℝ) (W n : ℕ) : Measurable (probeClock b E W n) := by
  unfold probeClock
  exact (continuous_quadForm.measurable.comp
    (((measurable_fullClock b E W n).comp measurable_fst).prodMk measurable_snd)).div_const _

theorem closedMatrix_quadForm_nonneg (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) (θ : ℝ)
    (g : Fin W → ℂ) :
    0 ≤ quadForm ((closurePhaseA b E W n ω θ)ᴴ * fullClock b E W n ω *
      closurePhaseA b E W n ω θ) g := by
  rw [CommonPortRatios.quadForm_conj]
  exact fullClock_quadForm_nonneg _ _ _ _ _ _

/-- `ofReal ∫ exp(-c max(x,0)) d(X_*μ) = ∫⁻ ofReal exp(-c max(X,0)) dμ`. -/
theorem ofReal_integral_map_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal (∫ x, Real.exp (-(c * max x 0)) ∂μ.map X) =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-(c * max (X ω) 0))) ∂μ := by
  have hf : Continuous fun x : ℝ => c * max x 0 :=
    continuous_const.mul (continuous_id.max continuous_const)
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg _ hf
      fun x => mul_nonneg hc (le_max_right _ _))
      (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-(c * max x 0))))
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hf.neg).measurable) hX]

end NegativeClockClosure

open NegativeClockClosure in
/-- **Finite-width Laplace domination** (the negative-clock theorem before the
limit): for `0 < b < 1/2`, `|E| < 2`, every width `W`, length `n ≥ 1`, phase interval
`[θ₁, θ₂] ⊆ [0, 2π]` with `θ₁ < θ₂`, `a = (θ₂-θ₁)/(2π)` and `s ≥ 0`,
`E e^{-sT_W} ≤ (θ₂-θ₁)⁻¹ ∫_{(θ₁,θ₂]} E e^{-s a C_θ} dθ`, `C_θ = closedClock` (the tests
`e^{-s max(x,0)}` are the bounded continuous versions; all clocks are `≥ 0`). -/
theorem negativeClock_finite_laplace {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E)
    (hE1 : E < 2) {W n : ℕ} (hn : 0 < n) {θ₁ θ₂ : ℝ} (h0 : 0 ≤ θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ ≤ 2 * π) {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal (∫ x, Real.exp (-(s * max x 0)) ∂clockLaw W b (probeClock b E W n)) ≤
      ENNReal.ofReal (θ₂ - θ₁)⁻¹ * ∫⁻ θ in Set.Ioc θ₁ θ₂, ENNReal.ofReal
        (∫ x, Real.exp (-(s * ((θ₂ - θ₁) / (2 * π)) * max x 0)) ∂closedClockLaw W b E n θ) := by
  have hσ : 0 ≤ s / (W : ℝ) ^ 2 := div_nonneg hs (sq_nonneg _)
  have hc0 : 0 ≤ (θ₂ - θ₁) / (2 * π) := div_nonneg (by linarith) (by positivity)
  have hsc : 0 ≤ s * ((θ₂ - θ₁) / (2 * π)) := mul_nonneg hs hc0
  have hσc : 0 ≤ s / (W : ℝ) ^ 2 * ((θ₂ - θ₁) / (2 * π)) := mul_nonneg hσ hc0
  -- the closed-port integrand as a lower integral
  have hMm := measurable_closedMatrix b E W n
  let G : GrowthPath W × ℝ → ℝ≥0∞ := fun p => ∫⁻ g, ENNReal.ofReal (Real.exp
    (-(s / (W : ℝ) ^ 2 * ((θ₂ - θ₁) / (2 * π)) * quadForm ((closurePhaseA b E W n p.1 p.2)ᴴ *
      fullClock b E W n p.1 * closurePhaseA b E W n p.1 p.2) g))) ∂circularVectorLaw (Fin W)
  have hGm : Measurable G := by
    refine Measurable.lintegral_prod_right' (f := fun q : (GrowthPath W × ℝ) × (Fin W → ℂ) =>
      ENNReal.ofReal (Real.exp (-(s / (W : ℝ) ^ 2 * ((θ₂ - θ₁) / (2 * π)) *
        quadForm ((closurePhaseA b E W n q.1.1 q.1.2)ᴴ * fullClock b E W n q.1.1 *
          closurePhaseA b E W n q.1.1 q.1.2) q.2)))) ?_
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_const.mul (continuous_quadForm.measurable.comp
        ((hMm.comp measurable_fst).prodMk measurable_snd))).neg))
  have hGeq : ∀ ω θ, ENNReal.ofReal (∫ g, Real.exp (-(s / (W : ℝ) ^ 2 *
      ((θ₂ - θ₁) / (2 * π)) * quadForm ((scatteringPhaseA (scatteringMatrix b E W n ω) θ)ᴴ *
        ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω) *
          scatteringPhaseA (scatteringMatrix b E W n ω) θ) g)) ∂circularVectorLaw (Fin W)) =
      G (ω, θ) := by
    intro ω θ
    have hcont : Continuous fun g : Fin W → ℂ => s / (W : ℝ) ^ 2 * ((θ₂ - θ₁) / (2 * π)) *
        quadForm ((closurePhaseA b E W n ω θ)ᴴ * fullClock b E W n ω *
          closurePhaseA b E W n ω θ) g :=
      continuous_const.mul (continuous_quadForm.comp (continuous_const.prodMk continuous_id))
    exact ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg _ hcont fun g =>
      mul_nonneg hσc (closedMatrix_quadForm_nonneg b E W n ω θ g))
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)
  -- left side as an iterated integral
  have hL : ENNReal.ofReal (∫ x, Real.exp (-(s * max x 0)) ∂clockLaw W b (probeClock b E W n)) =
      ∫⁻ ω, ENNReal.ofReal (∫ h, Real.exp (-(s / (W : ℝ) ^ 2 *
        quadForm ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω) h))
        ∂circularVectorLaw (Fin 2 × Fin W)) ∂growthPathLaw W b := by
    have hP := measurable_probeClock b E W n
    unfold clockLaw probedClockLaw
    have hm : Measurable fun z : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
        ENNReal.ofReal (Real.exp (-(s * max (probeClock b E W n z) 0))) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (hP.max measurable_const)).neg))
    rw [ofReal_integral_map_exp _ hP hs, lintegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun ω => ?_
    have hcont : Continuous fun h : Fin 2 × Fin W → ℂ => s / (W : ℝ) ^ 2 *
        quadForm ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω) h :=
      continuous_const.mul (continuous_quadForm.comp (continuous_const.prodMk continuous_id))
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg _ hcont fun h =>
      mul_nonneg hσ (fullClock_quadForm_nonneg b E W n ω h))
      (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    refine lintegral_congr fun h => ?_
    have hq := fullClock_quadForm_nonneg b E W n ω h
    have hp : 0 ≤ probeClock b E W n (ω, h) := div_nonneg hq (sq_nonneg _)
    rw [max_eq_left hp]
    unfold probeClock fullClock
    congr 3
    ring
  -- right side, for each phase
  have hR : ∀ θ, ∫⁻ ω, G (ω, θ) ∂growthPathLaw W b = ENNReal.ofReal
      (∫ x, Real.exp (-(s * ((θ₂ - θ₁) / (2 * π)) * max x 0)) ∂closedClockLaw W b E n θ) := by
    intro θ
    have hC := measurable_closedClock b E W n θ
    unfold closedClockLaw
    have hm : Measurable fun z : GrowthPath W × (Fin W → ℂ) =>
        ENNReal.ofReal (Real.exp (-(s * ((θ₂ - θ₁) / (2 * π)) * max (closedClock b E W n θ z) 0))) :=
      ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (hC.max measurable_const)).neg))
    rw [ofReal_integral_map_exp _ hC hsc, lintegral_prod _ hm.aemeasurable]
    refine lintegral_congr fun ω => lintegral_congr fun g => ?_
    have hp : 0 ≤ closedClock b E W n θ (ω, g) :=
      div_nonneg (closedMatrix_quadForm_nonneg b E W n ω θ g) (sq_nonneg _)
    rw [max_eq_left hp]
    unfold closedClock
    congr 3
    ring
  rw [hL]
  have hae := negativeClock_ae_scattering hb0 hb1 hE0 hE1 W n hn
  calc ∫⁻ ω, ENNReal.ofReal (∫ h, Real.exp (-(s / (W : ℝ) ^ 2 *
        quadForm ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω) h))
        ∂circularVectorLaw (Fin 2 × Fin W)) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal (θ₂ - θ₁)⁻¹ * (∫⁻ θ in Set.Ioc θ₁ θ₂, G (ω, θ))
          ∂growthPathLaw W b := by
        refine lintegral_mono_ae (hae.mono fun ω hω => ?_)
        have := negativeClock_phase_laplace (boundaryToInterior b E W n ω)
          (scatteringMatrix b E W n ω) hω.1 hω.2 h0 h12 h2 hσ
        simp_rw [hGeq] at this
        exact this
    _ = ENNReal.ofReal (θ₂ - θ₁)⁻¹ * ∫⁻ θ in Set.Ioc θ₁ θ₂, (∫⁻ ω, G (ω, θ)
          ∂growthPathLaw W b) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_lintegral_swap (f := fun ω θ => G (ω, θ)) hGm.aemeasurable]
    _ = _ := by
        congr 1
        exact lintegral_congr fun θ => hR θ

end Actual

end BlockBand.Endpoints.Clock
