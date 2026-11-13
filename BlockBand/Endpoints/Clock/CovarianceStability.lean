module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Endpoints.Clock.CommonPortRatios

/-!
# Stability of Gaussian clocks under a relative change of covariance

Step 4 of the proof of the two-positive-clocks lemma, used in the physical lead-profile theorem
and in the endpoint argument.

Law: `g ~ CN(0, I_N)` (`circularVectorLaw (Fin N)`); covariances `Γ = MMᴴ`, `Γ₀ = M₀M₀ᴴ` with
`(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `ω ≥ 0`. All bounds are dimension-free (uniform in `N`, `Γ₀`, `Γ`,
`M`, `M₀`, the clock matrices and the defaults).

Proved here (unconditional; no contract is consumed):
* `clockCovarianceStability_holds : ClockCovarianceStabilityContract` (Step 4 of the proof,
  both clauses);
* `clockCovarianceStability_cube`: the `k`-ratio form with numerators `-D ⪯ B_j ⪯ D` and a
  continuous test on the cube `[-1,1]^k`, used in the physical lead-profile theorem.

Proof. The paper differentiates `log det(I + Γ_t^{1/2}FΓ_t^{1/2})` along `Γ_t`. We use instead a
pointwise coupling on the dual Gaussian side, with no determinant: for `F = BᴴB ⪰ 0`,
`E_g exp(-(Mg)*F(Mg)) = E_h exp(-(Bᴴh)*Γ(Bᴴh))` (`integral_exp_neg_quadForm_mulVec_eq`, the
Laplace identity plus Sylvester), and pointwise
`|e^{-w*Γw} - e^{-w*Γ₀w}| ≤ |w*Γw - w*Γ₀w| ≤ ω w*Γ₀w`, whose `h`-expectation is
`ω Re Tr(BΓ₀Bᴴ) = ω Re Tr(Γ₀F)`. Hence the joint Laplace transforms differ by at most
`ω Re Tr(Γ₀F)` (`CovarianceStability.abs_laplace_sub_le`), which is the paper's bound. The weak
comparison is then `exists_laplace_comparison` (first moments `Tr(Γ₀P_i)/T ≤ K` of the reference
law), and the ratios are handled by the small-denominator device `1_{x<u} ≤ e·e^{-x/u}` with
`E exp(-X₀/u) ≤ u` for the reference and `≤ u + ω/u` for the perturbed law, mirroring
`commonPort_ratio_comparison`. The `k`-ratio form uses the positive clocks `P₀ = D`,
`P_{j+1} = D + B_j` (`Tr(Γ₀P_{j+1}) ≤ 2Tr(Γ₀D)`), as `commonPortRatios_of_commonPortMean`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder Matrix BoundedContinuousFunction

namespace CovarianceStability

/-!
## 1. Elementary algebra
-/

section Algebra

variable {ι : Type*} [Fintype ι]

/-- The quadratic form is subtractive in the matrix. -/
theorem quadForm_sub (P Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm (P - Q) v = quadForm P v - quadForm Q v := by
  unfold quadForm; rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- Pointwise sandwich: `|w*Γw - w*Γ₀w| ≤ ω w*Γ₀w` when `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`. -/
theorem abs_quadForm_sub_le {Γ₀ Γ : Matrix ι ι ℂ} {ω : ℝ}
    (h1 : (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef)
    (h2 : (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef) (w : ι → ℂ) :
    |quadForm Γ w - quadForm Γ₀ w| ≤ ω * quadForm Γ₀ w := by
  have a := CommonPortRatios.quadForm_nonneg_of_posSemidef h1 w
  have b := CommonPortRatios.quadForm_nonneg_of_posSemidef h2 w
  rw [quadForm_sub, CommonPortRatios.quadForm_smul_real] at a b
  rw [abs_le]; constructor <;> nlinarith

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (by linarith)
  have hle : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h1 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 := CommonPortRatios.one_sub_exp_neg_le (b - a)
  have h4 := CommonPortRatios.one_sub_exp_neg_nonneg (show 0 ≤ b - a by linarith)
  rw [h1]
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) h4]

/-- `v ↦ Re (Lv)*Q(Lv)` is continuous. -/
theorem continuous_quadForm_mulVec {κ : Type*} [Fintype κ] (Q : Matrix ι ι ℂ)
    (L : Matrix ι κ ℂ) : Continuous (fun v : κ → ℂ => quadForm Q (L *ᵥ v)) :=
  continuous_quadForm.comp (continuous_const.prodMk
    (Continuous.matrix_mulVec continuous_const continuous_id))

/-- `E_h Re (Lh)*Q(Lh) = Re Tr(LᴴQL)`. -/
theorem integral_quadForm_mulVec {κ : Type*} [Fintype κ] (Q : Matrix ι ι ℂ)
    (L : Matrix ι κ ℂ) :
    ∫ h, quadForm Q (L *ᵥ h) ∂circularVectorLaw κ = (Lᴴ * Q * L).trace.re := by
  simp_rw [← CommonPortRatios.quadForm_conj]
  exact integral_quadForm_circular _

/-- `h ↦ Re (Lh)*Q(Lh)` is integrable. -/
theorem integrable_quadForm_mulVec {κ : Type*} [Fintype κ] (Q : Matrix ι ι ℂ)
    (L : Matrix ι κ ℂ) :
    Integrable (fun h => quadForm Q (L *ᵥ h)) (circularVectorLaw κ) := by
  simp_rw [← CommonPortRatios.quadForm_conj]
  exact integrable_quadForm_circular _

/-- `E exp(-Re v*Qv)` of any measurable `v` with `Q ⪰ 0` is the integral of a function in `(0,1]`. -/
theorem integrable_exp_neg_quadForm_mulVec {κ : Type*} [Fintype κ] {Q : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) (L : Matrix ι κ ℂ) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun h => Real.exp (-(quadForm Q (L *ᵥ h) * c))) (circularVectorLaw κ) :=
  CommonPortRatios.integrable_of_abs_le _
    (Real.continuous_exp.measurable.comp
      (((continuous_quadForm_mulVec Q L).mul continuous_const).measurable.neg)) 1
    fun h => by
      rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef hQ _) hc

end Algebra

section Trace

variable {N : ℕ}

/-- `Re Tr(Γ₀Q) = Re Tr(M₀ᴴQM₀)` for `M₀M₀ᴴ = Γ₀`. -/
theorem traceAgainst_eq_trace_conj {Γ₀ M₀ : Matrix (Fin N) (Fin N) ℂ} (h : M₀ * M₀ᴴ = Γ₀)
    (Q : Matrix (Fin N) (Fin N) ℂ) : traceAgainst Γ₀ Q = (M₀ᴴ * Q * M₀).trace.re := by
  unfold traceAgainst; rw [← h, Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- `E_g Re (M₀g)*Q(M₀g) = Re Tr(Γ₀Q)`. -/
theorem integral_quadForm_mulVec_eq_traceAgainst {Γ₀ M₀ : Matrix (Fin N) (Fin N) ℂ}
    (h : M₀ * M₀ᴴ = Γ₀) (Q : Matrix (Fin N) (Fin N) ℂ) :
    ∫ g, quadForm Q (M₀ *ᵥ g) ∂circularVectorLaw (Fin N) = traceAgainst Γ₀ Q := by
  rw [integral_quadForm_mulVec, traceAgainst_eq_trace_conj h]

/-- `Re Tr(Γ₀Q) ≥ 0` for `Q ⪰ 0` and `Γ₀ = M₀M₀ᴴ`. -/
theorem traceAgainst_nonneg_of {Γ₀ M₀ : Matrix (Fin N) (Fin N) ℂ} (h : M₀ * M₀ᴴ = Γ₀)
    {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.PosSemidef) : 0 ≤ traceAgainst Γ₀ Q := by
  rw [traceAgainst_eq_trace_conj h]
  exact (Complex.nonneg_iff.mp (hQ.conjTranspose_mul_mul_same M₀).trace_nonneg).1

/-- `Re Tr(Γ₀·)` is additive. -/
theorem traceAgainst_add (Γ₀ P Q : Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ₀ (P + Q) = traceAgainst Γ₀ P + traceAgainst Γ₀ Q := by
  unfold traceAgainst; rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

/-- `Re Tr(Γ₀·)` is subtractive. -/
theorem traceAgainst_sub (Γ₀ P Q : Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ₀ (P - Q) = traceAgainst Γ₀ P - traceAgainst Γ₀ Q := by
  unfold traceAgainst; rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

/-- `Re Tr(Γ₀ Σ c_i P_i) = Σ c_i Re Tr(Γ₀P_i)` for real `c_i`. -/
theorem traceAgainst_sum_real_smul {n : Type*} [Fintype n] (Γ₀ : Matrix (Fin N) (Fin N) ℂ)
    (c : n → ℝ) (P : n → Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ₀ (∑ i, ((c i : ℝ) : ℂ) • P i) = ∑ i, c i * traceAgainst Γ₀ (P i) := by
  unfold traceAgainst
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- `Re Tr(Γ₀ (cQ)) = c Re Tr(Γ₀Q)` for real `c`. -/
theorem traceAgainst_smul_real (Γ₀ Q : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) :
    traceAgainst Γ₀ ((c : ℂ) • Q) = c * traceAgainst Γ₀ Q := by
  unfold traceAgainst
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end Trace

/-!
## 2. The Laplace transforms (the Sylvester-derivative bound)
-/

/-- **Laplace closeness under a relative change of covariance.** For every
`F ⪰ 0`, `MMᴴ = Γ`, `M₀M₀ᴴ = Γ₀` with `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`:
`|E_g e^{-(Mg)*F(Mg)} - E_g e^{-(M₀g)*F(M₀g)}| ≤ ω Re Tr(Γ₀F)`, dimension-free. -/
theorem abs_laplace_sub_le {N : ℕ} {Γ₀ Γ : Matrix (Fin N) (Fin N) ℂ} {ω : ℝ}
    (h1 : (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef)
    (h2 : (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef)
    {M M₀ : Matrix (Fin N) (Fin N) ℂ} (hM : M * Mᴴ = Γ) (hM₀ : M₀ * M₀ᴴ = Γ₀)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.PosSemidef) :
    |(∫ g, Real.exp (-quadForm F (M *ᵥ g)) ∂circularVectorLaw (Fin N)) -
        ∫ g, Real.exp (-quadForm F (M₀ *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤
      ω * traceAgainst Γ₀ F := by
  obtain ⟨B, hFB⟩ : ∃ B : Matrix (Fin N) (Fin N) ℂ, F = Bᴴ * B := by
    open scoped MatrixOrder in
    obtain ⟨S, hS, -, hSS⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      hF.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hF.nonneg)
    exact ⟨S, by rw [show Sᴴ = S from hS, hSS]⟩
  subst hFB
  rw [integral_exp_neg_quadForm_mulVec_eq B M, integral_exp_neg_quadForm_mulVec_eq B M₀, hM, hM₀]
  have hΓ : Γ.PosSemidef := hM ▸ posSemidef_self_mul_conjTranspose M
  have hΓ₀ : Γ₀.PosSemidef := hM₀ ▸ posSemidef_self_mul_conjTranspose M₀
  have hi : ∀ {Q : Matrix (Fin N) (Fin N) ℂ}, Q.PosSemidef →
      Integrable (fun h => Real.exp (-quadForm Q (Bᴴ *ᵥ h))) (circularVectorLaw (Fin N)) := by
    intro Q hQ
    have := integrable_exp_neg_quadForm_mulVec hQ Bᴴ 1 zero_le_one
    simpa only [mul_one] using this
  rw [← integral_sub (hi hΓ) (hi hΓ₀)]
  have hq := integrable_quadForm_mulVec Γ₀ Bᴴ
  calc |∫ h, (Real.exp (-quadForm Γ (Bᴴ *ᵥ h)) - Real.exp (-quadForm Γ₀ (Bᴴ *ᵥ h)))
        ∂circularVectorLaw (Fin N)|
      ≤ ∫ h, ω * quadForm Γ₀ (Bᴴ *ᵥ h) ∂circularVectorLaw (Fin N) := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hq.const_mul ω)
          (Filter.Eventually.of_forall fun h => ?_)
        rw [Real.norm_eq_abs]
        exact (abs_exp_neg_sub_exp_neg_le (CommonPortRatios.quadForm_nonneg_of_posSemidef hΓ _)
          (CommonPortRatios.quadForm_nonneg_of_posSemidef hΓ₀ _)).trans
          (abs_quadForm_sub_le h1 h2 _)
    _ = ω * traceAgainst Γ₀ (Bᴴ * B) := by
        rw [integral_const_mul, integral_quadForm_mulVec, conjTranspose_conjTranspose]
        unfold traceAgainst
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-!
## 3. Joint comparison of a finite family of clocks
-/

/-- **Joint comparison of a finite family of Gaussian clocks under a relative change of
covariance** (Step 4 of the proof, with the Laplace argument of Step 2). Fixed first: `n`, a
continuous `ψ : ℝⁿ → ℝ` with `|ψ| ≤ Mψ`, `K` and `ε > 0`.
Then `ω₀ > 0`; for every `N`, `Γ₀, Γ` with `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `0 ≤ ω ≤ ω₀`, all
`P_i ⪰ 0`, `T > 0` with `Re Tr(Γ₀P_i) ≤ KT`, all `MMᴴ = Γ`, `M₀M₀ᴴ = Γ₀`:
`|E ψ((Re (Mg)*P_i(Mg)/T)_i) - E ψ((Re (M₀g)*P_i(M₀g)/T)_i)| ≤ ε`. -/
theorem clockFamily_comparison (n : ℕ) (ψ : (Fin n → ℝ) → ℝ) (hψ : Continuous ψ) {Mψ : ℝ}
    (hM : ∀ x, |ψ x| ≤ Mψ) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ (N : ℕ) (Γ₀ Γ : Matrix (Fin N) (Fin N) ℂ) (ω : ℝ), 0 ≤ ω → ω ≤ ω₀ →
      (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef → (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef →
      ∀ P : Fin n → Matrix (Fin N) (Fin N) ℂ, (∀ i, (P i).PosSemidef) →
      ∀ T : ℝ, 0 < T → (∀ i, traceAgainst Γ₀ (P i) ≤ K * T) →
      ∀ M M₀ : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = Γ → M₀ * M₀ᴴ = Γ₀ →
        |(∫ g, ψ (fun i => quadForm (P i) (M *ᵥ g) / T) ∂circularVectorLaw (Fin N)) -
          ∫ g, ψ (fun i => quadForm (P i) (M₀ *ᵥ g) / T) ∂circularVectorLaw (Fin N)| ≤ ε := by
  set K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  obtain ⟨η, hη, Nl, hNl, hcmp⟩ := exists_laplace_comparison n ψ hψ hM K' hε
  set Λ := n * Nl * K'
  have hΛ : 0 ≤ Λ := by positivity
  refine ⟨η / (Λ + 1), by positivity, ?_⟩
  intro N Γ₀ Γ ω hω0 hω h1 h2 P hP T hT hPK M M₀ hMM hMM₀
  have hPK' : ∀ i, traceAgainst Γ₀ (P i) ≤ K' * T := fun i =>
    (hPK i).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hT.le)
  have hPtr : ∀ i, 0 ≤ traceAgainst Γ₀ (P i) := fun i => traceAgainst_nonneg_of hMM₀ (hP i)
  refine hcmp (circularVectorLaw (Fin N)) (circularVectorLaw (Fin N)) inferInstance inferInstance
    (fun g i => quadForm (P i) (M *ᵥ g) / T) (fun g i => quadForm (P i) (M₀ *ᵥ g) / T)
    (measurable_pi_iff.mpr fun i => ((continuous_quadForm_mulVec (P i) M).measurable.div_const _))
    (measurable_pi_iff.mpr fun i => ((continuous_quadForm_mulVec (P i) M₀).measurable.div_const _))
    (fun g i => div_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef (hP i) _) hT.le)
    (fun g i => div_nonneg (CommonPortRatios.quadForm_nonneg_of_posSemidef (hP i) _) hT.le)
    (fun i => (integrable_quadForm_mulVec (P i) M₀).div_const T)
    (fun i => by
      rw [integral_div, integral_quadForm_mulVec_eq_traceAgainst hMM₀, div_le_iff₀ hT]
      exact hPK' i) ?_
  intro lam hl hlN
  set c : Fin n → ℝ := fun i => lam i / T
  have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (hl i) hT.le
  set F := ∑ i, ((c i : ℝ) : ℂ) • P i
  have hF : F.PosSemidef := CommonPortRatios.posSemidef_sum_real_smul c hc0 P hP
  have e1 : ∀ v, ∑ i, lam i * (quadForm (P i) v / T) = quadForm F v := by
    intro v; rw [CommonPortRatios.quadForm_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c]; ring
  simp_rw [e1]
  have hTrF : traceAgainst Γ₀ F ≤ Λ := by
    rw [traceAgainst_sum_real_smul]
    calc ∑ i, c i * traceAgainst Γ₀ (P i) ≤ ∑ _i : Fin n, Nl / T * (K' * T) :=
          Finset.sum_le_sum fun i _ => mul_le_mul (div_le_div_of_nonneg_right (hlN i)
            hT.le) (hPK' i) (hPtr i) (by positivity)
      _ = Λ := by
          have := hT.ne'
          simp only [Λ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  refine (abs_laplace_sub_le h1 h2 hMM hMM₀ hF).trans ?_
  calc ω * traceAgainst Γ₀ F ≤ η / (Λ + 1) * Λ :=
        mul_le_mul hω hTrF (traceAgainst_nonneg_of hMM₀ hF) (by positivity)
    _ ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-!
## 4. Ratios with small denominators
-/

/-- `E exp(-(Re (M₀g)*P(M₀g)/T)/u) ≤ u` when `T = Re Tr(Γ₀P) > 0`, `u > 0`. -/
theorem integral_exp_neg_clock_div_le_of {N : ℕ} {Γ₀ M₀ P : Matrix (Fin N) (Fin N) ℂ}
    (hM₀ : M₀ * M₀ᴴ = Γ₀) (hP : P.PosSemidef) {T u : ℝ} (hT : T = traceAgainst Γ₀ P)
    (hT0 : 0 < T) (hu : 0 < u) :
    ∫ g, Real.exp (-(quadForm P (M₀ *ᵥ g) / T / u)) ∂circularVectorLaw (Fin N) ≤ u := by
  simp_rw [← CommonPortRatios.quadForm_conj]
  exact integral_exp_neg_clock_div_le (hP.conjTranspose_mul_mul_same M₀)
    (hT.trans (traceAgainst_eq_trace_conj hM₀ P)) hT0 hu

/-- **Ratio comparison with small denominators under a relative change of covariance**
(Step 4 of the proof with Step 3). Fixed first: `m`, a family `ψ_u`
(`u > 0`) of continuous tests on `ℝ^{m+1}` bounded by `Mψ`, `K` and `ε > 0`. Then `ω₀ > 0`;
for every `N`, `Γ₀, Γ` with `(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `0 ≤ ω ≤ ω₀`, all `P_i ⪰ 0` with
`T = Re Tr(Γ₀P₀) > 0`, `Re Tr(Γ₀P_i) ≤ KT`, all `MMᴴ = Γ`, `M₀M₀ᴴ = Γ₀`, and every measurable
`G` with `|G| ≤ Mψ` which equals `ψ_u((Re v*P_iv/s)_i)` wherever `Re v*P₀v/s ≥ u` (any scale
`s > 0`, any `u > 0`): `|E G(Mg) - E G(M₀g)| ≤ ε`. -/
theorem ratio_comparison (m : ℕ) (ψ : ℝ → (Fin (m + 1) → ℝ) → ℝ)
    (hψc : ∀ u, 0 < u → Continuous (ψ u)) {Mψ : ℝ} (hψM : ∀ u x, |ψ u x| ≤ Mψ) (K : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧ ∀ (N : ℕ) (Γ₀ Γ : Matrix (Fin N) (Fin N) ℂ) (ω : ℝ), 0 ≤ ω → ω ≤ ω₀ →
      (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef → (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef →
      ∀ P : Fin (m + 1) → Matrix (Fin N) (Fin N) ℂ, (∀ i, (P i).PosSemidef) →
      0 < traceAgainst Γ₀ (P 0) → (∀ i, traceAgainst Γ₀ (P i) ≤ K * traceAgainst Γ₀ (P 0)) →
      ∀ M M₀ : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = Γ → M₀ * M₀ᴴ = Γ₀ →
      ∀ G : (Fin N → ℂ) → ℝ, Measurable G → (∀ v, |G v| ≤ Mψ) →
      (∀ u, 0 < u → ∀ v (s : ℝ), 0 < s → u ≤ quadForm (P 0) v / s →
        G v = ψ u (fun i => quadForm (P i) v / s)) →
        |(∫ g, G (M *ᵥ g) ∂circularVectorLaw (Fin N)) -
          ∫ g, G (M₀ *ᵥ g) ∂circularVectorLaw (Fin N)| ≤ ε := by
  have hM0 : 0 ≤ Mψ := (abs_nonneg _).trans (hψM 1 0)
  set E := Real.exp 1
  have hE : 0 < E := Real.exp_pos 1
  set q := Mψ * E
  have hq : 0 ≤ q := by positivity
  set u := ε / (16 * (q + 1))
  have hu : 0 < u := by positivity
  set t := ε / (8 * (q + 1))
  have ht : 0 < t := by positivity
  obtain ⟨ω₁, hω₁, hfam⟩ := clockFamily_comparison (m + 1) (ψ u) (hψc u hu) (hψM u) K
    (half_pos hε)
  refine ⟨min ω₁ (t * u), lt_min hω₁ (by positivity), ?_⟩
  intro N Γ₀ Γ ω hω0 hω h1 h2 P hP hT hPK M M₀ hMM hMM₀ G hG hGM hagree
  set T := traceAgainst Γ₀ (P 0) with hTdef
  set μ := circularVectorLaw (Fin N)
  have hB := hfam N Γ₀ Γ ω hω0 (hω.trans (min_le_left _ _)) h1 h2 P hP T hT hPK M M₀ hMM hMM₀
  have hpm : ∀ L : Matrix (Fin N) (Fin N) ℂ, Measurable (fun g : Fin N → ℂ => L *ᵥ g) :=
    fun L => (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  -- the exponential weights
  set wL : (Fin N → ℂ) → ℝ := fun g => Real.exp (-(quadForm (P 0) (M *ᵥ g) / T / u))
  set wR : (Fin N → ℂ) → ℝ := fun g => Real.exp (-(quadForm (P 0) (M₀ *ᵥ g) / T / u))
  have hw : ∀ L : Matrix (Fin N) (Fin N) ℂ,
      Integrable (fun g => Real.exp (-(quadForm (P 0) (L *ᵥ g) / T / u))) μ := by
    intro L
    have := integrable_exp_neg_quadForm_mulVec (hP 0) L (1 / T / u) (by positivity)
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only; congr 2; field_simp
  have hwL : Integrable wL μ := hw M
  have hwR : Integrable wR μ := hw M₀
  -- the reference weight
  have hI : ∫ g, wR g ∂μ ≤ u := integral_exp_neg_clock_div_le_of hMM₀ (hP 0) rfl hT hu
  -- the perturbed weight, by the Laplace closeness at `F = P₀/(Tu)`
  have hJ : ∫ g, wL g ∂μ ≤ u + t := by
    set F : Matrix (Fin N) (Fin N) ℂ := ((1 / (T * u) : ℝ) : ℂ) • P 0
    have hF : F.PosSemidef := (hP 0).smul (Complex.zero_le_real.mpr (by positivity))
    have hFtr : traceAgainst Γ₀ F = 1 / u := by
      simp only [F]
      rw [traceAgainst_smul_real, ← hTdef]
      field_simp
    have hlap := abs_laplace_sub_le h1 h2 hMM hMM₀ hF
    have e : ∀ L : Matrix (Fin N) (Fin N) ℂ,
        (fun g => Real.exp (-quadForm F (L *ᵥ g))) =
          fun g => Real.exp (-(quadForm (P 0) (L *ᵥ g) / T / u)) := by
      intro L; funext g; simp only [F]; rw [CommonPortRatios.quadForm_smul_real]; congr 2
      field_simp
    rw [e M, e M₀, hFtr] at hlap
    have hωt : ω * (1 / u) ≤ t := by
      rw [mul_one_div, div_le_iff₀ hu]; exact hω.trans (min_le_right _ _)
    linarith [(abs_le.mp hlap).2, hI]
  -- the two cutoff errors
  have hGI : ∀ L : Matrix (Fin N) (Fin N) ℂ, Integrable (fun g => G (L *ᵥ g)) μ := fun L =>
    CommonPortRatios.integrable_of_abs_le μ (f := fun g => G (L *ᵥ g)) (hG.comp (hpm L)) Mψ
      fun g => hGM _
  have hψI : ∀ L : Matrix (Fin N) (Fin N) ℂ,
      Integrable (fun g => ψ u (fun i => quadForm (P i) (L *ᵥ g) / T)) μ := fun L =>
    CommonPortRatios.integrable_of_abs_le μ ((hψc u hu).measurable.comp
      (measurable_pi_iff.mpr fun i => (continuous_quadForm_mulVec (P i) L).measurable.div_const _))
      Mψ fun g => hψM _ _
  have hcut : ∀ L : Matrix (Fin N) (Fin N) ℂ,
      |(∫ g, G (L *ᵥ g) ∂μ) - ∫ g, ψ u (fun i => quadForm (P i) (L *ᵥ g) / T) ∂μ| ≤
        2 * Mψ * E * ∫ g, Real.exp (-(quadForm (P 0) (L *ᵥ g) / T / u)) ∂μ := by
    intro L
    rw [← integral_sub (hGI L) (hψI L), ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hw L).const_mul _)
      (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs]
    exact CommonPortRatios.abs_sub_le_two_mul_exp_neg hu (hGM _) (hψM _ _)
      (hagree u hu _ T hT)
  have hA := hcut M
  have hC := hcut M₀
  -- assemble
  have hq2 : 2 * q * (2 * u + t) ≤ ε / 2 := by
    have : 2 * q * (2 * u + t) = ε / 2 * (q / (q + 1)) := by
      simp only [u, t]; field_simp; ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
  have hJ0 : 0 ≤ ∫ g, wL g ∂μ := integral_nonneg fun g => (Real.exp_pos _).le
  have hI0 : 0 ≤ ∫ g, wR g ∂μ := integral_nonneg fun g => (Real.exp_pos _).le
  have hA' : |(∫ g, G (M *ᵥ g) ∂μ) - ∫ g, ψ u (fun i => quadForm (P i) (M *ᵥ g) / T) ∂μ| ≤
      2 * q * (u + t) := by
    refine hA.trans ?_
    have := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 2 * Mψ * E by positivity)
    simp only [q]; linarith
  have hC' : |(∫ g, G (M₀ *ᵥ g) ∂μ) - ∫ g, ψ u (fun i => quadForm (P i) (M₀ *ᵥ g) / T) ∂μ| ≤
      2 * q * u := by
    refine hC.trans ?_
    have := mul_le_mul_of_nonneg_left hI (show 0 ≤ 2 * Mψ * E by positivity)
    simp only [q]; linarith
  have htri := abs_sub_le (∫ g, G (M *ᵥ g) ∂μ)
    (∫ g, ψ u (fun i => quadForm (P i) (M *ᵥ g) / T) ∂μ) (∫ g, G (M₀ *ᵥ g) ∂μ)
  have htri2 := abs_sub_le (∫ g, ψ u (fun i => quadForm (P i) (M *ᵥ g) / T) ∂μ)
    (∫ g, ψ u (fun i => quadForm (P i) (M₀ *ᵥ g) / T) ∂μ) (∫ g, G (M₀ *ᵥ g) ∂μ)
  rw [abs_sub_comm (∫ g, ψ u (fun i => quadForm (P i) (M₀ *ᵥ g) / T) ∂μ)] at htri2
  nlinarith

end CovarianceStability

/-!
## 5. The contract and the `k`-ratio form
-/

open CovarianceStability

/-- **Covariance stability**, Step 4 of the proof of the two-positive-clocks lemma. Exactly
`ClockCovarianceStabilityContract`: fixed first `K`, a bounded continuous `ψ` of two clocks and
`Φ ∈ C_b([0,∞))`; for every `ε > 0` there is `ω₀ > 0`; for every `N`, `Γ₀ ⪰ 0`, `Γ` with
`(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `0 ≤ ω ≤ ω₀`, `D, C ⪰ 0` with `T₀ = Re Tr(Γ₀D) > 0`,
`Re Tr(Γ₀C) ≤ KT₀`, `MMᴴ = Γ`, `M₀M₀ᴴ = Γ₀` and measurable default `d`, both the joint clause
(clocks normalized by `T₀`) and the ratio clause hold within `ε`, with `g ~ CN(0, I_N)`. `ω₀`
depends only on `K, ψ, Φ, ε` (dimension-free). -/
theorem clockCovarianceStability_holds : ClockCovarianceStabilityContract := by
  intro K ψ Φ ε hε
  -- joint clause
  set ψ' : (Fin 2 → ℝ) → ℝ := fun x => ψ (clockPair (x 0) (x 1))
  have hψ' : Continuous ψ' := ψ.continuous.comp
    ((CommonPortRatios.continuous_projIci_zero.comp (continuous_apply 0)).prodMk
      (CommonPortRatios.continuous_projIci_zero.comp (continuous_apply 1)))
  have hψ'M : ∀ x, |ψ' x| ≤ ‖ψ‖ := fun x => by
    rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _
  obtain ⟨ω₁, hω₁, hfam⟩ := clockFamily_comparison 2 ψ' hψ' hψ'M (max 1 K) hε
  -- ratio clause
  set φ : ℝ → (Fin 2 → ℝ) → ℝ := fun u x => Φ (Set.projIci 0 (x 1 / max (x 0) u))
  have hφc : ∀ u, 0 < u → Continuous (φ u) := fun u hu => Φ.continuous.comp
    (CommonPortRatios.continuous_projIci_zero.comp ((continuous_apply 1).div
      ((continuous_apply 0).max continuous_const)
      fun x => (lt_of_lt_of_le hu (le_max_right _ _)).ne'))
  have hφM : ∀ u x, |φ u x| ≤ ‖Φ‖ := fun u x => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  obtain ⟨ω₂, hω₂, hrat⟩ := ratio_comparison 1 φ hφc hφM (max 1 K) hε
  refine ⟨min ω₁ ω₂, lt_min hω₁ hω₂, ?_⟩
  intro N Γ₀ Γ ω hω0 hω _hΓ₀ h1 h2 D C hD hC hT hCK M M₀ hMM hMM₀ d hd T
  have hP : ∀ i, (![D, C] i).PosSemidef := Fin.forall_fin_two.mpr ⟨hD, hC⟩
  have hPK : ∀ i, traceAgainst Γ₀ (![D, C] i) ≤ max 1 K * T := Fin.forall_fin_two.mpr
    ⟨by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 K) hT.le,
     by simpa using hCK.trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) hT.le)⟩
  refine ⟨hfam N Γ₀ Γ ω hω0 (hω.trans (min_le_left _ _)) h1 h2 ![D, C] hP T hT hPK
    M M₀ hMM hMM₀, ?_⟩
  have hGm : Measurable (fun v => Φ (ratioHalfLine C D d v)) := by
    refine Φ.continuous.measurable.comp
      (CommonPortRatios.continuous_projIci_zero.measurable.comp ?_)
    exact Measurable.ite (measurableSet_eq_fun (CommonPortRatios.measurable_quadForm_left D)
      measurable_const) hd
      ((CommonPortRatios.measurable_quadForm_left C).div
        (CommonPortRatios.measurable_quadForm_left D))
  have hGM : ∀ v, |Φ (ratioHalfLine C D d v)| ≤ ‖Φ‖ := fun v => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  refine hrat N Γ₀ Γ ω hω0 (hω.trans (min_le_right _ _)) h1 h2 ![D, C] hP hT hPK M M₀ hMM hMM₀
    _ hGm hGM ?_
  intro u hu v s hs hus
  have hq0 : quadForm D v ≠ 0 := by
    intro h0
    simp only [Matrix.cons_val_zero] at hus
    rw [h0, zero_div] at hus
    linarith
  simp only [φ, ratioHalfLine, hq0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Matrix.cons_val_zero] at hus
  rw [max_eq_left hus]
  congr 2
  field_simp

/-- **Covariance stability, `k`-ratio form** (the use of Step 4 of the two-positive-clocks
lemma in the physical lead-profile theorem). Fixed first `k` and a continuous
`Φ : [-1,1]^k → ℝ`; for every `ε > 0` there is `ω₀ > 0`; for every `N`, `Γ₀ ⪰ 0`, `Γ` with
`(1-ω)Γ₀ ⪯ Γ ⪯ (1+ω)Γ₀`, `0 ≤ ω ≤ ω₀`, every `D ⪰ 0` with `Re Tr(Γ₀D) > 0`, Hermitian `B_j` with
`-D ⪯ B_j ⪯ D` (`IsSandwiched`; no norm, rank or condition-number restriction), every
`MMᴴ = Γ`, `M₀M₀ᴴ = Γ₀` and measurable default `d`:
`|E Φ((Re (Mg)*B_j(Mg) / Re (Mg)*D(Mg))_j) - E Φ((Re (M₀g)*B_j(M₀g) / Re (M₀g)*D(M₀g))_j)| ≤ ε`
(ratios clamped to the cube by `ratioCube`), `g ~ CN(0, I_N)`. `ω₀` depends only on `k, Φ, ε`. -/
theorem clockCovarianceStability_cube (k : ℕ) (Φ : C(Fin k → Set.Icc (-1 : ℝ) 1, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ω₀ : ℝ, 0 < ω₀ ∧
    ∀ (N : ℕ) (Γ₀ Γ : Matrix (Fin N) (Fin N) ℂ) (ω : ℝ), 0 ≤ ω → ω ≤ ω₀ → Γ₀.PosSemidef →
      (((1 + ω : ℝ) : ℂ) • Γ₀ - Γ).PosSemidef → (Γ - ((1 - ω : ℝ) : ℂ) • Γ₀).PosSemidef →
    ∀ (D : Matrix (Fin N) (Fin N) ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ), D.PosSemidef →
      (∀ j, IsSandwiched (B j) D) → 0 < traceAgainst Γ₀ D →
    ∀ M M₀ : Matrix (Fin N) (Fin N) ℂ, M * Mᴴ = Γ → M₀ * M₀ᴴ = Γ₀ →
    ∀ d : (Fin N → ℂ) → Fin k → ℝ, Measurable d →
      |(∫ g, Φ (ratioCube B D d (M *ᵥ g)) ∂circularVectorLaw (Fin N)) -
          ∫ g, Φ (ratioCube B D d (M₀ *ᵥ g)) ∂circularVectorLaw (Fin N)| ≤ ε := by
  set ψ : ℝ → (Fin (k + 1) → ℝ) → ℝ := fun u x =>
    Φ (fun j => Set.projIcc (-1 : ℝ) 1 (by norm_num) (x j.succ / max (x 0) u - 1))
  have hψc : ∀ u, 0 < u → Continuous (ψ u) := fun u hu => Φ.continuous.comp
    (continuous_pi fun j => continuous_projIcc.comp (((continuous_apply j.succ).div
      ((continuous_apply 0).max continuous_const)
      fun x => (lt_of_lt_of_le hu (le_max_right _ _)).ne').sub continuous_const))
  have hψM : ∀ u x, |ψ u x| ≤ ‖Φ‖ := fun u x => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  obtain ⟨ω₀, hω₀, hrat⟩ := ratio_comparison k ψ hψc hψM 2 hε
  refine ⟨ω₀, hω₀, ?_⟩
  intro N Γ₀ Γ ω hω0 hω _hΓ₀ h1 h2 D B hD hB hT M M₀ hMM hMM₀ d hd
  set P : Fin (k + 1) → Matrix (Fin N) (Fin N) ℂ := Fin.cons D (fun j => D + B j)
  have hP0 : P 0 = D := rfl
  have hPs : ∀ j, P j.succ = D + B j := fun j => rfl
  have hP : ∀ i, (P i).PosSemidef := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hP0]; exact hD
    · rw [hPs]; exact (hB j).2.2
  have hPK : ∀ i, traceAgainst Γ₀ (P i) ≤ 2 * traceAgainst Γ₀ (P 0) := by
    intro i
    rw [hP0]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hP0]; linarith
    · rw [hPs, traceAgainst_add]
      have h0 := traceAgainst_nonneg_of hMM₀ (hB j).2.1
      rw [traceAgainst_sub] at h0
      linarith
  have hGm : Measurable (fun v => Φ (ratioCube B D d v)) := by
    refine Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun j => ?_)
    refine continuous_projIcc.measurable.comp ?_
    exact Measurable.ite (measurableSet_eq_fun (CommonPortRatios.measurable_quadForm_left D)
      measurable_const) ((measurable_pi_apply j).comp hd)
      ((CommonPortRatios.measurable_quadForm_left (B j)).div
        (CommonPortRatios.measurable_quadForm_left D))
  have hGM : ∀ v, |Φ (ratioCube B D d v)| ≤ ‖Φ‖ := fun v => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  refine hrat N Γ₀ Γ ω hω0 hω h1 h2 P hP (by rw [hP0]; exact hT) hPK M M₀ hMM hMM₀ _ hGm hGM ?_
  intro u hu v s hs hus
  rw [hP0] at hus
  have hq0 : quadForm D v ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hus
    linarith
  simp only [ψ]
  congr 1
  funext j
  simp only [ratioCube, hq0, ↓reduceIte]
  rw [hPs, hP0, max_eq_left hus, CommonPortRatios.quadForm_add]
  congr 1
  field_simp
  ring

end BlockBand.Endpoints.Clock
