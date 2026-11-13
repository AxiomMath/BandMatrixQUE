module

public import BlockBand.SourceProcess.SmallLeak.FluxMean
public import BlockBand.SourceProcess.ContractingWords.SlotMom

/-!
# The bilinear variance of the fresh layer in Hilbert–Schmidt form

In the paper, for positive old `X`, the bilinear variance of `Δ` gives
`E_jΔXΔ* ⪯ C[Tr X/W + δ₀²‖X‖]I`. Here, for deterministic `U, V` and a random `Δ` with
`‖EΔ‖ ≤ m` and bilinear fluctuations `‖u*(Δ - EΔ)v‖_{L²} ≤ σ‖u‖‖v‖`:
`E‖UΔV‖₂² ≤ 2(m² + σ²)‖U‖₂²‖V‖₂²` (`integral_hsNorm_sq_le`). With `σ = C_f(W^{-1/2} + δ₀)`
(`RawTag.delta_fresh_bounds`) this is the paper's bound paired with a positive `Q = R*R`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops BlockBand.SourceProcess.ContractingWords
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ComplexConjugate ENNReal

variable {W : ℕ} {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- The row `c` of `U`, conjugated, as a bilinear-form vector. -/
def rowVec (U : Matrix κ (Fin W) ℂ) (c : κ) : Fin W → ℂ := fun x => conj (U c x)

omit [Fintype κ] [Fintype ι] in
theorem mul_mul_apply_eq_bilinear (U : Matrix κ (Fin W) ℂ) (D : Matrix (Fin W) (Fin W) ℂ)
    (V : Matrix (Fin W) ι ℂ) (c : κ) (k : ι) :
    (U * D * V) c k = bilinear (rowVec U c) D (fun y => V y k) := by
  simp only [bilinear, dotProduct, mulVec, Matrix.mul_apply, rowVec, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem vecNorm_sq_eq_sum {n : Type*} [Fintype n] (v : n → ℂ) :
    vecNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [vecNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]

theorem sum_vecNorm_rowVec (U : Matrix κ (Fin W) ℂ) :
    ∑ c, vecNorm (rowVec U c) ^ 2 = hsNorm U ^ 2 := by
  rw [hsNorm_sq]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [vecNorm_sq_eq_sum]
  simp [rowVec]

theorem sum_vecNorm_col (V : Matrix (Fin W) ι ℂ) :
    ∑ k, vecNorm (fun y => V y k) ^ 2 = hsNorm V ^ 2 := by
  rw [hsNorm_sq, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => vecNorm_sq_eq_sum _

theorem bilinear_add (u : Fin W → ℂ) (A B : Matrix (Fin W) (Fin W) ℂ) (v : Fin W → ℂ) :
    bilinear u (A + B) v = bilinear u A v + bilinear u B v := by
  rw [bilinear, bilinear, bilinear, add_mulVec, dotProduct_add]

theorem norm_add_sq_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]

/-- **`E‖UΔV‖₂² ≤ 2(m² + σ²)‖U‖₂²‖V‖₂²`.** -/
theorem integral_hsNorm_sq_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Δ : Ω → Matrix (Fin W) (Fin W) ℂ) (hmeas : Measurable Δ)
    (U : Matrix κ (Fin W) ℂ) (V : Matrix (Fin W) ι ℂ) {m σ : ℝ} (hσ : 0 ≤ σ)
    (hm : ‖matrixExpect μ Δ‖ ≤ m)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Δ ω - matrixExpect μ Δ) v)
      (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal (σ * vecNorm u * vecNorm v)) :
    ∫ ω, hsNorm (U * Δ ω * V) ^ 2 ∂μ ≤ 2 * (m ^ 2 + σ ^ 2) * hsNorm U ^ 2 * hsNorm V ^ 2 := by
  set D := matrixExpect μ Δ
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
  set u := rowVec U
  set v : ι → Fin W → ℂ := fun k y => V y k
  set e : ι → κ → Ω → ℂ := fun k c ω => bilinear (u c) (Δ ω - D) (v k)
  have hmom : ∀ k c, Integrable (fun ω => ‖e k c ω‖ ^ 2) μ ∧
      ∫ ω, ‖e k c ω‖ ^ 2 ∂μ ≤ (σ * vecNorm (u c) * vecNorm (v k)) ^ 2 := by
    intro k c
    have hme : AEStronglyMeasurable (e k c) μ := by
      have : Measurable fun ω => bilinear (u c) (Δ ω - D) (v k) := by
        simp only [bilinear, dotProduct, mulVec]
        refine Finset.measurable_sum _ fun x _ => measurable_const.mul
          (Finset.measurable_sum _ fun y _ => ?_)
        exact ((hmeas.eval_matrix.sub measurable_const).mul measurable_const)
      exact this.aestronglyMeasurable
    have hb : eLpNorm (e k c) ((2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal (σ * vecNorm (u c) * vecNorm (v k)) := by
      have := hfl (u c) (v k)
      simpa using this
    have hβ : 0 ≤ σ * vecNorm (u c) * vecNorm (v k) :=
      mul_nonneg (mul_nonneg hσ (vecNorm_nonneg _)) (vecNorm_nonneg _)
    exact moments_of_eLpNorm hme hβ hb 2 (by norm_num) le_rfl
  -- pointwise
  have hpt : ∀ ω, hsNorm (U * Δ ω * V) ^ 2 ≤
      ∑ c, ∑ k, (2 * ‖(U * D * V) c k‖ ^ 2 + 2 * ‖e k c ω‖ ^ 2) := by
    intro ω
    rw [hsNorm_sq]
    refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun k _ => ?_
    have hsplit : (U * Δ ω * V) c k = (U * D * V) c k + e k c ω := by
      rw [mul_mul_apply_eq_bilinear, mul_mul_apply_eq_bilinear, ← bilinear_add]
      simp [D]
    rw [hsplit]
    exact norm_add_sq_le _ _
  have hIk : ∀ c k, Integrable (fun ω => 2 * ‖(U * D * V) c k‖ ^ 2 + 2 * ‖e k c ω‖ ^ 2) μ :=
    fun c k => (integrable_const _).add ((hmom k c).1.const_mul 2)
  have hIc : ∀ c, Integrable (fun ω => ∑ k, (2 * ‖(U * D * V) c k‖ ^ 2 + 2 * ‖e k c ω‖ ^ 2)) μ :=
    fun c => integrable_finsetSum _ fun k _ => hIk c k
  have hRI : Integrable (fun ω => ∑ c, ∑ k, (2 * ‖(U * D * V) c k‖ ^ 2 + 2 * ‖e k c ω‖ ^ 2)) μ :=
    integrable_finsetSum _ fun c _ => hIc c
  have hRint : ∫ ω, (∑ c, ∑ k, (2 * ‖(U * D * V) c k‖ ^ 2 + 2 * ‖e k c ω‖ ^ 2)) ∂μ ≤
      2 * (m ^ 2 + σ ^ 2) * hsNorm U ^ 2 * hsNorm V ^ 2 := by
    rw [integral_finsetSum _ fun c _ => hIc c]
    have h1 : ∀ c, ∫ ω, (∑ k, (2 * ‖(U * D * V) c k‖ ^ 2 + 2 * ‖e k c ω‖ ^ 2)) ∂μ ≤
        ∑ k, (2 * ‖(U * D * V) c k‖ ^ 2 +
          2 * (σ * vecNorm (u c) * vecNorm (v k)) ^ 2) := by
      intro c
      rw [integral_finsetSum _ fun k _ => hIk c k]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [integral_add (integrable_const _) ((hmom k c).1.const_mul 2), integral_const,
        integral_const_mul]
      simp only [probReal_univ, one_smul]
      linarith [(hmom k c).2]
    refine (Finset.sum_le_sum fun c _ => h1 c).trans ?_
    simp only [Finset.sum_add_distrib]
    have hA : ∑ c, ∑ k, 2 * ‖(U * D * V) c k‖ ^ 2 = 2 * hsNorm (U * D * V) ^ 2 := by
      rw [hsNorm_sq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
    have hUDV : hsNorm (U * D * V) ≤ hsNorm U * (m * hsNorm V) := by
      rw [Matrix.mul_assoc]
      refine (hsNorm_mul_le U (D * V)).trans (mul_le_mul_of_nonneg_left ?_ (hsNorm_nonneg _))
      exact (hsNorm_mul_le_opNorm D V).trans (mul_le_mul_of_nonneg_right hm (hsNorm_nonneg _))
    have hA' : 2 * hsNorm (U * D * V) ^ 2 ≤ 2 * m ^ 2 * hsNorm U ^ 2 * hsNorm V ^ 2 := by
      have := pow_le_pow_left₀ (hsNorm_nonneg _) hUDV 2
      nlinarith
    have hB : ∑ c, ∑ k, 2 * (σ * vecNorm (u c) * vecNorm (v k)) ^ 2 =
        2 * σ ^ 2 * (∑ c, vecNorm (u c) ^ 2) * ∑ k, vecNorm (v k) ^ 2 := by
      have e : ∀ c k, 2 * (σ * vecNorm (u c) * vecNorm (v k)) ^ 2 =
          (2 * σ ^ 2 * vecNorm (u c) ^ 2) * vecNorm (v k) ^ 2 := fun c k => by ring
      simp only [e, ← Finset.mul_sum, ← Finset.sum_mul]
    have hu : ∑ c, vecNorm (u c) ^ 2 = hsNorm U ^ 2 := sum_vecNorm_rowVec U
    have hv : ∑ k, vecNorm (v k) ^ 2 = hsNorm V ^ 2 := sum_vecNorm_col V
    rw [hA, hB, hu, hv]
    nlinarith
  by_cases hI : Integrable (fun ω => hsNorm (U * Δ ω * V) ^ 2) μ
  · exact (integral_mono hI hRI hpt).trans hRint
  · rw [integral_undef hI]; positivity

end BlockBand.SourceProcess.SmallLeak
