module

public import BlockBand.Transmission.Generator.StepExact
public import BlockBand.Transmission.PassiveCovariance.DressedTrace
public import BlockBand.Transmission.PassiveCovariance.MainTerm
public import BlockBand.Transmission.PassiveCovariance.LayerBlocks

/-!
# The expected second-order expansion of `Tr S^k` (one layer, abstract law)

**`step_quad`**: if `‖S‖ ≤ 1` a.s., `‖S̄‖ ≤ 1`, `E‖B‖²_HS ≤ H₂`, `E‖B‖‖B‖²_HS ≤ H₃` and the
covariance of `U` has the shape of the passive covariance lemma with error `ε`, then
`|E Re Tr S^k - Re Tr S̄^k - Re Σ c^j w_{im}(a(2-t_i-t_m) + σf'_{ii}f'_{mm} + σ'…)| ≤
 k³6^{2k}H₃ + k²·3(k-1)2^{3(k-1)}‖S̄ - D'‖H₂ + |c|^jεΣw_{im}`.
The linear term has mean zero (`integral_trace_mul_sand_centered`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {T : Matrix (Fin W) (Fin W) ℂ}

theorem trace_mul_sand (hT : T.PosSemidef) (X Z : Matrix (Fin W) (Fin W) ℂ) :
    (X * sand hT Z).trace = ∑ i, ∑ m, X i m *
      (((Real.sqrt (ts_lam hT m) * Real.sqrt (ts_lam hT i) : ℝ) : ℂ) * ts_ent hT Z m i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sand_apply]

theorem integrable_cre {g : Ω → ℂ} (hg : Integrable g μ) : Integrable (fun ω => (g ω).re) μ :=
  hg.re

theorem integral_cre {g : Ω → ℂ} (hg : Integrable g μ) : ∫ ω, (g ω).re ∂μ = (∫ ω, g ω ∂μ).re :=
  integral_re hg

theorem integrable_ts_ent_centered [IsFiniteMeasure μ] (hT : T.PosSemidef) (U : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ) (i m : Fin W) :
    Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i m) μ := by
  simp only [ts_ent, bilinear_sub]
  exact (integrable_bilinear U hUi _ _).sub (integrable_const _)

theorem integral_ts_ent_centered [IsProbabilityMeasure μ] (hT : T.PosSemidef)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (i m : Fin W) : ∫ ω, ts_ent hT (U ω - matrixExpect μ U) i m ∂μ = 0 := by
  simp only [ts_ent, bilinear_sub]
  rw [integral_sub (integrable_bilinear U hUi _ _) (integrable_const _), integral_const,
    ← bilinear_matrixExpect U _ _ hUi]
  simp

/-- **The linear term has mean zero.** -/
theorem integral_trace_mul_sand_centered [IsProbabilityMeasure μ] (hT : T.PosSemidef)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (X : Matrix (Fin W) (Fin W) ℂ) :
    Integrable (fun ω => (X * sand hT (U ω - matrixExpect μ U)).trace) μ ∧
      ∫ ω, (X * sand hT (U ω - matrixExpect μ U)).trace ∂μ = 0 := by
  simp only [trace_mul_sand]
  have hI : ∀ i m, Integrable (fun ω => X i m * (((Real.sqrt (ts_lam hT m) *
      Real.sqrt (ts_lam hT i) : ℝ) : ℂ) * ts_ent hT (U ω - matrixExpect μ U) m i)) μ :=
    fun i m => ((integrable_ts_ent_centered hT U hUi m i).const_mul _).const_mul _
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hI i m, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hI i m]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun m _ => hI i m]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_ts_ent_centered hT U hUi, mul_zero,
    mul_zero]

theorem norm_trace_le_card (M : Matrix (Fin W) (Fin W) ℂ) : ‖M.trace‖ ≤ ‖M‖ * W := by
  have h := norm_trace_mul_posSemidef_le Matrix.PosSemidef.one M
  rw [Matrix.mul_one, Matrix.trace_one, Fintype.card_fin] at h
  simpa using h

theorem continuous_sand (hT : T.PosSemidef) : Continuous (sand hT) := by
  unfold sand
  exact (continuous_const.matrix_mul ((continuous_const.matrix_mul continuous_id).matrix_mul
    continuous_const)).matrix_mul continuous_const

/-- **Expected second-order expansion.** -/
theorem step_quad [IsProbabilityMeasure μ] (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) (hUm : Measurable U)
    (hUi : ∀ i j, Integrable (fun ω => U ω i j) μ)
    (hp : ∀ i m, Integrable (fun ω => ts_ent hT (U ω - matrixExpect μ U) i m *
      ts_ent hT (U ω - matrixExpect μ U) m i) μ)
    (hS : ∀ᵐ ω ∂μ, ‖sand hT (U ω)‖ ≤ 1) (hSb : ‖sand hT (matrixExpect μ U)‖ ≤ 1)
    {H₂ H₃ : ℝ} (hI2 : Integrable (fun ω => frobSq (sand hT (U ω - matrixExpect μ U))) μ)
    (h2 : ∫ ω, frobSq (sand hT (U ω - matrixExpect μ U)) ∂μ ≤ H₂)
    (hI3 : Integrable (fun ω => ‖sand hT (U ω - matrixExpect μ U)‖ *
      frobSq (sand hT (U ω - matrixExpect μ U))) μ)
    (h3 : ∫ ω, ‖sand hT (U ω - matrixExpect μ U)‖ *
      frobSq (sand hT (U ω - matrixExpect μ U)) ∂μ ≤ H₃)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (f : Matrix (Fin W) (Fin W) ℂ) (a σ σ' : ℂ) {ε : ℝ}
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance μ U v₁ v₂ v₃ v₄ -
      (a * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - T) + crossedTensor v₁ v₂ v₃ v₄ (1 - T) 1) +
        σ * crossedTensor v₁ v₂ v₃ v₄ f f + σ' * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
      ε * fourNorm v₁ v₂ v₃ v₄) (j : ℕ) :
    |∫ ω, ((sand hT (U ω)) ^ (j + 2)).trace.re ∂μ -
        ((sand hT (matrixExpect μ U)) ^ (j + 2)).trace.re -
        (∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * (((ts_lam hT i * ts_lam hT m *
          wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
          (a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) +
            σ * (ts_ent hT f i i * ts_ent hT f m m) +
            σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))))).re| ≤
      ((j + 1 + 1 : ℕ) : ℝ) ^ 3 * (3 * 2) ^ (2 * (j + 1 + 1)) * H₃ +
        ((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) * (3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1)) *
          ‖sand hT (matrixExpect μ U) - diagonal (fun i => ((c * ts_lam hT i : ℝ) : ℂ))‖)) * H₂ +
        |c| ^ j * ε * ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * wsum j (ts_lam hT i) (ts_lam hT m) := by
  set A := sand hT (matrixExpect μ U)
  set B : Ω → Matrix (Fin W) (Fin W) ℂ := fun ω => sand hT (U ω - matrixExpect μ U)
  set D' := diagonal (fun i => ((c * ts_lam hT i : ℝ) : ℂ))
  set K₁ := ((j + 1 + 1 : ℕ) : ℝ) ^ 3 * (3 * 2) ^ (2 * (j + 1 + 1))
  set K₂ := ((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) * (3 * (j + 1 : ℕ) *
    2 ^ (3 * (j + 1)) * ‖A - D'‖))
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have hSAB : ∀ ω, sand hT (U ω) = A + B ω := fun ω => by
    simp only [A, B, sand_sub]; abel
  have hD'1 : ‖D'‖ ≤ 1 := norm_diagonal_le (c := (1 : ℝ)) _ zero_le_one fun i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hc0 (ts_lam_nonneg hT i))]
    nlinarith [ts_lam_nonneg hT i, ht1 i]
  have hD' : ‖D'‖ ≤ 2 := hD'1.trans (by norm_num)
  have hA2 : ‖A‖ ≤ 2 := hSb.trans (by norm_num)
  -- the four integrands
  set F0 : Ω → ℝ := fun ω => ((sand hT (U ω)) ^ (j + 2)).trace.re
  set F1 : Ω → ℂ := fun ω => (A ^ (j + 1) * B ω).trace
  set F2 : Ω → ℂ := fun ω => (pF2 D' (B ω) (j + 2)).trace
  have hF0m : AEStronglyMeasurable F0 μ := by
    have hc : Continuous fun Z : Matrix (Fin W) (Fin W) ℂ => ((sand hT Z) ^ (j + 2)).trace.re :=
      Complex.continuous_re.comp (((continuous_sand hT).pow _).matrix_trace)
    exact (hc.measurable.comp hUm).aestronglyMeasurable
  have hF0 : Integrable F0 μ := by
    refine Integrable.of_bound hF0m (W : ℝ) ?_
    filter_upwards [hS] with ω hω
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ((norm_trace_le_card _).trans ?_)
    have : ‖sand hT (U ω) ^ (j + 2)‖ ≤ 1 :=
      (norm_pow_le' _ (by omega)).trans (pow_le_one₀ (norm_nonneg _) hω)
    nlinarith [Nat.cast_nonneg (α := ℝ) W]
  obtain ⟨hF1, hF1z⟩ := integral_trace_mul_sand_centered hT U hUi (A ^ (j + 1))
  have hF2e : ∀ ω, F2 ω = ∑ i, ∑ m, ((ts_lam hT i * ts_lam hT m : ℝ) : ℂ) *
      (ts_ent hT (U ω - matrixExpect μ U) i m * ts_ent hT (U ω - matrixExpect μ U) m i) *
      wsum j (((c * ts_lam hT i : ℝ) : ℂ)) (((c * ts_lam hT m : ℝ) : ℂ)) := fun ω => by
    show (pF2 (diagonal fun i => ((c * ts_lam hT i : ℝ) : ℂ)) (sand hT (U ω - matrixExpect μ U))
      (j + 2)).trace = _
    rw [trace_pF2_diag]
    simp only [sand_mul_sand]
  have hF2 : Integrable F2 μ := by
    rw [show F2 = fun ω => _ from funext hF2e]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ =>
      ((hp i m).const_mul _).mul_const _
  -- the remainder
  set G : Ω → ℝ := fun ω => F0 ω - (A ^ (j + 2)).trace.re - ((j + 2 : ℕ) : ℝ) * (F1 ω).re -
    (F2 ω).re
  have hG : Integrable G μ :=
    ((hF0.sub (integrable_const _)).sub ((integrable_cre hF1).const_mul _)).sub
      (integrable_cre hF2)
  have hGb : ∀ᵐ ω ∂μ, |G ω| ≤ K₁ * (‖B ω‖ * frobSq (B ω)) + K₂ * frobSq (B ω) := by
    filter_upwards [hS] with ω hω
    have hB2 : ‖B ω‖ ≤ 2 := by
      have : B ω = sand hT (U ω) - A := by rw [hSAB]; abel
      rw [this]; exact (norm_sub_le _ _).trans (by linarith)
    have e1 := pe_second hA2 hB2 (by norm_num : (1 : ℝ) ≤ 2) (j + 1)
    have e2 := pe_pF2_sub hA2 hD' (by norm_num : (1 : ℝ) ≤ 2) (B := B ω) (j + 1)
    have hGe : G ω = (((A + B ω) ^ (j + 1 + 1)).trace - (A ^ (j + 1 + 1)).trace -
        ((j + 1 + 1 : ℕ) : ℂ) * (A ^ (j + 1) * B ω).trace - (pF2 A (B ω) (j + 1 + 1)).trace).re +
        ((pF2 A (B ω) (j + 1 + 1)).trace - (pF2 D' (B ω) (j + 1 + 1)).trace).re := by
      simp only [G, F0, F1, F2, hSAB, Complex.sub_re]
      rw [show ((j + 1 + 1 : ℕ) : ℂ) = (((j + 2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul]
      ring
    have t1 := (Complex.abs_re_le_norm _).trans e1
    have t2 := (Complex.abs_re_le_norm _).trans e2
    have q1 : K₁ * (‖B ω‖ * frobSq (B ω)) = ((j + 1 + 1 : ℕ) : ℝ) ^ 3 *
        (3 * 2) ^ (2 * (j + 1 + 1)) * ‖B ω‖ * frobSq (B ω) := by simp only [K₁]; ring
    have q2 : K₂ * frobSq (B ω) = ((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) *
        (3 * ((j + 1 : ℕ) : ℝ) * 2 ^ (3 * (j + 1)) * ‖A - D'‖ * frobSq (B ω))) := by
      simp only [K₂]; ring
    rw [hGe]
    have := abs_add_le (((A + B ω) ^ (j + 1 + 1)).trace - (A ^ (j + 1 + 1)).trace -
        ((j + 1 + 1 : ℕ) : ℂ) * (A ^ (j + 1) * B ω).trace - (pF2 A (B ω) (j + 1 + 1)).trace).re
      ((pF2 A (B ω) (j + 1 + 1)).trace - (pF2 D' (B ω) (j + 1 + 1)).trace).re
    linarith
  -- assemble
  have hint : ∫ ω, F0 ω ∂μ = (A ^ (j + 2)).trace.re + (∫ ω, F2 ω ∂μ).re + ∫ ω, G ω ∂μ := by
    have e : ∀ ω, F0 ω = (A ^ (j + 2)).trace.re + ((j + 2 : ℕ) : ℝ) * (F1 ω).re + (F2 ω).re +
        G ω := fun ω => by simp only [G]; ring
    simp_rw [e]
    have i1 : Integrable (fun ω => (F1 ω).re) μ := integrable_cre hF1
    have i2 : Integrable (fun ω => (F2 ω).re) μ := integrable_cre hF2
    have j0 : Integrable (fun ω => (A ^ (j + 2)).trace.re + ((j + 2 : ℕ) : ℝ) * (F1 ω).re) μ :=
      (integrable_const _).add (i1.const_mul _)
    have j1 : Integrable (fun ω => (A ^ (j + 2)).trace.re + ((j + 2 : ℕ) : ℝ) * (F1 ω).re +
        (F2 ω).re) μ := j0.add i2
    have j2 : Integrable (fun ω => ((j + 2 : ℕ) : ℝ) * (F1 ω).re) μ := i1.const_mul _
    rw [integral_add j1 hG, integral_add j0 i2, integral_add (integrable_const _) j2,
      integral_const, integral_const_mul,
      integral_cre hF1, hF1z, integral_cre hF2]
    simp
  have hGint : |∫ ω, G ω ∂μ| ≤ K₁ * H₃ + K₂ * H₂ := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |G ω| ∂μ ≤ ∫ ω, (K₁ * (‖B ω‖ * frobSq (B ω)) + K₂ * frobSq (B ω)) ∂μ :=
          integral_mono_ae hG.abs ((hI3.const_mul _).add (hI2.const_mul _)) hGb
      _ = K₁ * ∫ ω, ‖B ω‖ * frobSq (B ω) ∂μ + K₂ * ∫ ω, frobSq (B ω) ∂μ := by
          rw [integral_add (hI3.const_mul _) (hI2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ K₁ * H₃ + K₂ * H₂ := add_le_add (mul_le_mul_of_nonneg_left h3 hK₁)
          (mul_le_mul_of_nonneg_left h2 hK₂)
  have hq := quad_contract hT U hp f a σ σ' hcov c j
  have hF2q : |(∫ ω, F2 ω ∂μ).re - (∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * (((ts_lam hT i * ts_lam hT m *
      wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) * (a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) +
      σ * (ts_ent hT f i i * ts_ent hT f m m) +
      σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))))).re| ≤
      |c| ^ j * ε * ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * wsum j (ts_lam hT i) (ts_lam hT m) := by
    rw [← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans hq
  rw [hint]
  have : (A ^ (j + 2)).trace.re + (∫ ω, F2 ω ∂μ).re + ∫ ω, G ω ∂μ - (A ^ (j + 2)).trace.re -
      (∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * (((ts_lam hT i * ts_lam hT m *
        wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
        (a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) + σ * (ts_ent hT f i i * ts_ent hT f m m) +
          σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))))).re =
      ((∫ ω, F2 ω ∂μ).re - (∑ i, ∑ m, ((c ^ j : ℝ) : ℂ) * (((ts_lam hT i * ts_lam hT m *
        wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
        (a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) + σ * (ts_ent hT f i i * ts_ent hT f m m) +
          σ' * (conj (ts_ent hT f i i) * conj (ts_ent hT f m m))))).re) + ∫ ω, G ω ∂μ := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  linarith

end BlockBand.Transmission.Generator
