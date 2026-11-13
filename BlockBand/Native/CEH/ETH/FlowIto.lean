module

public import BlockBand.Native.CEH.ETH.FlowItoCalc
public import BlockBand.Native.CEH.Flow.ResolventIto

/-!
# CEH ETH: Itô formula for two-resolvent chains along the characteristic flow

* drift `1_{t ≤ s} · Re tr(K D_t)`,
  `D = (⟨R₁⟩ - m₁) R₁² A R₂ + (⟨R₂⟩ - m₂) R₁ A R₂² + ⟨R₁ A R₂⟩ R₁ R₂`; the last term contributes
  `Re(⟨R₁AR₂⟩ tr(R₂KR₁)) = Re(N ⟨R₁AR₂⟩⟨R₂KR₁⟩)` (`reTr_flowDrift2`);
* bracket density `1_{t ≤ s} · (1/N) ∑_x (Re tr(K (R₁E_xR₁AR₂ + R₁AR₂E_xR₂)))²`,
  `E_x = hermBasis x`.
After `s` the process is constant (stopped).

Specializations (`K = N⁻¹B`, `K = -iN⁻¹B`): `isContinuousSemimartingale_avgRe2/avgIm2_flowResolvent`
for `Re/Im ⟨R₁AR₂B⟩`, with drift
`Re/Im[(⟨R₁⟩ - m₁)⟨R₁²AR₂B⟩ + (⟨R₂⟩ - m₂)⟨R₁AR₂²B⟩ + ⟨R₁AR₂⟩⟨R₂BR₁⟩]` (plan §2 fact 3) and
bracket `(1/N) ∑_x (Re/Im(⟨R₁E_xR₁AR₂B⟩ + ⟨R₁AR₂E_xR₂B⟩))²` (fact 4).

* `∂_{E}R_i = -R_i E R_i` and `∂_σ R_i = R_i (∂_σ z_{i,σ}) R_i = -m_i R_i²`;
* first order (time): `-Re tr(K(m₁R₁²AR₂ + m₂R₁AR₂²))`;
* second order: `½ (1/N) ∑_x D²φ[E_x, E_x]`, `D²φ[E, E] = 2 Re tr(K(R₁ER₁ER₁AR₂ + R₁ER₁AR₂ER₂
  + R₁AR₂ER₂ER₂))`; with `∑_x E_x X E_x = tr(X) 1` this is
  `Re tr(K(⟨R₁⟩R₁²AR₂ + ⟨R₁AR₂⟩R₁R₂ + ⟨R₂⟩R₁AR₂²))`.
So for `K = N⁻¹B` the cross term is `⟨R₁AR₂⟩⟨R₁R₂B⟩ = ⟨R₁AR₂⟩⟨R₂BR₁⟩`, with coefficient one,
as in fact 3. Bracket: `(1/N) ∑_x (Dφ[E_x])²`. Checked numerically (N = 3, finite differences of
the generator and of the bracket, random `K, A, H, z_i, m_i`).

**Bracket bounds** (deterministic, all matrices): `sum_reTr2_sq_le`:
`∑_x (Re tr(K(R₁E_xR₁AR₂ + R₁AR₂E_xR₂)))² ≤ Re tr(S Sᴴ)`, `S = R₁AR₂KR₁ + R₂KR₁AR₂`;
`avgRe2_bracket_le`/`avgIm2_bracket_le`:
`(1/N) ∑_x (Re/Im(⟨R₁E_xR₁AR₂B⟩ + ⟨R₁AR₂E_xR₂B⟩))² ≤ N⁻² Re⟨S Sᴴ⟩`, `S = R₁AR₂BR₁ + R₂BR₁AR₂`;
`avgRe2_bracket_le_split`/`avgIm2_bracket_le_split`: `≤ 2N⁻² (Re⟨PPᴴ⟩ + Re⟨QQᴴ⟩)`,
`P = R₁AR₂BR₁`, `Q = R₂BR₁AR₂`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH
open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization BlockBand.Native.CEH.Flow
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {N : ℕ}

/-!
### The two-resolvent test function on the state space
-/

/-- Open domain: both characteristics at the time coordinate are nonreal. -/
def flowDomain2 (N : ℕ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) : Set (Fin (N * N + 1) → ℝ) :=
  flowDomain N z₁ m₁ s ∩ flowDomain N z₂ m₂ s

theorem isOpen_flowDomain2 (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) : IsOpen (flowDomain2 N z₁ m₁ z₂ m₂ s) :=
  (isOpen_flowDomain z₁ m₁ s).inter (isOpen_flowDomain z₂ m₂ s)

/-- The Itô test function `(t, y) ↦ Re tr(K R₁(y) A R₂(y))` (time-independent). -/
def flowTest2 (K A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) :
    ℝ × (Fin (N * N + 1) → ℝ) → ℝ :=
  invTest2 (flowBase N z₁ m₁ s) (flowLin N m₁) (flowBase N z₂ m₂ s) (flowLin N m₂) K A

theorem flowTest2_apply (K A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ)
    (p : ℝ × (Fin (N * N + 1) → ℝ)) :
    flowTest2 K A z₁ m₁ z₂ m₂ s p = reTr K (flowR z₁ m₁ s p.2 * A * flowR z₂ m₂ s p.2) := by
  simp only [flowTest2, invTest2, flowBase_add_flowLin_inv]

theorem flowTest2_contDiffOn (K A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) :
    ContDiffOn ℝ 2 (flowTest2 K A z₁ m₁ z₂ m₂ s) (Set.univ ×ˢ flowDomain2 N z₁ m₁ z₂ m₂ s) :=
  fun p hp => (contDiffAt_invTest2 _ _ _ _ K A (isUnit_flow (z := z₁) (m := m₁) (s := s) hp.2.1 p.1)
    (isUnit_flow (z := z₂) (m := m₂) (s := s) hp.2.2 p.1)).contDiffWithinAt

variable {K A : Matrix (Fin N) (Fin N) ℂ} {z₁ m₁ z₂ m₂ : ℂ} {s : ℝ} {y : Fin (N * N + 1) → ℝ}

theorem partialTime_flowTest2 (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ) :
    partialTime (flowTest2 K A z₁ m₁ z₂ m₂ s) (t, y) = 0 := by
  unfold partialTime flowTest2
  rw [fderiv_invTest2 _ _ _ _ K A (isUnit_flow hy.1 t) (isUnit_flow hy.2 t), flowLin_time,
    flowLin_time]
  simp [reTr]

theorem partialSpace_flowTest2_blk (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ)
    (k : Fin (N * N)) :
    partialSpace (flowTest2 K A z₁ m₁ z₂ m₂ s) (t, y) (finSumFinEquiv (Sum.inl k)) =
      -reTr K (flowR z₁ m₁ s y * hermBasis (finProdFinEquiv.symm k) * flowR z₁ m₁ s y * A *
          flowR z₂ m₂ s y +
        flowR z₁ m₁ s y * A * flowR z₂ m₂ s y * hermBasis (finProdFinEquiv.symm k) *
          flowR z₂ m₂ s y) := by
  unfold partialSpace flowTest2
  rw [fderiv_invTest2 _ _ _ _ K A (isUnit_flow hy.1 t) (isUnit_flow hy.2 t), flowLin_blk,
    flowLin_blk, flowBase_add_flowLin_inv, flowBase_add_flowLin_inv]

theorem partialSpace_flowTest2_last (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ) :
    partialSpace (flowTest2 K A z₁ m₁ z₂ m₂ s) (t, y) (finSumFinEquiv (Sum.inr 0)) =
      -reTr K (flowR z₁ m₁ s y * (m₁ • (1 : Matrix (Fin N) (Fin N) ℂ)) * flowR z₁ m₁ s y * A *
          flowR z₂ m₂ s y +
        flowR z₁ m₁ s y * A * flowR z₂ m₂ s y * (m₂ • (1 : Matrix (Fin N) (Fin N) ℂ)) *
          flowR z₂ m₂ s y) := by
  unfold partialSpace flowTest2
  rw [fderiv_invTest2 _ _ _ _ K A (isUnit_flow hy.1 t) (isUnit_flow hy.2 t), flowLin_last,
    flowLin_last, flowBase_add_flowLin_inv, flowBase_add_flowLin_inv]

theorem partialSpace2_flowTest2_blk (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ)
    (k l : Fin (N * N)) :
    partialSpace2 (flowTest2 K A z₁ m₁ z₂ m₂ s) (t, y) (finSumFinEquiv (Sum.inl k))
        (finSumFinEquiv (Sum.inl l)) =
      reTr K (secondTerm2 (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A
        (hermBasis (finProdFinEquiv.symm k)) (hermBasis (finProdFinEquiv.symm l))
        (hermBasis (finProdFinEquiv.symm k)) (hermBasis (finProdFinEquiv.symm l))) := by
  unfold partialSpace2 flowTest2
  rw [fderiv_fderiv_invTest2 _ _ _ _ K A (isUnit_flow hy.1 t) (isUnit_flow hy.2 t), flowLin_blk,
    flowLin_blk, flowLin_blk, flowLin_blk, flowBase_add_flowLin_inv, flowBase_add_flowLin_inv]

/-!
### Itô drift and bracket of the test function
-/

/-- The Itô contraction of the second-order term:
`∑_x S(E_x, E_x) = 2 (tr R₁ · R₁R₁AR₂ + tr(R₁AR₂) · R₁R₂ + tr R₂ · R₁AR₂R₂)`. -/
theorem sum_secondTerm2_hermBasis (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, secondTerm2 R₁ R₂ A (hermBasis x) (hermBasis x) (hermBasis x) (hermBasis x) =
      (2 : ℂ) • (R₁.trace • (R₁ * R₁ * A * R₂) + (R₁ * A * R₂).trace • (R₁ * R₂) +
        R₂.trace • (R₁ * A * R₂ * R₂)) := by
  have hx : ∀ x, secondTerm2 R₁ R₂ A (hermBasis x) (hermBasis x) (hermBasis x) (hermBasis x) =
      (2 : ℂ) • (R₁ * (hermBasis x * R₁ * hermBasis x) * (R₁ * A * R₂) +
        R₁ * (hermBasis x * (R₁ * A * R₂) * hermBasis x) * R₂ +
        (R₁ * A * R₂) * (hermBasis x * R₂ * hermBasis x) * R₂) := by
    intro x
    rw [two_smul]
    simp only [secondTerm2, Matrix.mul_assoc]
    abel
  rw [Finset.sum_congr rfl fun x _ => hx x, ← Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, sum_mul_hermBasis_mul_mul, sum_mul_hermBasis_mul_mul,
    sum_mul_hermBasis_mul_mul]
  simp only [Matrix.mul_assoc]

/-- The drift matrix `(⟨R₁⟩ - m₁) R₁²AR₂ + (⟨R₂⟩ - m₂) R₁AR₂² + ⟨R₁AR₂⟩ R₁R₂`. -/
def flowDrift2 (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (normalizedTrace R₁ - m₁) • (R₁ * R₁ * A * R₂) + (normalizedTrace R₂ - m₂) • (R₁ * A * R₂ * R₂) +
    normalizedTrace (R₁ * A * R₂) • (R₁ * R₂)

/-- The drift in trace form: `Re tr(K D) = Re[(⟨R₁⟩ - m₁) tr(K R₁²AR₂) + (⟨R₂⟩ - m₂) tr(K R₁AR₂²)
+ ⟨R₁AR₂⟩ tr(R₂KR₁)]`. -/
theorem reTr_flowDrift2 (K R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) :
    reTr K (flowDrift2 R₁ R₂ A m₁ m₂) =
      ((normalizedTrace R₁ - m₁) * trace (K * (R₁ * R₁ * A * R₂)) +
        (normalizedTrace R₂ - m₂) * trace (K * (R₁ * A * R₂ * R₂)) +
        normalizedTrace (R₁ * A * R₂) * trace (R₂ * K * R₁)).re := by
  have e : trace (K * (R₁ * R₂)) = trace (R₂ * K * R₁) := by
    rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  rw [reTr, flowDrift2, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_smul, trace_smul, trace_smul, trace_smul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, e]

/-- **Itô drift** of `Re tr(K R₁ A R₂)` before time `s`. -/
theorem itoDrift_flowTest2 (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ≥0) :
    itoDrift (flowTest2 K A z₁ m₁ z₂ m₂ s) y t (sumVec 0 fun _ => 1) (blockCov (gueCovVec N)) =
      reTr K (flowDrift2 (flowR z₁ m₁ s y) (flowR z₂ m₂ s y) A m₁ m₂) := by
  set R₁ := flowR z₁ m₁ s y
  set R₂ := flowR z₂ m₂ s y
  unfold itoDrift
  rw [partialTime_flowTest2 hy, sum_fin_split, sum_fin_split]
  simp only [sumVec_inl, sumVec_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    one_mul, blockCov_inr, sum_fin_split (fun j => blockCov _ _ j * _), blockCov_inl_inl,
    blockCov_inl_inr, add_zero, gueCovVec_apply, ite_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [partialSpace_flowTest2_last hy]
  simp only [partialSpace2_flowTest2_blk hy]
  have hsum : ∑ k : Fin (N * N), 1 / (N : ℝ) * reTr K (secondTerm2 R₁ R₂ A
      (hermBasis (finProdFinEquiv.symm k)) (hermBasis (finProdFinEquiv.symm k))
      (hermBasis (finProdFinEquiv.symm k)) (hermBasis (finProdFinEquiv.symm k))) =
      1 / (N : ℝ) * (2 * reTr K (R₁.trace • (R₁ * R₁ * A * R₂) +
        (R₁ * A * R₂).trace • (R₁ * R₂) + R₂.trace • (R₁ * A * R₂ * R₂))) := by
    rw [sum_hermBasis_reindex (fun E => 1 / (N : ℝ) * reTr K (secondTerm2 R₁ R₂ A E E E E)),
      ← Finset.mul_sum, ← reTr_sum, sum_secondTerm2_hermBasis,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, reTr_ofReal_smul]
  rw [hsum]
  have e1 : -reTr K (R₁ * (m₁ • (1 : Matrix (Fin N) (Fin N) ℂ)) * R₁ * A * R₂ +
        R₁ * A * R₂ * (m₂ • (1 : Matrix (Fin N) (Fin N) ℂ)) * R₂) +
      1 / 2 * (1 / (N : ℝ) * (2 * reTr K (R₁.trace • (R₁ * R₁ * A * R₂) +
        (R₁ * A * R₂).trace • (R₁ * R₂) + R₂.trace • (R₁ * A * R₂ * R₂)))) =
      reTr K (-(R₁ * (m₁ • (1 : Matrix (Fin N) (Fin N) ℂ)) * R₁ * A * R₂ +
        R₁ * A * R₂ * (m₂ • (1 : Matrix (Fin N) (Fin N) ℂ)) * R₂) +
        ((1 / (N : ℝ) : ℝ) : ℂ) • (R₁.trace • (R₁ * R₁ * A * R₂) +
        (R₁ * A * R₂).trace • (R₁ * R₂) + R₂.trace • (R₁ * A * R₂ * R₂))) := by
    simp only [reTr_add, reTr_neg, reTr_ofReal_smul]; ring
  rw [e1]
  congr 1
  unfold flowDrift2 normalizedTrace
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, sub_smul, smul_add, smul_smul,
    Matrix.mul_assoc]
  push_cast
  rw [one_div]
  abel

/-- **Itô bracket** of `Re tr(K R₁ A R₂)` before time `s`. -/
theorem itoBracket_flowTest2 (hy : y ∈ flowDomain2 N z₁ m₁ z₂ m₂ s) (t : ℝ≥0) :
    itoBracket (flowTest2 K A z₁ m₁ z₂ m₂ s) y t (blockCov (gueCovVec N)) =
      1 / (N : ℝ) * ∑ x, reTr K (flowR z₁ m₁ s y * hermBasis x * flowR z₁ m₁ s y * A *
        flowR z₂ m₂ s y + flowR z₁ m₁ s y * A * flowR z₂ m₂ s y * hermBasis x *
        flowR z₂ m₂ s y) ^ 2 := by
  set R₁ := flowR z₁ m₁ s y
  set R₂ := flowR z₂ m₂ s y
  unfold itoBracket
  rw [sum_fin_split]
  simp only [blockCov_inr, zero_mul, Finset.sum_const_zero, add_zero,
    sum_fin_split (fun j => blockCov _ _ j * _ * _), blockCov_inl_inl, blockCov_inl_inr,
    gueCovVec_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    partialSpace_flowTest2_blk hy]
  rw [sum_hermBasis_reindex (fun E => 1 / (N : ℝ) * -reTr K (R₁ * E * R₁ * A * R₂ +
    R₁ * A * R₂ * E * R₂) * -reTr K (R₁ * E * R₁ * A * R₂ + R₁ * A * R₂ * E * R₂)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-!
### Measurability
-/

theorem continuous_flowShift (z m : ℂ) (s : ℝ) :
    Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) =>
      vecHerm N (flowBlk p.2) - flowSpectral z m s (flowLast p.2) •
        (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hb : Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) => flowBlk p.2 :=
    continuous_pi fun k => (continuous_apply _).comp continuous_snd
  have hs : Continuous fun p : ℝ × (Fin (N * N + 1) → ℝ) =>
      flowSpectral z m s (flowLast p.2) := by
    simp only [flowSpectral, flowLast]
    fun_prop
  exact (continuous_vecHerm.comp hb).sub (hs.smul continuous_const)

theorem measurable_flowR (z m : ℂ) (s : ℝ) :
    Measurable fun p : ℝ × (Fin (N * N + 1) → ℝ) => flowR z m s p.2 :=
  measurable_matrix_inv'.comp (continuous_flowShift z m s).measurable

theorem measurable_flowMatrix_mul {α : Type*} [MeasurableSpace α]
    {f g : α → Matrix (Fin N) (Fin N) ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun p => f p * g p := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hg))

theorem measurable_flowTest2 (K A : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ) (s : ℝ) :
    Measurable (flowTest2 K A z₁ m₁ z₂ m₂ s) := by
  have h : flowTest2 K A z₁ m₁ z₂ m₂ s =
      fun p => reTr K (flowR z₁ m₁ s p.2 * A * flowR z₂ m₂ s p.2) :=
    funext (flowTest2_apply K A z₁ m₁ z₂ m₂ s)
  rw [h]
  exact (continuous_reTr K).measurable.comp (measurable_flowMatrix_mul
    (measurable_flowMatrix_mul (measurable_flowR z₁ m₁ s) measurable_const)
    (measurable_flowR z₂ m₂ s))

/-!
### Averaged functionals
-/

theorem normalizedTrace_add_mul (X Y B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace ((X + Y) * B) = normalizedTrace (X * B) + normalizedTrace (Y * B) := by
  simp only [normalizedTrace_eq, Matrix.add_mul, trace_add, mul_add]

theorem normalizedTrace_bracket2_mul (R₁ R₂ A B E : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace ((R₁ * E * R₁ * A * R₂ + R₁ * A * R₂ * E * R₂) * B) =
      normalizedTrace (R₁ * E * R₁ * A * R₂ * B) + normalizedTrace (R₁ * A * R₂ * E * R₂ * B) :=
  normalizedTrace_add_mul _ _ _

/-- The drift matrix against `B`: `⟨D B⟩ = (⟨R₁⟩ - m₁)⟨R₁²AR₂B⟩ + (⟨R₂⟩ - m₂)⟨R₁AR₂²B⟩
+ ⟨R₁AR₂⟩⟨R₂BR₁⟩`. -/
theorem normalizedTrace_flowDrift2_mul (R₁ R₂ A B : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) :
    normalizedTrace (flowDrift2 R₁ R₂ A m₁ m₂ * B) =
      (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * R₁ * A * R₂ * B) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (R₁ * A * R₂ * R₂ * B) +
        normalizedTrace (R₁ * A * R₂) * normalizedTrace (R₂ * B * R₁) := by
  have e : normalizedTrace (R₁ * R₂ * B) = normalizedTrace (R₂ * B * R₁) := by
    rw [normalizedTrace_eq, normalizedTrace_eq, Matrix.mul_assoc, trace_mul_comm]
  rw [flowDrift2, normalizedTrace_add_mul, normalizedTrace_add_mul, normalizedTrace_smul_mul,
    normalizedTrace_smul_mul, normalizedTrace_smul_mul, e]

/-!
### Bracket bounds
-/

theorem trace_mul_mid (K X E Y : Matrix (Fin N) (Fin N) ℂ) :
    trace (K * (X * E * Y)) = trace (E * (Y * K * X)) := by
  rw [show K * (X * E * Y) = (K * X * E) * Y by simp only [Matrix.mul_assoc], trace_mul_comm,
    show Y * (K * X * E) = (Y * K * X) * E by simp only [Matrix.mul_assoc], trace_mul_comm]

/-- The bracket functional in basis form: `Re tr(K(R₁ER₁AR₂ + R₁AR₂ER₂)) = Re tr(E S)`,
`S = R₁AR₂KR₁ + R₂KR₁AR₂`. -/
theorem reTr2_basis (K A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) (x : Fin N × Fin N) :
    reTr K (R₁ * hermBasis x * R₁ * A * R₂ + R₁ * A * R₂ * hermBasis x * R₂) =
      (trace (hermBasis x * (R₁ * A * R₂ * K * R₁ + R₂ * K * R₁ * A * R₂))).re := by
  have h1 : trace (K * (R₁ * hermBasis x * R₁ * A * R₂)) =
      trace (hermBasis x * (R₁ * A * R₂ * K * R₁)) := by
    rw [show R₁ * hermBasis x * R₁ * A * R₂ = R₁ * hermBasis x * (R₁ * A * R₂) by
      simp only [Matrix.mul_assoc], trace_mul_mid]
  have h2 : trace (K * (R₁ * A * R₂ * hermBasis x * R₂)) =
      trace (hermBasis x * (R₂ * K * R₁ * A * R₂)) := by
    rw [trace_mul_mid]
    simp only [Matrix.mul_assoc]
  rw [reTr, Matrix.mul_add, trace_add, h1, h2, Matrix.mul_add, trace_add]

/-- General two-resolvent bracket bound:
`∑_x (Re tr(K(R₁E_xR₁AR₂ + R₁AR₂E_xR₂)))² ≤ Re tr(S Sᴴ)`, `S = R₁AR₂KR₁ + R₂KR₁AR₂`. -/
theorem sum_reTr2_sq_le (K A R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, reTr K (R₁ * hermBasis x * R₁ * A * R₂ + R₁ * A * R₂ * hermBasis x * R₂) ^ 2 ≤
      (trace ((R₁ * A * R₂ * K * R₁ + R₂ * K * R₁ * A * R₂) *
        (R₁ * A * R₂ * K * R₁ + R₂ * K * R₁ * A * R₂)ᴴ)).re := by
  rw [← sum_normSq_trace]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [reTr2_basis, sq]
  exact Complex.re_sq_le_normSq _

theorem re_trace_mul_conjTranspose_nonneg (M : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (trace (M * Mᴴ)).re := by
  rw [← sum_normSq_trace]
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg _

/-- `Re tr((P + Q)(P + Q)ᴴ) ≤ 2 (Re tr(PPᴴ) + Re tr(QQᴴ))`. -/
theorem re_trace_add_mul_conjTranspose_le (P Q : Matrix (Fin N) (Fin N) ℂ) :
    (trace ((P + Q) * (P + Q)ᴴ)).re ≤ 2 * ((trace (P * Pᴴ)).re + (trace (Q * Qᴴ)).re) := by
  have h := re_trace_mul_conjTranspose_nonneg (P - Q)
  have e : (trace ((P + Q) * (P + Q)ᴴ)).re + (trace ((P - Q) * (P - Q)ᴴ)).re =
      2 * ((trace (P * Pᴴ)).re + (trace (Q * Qᴴ)).re) := by
    simp only [conjTranspose_add, conjTranspose_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.sub_mul, Matrix.mul_sub, trace_add, trace_sub, Complex.add_re, Complex.sub_re]
    ring
  linarith

theorem normalizedTrace_re_mul_conjTranspose (M : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (M * Mᴴ)).re = 1 / (N : ℝ) * (trace (M * Mᴴ)).re := by
  rw [normalizedTrace_eq, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    one_div]

/-- **Averaged two-resolvent bracket bound** for a weight `c • B` with `|c|² = N⁻²`. -/
theorem avg2_bracket_le_aux (c : ℂ) (hc : Complex.normSq c = 1 / (N : ℝ) ^ 2)
    (A B R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, reTr (c • B) (R₁ * hermBasis x * R₁ * A * R₂ +
        R₁ * A * R₂ * hermBasis x * R₂) ^ 2 ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂) *
        (R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂)ᴴ)).re := by
  have h := sum_reTr2_sq_le (c • B) A R₁ R₂
  have e : R₁ * A * R₂ * (c • B) * R₁ + R₂ * (c • B) * R₁ * A * R₂ =
      c • (R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [e, trace_smul_mul_conjTranspose, hc] at h
  rw [normalizedTrace_re_mul_conjTranspose]
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  calc _ ≤ 1 / (N : ℝ) * (1 / (N : ℝ) ^ 2 * (trace ((R₁ * A * R₂ * B * R₁ +
          R₂ * B * R₁ * A * R₂) * (R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂)ᴴ)).re) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by ring

theorem normSq_inv_natCast : Complex.normSq ((N : ℂ)⁻¹) = 1 / (N : ℝ) ^ 2 := by
  rw [Complex.normSq_inv, Complex.normSq_natCast, one_div, sq]

theorem normSq_negI_inv_natCast :
    Complex.normSq (-Complex.I * (N : ℂ)⁻¹) = 1 / (N : ℝ) ^ 2 := by
  rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, normSq_inv_natCast]

/-- **Averaged two-resolvent bracket bound** (real part):
`(1/N) ∑_x (Re(⟨R₁E_xR₁AR₂B⟩ + ⟨R₁AR₂E_xR₂B⟩))² ≤ N⁻² Re⟨S Sᴴ⟩`, `S = R₁AR₂BR₁ + R₂BR₁AR₂`. -/
theorem avgRe2_bracket_le (A B R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (R₁ * hermBasis x * R₁ * A * R₂ * B) +
        normalizedTrace (R₁ * A * R₂ * hermBasis x * R₂ * B)).re ^ 2 ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂) *
        (R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂)ᴴ)).re := by
  have h := avg2_bracket_le_aux ((N : ℂ)⁻¹) normSq_inv_natCast A B R₁ R₂
  simp only [reTr_avgRe, normalizedTrace_bracket2_mul] at h
  exact h

/-- **Averaged two-resolvent bracket bound** (imaginary part). -/
theorem avgIm2_bracket_le (A B R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (R₁ * hermBasis x * R₁ * A * R₂ * B) +
        normalizedTrace (R₁ * A * R₂ * hermBasis x * R₂ * B)).im ^ 2 ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂) *
        (R₁ * A * R₂ * B * R₁ + R₂ * B * R₁ * A * R₂)ᴴ)).re := by
  have h := avg2_bracket_le_aux (-Complex.I * (N : ℂ)⁻¹) normSq_negI_inv_natCast A B R₁ R₂
  simp only [reTr_avgIm, normalizedTrace_bracket2_mul] at h
  exact h

theorem normalizedTrace_add_mul_conjTranspose_le (P Q : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((P + Q) * (P + Q)ᴴ)).re ≤
      2 * ((normalizedTrace (P * Pᴴ)).re + (normalizedTrace (Q * Qᴴ)).re) := by
  simp only [normalizedTrace_re_mul_conjTranspose]
  have h := re_trace_add_mul_conjTranspose_le P Q
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  nlinarith

/-- Split form (real part): `≤ 2N⁻² (Re⟨PPᴴ⟩ + Re⟨QQᴴ⟩)`, `P = R₁AR₂BR₁`, `Q = R₂BR₁AR₂`. -/
theorem avgRe2_bracket_le_split (A B R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (R₁ * hermBasis x * R₁ * A * R₂ * B) +
        normalizedTrace (R₁ * A * R₂ * hermBasis x * R₂ * B)).re ^ 2 ≤
      2 / (N : ℝ) ^ 2 * ((normalizedTrace ((R₁ * A * R₂ * B * R₁) * (R₁ * A * R₂ * B * R₁)ᴴ)).re +
        (normalizedTrace ((R₂ * B * R₁ * A * R₂) * (R₂ * B * R₁ * A * R₂)ᴴ)).re) := by
  refine (avgRe2_bracket_le A B R₁ R₂).trans ?_
  have h := normalizedTrace_add_mul_conjTranspose_le (R₁ * A * R₂ * B * R₁) (R₂ * B * R₁ * A * R₂)
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2 := by positivity
  calc _ ≤ 1 / (N : ℝ) ^ 2 * (2 * ((normalizedTrace ((R₁ * A * R₂ * B * R₁) *
          (R₁ * A * R₂ * B * R₁)ᴴ)).re + (normalizedTrace ((R₂ * B * R₁ * A * R₂) *
          (R₂ * B * R₁ * A * R₂)ᴴ)).re)) := mul_le_mul_of_nonneg_left h hN
    _ = _ := by ring

/-- Split form (imaginary part). -/
theorem avgIm2_bracket_le_split (A B R₁ R₂ : Matrix (Fin N) (Fin N) ℂ) :
    1 / (N : ℝ) * ∑ x, (normalizedTrace (R₁ * hermBasis x * R₁ * A * R₂ * B) +
        normalizedTrace (R₁ * A * R₂ * hermBasis x * R₂ * B)).im ^ 2 ≤
      2 / (N : ℝ) ^ 2 * ((normalizedTrace ((R₁ * A * R₂ * B * R₁) * (R₁ * A * R₂ * B * R₁)ᴴ)).re +
        (normalizedTrace ((R₂ * B * R₁ * A * R₂) * (R₂ * B * R₁ * A * R₂)ᴴ)).re) := by
  refine (avgIm2_bracket_le A B R₁ R₂).trans ?_
  have h := normalizedTrace_add_mul_conjTranspose_le (R₁ * A * R₂ * B * R₁) (R₂ * B * R₁ * A * R₂)
  have hN : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2 := by positivity
  calc _ ≤ 1 / (N : ℝ) ^ 2 * (2 * ((normalizedTrace ((R₁ * A * R₂ * B * R₁) *
          (R₁ * A * R₂ * B * R₁)ᴴ)).re + (normalizedTrace ((R₂ * B * R₁ * A * R₂) *
          (R₂ * B * R₁ * A * R₂)ᴴ)).re)) := mul_le_mul_of_nonneg_left h hN
    _ = _ := by ring

/-!
### The stochastic layer
-/

section Stochastic

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Matrix (Fin N) (Fin N) ℂ}

/-- **Itô formula for `Re tr(K R₁ A R₂)` along the characteristic flow**, stopped at `s`.
For a Hermitian Brownian motion `G` (`E|dG_ab|² = dt/N`), deterministic Hermitian `F`, `s ≥ 0`,
nonreal `z_i` and `m_i` with `Im z_i · Im m_i ≥ 0`, and all matrices `K`, `A`, the real process
`t ↦ Re tr(K R_{1,t∧s} A R_{2,t∧s})`, `R_{i,σ} = (F + G_σ - (z_i + (s - σ) m_i))⁻¹`, is a
continuous semimartingale for `𝓖` with drift `1_{t ≤ s} Re tr(K D_t)`,
`D = (⟨R₁⟩ - m₁) R₁²AR₂ + (⟨R₂⟩ - m₂) R₁AR₂² + ⟨R₁AR₂⟩ R₁R₂` (`flowDrift2`, trace form
`reTr_flowDrift2`), and bracket density
`1_{t ≤ s} (1/N) ∑_x (Re tr(K (R₁E_xR₁AR₂ + R₁AR₂E_xR₂)))²` (`E_x = hermBasis x`). -/
theorem isContinuousSemimartingale_reTr_flowResolvent2 (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im)
    (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (s : ℝ≥0) (K A : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => reTr K (flowResolvent F G z₁ m₁ s (min t s) ω * A *
        flowResolvent F G z₂ m₂ s (min t s) ω))
      (fun t ω _ => if t ≤ s then
        reTr K (flowDrift2 (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A
          m₁ m₂) else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, reTr K (flowResolvent F G z₁ m₁ s t ω * hermBasis x *
          flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω +
          flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω * hermBasis x *
          flowResolvent F G z₂ m₂ s t ω) ^ 2 else 0) := by
  set ρ : Ω → WithTop ℝ≥0 := fun _ => (s : WithTop ℝ≥0)
  have hst := BlockBand.SourceProcess.Stochastic.Semimartingale.stoppedSemimartingale_holds
    (N * N + 1) Ω Q 𝓖 _ _ _ (isContinuousSemimartingale_flowState (F := F) hG) ρ
    (isStoppingTime_const 𝓖 _)
  have hU : ∀ t ω, stoppedProcess (flowState F G) ρ t ω ∈ flowDomain2 N z₁ m₁ z₂ m₂ s := by
    intro t ω
    rw [stoppedProcess_flowState]
    have hle := NNReal.coe_le_coe.mpr (min_le_right t s)
    simp only [flowDomain2, flowDomain, Set.mem_inter_iff, Set.mem_ofPred_eq, flowState,
      flowLast_sumVec]
    exact ⟨flowSpectral_im_ne_zero hz₁ hm₁ hle, flowSpectral_im_ne_zero hz₂ hm₂ hle⟩
  have hito := BlockBand.SourceProcess.Stochastic.SemimartingaleIto.semimartingaleItoFormula_holds
    (N * N + 1) Ω Q 𝓖 _ _ _ hst (flowDomain2 N z₁ m₁ z₂ m₂ s) (isOpen_flowDomain2 z₁ m₁ z₂ m₂ s)
    (Eventually.of_forall fun ω t => hU t ω) (flowTest2 K A z₁ m₁ z₂ m₂ s)
    (measurable_flowTest2 K A z₁ m₁ z₂ m₂ s) (flowTest2_contDiffOn K A z₁ m₁ z₂ m₂ s)
  have hsw : ∀ {E : Type} [Zero E] (f : E) (t : ℝ≥0) (ω : Ω),
      switchAfter ρ (fun _ _ => f) t ω = if t ≤ s then f else 0 := by
    intro E _ f t ω
    simp only [switchAfter, ρ, WithTop.coe_le_coe]
  have hR : ∀ (z m : ℂ) t ω, flowR z m s (stoppedProcess (flowState F G) ρ t ω) =
      flowResolvent F G z m s (min t s) ω := by
    intro z m t ω
    rw [stoppedProcess_flowState, flowR_flowState hF hG]
  have e1 : (fun (t : ℝ≥0) ω (_ : Fin 1) => flowTest2 K A z₁ m₁ z₂ m₂ s
      ((t : ℝ), stoppedProcess (flowState F G) ρ t ω)) =
      fun t ω _ => reTr K (flowResolvent F G z₁ m₁ s (min t s) ω * A *
        flowResolvent F G z₂ m₂ s (min t s) ω) := by
    funext t ω i
    rw [flowTest2_apply, hR, hR]
  have e2 : (fun (t : ℝ≥0) ω (_ : Fin 1) => itoDrift (flowTest2 K A z₁ m₁ z₂ m₂ s)
      (stoppedProcess (flowState F G) ρ t ω) t
      (switchAfter ρ (fun _ _ => sumVec 0 fun _ => 1) t ω)
      (switchAfter ρ (fun _ _ => blockCov (e := 1) (gueCovVec N)) t ω)) =
      fun t ω _ => if t ≤ s then
        reTr K (flowDrift2 (flowResolvent F G z₁ m₁ s t ω) (flowResolvent F G z₂ m₂ s t ω) A
          m₁ m₂) else 0 := by
    funext t ω i
    rw [hsw, hsw]
    split_ifs with h
    · rw [itoDrift_flowTest2 (hU t ω), hR, hR, min_eq_left h]
    · simp [itoDrift, partialTime_flowTest2 (hU t ω)]
  have e3 : (fun (t : ℝ≥0) ω => Matrix.of fun (_ _ : Fin 1) =>
      itoBracket (flowTest2 K A z₁ m₁ z₂ m₂ s) (stoppedProcess (flowState F G) ρ t ω) t
      (switchAfter ρ (fun _ _ => blockCov (e := 1) (gueCovVec N)) t ω)) =
      fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, reTr K (flowResolvent F G z₁ m₁ s t ω * hermBasis x *
          flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω +
          flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω * hermBasis x *
          flowResolvent F G z₂ m₂ s t ω) ^ 2 else 0 := by
    funext t ω
    rw [hsw]
    split_ifs with h
    · rw [itoBracket_flowTest2 (hU t ω), hR, hR, min_eq_left h]
    · rw [itoBracket_zero]
  rw [e1, e2, e3] at hito
  exact hito

/-- **Averaged, real part**: `t ↦ Re⟨R_{1,t∧s} A R_{2,t∧s} B⟩` is a continuous semimartingale
with drift `1_{t≤s} Re[(⟨R₁⟩ - m₁)⟨R₁²AR₂B⟩ + (⟨R₂⟩ - m₂)⟨R₁AR₂²B⟩ + ⟨R₁AR₂⟩⟨R₂BR₁⟩]` and
bracket `1_{t≤s} (1/N) ∑_x (Re(⟨R₁E_xR₁AR₂B⟩ + ⟨R₁AR₂E_xR₂B⟩))²` (bounded by
`avgRe2_bracket_le`). -/
theorem isContinuousSemimartingale_avgRe2_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im)
    (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (s : ℝ≥0) (A B : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (normalizedTrace (flowResolvent F G z₁ m₁ s (min t s) ω * A *
        flowResolvent F G z₂ m₂ s (min t s) ω * B)).re)
      (fun t ω _ => if t ≤ s then
        ((normalizedTrace (flowResolvent F G z₁ m₁ s t ω) - m₁) *
            normalizedTrace (flowResolvent F G z₁ m₁ s t ω * flowResolvent F G z₁ m₁ s t ω * A *
              flowResolvent F G z₂ m₂ s t ω * B) +
          (normalizedTrace (flowResolvent F G z₂ m₂ s t ω) - m₂) *
            normalizedTrace (flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω *
              flowResolvent F G z₂ m₂ s t ω * B) +
          normalizedTrace (flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω) *
            normalizedTrace (flowResolvent F G z₂ m₂ s t ω * B *
              flowResolvent F G z₁ m₁ s t ω)).re else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (normalizedTrace (flowResolvent F G z₁ m₁ s t ω * hermBasis x *
            flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω * B) +
          normalizedTrace (flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω *
            hermBasis x * flowResolvent F G z₂ m₂ s t ω * B)).re ^ 2 else 0) := by
  have h := isContinuousSemimartingale_reTr_flowResolvent2 hG hF hz₁ hm₁ hz₂ hm₂ s
    ((N : ℂ)⁻¹ • B) A
  simp only [reTr_avgRe, normalizedTrace_flowDrift2_mul] at h
  simp only [normalizedTrace_bracket2_mul] at h
  exact h

/-- **Averaged, imaginary part**: as `isContinuousSemimartingale_avgRe2_flowResolvent` with `Im`
(bracket bound `avgIm2_bracket_le`). -/
theorem isContinuousSemimartingale_avgIm2_flowResolvent (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : F.IsHermitian) {z₁ m₁ z₂ m₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hm₁ : 0 ≤ z₁.im * m₁.im)
    (hz₂ : z₂.im ≠ 0) (hm₂ : 0 ≤ z₂.im * m₂.im) (s : ℝ≥0) (A B : Matrix (Fin N) (Fin N) ℂ) :
    IsContinuousSemimartingale (d := 1) Q 𝓖
      (fun t ω _ => (normalizedTrace (flowResolvent F G z₁ m₁ s (min t s) ω * A *
        flowResolvent F G z₂ m₂ s (min t s) ω * B)).im)
      (fun t ω _ => if t ≤ s then
        ((normalizedTrace (flowResolvent F G z₁ m₁ s t ω) - m₁) *
            normalizedTrace (flowResolvent F G z₁ m₁ s t ω * flowResolvent F G z₁ m₁ s t ω * A *
              flowResolvent F G z₂ m₂ s t ω * B) +
          (normalizedTrace (flowResolvent F G z₂ m₂ s t ω) - m₂) *
            normalizedTrace (flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω *
              flowResolvent F G z₂ m₂ s t ω * B) +
          normalizedTrace (flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω) *
            normalizedTrace (flowResolvent F G z₂ m₂ s t ω * B *
              flowResolvent F G z₁ m₁ s t ω)).im else 0)
      (fun t ω => Matrix.of fun _ _ => if t ≤ s then
        1 / (N : ℝ) * ∑ x, (normalizedTrace (flowResolvent F G z₁ m₁ s t ω * hermBasis x *
            flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω * B) +
          normalizedTrace (flowResolvent F G z₁ m₁ s t ω * A * flowResolvent F G z₂ m₂ s t ω *
            hermBasis x * flowResolvent F G z₂ m₂ s t ω * B)).im ^ 2 else 0) := by
  have h := isContinuousSemimartingale_reTr_flowResolvent2 hG hF hz₁ hm₁ hz₂ hm₂ s
    ((-Complex.I * (N : ℂ)⁻¹) • B) A
  simp only [reTr_avgIm, normalizedTrace_flowDrift2_mul] at h
  simp only [normalizedTrace_bracket2_mul] at h
  exact h

end Stochastic

end BlockBand.Native.CEH.ETH
