module

public import BlockBand.Layers.TaggedDecayStep
public import BlockBand.Layers.TaggedDecayMeanCore

/-!
# `TdcLayerMean`: the differentiated mean equation of one untagged layer

Part of the proof of the tagged decay bound of the tagged-trace lemma: the ingredients of the
statement `TdcLayerMean` of `TaggedDecayStep`, which is proved by `tdcLayerMean_holds`.

Law: one fresh separate-port layer `μ = layerLaw W b .separate` at `z = z_∂(E)`, conditional on the
deterministic Hermitian old input `X` and the deterministic clock `Y ⪰ 0`; `S = K*YK`, `K = z - X`.
The source family is `X(h) = X - hS` (exactly linear, Hermitian for every real `h`), with the
resolvents `𝒢(h) = layerResolvent .separate E z (X(h))` and the matrix means `Ḡ(h) = E𝒢(h)`
(entrywise, `matrixExpect`).

## Proof ("Differentiate this identity before estimating")

1. **The exact mean identity at every `h`** (`meanEquation_holds`):
   `(𝒟(h) - 𝒮(ḡ(h))) Ḡ(h) = I + Resid(h)`, `𝒟(h) = tflConst(X(h)) = 𝒟(0) + h Ŝ`, `𝒮` the scalar
   self-energy (`tdmShift`, a continuous linear function of `Ḡ`).
2. **Derivatives at `h = 0`**: `Ḡ'(0) = E(-𝒢Ŝ𝒢)` (`tdm_hasDerivAt_expect`, the resolvent identity
   and fourth moments from the Gaussian absorption lemma); `Resid'(0)` from the
   differentiated-covariance lemma (`tgtCurvedClause`, `tdm_resid_eq`)
   with `‖Resid'(0)‖ ≤ 6 C W⁻² ‖Y‖ ≤ 6 C u/W`.
3. **The differentiated identity** (`tdm_deriv_identity`, uniqueness of derivatives):
   `(𝒟 - 𝒮(ḡ)) Ḡ' = Resid' - (Ŝ - 𝒮(ḡ')) Ḡ`, whose physical and port blocks are the
   hypotheses of `tdm_core` (`BlockBand.Layers.TaggedDecayMeanCore`).
4. **The comparison point** (`layerComparison_holds`): `|ḡ - a| ≤ C(d(X) + W⁻²)`;
   `‖Resid(0)‖ ≤ C W⁻²` (`lct_cov_one_letter`); the margin of the strict contraction bound
   (`strictContraction_margin`) gives `q < 1` in `tdm_core`.
5. **The outgoing derivative** (`tdc_D_step`, `tdc_D_step_eq_gdot`): a.s.
   `D_j(X₊, Y₊) = W⁻¹ Tr Q_j 𝒢Ŝ𝒢`, so `E D_j(X₊, Y₊) = -W⁻¹ Tr Q_j Ḡ'(0)`.

The instantiation of the analytic inputs and the closure by `tdm_core` is
`tdcLayerMean_holds` in `BlockBand.Layers.TaggedDecayMeanHolds`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. The derivative of the matrix mean
-/

section MeanDeriv

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- **Derivative of the matrix mean** along a family with the resolvent identity
`G_h - G₀ = -h G_h P G₀` (a.e.) and `E‖G_h‖⁴ ≤ C₄` for `|h| ≤ 1`:
`h ↦ E G_h` has derivative `E(-G₀ P G₀)` at `0`. -/
theorem tdm_hasDerivAt_expect {μ : Measure Ω} [IsProbabilityMeasure μ] (G : ℝ → Ω → Matrix ι ι ℂ)
    (P : Matrix ι ι ℂ) (hGm : ∀ h, Measurable (G h))
    (hres : ∀ h : ℝ, ∀ᵐ ω ∂μ, G h ω - G 0 ω = -((h : ℂ) • (G h ω * P * G 0 ω)))
    {C4 : ℝ} (hmom : ∀ h : ℝ, |h| ≤ 1 →
      Integrable (fun ω => ‖G h ω‖ ^ 4) μ ∧ ∫ ω, ‖G h ω‖ ^ 4 ∂μ ≤ C4) :
    HasDerivAt (fun h : ℝ => matrixExpect μ (G h))
      (matrixExpect μ (fun ω => -(G 0 ω * P * G 0 ω))) 0 := by
  set p := ‖P‖ with hp
  have hp0 : 0 ≤ p := norm_nonneg _
  set Gd : Ω → Matrix ι ι ℂ := fun ω => -(G 0 ω * P * G 0 ω) with hGd
  have h0 : |(0 : ℝ)| ≤ 1 := by simp
  have hC4 : 0 ≤ C4 := (integral_nonneg fun ω => by positivity).trans (hmom 0 h0).2
  set Q : ℝ → Ω → ℝ := fun h ω => 1 + ‖G h ω‖ ^ 4 + ‖G 0 ω‖ ^ 4 with hQ
  set B := 1 + 2 * C4 with hB
  have hQi : ∀ h, |h| ≤ 1 → Integrable (Q h) μ := fun h hh =>
    ((integrable_const 1).add (hmom h hh).1).add (hmom 0 h0).1
  have hQB : ∀ h, |h| ≤ 1 → ∫ ω, Q h ω ∂μ ≤ B := fun h hh => by
    simp only [hQ]
    have i1 : Integrable (fun ω => (1 : ℝ) + ‖G h ω‖ ^ 4) μ :=
      (integrable_const 1).add (hmom h hh).1
    rw [integral_add i1 (hmom 0 h0).1, integral_add (integrable_const 1) (hmom h hh).1,
      integral_const, probReal_univ, one_smul]
    linarith [(hmom h hh).2, (hmom 0 h0).2]
  have mono : ∀ h ω (i j : ℕ), i + j ≤ 4 → ‖G h ω‖ ^ i * ‖G 0 ω‖ ^ j ≤ Q h ω :=
    fun h ω i j hij => dcv_mono_le (norm_nonneg _) (norm_nonneg _) hij
  have hGQ : ∀ h ω, ‖G h ω‖ ≤ Q h ω := fun h ω => by simpa using mono h ω 1 0 (by norm_num)
  have hG02 : ∀ ω, ‖G 0 ω‖ ^ 2 ≤ Q 0 ω := fun ω => by simpa using mono 0 ω 0 2 (by norm_num)
  have hGdn : ∀ ω, ‖Gd ω‖ ≤ p * ‖G 0 ω‖ ^ 2 := fun ω => by
    simp only [hGd, norm_neg]
    exact (tdm_norm_mul3_le _ _ _).trans (le_of_eq (by ring))
  have mG : ∀ h, AEStronglyMeasurable (G h) μ := fun h => (hGm h).aestronglyMeasurable
  have hGdm : Measurable Gd :=
    (((continuous_id.mul continuous_const).mul continuous_id).neg.measurable).comp (hGm 0)
  have iG : ∀ h, |h| ≤ 1 → Integrable (G h) μ := fun h hh =>
    Integrable.mono' (hQi h hh) (mG h) (ae_of_all _ fun ω => hGQ h ω)
  have iGd : Integrable Gd μ :=
    Integrable.mono' ((hQi 0 h0).const_mul p) hGdm.aestronglyMeasurable (ae_of_all _ fun ω =>
      (hGdn ω).trans (mul_le_mul_of_nonneg_left (hG02 ω) hp0))
  refine dcv_hasDerivAt_of_sq (K := p ^ 2 * B) fun t ht => ?_
  have hexp : ∀ᵐ ω ∂μ, ‖G t ω - G 0 ω - (t : ℂ) • Gd ω‖ ≤ t ^ 2 * (p ^ 2 * Q t ω) :=
    (hres t).mono fun ω hω =>
      (dcv_expand_le (0 : Matrix ι ι ℂ →L[ℝ] ℂ) le_rfl (fun N => by simp) hω).2.1
  rw [dcv_matrixExpect_eq_integral (iG t ht), dcv_matrixExpect_eq_integral (iG 0 h0),
    dcv_matrixExpect_eq_integral iGd]
  have j1 : Integrable (fun ω => G t ω - G 0 ω) μ := (iG t ht).sub (iG 0 h0)
  have j2 : Integrable (fun ω => (t : ℝ) • Gd ω) μ := iGd.smul (t : ℝ)
  rw [← integral_smul, ← integral_sub (iG t ht) (iG 0 h0), ← integral_sub j1 j2]
  refine (dcv_norm_integral_le (hQi t ht) (k := t ^ 2 * p ^ 2) ?_).trans ?_
  · filter_upwards [hexp] with ω hω
    rw [Complex.coe_smul] at hω
    refine hω.trans (le_of_eq ?_)
    ring
  · have := mul_le_mul_of_nonneg_left (hQB t ht) (by positivity : 0 ≤ t ^ 2 * p ^ 2)
    linarith

end MeanDeriv

/-!
## 2. The covariance residual as a linear function of `Cov(g_D, 𝒢)`
-/

section Resid

variable {W : ℕ}

/-- `Cov(f, P U) = P Cov(f, U)` (entrywise expectations, integrable `U` and `fU`). -/
theorem tdm_cov_mul_left {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : Ω → ℂ) (U : Ω → Matrix ι ι ℂ) (P : Matrix ι ι ℂ)
    (hU : Integrable U μ) (hfU : Integrable (fun ω => f ω • U ω) μ) :
    meqCov μ f (fun ω => P * U ω) = P * dcvCov μ f U := by
  set L := ContinuousLinearMap.mul ℂ (Matrix ι ι ℂ) P
  have h1 : Integrable (fun ω => P * U ω) μ := L.integrable_comp hU
  have e2 : (fun ω => f ω • (P * U ω)) = fun ω => P * (f ω • U ω) := by
    funext ω; rw [Matrix.mul_smul]
  have h2 : Integrable (fun ω => f ω • (P * U ω)) μ := by
    rw [e2]; exact L.integrable_comp hfU
  unfold meqCov dcvCov
  rw [meq_matrixExpect_eq h1, meq_matrixExpect_eq h2, meq_matrixExpect_eq hU,
    meq_matrixExpect_eq hfU, e2]
  have i1 : ∫ ω, P * (f ω • U ω) ∂μ = P * ∫ ω, f ω • U ω ∂μ := L.integral_comp_comm hfU
  have i2 : ∫ ω, P * U ω ∂μ = P * ∫ ω, U ω ∂μ := L.integral_comp_comm hU
  rw [i1, i2, Matrix.mul_sub, Matrix.mul_smul]

/-- The covariance `Cov(W⁻¹ Tr(D𝒢), 𝒢)`. -/
def tdmCov (μ : Measure (LayerSample W .separate)) (D : Matrix (LayerSite W .separate)
    (LayerSite W .separate) ℂ) (G : LayerSample W .separate → Matrix (LayerSite W .separate)
      (LayerSite W .separate) ℂ) : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * G ω).trace) G

/-- The linear combination of covariances forming the residual. -/
def tdmLc (b : ℝ) (A B : Fin 2 → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  ∑ a : Fin 2, (1 - 2 * (b : ℂ)) • (meqPhysProj (σ := .separate) a * A a) +
    ∑ a : Fin 2, ∑ j : Fin 2, ((b : ℂ) * meqInc .separate a j) •
      (meqPhysProj (σ := .separate) a * B j + meqPortProj (σ := .separate) j * A a)

/-- **The residual in covariance form**: with `𝒢` and `W⁻¹Tr(D𝒢)𝒢` integrable for `‖D‖ ≤ 1`,
`Resid = Σ_a c P_a Cov(g_a, 𝒢) + Σ_{a,j} b inc(a,j) (P_a Cov(g_{port j}, 𝒢) + Q_j Cov(g_a, 𝒢))`. -/
theorem tdm_resid_eq {μ : Measure (LayerSample W .separate)} (b : ℝ)
    (G : LayerSample W .separate → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    (hG : Integrable G μ)
    (hfG : ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      Integrable (fun ω => ((W : ℂ)⁻¹ * (D * G ω).trace) • G ω) μ) :
    meqResid μ (1 - 2 * (b : ℂ)) b G =
      tdmLc b (fun a => tdmCov μ (meqPhysProj a) G) (fun j => tdmCov μ (meqPortProj j) G) := by
  have hP := fun a => hfG _ (meq_norm_physProj_le (W := W) (σ := .separate) a)
  have hQ := fun j => hfG _ (meq_norm_portProj_le (W := W) (σ := .separate) j)
  unfold meqResid tdmLc tdmCov
  simp only [lct_phys_eq_trace, lct_port_eq_trace]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [tdm_cov_mul_left _ _ _ hG (hP a)]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
    rw [tdm_cov_mul_left _ _ _ hG (hQ j), tdm_cov_mul_left _ _ _ hG (hP a)]

/-- `tdmLc` is differentiable along differentiable families, with the obvious derivative. -/
theorem tdm_hasDerivAt_lc (b : ℝ)
    {A B : ℝ → Fin 2 → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ}
    {A' B' : Fin 2 → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ}
    (hA : ∀ a, HasDerivAt (fun h => A h a) (A' a) 0)
    (hB : ∀ j, HasDerivAt (fun h => B h j) (B' j) 0) :
    HasDerivAt (fun h => tdmLc b (A h) (B h)) (tdmLc b A' B') 0 := by
  have hT1 : ∀ a : Fin 2, HasDerivAt
      (fun h => (1 - 2 * (b : ℂ)) • (meqPhysProj (σ := .separate) a * A h a))
      ((1 - 2 * (b : ℂ)) • (meqPhysProj (σ := .separate) a * A' a)) 0 := fun a =>
    ((hA a).const_mul (meqPhysProj (σ := .separate) a)).const_smul (1 - 2 * (b : ℂ))
  have hT2 : ∀ a j : Fin 2, HasDerivAt
      (fun h => ((b : ℂ) * meqInc .separate a j) •
        (meqPhysProj (σ := .separate) a * B h j + meqPortProj (σ := .separate) j * A h a))
      (((b : ℂ) * meqInc .separate a j) •
        (meqPhysProj (σ := .separate) a * B' j + meqPortProj (σ := .separate) j * A' a)) 0 :=
    fun a j => (((hB j).const_mul (meqPhysProj (σ := .separate) a)).add
      ((hA a).const_mul (meqPortProj (σ := .separate) j))).const_smul ((b : ℂ) * meqInc .separate a j)
  unfold tdmLc
  simp only [Fin.sum_univ_two]
  exact ((hT1 0).add (hT1 1)).add (((hT2 0 0).add (hT2 0 1)).add ((hT2 1 0).add (hT2 1 1)))

/-- `‖tdmLc b A B‖ ≤ 6 β` when every `‖A a‖, ‖B j‖ ≤ β`, `0 < b < 1/2`. -/
theorem tdm_norm_lc_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {A B : Fin 2 → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ} {β : ℝ}
    (hA : ∀ a, ‖A a‖ ≤ β) (hB : ∀ j, ‖B j‖ ≤ β) : ‖tdmLc b A B‖ ≤ 6 * β := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans (hA 0)
  have hc := tdm_norm_c hb1
  have hbn := tdm_norm_b hb0
  have hPA : ∀ a k, ‖meqPhysProj (W := W) (σ := .separate) a * A k‖ ≤ β := fun a k =>
    (norm_mul_le _ _).trans (by
      have := meq_norm_physProj_le (W := W) (σ := .separate) a
      nlinarith only [this, hA k, norm_nonneg (A k), norm_nonneg
        (meqPhysProj (W := W) (σ := .separate) a)])
  have hPB : ∀ a k, ‖meqPhysProj (W := W) (σ := .separate) a * B k‖ ≤ β := fun a k =>
    (norm_mul_le _ _).trans (by
      have := meq_norm_physProj_le (W := W) (σ := .separate) a
      nlinarith only [this, hB k, norm_nonneg (B k), norm_nonneg
        (meqPhysProj (W := W) (σ := .separate) a)])
  have hQA : ∀ j k, ‖meqPortProj (W := W) (σ := .separate) j * A k‖ ≤ β := fun j k =>
    (norm_mul_le _ _).trans (by
      have := meq_norm_portProj_le (W := W) (σ := .separate) j
      nlinarith only [this, hA k, norm_nonneg (A k), norm_nonneg
        (meqPortProj (W := W) (σ := .separate) j)])
  have hinc : ∀ a j, ‖(b : ℂ) * meqInc .separate a j‖ ≤ b := fun a j => by
    rw [norm_mul, hbn]
    have := lct_norm_meqInc_le (σ := .separate) a j
    nlinarith only [this, hb0, norm_nonneg (meqInc .separate a j)]
  have t1 : ∀ a, ‖(1 - 2 * (b : ℂ)) • (meqPhysProj (σ := .separate) a * A a)‖ ≤ β := fun a => by
    rw [norm_smul, hc]
    nlinarith only [hPA a a, hb0, hb1, norm_nonneg (meqPhysProj (W := W) (σ := .separate) a * A a)]
  have t2 : ∀ a j, ‖((b : ℂ) * meqInc .separate a j) •
      (meqPhysProj (σ := .separate) a * B j + meqPortProj (σ := .separate) j * A a)‖ ≤ 2 * b * β :=
    fun a j => by
      rw [norm_smul]
      have h := (norm_add_le _ _).trans (add_le_add (hPB a j) (hQA j a))
      have h0 := norm_nonneg (meqPhysProj (W := W) (σ := .separate) a * B j +
        meqPortProj (σ := .separate) j * A a)
      nlinarith only [h, hinc a j, h0, hβ, norm_nonneg ((b : ℂ) * meqInc .separate a j)]
  unfold tdmLc
  simp only [Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  have s1 := (norm_add_le _ _).trans (add_le_add (t1 0) (t1 1))
  have s2 := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (t2 0 0) (t2 0 1)))
    ((norm_add_le _ _).trans (add_le_add (t2 1 0) (t2 1 1))))
  nlinarith only [s1, s2, hb0, hb1, hβ]

end Resid

/-!
## 3. The self-energy as a continuous linear map
-/

section Shift

variable {W : ℕ}

/-- `M ↦ 𝒮(g(M)) = meqShift (c, b) (W⁻¹ Tr P_a M) (W⁻¹ Tr Q_j M)`. -/
def tdmShiftLin (b : ℝ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ →ₗ[ℝ]
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ where
  toFun M := meqShift .separate (1 - 2 * (b : ℂ)) b (fun a => physBlockTrace M a)
    (fun j => portBlockTrace M j)
  map_add' M N := by
    have hA : ∀ a, physBlockTrace (M + N) a = physBlockTrace M a + physBlockTrace N a :=
      fun a => map_add (meqPhysTraceCLM (W := W) (σ := .separate) a) M N
    have hP : ∀ j, portBlockTrace (M + N) j = portBlockTrace M j + portBlockTrace N j :=
      fun j => map_add (meqPortTraceCLM (W := W) (σ := .separate) j) M N
    simp only [hA, hP]
    unfold meqShift
    rw [diagonal_add]
    congr 1
    funext x
    rcases x with x | x <;> simp <;> ring
  map_smul' r M := by
    have hA : ∀ a, physBlockTrace (r • M) a = (r : ℂ) * physBlockTrace M a := fun a => by
      rw [← Complex.coe_smul]
      exact map_smul (meqPhysTraceCLM (W := W) (σ := .separate) a) (r : ℂ) M
    have hP : ∀ j, portBlockTrace (r • M) j = (r : ℂ) * portBlockTrace M j := fun j => by
      rw [← Complex.coe_smul]
      exact map_smul (meqPortTraceCLM (W := W) (σ := .separate) j) (r : ℂ) M
    simp only [hA, hP, RingHom.id_apply]
    unfold meqShift
    rw [← Complex.coe_smul, ← diagonal_smul]
    congr 1
    funext x
    rcases x with x | x <;> simp <;> ring_nf

/-- The self-energy as a continuous linear map. -/
def tdmShift (b : ℝ) :
    Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ →L[ℝ]
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
  LinearMap.toContinuousLinearMap (tdmShiftLin b)

theorem tdmShift_apply (b : ℝ) (M : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    tdmShift b M = meqShift .separate (1 - 2 * (b : ℂ)) b (fun a => physBlockTrace M a)
      (fun j => portBlockTrace M j) := rfl

/-- `tflConst(X - hS) = tflConst(X) + h Ŝ`. -/
theorem tdm_tflConst_sub (E : ℝ) (z : ℂ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (h : ℝ) :
    tflConst .separate E z (X - (h : ℂ) • S) = tflConst .separate E z X + (h : ℂ) • dcvHat S := by
  unfold tflConst dcvHat
  rw [fromBlocks_smul, fromBlocks_add]
  congr 1
  · abel
  · simp
  · simp
  · simp

end Shift

/-!
## 4. The differentiated identity and its blocks
-/

section Identity

variable {W : ℕ}

/-- **Differentiating the exact mean identity** (in the paper: "Differentiate this identity
before estimating"). If `F(h) = (𝒟(0) + hŜ - 𝒮(Ḡ(h))) Ḡ(h) = I + Resid(h)` for every `h`, with
`Ḡ'(0) = Ġ` and `Resid'(0) = Ṙ`, then `(𝒟(0) - 𝒮(Ḡ(0))) Ġ = Ṙ - (Ŝ - 𝒮(Ġ)) Ḡ(0)`. -/
theorem tdm_deriv_identity (b : ℝ) (D0 Sh : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)
    {Gb Rs : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ}
    {Gdot Rdot : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ}
    (hF : ∀ h : ℝ, (D0 + (h : ℂ) • Sh - tdmShift b (Gb h)) * Gb h = 1 + Rs h)
    (hG : HasDerivAt Gb Gdot 0) (hR : HasDerivAt Rs Rdot 0) :
    (D0 - tdmShift b (Gb 0)) * Gdot = Rdot - (Sh - tdmShift b Gdot) * Gb 0 := by
  have hlin : HasDerivAt (fun h : ℝ => D0 + (h : ℂ) • Sh) Sh 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const Sh).const_add D0
    simpa [Complex.coe_smul] using this
  have hsh : HasDerivAt (fun h => tdmShift b (Gb h)) (tdmShift b Gdot) 0 :=
    (tdmShift b).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hG
  have hN := (hlin.sub hsh).mul hG
  have hN' : HasDerivAt (fun h => 1 + Rs h)
      ((Sh - tdmShift b Gdot) * Gb 0 + (D0 + ((0 : ℝ) : ℂ) • Sh - tdmShift b (Gb 0)) * Gdot) 0 := by
    have e : (fun h => 1 + Rs h) = fun h : ℝ => (D0 + (h : ℂ) • Sh - tdmShift b (Gb h)) * Gb h := by
      funext h; exact (hF h).symm
    rw [e]; exact hN
  have hu := hN'.unique (hR.const_add 1)
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hu
  rw [← hu]; abel

/-- `(A B)₁₁ = A₁₁ B₁₁ + A₁₂ B₂₁`. -/
theorem tdm_toBlocks11_mul {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₁₁]

theorem tdm_portBlockTrace_one (hW : 0 < W) (j : Fin 2) :
    portBlockTrace (1 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) j = 1 := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  simp [portBlockTrace, hW']

/-- **The blocks of the differentiated identity.** With `v = W⁻¹ Tr P Ġ`, `w = W⁻¹ Tr Q Ġ`,
`gA = W⁻¹ Tr P Ḡ`, `gP = W⁻¹ Tr Q Ḡ`:
the physical block `T Ġ₁₁ = Ṙ₁₁ - S Ḡ₁₁ + diag(cv + bw) Ḡ₁₁` and the port traces
`(z - b gA_j) w_j = W⁻¹ Tr Q_j Ṙ + b v_j gP_j`. -/
theorem tdm_blocks (hW : 0 < W) (b E : ℝ) (z : ℂ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {Gb Gdot Rdot : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ}
    (h : (tflConst .separate E z X - tdmShift b Gb) * Gdot = Rdot - (dcvHat S - tdmShift b Gdot) * Gb) :
    meqTop .separate E X (1 - 2 * (b : ℂ)) b (fun a => physBlockTrace Gb a)
        (fun j => portBlockTrace Gb j) * Gdot.toBlocks₁₁ =
      Rdot.toBlocks₁₁ - S * Gb.toBlocks₁₁ + diagonal (fun x : Fin 2 × Fin W =>
        (1 - 2 * (b : ℂ)) * physBlockTrace Gdot x.1 + (b : ℂ) * portBlockTrace Gdot x.1) *
          Gb.toBlocks₁₁ ∧
    ∀ j : Fin 2, (z - (b : ℂ) * physBlockTrace Gb j) * portBlockTrace Gdot j =
      portBlockTrace Rdot j + (b : ℂ) * physBlockTrace Gdot j * portBlockTrace Gb j := by
  set Rhs := Rdot - (dcvHat S - tdmShift b Gdot) * Gb with hRhs
  have h1 : (tflConst .separate E z X - meqShift .separate (1 - 2 * (b : ℂ)) b
      (fun a => physBlockTrace Gb a) (fun j => portBlockTrace Gb j)) * Gdot = 1 + (Rhs - 1) := by
    rw [add_sub_cancel]; exact h
  have hsh11 : (tdmShift b Gdot).toBlocks₁₁ = diagonal (fun x : Fin 2 × Fin W =>
      (1 - 2 * (b : ℂ)) * physBlockTrace Gdot x.1 + (b : ℂ) * portBlockTrace Gdot x.1) := by
    have hs : ∀ i : Fin 2, ∑ j : Fin 2, meqInc .separate i j * portBlockTrace Gdot j =
        portBlockTrace Gdot i := fun i => meq_sum_inc_separate_phys (fun x => portBlockTrace Gdot x) i
    rw [tdmShift_apply]
    unfold meqShift
    ext p q
    rw [toBlocks₁₁, of_apply, diagonal_apply, diagonal_apply]
    simp only [Sum.inl.injEq, Sum.elim_inl, hs]
  have hsh12 : (tdmShift b Gdot).toBlocks₁₂ = 0 := by
    rw [tdmShift_apply]
    ext p q
    simp [meqShift, toBlocks₁₂]
  refine ⟨?_, fun j => ?_⟩
  · have hb := (meq_blocks h1).1
    rw [hb]
    have e1 : (1 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ).toBlocks₁₁ = 1 := by
      ext p q; simp [toBlocks₁₁, Matrix.one_apply]
    have e2 : (Rhs - 1).toBlocks₁₁ = Rhs.toBlocks₁₁ - 1 := by
      rw [← e1]; rfl
    rw [e2, add_sub_cancel, hRhs]
    have e3 : (Rdot - (dcvHat S - tdmShift b Gdot) * Gb).toBlocks₁₁ =
        Rdot.toBlocks₁₁ - ((dcvHat S - tdmShift b Gdot) * Gb).toBlocks₁₁ := rfl
    rw [e3, tdm_toBlocks11_mul]
    have e4 : (dcvHat S - tdmShift b Gdot).toBlocks₁₁ = S - (tdmShift b Gdot).toBlocks₁₁ := by
      ext p q; simp [dcvHat, toBlocks₁₁, fromBlocks]
    have e5 : (dcvHat S - tdmShift b Gdot).toBlocks₁₂ = 0 := by
      have : (dcvHat S - tdmShift b Gdot).toBlocks₁₂ =
          (dcvHat S : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ).toBlocks₁₂ -
            (tdmShift b Gdot).toBlocks₁₂ := rfl
      rw [this, hsh12, sub_zero]
      ext p q; simp [dcvHat, toBlocks₁₂]
    rw [e4, e5, hsh11, Matrix.zero_mul, add_zero, Matrix.sub_mul]
    abel
  · have hp := meq_port_scalar hW h1 j
    rw [meqPortCoef, meq_sum_inc_separate_port] at hp
    rw [hp]
    have hlin : ∀ A B : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ,
        portBlockTrace (A - B) j = portBlockTrace A j - portBlockTrace B j := fun A B =>
      map_sub (meqPortTraceCLM (W := W) (σ := .separate) j) A B
    rw [hlin, tdm_portBlockTrace_one hW, add_sub_cancel, hRhs, hlin]
    have hs : ∀ i : Fin 2, ∑ a : Fin 2, meqInc .separate a i * physBlockTrace Gdot a =
        physBlockTrace Gdot i := fun i => meq_sum_inc_separate_port (fun x => physBlockTrace Gdot x) i
    have hentry : ∀ α : Fin W, (((dcvHat S : Matrix (LayerSite W .separate)
        (LayerSite W .separate) ℂ) - tdmShift b Gdot) * Gb) (Sum.inr (j, α)) (Sum.inr (j, α)) =
          -((b : ℂ) * physBlockTrace Gdot j) * Gb (Sum.inr (j, α)) (Sum.inr (j, α)) := by
      intro α
      rw [Matrix.sub_mul, Matrix.sub_apply, tdmShift_apply]
      have h0 : ((dcvHat S : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) * Gb)
          (Sum.inr (j, α)) (Sum.inr (j, α)) = 0 := by
        simp [dcvHat, Matrix.mul_apply, Fintype.sum_sum_type]
      rw [h0]
      unfold meqShift
      rw [diagonal_mul]
      simp only [Sum.elim_inr, hs]
      ring
    have hent : portBlockTrace (((dcvHat S : Matrix (LayerSite W .separate)
        (LayerSite W .separate) ℂ) - tdmShift b Gdot) * Gb) j =
        -((b : ℂ) * physBlockTrace Gdot j * portBlockTrace Gb j) := by
      unfold portBlockTrace
      simp only [hentry, ← Finset.mul_sum]
      ring
    rw [hent]; ring

end Identity

/-!
## 5. The differentiated mean system of one layer
-/

section System

variable {W : ℕ}

/-- `meqTop` of the separate shape is `tdmTop` on `|E| ≤ 2` (`z_∂ = -E - (1-b)a`). -/
theorem tdm_top_eq (b : ℝ) {E : ℝ} (hE : |E| ≤ 2) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (gA gP : Fin 2 → ℂ) :
    meqTop .separate E X (1 - 2 * (b : ℂ)) b gA gP = tdmTop b E X gA gP := by
  have ha := matchedA_add_inv hE
  have hz : boundaryZ b E = -(E : ℂ) - (1 - (b : ℂ)) * matchedA E := by
    unfold boundaryZ; linear_combination ha
  rw [meqTop_separate]
  unfold tdmTop tdmDelta tdcK
  rw [hz]
  ext p q
  simp only [Matrix.sub_apply, Matrix.neg_apply, diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `x ≤ 1 + x⁴` and `x² ≤ 1 + x⁴` for `x ≥ 0`. -/
theorem tdm_pow_le (x : ℝ) : x ≤ 1 + x ^ 4 ∧ x ^ 2 ≤ 1 + x ^ 4 := by
  constructor
  · nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg x, sq_nonneg (x ^ 2 + x)]
  · nlinarith [sq_nonneg (x ^ 2 - 1)]

/-- **The differentiated mean system of one separate-port layer** (deterministic data `X`, `Y`,
`E`; the analytic inputs instantiated). Outputs the data of `tdm_core` and the identity
`E D_j(X₊, Y₊) = -w_j`. -/
theorem tdm_layer_system (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (hE2 : |E| ≤ 2) (hz : 0 < (boundaryZ b E).im)
    {X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (hY : Y.PosSemidef)
    {C4 θ B β : ℝ}
    (hinv : ∀ h : ℝ, ∀ᵐ ω ∂layerLaw W b .separate, IsUnit (layerMatrix .separate E (boundaryZ b E)
      (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) ω).det)
    (hmom : ∀ h : ℝ, Integrable (fun ω => ‖layerResolvent .separate E (boundaryZ b E)
        (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) ω‖ ^ 4) (layerLaw W b .separate) ∧
      ∫ ω, ‖layerResolvent .separate E (boundaryZ b E)
        (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) ω‖ ^ 4 ∂layerLaw W b .separate ≤ C4)
    (hmean : ∀ h : ℝ,
      (tflConst .separate E (boundaryZ b E) (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) -
        meqShift .separate (1 - 2 * (b : ℂ)) b
          (meqMeanA (layerLaw W b .separate) (layerResolvent .separate E (boundaryZ b E)
            (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X))))
          (meqMeanP (layerLaw W b .separate) (layerResolvent .separate E (boundaryZ b E)
            (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X))))) *
        matrixExpect (layerLaw W b .separate) (layerResolvent .separate E (boundaryZ b E)
          (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X))) =
      1 + meqResid (layerLaw W b .separate) (1 - 2 * (b : ℂ)) b (layerResolvent .separate E
        (boundaryZ b E) (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X))))
    (hcurv : ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      HasDerivAt (fun h : ℝ => dcvCov (layerLaw W b .separate)
          (fun ω => (W : ℂ)⁻¹ * (D * layerResolvent .separate E (boundaryZ b E)
            (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) ω).trace)
          (fun ω => layerResolvent .separate E (boundaryZ b E)
            (X - (h : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) ω))
        (dcvCovDir (layerLaw W b .separate) D
          (fun ω => layerResolvent .separate E (boundaryZ b E) X ω)
          (dcvHat ((tdcK b E X)ᴴ * Y * tdcK b E X))) 0 ∧
      ‖dcvCovDir (layerLaw W b .separate) D
          (fun ω => layerResolvent .separate E (boundaryZ b E) X ω)
          (dcvHat ((tdcK b E X)ᴴ * Y * tdcK b E X))‖ ≤ β)
    (hcmp : ∀ i, ‖meqMeanA (layerLaw W b .separate) (layerResolvent .separate E (boundaryZ b E) X) i -
        matchedA E‖ + ‖meqMeanP (layerLaw W b .separate)
          (layerResolvent .separate E (boundaryZ b E) X) i - matchedA E‖ ≤ θ)
    (hcov : ∀ P Q : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖P‖ ≤ 1 → ‖Q‖ ≤ 1 →
      ‖meqCov (layerLaw W b .separate)
          (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent .separate E (boundaryZ b E) X ω).trace)
          (fun ω => Q * layerResolvent .separate E (boundaryZ b E) X ω)‖ ≤ B) :
    ∃ (gA gP v w rp : Fin 2 → ℂ) (Gb Gd Res Rd : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ),
      (∀ i, ‖gA i - matchedA E‖ + ‖gP i - matchedA E‖ ≤ θ) ∧ ‖Res‖ ≤ 6 * B ∧
      ‖Rd‖ ≤ 6 * β ∧ (∀ j, ‖rp j‖ ≤ 6 * β) ∧
      tdmTop b E X gA gP * Gb = 1 + Res ∧
      tdmTop b E X gA gP * Gd = Rd - (tdcK b E X)ᴴ * Y * tdcK b E X * Gb +
        diagonal (fun x : Fin 2 × Fin W => (1 - 2 * (b : ℂ)) * v x.1 + (b : ℂ) * w x.1) * Gb ∧
      (∀ i, v i = blockTrace Gd i) ∧
      (∀ j, (boundaryZ b E - (b : ℂ) * gA j) * w j = rp j + (b : ℂ) * v j * gP j) ∧
      ∀ j, ∫ ℓ, tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j
        ∂layerLaw W b .separate = -w j := by
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  set μ := layerLaw W b .separate with hμ
  set z := boundaryZ b E with hzdef
  set K := tdcK b E X with hK
  set S := Kᴴ * Y * K with hSdef
  have hS : S.PosSemidef := hY.conjTranspose_mul_mul_same K
  set Sh : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ := dcvHat S with hSh
  set G : ℝ → LayerSample W .separate → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun h ω => layerResolvent .separate E z (X - (h : ℂ) • S) ω with hGdef
  set G0 : LayerSample W .separate → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun ω => layerResolvent .separate E z X ω with hG0def
  have hG0 : G 0 = G0 := by funext ω; simp [hGdef, hG0def]
  have hGm : ∀ h, Measurable (G h) := fun h => measurable_layerResolvent .separate E z _
  -- integrability
  have hint : ∀ h, Integrable (G h) μ := fun h =>
    Integrable.mono' ((integrable_const 1).add (hmom h).1) (hGm h).aestronglyMeasurable
      (ae_of_all _ fun ω => (tdm_pow_le _).1)
  have hint2 : ∀ h, Integrable (fun ω => ‖G h ω‖ ^ 2) μ := fun h =>
    Integrable.mono' ((integrable_const 1).add (hmom h).1)
      ((hGm h).norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact (tdm_pow_le _).2)
  have hintf : ∀ h (D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ), ‖D‖ ≤ 1 →
      Integrable (fun ω => ((W : ℂ)⁻¹ * (D * G h ω).trace) • G h ω) μ := by
    intro h D hD
    refine Integrable.mono' ((hint2 h).const_mul 4) ?_ (ae_of_all _ fun ω => ?_)
    · exact ((((tflTraceCLM W .separate D).continuous.measurable.comp (hGm h))).smul
        (hGm h)).aestronglyMeasurable
    · rw [norm_smul]
      have h1 := dcv_traceCLM_le (σ := .separate) hW D (G h ω)
      rw [tflTraceCLM_apply] at h1
      calc ‖(W : ℂ)⁻¹ * (D * G h ω).trace‖ * ‖G h ω‖ ≤ (4 * ‖D‖ * ‖G h ω‖) * ‖G h ω‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ 4 * ‖G h ω‖ ^ 2 := by nlinarith [norm_nonneg (G h ω), sq_nonneg ‖G h ω‖]
  -- step 1: the mean derivative
  have hres : ∀ h : ℝ, ∀ᵐ ω ∂μ, G h ω - G 0 ω = -((h : ℂ) • (G h ω * Sh * G 0 ω)) := fun h => by
    filter_upwards [hinv h, hinv 0] with ω h1 h0
    set Nh := layerMatrix .separate E z (X - (h : ℂ) • S) ω with hNh
    set N0 := layerMatrix .separate E z (X - ((0 : ℝ) : ℂ) • S) ω with hN0
    have k1 : Nh⁻¹ * Nh = 1 := nonsing_inv_mul _ h1
    have k0 : N0 * N0⁻¹ = 1 := mul_nonsing_inv _ h0
    have hdiff : N0 - Nh = -((h : ℂ) • Sh) := by
      rw [hNh, hN0, dcv_layerMatrix_sub, dcv_layerMatrix_sub]
      simp [hSh]
    change Nh⁻¹ - N0⁻¹ = -((h : ℂ) • (Nh⁻¹ * Sh * N0⁻¹))
    calc Nh⁻¹ - N0⁻¹ = Nh⁻¹ * (N0 * N0⁻¹) - (Nh⁻¹ * Nh) * N0⁻¹ := by
          rw [k0, k1, Matrix.mul_one, Matrix.one_mul]
      _ = Nh⁻¹ * (N0 - Nh) * N0⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = -((h : ℂ) • (Nh⁻¹ * Sh * N0⁻¹)) := by
          rw [hdiff, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  set Gdot := matrixExpect μ (fun ω => -(G 0 ω * Sh * G 0 ω)) with hGdot
  have hGd : HasDerivAt (fun h => matrixExpect μ (G h)) Gdot 0 :=
    tdm_hasDerivAt_expect G Sh hGm hres (fun h _ => hmom h)
  -- step 2: the residual derivative
  set A' : Fin 2 → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun a => dcvCovDir μ (meqPhysProj a) G0 Sh with hA'
  set B' : Fin 2 → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun j => dcvCovDir μ (meqPortProj j) G0 Sh with hB'
  set Rdot := tdmLc b A' B' with hRdot
  have hRe : (fun h => meqResid μ (1 - 2 * (b : ℂ)) b (G h)) =
      fun h => tdmLc b (fun a => tdmCov μ (meqPhysProj a) (G h))
        (fun j => tdmCov μ (meqPortProj j) (G h)) := by
    funext h
    exact tdm_resid_eq b (G h) (hint h) (hintf h)
  have hRd : HasDerivAt (fun h => meqResid μ (1 - 2 * (b : ℂ)) b (G h)) Rdot 0 := by
    rw [hRe]
    exact tdm_hasDerivAt_lc b
      (fun a => (hcurv _ (meq_norm_physProj_le (W := W) (σ := .separate) a)).1)
      (fun j => (hcurv _ (meq_norm_portProj_le (W := W) (σ := .separate) j)).1)
  have hRdn : ‖Rdot‖ ≤ 6 * β :=
    tdm_norm_lc_le hb0 hb1
      (fun a => (hcurv _ (meq_norm_physProj_le (W := W) (σ := .separate) a)).2)
      (fun j => (hcurv _ (meq_norm_portProj_le (W := W) (σ := .separate) j)).2)
  -- step 3: the differentiated identity
  set Gb : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
    fun h => matrixExpect μ (G h) with hGb
  have hshift : ∀ h, meqShift .separate (1 - 2 * (b : ℂ)) b (meqMeanA μ (G h)) (meqMeanP μ (G h)) =
      tdmShift b (Gb h) := by
    intro h
    rw [tdmShift_apply]
    congr 1
    · funext a; exact (meq_physBlockTrace_matrixExpect (hint h) a).symm
    · funext j; exact (meq_portBlockTrace_matrixExpect (hint h) j).symm
  have hF : ∀ h : ℝ, (tflConst .separate E z X + (h : ℂ) • Sh - tdmShift b (Gb h)) * Gb h =
      1 + meqResid μ (1 - 2 * (b : ℂ)) b (G h) := by
    intro h
    rw [← hshift h, ← tdm_tflConst_sub]
    exact hmean h
  have hid := tdm_deriv_identity b (tflConst .separate E z X) Sh hF hGd hRd
  have hbl := tdm_blocks hW b E z X S hid
  -- step 4: the mean equation at `h = 0`
  have hF0 := hF 0
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hF0
  rw [tdmShift_apply] at hF0
  have hb0' := (meq_blocks hF0).1
  rw [tdm_top_eq b hE2] at hb0' hbl
  have hRes : ‖(meqResid μ (1 - 2 * (b : ℂ)) b (G 0)).toBlocks₁₁‖ ≤ 6 * B := by
    rw [meq_resid_toBlocks11, hG0]
    have c1 : ∀ a, ‖meqCov μ (fun ω => physBlockTrace (G0 ω) a)
        (fun ω => meqPhysProj a * G0 ω)‖ ≤ B := by
      intro a
      rw [lct_cov_phys_eq]
      exact hcov _ _ (meq_norm_physProj_le a) (meq_norm_physProj_le a)
    have c2 : ∀ a j, ‖meqCov μ (fun ω => portBlockTrace (G0 ω) j)
        (fun ω => meqPhysProj a * G0 ω)‖ ≤ B := by
      intro a j
      rw [lct_cov_port_eq]
      exact hcov _ _ (meq_norm_portProj_le j) (meq_norm_physProj_le a)
    have h := lct_norm_residTop_le (σ := .separate) μ hb0.le hb1.le G0 c1 c2
    refine h.trans (le_of_eq ?_)
    norm_num
  have hGb0 : Gb 0 = matrixExpect μ G0 := by simp only [hGb, hG0]
  refine ⟨fun a => physBlockTrace (Gb 0) a, fun j => portBlockTrace (Gb 0) j,
    fun a => physBlockTrace Gdot a, fun j => portBlockTrace Gdot j,
    fun j => portBlockTrace Rdot j, (Gb 0).toBlocks₁₁, Gdot.toBlocks₁₁,
    (meqResid μ (1 - 2 * (b : ℂ)) b (G 0)).toBlocks₁₁, Rdot.toBlocks₁₁,
    ?_, hRes, (lct_norm_toBlocks11_le _).trans hRdn,
    fun j => (meq_norm_portBlockTrace_le _ _).trans hRdn, hb0', hbl.1, fun i => rfl, hbl.2, ?_⟩
  · intro i
    simp only
    rw [hGb0, meq_physBlockTrace_matrixExpect (hG0 ▸ hint 0),
      meq_portBlockTrace_matrixExpect (hG0 ▸ hint 0)]
    exact hcmp i
  · -- step 5: the outgoing derivative
    intro j
    have hGGm : Measurable (fun ω => G 0 ω * Sh * G 0 ω) :=
      (((continuous_id.mul continuous_const).mul continuous_id).measurable).comp (hGm 0)
    have hGGi : Integrable (fun ω => G 0 ω * Sh * G 0 ω) μ := by
      refine Integrable.mono' ((hint2 0).const_mul ‖Sh‖) hGGm.aestronglyMeasurable
        (ae_of_all _ fun ω => (tdm_norm_mul3_le _ _ _).trans (le_of_eq (by ring)))
    have hae : ∀ᵐ ℓ ∂μ, tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j =
        portBlockTrace (G 0 ℓ * Sh * G 0 ℓ) j := by
      filter_upwards [lct_ae_blocks_isHermitian W b .separate,
        srec_ae_isUnit_top hb1 .separate E X] with ℓ hℓ hSℓ
      have hNℓ := clk_layerMatrix_isUnit E z X ℓ hSℓ
        (clk_K_isUnit (srec_layerSchur_isHermitian E hX ℓ hℓ) hz)
      rw [tdc_D_step hz hX Y ℓ hℓ hSℓ hNℓ j, tdc_D_step_eq_gdot, lct_port_eq_trace, hG0]
    rw [integral_congr_ae hae]
    have hneg : Integrable (fun ω => -(G 0 ω * Sh * G 0 ω)) μ := hGGi.neg
    show _ = -portBlockTrace Gdot j
    rw [hGdot, meq_portBlockTrace_matrixExpect hneg, meqMeanP]
    have e : (fun ω => portBlockTrace (-(G 0 ω * Sh * G 0 ω)) j) =
        fun ω => -portBlockTrace (G 0 ω * Sh * G 0 ω) j := by
      funext ω; exact map_neg (meqPortTraceCLM (W := W) (σ := .separate) j) _
    rw [e, integral_neg, neg_neg]

end System

end BlockBand.Layers
