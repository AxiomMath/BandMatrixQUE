module

public import BlockBand.Critical.CommonPort.WeightedCov
public import BlockBand.Critical.CommonPort.SchwingerDyson

/-!
# Common-port mean: the residuals of the mean equations

Law: `layerLaw W b .common`, conditional on the deformation (every deterministic Hermitian `X`);
`e ∈ bulkInterval κ`. Notation: `𝒢 = commonPortResolvent b e X`, `P = meqPortProj 0` (the
common port projector), `F = 𝒢P𝒢ᴴ`, `K̂ = padTop (z_b - X)`, `c = 1 - 2b`; residuals `sdResid`
and `meqResidTop`.

* `meqCov_mul_right`, `sdResid_mul_right`: `Cov(f, U) D = Cov(f, U D)` and
  `sdResid(Y, Z) D = sdResid(Y, Z D)` for deterministic `D` (integrable `U`, `fU`).
* `norm_sdResid_le`: `‖sdResid‖ ≤ (#blocks + 2 #blocks #ports) B` when every covariance in it
  has norm `≤ B` (`0 ≤ b ≤ 1/2`).
* `sd_integrability`: `F, 𝒢ᴴ, ‖𝒢‖‖F‖, ‖F‖‖𝒢ᴴ‖ ∈ L¹` from `‖𝒢‖³ ∈ L¹`.
* word identities `wordEval_one`, `wordEval_two`, `wordEval_one_conj`, `wordEval_zero'`.
* **`commonPort_residuals`**: from the hypothesis `GaussianAbsorptionContract`, via
  `traceCovariance_holds` (unweighted words) and `weightedCov_holds` (weighted words):
  `‖sdResid(𝒢, F)‖`, `‖sdResid(F, 𝒢ᴴ)‖`, `‖sdResid(𝒢, F) K̂ᴴ‖`, `‖sdResid(F, 𝒢ᴴ) K̂ᴴ‖`,
  `‖meqResidTop(𝒢)‖ ≤ C W⁻²` for `W ≥ W₀`, uniformly in Hermitian `X` and `e ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical BlockBand.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. Right multiplication of covariances and residuals
-/

section Algebra

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Cov(f, U) D = Cov(f, U D)` for a deterministic matrix `D` (`U`, `fU` Bochner integrable). -/
theorem meqCov_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : Measure Ω} {f : Ω → ℂ}
    {U : Ω → Matrix ι ι ℂ} (hU : Integrable U ν) (hfU : Integrable (fun ω => f ω • U ω) ν)
    (D : Matrix ι ι ℂ) : meqCov ν f U * D = meqCov ν f (fun ω => U ω * D) := by
  set R := (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).flip D with hR
  have hRapp : ∀ N, R N = N * D := fun N => rfl
  have hUD : Integrable (fun ω => U ω * D) ν := by
    simpa only [hRapp] using R.integrable_comp hU
  have hfUD : Integrable (fun ω => f ω • (U ω * D)) ν := by
    have := R.integrable_comp hfU
    simpa only [hRapp, Matrix.smul_mul] using this
  rw [meq_cov_eq hfU hU, meq_cov_eq hfUD hUD]
  have e1 : ∫ ω, U ω * D ∂ν = (∫ ω, U ω ∂ν) * D := by
    have := R.integral_comp_comm hU
    simpa only [hRapp] using this
  have e2 : ∫ ω, f ω • (U ω * D) ∂ν = (∫ ω, f ω • U ω ∂ν) * D := by
    have := R.integral_comp_comm hfU
    simpa only [hRapp, Matrix.smul_mul] using this
  rw [e1, e2, Matrix.sub_mul, Matrix.smul_mul]

variable {W : ℕ} {σ : LayerShape}

/-- `sdResid(Y, Z) D = sdResid(Y, Z D)` (hypotheses of `sd_expand`). -/
theorem sdResid_mul_right {ν : Measure Ω} [IsFiniteMeasure ν]
    {Y Z : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hYm : AEStronglyMeasurable Y ν)
    (hZm : AEStronglyMeasurable Z ν) (hYZ : Integrable (fun ω => ‖Y ω‖ * ‖Z ω‖) ν)
    (hZi : Integrable Z ν) (c b : ℂ) (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    sdResid ν c b Y Z * D = sdResid ν c b Y (fun ω => Z ω * D) := by
  have iA : ∀ (a : Fin σ.blocks) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
      Integrable (fun ω => physBlockTrace (Y ω) a • (P * Z ω)) ν := fun a P =>
    sd_integrable_trace_smul hYm hZm hYZ (meq_continuous_physBlockTrace a)
      (fun M => meq_norm_physBlockTrace_le M a) P
  have iP : ∀ (j : Fin σ.ports) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
      Integrable (fun ω => portBlockTrace (Y ω) j • (P * Z ω)) ν := fun j P =>
    sd_integrable_trace_smul hYm hZm hYZ (meq_continuous_portBlockTrace j)
      (fun M => meq_norm_portBlockTrace_le M j) P
  have iZ : ∀ P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      Integrable (fun ω => P * Z ω) ν := fun P => hZi.const_mul P
  have hassoc : ∀ (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ),
      (fun ω => P * Z ω * D) = fun ω => P * (Z ω * D) := fun P => by
    funext ω; rw [Matrix.mul_assoc]
  unfold sdResid
  simp only [Matrix.add_mul, Finset.sum_mul, Matrix.smul_mul]
  simp only [meqCov_mul_right (iZ _) (iA _ _), meqCov_mul_right (iZ _) (iP _ _), hassoc]

/-- **Residual bound**: if every covariance entering `sdResid ν c b Y Z` has norm `≤ B`, then
`‖sdResid‖ ≤ (#blocks + 2 #blocks #ports) B` (`0 ≤ b ≤ 1/2`, `c = 1 - 2b`). -/
theorem norm_sdResid_le (ν : Measure Ω) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (Y Z : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) {B : ℝ}
    (h1 : ∀ a, ‖meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPhysProj a * Z ω)‖ ≤ B)
    (h2 : ∀ a j, ‖meqCov ν (fun ω => portBlockTrace (Y ω) j) (fun ω => meqPhysProj a * Z ω)‖ ≤ B)
    (h3 : ∀ a j, ‖meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPortProj j * Z ω)‖ ≤ B) :
    ‖sdResid ν (1 - 2 * (b : ℂ)) b Y Z‖ ≤ (σ.blocks + 2 * (σ.blocks * σ.ports) : ℕ) * B := by
  have hc : ‖(1 - 2 * (b : ℂ))‖ ≤ 1 := by
    rw [show (1 - 2 * (b : ℂ)) = ((1 - 2 * b : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hbn : ∀ a j, ‖(b : ℂ) * meqInc σ a j‖ ≤ 1 := fun a j => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    have := lct_norm_meqInc_le a j
    have := norm_nonneg (meqInc σ a j)
    nlinarith
  have hB0 : 0 ≤ B := by
    rcases Nat.eq_zero_or_pos σ.blocks with h | h
    · cases σ <;> simp at h
    · exact (norm_nonneg _).trans (h1 ⟨0, h⟩)
  unfold sdResid
  refine (norm_add_le _ _).trans ?_
  have hA : ‖∑ a, (1 - 2 * (b : ℂ)) • meqCov ν (fun ω => physBlockTrace (Y ω) a)
      (fun ω => meqPhysProj a * Z ω)‖ ≤ σ.blocks * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖(1 - 2 * (b : ℂ)) • meqCov ν (fun ω => physBlockTrace (Y ω) a)
          (fun ω => meqPhysProj a * Z ω)‖ ≤ ∑ _a : Fin σ.blocks, B := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [norm_smul]
          have := norm_nonneg (meqCov ν (fun ω => physBlockTrace (Y ω) a)
            (fun ω => meqPhysProj a * Z ω))
          nlinarith [h1 a, norm_nonneg (1 - 2 * (b : ℂ))]
      _ = σ.blocks * B := by simp
  have hP : ‖∑ a, ∑ j, ((b : ℂ) * meqInc σ a j) •
      (meqCov ν (fun ω => portBlockTrace (Y ω) j) (fun ω => meqPhysProj a * Z ω) +
        meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPortProj j * Z ω))‖ ≤
      (σ.blocks * σ.ports : ℕ) * (2 * B) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖∑ j, ((b : ℂ) * meqInc σ a j) •
          (meqCov ν (fun ω => portBlockTrace (Y ω) j) (fun ω => meqPhysProj a * Z ω) +
            meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPortProj j * Z ω))‖
        ≤ ∑ _a : Fin σ.blocks, ∑ _j : Fin σ.ports, 2 * B := by
          refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_smul]
          have h23 := (norm_add_le _ _).trans (add_le_add (h2 a j) (h3 a j))
          have := norm_nonneg (meqCov ν (fun ω => portBlockTrace (Y ω) j)
            (fun ω => meqPhysProj a * Z ω) +
              meqCov ν (fun ω => physBlockTrace (Y ω) a) (fun ω => meqPortProj j * Z ω))
          nlinarith [hbn a j, norm_nonneg ((b : ℂ) * meqInc σ a j)]
      _ = (σ.blocks * σ.ports : ℕ) * (2 * B) := by simp; ring
  push_cast at hP ⊢
  linarith

end Algebra

/-!
## 2. Integrability and word identities
-/

section Words

variable {W : ℕ} {σ : LayerShape}

/-- `t ≤ 1 + t³` and `t² ≤ 1 + t³` for real `t ≥ 0` (majorants for `‖𝒢‖`, `‖𝒢‖²`). -/
theorem sd_le_cube {t : ℝ} (ht : 0 ≤ t) : t ≤ 1 + t ^ 3 ∧ t ^ 2 ≤ 1 + t ^ 3 :=
  sd_le_one_add_cube ht

/-- Integrability for the two-resolvent expansion from `‖G‖³ ∈ L¹` (`‖P‖ ≤ 1`, probability
law): `F = GPGᴴ`, `Gᴴ`, `‖G‖‖F‖`, `‖F‖‖Gᴴ‖` are integrable. -/
theorem sd_integrability {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hm : Measurable G)
    {P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hP : ‖P‖ ≤ 1)
    (hG3 : Integrable (fun ω => ‖G ω‖ ^ 3) ν) :
    Integrable G ν ∧ Integrable (fun ω => G ω * P * (G ω)ᴴ) ν ∧
      Integrable (fun ω => (G ω)ᴴ) ν ∧
      Integrable (fun ω => ‖G ω‖ * ‖G ω * P * (G ω)ᴴ‖) ν ∧
      Integrable (fun ω => ‖G ω * P * (G ω)ᴴ‖ * ‖(G ω)ᴴ‖) ν := by
  have hGm : AEStronglyMeasurable G ν := hm.aestronglyMeasurable
  have cF : Continuous (fun N : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => N * P * Nᴴ) :=
    (continuous_id.mul continuous_const).mul continuous_id.matrix_conjTranspose
  have hFm : AEStronglyMeasurable (fun ω => G ω * P * (G ω)ᴴ) ν :=
    (cF.measurable.comp hm).aestronglyMeasurable
  have hHm : AEStronglyMeasurable (fun ω => (G ω)ᴴ) ν :=
    (continuous_id.matrix_conjTranspose.measurable.comp hm).aestronglyMeasurable
  have hD : Integrable (fun ω => 1 + ‖G ω‖ ^ 3) ν := (integrable_const 1).add hG3
  have nF : ∀ ω, ‖G ω * P * (G ω)ᴴ‖ ≤ ‖G ω‖ ^ 2 := by
    intro ω
    refine (norm_mul_le _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    calc ‖G ω * P‖ * ‖G ω‖ ≤ ‖G ω‖ * 1 * ‖G ω‖ := by
          gcongr; exact (norm_mul_le _ _).trans (by gcongr)
      _ = ‖G ω‖ ^ 2 := by ring
  have hG1 : Integrable G ν :=
    hD.mono' hGm (ae_of_all _ fun ω => (sd_le_cube (norm_nonneg _)).1)
  refine ⟨hG1, ?_, ?_, ?_, ?_⟩
  · exact hD.mono' hFm (ae_of_all _ fun ω => (nF ω).trans (sd_le_cube (norm_nonneg _)).2)
  · exact hG1.norm.mono' hHm (ae_of_all _ fun ω => by rw [l2_opNorm_conjTranspose])
  · refine hG3.mono' (hGm.norm.mul hFm.norm) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖G ω‖ * ‖G ω * P * (G ω)ᴴ‖ ≤ ‖G ω‖ * ‖G ω‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (nF ω) (norm_nonneg _)
      _ = ‖G ω‖ ^ 3 := by ring
  · refine hG3.mono' (hFm.norm.mul hHm.norm) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity), l2_opNorm_conjTranspose]
    calc ‖G ω * P * (G ω)ᴴ‖ * ‖G ω‖ ≤ ‖G ω‖ ^ 2 * ‖G ω‖ :=
          mul_le_mul_of_nonneg_right (nF ω) (norm_nonneg _)
      _ = ‖G ω‖ ^ 3 := by ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Deterministic word identity: the empty word `![A]` is `A`. -/
theorem wordEval_zero' (A G : Matrix n n ℂ) : wordEval (ℓ := 0) ![] ![A] G = A := by
  simp [wordEval]

/-- Deterministic word identity: `w(G) = A G B` for `ε = ![false]`, `D = ![A, B]`. -/
theorem wordEval_one (A B G : Matrix n n ℂ) :
    wordEval (ℓ := 1) ![false] ![A, B] G = A * G * B := by
  simp [wordEval, Matrix.mul_assoc]

/-- Deterministic word identity: `w(G) = A Gᴴ B` for `ε = ![true]`, `D = ![A, B]`. -/
theorem wordEval_one_conj (A B G : Matrix n n ℂ) :
    wordEval (ℓ := 1) ![true] ![A, B] G = A * Gᴴ * B := by
  simp [wordEval, Matrix.mul_assoc]

/-- Deterministic word identity: `w(G) = A G B Gᴴ C` for `ε = ![false, true]`. -/
theorem wordEval_two (A B C G : Matrix n n ℂ) :
    wordEval (ℓ := 2) ![false, true] ![A, B, C] G = A * G * B * Gᴴ * C := by
  simp [wordEval, List.ofFn_succ, Matrix.mul_assoc]

/-- Letter bounds `‖D j‖ ≤ 1` for `D = ![A, B]` (operator norm). -/
theorem norm_vec2_le {A B : Matrix n n ℂ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    ∀ j : Fin 2, ‖(![A, B] : Fin 2 → Matrix n n ℂ) j‖ ≤ 1 := by
  intro j; fin_cases j
  · exact hA
  · exact hB

/-- Letter bounds `‖D j‖ ≤ 1` for `D = ![A, B, C]` (operator norm). -/
theorem norm_vec3_le {A B C : Matrix n n ℂ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ∀ j : Fin 3, ‖(![A, B, C] : Fin 3 → Matrix n n ℂ) j‖ ≤ 1 := by
  intro j; fin_cases j
  · exact hA
  · exact hB
  · exact hC

/-- Letter bound `‖D j‖ ≤ 1` for `D = ![A]` (operator norm). -/
theorem norm_vec1_le {A : Matrix n n ℂ} (hA : ‖A‖ ≤ 1) :
    ∀ j : Fin 1, ‖(![A] : Fin 1 → Matrix n n ℂ) j‖ ≤ 1 := by
  intro j; fin_cases j; exact hA

end Words

/-!
## 3. The residual bounds on `layerLaw`
-/

section Bounds

/-- The common port projector `P = meqPortProj 0` has norm `≤ 1`. -/
theorem norm_commonP_le {W : ℕ} :
    ‖(meqPortProj (W := W) (σ := .common) 0 : Matrix (LayerSite W .common)
      (LayerSite W .common) ℂ)‖ ≤ 1 := meq_norm_portProj_le 0

/-- **Common-port mean: residual bounds**.
Law
`layerLaw W b.common`;
`0 < b < 1/2`, `κ > 0` first, then `C ≥ 0, W₀`; uniformly in `W ≥ W₀`,
Hermitian `X`, `e ∈ bulkInterval κ`.
With `𝒢 = commonPortResolvent b e X`, `P = meqPortProj 0`,
`F = 𝒢P𝒢ᴴ`, `K̂ = padTop (z_b - X)`, `c = 1 - 2b` (operator norms):
`‖sdResid(𝒢, F)‖, ‖sdResid(F, 𝒢ᴴ)‖, ‖sdResid(𝒢, F) K̂ᴴ‖, ‖sdResid(F, 𝒢ᴴ) K̂ᴴ‖,
‖meqResidTop(𝒢)‖ ≤ C W⁻²`.
Hypothesis:
`GaussianAbsorptionContract`;
other inputs `traceCovariance_holds` (unweighted words, `L = 2`, `K = 1`) and
`weightedCov_holds`.
-/
theorem commonPort_residuals (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
        ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
        ∀ e ∈ bulkInterval κ,
          ‖sdResid (layerLaw W b .common) (1 - 2 * (b : ℂ)) b (commonPortResolvent b e X)
              (fun ω => commonPortResolvent b e X ω * meqPortProj 0 *
                (commonPortResolvent b e X ω)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
          ‖sdResid (layerLaw W b .common) (1 - 2 * (b : ℂ)) b
              (fun ω => commonPortResolvent b e X ω * meqPortProj 0 *
                (commonPortResolvent b e X ω)ᴴ)
              (fun ω => (commonPortResolvent b e X ω)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 ∧
          ‖sdResid (layerLaw W b .common) (1 - 2 * (b : ℂ)) b (commonPortResolvent b e X)
              (fun ω => commonPortResolvent b e X ω * meqPortProj 0 *
                (commonPortResolvent b e X ω)ᴴ) *
                (padTop (matchedLeadK b e X))ᴴ‖ ≤ C / (W : ℝ) ^ 2 ∧
          ‖sdResid (layerLaw W b .common) (1 - 2 * (b : ℂ)) b
              (fun ω => commonPortResolvent b e X ω * meqPortProj 0 *
                (commonPortResolvent b e X ω)ᴴ)
              (fun ω => (commonPortResolvent b e X ω)ᴴ) *
                (padTop (matchedLeadK b e X))ᴴ‖ ≤ C / (W : ℝ) ^ 2 ∧
          ‖meqResidTop (layerLaw W b .common) (1 - 2 * (b : ℂ)) b
              (commonPortResolvent b e X)‖ ≤ C / (W : ℝ) ^ 2 := by
  intro b hb0 hb1 κ hκ
  by_cases hκ2 : 2 < κ
  · refine ⟨0, 0, le_rfl, fun W _ _ X _ e he => ?_⟩
    exact absurd (le_trans he.1 he.2) (by linarith)
  push Not at hκ2
  set η₀ : ℝ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
  have hη0 : 0 < η₀ := by
    have hs := Real.sqrt_pos.mpr (BlockBand.Layers.four_sub_sq_pos hκ (by linarith))
    have : 0 < 1 - 2 * b := by linarith
    positivity
  obtain ⟨Cu, Wu, hu⟩ := traceCovariance_holds hGA b hb0 hb1 η₀ 3 hη0 2 1
  obtain ⟨Cw, Ww, hw⟩ := weightedCov_holds hGA b hb0 hb1 κ hκ
  obtain ⟨ε₁, CG, hε₁, hCG, hGA'⟩ := hGA b hb0 hb1 η₀ 3 hη0
  set Cm : ℝ := max (max Cu Cw) 0 with hCm
  have hCm0 : 0 ≤ Cm := le_max_right _ _
  refine ⟨6 * Cm, max (max Wu Ww) ⌈(3 : ℝ) / ε₁⌉₊, by positivity, ?_⟩
  intro W hW hW₀ X hX e he
  have hWu : Wu ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hWw : Ww ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have h3W : (3 : ℝ) ≤ ε₁ * W := by
    have h1 : (3 : ℝ) / ε₁ ≤ W :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hW₀)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have heabs : |e| ≤ 2 := (abs_lt_two_of_mem_bulkInterval hκ he).le
  have hzim : η₀ ≤ (commonZ b e).im := commonZ_im_ge_of_mem_bulkInterval hb1.le hκ he
  have hznorm : ‖commonZ b e‖ ≤ 3 := norm_commonZ_le hb0.le (by linarith) heabs
  obtain ⟨-, hmom⟩ := hGA' W hW .common X hX e (commonZ b e) hzim hznorm
  have := bond_isProbabilityMeasure_layerLaw W b .common
  set ν := layerLaw W b .common with hν
  set G := commonPortResolvent b e X with hGdef
  set P : Matrix (LayerSite W .common) (LayerSite W .common) ℂ := meqPortProj 0 with hPdef
  set Kh : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
    padTop (matchedLeadK b e X) with hKh
  have hGm : Measurable G := measurable_layerResolvent .common e (commonZ b e) X
  have hG3 : Integrable (fun ω => ‖G ω‖ ^ 3) ν := by
    have h := hmom 3 (by norm_num) h3W
    have h' : eLpNorm (fun ω => ‖G ω‖) (ENNReal.ofReal ((3 : ℕ) : ℝ)) ν ≤ ENNReal.ofReal CG := by
      rw [Nat.cast_ofNat]; exact h
    exact (tcv_moment (by norm_num : 1 ≤ 3) hCG.le h').1
  obtain ⟨-, hFi, hHi, hGF, hFH⟩ := sd_integrability (P := P) hGm norm_commonP_le hG3
  have cF : Continuous (fun N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
      N * P * Nᴴ) := (continuous_id.mul continuous_const).mul continuous_id.matrix_conjTranspose
  have hFm : AEStronglyMeasurable (fun ω => G ω * P * (G ω)ᴴ) ν :=
    (cF.measurable.comp hGm).aestronglyMeasurable
  have hHm : AEStronglyMeasurable (fun ω => (G ω)ᴴ) ν :=
    (continuous_id.matrix_conjTranspose.measurable.comp hGm).aestronglyMeasurable
  set B : ℝ := Cm / (W : ℝ) ^ 2 with hB
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hCuB : Cu / (W : ℝ) ^ 2 ≤ B :=
    div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)
  have hCwB : Cw / (W : ℝ) ^ 2 ≤ B :=
    div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)
  -- unweighted and weighted word covariances
  have hcovU : ∀ (ℓf ℓU : ℕ), ℓf ≤ 2 → ℓU ≤ 2 → ∀ (εf : Fin ℓf → Bool)
      (Df : Fin (ℓf + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
      (εU : Fin ℓU → Bool)
      (DU : Fin (ℓU + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ),
      (∀ j, ‖Df j‖ ≤ 1) → (∀ j, ‖DU j‖ ≤ 1) →
      ‖meqCov ν (fun ω => (W : ℂ)⁻¹ * (wordEval εf Df (G ω)).trace)
        (fun ω => wordEval εU DU (G ω))‖ ≤ B := by
    intro ℓf ℓU hf hU εf Df εU DU hDf hDU
    exact ((hu W hW hWu .common X hX e (commonZ b e) hzim hznorm ℓf ℓU hf hU εf Df εU DU hDf
      hDU).2.2.2).trans hCuB
  have hcovW : ∀ (ℓf ℓU : ℕ), ℓf ≤ 2 → ℓU ≤ 1 → ∀ (εf : Fin ℓf → Bool)
      (Df : Fin (ℓf + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
      (εU : Fin ℓU → Bool)
      (DU : Fin (ℓU + 1) → Matrix (LayerSite W .common) (LayerSite W .common) ℂ),
      (∀ j, ‖Df j‖ ≤ 1) → (∀ j, ‖DU j‖ ≤ 1) →
      ‖meqCov ν (fun ω => (W : ℂ)⁻¹ * (wordEval εf Df (G ω)).trace)
        (fun ω => wordEval εU DU (G ω) * (Kh * G ω)ᴴ)‖ ≤ B := by
    intro ℓf ℓU hf hU εf Df εU DU hDf hDU
    exact ((hw W hW hWw X hX e he ℓf ℓU hf hU εf Df εU DU hDf hDU).2.2.2).trans hCwB
  have hPa := fun a : Fin LayerShape.common.blocks =>
    meq_norm_physProj_le (W := W) (σ := .common) a
  have hQj := fun j : Fin LayerShape.common.ports =>
    meq_norm_portProj_le (W := W) (σ := .common) j
  have h1n := lct_norm_one_le (n := LayerSite W .common)
  -- trace functionals as words
  have efA : ∀ (Y : LayerSample W .common → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
      a, (fun ω => physBlockTrace (Y ω) a) = fun ω => (W : ℂ)⁻¹ *
        (wordEval (ℓ := 1) (fun _ => false) ![meqPhysProj a, 1] (Y ω)).trace := fun Y a => by
    funext ω; exact meq_physBlockTrace_eq_word _ a
  have efP : ∀ (Y : LayerSample W .common → Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
      j, (fun ω => portBlockTrace (Y ω) j) = fun ω => (W : ℂ)⁻¹ *
        (wordEval (ℓ := 1) (fun _ => false) ![meqPortProj j, 1] (Y ω)).trace := fun Y j => by
    funext ω; exact meq_portBlockTrace_eq_word _ j
  have efFA : ∀ a, (fun ω => physBlockTrace (G ω * P * (G ω)ᴴ) a) = fun ω => (W : ℂ)⁻¹ *
      (wordEval (ℓ := 2) ![false, true] ![meqPhysProj a, P, 1] (G ω)).trace := fun a => by
    funext ω; rw [lct_phys_eq_trace, wordEval_two]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have efFP : ∀ j, (fun ω => portBlockTrace (G ω * P * (G ω)ᴴ) j) = fun ω => (W : ℂ)⁻¹ *
      (wordEval (ℓ := 2) ![false, true] ![meqPortProj j, P, 1] (G ω)).trace := fun j => by
    funext ω; rw [lct_port_eq_trace, wordEval_two]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have eUF : ∀ N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ,
      (fun ω => N * (G ω * P * (G ω)ᴴ)) =
        fun ω => wordEval (ℓ := 2) ![false, true] ![N, P, 1] (G ω) := fun N => by
    funext ω; rw [wordEval_two]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have eUH : ∀ N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ,
      (fun ω => N * (G ω)ᴴ) = fun ω => wordEval (ℓ := 1) ![true] ![N, 1] (G ω) := fun N => by
    funext ω; rw [wordEval_one_conj, Matrix.mul_one]
  have eUFK : ∀ N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ,
      (fun ω => N * (G ω * P * (G ω)ᴴ * Khᴴ)) =
        fun ω => wordEval (ℓ := 1) ![false] ![N, P] (G ω) * (Kh * G ω)ᴴ := fun N => by
    funext ω; rw [wordEval_one, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have eUHK : ∀ N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ,
      (fun ω => N * ((G ω)ᴴ * Khᴴ)) =
        fun ω => wordEval (ℓ := 0) ![] ![N] (G ω) * (Kh * G ω)ᴴ := fun N => by
    funext ω; rw [wordEval_zero', conjTranspose_mul]
  have eUG : ∀ N : Matrix (LayerSite W .common) (LayerSite W .common) ℂ,
      (fun ω => N * G ω) = fun ω => wordEval (ℓ := 1) (fun _ => false) ![N, 1] (G ω) :=
    fun N => by funext ω; exact meq_mul_eq_wordEval N (G ω)
  have h6 : ((LayerShape.common.blocks + 2 * (LayerShape.common.blocks *
      LayerShape.common.ports) : ℕ) : ℝ) * B = 6 * Cm / (W : ℝ) ^ 2 := by
    simp only [LayerShape.blocks, LayerShape.ports, hB]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (norm_sdResid_le ν hb0.le hb1.le G _ (fun a => ?_) (fun a j => ?_)
      (fun a j => ?_)).trans (le_of_eq h6)
    · rw [efA, eUF]
      exact hcovU 1 2 (by norm_num) le_rfl _ _ _ _ (norm_vec2_le (hPa a) h1n)
        (norm_vec3_le (hPa a) norm_commonP_le h1n)
    · rw [efP, eUF]
      exact hcovU 1 2 (by norm_num) le_rfl _ _ _ _ (norm_vec2_le (hQj j) h1n)
        (norm_vec3_le (hPa a) norm_commonP_le h1n)
    · rw [efA, eUF]
      exact hcovU 1 2 (by norm_num) le_rfl _ _ _ _ (norm_vec2_le (hPa a) h1n)
        (norm_vec3_le (hQj j) norm_commonP_le h1n)
  · refine (norm_sdResid_le ν hb0.le hb1.le _ _ (fun a => ?_) (fun a j => ?_)
      (fun a j => ?_)).trans (le_of_eq h6)
    · rw [efFA, eUH]
      exact hcovU 2 1 le_rfl (by norm_num) _ _ _ _ (norm_vec3_le (hPa a) norm_commonP_le h1n)
        (norm_vec2_le (hPa a) h1n)
    · rw [efFP, eUH]
      exact hcovU 2 1 le_rfl (by norm_num) _ _ _ _ (norm_vec3_le (hQj j) norm_commonP_le h1n)
        (norm_vec2_le (hPa a) h1n)
    · rw [efFA, eUH]
      exact hcovU 2 1 le_rfl (by norm_num) _ _ _ _ (norm_vec3_le (hPa a) norm_commonP_le h1n)
        (norm_vec2_le (hQj j) h1n)
  · rw [sdResid_mul_right hGm.aestronglyMeasurable hFm hGF hFi]
    refine (norm_sdResid_le ν hb0.le hb1.le G _ (fun a => ?_) (fun a j => ?_)
      (fun a j => ?_)).trans (le_of_eq h6)
    · rw [efA, eUFK]
      exact hcovW 1 1 (by norm_num) le_rfl _ _ _ _ (norm_vec2_le (hPa a) h1n)
        (norm_vec2_le (hPa a) norm_commonP_le)
    · rw [efP, eUFK]
      exact hcovW 1 1 (by norm_num) le_rfl _ _ _ _ (norm_vec2_le (hQj j) h1n)
        (norm_vec2_le (hPa a) norm_commonP_le)
    · rw [efA, eUFK]
      exact hcovW 1 1 (by norm_num) le_rfl _ _ _ _ (norm_vec2_le (hPa a) h1n)
        (norm_vec2_le (hQj j) norm_commonP_le)
  · rw [sdResid_mul_right hFm hHm hFH hHi]
    refine (norm_sdResid_le ν hb0.le hb1.le _ _ (fun a => ?_) (fun a j => ?_)
      (fun a j => ?_)).trans (le_of_eq h6)
    · rw [efFA, eUHK]
      exact hcovW 2 0 le_rfl (by norm_num) _ _ _ _ (norm_vec3_le (hPa a) norm_commonP_le h1n)
        (norm_vec1_le (hPa a))
    · rw [efFP, eUHK]
      exact hcovW 2 0 le_rfl (by norm_num) _ _ _ _ (norm_vec3_le (hQj j) norm_commonP_le h1n)
        (norm_vec1_le (hPa a))
    · rw [efFA, eUHK]
      exact hcovW 2 0 le_rfl (by norm_num) _ _ _ _ (norm_vec3_le (hPa a) norm_commonP_le h1n)
        (norm_vec1_le (hQj j))
  · refine (lct_norm_residTop_le (b := b) (B := B) ν hb0.le hb1.le G (fun a => ?_)
      (fun a j => ?_)).trans ?_
    · rw [efA, eUG]
      exact hcovU 1 1 (by norm_num) (by norm_num) _ _ _ _ (norm_vec2_le (hPa a) h1n)
        (norm_vec2_le (hPa a) h1n)
    · rw [efP, eUG]
      exact hcovU 1 1 (by norm_num) (by norm_num) _ _ _ _ (norm_vec2_le (hQj j) h1n)
        (norm_vec2_le (hPa a) h1n)
    · have hB0 : 0 ≤ B := by positivity
      simp only [LayerShape.blocks, LayerShape.ports, hB]
      push_cast
      have : (2 + 2 * 1 : ℝ) * (Cm / (W : ℝ) ^ 2) ≤ 6 * Cm / (W : ℝ) ^ 2 := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith

end Bounds

end BlockBand.Critical.CommonPort
