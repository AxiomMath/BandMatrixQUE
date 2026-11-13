module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanForm

/-!
# The pieces of `EΓ - θ_*I` (strictly passive `X`)

Hypothesis: `PassiveBoundsStatement`. Law `freshLaw W b`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`,
operator norm.

* `gap_covs`: the four trace–matrix covariances of `gap_mean_eq` are `O(W⁻²)` (the trace–matrix
  bound of `PassiveBoundsStatement` with words of length `≤ 2`: `⟨𝒢₁₂𝒢₂₁⟩, ⟨𝒢₂₂𝒢₂₂⟩, ⟨𝒢₁₁⟩,
  ⟨𝒢₂₂⟩` against `K𝒢₁₁`, `L𝒢₂₁`);
* `gap_decomp`: `EΓ = Ω·E[L𝒢₂₁] + (cEτ₀ + bEτ₁)·E[K𝒢₁₁] + c R₁ + c R₂ + b R₃ + b R₄`
  (`Ω = z + E + cE⟨𝒢₁₁⟩ + bE⟨𝒢₂₂⟩`; `R_i` the covariances);
* `theta_eq`: `cEτ₀ + bEτ₁ = thetaOf` (the source mixing scalar `θ = σ(E𝒢P₂𝒢)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer (passiveLetter passiveWord PassiveBoundsStatement
  layerAt g11 g12 g21 g22 kG11 lAt paramDisk)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The trace–matrix covariance `E[fU] - (Ef)(EU)`. -/
abbrev covR {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℂ)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  matrixExpect μ (fun ω => f ω • U ω) - (∫ ω, f ω ∂μ) • matrixExpect μ U

theorem passiveWord_two (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (k m : Fin 6) :
    passiveWord E w X ![(k, false), (m, false)] (fun _ => 1) =
      fun ω => passiveLetter E w X ω k * passiveLetter E w X ω m := by
  funext ω; simp [passiveWord, List.ofFn_succ]

/-- **The four covariances**, `O(W⁻²)`. -/
theorem gap_covs (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef →
      let μ := freshLaw W b
      (∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 0 x y) μ) ∧
      (∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 4 x y) μ) ∧
      (∀ x y, Integrable (fun ω => kfGap b E X ω x y) μ) ∧
      Integrable (tau0 b E X) μ ∧ Integrable (tau1 b E X) μ ∧
      Integrable (physTr b E X) μ ∧ Integrable (portTr b E X) μ ∧
      ‖covR μ (tau0 b E X) (fun ω => passiveLetter E (boundaryZ b E) X ω 4)‖ ≤ C / (W : ℝ) ^ 2 ∧
      ‖covR μ (physTr b E X) (kfGap b E X)‖ ≤ C / (W : ℝ) ^ 2 ∧
      ‖covR μ (tau1 b E X) (fun ω => passiveLetter E (boundaryZ b E) X ω 4)‖ ≤ C / (W : ℝ) ^ 2 ∧
      ‖covR μ (portTr b E X) (kfGap b E X)‖ ≤ C / (W : ℝ) ^ 2 := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  obtain ⟨C, W₀, h⟩ := hA.traceMatrix b hb0 hb _ hκ 2 1
  refine ⟨max C 0, W₀, le_max_right _ _, fun W hW X hX => ?_⟩
  intro μ
  have hE := PassiveLayer.mem_bulkInterval_min E
  have hz : boundaryZ b E ∈ paramDisk b E :=
    PassiveLayer.boundaryZ_mem_paramDisk (by linarith) h1 h2
  have hD1 : ∀ j : Fin 2, ‖(fun _ : Fin 2 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  have hD2 : ∀ j : Fin 3, ‖(fun _ : Fin 3 => (1 : Matrix (Fin W) (Fin W) ℂ)) j‖ ≤ 1 :=
    fun _ => norm_one_matrix_le
  have hCW : C / (W : ℝ) ^ 2 ≤ max C 0 / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  have c1 := h W hW E hE _ hz X hX 2 1 (by norm_num) (by norm_num) ![(1, false), (2, false)]
    (fun _ => 1) (fun _ => (4, false)) (fun _ => 1) hD2 hD1
  have c2 := h W hW E hE _ hz X hX 1 2 (by norm_num) (by norm_num) (fun _ => (0, false))
    (fun _ => 1) ![(5, false), (2, false)] (fun _ => 1) hD1 hD2
  have c3 := h W hW E hE _ hz X hX 2 1 (by norm_num) (by norm_num) ![(3, false), (3, false)]
    (fun _ => 1) (fun _ => (4, false)) (fun _ => 1) hD2 hD1
  have c4 := h W hW E hE _ hz X hX 1 2 (by norm_num) (by norm_num) (fun _ => (3, false))
    (fun _ => 1) ![(5, false), (2, false)] (fun _ => 1) hD1 hD2
  have c5 := h W hW E hE _ hz X hX 1 1 (by norm_num) (by norm_num) (fun _ => (0, false))
    (fun _ => 1) (fun _ => (0, false)) (fun _ => 1) hD1 hD1
  simp only [passiveWord_two, passiveWord_single_fun] at c1 c2 c3 c4 c5
  exact ⟨c5.2.1, c1.2.1, c2.2.1, c1.1, c3.1, c2.1, c4.1, c1.2.2.2.trans hCW, c2.2.2.2.trans hCW,
    c3.2.2.2.trans hCW, c4.2.2.2.trans hCW⟩

theorem matrixExpect_smul_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Ω → ℂ)
    (U : Ω → Matrix (Fin W) (Fin W) ℂ) :
    matrixExpect μ (fun ω => f ω • U ω) = covR μ f U + (∫ ω, f ω ∂μ) • matrixExpect μ U := by
  simp only [covR, sub_add_cancel]

/-- **The decomposition of `EΓ`** (strictly passive `X`). -/
theorem gap_decomp {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef) {C4 C6 : ℝ}
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hm6 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (3 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C6) (hW : 0 < W) :
    let μ := freshLaw W b
    let c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
    let L4 := fun ω => passiveLetter E (boundaryZ b E) X ω 4
    matrixExpect μ (gapLetter b E X) =
      (boundaryZ b E + E + c * ∫ ω, physTr b E X ω ∂μ + (b : ℂ) * ∫ ω, portTr b E X ω ∂μ) •
          matrixExpect μ (kfGap b E X) +
        (c * ∫ ω, tau0 b E X ω ∂μ + (b : ℂ) * ∫ ω, tau1 b E X ω ∂μ) • matrixExpect μ L4 +
        c • covR μ (tau0 b E X) L4 + c • covR μ (physTr b E X) (kfGap b E X) +
        (b : ℂ) • covR μ (tau1 b E X) L4 + (b : ℂ) • covR μ (portTr b E X) (kfGap b E X) := by
  intro μ c L4
  have h := gap_mean_eq hb0 hb h1 h2 hX hm4 hm6 hW
  simp only [] at h
  rw [h, matrixExpect_smul_add (tau0 b E X), matrixExpect_smul_add (physTr b E X),
    matrixExpect_smul_add (tau1 b E X), matrixExpect_smul_add (portTr b E X)]
  simp only [add_smul, smul_add, smul_smul]
  abel

theorem blkAt_tGap_zero (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : blkAt (tGap b E X ω) 0 0 = fGap b E X ω := by
  ext x y; rw [fGap_apply]; rfl

theorem blkAt_tGap_one (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    blkAt (tGap b E X ω) 1 1 =
      passiveLetter E (boundaryZ b E) X ω 3 * passiveLetter E (boundaryZ b E) X ω 3 := by
  ext x y
  show tGap b E X ω (port x) (port y) = _
  rw [tGap_port]; rfl

/-- `cEτ₀ + bEτ₁` is the source mixing scalar `θ = σ(E𝒢P₂𝒢)`. -/
theorem theta_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ((1 - 2 * b : ℝ) : ℂ) * (∫ ω, tau0 b E X ω ∂freshLaw W b) +
        (b : ℂ) * ∫ ω, tau1 b E X ω ∂freshLaw W b = SourceMixing.thetaOf b E X := by
  have e0 : ∫ ω, tau0 b E X ω ∂freshLaw W b = SourceMixing.tauTwo b E X 0 := by
    unfold SourceMixing.tauTwo
    congr 1; funext ω
    rw [SourceMixing.blkTr]
    exact congrArg (fun M : Matrix (Fin W) (Fin W) ℂ => (W : ℂ)⁻¹ * M.trace)
      (blkAt_tGap_zero b E X ω).symm
  have e1 : ∫ ω, tau1 b E X ω ∂freshLaw W b = SourceMixing.tauTwo b E X 1 := by
    unfold SourceMixing.tauTwo
    congr 1; funext ω
    rw [SourceMixing.blkTr]
    exact congrArg (fun M : Matrix (Fin W) (Fin W) ℂ => (W : ℂ)⁻¹ * M.trace)
      (blkAt_tGap_one b E X ω).symm
  rw [e0, e1]; rfl

/-- `E[K𝒢₁₁] = (K̂E𝒢)₀₀`. -/
theorem expect_letter4 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (hint : ∀ x y, Integrable (fun ω => passiveLetter E (boundaryZ b E) X ω 0 x y) (freshLaw W b)) :
    matrixExpect (freshLaw W b) (fun ω => passiveLetter E (boundaryZ b E) X ω 4) =
      blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 := by
  rw [(SourceMixing.blkAt_kHat_mul_zero b E X _).1, SourceMixing.blkAt_matrixExpect]
  have e : (fun ω => blkAt (gRes b E X ω) 0 0) = fun ω => passiveLetter E (boundaryZ b E) X ω 0 := by
    funext ω; ext x y; rfl
  rw [e, ← FullSource.matrixExpect_mul_left _ _ hint]
  rfl

end BlockBand.SourceProcess.CompleteSourceGap
