module

public import BlockBand.SourceProcess.CompleteSourceGap.Mean
public import BlockBand.SourceProcess.FullSource.DeltaMeanStrict

/-!
# The right Schwinger–Dyson identity for `T = 𝒢P₂𝒢`

* `hasLayerDeriv_tGap`: `d(𝒢P₂𝒢) = -(𝒢N𝒢)P₂𝒢 - 𝒢P₂(𝒢N𝒢)` along every Hermitian sample direction;
* **`meanSD_gap_right_of`**: Gaussian integration by parts on the **right** factor
  `V = layerLin` (`stein_layerA_lin`, `stein_layerBconj_lin`, as `meanSD_right_of` for `𝒢`):
  `E[(TV)_{α,y}] = -(c/W)E[Tr T₁₁·𝒢_{αy} + Tr𝒢₁₁·T_{αy}] - (b/W)E[Tr T₂₂·𝒢_{αy} + Tr𝒢₂₂·T_{αy}]`.
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
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `T = 𝒢P₂𝒢` (the integrand of `tauTwo`). -/
abbrev tGap (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    LayerMat W :=
  gRes b E X ω * (portProj * gRes b E X ω)

/-- The linear map `N ↦ -((𝒢N𝒢)P₂𝒢 + 𝒢P₂(𝒢N𝒢))_{αβ}`. -/
def tDeriv (G : LayerMat W) (α β : LayerSite W .oneBlockOnePort) : LayerMat W →ₗ[ℂ] ℂ where
  toFun N := -((G * N * G * (portProj * G) + G * (portProj * (G * N * G)) : LayerMat W) α β)
  map_add' N N' := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; ring
  map_smul' c N := by
    simp; ring

theorem tDeriv_apply (G N : LayerMat W) (α β : LayerSite W .oneBlockOnePort) :
    tDeriv G α β N =
      -((G * N * G * (portProj * G) + G * (portProj * (G * N * G)) : LayerMat W) α β) := rfl

theorem tDeriv_single (G : LayerMat W) (α β i j : LayerSite W .oneBlockOnePort) :
    tDeriv G α β (Matrix.single i j 1) =
      -(G α i * (G * (portProj * G) : LayerMat W) j β + (G * (portProj * G) : LayerMat W) α i * G j β) := by
  rw [tDeriv_apply, Matrix.add_apply,
    show G * Matrix.single i j 1 * G * (portProj * G) =
      G * Matrix.single i j 1 * (G * (portProj * G)) by simp only [Matrix.mul_assoc],
    show G * (portProj * (G * Matrix.single i j 1 * G)) =
      G * (portProj * G) * Matrix.single i j 1 * G by simp only [Matrix.mul_assoc],
    SourceMixing.mul_single_mul_apply', SourceMixing.mul_single_mul_apply']

theorem entryCLM_apply (α β : LayerSite W .oneBlockOnePort) (M : LayerMat W) :
    entryCLM α β M = M α β := rfl

theorem hasLayerDeriv_tGap (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (hinv : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian →
      IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω))
    (α β : LayerSite W .oneBlockOnePort) :
    HasLayerDeriv (fun ω => tGap b E X ω α β) (fun ω => tDeriv (gRes b E X ω) α β) := by
  intro ω hω Δ _
  have h := hasDerivAt_layerResolvent E (boundaryZ b E) _ ω Δ (hinv ω hω)
  have hT := h.mul (h.const_mul (portProj : LayerMat W))
  have h2 := (entryCLM α β).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hT
  refine h2.congr_deriv ?_
  rw [tDeriv_apply, entryCLM_apply]
  simp only [Complex.ofReal_zero, zero_smul, add_zero, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.add_apply, Matrix.neg_apply, neg_add, gRes]

theorem measurable_tGap (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (tGap (W := W) b E X) := by
  have hc : Continuous fun M : LayerMat W => M * (portProj * M) :=
    continuous_id.matrix_mul (continuous_const.matrix_mul continuous_id)
  exact hc.measurable.comp (measurable_layerRes E (boundaryZ b E) X)

theorem norm_tGap_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ‖tGap b E X ω‖ ≤ ‖gRes b E X ω‖ ^ 2 := by
  have h1 := Matrix.l2_opNorm_mul (gRes b E X ω) (portProj * gRes b E X ω)
  have h2 := Matrix.l2_opNorm_mul (portProj : LayerMat W) (gRes b E X ω)
  have hP : ‖(portProj : LayerMat W)‖ ≤ 1 := norm_portProj_le
  have hG := norm_nonneg (gRes b E X ω)
  have := norm_nonneg (portProj * gRes b E X ω)
  calc ‖tGap b E X ω‖ ≤ ‖gRes b E X ω‖ * ‖portProj * gRes b E X ω‖ := h1
    _ ≤ ‖gRes b E X ω‖ * ‖gRes b E X ω‖ := by gcongr; nlinarith
    _ = _ := by ring

/-- `|D_ω(N)| ≤ 2‖N‖‖𝒢‖³`. -/
theorem norm_tDeriv_le (G N : LayerMat W) (γ β : LayerSite W .oneBlockOnePort) :
    ‖tDeriv G γ β N‖ ≤ 2 * ‖N‖ * ‖G‖ ^ 3 := by
  have hP : ‖(portProj : LayerMat W)‖ ≤ 1 := norm_portProj_le
  have hg := norm_nonneg G
  have hN := norm_nonneg N
  have hGNG := norm_mul_mul_le G N
  have h4 := norm_nonneg (G * N * G)
  have e1 : ‖G * N * G * (portProj * G)‖ ≤ ‖N‖ * ‖G‖ ^ 3 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    have h2 := Matrix.l2_opNorm_mul (portProj : LayerMat W) G
    have h3 := norm_nonneg (portProj * G)
    have h5 : ‖portProj * G‖ ≤ ‖G‖ := h2.trans (by nlinarith)
    calc ‖G * N * G‖ * ‖portProj * G‖ ≤ (‖N‖ * ‖G‖ ^ 2) * ‖G‖ :=
          mul_le_mul hGNG h5 h3 (by positivity)
      _ = _ := by ring
  have e2 : ‖G * (portProj * (G * N * G))‖ ≤ ‖N‖ * ‖G‖ ^ 3 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    have h2 := Matrix.l2_opNorm_mul (portProj : LayerMat W) (G * N * G)
    have h5 : ‖portProj * (G * N * G)‖ ≤ ‖N‖ * ‖G‖ ^ 2 := h2.trans (by nlinarith)
    calc ‖G‖ * ‖portProj * (G * N * G)‖ ≤ ‖G‖ * (‖N‖ * ‖G‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h5 hg
      _ = _ := by ring
  rw [tDeriv_apply, norm_neg]
  refine (norm_entry_le' _ γ β).trans ((norm_add_le _ _).trans ?_)
  linarith

/-- `L²` bound for a function dominated by `c‖𝒢‖^k`, `k ≤ 3`. -/
theorem memLp_two_of_le_pow {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ}
    {f : LayerSample W .oneBlockOnePort → ℂ} (hf : Measurable f) {c : ℝ} (hc : 0 ≤ c) (k : ℕ)
    (hk : 1 ≤ k) {C : ℝ}
    (hm : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * k))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C)
    (hb : ∀ ω, ‖f ω‖ ≤ c * ‖gRes b E X ω‖ ^ k) : MemLp f 2 (layerLaw W b .oneBlockOnePort) := by
  have hgm : Measurable fun ω => ‖gRes b E X ω‖ :=
    continuous_norm.measurable.comp (measurable_layerRes E (boundaryZ b E) X)
  exact lt_of_le_of_lt (eLpNorm_two_le_of_pow_bound hf.aestronglyMeasurable
    (fun ω => norm_nonneg _) hgm.aestronglyMeasurable hc k hk hb hm)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).lt_top

section SD
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C2 C4 C6 : ℝ}

/-- **Right Schwinger–Dyson identity for `T = 𝒢P₂𝒢`.** -/
theorem meanSD_gap_right_of (hη : 0 < etaZ b E) (hX : (passiveY X).PosDef)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (hm6 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (3 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C6)
    (α : LayerSite W .oneBlockOnePort) (y : Fin W) :
    ∫ ω, (tGap b E X ω * layerLin ω) α (phys y) ∂layerLaw W b .oneBlockOnePort =
      -((gueVar W b : ℂ) * ∫ ω, (∑ a, tGap b E X ω (phys a) (phys a)) * gRes b E X ω α (phys y) +
          (∑ a, gRes b E X ω (phys a) (phys a)) * tGap b E X ω α (phys y)
        ∂layerLaw W b .oneBlockOnePort) -
      (ginVar W b : ℂ) * ∫ ω, (∑ a, tGap b E X ω (port a) (port a)) * gRes b E X ω α (phys y) +
          (∑ a, gRes b E X ω (port a) (port a)) * tGap b E X ω α (phys y)
        ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  have hinv := fun ω hω => isUnit_layerMatrix_strict (E := E) hη hX ω hω
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hTm := measurable_tGap (W := W) b E X
  -- integrability
  have hΦ : ∀ γ β, MemLp (fun ω => tGap b E X ω γ β) 2 μ := fun γ β =>
    memLp_two_of_le_pow hTm.eval_matrix zero_le_one 2 (by norm_num) hm4
      (fun ω => by rw [one_mul]; exact (norm_entry_le' _ γ β).trans (norm_tGap_le b E X ω))
  have hDm : ∀ γ β (N : LayerMat W), Measurable fun ω => tDeriv (gRes b E X ω) γ β N := by
    intro γ β N
    have e : (fun ω => tDeriv (gRes b E X ω) γ β N) = fun ω =>
        -((gRes b E X ω * N * gRes b E X ω * (portProj * gRes b E X ω) + gRes b E X ω * (portProj * (gRes b E X ω * N * gRes b E X ω)) :
          LayerMat W) γ β) := rfl
    rw [e]
    exact ((((hGm.mul_const N).mul hGm).mul (hGm.const_mul portProj)).add
      (hGm.mul (((hGm.mul_const N).mul hGm).const_mul portProj))).eval_matrix.neg
  have hDi : ∀ γ β (N : LayerMat W), Integrable (fun ω => tDeriv (gRes b E X ω) γ β N) μ := fun γ β N =>
    (memLp_two_of_le_pow (hDm γ β N) (by positivity : (0 : ℝ) ≤ 2 * ‖N‖) 3 (by norm_num) hm6
      (fun ω => norm_tDeriv_le _ N γ β)).integrable one_le_two
  -- the two integrations by parts
  have hA : ∀ a, ∫ ω, tGap b E X ω α (phys a) * ω.1 0 a y ∂μ =
      -((gueVar W b : ℂ) * ∫ ω, gRes b E X ω α (phys y) * tGap b E X ω (phys a) (phys a) +
        tGap b E X ω α (phys y) * gRes b E X ω (phys a) (phys a) ∂μ) := by
    intro a
    have h := stein_layerA_lin b (fun ω => tGap b E X ω α (phys a))
      (fun ω => tDeriv (gRes b E X ω) α (phys a)) (hasLayerDeriv_tGap b E X hinv α (phys a))
      hTm.eval_matrix (hΦ _ _) (hDi _ _) a y
    rw [layerA_single] at h
    have e1 : (fun ω => tGap b E X ω α (phys a) * ω.1 0 a y) =
        fun ω => ω.1 0 a y * tGap b E X ω α (phys a) := by funext ω; ring
    rw [e1, h, ← mul_neg, ← integral_neg]
    congr 1; congr 1; funext ω
    rw [tDeriv_single]
  have hB : ∀ a, ∫ ω, tGap b E X ω α (port a) * star (ω.2 0 0 y a) ∂μ =
      -((ginVar W b : ℂ) * ∫ ω, gRes b E X ω α (phys y) * tGap b E X ω (port a) (port a) +
        tGap b E X ω α (phys y) * gRes b E X ω (port a) (port a) ∂μ) := by
    intro a
    have h := stein_layerBconj_lin b (fun ω => tGap b E X ω α (port a))
      (fun ω => tDeriv (gRes b E X ω) α (port a)) (hasLayerDeriv_tGap b E X hinv α (port a))
      hTm.eval_matrix (hΦ _ _) (hDi _ _) y a
    rw [upperB_single] at h
    have e1 : (fun ω => tGap b E X ω α (port a) * star (ω.2 0 0 y a)) =
        fun ω => star (ω.2 0 0 y a) * tGap b E X ω α (port a) := by funext ω; ring
    rw [e1, h, ← mul_neg, ← integral_neg]
    congr 1; congr 1; funext ω
    rw [tDeriv_single]
  have hiA : ∀ a, Integrable (fun ω => tGap b E X ω α (phys a) * ω.1 0 a y) μ := fun a => by
    have := (memLp_layer_A b a y).integrable_mul (hΦ α (phys a))
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have hiB : ∀ a, Integrable (fun ω => tGap b E X ω α (port a) * star (ω.2 0 0 y a)) μ :=
    fun a => by
      have := (memLp_layer_B b y a).star.integrable_mul (hΦ α (port a))
      exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have hprod : ∀ γ δ ε, Integrable (fun ω => gRes b E X ω α (phys y) * tGap b E X ω γ δ +
      tGap b E X ω α (phys y) * gRes b E X ω ε ε) μ := by
    intro γ δ ε
    refine (memLp_two_of_le_pow (f := fun ω => gRes b E X ω α (phys y) * tGap b E X ω γ δ +
      tGap b E X ω α (phys y) * gRes b E X ω ε ε) ((hGm.eval_matrix.mul hTm.eval_matrix).add
      (hTm.eval_matrix.mul hGm.eval_matrix)) (by norm_num : (0 : ℝ) ≤ 2) 3 (by norm_num) hm6
      (fun ω => ?_)).integrable one_le_two
    have h1 := norm_entry_le' (gRes b E X ω) α (phys y)
    have h2 := (norm_entry_le' (tGap b E X ω) γ δ).trans (norm_tGap_le b E X ω)
    have h3 := (norm_entry_le' (tGap b E X ω) α (phys y)).trans (norm_tGap_le b E X ω)
    have h4 := norm_entry_le' (gRes b E X ω) ε ε
    have hg := norm_nonneg (gRes b E X ω)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have : ‖gRes b E X ω α (phys y)‖ * ‖tGap b E X ω γ δ‖ ≤ ‖gRes b E X ω‖ * ‖gRes b E X ω‖ ^ 2 :=
      mul_le_mul h1 h2 (norm_nonneg _) hg
    have : ‖tGap b E X ω α (phys y)‖ * ‖gRes b E X ω ε ε‖ ≤ ‖gRes b E X ω‖ ^ 2 * ‖gRes b E X ω‖ :=
      mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
    nlinarith
  have e : (fun ω => (tGap b E X ω * layerLin ω) α (phys y)) = fun ω =>
      ∑ a, tGap b E X ω α (phys a) * ω.1 0 a y +
        ∑ a, tGap b E X ω α (port a) * star (ω.2 0 0 y a) := by
    funext ω; exact FullSource.mul_layerLin_phys ω _ α y
  rw [e, integral_add (integrable_finsetSum _ fun a _ => hiA a)
    (integrable_finsetSum _ fun a _ => hiB a), integral_finsetSum _ (fun a _ => hiA a),
    integral_finsetSum _ (fun a _ => hiB a)]
  simp only [hA, hB, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun a _ => hprod _ _ _),
    ← integral_finsetSum _ (fun a _ => hprod _ _ _)]
  have hc : ∀ (f g : Fin W → ℂ) (u v : ℂ),
      ∑ i, (u * f i + v * g i) = (∑ i, f i) * u + (∑ i, g i) * v := by
    intro f g u v
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  simp only [hc]
  ring

end SD

end BlockBand.SourceProcess.CompleteSourceGap
