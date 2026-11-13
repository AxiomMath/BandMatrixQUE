module

public import BlockBand.Layers.WeightedLayerWard
public import BlockBand.Internal.Contracts.LayersOnePort

/-!
# The one-port weighted trace–matrix covariance

Proves `LayersOnePort.OnePortWeightedCovarianceContract`: the covariance step of the proof of the
weighted layer lemma, equivalently the clause of the passive bounds lemma at `Y = 0`, for the
one-block one-port layer.

Setting (that of the contract): `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`,
`E ∈ bulkInterval κ`, a deterministic Hermitian `X` (`W × W`) placed on the physical sites by
`onePortLift`, `𝒢 = onePortResolvent b E X`, `𝒦 = onePortWeight b E X = diag(z - X, 0)`,
deterministic `P, Q` with `‖P‖, ‖Q‖ ≤ 1`. Norms: `ℓ²` operator norm
(`Matrix.Norms.L2Operator`); expectations entrywise (`matrixExpect`).

Proof.
1. `onePortResolvent b E X = layerResolvent .oneBlockOnePort E z (onePortLift X)` (by
   definition), `onePortLift X` is Hermitian (`opc_lift_isHermitian`), and
   `𝒦* = wlKh (z - onePortLift X)*` (`opc_weight_conjTranspose`).
2. On `bulkInterval κ`, `Im z ≥ η₀(b, κ) > 0`, `|z| ≤ 3`, `|E| ≤ 2` (`wl_bulk`), so
   `wl_cov_weighted` at `σ = .oneBlockOnePort` gives `‖Cov(g, Q𝒢) 𝒦*‖ ≤ C W⁻²`.
3. `‖𝒢‖ ≤ F` with `‖F‖_{L²} ≤ C₂` (`wl_moment_setup`, `q = 2`), so `g`, `Q𝒢` and `g Q𝒢` are
   Bochner integrable (`|g| ≤ 4‖𝒢‖`, `‖Q𝒢‖ ≤ ‖𝒢‖`).
4. Right multiplication by the deterministic `𝒦*` is a continuous linear map
   (`opc_matrixExpect_mul_right`), hence `Cov(g, Q𝒢𝒦*) = Cov(g, Q𝒢) 𝒦*` with all integrands
   integrable.

Inputs: `Inputs.ConditionalBlockGUECount` only (through `wl_cov_weighted` and
`wl_moment_setup`, i.e. `gaussianAbsorption_holds`). `Inputs.GaussianLpGradient` is not used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-- The lift `onePortLift X` of a Hermitian `X` is Hermitian. -/
theorem opc_lift_isHermitian {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : X.IsHermitian) :
    (onePortLift X).IsHermitian :=
  IsHermitian.ext fun u v => hX.apply u.2 v.2

/-- `𝒦* = wlKh (z - onePortLift X)*`: the one-port weight is `wlKh` at `K = z - X`. -/
theorem opc_weight_conjTranspose {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (onePortWeight b E X)ᴴ = wlKh (m := PortSite W .oneBlockOnePort)
      (boundaryZ b E • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ)
        - onePortLift X)ᴴ := by
  rw [← wlKh_conjTranspose]
  rfl

/-- Right multiplication by a deterministic matrix commutes with `matrixExpect`, and preserves
Bochner integrability. -/
theorem opc_matrixExpect_mul_right {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {M : Ω → Matrix ι ι ℂ} (hM : Integrable M μ) (D : Matrix ι ι ℂ) :
    Integrable (fun ω => M ω * D) μ ∧
      matrixExpect μ (fun ω => M ω * D) = matrixExpect μ M * D := by
  set T : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ D) with hT
  have hTa : ∀ N, T N = N * D := fun _ => rfl
  have hi : Integrable (fun ω => M ω * D) μ := by
    simpa only [hTa] using T.integrable_comp hM
  refine ⟨hi, ?_⟩
  rw [meq_matrixExpect_eq hi, meq_matrixExpect_eq hM]
  simpa only [hTa] using T.integral_comp_comm hM

/-- **One-port weighted trace–matrix covariance**: `LayersOnePort.OnePortWeightedCovarianceContract`,
the covariance step of the proof of the weighted layer lemma (keep `𝒢₁₁K*` inside each
covariance; the contraction in the trace–matrix lemma still gives `W⁻²`), equivalently the
clause of the passive bounds lemma at `Y = 0`, for the one-block one-port layer.

* Law/measure: `layerLaw W b .oneBlockOnePort` (`A ~ GUE_W(c/W)`, `c = 1 - 2b`,
  `B ~ Gin(b/W)` independent) at `z = z_∂(E) = boundaryZ b E`; `X` deterministic Hermitian
  (`W × W`, no bound on `‖X‖`; the conditional form `E(·|X)` follows by Fubini),
  `𝒢 = onePortResolvent b E X`, `𝒦 = onePortWeight b E X = diag(z - X, 0)`.
* Domain: `b ∈ (0, 1/2)`, `κ > 0`, `E ∈ bulkInterval κ`, `W ≥ W₀`, `X` Hermitian, `P, Q`
  deterministic matrices on the layer sites with `‖P‖, ‖Q‖ ≤ 1`.
* Norms/normalizations: `ℓ²` operator norm (`Matrix.Norms.L2Operator`);
  `g = W⁻¹ Tr(P𝒢)`, `U = Q𝒢𝒦*`; covariance `E(gU) - (Eg)(EU)` with entrywise expectations
  (`matrixExpect`).
* Conclusion: `g`, the entries of `U` and of `gU` are integrable, and
  `‖E(gU) - (Eg)(EU)‖ ≤ C W⁻²`.
* Quantifier order: `b`, `κ` first; then `C` and `W₀` (depending on `b, κ` only); then
  uniformly in `W ≥ W₀`, Hermitian `X`, `E ∈ bulkInterval κ` and `P, Q`.
* Uniformity: `C, W₀` do not depend on `W, X, E, P, Q`; in particular uniform in the unbounded
  weight `K = z - X` (the weight enters only through `wl_cov_weighted`, whose bound is uniform
  in Hermitian `X`).
* Order of limits: none (fixed `W`; the `κ → 0` regularization is internal to
  `wl_cov_weighted`).
* Inputs: `Inputs.ConditionalBlockGUECount`, through `wl_cov_weighted` and `wl_moment_setup`
  (`gaussianAbsorption_holds`), and `wl_bulk`. `Inputs.GaussianLpGradient` is not needed and is
  not a hypothesis. -/
theorem onePortWeightedCovariance_holds (hcount : ConditionalBlockGUECount) :
    OnePortWeightedCovarianceContract := by
  intro b hb0 hb1 κ hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨Cw, Ww, -, hcov⟩ := wl_cov_weighted hcount hb0 hb1 hη₀
  obtain ⟨C2, W2, -, hmom⟩ := wl_moment_setup hcount hb0 hb1 hη₀ (q := 2) (by norm_num)
  refine ⟨Cw, max Ww W2, ?_⟩
  intro W hW hWW X hX E hE P Q hP hQ
  dsimp only
  have hWw : Ww ≤ W := (le_max_left _ _).trans hWW
  have hW2 : W2 ≤ W := (le_max_right _ _).trans hWW
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  have hXl : (onePortLift X).IsHermitian := opc_lift_isHermitian hX
  rw [opc_weight_conjTranspose]
  unfold onePortResolvent
  set z := boundaryZ b E with hzdef
  set Xl := onePortLift X with hXldef
  set μ := layerLaw W b .oneBlockOnePort with hμ
  set Kh := wlKh (m := PortSite W .oneBlockOnePort)
    (z • (1 : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) - Xl)ᴴ
    with hKh
  have := bond_isProbabilityMeasure_layerLaw W b .oneBlockOnePort
  obtain ⟨-, hF⟩ := hmom W hW hW2 .oneBlockOnePort Xl hXl E z hz hzM
  -- integrability of `‖𝒢‖` and `‖𝒢‖²`
  set 𝒢 := fun ω => layerResolvent .oneBlockOnePort E z Xl ω with h𝒢
  have hGm : Measurable 𝒢 := measurable_layerResolvent .oneBlockOnePort E z Xl
  set F := wlF (σ := .oneBlockOnePort) E z Xl with hFdef
  have hFmem : MemLp F 2 μ := by
    have h1 : MemLp F (ENNReal.ofReal 2) μ :=
      memLp_iff.mpr (lt_of_le_of_lt hF ENNReal.ofReal_lt_top)
    simpa using h1
  have hGF : ∀ ω, ‖𝒢 ω‖ ≤ F ω := fun ω => by
    have hg0 := norm_nonneg (𝒢 ω)
    have hl0 := norm_nonneg (wlLam ω)
    change ‖𝒢 ω‖ ≤ 1 + 6 * ((1 + ‖wlLam ω‖) * ‖𝒢 ω‖)
    nlinarith
  have hG2 : Integrable (fun ω => ‖𝒢 ω‖ ^ 2) μ := by
    refine Integrable.mono' hFmem.integrable_sq ((hGm.norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGF ω) 2
  have hG1 : Integrable (fun ω => ‖𝒢 ω‖) μ := by
    have hd : Integrable (fun ω => 1 + ‖𝒢 ω‖ ^ 2) μ := (integrable_const (1 : ℝ)).add hG2
    refine Integrable.mono' hd hGm.norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    nlinarith [sq_nonneg (‖𝒢 ω‖ - 1), norm_nonneg (𝒢 ω)]
  -- the trace `g`, the matrix `Q𝒢` and their product
  set f : LayerSample W .oneBlockOnePort → ℂ := fun ω => (W : ℂ)⁻¹ * (P * 𝒢 ω).trace with hfdef
  set V : LayerSample W .oneBlockOnePort →
      Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
    fun ω => Q * 𝒢 ω with hVdef
  have hfm : Measurable f :=
    (continuous_const.mul ((continuous_const.matrix_mul continuous_id).matrix_trace)).measurable.comp
      hGm
  have hVm : Measurable V := (continuous_const.matrix_mul continuous_id).measurable.comp hGm
  have hV_le : ∀ ω, ‖V ω‖ ≤ ‖𝒢 ω‖ := fun ω => (norm_mul_le _ _).trans (by
    calc ‖Q‖ * ‖𝒢 ω‖ ≤ 1 * ‖𝒢 ω‖ := by gcongr
      _ = ‖𝒢 ω‖ := one_mul _)
  have hf_le : ∀ ω, ‖f ω‖ ≤ 4 * ‖𝒢 ω‖ := fun ω => by
    refine (tcv_tr_le (σ := .oneBlockOnePort) hW (P * 𝒢 ω)).trans ?_
    gcongr
    calc ‖P * 𝒢 ω‖ ≤ ‖P‖ * ‖𝒢 ω‖ := norm_mul_le _ _
      _ ≤ 1 * ‖𝒢 ω‖ := by gcongr
      _ = ‖𝒢 ω‖ := one_mul _
  have hif : Integrable f μ :=
    Integrable.mono' (hG1.const_mul 4) hfm.aestronglyMeasurable (ae_of_all _ hf_le)
  have hiV : Integrable V μ :=
    Integrable.mono' hG1 hVm.aestronglyMeasurable (ae_of_all _ hV_le)
  have hiFV : Integrable (fun ω => f ω • V ω) μ := by
    refine Integrable.mono' (hG2.const_mul 4) (hfm.smul hVm).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [norm_smul, sq]
    calc ‖f ω‖ * ‖V ω‖ ≤ (4 * ‖𝒢 ω‖) * ‖𝒢 ω‖ :=
          mul_le_mul (hf_le ω) (hV_le ω) (norm_nonneg _) (by positivity)
      _ = 4 * (‖𝒢 ω‖ * ‖𝒢 ω‖) := by ring
  -- right multiplication by the deterministic weight
  obtain ⟨hiVK, hEVK⟩ := opc_matrixExpect_mul_right hiV Kh
  obtain ⟨hiFVK, hEFVK⟩ := opc_matrixExpect_mul_right hiFV Kh
  have e : (fun ω => f ω • (V ω * Kh)) = fun ω => (f ω • V ω) * Kh :=
    funext fun ω => (smul_mul_assoc _ _ _).symm
  have hentry : ∀ {Y : LayerSample W .oneBlockOnePort →
      Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ},
      Integrable Y μ → ∀ x y, Integrable (fun ω => Y ω x y) μ := fun hY x y =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ x y :
      Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ →ₗ[ℂ] ℂ)).integrable_comp
      hY
  refine ⟨hif, hentry hiVK, fun x y => ?_, ?_⟩
  · refine (hentry hiFVK x y).congr (ae_of_all _ fun ω => ?_)
    change ((f ω • V ω) * Kh) x y = f ω * (V ω * Kh) x y
    rw [smul_mul_assoc, Matrix.smul_apply, smul_eq_mul]
  · change ‖matrixExpect μ (fun ω => f ω • (V ω * Kh)) - (∫ ω, f ω ∂μ) •
      matrixExpect μ (fun ω => V ω * Kh)‖ ≤ Cw / (W : ℝ) ^ 2
    rw [e, hEFVK, hEVK, ← smul_mul_assoc, ← sub_mul]
    exact hcov W hW hWw .oneBlockOnePort Xl hXl E z hz hzM hE2 P Q hP hQ

end BlockBand.Layers
