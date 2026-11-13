module

public import BlockBand.SourceProcess.FullSourceCovariance.FirstLp

/-!
# The self-energy scalar as a test functional; `Ω̄ = O(δ₀ + W⁻²)`

The mean of the self-energy scalar `τ` is close to `-(z+E)`, and `τ` is a test functional with an
explicit layer derivative.

* **`omegaBar_close hA`**: `|(z+E) + Eτ| ≤ C(δ₀ + W⁻²)` for strictly
  passive `X` with `δ₀ ≤ d₁`, uniformly on `bulkInterval κ`. Here `Eτ = cE⟨𝒢₁₁⟩ + bE⟨𝒢₂₂⟩`
  (`selfTau_eq_traces`) and `z + E = -(1-b)a`, so `(z+E) + Eτ = c(v - a) + b(u - a)`
  (`meanScalars_close`; the algebra of `deltaMean_strict`).
* `tauDer D G : N ↦ -τ_D(G N G)` and **`hasLayerDeriv_tauD`**: the layer derivative of
  `ω ↦ τ_D(𝒢) + κ` at `Y ≻ 0`; `tauDer_single`: `Dτ(E_{βγ}) = -W⁻¹(𝒢D𝒢)_{γβ}`;
  `starDeriv_tauDer_single`: `Dτ̄(E_{βγ}) = -W⁻¹((𝒢D𝒢)ᴴ)_{γβ}`.
* `crossed_mat_pt`, `crossed_mat_form`: `Σ_{β,γ} c_βσ(β,γ) f_γ M_{γβ} = a*K̂𝒢·diag(s)·M c` for
  `f = a*K̂𝒢`, physical `c` — the crossed term of `delta_ibp` against a trace test.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem selfTau_eq_traces {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    selfTau b (gRes b E X ω) = ((1 - 2 * b : ℝ) : ℂ) * physTr b E X ω + (b : ℂ) * portTr b E X ω := by
  simp only [physTr, portTr]
  rw [selfTau, trace_letter0, trace_letter3, gueVar_cast hb, ginVar_cast hb0, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> ring

/-- **`Ω̄ = (z+E) + Eτ = O(δ₀ + W⁻²)`** (strictly passive `X`, bulk-uniform). -/
theorem omegaBar_close (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (d₁ C : ℝ) (W₀ : ℕ), 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDistance0 b E X ≤ d₁ →
        ‖(boundaryZ b E + E) + ∫ ω, selfTau b (gRes b E X ω) ∂freshLaw W b‖ ≤
          C * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hsc⟩ := FullSource.meanScalars_close hA hb0 hb hκ
  obtain ⟨Wi, hi⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 1
  refine ⟨d₁, Cs, max (max Ws Wi) 1, hd₁, hCs, fun W hW E hE X hX hδ => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWs, hWi⟩, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  set μ := freshLaw W b
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hent : ∀ α β, Integrable (fun ω => gRes b E X ω α β) μ := fun α β =>
    hi W hWi E hE X hX.posSemidef _ hGm.eval_matrix.aestronglyMeasurable 1 fun ω => by
      rw [one_mul, pow_one]; exact norm_entry_le_btFun b E X ω α β
  have hP : Integrable (fun ω => physTr b E X ω) μ := by
    simp only [physTr, trace_letter0]
    exact (integrable_finsetSum _ fun k _ => hent _ _).const_mul _
  have hQ : Integrable (fun ω => portTr b E X ω) μ := by
    simp only [portTr, trace_letter3]
    exact (integrable_finsetSum _ fun k _ => hent _ _).const_mul _
  set v := ∫ ω, physTr b E X ω ∂μ
  set u := ∫ ω, freshPortTrace b E X ω ∂μ
  have hu' : ∫ ω, portTr b E X ω ∂μ = u := FullSource.integral_portTr_eq hb hW1 X
  set c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
  have hτ : ∫ ω, selfTau b (gRes b E X ω) ∂μ = c * v + (b : ℂ) * u := by
    simp only [selfTau_eq_traces hb0 hb]
    rw [integral_add (hP.const_mul _) (hQ.const_mul _), integral_const_mul c,
      integral_const_mul (b : ℂ), hu']
  obtain ⟨hv, hu⟩ := hsc W hWs E hE X hX hδ
  have hΩ : (boundaryZ b E + E) + (c * v + (b : ℂ) * u) =
      c * (v - matchedA E) + (b : ℂ) * (u - matchedA E) := by
    rw [FullSource.boundaryZ_add_E h1 h2]; simp only [c]; push_cast; ring
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hnc : ‖c‖ = 1 - 2 * b := by simp only [c, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hnb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  set δw := jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2
  have hδw : 0 ≤ δw := add_nonneg (norm_nonneg _) (by positivity)
  rw [hτ, hΩ]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hnc, hnb]
  have : (1 - 2 * b) * ‖v - matchedA E‖ + b * ‖u - matchedA E‖ ≤
      (1 - 2 * b) * (Cs * δw) + b * (Cs * δw) :=
    add_le_add (mul_le_mul_of_nonneg_left hv hc0) (mul_le_mul_of_nonneg_left hu hb0.le)
  have h3 : 0 ≤ Cs * δw := mul_nonneg hCs hδw
  nlinarith

/-- `N ↦ -τ_D(G N G)`, the layer derivative of `τ_D(𝒢)`. -/
def tauDer (D G : LayerMat W) : LayerMat W →ₗ[ℂ] ℂ where
  toFun N := -tauD D (G * N * G)
  map_add' N N' := by
    simp only [Matrix.mul_add, Matrix.add_mul, tauD, Matrix.trace_add]; ring
  map_smul' c N := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, tauD, Matrix.trace_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem tauDer_apply (D G N : LayerMat W) : tauDer D G N = -tauD D (G * N * G) := rfl

theorem hasLayerDeriv_tauD {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) (D : LayerMat W) (κ : ℂ) :
    HasLayerDeriv (fun ω => tauD D (gRes b E X ω) + κ) (fun ω => tauDer D (gRes b E X ω)) := by
  intro ω hω Δ _
  have h := hasDerivAt_layerResolvent E (boundaryZ b E) _ ω Δ
    (isUnit_layerMatrix_strict hη hY ω hω)
  have h2 := (((tauDCLM D).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h).add_const κ
  show HasDerivAt (fun s : ℝ => tauD D (gRes b E X (ω + (s : ℂ) • Δ)) + κ)
    (tauDer D (gRes b E X ω) (layerLin Δ)) 0
  convert h2 using 1
  · funext s; rfl
  · rw [ContinuousLinearMap.coe_restrictScalars', map_neg, tauDCLM_apply, tauDer_apply]

theorem tauDer_single (D G : LayerMat W) (β γ : LayerSite W .oneBlockOnePort) :
    tauDer D G (Matrix.single β γ 1) = -((W : ℂ)⁻¹ * (G * D * G) γ β) := by
  rw [tauDer_apply, tauD]
  congr 2
  rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, trace_single_mul, one_smul, Matrix.mul_assoc]

theorem starDeriv_tauDer_single (D G : LayerMat W) (β γ : LayerSite W .oneBlockOnePort) :
    starDeriv (tauDer D G) (Matrix.single β γ 1) = -((W : ℂ)⁻¹ * ((G * D * G)ᴴ) γ β) := by
  rw [starDeriv_apply, Matrix.conjTranspose_single, star_one, tauDer_single, star_neg, star_mul',
    conjTranspose_apply]
  simp

/-- Only physical rows contribute: `Σ_{β,γ} c_βσ(β,γ) f_γ M_{γβ} = Σ_γ s_γ f_γ (Mc)_γ`. -/
theorem crossed_mat_pt (b : ℝ) (c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) (f : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W) :
    ∑ β, ∑ γ, c β * siteVar W b β γ * (f γ * M γ β) =
      ∑ γ, physVar W b γ * (f γ * (M *ᵥ c) γ) := by
  have key : ∀ β γ, c β * siteVar W b β γ = c β * physVar W b γ := by
    intro β γ
    rcases β with i | ⟨i, x⟩
    · rw [siteVar_phys_eq]
    · obtain rfl : i = 0 := Subsingleton.elim i 0
      have : c (Sum.inr (0, x)) = 0 := hc x
      rw [this, zero_mul, zero_mul]
  simp only [key, mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem crossed_mat_form (b : ℝ) (a c : LayerSite W .oneBlockOnePort → ℂ) (Mk M : LayerMat W) :
    ∑ γ, physVar W b γ * ((star a ᵥ* Mk) γ * (M *ᵥ c) γ) =
      star a ⬝ᵥ ((Mk * diagonal (physVar W b) * M) *ᵥ c) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring

theorem norm_diag_physVar_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ‖diagonal (physVar W b)‖ ≤ 1 / W :=
  norm_diagonal_le _ (by positivity) fun γ => norm_physVar_le hb0 hb γ

end BlockBand.SourceProcess.FullSourceCovariance
