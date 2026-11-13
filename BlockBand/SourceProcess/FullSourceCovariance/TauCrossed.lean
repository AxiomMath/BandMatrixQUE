module

public import BlockBand.SourceProcess.FullSourceCovariance.TauTest

/-!
# The crossed term of `delta_ibp` against a trace test is `O(W⁻²)`

`crossed_trace_bound`: in the integration by parts `delta_ibp` against a trace test functional
built from a continuous map `A` with `‖A(G)‖ ≤ ‖G‖²`, the crossed term is `O(W⁻²)`, uniformly on
the bulk and for every passive `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_kHat_gRes_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖kHat b E X * gRes b E X ω‖ ≤ 1 + btFun b E X ω := by
  have := wBound_kHat_le b E X ω
  simp only [wBound] at this
  linarith [norm_nonneg (gRes b E X ω)]

/-- **The crossed term against a trace test**, `O(W⁻²)` (bulk-uniform). -/
theorem crossed_trace_bound (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ A : LayerMat W → LayerMat W, Continuous A → (∀ G, ‖A G‖ ≤ ‖G‖ ^ 2) →
      ∀ x y : Fin W → ℂ,
        ‖∑ β, ∑ γ, physVec y β * siteVar W b β γ *
            ∫ ω, (star (physVec x) ᵥ* (kHat b E X * gRes b E X ω)) γ *
              (-((W : ℂ)⁻¹ * A (gRes b E X ω) γ β)) ∂freshLaw W b‖ ≤
          C * ((W : ℝ)⁻¹) ^ 2 * (vecNorm x * vecNorm y) := by
  obtain ⟨Wi, hi⟩ := LengthUniform.integrable_poly_bulk hA hb0 hb hκ 3
  obtain ⟨C3, W3, hC3, hp⟩ := poly_eLpNorm_bulk hA hb0 hb hκ 3 (by norm_num)
  refine ⟨C3, max (max Wi W3) 1, hC3, fun W hW E hE X hX A hAc hAn x y => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWi, hW3⟩, hW1⟩ := hW
  have hWr : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  set μ := freshLaw W b
  set a := physVec x
  set c := physVec y
  set Kh := kHat b E X
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  have hB1 := fun ω => one_le_one_add_btFun b E X ω
  have hAB : ∀ ω, ‖A (gRes b E X ω)‖ ≤ (1 + btFun b E X ω) ^ 2 := fun ω =>
    (hAn _).trans (pow_le_pow_left₀ (norm_nonneg _) (norm_gRes_le_one_add b E X ω) 2)
  have ha0 := PassiveCovariance.vecNorm_nonneg a
  have hc0 := PassiveCovariance.vecNorm_nonneg c
  -- integrability of the summands
  have hXi : ∀ β γ, Integrable (fun ω => (star a ᵥ* (Kh * gRes b E X ω)) γ *
      (-((W : ℂ)⁻¹ * A (gRes b E X ω) γ β))) μ := by
    intro β γ
    have hc : Continuous fun G : LayerMat W => (star a ᵥ* (Kh * G)) γ *
        (-((W : ℂ)⁻¹ * A G γ β)) :=
      (continuous_letter_entry Kh a γ).mul
        ((continuous_const.mul ((hAc.matrix_elem γ β))).neg)
    refine hi W hWi E hE X hX _ (hc.measurable.comp hGm).aestronglyMeasurable
      (vecNorm a * (W : ℝ)⁻¹) fun ω => ?_
    obtain ⟨e1, -⟩ := letter_entry_bounds b E X ω a c γ
    have e2 : ‖-((W : ℂ)⁻¹ * A (gRes b E X ω) γ β)‖ ≤ (W : ℝ)⁻¹ * (1 + btFun b E X ω) ^ 2 := by
      rw [norm_neg, norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        ((FullSource.norm_entry_le_op _ γ β).trans (hAB ω)) (by positivity)
    rw [norm_mul]
    calc _ ≤ (vecNorm a * (1 + btFun b E X ω)) * ((W : ℝ)⁻¹ * (1 + btFun b E X ω) ^ 2) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg ha0 (by linarith [hB1 ω]))
      _ = _ := by ring
  rw [sum_sum_integral (fun β γ => c β * siteVar W b β γ) _ hXi]
  -- the pointwise form
  set M : LayerMat W → LayerMat W := fun G => (-(W : ℂ)⁻¹) • A G
  set g : LayerSample W .oneBlockOnePort → ℂ := fun ω =>
    star a ⬝ᵥ ((Kh * gRes b E X ω * diagonal (physVar W b) * M (gRes b E X ω)) *ᵥ c)
  have hpt : ∀ ω, (∑ β, ∑ γ, c β * siteVar W b β γ * ((star a ᵥ* (Kh * gRes b E X ω)) γ *
      (-((W : ℂ)⁻¹ * A (gRes b E X ω) γ β)))) = g ω := by
    intro ω
    have e : ∀ β γ, (star a ᵥ* (Kh * gRes b E X ω)) γ * (-((W : ℂ)⁻¹ * A (gRes b E X ω) γ β)) =
        (star a ᵥ* (Kh * gRes b E X ω)) γ * M (gRes b E X ω) γ β := fun β γ => by
      simp only [M, Matrix.smul_apply, smul_eq_mul, neg_mul]
    simp only [e]
    rw [crossed_mat_pt b c (physVec_port y), crossed_mat_form]
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  -- the bound
  have hMc : Continuous M := hAc.const_smul (-(W : ℂ)⁻¹)
  have hPc : Continuous fun G : LayerMat W => Kh * G * diagonal (physVar W b) * M G :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_mul hMc
  have hgc : Continuous fun G : LayerMat W =>
      star a ⬝ᵥ ((Kh * G * diagonal (physVar W b) * M G) *ᵥ c) :=
    continuous_const.dotProduct (hPc.matrix_mulVec continuous_const)
  have hgm : Measurable g := hgc.measurable.comp hGm
  set K := vecNorm a * vecNorm c * ((W : ℝ)⁻¹ * (W : ℝ)⁻¹)
  have hK : 0 ≤ K := by positivity
  have hgB : ∀ ω, ‖g ω‖ ≤ K * (1 + btFun b E X ω) ^ 3 := by
    intro ω
    have hM : ‖M (gRes b E X ω)‖ ≤ (W : ℝ)⁻¹ * (1 + btFun b E X ω) ^ 2 := by
      simp only [M]
      rw [norm_smul, norm_neg, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hAB ω) (by positivity)
    have hD := norm_diag_physVar_le (W := W) hb0 hb
    have hk := norm_kHat_gRes_le b E X ω
    have hprod : ‖Kh * gRes b E X ω * diagonal (physVar W b) * M (gRes b E X ω)‖ ≤
        (1 + btFun b E X ω) * (1 / W) * ((W : ℝ)⁻¹ * (1 + btFun b E X ω) ^ 2) := by
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      refine mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hk hD (norm_nonneg _)
        (by linarith [hB1 ω]))) hM (norm_nonneg _) (by have := hB1 ω; positivity)
    refine (norm_form_le a c _).trans ?_
    calc vecNorm a * vecNorm c * ‖Kh * gRes b E X ω * diagonal (physVar W b) * M (gRes b E X ω)‖
        ≤ vecNorm a * vecNorm c * ((1 + btFun b E X ω) * (1 / W) *
          ((W : ℝ)⁻¹ * (1 + btFun b E X ω) ^ 2)) := by gcongr
      _ = K * (1 + btFun b E X ω) ^ 3 := by simp only [K]; rw [one_div]; ring
  have h2 := hp W hW3 E hE X hX g hgm.aestronglyMeasurable K hK hgB
  refine (norm_integral_le_of hgm.aemeasurable (mul_nonneg hK hC3) h2).trans (le_of_eq ?_)
  simp only [K, a, c]
  rw [vecNorm_physVec, vecNorm_physVec]
  ring

end BlockBand.SourceProcess.FullSourceCovariance
