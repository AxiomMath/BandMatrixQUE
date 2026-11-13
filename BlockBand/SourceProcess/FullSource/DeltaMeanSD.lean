module

public import BlockBand.SourceProcess.FullSource.DeltaReduction
public import BlockBand.Transmission.PathScalar.MeanStepLimit

/-!
# The right Schwinger–Dyson identity and the exact form of `EΔ`

Gaussian integration by parts on the right factor gives the right Schwinger–Dyson identity for
the layer resolvent, and from it the exact form of the mean of `Δ`.

* `meanSD_right_of`: Gaussian IBP (`stein_layerA_lin`, `stein_layerBconj_lin`) on the
  **right** factor, `E[(𝒢V)_{α,y}] = -(c/W)E[Tr𝒢₁₁·𝒢_{αy}] - (b/W)E[Tr𝒢₂₂·𝒢_{αy}]`, `V = layerLin`.

Proved in the sibling module from `meanSD_right_of`:

* `meanSD_right_matrix`: with `𝒢V = 1 - 𝒢H₀`,
  `1 + E·E𝒢₁₁ + E𝒢₁₁·X = -c E[⟨𝒢₁₁⟩𝒢₁₁] - b E[⟨𝒢₂₂⟩𝒢₁₁]` (the transpose-side physical mean
  equation; `meanSD_phys_matrix` is the left one).
* **`delta_mean_eq`**: `EΔ = (z+E)E[K𝒢₁₁] + c E[⟨𝒢₁₁⟩K𝒢₁₁] + b E[⟨𝒢₂₂⟩K𝒢₁₁]` exactly.
  Here `K` stays attached to the bounded letter `K𝒢₁₁`: `EΔ = E[K𝒢₁₁]K - K` and the
  right identity, multiplied by `K` on the left, absorb the right factor `K` exactly.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem mul_layerLin_phys (ω : LayerSample W .oneBlockOnePort) (G : LayerMat W)
    (α : LayerSite W .oneBlockOnePort) (y : Fin W) :
    (G * layerLin ω) α (phys y) =
      ∑ a, G α (phys a) * ω.1 0 a y + ∑ a, G α (port a) * star (ω.2 0 0 y a) := by
  rw [Matrix.mul_apply, sum_layerSite]
  simp [layerLin, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix, LayerShape.incident]

section SD
variable {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C2 C4 : ℝ}

/-- **Right Schwinger–Dyson identity** (Gaussian IBP on the right factor `V`). -/
theorem meanSD_right_of (hη : 0 < etaZ b E) (hX : (passiveY X).PosDef)
    (hm2 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (1 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C2)
    (hm4 : eLpNorm (fun ω => ‖gRes b E X ω‖) (ENNReal.ofReal (2 * (2 : ℕ)))
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C4)
    (α : LayerSite W .oneBlockOnePort) (y : Fin W) :
    ∫ ω, (gRes b E X ω * layerLin ω) α (phys y) ∂layerLaw W b .oneBlockOnePort =
      -((gueVar W b : ℂ) * ∫ ω, (∑ a, gRes b E X ω (phys a) (phys a)) * gRes b E X ω α (phys y)
        ∂layerLaw W b .oneBlockOnePort) -
      (ginVar W b : ℂ) * ∫ ω, (∑ a, gRes b E X ω (port a) (port a)) * gRes b E X ω α (phys y)
        ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  have hinv := fun ω hω => isUnit_layerMatrix_strict (E := E) hη hX ω hω
  have hGm := measurable_layerRes (W := W) E (boundaryZ b E) X
  -- entry integrability
  have hΦ : ∀ γ β, MemLp (fun ω => gRes b E X ω γ β) 2 μ := fun γ β => by
    simpa using (sd_integrability hm2 hm4 β).1 γ
  have hDi : ∀ γ β (N : LayerMat W), Integrable (fun ω => resDeriv (gRes b E X ω) γ β N) μ :=
    fun γ β N => by
      have := ((sd_integrability hm2 hm4 β).2 γ N).neg
      simpa [resDeriv] using this
  have hprod : ∀ γ β δ ε, Integrable (fun ω => gRes b E X ω γ δ * gRes b E X ω ε β) μ :=
    fun γ β δ ε => by
      have := (sd_integrability hm2 hm4 β).2 γ (Matrix.single δ ε 1)
      simpa only [one_mul, mul_single_mul_apply] using this
  -- the two IBPs
  have hA : ∀ a, ∫ ω, gRes b E X ω α (phys a) * ω.1 0 a y ∂μ =
      -((gueVar W b : ℂ) * ∫ ω, gRes b E X ω (phys a) (phys a) * gRes b E X ω α (phys y) ∂μ) := by
    intro a
    have h := stein_layerA_lin b (fun ω => gRes b E X ω α (phys a))
      (fun ω => resDeriv (gRes b E X ω) α (phys a))
      (hasLayerDeriv_resolvent_entry E (boundaryZ b E) _ hinv α (phys a)) hGm.eval_matrix
      (hΦ _ _) (hDi _ _) a y
    rw [layerA_single] at h
    have e1 : (fun ω => gRes b E X ω α (phys a) * ω.1 0 a y) =
        fun ω => ω.1 0 a y * gRes b E X ω α (phys a) := by funext ω; ring
    rw [e1, h, ← mul_neg, ← integral_neg]
    congr 1; congr 1; funext ω
    simp [resDeriv, mul_single_mul_apply, mul_comm]
  have hB : ∀ a, ∫ ω, gRes b E X ω α (port a) * star (ω.2 0 0 y a) ∂μ =
      -((ginVar W b : ℂ) * ∫ ω, gRes b E X ω (port a) (port a) * gRes b E X ω α (phys y) ∂μ) := by
    intro a
    have h := stein_layerBconj_lin b (fun ω => gRes b E X ω α (port a))
      (fun ω => resDeriv (gRes b E X ω) α (port a))
      (hasLayerDeriv_resolvent_entry E (boundaryZ b E) _ hinv α (port a)) hGm.eval_matrix
      (hΦ _ _) (hDi _ _) y a
    rw [upperB_single] at h
    have e1 : (fun ω => gRes b E X ω α (port a) * star (ω.2 0 0 y a)) =
        fun ω => star (ω.2 0 0 y a) * gRes b E X ω α (port a) := by funext ω; ring
    rw [e1, h, ← mul_neg, ← integral_neg]
    congr 1; congr 1; funext ω
    simp [resDeriv, mul_single_mul_apply, mul_comm]
  have hiA : ∀ a, Integrable (fun ω => gRes b E X ω α (phys a) * ω.1 0 a y) μ := fun a => by
    have := (memLp_layer_A b a y).integrable_mul (hΦ α (phys a))
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have hiB : ∀ a, Integrable (fun ω => gRes b E X ω α (port a) * star (ω.2 0 0 y a)) μ := fun a => by
    have := (memLp_layer_B b y a).star.integrable_mul (hΦ α (port a))
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_comm])
  have e : (fun ω => (gRes b E X ω * layerLin ω) α (phys y)) = fun ω =>
      ∑ a, gRes b E X ω α (phys a) * ω.1 0 a y +
        ∑ a, gRes b E X ω α (port a) * star (ω.2 0 0 y a) := by
    funext ω; exact mul_layerLin_phys ω _ α y
  rw [e, integral_add (integrable_finsetSum _ fun a _ => hiA a)
    (integrable_finsetSum _ fun a _ => hiB a), integral_finsetSum _ (fun a _ => hiA a),
    integral_finsetSum _ (fun a _ => hiB a)]
  simp only [hA, hB, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [← integral_finsetSum _ (fun a _ => hprod _ _ _ _),
    ← integral_finsetSum _ (fun a _ => hprod _ _ _ _)]
  simp only [Finset.sum_mul]
  ring

end SD

/-- `(𝒢H₀)_{x,y}` on the physical block (`H₀ = [[-E - X, 0], [0, z]]`), right action. -/
theorem H0_phys_right (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (G : LayerMat W) (x y : Fin W) :
    (G * layerMatrix .oneBlockOnePort E z (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0)
      (phys x) (phys y) = -(E : ℂ) * G (phys x) (phys y) - ∑ k, G (phys x) (phys k) * X k y := by
  rw [Matrix.mul_apply, sum_layerSite]
  simp [layerMatrix, bondMatrix, Matrix.one_apply,
    BlockBand.Internal.Contracts.Layers.blockDiag, mul_sub, Finset.sum_sub_distrib]
  ring

theorem ae_mul_layerLin {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef) :
    ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, gRes b E X ω * layerLin ω =
      1 - gRes b E X ω * layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  filter_upwards [ae_layer_herm b] with ω hω
  have hu := isUnit_layerMatrix_strict hη hX ω hω
  have hH : gRes b E X ω * layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [layerMatrix_eq_add, Matrix.mul_add] at hH
  rw [← hH]; abel

end BlockBand.SourceProcess.FullSource
