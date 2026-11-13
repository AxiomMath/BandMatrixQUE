module

public import BlockBand.Transmission.PassiveCovariance.SdSite

/-!
# The right Gaussian integration by parts with a general test functional

At strictly passive `X` (`Y ≻ 0`), law `layerLaw W b .oneBlockOnePort` (`= freshLaw`), `z = z_∂(E)`,
`η > 0`, `V = layerLin ω` the Gaussian part of the layer matrix, and any test `Ψ` with a
`ℂ`-linear layer derivative `DΨ`:

`E[(𝒢V)_{αβ} Ψ] = Σ_γ σ(β,γ) E[𝒢_{αγ} DΨ(E_{βγ}) - Ψ 𝒢_{γγ} 𝒢_{αβ}]`   (`replica_right`).

This is the right-hand analogue of `replica_site_gen` (which integrates the *left*
factor `V` by parts) and the general-`Ψ` version of `FullSource.meanSD_right_of` (`Ψ = 1`).
It is derived from `replica_site_gen` on the side `𝒢ᴴ` with the test `conj Ψ`:
`conj((𝒢V)_{αβ}) = (V𝒢ᴴ)_{βα}` at Hermitian samples, and `conj Ψ` has derivative
`N ↦ conj(DΨ(Nᴴ))` (`starDeriv`, `hasLayerDeriv_star`).

The three integrability hypotheses are those of `replica_site_gen`, in the right orientation;
in the applications they follow from `‖𝒢‖ ∈ L⁴`, `Ψ ∈ L⁴` and `DΨ(N) ∈ L²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `N ↦ conj(D(Nᴴ))`: the layer derivative of `conj Ψ` when `D` is that of `Ψ`. -/
def starDeriv (D : LayerMat W →ₗ[ℂ] ℂ) : LayerMat W →ₗ[ℂ] ℂ where
  toFun N := star (D Nᴴ)
  map_add' N N' := by simp [Matrix.conjTranspose_add]
  map_smul' c N := by simp [Matrix.conjTranspose_smul]

theorem starDeriv_apply (D : LayerMat W →ₗ[ℂ] ℂ) (N : LayerMat W) :
    starDeriv D N = star (D Nᴴ) := rfl

theorem hasLayerDeriv_star {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {D : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ} (h : HasLayerDeriv Ψ D) :
    HasLayerDeriv (fun ω => star (Ψ ω)) (fun ω => starDeriv (D ω)) := by
  intro ω hω Δ hΔ
  have h1 := (h ω hω Δ hΔ).star
  have hL := (layerLin_isHermitian Δ hΔ).eq
  show HasDerivAt _ (star (D ω (layerLin Δ)ᴴ)) 0
  rw [hL]; exact h1

theorem integrable_star_fun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : Integrable (fun ω => star (f ω)) μ :=
  memLp_one_iff_integrable.1 (memLp_one_iff_integrable.2 hf).star

theorem star_siteVar (b : ℝ) (β γ : LayerSite W .oneBlockOnePort) :
    star (siteVar W b β γ) = siteVar W b β γ := by
  rcases β with β | β <;> rcases γ with γ | γ <;> simp [siteVar]

/-- **The right replica identity** for a general test functional. -/
theorem replica_right {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΨ : HasLayerDeriv Ψ DΨ) (hΨm : Measurable Ψ) (α β : LayerSite W .oneBlockOnePort)
    (hL2 : ∀ γ, MemLp (fun ω => gRes b E X ω α γ * Ψ ω) 2 (layerLaw W b .oneBlockOnePort))
    (hI1 : ∀ γ N, Integrable (fun ω => gRes b E X ω α γ * DΨ ω N) (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) α γ)
      (layerLaw W b .oneBlockOnePort)) :
    Integrable (fun ω => (gRes b E X ω * layerLin ω) α β * Ψ ω) (layerLaw W b .oneBlockOnePort) ∧
    ∫ ω, (gRes b E X ω * layerLin ω) α β * Ψ ω ∂layerLaw W b .oneBlockOnePort =
      ∑ γ, siteVar W b β γ * ∫ ω, (gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1) -
          Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β)) ∂layerLaw W b .oneBlockOnePort := by
  set μ := layerLaw W b .oneBlockOnePort
  set G := gSide b E X true
  have hGe : ∀ ω γ δ, G ω γ δ = star (gRes b E X ω δ γ) := fun ω γ δ => by
    simp [G, gSide, conjTranspose_apply]
  have hGNG : ∀ ω (N : LayerMat W) γ δ, (G ω * N * G ω) γ δ =
      star ((gRes b E X ω * Nᴴ * gRes b E X ω) δ γ) := fun ω N γ δ => by
    have : G ω * N * G ω = (gRes b E X ω * Nᴴ * gRes b E X ω)ᴴ := by
      simp [G, gSide, conjTranspose_mul, Matrix.mul_assoc]
    rw [this, conjTranspose_apply]
  have h := replica_site_gen b G (hasLayerDeriv_gSide hη hY true) (measurable_gSide b E X true)
    (Ψ := fun ω => star (Ψ ω)) (hasLayerDeriv_star hΨ)
    (continuous_star.measurable.comp hΨm : Measurable fun ω => star (Ψ ω)) β α
    (fun γ => by
      have e : (fun ω => G ω γ α * star (Ψ ω)) = star (fun ω => gRes b E X ω α γ * Ψ ω) := by
        funext ω; simp [hGe]
      rw [e]; exact (hL2 γ).star)
    (fun γ N => by
      have e : (fun ω => G ω γ α * starDeriv (DΨ ω) N) =
          fun ω => star (gRes b E X ω α γ * DΨ ω Nᴴ) := by
        funext ω; rw [hGe, starDeriv_apply, star_mul']
      rw [e]; exact integrable_star_fun (hI1 γ Nᴴ))
    (fun γ N => by
      have e : (fun ω => star (Ψ ω) * (G ω * N * G ω) γ α) =
          fun ω => star (Ψ ω * (gRes b E X ω * Nᴴ * gRes b E X ω) α γ) := by
        funext ω; simp [hGNG]
      rw [e]; exact integrable_star_fun (hI2 γ Nᴴ))
  -- at Hermitian samples, `(V𝒢ᴴ)_{βα} conj Ψ = conj((𝒢V)_{αβ} Ψ)`
  have hae : ∀ᵐ ω ∂μ, (layerLin ω * G ω) β α * star (Ψ ω) =
      star ((gRes b E X ω * layerLin ω) α β * Ψ ω) := by
    filter_upwards [PathScalar.ae_layer_herm b] with ω hω
    have hL := (layerLin_isHermitian ω hω).eq
    have : layerLin ω * G ω = (gRes b E X ω * layerLin ω)ᴴ := by
      simp [G, gSide, conjTranspose_mul, hL]
    rw [this, conjTranspose_apply, star_mul']
  obtain ⟨hint, heq⟩ := h
  have hint' : Integrable (fun ω => (gRes b E X ω * layerLin ω) α β * Ψ ω) μ := by
    have := integrable_star_fun (hint.congr hae)
    simpa using this
  refine ⟨hint', ?_⟩
  have hl : ∫ ω, (layerLin ω * G ω) β α * star (Ψ ω) ∂μ =
      star (∫ ω, (gRes b E X ω * layerLin ω) α β * Ψ ω ∂μ) := by
    rw [integral_congr_ae hae]
    exact integral_conj
  rw [hl] at heq
  have hr : ∀ γ, ∫ ω, (G ω γ α * starDeriv (DΨ ω) (Matrix.single γ β 1) -
        star (Ψ ω) * (G ω γ γ * G ω β α)) ∂layerLaw W b .oneBlockOnePort =
      star (∫ ω, (gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1) -
        Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β)) ∂μ) := fun γ => by
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans integral_conj
    simp only [hGe]
    show _ = star _
    rw [star_sub, star_mul', star_mul', star_mul', starDeriv_apply, conjTranspose_single, star_one]
  simp only [hr] at heq
  have := congrArg star heq
  rw [star_star, star_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [star_mul', star_star, star_siteVar]

end BlockBand.SourceProcess.FullSourceCovariance
