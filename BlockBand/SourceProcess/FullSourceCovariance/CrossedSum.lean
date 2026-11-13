module

public import BlockBand.SourceProcess.FullSourceCovariance.CovOppLevel0

/-!
# The crossed sums of Level 0 as products (both signs)

* `crossed_same_sum`: `Σ_{β,γ} c_β σ(β,γ) E[f_γ g_β h_γ] = E[(Σ_β c_β g_β)·Σ_γ s_γ f_γ h_γ]`;
* `crossed_opp_sum`: `Σ_{β,γ} c_β σ(β,γ) E[f_γ ḡ_γ h̄_β] = E[(Σ_γ s_γ f_γ ḡ_γ)·Σ_β c_β h̄_β]`.

With the bulk integrability of the letters (`integrable_poly_bulk`), these give, in the sibling
module:

* **`cov_same_level1`**: `Cov(x*Δy, x'*Δy') = E[((z+E)+τ)FΨ] + E[F(x',y)·Φ]`,
  `Φ = Σ_γ s_γ (a*K̂𝒢)_γ (𝒢K̂c')_γ = a*K̂𝒢 S 𝒢K̂c'`;
* **`cov_opp_level1`**: `CrossCov = E[((z+E)+τ)F·Ψ̄] + E[Φ'·conj H]`,
  `Φ' = Σ_γ s_γ (a*K̂𝒢)_γ conj((a'*K̂𝒢)_γ) = a*K̂𝒢 S (K̂𝒢)ᴴ a'`, `H = c*𝒢K̂c' = y*𝒢₁₁Ky'`.
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

/-- The physical row of the variance profile: `s_γ = σ(phys j, γ)` (`c/W` on physical sites,
`b/W` on port sites). -/
def physVar (W : ℕ) (b : ℝ) : LayerSite W .oneBlockOnePort → ℂ
  | Sum.inl _ => (gueVar W b : ℂ)
  | Sum.inr _ => (ginVar W b : ℂ)

theorem siteVar_phys_eq (b : ℝ) (i : PhysSite W .oneBlockOnePort)
    (γ : LayerSite W .oneBlockOnePort) : siteVar W b (Sum.inl i) γ = physVar W b γ := by
  rcases γ with γ | γ <;> rfl

theorem norm_physVar_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (γ : LayerSite W .oneBlockOnePort) :
    ‖physVar W b γ‖ ≤ 1 / W := by
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; rcases γ with ⟨_, γ⟩ | ⟨_, γ⟩ <;> exact γ.elim0
  · have := norm_bVar_le (W := W) b hb0.le hb (blkOf (phys (⟨0, h⟩ : Fin W))) (blkOf γ)
    rw [← siteVar_eq_bVar] at this
    rcases γ with γ | γ <;> exact this

/-- Pointwise form of the equal-sign crossed sum. -/
theorem crossed_same_pt (b : ℝ) (c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) (f g h : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ β, ∑ γ, c β * siteVar W b β γ * (f γ * (g β * h γ)) =
      (∑ β, c β * g β) * ∑ γ, physVar W b γ * (f γ * h γ) := by
  rw [sum_layerSite, sum_layerSite (fun β => c β * g β)]
  simp only [hc, zero_mul, Finset.sum_const_zero, add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [siteVar_phys_eq]; ring

/-- Pointwise form of the opposite-sign crossed sum. -/
theorem crossed_opp_pt (b : ℝ) (c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) (f g h : LayerSite W .oneBlockOnePort → ℂ) :
    ∑ β, ∑ γ, c β * siteVar W b β γ * (f γ * (star (g γ) * star (h β))) =
      (∑ γ, physVar W b γ * (f γ * star (g γ))) * ∑ β, c β * star (h β) := by
  rw [sum_layerSite, sum_layerSite (fun β => c β * star (h β))]
  simp only [hc, zero_mul, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [siteVar_phys_eq]; ring

theorem physVec_port (y : Fin W → ℂ) (j : Fin W) : physVec y (port j) = 0 := rfl

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exchange of the finite double sum and the integral. -/
theorem sum_sum_integral (k : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort → ℂ)
    (X : LayerSite W .oneBlockOnePort → LayerSite W .oneBlockOnePort → Ω → ℂ)
    (hX : ∀ β γ, Integrable (X β γ) μ) :
    ∑ β, ∑ γ, k β γ * ∫ ω, X β γ ω ∂μ = ∫ ω, ∑ β, ∑ γ, k β γ * X β γ ω ∂μ := by
  rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun γ _ => (hX β γ).const_mul _]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_finsetSum _ fun γ _ => (hX β γ).const_mul _]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [integral_const_mul]

theorem crossed_same_sum (b : ℝ) (c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) (f g h : Ω → LayerSite W .oneBlockOnePort → ℂ)
    (hX : ∀ β γ, Integrable (fun ω => f ω γ * (g ω β * h ω γ)) μ) :
    ∑ β, ∑ γ, c β * siteVar W b β γ * ∫ ω, f ω γ * (g ω β * h ω γ) ∂μ =
      ∫ ω, (∑ β, c β * g ω β) * ∑ γ, physVar W b γ * (f ω γ * h ω γ) ∂μ := by
  rw [sum_sum_integral (fun β γ => c β * siteVar W b β γ) _ hX]
  exact integral_congr_ae (Eventually.of_forall fun ω => crossed_same_pt b c hc _ _ _)

theorem crossed_opp_sum (b : ℝ) (c : LayerSite W .oneBlockOnePort → ℂ)
    (hc : ∀ j, c (port j) = 0) (f g h : Ω → LayerSite W .oneBlockOnePort → ℂ)
    (hX : ∀ β γ, Integrable (fun ω => f ω γ * (star (g ω γ) * star (h ω β))) μ) :
    ∑ β, ∑ γ, c β * siteVar W b β γ * ∫ ω, f ω γ * (star (g ω γ) * star (h ω β)) ∂μ =
      ∫ ω, (∑ γ, physVar W b γ * (f ω γ * star (g ω γ))) * ∑ β, c β * star (h ω β) ∂μ := by
  rw [sum_sum_integral (fun β γ => c β * siteVar W b β γ) _ hX]
  exact integral_congr_ae (Eventually.of_forall fun ω => crossed_opp_pt b c hc _ _ _)

end Generic

/-- `‖(a*M)_γ‖ ≤ ‖a‖‖M‖`. -/
theorem norm_vecMul_apply_le (a : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W)
    (γ : LayerSite W .oneBlockOnePort) : ‖(star a ᵥ* M) γ‖ ≤ vecNorm a * ‖M‖ := by
  have e : (star a ᵥ* M) γ = star a ⬝ᵥ (M *ᵥ Pi.single γ 1) := by
    rw [dotProduct_mulVec]; simp [dotProduct, Pi.single_apply]
  have h1 : vecNorm (Pi.single γ (1 : ℂ)) = 1 := by
    simp only [vecNorm, Pi.single_apply]
    rw [Finset.sum_eq_single γ (fun y _ hy => by simp [hy]) (by simp)]; simp
  rw [e]; have := norm_form_le a (Pi.single γ 1) M; rw [h1, mul_one] at this; exact this

/-- `‖(Mv)_γ‖ ≤ ‖M‖‖v‖`. -/
theorem norm_mulVec_apply_le (M : LayerMat W) (v : LayerSite W .oneBlockOnePort → ℂ)
    (γ : LayerSite W .oneBlockOnePort) : ‖(M *ᵥ v) γ‖ ≤ ‖M‖ * vecNorm v := by
  have e : (M *ᵥ v) γ = star (Pi.single γ (1 : ℂ)) ⬝ᵥ (M *ᵥ v) := by
    simp [dotProduct, Pi.single_apply]
  have h1 : vecNorm (Pi.single γ (1 : ℂ)) = 1 := by
    simp only [vecNorm, Pi.single_apply]
    rw [Finset.sum_eq_single γ (fun y _ hy => by simp [hy]) (by simp)]; simp
  rw [e]; have := norm_form_le (Pi.single γ 1) v M; rw [h1, one_mul] at this; linarith

end BlockBand.SourceProcess.FullSourceCovariance
