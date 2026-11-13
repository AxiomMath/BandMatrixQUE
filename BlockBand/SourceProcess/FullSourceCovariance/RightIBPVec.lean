module

public import BlockBand.SourceProcess.FullSourceCovariance.RightIBP

/-!
# The right integration by parts for a bilinear form `p*𝒢Vc`

Strictly passive `X`, law `layerLaw W b
.oneBlockOnePort`, any deterministic vectors `p, c` on the layer sites and any test `Ψ` with a
layer derivative. Summing `replica_right` against `p̄_α c_β`:

`E[(p*𝒢Vc)Ψ] = Σ_{β,γ} c_β σ(β,γ) E[(p*𝒢)_γ DΨ(E_{βγ})] - E[Ψ·p*𝒢S[𝒢]c]`   (`replica_right_vec`),

with `S[𝒢] = sdiag b 𝒢` the self-energy. Only the row `p*𝒢` and the form `p*𝒢S[𝒢]c` appear on
the right; for `p = K̂ᴴa` they are the bounded letters `a*K̂𝒢` (no `K` is left free).
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

theorem dotProduct_mulVec_expand (p c : LayerSite W .oneBlockOnePort → ℂ) (M : LayerMat W) (ψ : ℂ) :
    (star p ⬝ᵥ (M *ᵥ c)) * ψ = ∑ α, ∑ β, (star (p α) * c β) * (M α β * ψ) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem sdiag_form_expand (b : ℝ) (p c : LayerSite W .oneBlockOnePort → ℂ) (G : LayerMat W) (ψ : ℂ) :
    ψ * (star p ⬝ᵥ ((G * sdiag b G) *ᵥ c)) =
      ∑ α, ∑ β, ∑ γ, (star (p α) * c β * siteVar W b β γ) * (ψ * (G γ γ * G α β)) := by
  simp only [sdiag, mul_diagonal, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun γ _ => ?_
  ring

/-- **The right replica identity for a bilinear form** `p*𝒢Vc`. -/
theorem replica_right_vec {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hY : (passiveY X).PosDef) {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΨ : HasLayerDeriv Ψ DΨ) (hΨm : Measurable Ψ) (p c : LayerSite W .oneBlockOnePort → ℂ)
    (hL2 : ∀ α γ, MemLp (fun ω => gRes b E X ω α γ * Ψ ω) 2 (layerLaw W b .oneBlockOnePort))
    (hI1 : ∀ α γ N, Integrable (fun ω => gRes b E X ω α γ * DΨ ω N)
      (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ α γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) α γ)
      (layerLaw W b .oneBlockOnePort))
    (hI3 : ∀ α β γ, Integrable (fun ω => Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β))
      (layerLaw W b .oneBlockOnePort)) :
    Integrable (fun ω => (star p ⬝ᵥ ((gRes b E X ω * layerLin ω) *ᵥ c)) * Ψ ω)
        (layerLaw W b .oneBlockOnePort) ∧
    ∫ ω, (star p ⬝ᵥ ((gRes b E X ω * layerLin ω) *ᵥ c)) * Ψ ω ∂layerLaw W b .oneBlockOnePort =
      ∑ β, ∑ γ, c β * siteVar W b β γ *
          ∫ ω, (star p ᵥ* gRes b E X ω) γ * DΨ ω (Matrix.single β γ 1)
            ∂layerLaw W b .oneBlockOnePort -
        ∫ ω, Ψ ω * (star p ⬝ᵥ ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c))
          ∂layerLaw W b .oneBlockOnePort := by
  have hR := fun α β => replica_right hη hY hΨ hΨm α β (hL2 α) (hI1 α) (hI2 α)
  have e1 : (fun ω => (star p ⬝ᵥ ((gRes b E X ω * layerLin ω) *ᵥ c)) * Ψ ω) = fun ω =>
      ∑ α, ∑ β, (star (p α) * c β) * ((gRes b E X ω * layerLin ω) α β * Ψ ω) :=
    funext fun ω => dotProduct_mulVec_expand p c _ _
  have hint : ∀ α, Integrable (fun ω => ∑ β, (star (p α) * c β) *
      ((gRes b E X ω * layerLin ω) α β * Ψ ω)) (layerLaw W b .oneBlockOnePort) := fun α =>
    integrable_finsetSum _ fun β _ => (hR α β).1.const_mul _
  refine ⟨by rw [e1]; exact integrable_finsetSum _ fun α _ => hint α, ?_⟩
  rw [e1, integral_finsetSum _ fun α _ => hint α]
  have e5 : ∀ α, ∫ ω, ∑ β, (star (p α) * c β) * ((gRes b E X ω * layerLin ω) α β * Ψ ω)
      ∂layerLaw W b .oneBlockOnePort = ∑ β, (star (p α) * c β) * ∑ γ, siteVar W b β γ *
        ∫ ω, (gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1) -
          Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β)) ∂layerLaw W b .oneBlockOnePort := by
    intro α
    rw [integral_finsetSum _ fun β _ => (hR α β).1.const_mul _]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_const_mul, (hR α β).2]
  rw [Finset.sum_congr rfl fun α _ => e5 α]
  -- the derivative term
  have e2 : ∀ β γ, ∫ ω, (star p ᵥ* gRes b E X ω) γ * DΨ ω (Matrix.single β γ 1) ∂layerLaw W b .oneBlockOnePort =
      ∑ α, star (p α) * ∫ ω, gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1) ∂layerLaw W b .oneBlockOnePort := fun β γ => by
    have e : (fun ω => (star p ᵥ* gRes b E X ω) γ * DΨ ω (Matrix.single β γ 1)) = fun ω =>
        ∑ α, star (p α) * (gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1)) := by
      funext ω; simp only [vecMul, dotProduct, Pi.star_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => by ring
    rw [e, integral_finsetSum _ fun α _ => (hI1 α γ _).const_mul _]
    simp only [integral_const_mul]
  -- the self-energy term
  have e3 : ∫ ω, Ψ ω * (star p ⬝ᵥ ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c)) ∂layerLaw W b .oneBlockOnePort =
      ∑ α, ∑ β, ∑ γ, (star (p α) * c β * siteVar W b β γ) *
        ∫ ω, Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β) ∂layerLaw W b .oneBlockOnePort := by
    have e : (fun ω => Ψ ω * (star p ⬝ᵥ ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c))) =
        fun ω => ∑ α, ∑ β, ∑ γ, (star (p α) * c β * siteVar W b β γ) *
          (Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β)) :=
      funext fun ω => sdiag_form_expand b p c _ _
    rw [e, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      integrable_finsetSum _ fun γ _ => (hI3 α β γ).const_mul _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => integrable_finsetSum _ fun γ _ => (hI3 α β γ).const_mul _]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_finsetSum _ fun γ _ => (hI3 α β γ).const_mul _]
    simp only [integral_const_mul]
  rw [e3]
  simp only [e2]
  -- split `∫(A - B)` and rearrange the finite sums
  have e4 : ∀ α β γ, ∫ ω, (gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1) -
      Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β)) ∂layerLaw W b .oneBlockOnePort =
      ∫ ω, gRes b E X ω α γ * DΨ ω (Matrix.single β γ 1) ∂layerLaw W b .oneBlockOnePort -
        ∫ ω, Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β) ∂layerLaw W b .oneBlockOnePort := fun α β γ =>
    integral_sub (hI1 α γ _) (hI3 α β γ)
  simp only [e4, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun α _ => ?_
    ring
  · exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun γ _ => by ring

end BlockBand.SourceProcess.FullSourceCovariance
