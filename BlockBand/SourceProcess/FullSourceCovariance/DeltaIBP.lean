module

public import BlockBand.SourceProcess.FullSourceCovariance.RightIBPVec
public import BlockBand.SourceProcess.FullSource.DeltaMeanSD
public import BlockBand.Transmission.PassiveCovariance.GamNear
public import BlockBand.Transmission.SourceMixing.PassiveMeanBlock

/-!
# The exact integration by parts for `Δ` against a general test functional

* `delta_form_eq` (deterministic, at every sample where the layer matrix is invertible): the
  **right `K` weight is removed**, `x*Δy = (z+E)·a*K̂𝒢c - a*K̂𝒢Vc`. (From `𝒢H = I`,
  `H = H₀ + V`, `H₀ = diag(-E-X, z)`.)
* `sdiag_mulVec_physVec`: `S[𝒢]c = τc` for physical `c`.
* **`delta_ibp`**: at strictly passive `X`, for every test `Ψ` with a layer derivative,
  `E[(x*Δy)Ψ] = E[((z+E) + τ)FΨ] - Σ_{β,γ} c_β σ(β,γ) E[(a*K̂𝒢)_γ DΨ(E_{βγ})]`.

Only the bounded letter `K̂𝒢` appears on the right (no error is ever multiplied by `‖K‖`). With
`Ψ = Ψ₀ - EΨ₀` this is the exact first step of the weighted resolvent tensor expansion for both
covariances of `Δ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The physical self-energy scalar `τ = (c/W)Tr𝒢₁₁ + (b/W)Tr𝒢₂₂` of a layer matrix. -/
def selfTau (b : ℝ) (G : LayerMat W) : ℂ :=
  ∑ k, (gueVar W b : ℂ) * G (phys k) (phys k) + ∑ k, (ginVar W b : ℂ) * G (port k) (port k)

theorem sdiag_mulVec_physVec (b : ℝ) (G : LayerMat W) (y : Fin W → ℂ) :
    sdiag b G *ᵥ physVec y = selfTau b G • physVec y := by
  funext α
  rcases α with ⟨i, x⟩ | ⟨i, x⟩ <;> obtain rfl : i = 0 := Subsingleton.elim i 0
  · simp only [sdiag, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [sum_siteVar_phys]; rfl
  · simp [sdiag, mulVec_diagonal, physVec]

theorem blkAt_one_zero : blkAt (1 : LayerMat W) 0 0 = 1 := by
  ext x y; simp [blkAt, siteOf, Matrix.one_apply]

theorem blkAt_sub' (M N : LayerMat W) (r s : Fin 2) :
    blkAt (M - N) r s = blkAt M r s - blkAt N r s := by
  ext x y; simp [blkAt]

theorem blkAt_H0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    blkAt (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0) 0 0 = -(E : ℂ) • 1 - X ∧
    blkAt (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0) 1 0 = 0 := by
  constructor <;> ext x y <;>
    simp [blkAt, siteOf, layerMatrix, BlockBand.Internal.Contracts.Layers.blockDiag, bondMatrix,
      Matrix.one_apply, LayerShape.incident, sub_eq_add_neg]

theorem blkAt_gRes_zero (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    blkAt (gRes b E X ω) 0 0 = g11 E (boundaryZ b E) X ω := by
  ext x y; simp [blkAt, siteOf, g11, layerAt, liftX]

/-- **The right weight removed**: `x*Δy = (z+E)·a*K̂𝒢c - a*K̂𝒢Vc` wherever `𝒢H = I`. -/
theorem delta_form_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort)
    (hω : gRes b E X ω * layerLin ω = 1 - gRes b E X ω * layerMatrix .oneBlockOnePort E
      (boundaryZ b E) (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) 0)
    (x y : Fin W → ℂ) :
    bilinear x (freshDelta b E X ω) y =
      (boundaryZ b E + E) * (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) -
        star (physVec x) ⬝ᵥ ((kHat b E X * (gRes b E X ω * layerLin ω)) *ᵥ physVec y) := by
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set g := g11 E (boundaryZ b E) X ω
  obtain ⟨h00, h10⟩ := blkAt_H0 b E X
  have e1 : blkAt (kHat b E X * gRes b E X ω) 0 0 = K * g := by
    rw [(SourceMixing.blkAt_kHat_mul_zero b E X _).1, blkAt_gRes_zero]
  have e2 : blkAt (kHat b E X * (gRes b E X ω * layerLin ω)) 0 0 =
      K * (1 - g * (-(E : ℂ) • 1 - X)) := by
    rw [(SourceMixing.blkAt_kHat_mul_zero b E X _).1, hω, blkAt_sub', blkAt_one_zero, blkAt_mul,
      Fin.sum_univ_two, h00, h10, Matrix.mul_zero, add_zero, blkAt_gRes_zero]
  rw [form_physVec, form_physVec, e1, e2, FullSource.freshDelta_eq, ← bilinear_smul,
    ← PassiveCovariance.bilinear_sub]
  congr 1
  have hK : (boundaryZ b E + E) • (1 : Matrix (Fin W) (Fin W) ℂ) + (-(E : ℂ) • 1 - X) = K := by
    simp only [K, add_smul, neg_smul]; abel
  calc K * g * K - K = K * g * ((boundaryZ b E + E) • 1 + (-(E : ℂ) • 1 - X)) - K := by rw [hK]
    _ = _ := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_sub K 1, Matrix.mul_one,
        Matrix.mul_assoc K g]
      abel

/-- **The exact Δ integration by parts** against a general test functional (strict `X`). -/
theorem delta_ibp {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosDef)
    {Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {DΨ : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΨ : HasLayerDeriv Ψ DΨ) (hΨm : Measurable Ψ) (x y : Fin W → ℂ)
    (hL2 : ∀ α γ, MemLp (fun ω => gRes b E X ω α γ * Ψ ω) 2 (layerLaw W b .oneBlockOnePort))
    (hI1 : ∀ α γ N, Integrable (fun ω => gRes b E X ω α γ * DΨ ω N)
      (layerLaw W b .oneBlockOnePort))
    (hI2 : ∀ α γ N, Integrable (fun ω => Ψ ω * (gRes b E X ω * N * gRes b E X ω) α γ)
      (layerLaw W b .oneBlockOnePort))
    (hI3 : ∀ α β γ, Integrable (fun ω => Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β))
      (layerLaw W b .oneBlockOnePort))
    (hF : Integrable (fun ω => (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) *
      Ψ ω) (layerLaw W b .oneBlockOnePort)) :
    ∫ ω, bilinear x (freshDelta b E X ω) y * Ψ ω ∂layerLaw W b .oneBlockOnePort =
      ∫ ω, ((boundaryZ b E + E) + selfTau b (gRes b E X ω)) *
          (star (physVec x) ⬝ᵥ ((kHat b E X * gRes b E X ω) *ᵥ physVec y)) * Ψ ω
          ∂layerLaw W b .oneBlockOnePort -
        ∑ β, ∑ γ, physVec y β * siteVar W b β γ *
          ∫ ω, (star (physVec x) ᵥ* (kHat b E X * gRes b E X ω)) γ * DΨ ω (Matrix.single β γ 1)
            ∂layerLaw W b .oneBlockOnePort := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  set Kh := kHat b E X
  set a := physVec x
  set c := physVec y
  set p := Khᴴ *ᵥ a
  set F := fun ω => star a ⬝ᵥ ((Kh * gRes b E X ω) *ᵥ c)
  obtain ⟨hint, hvec⟩ := replica_right_vec hη hY hΨ hΨm p c hL2 hI1 hI2 hI3
  have ep : ∀ (M : LayerMat W), star a ⬝ᵥ ((Kh * M) *ᵥ c) = star p ⬝ᵥ (M *ᵥ c) := fun M =>
    star_dotProduct_mul_mulVec Kh M a c
  have epr : ∀ (M : LayerMat W), star p ᵥ* M = star a ᵥ* (Kh * M) := fun M => by
    rw [star_mulVec, conjTranspose_conjTranspose, vecMul_vecMul]
  -- the a.s. form of `x*Δy`
  have hae : ∀ᵐ ω ∂layerLaw W b .oneBlockOnePort, bilinear x (freshDelta b E X ω) y * Ψ ω =
      (boundaryZ b E + E) * (F ω * Ψ ω) -
        (star p ⬝ᵥ ((gRes b E X ω * layerLin ω) *ᵥ c)) * Ψ ω := by
    filter_upwards [FullSource.ae_mul_layerLin hb h1 h2 hY] with ω hω
    rw [delta_form_eq b E X ω hω x y, ep, ep]
    simp only [F, ep]
    ring
  -- `τFΨ` is integrable and equals the self-energy term
  have eS : ∀ ω, Ψ ω * (star p ⬝ᵥ ((gRes b E X ω * sdiag b (gRes b E X ω)) *ᵥ c)) =
      selfTau b (gRes b E X ω) * F ω * Ψ ω := fun ω => by
    rw [← mulVec_mulVec, sdiag_mulVec_physVec, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp only [F, ep]; ring
  have hS : Integrable (fun ω => selfTau b (gRes b E X ω) * F ω * Ψ ω)
      (layerLaw W b .oneBlockOnePort) := by
    have e : (fun ω => selfTau b (gRes b E X ω) * F ω * Ψ ω) = fun ω =>
        ∑ α, ∑ β, ∑ γ, (star (p α) * c β * siteVar W b β γ) *
          (Ψ ω * (gRes b E X ω γ γ * gRes b E X ω α β)) := by
      funext ω; rw [← eS, sdiag_form_expand]
    rw [e]
    exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      integrable_finsetSum _ fun γ _ => (hI3 α β γ).const_mul _
  rw [integral_congr_ae hae, integral_sub (hF.const_mul _) hint, integral_const_mul, hvec]
  simp only [eS, epr]
  have e3 : (fun ω => ((boundaryZ b E + E) + selfTau b (gRes b E X ω)) * F ω * Ψ ω) =
      fun ω => (boundaryZ b E + E) * (F ω * Ψ ω) + selfTau b (gRes b E X ω) * F ω * Ψ ω := by
    funext ω; ring
  rw [e3, integral_add (hF.const_mul _) hS, integral_const_mul]
  ring

end BlockBand.SourceProcess.FullSourceCovariance
