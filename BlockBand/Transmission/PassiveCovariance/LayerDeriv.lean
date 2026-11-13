module

public import BlockBand.Transmission.PassiveCovariance.LayerIBPHerm
public import BlockBand.Transmission.PassiveCovariance.LayerSmooth

/-!
# Linear layer derivatives and the linear-form Gaussian IBP on the fresh layer

Both `𝒢` and `𝒢*` are smooth in the Gaussian sample, and every direction `Δ` with a Hermitian
block has a Hermitian `layerLin Δ`. The derivative of a functional is therefore a `ℂ`-linear
form `D_ω` evaluated at `layerLin Δ` (`HasLayerDeriv`), and the real IBP of `LayerIBP` collapses
to:

* `stein_layerA_lin`: `E[A_xy Φ] = (c/W) E[D_ω(diag E_yx)]`;
* `stein_layerB_lin`: `E[B_xy Φ] = (b/W) E[D_ω(lowerB E_xy)]`, `lowerB M = [[0,0],[M*,0]]`;
* `stein_layerBconj_lin`: `E[B̄_xy Φ] = (b/W) E[D_ω(upperB E_xy)]`, `upperB M = [[0,M],[0,0]]`.

Calculus: `hasLayerDeriv_resolvent_entry` (`D = -(𝒢N𝒢)_{αβ}`) and
`hasLayerDeriv_resolvent_adj_entry` (`D = -(𝒢*N𝒢*)_{αβ}`) at every Hermitian sample where
the layer matrix is invertible, together with product, sum, scalar and constant rules.
`stein_layerB_herm` supplies the bond IBP with derivatives required only at
Hermitian blocks.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission
open scoped NNReal ComplexOrder Matrix.Norms.L2Operator

section Lin
variable {W : ℕ}

/-- Matrices on the layer sites. -/
abbrev LayerMat (W : ℕ) := Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ

/-- `Φ` has the `ℂ`-linear layer derivative `D`: along every sample direction `Δ` with
Hermitian block, at every sample with Hermitian block, `d/ds Φ(ω + sΔ)|₀ = D_ω(layerLin Δ)`. -/
def HasLayerDeriv (Φ : LayerSample W .oneBlockOnePort → ℂ)
    (D : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) : Prop :=
  ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian →
    ∀ Δ : LayerSample W .oneBlockOnePort, (Δ.1 0).IsHermitian →
      HasDerivAt (fun s : ℝ => Φ (ω + (s : ℂ) • Δ)) (D ω (layerLin Δ)) 0

/-- The block direction `(A ↦ M, B ↦ 0)`. -/
def dirA (M : Matrix (Fin W) (Fin W) ℂ) : LayerSample W .oneBlockOnePort := (fun _ => M, 0)

/-- The bond direction `(A ↦ 0, B ↦ M)`. -/
def dirB (M : Matrix (Fin W) (Fin W) ℂ) : LayerSample W .oneBlockOnePort := (0, fun _ _ => M)

theorem add_smul_dirA (ω : LayerSample W .oneBlockOnePort) (M : Matrix (Fin W) (Fin W) ℂ) (s : ℝ) :
    ((fun i => ω.1 i + (s : ℂ) • M), ω.2) = ω + (s : ℂ) • dirA M := by
  ext <;> simp [dirA]

theorem add_smul_dirB (ω : LayerSample W .oneBlockOnePort) (M : Matrix (Fin W) (Fin W) ℂ) (s : ℝ) :
    (ω.1, fun i j => ω.2 i j + (s : ℂ) • M) = ω + (s : ℂ) • dirB M := by
  ext <;> simp [dirB]

theorem add_smul_dirB_I (ω : LayerSample W .oneBlockOnePort) (M : Matrix (Fin W) (Fin W) ℂ) (s : ℝ) :
    (ω.1, fun i j => ω.2 i j + ((s : ℂ) * Complex.I) • M) = ω + (s : ℂ) • dirB (Complex.I • M) := by
  ext
  · simp [dirB]
  · simp [dirB]; ring

theorem hermDir_isHermitian (a c : Fin W) : (hermDir a c).IsHermitian := by
  simp [hermDir, IsHermitian, conjTranspose_add, Matrix.conjTranspose_single, add_comm]

theorem skewDir_isHermitian (a c : Fin W) : (skewDir a c).IsHermitian := by
  simp only [skewDir, IsHermitian, conjTranspose_smul, conjTranspose_sub,
    Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I]
  rw [← neg_sub, smul_neg, neg_smul, neg_neg]

/-- The block part `diag(M)` on the physical sites. -/
def layerA (M : Matrix (Fin W) (Fin W) ℂ) : LayerMat W :=
  fromBlocks (BlockBand.Internal.Contracts.Layers.blockDiag fun _ : Fin 1 => M) 0 0 0

theorem layerLin_dirA (M : Matrix (Fin W) (Fin W) ℂ) : layerLin (dirA M) = layerA M := by
  have h0 : bondMatrix LayerShape.oneBlockOnePort
      (0 : Fin 1 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) = 0 := by
    ext u v; simp [bondMatrix]
  simp only [layerLin, dirA, layerA, h0, conjTranspose_zero]

theorem layerA_add (M N : Matrix (Fin W) (Fin W) ℂ) : layerA (M + N) = layerA M + layerA N := by
  rw [layerA, layerA, layerA, fromBlocks_add]
  congr 1
  · ext u v; simp only [BlockBand.Internal.Contracts.Layers.blockDiag, Matrix.add_apply]
    split_ifs <;> simp
  · simp
  · simp
  · simp

theorem layerA_smul (c : ℂ) (M : Matrix (Fin W) (Fin W) ℂ) : layerA (c • M) = c • layerA M := by
  rw [layerA, layerA, fromBlocks_smul]
  congr 1
  · ext u v; simp only [BlockBand.Internal.Contracts.Layers.blockDiag, Matrix.smul_apply]
    split_ifs <;> simp
  · simp
  · simp
  · simp

theorem hermDir_add_I_skewDir (a c : Fin W) :
    hermDir a c + Complex.I • skewDir a c = (2 : ℂ) • Matrix.single c a 1 := by
  simp only [hermDir, skewDir, smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul]
  module

/-- **Linear-form GUE IBP on the layer**: `E[A_xy Φ] = (c/W) E[D_ω(diag E_yx)]`. -/
theorem stein_layerA_lin (b : ℝ) (Φ : LayerSample W .oneBlockOnePort → ℂ)
    (D : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) (hD : HasLayerDeriv Φ D)
    (hm : Measurable Φ) (hΦ : MemLp Φ 2 (layerLaw W b .oneBlockOnePort))
    (hDi : ∀ N, Integrable (fun ω => D ω N) (layerLaw W b .oneBlockOnePort)) (x y : Fin W) :
    ∫ ω, ω.1 0 x y * Φ ω ∂layerLaw W b .oneBlockOnePort =
      (gueVar W b : ℂ) * ∫ ω, D ω (layerA (Matrix.single y x 1)) ∂layerLaw W b .oneBlockOnePort := by
  have h := stein_layerA b Φ (fun ω => D ω (layerA (hermDir x y)))
    (fun ω => D ω (layerA (skewDir x y))) x y hm
    (fun ω hω => by
      have e : (fun s : ℝ => Φ ((fun i => ω.1 i + (s : ℂ) • hermDir x y), ω.2)) =
          fun s : ℝ => Φ (ω + (s : ℂ) • dirA (hermDir x y)) := by
        funext s; rw [add_smul_dirA]
      rw [e, ← layerLin_dirA]
      exact hD ω hω _ (hermDir_isHermitian x y))
    (fun ω hω => by
      have e : (fun s : ℝ => Φ ((fun i => ω.1 i + (s : ℂ) • skewDir x y), ω.2)) =
          fun s : ℝ => Φ (ω + (s : ℂ) • dirA (skewDir x y)) := by
        funext s; rw [add_smul_dirA]
      rw [e, ← layerLin_dirA]
      exact hD ω hω _ (skewDir_isHermitian x y))
    hΦ (hDi _) (hDi _)
  rw [h]
  have e2 : (fun ω => D ω (layerA (hermDir x y)) + Complex.I * D ω (layerA (skewDir x y))) =
      fun ω => 2 * D ω (layerA (Matrix.single y x 1)) := by
    funext ω
    rw [← smul_eq_mul, ← map_smul, ← map_add, ← layerA_smul, ← layerA_add,
      hermDir_add_I_skewDir, layerA_smul, map_smul, smul_eq_mul]
  rw [e2, integral_const_mul]
  ring

/-- The bond block `B ↦ M` (physical × port). -/
abbrev bondOf (M : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (PhysSite W .oneBlockOnePort) (PortSite W .oneBlockOnePort) ℂ :=
  bondMatrix .oneBlockOnePort (fun _ _ => M)

/-- `[[0, 0], [M*, 0]]` (the `B*` slot). -/
def lowerB (M : Matrix (Fin W) (Fin W) ℂ) : LayerMat W := fromBlocks 0 0 (bondOf M)ᴴ 0

/-- `[[0, M], [0, 0]]` (the `B` slot). -/
def upperB (M : Matrix (Fin W) (Fin W) ℂ) : LayerMat W := fromBlocks 0 (bondOf M) 0 0

theorem layerLin_dirB (M : Matrix (Fin W) (Fin W) ℂ) :
    layerLin (dirB M) = fromBlocks 0 (bondOf M) (bondOf M)ᴴ 0 := by
  have h0 : BlockBand.Internal.Contracts.Layers.blockDiag
      (0 : Fin 1 → Matrix (Fin W) (Fin W) ℂ) = 0 := by
    ext u v; simp [BlockBand.Internal.Contracts.Layers.blockDiag]
  simp only [layerLin, dirB, h0]

theorem bondOf_smul (c : ℂ) (M : Matrix (Fin W) (Fin W) ℂ) : bondOf (c • M) = c • bondOf M := by
  ext u v; simp [bondMatrix]

theorem layerLin_dirB_plus (M : Matrix (Fin W) (Fin W) ℂ) :
    layerLin (dirB M) + Complex.I • layerLin (dirB (Complex.I • M)) = (2 : ℂ) • lowerB M := by
  rw [layerLin_dirB, layerLin_dirB, bondOf_smul, conjTranspose_smul, lowerB, fromBlocks_smul,
    fromBlocks_smul, fromBlocks_add]
  congr 1
  · simp
  · rw [smul_smul, Complex.I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]
  · rw [smul_smul, Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    rw [two_smul]
  · simp

theorem layerLin_dirB_minus (M : Matrix (Fin W) (Fin W) ℂ) :
    layerLin (dirB M) - Complex.I • layerLin (dirB (Complex.I • M)) = (2 : ℂ) • upperB M := by
  rw [layerLin_dirB, layerLin_dirB, bondOf_smul, conjTranspose_smul, upperB, fromBlocks_smul,
    fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  congr 1
  · simp
  · rw [smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg, two_smul]
  · rw [smul_smul, Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg, one_smul,
      add_neg_cancel, smul_zero]
  · simp

/-- **Linear-form Ginibre IBP on the layer**: `E[B_xy Φ] = (b/W) E[D_ω([[0,0],[E_xy*,0]])]`. -/
theorem stein_layerB_lin (b : ℝ) (Φ : LayerSample W .oneBlockOnePort → ℂ)
    (D : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) (hD : HasLayerDeriv Φ D)
    (hm : Measurable Φ) (hΦ : MemLp Φ 2 (layerLaw W b .oneBlockOnePort))
    (hDi : ∀ N, Integrable (fun ω => D ω N) (layerLaw W b .oneBlockOnePort)) (x y : Fin W) :
    ∫ ω, ω.2 0 0 x y * Φ ω ∂layerLaw W b .oneBlockOnePort =
      (ginVar W b : ℂ) * ∫ ω, D ω (lowerB (Matrix.single x y 1)) ∂layerLaw W b .oneBlockOnePort := by
  set E1 : Matrix (Fin W) (Fin W) ℂ := Matrix.single x y 1
  have h0 : ((dirB E1).1 0).IsHermitian := by simp [dirB]
  have hI : ((dirB (Complex.I • E1)).1 0).IsHermitian := by simp [dirB]
  have h := stein_layerB_herm b Φ (fun ω => D ω (layerLin (dirB E1)))
    (fun ω => D ω (layerLin (dirB (Complex.I • E1)))) x y hm
    (fun ω hω => by
      have e : (fun s : ℝ => Φ (ω.1, fun i j => ω.2 i j + (s : ℂ) • E1)) =
          fun s : ℝ => Φ (ω + (s : ℂ) • dirB E1) := by funext s; rw [add_smul_dirB]
      rw [e]; exact hD ω hω _ h0)
    (fun ω hω => by
      have e : (fun s : ℝ => Φ (ω.1, fun i j => ω.2 i j + ((s : ℂ) * Complex.I) • E1)) =
          fun s : ℝ => Φ (ω + (s : ℂ) • dirB (Complex.I • E1)) := by funext s; rw [add_smul_dirB_I]
      rw [e]; exact hD ω hω _ hI)
    hΦ (hDi _) (hDi _)
  rw [h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show (D ω (layerLin (dirB E1)) + Complex.I * D ω (layerLin (dirB (Complex.I • E1)))) / 2 = _
  rw [← smul_eq_mul, ← map_smul, ← map_add, layerLin_dirB_plus, map_smul, smul_eq_mul]
  ring

/-- **Linear-form IBP for `B̄`**: `E[conj(B_xy) Φ] = (b/W) E[D_ω([[0,E_xy],[0,0]])]`. -/
theorem stein_layerBconj_lin (b : ℝ) (Φ : LayerSample W .oneBlockOnePort → ℂ)
    (D : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ) (hD : HasLayerDeriv Φ D)
    (hm : Measurable Φ) (hΦ : MemLp Φ 2 (layerLaw W b .oneBlockOnePort))
    (hDi : ∀ N, Integrable (fun ω => D ω N) (layerLaw W b .oneBlockOnePort)) (x y : Fin W) :
    ∫ ω, star (ω.2 0 0 x y) * Φ ω ∂layerLaw W b .oneBlockOnePort =
      (ginVar W b : ℂ) * ∫ ω, D ω (upperB (Matrix.single x y 1)) ∂layerLaw W b .oneBlockOnePort := by
  set E1 : Matrix (Fin W) (Fin W) ℂ := Matrix.single x y 1
  have h0 : ((dirB E1).1 0).IsHermitian := by simp [dirB]
  have hI : ((dirB (Complex.I • E1)).1 0).IsHermitian := by simp [dirB]
  have hstar : ∀ {f : LayerSample W .oneBlockOnePort → ℂ},
      Integrable f (layerLaw W b .oneBlockOnePort) →
      Integrable (fun ω => star (f ω)) (layerLaw W b .oneBlockOnePort) := fun hf => by
    simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp hf
  have h := stein_layerB_herm b (fun ω => star (Φ ω)) (fun ω => star (D ω (layerLin (dirB E1))))
    (fun ω => star (D ω (layerLin (dirB (Complex.I • E1))))) x y
    (continuous_star.measurable.comp hm)
    (fun ω hω => by
      have e : (fun s : ℝ => star (Φ (ω.1, fun i j => ω.2 i j + (s : ℂ) • E1))) =
          fun s : ℝ => star (Φ (ω + (s : ℂ) • dirB E1)) := by funext s; rw [add_smul_dirB]
      rw [e]; exact (hD ω hω _ h0).star)
    (fun ω hω => by
      have e : (fun s : ℝ => star (Φ (ω.1, fun i j => ω.2 i j + ((s : ℂ) * Complex.I) • E1))) =
          fun s : ℝ => star (Φ (ω + (s : ℂ) • dirB (Complex.I • E1))) := by
        funext s; rw [add_smul_dirB_I]
      rw [e]; exact (hD ω hω _ hI).star)
    hΦ.star (hstar (hDi _)) (hstar (hDi _))
  have e1 : ∫ ω, star (ω.2 0 0 x y) * Φ ω ∂layerLaw W b .oneBlockOnePort =
      (starRingEnd ℂ) (∫ ω, ω.2 0 0 x y * star (Φ ω) ∂layerLaw W b .oneBlockOnePort) := by
    rw [← integral_conj]; congr 1; funext ω; simp
  rw [e1, h, map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  show ((starRingEnd ℂ) (star (D ω (layerLin (dirB E1)))) + -Complex.I *
      (starRingEnd ℂ) (star (D ω (layerLin (dirB (Complex.I • E1)))))) / 2 = _
  simp only [Complex.star_def, Complex.conj_conj]
  rw [neg_mul, ← sub_eq_add_neg, ← smul_eq_mul, ← map_smul, ← map_sub, layerLin_dirB_minus,
    map_smul, smul_eq_mul]
  ring

end Lin

section Calc
variable {W : ℕ}

theorem layerLin_isHermitian (Δ : LayerSample W .oneBlockOnePort) (hΔ : (Δ.1 0).IsHermitian) :
    (layerLin Δ).IsHermitian := by
  refine IsHermitian.fromBlocks ?_ rfl isHermitian_zero
  ext u v
  simp only [conjTranspose_apply, BlockBand.Internal.Contracts.Layers.blockDiag]
  have hu : u.1 = 0 := Subsingleton.elim _ _
  have hv : v.1 = 0 := Subsingleton.elim _ _
  simp only [hu, hv, ite_true]
  have h := congrFun (congrFun hΔ u.2) v.2
  simpa [conjTranspose_apply] using h

/-- The entry map `M ↦ M α β`. -/
def entryCLM (α β : LayerSite W .oneBlockOnePort) : LayerMat W →L[ℝ] ℂ :=
  (LinearMap.toContinuousLinearMap
    ({ toFun := fun M => M α β, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      LayerMat W →ₗ[ℂ] ℂ)).restrictScalars ℝ

/-- The linear map `N ↦ -(G N G)_{αβ}`. -/
def resDeriv (G : LayerMat W) (α β : LayerSite W .oneBlockOnePort) : LayerMat W →ₗ[ℂ] ℂ where
  toFun N := -(G * N * G) α β
  map_add' N N' := by simp [Matrix.mul_add, Matrix.add_mul]; ring
  map_smul' c N := by simp

/-- The linear map `N ↦ -(G* N G*)_{αβ}`. -/
def resDerivAdj (G : LayerMat W) (α β : LayerSite W .oneBlockOnePort) : LayerMat W →ₗ[ℂ] ℂ :=
  resDeriv Gᴴ α β

theorem hasLayerDeriv_resolvent_entry (E : ℝ) (z : ℂ) (X' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
    (hinv : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian →
      IsUnit (layerMatrix .oneBlockOnePort E z X' ω)) (α β : LayerSite W .oneBlockOnePort) :
    HasLayerDeriv (fun ω => layerResolvent .oneBlockOnePort E z X' ω α β)
      (fun ω => resDeriv (layerResolvent .oneBlockOnePort E z X' ω) α β) := by
  intro ω hω Δ _
  have h := hasDerivAt_layerResolvent E z X' ω Δ (hinv ω hω)
  have h2 := (entryCLM α β).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h2

theorem hasLayerDeriv_resolvent_adj_entry (E : ℝ) (z : ℂ)
    (X' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
    (hinv : ∀ ω : LayerSample W .oneBlockOnePort, (ω.1 0).IsHermitian →
      IsUnit (layerMatrix .oneBlockOnePort E z X' ω)) (α β : LayerSite W .oneBlockOnePort) :
    HasLayerDeriv (fun ω => (layerResolvent .oneBlockOnePort E z X' ω)ᴴ α β)
      (fun ω => resDerivAdj (layerResolvent .oneBlockOnePort E z X' ω) α β) := by
  intro ω hω Δ hΔ
  have h := (hasLayerDeriv_resolvent_entry E z X' hinv β α ω hω Δ hΔ).star
  have hL := layerLin_isHermitian Δ hΔ
  simp only [conjTranspose_apply]
  convert h using 1
  simp only [resDerivAdj, resDeriv, LinearMap.coe_mk, AddHom.coe_mk, star_neg]
  congr 1
  rw [← conjTranspose_apply, conjTranspose_mul, conjTranspose_mul, hL.eq, Matrix.mul_assoc]

theorem hasLayerDeriv_const (c : ℂ) :
    HasLayerDeriv (W := W) (fun _ => c) (fun _ => 0) := fun _ _ _ _ => by
  simpa using hasDerivAt_const (0 : ℝ) c

theorem HasLayerDeriv.mul {Φ Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {D D' : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΦ : HasLayerDeriv Φ D) (hΨ : HasLayerDeriv Ψ D') :
    HasLayerDeriv (fun ω => Φ ω * Ψ ω) (fun ω => Φ ω • D' ω + Ψ ω • D ω) := by
  intro ω hω Δ hΔ
  have h := (hΦ ω hω Δ hΔ).mul (hΨ ω hω Δ hΔ)
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h
  convert h using 1
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem HasLayerDeriv.add {Φ Ψ : LayerSample W .oneBlockOnePort → ℂ}
    {D D' : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΦ : HasLayerDeriv Φ D) (hΨ : HasLayerDeriv Ψ D') :
    HasLayerDeriv (fun ω => Φ ω + Ψ ω) (fun ω => D ω + D' ω) := by
  intro ω hω Δ hΔ
  exact (hΦ ω hω Δ hΔ).add (hΨ ω hω Δ hΔ)

theorem HasLayerDeriv.const_mul {Φ : LayerSample W .oneBlockOnePort → ℂ}
    {D : LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ} (c : ℂ) (hΦ : HasLayerDeriv Φ D) :
    HasLayerDeriv (fun ω => c * Φ ω) (fun ω => c • D ω) := by
  intro ω hω Δ hΔ
  simpa using (hΦ ω hω Δ hΔ).const_mul c

theorem HasLayerDeriv.sum {ι : Type*} (s : Finset ι) {Φ : ι → LayerSample W .oneBlockOnePort → ℂ}
    {D : ι → LayerSample W .oneBlockOnePort → LayerMat W →ₗ[ℂ] ℂ}
    (hΦ : ∀ i ∈ s, HasLayerDeriv (Φ i) (D i)) :
    HasLayerDeriv (fun ω => ∑ i ∈ s, Φ i ω) (fun ω => ∑ i ∈ s, D i ω) := by
  intro ω hω Δ hΔ
  have h := HasDerivAt.fun_sum (u := s) (A := fun i (s' : ℝ) => Φ i (ω + (s' : ℂ) • Δ))
    (fun i hi => hΦ i hi ω hω Δ hΔ)
  simpa [LinearMap.sum_apply] using h

end Calc

end BlockBand.Transmission.PassiveCovariance
