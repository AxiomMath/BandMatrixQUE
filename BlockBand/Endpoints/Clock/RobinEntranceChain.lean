module

public import BlockBand.Endpoints.Clock.OpenInputsPath
public import BlockBand.Endpoints.Clock.PhaseResolution
public import BlockBand.Endpoints.Clock.ClockMixingAlgebra
public import BlockBand.Layers.ResolventRowSum

/-!
# The Robin entrance lemma: the fresh layer block equations and the one-ended chain on the path

Eliminating the far auxiliary coordinate leaves the initial Hermitian cavity `X₀ = B₀*λ_θ⁻¹B₀` and
zero initial interior clock; the remaining fresh layers and near matched absorber are those of the
one-ended path. This file contains the deterministic algebra for this step.

## Contents

* Fresh layer (`OneEndedLayer W`, one block, one port; `z = boundaryZ b E`): with
  `freshFull = [[A - E - X, B],[B*, zI]]` on `Fin W ⊕ Fin W`, `freshLayer` is `freshFull⁻¹` read
  through `Fin 1 × Fin W ≃ Fin W` (`freshLayer_eq`), `freshG12` is its `(1,2)` block
  (`freshG12_eq`), `freshG22` its `(2,2)` block, and `freshSchur = B*(A - E - X)⁻¹B`
  (`freshSchur_eq'`). If `A - E - X` and `z - X₊` are invertible: `freshFull` is invertible
  (`freshFull_isUnit`), and `(A - E - X)𝒢₁₂ + B𝒢₂₂ = 0`, `B*𝒢₁₂ + z𝒢₂₂ = I` (`fresh_blocks`),
  `B*𝒢₁₂ = -X₊𝒢₂₂` (`fresh_schur_rel`), `(z - X₊)𝒢₂₂ = I` (`fresh_port_rel`).
* The one-ended chain read off a growth sample `ω` (`GrowthPath W`): layer `k` is
  `robinLayer ω k = (A_k, B_{k+1})` (block `k` and the bond to the next block, or to the near
  port); `robinX E D ω j = X_j`, `robinY b E D ω j = Y_j` (weight `q ≡ 1`) are `oneEndedX` and
  `oneEndedY` of these layers.
* The near-port input `g` descends the chain: `robinInput … n g k = v_{n-k}` with
  `v_n = g`, `v_j = L_{j+1} v_{j+1}`; the block amplitudes are
  `robinAmp … n g j = (𝒢_{j+1})₁₂ v_{j+1}` (block `j`). Clock identity
  (`quadForm_robinY`): `Re v_m* Y_m v_m = Σ_{j<m} ‖a_j‖²` for `m ≤ n`; at `m = n`,
  `Re g* Y_n g = Σ_{j<n} ‖a_j‖²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix

namespace RobinEntrance

variable {W : ℕ}

/-!
## 1. The fresh layer on `Fin W ⊕ Fin W`
-/

/-- `(Fin 1 × Fin W) ⊕ (Fin 1 × Fin W) ≃ Fin W ⊕ Fin W`. -/
def siteEquiv (W : ℕ) : LayerSite W .oneBlockOnePort ≃ Fin W ⊕ Fin W :=
  Equiv.sumCongr (Equiv.uniqueProd (Fin W) (Fin 1)) (Equiv.uniqueProd (Fin W) (Fin 1))

/-- `[[A - E - X, B],[B*, zI]]` of one fresh layer, on `Fin W ⊕ Fin W` (`z = boundaryZ b E`). -/
def freshFull (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ :=
  fromBlocks (ω.1 0 - (E : ℂ) • 1 - X) (ω.2 0 0) (ω.2 0 0)ᴴ (boundaryZ b E • 1)

theorem layerMatrix_eq_submatrix (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    layerMatrix .oneBlockOnePort E (boundaryZ b E)
        (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω =
      (freshFull b E X ω).submatrix (siteEquiv W) (siteEquiv W) := by
  ext (⟨i, x⟩ | ⟨i, x⟩) (⟨k, y⟩ | ⟨k, y⟩) <;> fin_cases i <;> fin_cases k <;>
    simp [layerMatrix, freshFull, siteEquiv, Internal.Contracts.Layers.blockDiag, bondMatrix,
      LayerShape.incident, Matrix.one_apply]

theorem freshLayer_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    freshLayer b E X ω = (freshFull b E X ω)⁻¹.submatrix (siteEquiv W) (siteEquiv W) := by
  rw [freshLayer, layerResolvent, layerMatrix_eq_submatrix, inv_submatrix_equiv]

theorem freshG12_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    freshG12 b E X ω = (freshFull b E X ω)⁻¹.toBlocks₁₂ := by
  ext x y
  simp [freshG12, freshLayer_eq, toBlocks₁₂, siteEquiv]

theorem freshSchur_eq' (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    freshSchur E X ω = (ω.2 0 0)ᴴ * (ω.1 0 - (E : ℂ) • 1 - X)⁻¹ * ω.2 0 0 := by
  set e := Equiv.uniqueProd (Fin W) (Fin 1)
  have hT : Internal.Contracts.Layers.blockDiag ω.1 -
      (E : ℂ) • (1 : Matrix (PhysSite W .oneBlockOnePort) _ ℂ) -
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) =
      (ω.1 0 - (E : ℂ) • 1 - X).submatrix e e := by
    ext ⟨i, x⟩ ⟨k, y⟩; fin_cases i; fin_cases k
    simp [Internal.Contracts.Layers.blockDiag, e, Matrix.one_apply]
  have hB : bondMatrix .oneBlockOnePort ω.2 = (ω.2 0 0).submatrix e e := by
    ext ⟨i, x⟩ ⟨k, y⟩; fin_cases i; fin_cases k
    simp [bondMatrix, LayerShape.incident, e]
  ext x y
  simp only [freshSchur, layerSchur, Matrix.of_apply, hT, hB, inv_submatrix_equiv,
    conjTranspose_submatrix, submatrix_mul_equiv]
  simp [e]

/-- `(𝒢)₂₂`: the port block of the fresh layer resolvent. -/
def freshG22 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    Matrix (Fin W) (Fin W) ℂ :=
  (freshFull b E X ω)⁻¹.toBlocks₂₂

theorem freshFull_isUnit {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : OneEndedLayer W}
    (hA : IsUnit (ω.1 0 - (E : ℂ) • 1 - X).det)
    (hz : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur E X ω).det) :
    IsUnit (freshFull b E X ω).det := by
  let _ := invertibleOfIsUnitDet _ hA
  rw [freshFull, det_fromBlocks₁₁, invOf_eq_nonsing_inv, ← freshSchur_eq']
  exact hA.mul hz

theorem fresh_blocks {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : OneEndedLayer W}
    (hF : IsUnit (freshFull b E X ω).det) :
    (ω.1 0 - (E : ℂ) • 1 - X) * freshG12 b E X ω + ω.2 0 0 * freshG22 b E X ω = 0 ∧
      (ω.2 0 0)ᴴ * freshG12 b E X ω + boundaryZ b E • freshG22 b E X ω = 1 := by
  have h := mul_nonsing_inv (freshFull b E X ω) hF
  rw [freshG12_eq, freshG22]
  set G := (freshFull b E X ω)⁻¹ with hG
  rw [← fromBlocks_toBlocks G, freshFull, fromBlocks_multiply, ← fromBlocks_one] at h
  have h12 := congrArg toBlocks₁₂ h
  have h22 := congrArg toBlocks₂₂ h
  simp only [toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂] at h12 h22
  refine ⟨h12, ?_⟩
  rw [Matrix.smul_mul, Matrix.one_mul] at h22
  exact h22

theorem fresh_G12 {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : OneEndedLayer W}
    (hA : IsUnit (ω.1 0 - (E : ℂ) • 1 - X).det) (hF : IsUnit (freshFull b E X ω).det) :
    freshG12 b E X ω = -((ω.1 0 - (E : ℂ) • 1 - X)⁻¹ * ω.2 0 0 * freshG22 b E X ω) := by
  have h1 := (fresh_blocks hF).1
  have h2 : (ω.1 0 - (E : ℂ) • 1 - X) * freshG12 b E X ω = -(ω.2 0 0 * freshG22 b E X ω) :=
    eq_neg_of_add_eq_zero_left h1
  have := congrArg (fun M => (ω.1 0 - (E : ℂ) • 1 - X)⁻¹ * M) h2
  simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.one_mul, Matrix.mul_neg] at this
  exact this

theorem fresh_schur_rel {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : OneEndedLayer W}
    (hA : IsUnit (ω.1 0 - (E : ℂ) • 1 - X).det) (hF : IsUnit (freshFull b E X ω).det) :
    (ω.2 0 0)ᴴ * freshG12 b E X ω = -(freshSchur E X ω * freshG22 b E X ω) := by
  rw [fresh_G12 hA hF, freshSchur_eq']
  simp only [Matrix.mul_neg, Matrix.mul_assoc]

theorem fresh_port_rel {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : OneEndedLayer W}
    (hA : IsUnit (ω.1 0 - (E : ℂ) • 1 - X).det) (hF : IsUnit (freshFull b E X ω).det) :
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur E X ω) *
      freshG22 b E X ω = 1 := by
  have h := (fresh_blocks hF).2
  rw [fresh_schur_rel hA hF] at h
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, ← h]
  abel

theorem freshL_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    freshL b E X ω = (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * freshG12 b E X ω :=
  rfl

/-!
## 2. The one-ended chain of a growth sample
-/

/-- Layer `k` of the one-ended chain read from a growth sample: block `A_k` and the bond
`B_{k+1}` coupling it to block `k+1` (or to the near port at length `k+1`). -/

def robinLayer (ω : GrowthPath W) (k : ℕ) : OneEndedLayer W :=
  (fun _ => ω.1 k, fun _ _ => ω.2 (k + 1))

/-- The first `j` layers. -/
def robinLayers (ω : GrowthPath W) (j : ℕ) : Fin j → OneEndedLayer W := fun i => robinLayer ω i

/-- `X_j` of the one-ended chain of `ω` started at `X_0 = D`. -/
def robinX (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) (j : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  oneEndedX E D j (robinLayers ω j)

theorem robinX_zero (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) :
    robinX E D ω 0 = D := rfl

theorem robinX_succ (E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) (j : ℕ) :
    robinX E D ω (j + 1) = freshSchur E (robinX E D ω j) (robinLayer ω j) := rfl

/-- `Y_j` (weight `q ≡ 1`) of the one-ended chain of `ω` started at `X_0 = D`. -/
def robinY (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) (j : ℕ) :
    Matrix (Fin W) (Fin W) ℂ :=
  oneEndedY b E (fun _ => 1) D j (robinLayers ω j)

theorem robinY_zero (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) :
    robinY b E D ω 0 = 0 := rfl

theorem robinY_succ (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) (j : ℕ) :
    robinY b E D ω (j + 1) = freshC b E (robinX E D ω j) (robinLayer ω j) +
      (freshL b E (robinX E D ω j) (robinLayer ω j))ᴴ * robinY b E D ω j *
        freshL b E (robinX E D ω j) (robinLayer ω j) := by
  rw [robinY, oneEndedY]
  simp only [Complex.ofReal_one, one_smul]
  rfl

theorem quadForm_add' {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm (A + B) v = quadForm A v + quadForm B v := by
  unfold quadForm; rw [add_mulVec, dotProduct_add, Complex.add_re]

theorem quadForm_sandwich {ι κ : Type*} [Fintype ι] [Fintype κ] (L : Matrix ι κ ℂ)
    (Y : Matrix ι ι ℂ) (v : κ → ℂ) : quadForm (Lᴴ * Y * L) v = quadForm Y (L *ᵥ v) := by
  unfold quadForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem quadForm_conjTranspose_mul_self {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (L : Matrix ι κ ℂ) (v : κ → ℂ) : quadForm (Lᴴ * L) v = vecNormSq (L *ᵥ v) := by
  have h := quadForm_sandwich L 1 v
  rw [Matrix.mul_one] at h
  rw [h]; unfold quadForm
  rw [one_mulVec, star_dotProduct_self_eq, Complex.ofReal_re]

/-- The descending inputs: `robinInput … n g k = v_{n-k}`, `v_n = g`, `v_j = L_{j+1} v_{j+1}`. -/
def robinInput (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) (n : ℕ)
    (g : Fin W → ℂ) : ℕ → (Fin W → ℂ)
  | 0 => g
  | k + 1 => freshL b E (robinX E D ω (n - 1 - k)) (robinLayer ω (n - 1 - k)) *ᵥ
      robinInput b E D ω n g k

theorem robinInput_step (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) {n : ℕ}
    (g : Fin W → ℂ) {m : ℕ} (hm : m + 1 ≤ n) :
    robinInput b E D ω n g (n - m) = freshL b E (robinX E D ω m) (robinLayer ω m) *ᵥ
      robinInput b E D ω n g (n - (m + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
  have h1 : n - (m + 1) = k := by omega
  have h2 : n - 1 - k = m := by omega
  rw [hk, robinInput, h1, h2]

/-- The amplitude of block `j`: `a_j = (𝒢_{j+1})₁₂ v_{j+1}`. -/
def robinAmp (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) (n : ℕ)
    (g : Fin W → ℂ) (j : ℕ) : Fin W → ℂ :=
  freshG12 b E (robinX E D ω j) (robinLayer ω j) *ᵥ robinInput b E D ω n g (n - (j + 1))

/-- **Clock identity** of the descending chain: `Re v_m* Y_m v_m = Σ_{j<m} ‖a_j‖²` for
`m ≤ n`. -/
theorem quadForm_robinY (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (ω : GrowthPath W) {n : ℕ}
    (g : Fin W → ℂ) : ∀ m, m ≤ n → quadForm (robinY b E D ω m) (robinInput b E D ω n g (n - m)) =
      ∑ j ∈ Finset.range m, vecNormSq (robinAmp b E D ω n g j) := by
  intro m
  induction m with
  | zero => intro _; simp [robinY_zero, quadForm]
  | succ m ih =>
    intro hm
    rw [robinY_succ, quadForm_add', freshC, quadForm_conjTranspose_mul_self, quadForm_sandwich,
      ← robinInput_step b E D ω g hm, ih (by omega), Finset.sum_range_succ, add_comm]
    rfl
end RobinEntrance

end BlockBand.Endpoints.Clock
