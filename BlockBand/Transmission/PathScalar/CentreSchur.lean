module

public import BlockBand.Transmission.PathScalar.Superexp

/-!
# Centre growth, deterministic part: one separate-port layer is a Schur complement

`newPath inner ℓ` is the path of length `r + 2` obtained from a path sample `inner` of length `r`
by adding the two blocks `ℓ.1 0` (new position `0`) and `ℓ.1 1` (new position `r + 1`) of a
separate-port layer `ℓ`; the old port bonds become the new end bonds (`(B_near)ᴴ` at bond `0`,
`B_far` at bond `r`, matching the orientation of `pathMatrix`), and the new port bonds are the
diagonal layer bonds `ℓ.2 0 0`, `ℓ.2 1 1` (the off-diagonal layer bonds are not incident for
`.separate`).

Main result `pathSchur_newPath`: for `r ≥ 1` and `H_inner - E` invertible,
`pathSchur E (newPath inner ℓ) = layerSchur .separate E (pathSchur E inner) ℓ`
(`X_{r+2} = B*(A - E - X_r)⁻¹B`), the step of `Layers.grownSchur`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.Bridge
open scoped Matrix

variable {W : ℕ}

/-- Sites of the length-`r+2` path: the two new end blocks first (`0 ↦` position `0`,
`1 ↦` position `r+1`), then the old path (`i ↦` position `i+1`). -/
def outerEquiv (r W : ℕ) : (Fin 2 × Fin W) ⊕ (Fin r × Fin W) ≃ Fin (r + 2) × Fin W where
  toFun
    | Sum.inl p => (⟨if p.1.val = 0 then 0 else r + 1, by split_ifs <;> omega⟩, p.2)
    | Sum.inr p => (⟨p.1.val + 1, by have := p.1.isLt; omega⟩, p.2)
  invFun p :=
    if h0 : p.1.val = 0 then Sum.inl (0, p.2)
    else if h1 : p.1.val = r + 1 then Sum.inl (1, p.2)
    else Sum.inr (⟨p.1.val - 1, by have := p.1.isLt; omega⟩, p.2)
  left_inv := by
    rintro (⟨a, x⟩ | ⟨i, x⟩)
    · fin_cases a <;> simp
    · have := i.isLt
      have h : ¬ (i.val = r) := by omega
      simp [h]
  right_inv := by
    rintro ⟨i, x⟩
    have := i.isLt
    by_cases h0 : i.val = 0
    · simp only [h0, dite_true]; simp [Fin.ext_iff, h0]
    · by_cases h1 : i.val = r + 1
      · simp only [h1, dite_true]; simp [Fin.ext_iff, h1]
      · simp only [h0, h1, dite_false]; ext <;> simp; omega

theorem outerEquiv_inl_fst (r : ℕ) (a : Fin 2) (x : Fin W) :
    ((outerEquiv r W (Sum.inl (a, x))).1 : ℕ) = if a.val = 0 then 0 else r + 1 := rfl

theorem outerEquiv_inr_fst (r : ℕ) (i : Fin r) (x : Fin W) :
    ((outerEquiv r W (Sum.inr (i, x))).1 : ℕ) = i.val + 1 := rfl

@[simp] theorem outerEquiv_snd (r : ℕ) (p : (Fin 2 × Fin W) ⊕ (Fin r × Fin W)) :
    (outerEquiv r W p).2 = Sum.elim Prod.snd Prod.snd p := by
  rcases p with p | p <;> rfl

/-- The path of length `r+2` grown from `inner` by one separate-port layer `ℓ`. -/
def newPath {r : ℕ} (inner : PathSample W r) (ℓ : LayerSample W .separate) :
    PathSample W (r + 2) :=
  (fun i => if h0 : i.val = 0 then ℓ.1 0 else if h1 : i.val = r + 1 then ℓ.1 1
      else inner.1 ⟨i.val - 1, by have := i.isLt; omega⟩,
   fun j => if h0 : j.val = 0 then (inner.2.2 0)ᴴ else if h1 : j.val = r then inner.2.2 1
      else inner.2.1 ⟨j.val - 1, by have := j.isLt; omega⟩,
   ![ℓ.2 0 0, ℓ.2 1 1])

/-- **Block form of the grown pencil**: new end blocks first,
`H_{r+2} - E = [[diag(A₀', A₁') - E, Cᴴ], [C, H_r - E]]`, `C` the old port coupling. -/
theorem pencil_newPath_submatrix (E : ℝ) {r : ℕ} (hr : 1 ≤ r) (inner : PathSample W r)
    (ℓ : LayerSample W .separate) :
    (pathMatrix (newPath inner ℓ) - (E : ℂ) • 1).submatrix (outerEquiv r W) (outerEquiv r W) =
      Matrix.fromBlocks (BlockBand.Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1)
        (pathPortCoupling inner)ᴴ (pathPortCoupling inner) (pathMatrix inner - (E : ℂ) • 1) := by
  ext (⟨a, x⟩ | ⟨i, x⟩) (⟨a', y⟩ | ⟨j, y⟩)
  · fin_cases a <;> fin_cases a' <;>
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₁, outerEquiv, Equiv.coe_fn_mk, newPath, pathMatrix,
      BlockBand.Internal.Contracts.Layers.blockDiag, Fin.mk.injEq, Prod.mk.injEq] <;>
    split_ifs <;> simp_all <;> omega
  · have := j.isLt
    fin_cases a <;>
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.fromBlocks_apply₁₂, outerEquiv, Equiv.coe_fn_mk, newPath, pathMatrix, pathPortCoupling,
      Matrix.conjTranspose_apply, Fin.mk.injEq, Prod.mk.injEq] <;> simp <;>
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  · have := i.isLt
    fin_cases a' <;>
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.fromBlocks_apply₂₁, outerEquiv, Equiv.coe_fn_mk, newPath, pathMatrix, pathPortCoupling,
      Fin.mk.injEq, Prod.mk.injEq]
    all_goals simp
    all_goals split_ifs <;> first | rfl | (exfalso; omega) | simp
  · have := i.isLt; have := j.isLt
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.fromBlocks_apply₂₂, outerEquiv, Equiv.coe_fn_mk, newPath, pathMatrix,
      Fin.mk.injEq, Prod.mk.injEq]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- The port coupling of the grown path, new end blocks first: `[B_layer; 0]`. -/
theorem portCoupling_newPath_submatrix {r : ℕ} (inner : PathSample W r)
    (ℓ : LayerSample W .separate) :
    (pathPortCoupling (newPath inner ℓ)).submatrix (outerEquiv r W) id =
      Matrix.fromRows (bondMatrix .separate ℓ.2) 0 := by
  ext (⟨a, x⟩ | ⟨i, x⟩) ⟨j, y⟩
  · fin_cases a <;> fin_cases j <;>
    simp [outerEquiv, newPath, pathPortCoupling, bondMatrix, LayerShape.incident]
  · have := i.isLt
    simp only [Matrix.submatrix_apply, id, outerEquiv, Equiv.coe_fn_mk, pathPortCoupling,
      Matrix.fromRows_apply_inr, Matrix.zero_apply]
    rw [ite_eq_right]
    rintro (⟨_, h⟩ | ⟨_, h⟩) <;> simp at h; omega

/-- Reindexing a congruence along an equivalence of the inner index. -/
theorem congr_submatrix_equiv {m n p : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (C : Matrix m p ℂ) (G : Matrix m m ℂ) (e : n ≃ m) :
    Cᴴ * G * C = (C.submatrix e id)ᴴ * G.submatrix e e * C.submatrix e id := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv _ _ _ e _,
    Matrix.submatrix_mul_equiv _ _ _ e _, Matrix.submatrix_id_id]

/-- **One separate-port layer is a Schur complement** (the two-ended recursion): for `r ≥ 1`
and `H_r - E` invertible, the two-port Schur matrix of the grown path is the layer Schur
matrix `B*(A - E - X_r)⁻¹B` at the old Schur matrix `X_r = pathSchur E inner`. -/
theorem pathSchur_newPath (E : ℝ) {r : ℕ} (hr : 1 ≤ r) (inner : PathSample W r)
    (ℓ : LayerSample W .separate) (hH : IsUnit (pathMatrix inner - (E : ℂ) • 1)) :
    pathSchur E (newPath inner ℓ) = layerSchur .separate E (pathSchur E inner) ℓ := by
  rw [pathSchur, congr_submatrix_equiv _ _ (outerEquiv r W), portCoupling_newPath_submatrix,
    ← Matrix.inv_submatrix_equiv, pencil_newPath_submatrix E hr, fromRows_zero_sandwich,
    toBlocks₁₁_inv_fromBlocks _ _ _ _ hH, layerSchur, pathSchur]

end BlockBand.Transmission.PathScalar
