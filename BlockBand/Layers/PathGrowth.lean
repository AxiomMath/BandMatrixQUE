module

public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.LayerMeasurability

/-!
# Exact two-ended growth of the path Schur matrix

The two-ended recursion: growing the path from its center, `X_{r+2} = B*(A - E - X_r)⁻¹B` with
`A = diag(A₁, A₂)` fresh GUE blocks and `B = diag(B₁, B₂)` fresh bonds.

* `pgGrow : LayerSample W .separate × PathSample W r → PathSample W (r+2)` places the layer's
  block `0` at position `0`, the old path at `1, …, r`, the layer's block `1` at `r+1`. Since
  `pathMatrix` puts bond `k` at entry `(k, k+1)` and `pathPortCoupling` puts the port bond at
  entry `(block, port)`, the old port bond `B_p⁰` becomes the internal bond `0` as `(B_p⁰)ᴴ`
  and `B_p¹` becomes bond `r` unchanged; old bond `k` becomes bond `k+1`. The new port bonds
  are the diagonal layer bonds `B₀₀, B₁₁` (the only ones `bondMatrix .separate` couples).
* Deterministic composition (`r ≥ 1`): `pathSchur_pgGrow`, `portResolvent_pgGrow`,
  `pathPortResolvent_pgGrow`, `det_pgGrow`, `isUnit_det_pgGrow_iff`.
* Law (`r ≥ 1`): `measurePreserving_pgGrow`, `map_pgGrow_pathLaw` (a coordinate permutation,
  a marginal, and `pg_mp_conjTranspose_ginibre`: `Gin` is invariant under `M ↦ Mᴴ`).
* Growing path (`r₀ ≥ 1`, `k ≤ L`): `pgPath`, `grownSchur_eq_pathSchur`,
  `measurePreserving_pgPath`, `ae_grownSchur_eq_pathSchur`, `map_grownSchur_growthLaw`, under
  the explicit hypothesis that `H_path - E` is a.s. invertible under every `pathLaw`; that
  hypothesis is discharged for `b < 1/2` in `BlockBand.Layers.PathGrowthLaw`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

/-!
## 1. The reindexing of the grown path
-/

/-- Positions of the grown path `Fin (r+2)`: position `0` is the new left block (`inl 0`),
positions `1, …, r` are the old path (`inr (k-1)`), position `r+1` is the new right block
(`inl 1`). -/
def pgPos (r : ℕ) : Fin (r + 2) ≃ Fin 2 ⊕ Fin r where
  toFun k :=
    if h0 : k.val = 0 then .inl 0 else if h : k.val ≤ r then .inr ⟨k.val - 1, by omega⟩ else .inl 1
  invFun
    | .inl j => if j.val = 0 then 0 else Fin.last (r + 1)
    | .inr i => ⟨i.val + 1, by omega⟩
  left_inv k := by
    by_cases h0 : k.val = 0
    · simp only [h0, ↓reduceDIte]
      ext; simp [h0]
    · by_cases h : k.val ≤ r
      · simp only [h0, h, ↓reduceDIte]
        ext; simp; omega
      · simp only [h0, h, ↓reduceDIte]
        ext; simp; omega
  right_inv x := by
    rcases x with j | i
    · fin_cases j
      · simp
      · simp
    · have h1 : ¬ (i.val + 1 = 0) := by omega
      have h2 : i.val + 1 ≤ r := by omega
      simp [h2]

@[simp] theorem pgPos_symm_inl_zero (r : ℕ) : ((pgPos r).symm (.inl 0)).val = 0 := rfl

@[simp] theorem pgPos_symm_inl_one (r : ℕ) : ((pgPos r).symm (.inl 1)).val = r + 1 := rfl

@[simp] theorem pgPos_symm_inr (r : ℕ) (i : Fin r) : ((pgPos r).symm (.inr i)).val = i.val + 1 :=
  rfl

/-- Sites of the grown path, split into the two new blocks and the old path. -/
def pgSite (W r : ℕ) : (Fin 2 × Fin W) ⊕ (Fin r × Fin W) ≃ Fin (r + 2) × Fin W :=
  (Equiv.sumProdDistrib (Fin 2) (Fin r) (Fin W)).symm.trans
    ((pgPos r).symm.prodCongr (Equiv.refl (Fin W)))

@[simp] theorem pgSite_inl (W r : ℕ) (j : Fin 2) (a : Fin W) :
    pgSite W r (.inl (j, a)) = ((pgPos r).symm (.inl j), a) := rfl

@[simp] theorem pgSite_inr (W r : ℕ) (i : Fin r) (a : Fin W) :
    pgSite W r (.inr (i, a)) = ((pgPos r).symm (.inr i), a) := rfl

/-- **The grown path** `pgGrow (ℓ, ω)`: the layer's block `0` becomes position `0`, the old path
positions `1, …, r`, the layer's block `1` position `r+1`; the old port bonds become the internal
bonds `(0,1)` (as `(B_p⁰)ᴴ`, since the path's bond `k` is the `(k, k+1)` entry) and `(r, r+1)`,
the old internal bond `k` becomes bond `k+1`; the new port bonds are the diagonal layer bonds
`B₀₀, B₁₁` (the off-diagonal `B₀₁, B₁₀` are not coupled in a `.separate` layer). -/
def pgGrow {W r : ℕ} (x : LayerSample W .separate × PathSample W r) : PathSample W (r + 2) :=
  (fun k => Sum.elim x.1.1 x.2.1 (pgPos r k),
    fun k => if h0 : k.val = 0 then (x.2.2.2 0)ᴴ
      else if h : k.val < r then x.2.2.1 ⟨k.val - 1, by omega⟩ else x.2.2.2 1,
    fun j => x.1.2 j j)

theorem pgGrow_blocks {W r : ℕ} (x : LayerSample W .separate × PathSample W r) (u : Fin 2 ⊕ Fin r) :
    (pgGrow x).1 ((pgPos r).symm u) = Sum.elim x.1.1 x.2.1 u := by
  simp [pgGrow]

theorem pgGrow_bond {W r : ℕ} (x : LayerSample W .separate × PathSample W r)
    (k : Fin (r + 2 - 1)) :
    (pgGrow x).2.1 k = if h0 : k.val = 0 then (x.2.2.2 0)ᴴ
      else if h : k.val < r then x.2.2.1 ⟨k.val - 1, by omega⟩ else x.2.2.2 1 := rfl

/-- The grown path matrix in the split coordinates (new blocks, old path) is
`[[diag(A₁, A₂), B_pᴴ], [B_p, H_path]]`. -/
theorem pgGrow_pathMatrix {W r : ℕ} (hr : 1 ≤ r) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) :
    (pathMatrix (pgGrow (ℓ, ω))).submatrix (pgSite W r) (pgSite W r) =
      Matrix.fromBlocks (Internal.Contracts.Layers.blockDiag ℓ.1) (pathPortCoupling ω)ᴴ
        (pathPortCoupling ω)
        (pathMatrix ω) := by
  have hr0 : r ≠ 0 := by omega
  ext (⟨j, a⟩ | ⟨i, a⟩) (⟨j', c⟩ | ⟨i', c⟩)
  · fin_cases j <;> fin_cases j' <;>
      simp [pathMatrix, Internal.Contracts.Layers.blockDiag, pgGrow_blocks, hr0]
  · fin_cases j <;> simp [pathMatrix, pathPortCoupling, pgGrow_bond] <;> split_ifs <;> simp_all <;>
      omega
  · fin_cases j' <;> simp [pathMatrix, pathPortCoupling, pgGrow_bond]
    all_goals split_ifs <;> simp_all <;> omega
  · simp [pathMatrix, pgGrow_bond, pgGrow_blocks]
    split_ifs <;> simp_all

/-- The grown port coupling in the split coordinates: the layer bond matrix on the new blocks,
zero on the old path. -/
theorem pgGrow_portCoupling {W r : ℕ} (ℓ : LayerSample W .separate) (ω : PathSample W r) :
    (pathPortCoupling (pgGrow (ℓ, ω))).submatrix (pgSite W r) id =
      Matrix.fromRows (bondMatrix .separate ℓ.2) (0 : Matrix (Fin r × Fin W) _ ℂ) := by
  ext (⟨j, a⟩ | ⟨i, a⟩) ⟨j', c⟩
  · fin_cases j <;> fin_cases j' <;>
      simp [pathPortCoupling, bondMatrix, LayerShape.incident, pgGrow]
  · fin_cases j' <;> simp [pathPortCoupling, pgGrow]
    omega

/-- The grown path matrix minus `E` in split coordinates. -/
theorem pgGrow_pathMatrix_sub {W r : ℕ} (hr : 1 ≤ r) (E : ℝ) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) :
    (pathMatrix (pgGrow (ℓ, ω)) - (E : ℂ) • 1).submatrix (pgSite W r) (pgSite W r) =
      Matrix.fromBlocks (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1)
        (pathPortCoupling ω)ᴴ (pathPortCoupling ω) (pathMatrix ω - (E : ℂ) • 1) := by
  rw [show (pathMatrix (pgGrow (ℓ, ω)) - (E : ℂ) • 1).submatrix (pgSite W r) (pgSite W r) =
      (pathMatrix (pgGrow (ℓ, ω))).submatrix (pgSite W r) (pgSite W r) -
        (E : ℂ) • (1 : Matrix (Fin (r + 2) × Fin W) (Fin (r + 2) × Fin W) ℂ).submatrix
          (pgSite W r) (pgSite W r) from rfl, submatrix_one_equiv, pgGrow_pathMatrix hr]
  ext (i | i) (j | j) <;> simp [one_apply]

/-- Sandwiching a block matrix between `fromRows B 0` keeps only the top-left block. -/
theorem pg_fromRows_sandwich {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    (B : Matrix m o ℂ) (Q₁₁ : Matrix m m ℂ) (Q₁₂ : Matrix m n ℂ) (Q₂₁ : Matrix n m ℂ)
    (Q₂₂ : Matrix n n ℂ) :
    (Matrix.fromRows B (0 : Matrix n o ℂ))ᴴ * Matrix.fromBlocks Q₁₁ Q₁₂ Q₂₁ Q₂₂ *
        Matrix.fromRows B (0 : Matrix n o ℂ) = Bᴴ * Q₁₁ * B := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows]
  simp

/-- `pathSchur` of the grown path, reindexed: `(B_layer)ᴴ [(H' - E)⁻¹]_{new,new} B_layer`. -/
theorem pathSchur_pgGrow_eq_sandwich {W r : ℕ} (hr : 1 ≤ r) (E : ℝ)
    (ℓ : LayerSample W .separate) (ω : PathSample W r) :
    pathSchur E (pgGrow (ℓ, ω)) =
      (Matrix.fromRows (bondMatrix .separate ℓ.2) (0 : Matrix (Fin r × Fin W) _ ℂ))ᴴ *
        (Matrix.fromBlocks (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1)
          (pathPortCoupling ω)ᴴ (pathPortCoupling ω) (pathMatrix ω - (E : ℂ) • 1))⁻¹ *
        Matrix.fromRows (bondMatrix .separate ℓ.2) (0 : Matrix (Fin r × Fin W) _ ℂ) := by
  rw [← pgGrow_pathMatrix_sub hr, ← pgGrow_portCoupling ℓ ω, inv_submatrix_equiv,
    conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]
  rfl

/-- Determinant of the grown path: `det(H' - E) = det(H - E) · det(A - E - X_r)`. -/
theorem det_pgGrow {W r : ℕ} (hr : 1 ≤ r) (E : ℝ) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det) :
    (pathMatrix (pgGrow (ℓ, ω)) - (E : ℂ) • 1).det =
      (pathMatrix ω - (E : ℂ) • 1).det *
        (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det := by
  let _ := invertibleOfIsUnitDet _ hH
  rw [← det_submatrix_equiv_self (pgSite W r), pgGrow_pathMatrix_sub hr, det_fromBlocks₂₂,
    invOf_eq_nonsing_inv]
  rfl

/-- Given an invertible old path, the grown path is invertible iff the layer's top block
`A - E - X_r` is. -/
theorem isUnit_det_pgGrow_iff {W r : ℕ} (hr : 1 ≤ r) (E : ℝ) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det) :
    IsUnit (pathMatrix (pgGrow (ℓ, ω)) - (E : ℂ) • 1).det ↔
      IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det := by
  rw [det_pgGrow hr E ℓ ω hH, IsUnit.mul_iff]
  exact ⟨fun h => h.2, fun h => ⟨hH, h⟩⟩

/-- **Deterministic two-ended Schur composition** (the two-ended recursion): if `H_path - E` and
`A - E - X_r` are invertible, the Schur matrix of the grown path is the outgoing layer Schur
matrix `X_{r+2} = B*(A - E - X_r)⁻¹B` with `X_r = pathSchur E ω`. -/
theorem pathSchur_pgGrow {W r : ℕ} (hr : 1 ≤ r) (E : ℝ) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det) :
    pathSchur E (pgGrow (ℓ, ω)) = layerSchur .separate E (pathSchur E ω) ℓ := by
  let _ := invertibleOfIsUnitDet _ hH
  have hS' : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 -
      (pathPortCoupling ω)ᴴ * ⅟(pathMatrix ω - (E : ℂ) • 1) * pathPortCoupling ω).det := by
    rw [invOf_eq_nonsing_inv]; exact hS
  let _ := invertibleOfIsUnitDet _ hS'
  let _ := fromBlocks₂₂Invertible (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1)
    (pathPortCoupling ω)ᴴ (pathPortCoupling ω) (pathMatrix ω - (E : ℂ) • 1)
  rw [pathSchur_pgGrow_eq_sandwich hr, ← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq,
    pg_fromRows_sandwich, invOf_eq_nonsing_inv, invOf_eq_nonsing_inv]
  rfl

/-- The port block of the inverse of `[[A, B], [C, D]]` with `A` invertible is the inverse of
the Schur complement `D - C A⁻¹ B` (both sides vanish when the complement is singular). -/
theorem pg_toBlocks22_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hA : IsUnit A.det) :
    (Matrix.fromBlocks A B C D)⁻¹.toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let _ := invertibleOfIsUnitDet _ hA
  by_cases hS : IsUnit (D - C * A⁻¹ * B).det
  · have hS2 : IsUnit (D - C * ⅟A * B).det := by rwa [invOf_eq_nonsing_inv]
    let _ := invertibleOfIsUnitDet _ hS2
    let _ := fromBlocks₁₁Invertible A B C D
    rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq, toBlocks_fromBlocks₂₂,
      invOf_eq_nonsing_inv (D - C * ⅟A * B), invOf_eq_nonsing_inv A]
  · have hS' : ¬ IsUnit (D - C * ⅟A * B) := by rwa [isUnit_iff_isUnit_det, invOf_eq_nonsing_inv]
    have hM : ¬ IsUnit (Matrix.fromBlocks A B C D).det := by
      rw [← isUnit_iff_isUnit_det, isUnit_fromBlocks_iff_of_invertible₁₁]; exact hS'
    rw [nonsing_inv_apply_not_isUnit _ hM, nonsing_inv_apply_not_isUnit _ hS]
    ext i j; rfl

/-- **Port resolvents along the growth**: for any `z`, `(z - X_{r+2})⁻¹` is the port block of
the layer resolvent `𝒢` with `X = X_r` (`X_r = pathSchur E ω`). -/
theorem portResolvent_pgGrow {W r : ℕ} (hr : 1 ≤ r) (E : ℝ) (z : ℂ)
    (ℓ : LayerSample W .separate) (ω : PathSample W r)
    (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det) :
    (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - pathSchur E (pgGrow (ℓ, ω)))⁻¹ =
      (layerResolvent .separate E z (pathSchur E ω) ℓ).toBlocks₂₂ := by
  rw [pathSchur_pgGrow hr E ℓ ω hH hS, layerResolvent, layerMatrix, pg_toBlocks22_inv _ _ _ _ hS]
  rfl

/-- `pathPortResolvent` (`R_{r+2} = (z_∂ - X_{r+2})⁻¹`) is the port block of the layer resolvent
at `z = z_∂(E)` with `X = X_r`. -/
theorem pathPortResolvent_pgGrow {W r : ℕ} (hr : 1 ≤ r) (b E : ℝ)
    (ℓ : LayerSample W .separate) (ω : PathSample W r)
    (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det) :
    pathPortResolvent b E (pgGrow (ℓ, ω)) =
      (layerResolvent .separate E (boundaryZ b E) (pathSchur E ω) ℓ).toBlocks₂₂ :=
  portResolvent_pgGrow hr E (boundaryZ b E) ℓ ω hH hS

/-!
## 2. The law of the grown path
-/

instance pg_isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) (σ : LayerShape) :
    IsProbabilityMeasure (layerLaw W b σ) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold layerLaw
  infer_instance

/-- The `.separate` instance (the shape-generic one is not found through `Fin σ.blocks`). -/
instance pg_isProbabilityMeasure_layerLaw_separate (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (layerLaw W b .separate) :=
  pg_isProbabilityMeasure_layerLaw W b .separate

instance pg_isProbabilityMeasure_pathLaw (W r : ℕ) (b : ℝ) :
    IsProbabilityMeasure (pathLaw W r b) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold pathLaw
  infer_instance

instance pg_isProbabilityMeasure_growthLaw (W r₀ L : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthLaw W r₀ L b) := by
  unfold growthLaw
  infer_instance

/-- Reindexing a product of identical factors is measure preserving. -/
theorem pg_mp_reindex {ι ι' β : Type*} [Fintype ι] [Fintype ι'] [MeasurableSpace β]
    (μ : Measure β) [SigmaFinite μ] (e : ι ≃ ι') :
    MeasurePreserving (fun (f : ι → β) (i : ι') => f (e.symm i))
      (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι' => μ) := by
  have h := measurePreserving_arrowCongr' (fun _ : ι => μ) (fun _ : ι' => μ) e
    (MeasurableEquiv.refl β) (fun _ => MeasurePreserving.id μ)
  exact h

/-- The rearrangement `((a, b), (c, d)) ↦ ((a, c), (d, b))` is measure preserving. -/
theorem pg_mp_rearrange {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ)
    (μd : Measure δ) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.1.1, x.2.1), (x.2.2, x.1.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μd.prod μb)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm MeasurableEquiv.prodAssoc
  have h6 := (MeasurePreserving.id (μa.prod μc)).prod
    (Measure.measurePreserving_swap (μ := μb) (ν := μd))
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))

/-- The white-noise coordinates of `Mᴴ` in terms of those of `M`: transpose the index and flip
the sign of the imaginary coordinate. -/
def pgConjNoise {ι κ : Type*} (x : ι × κ × Fin 2 → ℝ) : κ × ι × Fin 2 → ℝ :=
  fun y => if y.2.2 = 0 then x (y.2.1, y.1, y.2.2) else -x (y.2.1, y.1, y.2.2)

/-- `pgConjNoise` preserves white noise (a coordinate permutation and sign flips of centered
Gaussians). -/
theorem pg_mp_conjNoise {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ℝ≥0) :
    MeasurePreserving (pgConjNoise (ι := ι) (κ := κ)) (whiteNoise _ v) (whiteNoise _ v) := by
  let e : ι × κ × Fin 2 ≃ κ × ι × Fin 2 :=
    { toFun := fun x => (x.2.1, x.1, x.2.2)
      invFun := fun y => (y.2.1, y.1, y.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 := pg_mp_reindex (gaussianReal 0 v) e
  have hneg : MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 v) (gaussianReal 0 v) :=
    ⟨measurable_neg, by rw [gaussianReal_map_neg, neg_zero]⟩
  have h2 := measurePreserving_pi (fun _ : κ × ι × Fin 2 => gaussianReal 0 v)
    (fun _ => gaussianReal 0 v) (f := fun y (x : ℝ) => if y.2.2 = 0 then x else -x)
    (fun y => by
      by_cases h : y.2.2 = 0
      · simp only [h, ite_true]; exact MeasurePreserving.id _
      · simp only [h, ite_false]; exact hneg)
  have h3 := h2.comp h1
  unfold whiteNoise
  convert h3 using 1
  funext x y
  rfl

/-- **Ginibre matrices are invariant under conjugate transposition.** -/
theorem pg_mp_conjTranspose_ginibre {ι κ : Type*} [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    MeasurePreserving (fun M : Matrix ι κ ℂ => Mᴴ) (ginibreMeasure ι κ t)
      (ginibreMeasure κ ι t) := by
  have hct : Measurable (fun M : Matrix ι κ ℂ => Mᴴ) :=
    (continuous_id.matrix_conjTranspose).measurable
  refine ⟨hct, ?_⟩
  have hN := pg_mp_conjNoise (ι := ι) (κ := κ) (t / 2)
  have hcomp : (fun M : Matrix ι κ ℂ => Mᴴ) ∘ ginibreAssemble =
      ginibreAssemble ∘ pgConjNoise := by
    funext x
    ext i j
    simp only [Function.comp_apply, conjTranspose_apply, ginibreAssemble, Matrix.of_apply,
      pgConjNoise]
    simp
  rw [ginibreMeasure_eq_map, Measure.map_map hct measurable_ginibreAssemble, hcomp,
    ← Measure.map_map measurable_ginibreAssemble hN.measurable, hN.map_eq]
  rfl

/-- The block coordinates of the grown path: `(A_layer, A_path) ↦ A'`. -/
def pgGrowBlocks {β : Type*} (r : ℕ) (p : (Fin 2 → β) × (Fin r → β)) : Fin (r + 2) → β :=
  fun k => Sum.elim p.1 p.2 (pgPos r k)

/-- The internal-bond coordinates of the grown path `(B_path, B_ports) ↦ B'` (for `r = s + 1`). -/
def pgGrowBonds {W : ℕ} (s : ℕ)
    (p : (Fin s → Matrix (Fin W) (Fin W) ℂ) × (Fin 2 → Matrix (Fin W) (Fin W) ℂ)) :
    Fin (s + 2) → Matrix (Fin W) (Fin W) ℂ :=
  fun k => if h0 : k.val = 0 then (p.2 0)ᴴ
    else if h : k.val < s + 1 then p.1 ⟨k.val - 1, by omega⟩ else p.2 1

/-- The port coordinates of the grown path: the diagonal layer bonds. -/
def pgGrowPorts {β : Type*} (B : Fin 2 → Fin 2 → β) : Fin 2 → β := fun j => B j j

theorem pg_mp_growBlocks {β : Type*} [MeasurableSpace β] (r : ℕ) (μ : Measure β)
    [SigmaFinite μ] :
    MeasurePreserving (pgGrowBlocks (β := β) r)
      ((Measure.pi fun _ : Fin 2 => μ).prod (Measure.pi fun _ : Fin r => μ))
      (Measure.pi fun _ : Fin (r + 2) => μ) := by
  have h := (pg_mp_reindex μ (pgPos r).symm).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 2 ⊕ Fin r => μ))
  convert h using 1
  funext p k
  simp only [pgGrowBlocks, Function.comp_apply, Equiv.symm_symm]
  rcases pgPos r k with j | i <;> rfl

theorem pg_mp_growBonds (W s : ℕ) (t : ℝ≥0) :
    MeasurePreserving (pgGrowBonds (W := W) s)
      ((Measure.pi fun _ : Fin s => ginibreMeasure (Fin W) (Fin W) t).prod
        (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) t))
      (Measure.pi fun _ : Fin (s + 2) => ginibreMeasure (Fin W) (Fin W) t) := by
  set μ := ginibreMeasure (Fin W) (Fin W) t
  have hc : MeasurePreserving (fun q : Fin 2 → Matrix (Fin W) (Fin W) ℂ =>
      fun j => if j = 0 then (q j)ᴴ else q j) (Measure.pi fun _ : Fin 2 => μ)
      (Measure.pi fun _ : Fin 2 => μ) :=
    measurePreserving_pi (fun _ => μ) (fun _ => μ)
      (f := fun j (A : Matrix (Fin W) (Fin W) ℂ) => if j = 0 then Aᴴ else A)
      (fun j => by
        by_cases h : j = 0
        · simp only [h, ite_true]; exact pg_mp_conjTranspose_ginibre t
        · simp only [h, ite_false]; exact MeasurePreserving.id _)
  have hs := (Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin s => μ)
    (ν := Measure.pi fun _ : Fin 2 => μ))
  have h := (pg_mp_growBlocks s μ).comp ((hc.prod (MeasurePreserving.id _)).comp hs)
  convert h using 1
  funext p k
  simp only [pgGrowBonds, pgGrowBlocks, Function.comp_apply, Prod.map, Prod.swap, id]
  by_cases h0 : k.val = 0
  · have hk0 : k = 0 := Fin.ext h0
    have hk : pgPos s k = .inl 0 := by simp [pgPos, hk0]
    simp [h0, hk]
  · have hk0 : k ≠ 0 := fun h => h0 (by rw [h]; rfl)
    by_cases h1 : k.val < s + 1
    · have hk : pgPos s k = .inr ⟨k.val - 1, by omega⟩ := by
        simp [pgPos, hk0, show k.val ≤ s by omega]
      simp [h0, h1, hk]
    · have hk : pgPos s k = .inl 1 := by
        simp [pgPos, hk0, show ¬ k.val ≤ s by omega]
      simp [h0, h1, hk]

theorem pg_mp_growPorts {β : Type*} [MeasurableSpace β] (μ : Measure β)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (pgGrowPorts (β := β))
      (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ)
      (Measure.pi fun _ : Fin 2 => μ) :=
  measurePreserving_pi (fun _ => Measure.pi fun _ : Fin 2 => μ) (fun _ => μ)
    (f := fun j (g : Fin 2 → β) => g j)
    (fun j => measurePreserving_eval (fun _ : Fin 2 => μ) j)

/-- `pgGrow` in coordinates, for `r = s + 1`. -/
theorem pgGrow_eq_coords {W s : ℕ} (x : LayerSample W .separate × PathSample W (s + 1)) :
    pgGrow x = (pgGrowBlocks (s + 1) (x.1.1, x.2.1),
      pgGrowBonds (W := W) s (x.2.2.1, x.2.2.2), pgGrowPorts x.1.2) := rfl

/-- **Law of the grown path**: under the product of a fresh separate-port layer and an
independent path of `r ≥ 1` blocks, `pgGrow` is distributed as a path of `r + 2` blocks. -/
theorem measurePreserving_pgGrow {W r : ℕ} (b : ℝ) (hr : 1 ≤ r) :
    MeasurePreserving (pgGrow (W := W) (r := r))
      ((layerLaw W b .separate).prod (pathLaw W r b)) (pathLaw W (r + 2) b) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have := fun t => isProbabilityMeasure_gueMeasure W t
  set g := BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W)
    (Real.toNNReal ((1 - 2 * b) / W))
  set μ := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hR := pg_mp_rearrange (Measure.pi fun _ : Fin 2 => g)
    (Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 2 => μ)
    (Measure.pi fun _ : Fin (s + 1) => g)
    ((Measure.pi fun _ : Fin s => μ).prod (Measure.pi fun _ : Fin 2 => μ))
  have hF := (pg_mp_growBlocks (s + 1) g).prod
    ((pg_mp_growBonds W s (Real.toNNReal (b / W))).prod (pg_mp_growPorts μ))
  exact hF.comp hR

/-- The law identity of the two-ended recursion: `(layerLaw ⊗ pathLaw r) ∘ pgGrow⁻¹ =
pathLaw (r + 2)` for `r ≥ 1`. -/
theorem map_pgGrow_pathLaw {W r : ℕ} (b : ℝ) (hr : 1 ≤ r) :
    ((layerLaw W b .separate).prod (pathLaw W r b)).map pgGrow = pathLaw W (r + 2) b :=
  (measurePreserving_pgGrow b hr).map_eq

/-!
## 3. The growing path
-/

/-- The path after `k` growth steps of a growth sample (`k ≤ L`; past `L` the zero layer is
used, which plays no role for `k ≤ L`). -/
def pgPath {W r₀ L : ℕ} (ω : GrowthSample W r₀ L) : (k : ℕ) → PathSample W (r₀ + 2 * k)
  | 0 => ω.1
  | k + 1 => pgGrow (if h : k < L then ω.2 ⟨k, h⟩ else 0, pgPath ω k)

theorem pgPath_succ {W r₀ L : ℕ} (ω : GrowthSample W r₀ L) {k : ℕ} (hk : k < L) :
    pgPath ω (k + 1) = pgGrow (ω.2 ⟨k, hk⟩, pgPath ω k) := by
  simp [pgPath, hk]

/-- **Deterministic growth identity**: along a growth sample whose paths `H_{r₀+2j} - E`
(`j ≤ k`) are all invertible, `X_{r₀+2k} = grownSchur E ω k` is the Schur matrix of the grown
path `pgPath ω k`. -/
theorem grownSchur_eq_pathSchur {W r₀ L : ℕ} (hr₀ : 1 ≤ r₀) (E : ℝ) (ω : GrowthSample W r₀ L) :
    ∀ k, k ≤ L → (∀ j, j ≤ k → IsUnit (pathMatrix (pgPath ω j) - (E : ℂ) • 1).det) →
      grownSchur E ω k = pathSchur E (pgPath ω k)
  | 0, _, _ => rfl
  | k + 1, hk, hinv => by
    have hkL : k < L := by omega
    have ih := grownSchur_eq_pathSchur hr₀ E ω k (by omega) (fun j hj => hinv j (by omega))
    have hH := hinv k (by omega)
    have hG := hinv (k + 1) le_rfl
    rw [pgPath_succ ω hkL] at hG ⊢
    have hr : 1 ≤ r₀ + 2 * k := by omega
    have hS := (isUnit_det_pgGrow_iff hr E (ω.2 ⟨k, hkL⟩) (pgPath ω k) hH).mp hG
    simp only [grownSchur, hkL, dite_true]
    rw [ih, pathSchur_pgGrow hr E _ _ hH hS]

/-- Truncation of a growth sample to its first `L` layers. -/
def pgTrunc {W r₀ L : ℕ} (ω : GrowthSample W r₀ (L + 1)) : GrowthSample W r₀ L :=
  (ω.1, Fin.init ω.2)

theorem pgPath_pgTrunc {W r₀ L : ℕ} (ω : GrowthSample W r₀ (L + 1)) :
    ∀ k, k ≤ L → pgPath (pgTrunc ω) k = pgPath ω k
  | 0, _ => rfl
  | k + 1, hk => by
    have hkL : k < L := by omega
    rw [pgPath_succ _ hkL, pgPath_succ ω (by omega), pgPath_pgTrunc ω k (by omega)]
    rfl

/-- Splitting off the last layer of a growth sample is measure preserving. -/
theorem pg_mp_splitLast (W r₀ L : ℕ) (b : ℝ) :
    MeasurePreserving (fun ω : GrowthSample W r₀ (L + 1) => (pgTrunc ω, ω.2 (Fin.last L)))
      (growthLaw W r₀ (L + 1) b) ((growthLaw W r₀ L b).prod (layerLaw W b .separate)) := by
  have hpi := measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => layerLaw W b .separate)
    (Fin.last L)
  have h1 := (MeasurePreserving.id (pathLaw W r₀ b)).prod hpi
  have h2 := (measurePreserving_prodAssoc (pathLaw W r₀ b) (layerLaw W b .separate)
    (Measure.pi fun _ : Fin L => layerLaw W b .separate)).symm MeasurableEquiv.prodAssoc
  have h3 := (Measure.measurePreserving_swap (μ := pathLaw W r₀ b)
    (ν := layerLaw W b .separate)).prod
    (MeasurePreserving.id (Measure.pi fun _ : Fin L => layerLaw W b .separate))
  have h4 := measurePreserving_prodAssoc (layerLaw W b .separate) (pathLaw W r₀ b)
    (Measure.pi fun _ : Fin L => layerLaw W b .separate)
  have h5 := Measure.measurePreserving_swap (μ := layerLaw W b .separate)
    (ν := (pathLaw W r₀ b).prod (Measure.pi fun _ : Fin L => layerLaw W b .separate))
  have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  unfold growthLaw
  convert h using 1
  funext ω
  refine Prod.ext (Prod.ext rfl ?_) rfl
  funext j
  change ω.2 (Fin.castSucc j) = ω.2 ((Fin.last L).succAbove j)
  rw [Fin.succAbove_last]

/-- **Law of the growing path**: for `r₀ ≥ 1` and `k ≤ L`, the grown path `pgPath ω k` under
`growthLaw W r₀ L b` is distributed as `pathLaw W (r₀ + 2k) b`. -/
theorem measurePreserving_pgPath {W r₀ : ℕ} (b : ℝ) (hr₀ : 1 ≤ r₀) :
    ∀ L k, k ≤ L → MeasurePreserving (fun ω : GrowthSample W r₀ L => pgPath ω k)
      (growthLaw W r₀ L b) (pathLaw W (r₀ + 2 * k) b)
  | 0, 0, _ => by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    unfold growthLaw
    exact measurePreserving_fst
  | 0, k + 1, hk => absurd hk (by omega)
  | L + 1, k, hk => by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have hT := pg_mp_splitLast W r₀ L b
    rcases Nat.lt_or_ge k (L + 1) with hkL | hkL
    · have hP := measurePreserving_pgPath (W := W) b hr₀ L k (by omega)
      have h := (hP.comp (measurePreserving_fst (μ := growthLaw W r₀ L b)
        (ν := layerLaw W b .separate))).comp hT
      convert h using 1
      funext ω
      exact (pgPath_pgTrunc ω k (by omega)).symm
    · obtain rfl : k = L + 1 := by omega
      have hP := measurePreserving_pgPath (W := W) b hr₀ L L le_rfl
      have hG := measurePreserving_pgGrow (W := W) b (show 1 ≤ r₀ + 2 * L by omega)
      have h := (hG.comp (Measure.measurePreserving_swap.comp
        (hP.prod (MeasurePreserving.id (layerLaw W b .separate))))).comp hT
      convert h using 1
      funext ω
      simp only [Function.comp_apply, Prod.map, Prod.swap, id]
      rw [pgPath_succ ω (Nat.lt_succ_self L), pgPath_pgTrunc ω L le_rfl]
      rfl

/-- Entries of a measurable matrix-valued map are measurable. -/
theorem pg_entry {Ω m n : Type*} [MeasurableSpace Ω] {f : Ω → Matrix m n ℂ} (hf : Measurable f)
    (a : m) (c : n) : Measurable (fun ω => f ω a c) :=
  (measurable_pi_apply c).comp ((measurable_pi_apply a).comp hf)

/-- The path matrix is measurable in the Gaussian coordinates. -/
theorem measurable_pathMatrix (W r : ℕ) :
    Measurable (fun ω : PathSample W r => pathMatrix ω) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold pathMatrix
  split_ifs
  · fun_prop
  · fun_prop
  · exact continuous_star.measurable.comp (by fun_prop)
  · fun_prop

/-- The port coupling is measurable in the Gaussian coordinates. -/
theorem measurable_pathPortCoupling (W r : ℕ) :
    Measurable (fun ω : PathSample W r => pathPortCoupling ω) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold pathPortCoupling
  split_ifs
  · fun_prop
  · fun_prop

/-- `ω ↦ X_r = pathSchur E ω` is measurable. -/
theorem measurable_pathSchur (W r : ℕ) (E : ℝ) :
    Measurable (fun ω : PathSample W r => pathSchur E ω) := by
  have hP := measurable_pathPortCoupling W r
  have hM : Measurable (fun ω : PathSample W r => pathMatrix ω - (E : ℂ) • 1) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    simp only [Matrix.sub_apply]
    exact (pg_entry (measurable_pathMatrix W r) x y).sub measurable_const
  have hN : Measurable (fun ω : PathSample W r => (pathMatrix ω - (E : ℂ) • 1)⁻¹) :=
    measurable_matrix_inv.comp hM
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [pathSchur, Matrix.mul_apply, conjTranspose_apply]
  refine Finset.measurable_sum _ fun l _ => (Finset.measurable_sum _ fun k _ => ?_).mul
    (pg_entry hP l j)
  exact (continuous_star.measurable.comp (pg_entry hP k i)).mul (pg_entry hN k l)

/-- **Almost-sure growth identity**: for `r₀ ≥ 1` and `k ≤ L`, if every path law `pathLaw W r b`
(`r ≥ 1`) charges only paths with `H_path - E` invertible, then `growthLaw W r₀ L b`-a.s.
`grownSchur E ω k = pathSchur E (pgPath ω k)`. -/
theorem ae_grownSchur_eq_pathSchur {W r₀ L : ℕ} (b E : ℝ) (hr₀ : 1 ≤ r₀)
    (hinv : ∀ r, 1 ≤ r → ∀ᵐ ω ∂pathLaw W r b, IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    {k : ℕ} (hk : k ≤ L) :
    ∀ᵐ ω ∂growthLaw W r₀ L b, grownSchur E ω k = pathSchur E (pgPath ω k) := by
  have hall : ∀ᵐ ω ∂growthLaw W r₀ L b,
      ∀ j : ℕ, j ≤ k → IsUnit (pathMatrix (pgPath ω j) - (E : ℂ) • 1).det := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ≤ k
    · have hP := measurePreserving_pgPath (W := W) b hr₀ L j (hj.trans hk)
      filter_upwards [hP.quasiMeasurePreserving.ae (hinv (r₀ + 2 * j) (by omega))] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [hall] with ω hω
  exact grownSchur_eq_pathSchur hr₀ E ω k hk hω

/-- **Law of the grown Schur matrix** (the two-ended recursion along the growing path):
for `r₀ ≥ 1` and `k ≤ L`, if every path law `pathLaw W r b` (`r ≥ 1`) charges only paths with
`H_path - E` invertible, then the law of `X_{r₀+2k} = grownSchur E ω k` under
`growthLaw W r₀ L b` is the law of `pathSchur E` under `pathLaw W (r₀ + 2k) b`. -/
theorem map_grownSchur_growthLaw {W r₀ L : ℕ} (b E : ℝ) (hr₀ : 1 ≤ r₀)
    (hinv : ∀ r, 1 ≤ r → ∀ᵐ ω ∂pathLaw W r b, IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    {k : ℕ} (hk : k ≤ L) :
    (growthLaw W r₀ L b).map (fun ω => grownSchur E ω k) =
      (pathLaw W (r₀ + 2 * k) b).map (pathSchur E) := by
  have hae : (fun ω => grownSchur E ω k) =ᵐ[growthLaw W r₀ L b]
      (fun ω => pathSchur E (pgPath ω k)) := ae_grownSchur_eq_pathSchur b E hr₀ hinv hk
  have hP := measurePreserving_pgPath (W := W) b hr₀ L k hk
  rw [Measure.map_congr hae, ← hP.map_eq,
    Measure.map_map (measurable_pathSchur W (r₀ + 2 * k) E) hP.measurable]
  rfl

end BlockBand.Layers
