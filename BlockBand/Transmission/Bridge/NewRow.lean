module

public import BlockBand.Transmission.Bridge.Discharge

/-!
# The new row `D₊` and the new-tag injection `Y_{j+1;j} = D₊ᴴD₊`

* `nearSel_resolvent_transport`: `ι*ℝN = D₊` for a deterministic old two-port `𝕏`
  (`z - 𝕏₁₁`, `z - X` invertible);
* `boundaryToInterior_succ_newRow`: the new row of `𝒰_{j+1}` is `D₊` at `𝕏_j`;
* `tagResponse_succ_new`: `Y_{j+1;j} = D₊ᴴD₊` (the injection `C₊` of the newest block).
Together with `tagResponse_succ` (old tags `Y_{j+1;k} = NᴴY_{j;k}N`, `k < j`) this is the
tag form of the full clock recursion.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix

variable {W : ℕ}

/-- `D₊ = [𝒢₁₂, 𝒢₁₁Kℝ₁₂]`, `K = z - X`, `X = nearSchur z 𝕏`, `ℝ = (z - 𝕏)⁻¹`;
`𝒢₁₂`, `𝒢₁₁` are the block-port and block-block parts of the fresh layer resolvent. -/
def freshD (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω' : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin 2 × Fin W) ℂ :=
  let X := nearSchur (boundaryZ b E) XX
  let K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  fun x c => if c.1 = 0 then freshBlock b E X ω' true false x c.2
    else (freshBlock b E X ω' true true * K * portBlock (twoPortResolvent b E XX) 0 1) x c.2

theorem colBlock_ext (M M' : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (h : ∀ i, colBlock M i = colBlock M' i) : M = M' := by
  ext x ⟨i, y⟩; simpa [colBlock] using congrFun (congrFun (h i) x) y

/-- **`ι*ℝN = D₊`**, for every old two-port `𝕏` with `z - 𝕏₁₁` and `z - X`
invertible. -/
theorem nearSel_resolvent_transport (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω' : LayerSample W .oneBlockOnePort)
    (hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1))
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX)) :
    nearSel W * twoPortResolvent b E XX * freshTransport b E XX ω' = freshD b E XX ω' := by
  set z := boundaryZ b E
  set X := nearSchur z XX
  set N := freshTransport b E XX ω'
  set Rr := twoPortResolvent b E XX
  set K : Matrix (Fin W) (Fin W) ℂ := z • 1 - X
  set g := freshBlock b E X ω'
  set R01 := portBlock Rr 0 1
  have hR : portBlock Rr 0 0 = K⁻¹ := portBlock_twoPortResolvent_zero_zero b E XX hD
  have hRK : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  have hL : freshL b E X ω' = K * g true false := rfl
  have hΔ : freshDelta b E X ω' = K * g true true * K - K := rfl
  have cb1 : ∀ i, colBlock (nearSel W * Rr * N) i =
      if i = 0 then K⁻¹ * (K * g true false) else K⁻¹ * ((K * g true true * K - K) * R01) + R01 := by
    intro i; rw [← hR, ← hL, ← hΔ]
    ext x y
    simp only [colBlock, Matrix.of_apply, Matrix.mul_assoc, nearSel_mul_apply]
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    fin_cases i <;> simp [N, freshTransport, portBlock, R01, Matrix.mul_apply, Matrix.one_apply] <;> rfl
  have cbD : ∀ i, colBlock (freshD b E XX ω') i =
      if i = 0 then g true false else g true true * K * R01 := by
    intro i; ext x y; fin_cases i <;> rfl
  apply colBlock_ext
  intro i
  rw [cb1, cbD]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ite_true]
    rw [← Matrix.mul_assoc, hRK, Matrix.one_mul]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K⁻¹ K, hRK, Matrix.one_mul, ← Matrix.mul_assoc K⁻¹ K, hRK,
      Matrix.one_mul]
    abel

/-- The invertibility facts used by the new-row identity, along a passive unabsorbed sample. -/
theorem newRow_pencils {b E : ℝ} {ω : GrowthPath W} (h : PassiveSample b E (fun _ => 0) ω)
    (j : ℕ) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
        portBlock (pathSchur E (pathAt W j ω)) 1 1) ∧
      IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
        nearSchur (boundaryZ b E) (pathSchur E (pathAt W j ω))) := by
  have hX := pathSchur_isHermitian E j ω h.herm
  refine ⟨portPencil_isUnit _ (by
      ext x y; simpa [portBlock, Matrix.conjTranspose_apply] using
        congrFun (congrFun hX (1, x)) (1, y)) h.height, ?_⟩
  have := isUnit_nearPencil_absorbed h j
  rwa [← pathX, pathX_eq] at this

/-- **The new row of `𝒰_{j+1}` is `D₊`**: for `j ≥ 1`, the row of the newest block
(position `0`) of the boundary-to-interior map of the length-`j+1` path is
`D₊ = freshD b E 𝕏_j (freshSample W j ω)`. Hypotheses as in `boundaryToInterior_succ`. -/
theorem boundaryToInterior_succ_newRow (b E : ℝ) {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1))
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω))) :
    (boundaryToInterior b E W (j + 1) ω).submatrix (fun x => ((0 : Fin (j + 1)), x)) id =
      freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω) := by
  obtain ⟨hU, -⟩ := boundaryToInterior_succ b E hj ω hA hη hF hF' hG
  obtain ⟨hD, hK⟩ := newRow_pencils (b := b) ⟨hA, fun _ => le_rfl, hη⟩ j
  rw [← nearSel_resolvent_transport b E _ _ hD hK, ← boundaryResolvent_eq b E j ω hF]
  ext x c
  simpa [headEquiv_inl] using congrFun (congrFun hU (Sum.inl x)) c

/-- **The new-tag injection** (the `q_{j+1}C₊` term of the full clock recursion):
for `j ≥ 1`, `Y_{j+1;j} = D₊ᴴD₊ = C₊` (the tag of the newest block, birth index `j`).
Hypotheses as in `boundaryToInterior_succ`. -/
theorem tagResponse_succ_new (b E : ℝ) {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1))
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω))) :
    tagResponse b E W (j + 1) j ω =
      (freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω))ᴴ *
        freshD b E (pathSchur E (pathAt W j ω)) (freshSample W j ω) := by
  obtain ⟨hU, -⟩ := boundaryToInterior_succ b E hj ω hA hη hF hF' hG
  obtain ⟨hD, hK⟩ := newRow_pencils (b := b) ⟨hA, fun _ => le_rfl, hη⟩ j
  set e := headEquiv j W
  have hP : (tagProjection W (j + 1) j).submatrix e e = Matrix.fromBlocks 1 0 0 0 := by
    ext (x | ⟨i, x⟩) (y | ⟨l, y⟩) <;>
      simp only [e, tagProjection, Matrix.submatrix_apply, headEquiv_inl, headEquiv_inr,
        Fin.val_succ, Fin.val_zero, Prod.mk.injEq, Fin.succ_inj, false_and, Fin.succ_ne_zero,
        Matrix.diagonal_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
        Matrix.one_apply] <;>
      split_ifs <;> simp_all
    all_goals exact Fin.succ_ne_zero _ (‹(0 : Fin (j + 1)) = _ ∧ _›.1).symm
  have hre : tagResponse b E W (j + 1) j ω =
      ((boundaryToInterior b E W (j + 1) ω).submatrix e id)ᴴ *
        (tagProjection W (j + 1) j).submatrix e e *
        (boundaryToInterior b E W (j + 1) ω).submatrix e id := by
    rw [tagResponse, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  rw [hre, hU, hP, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, boundaryResolvent_eq b E j ω hF,
    nearSel_resolvent_transport b E _ _ hD hK]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.zero_mul]

end BlockBand.Transmission.Bridge
