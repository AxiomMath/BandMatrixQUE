module

public import BlockBand.Transmission.Bridge.Transport

/-!
# One growth step: `𝒰_{j+1} = [D₊ ; 𝒰_j N]` with `N = freshTransport b E 𝕏_j`

Proves `boundaryToInterior_succ`, the transport of the boundary-to-interior map along one step
of the near-end growth.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- The one-step transport `N` of the growth step `j → j+1`: the one-layer transport
`freshTransport` at the old two-port Schur matrix `𝕏_j` and the fresh layer of the step. -/
abbrev transportN (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  freshTransport b E (pathSchur E (pathAt W j ω)) (freshSample W j ω)

theorem fromRows_add' {m₁ m₂ n : Type*} (A₁ B₁ : Matrix m₁ n ℂ) (A₂ B₂ : Matrix m₂ n ℂ) :
    Matrix.fromRows A₁ A₂ + Matrix.fromRows B₁ B₂ = Matrix.fromRows (A₁ + B₁) (A₂ + B₂) := by
  ext (i | i) j <;> simp

/-- `z - X_j` is invertible along a passive sample. -/
theorem isUnit_nearPencil (b E : ℝ) (j : ℕ) (ω : GrowthPath W)
    (h : PassiveSample b E (fun _ => 0) ω) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathX b E W j ω) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  have hp : boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - pathX b E W j ω =
    portPencil (pathX b E W j ω) (boundaryZ b E) := rfl
  rw [hp, matrixImaginaryPart_portPencil_general, sub_eq_add_neg, add_comm]
  exact Matrix.PosDef.posSemidef_add (pathNearSchur_passive h j) (Matrix.PosDef.one.smul h.height)

/-- **Transport of the boundary-to-interior map**: for `j ≥ 1`, newest block first, the
boundary-to-interior map of the length-`j+1` path is `[ι*ℝ_j N ; 𝒰_j N]` with
`N = transportN b E W j ω = freshTransport b E 𝕏_j (freshSample W j ω)`; its new row
`ι*ℝ_jN` equals `D₊ = [𝒢₁₂, 𝒢₁₁Kℝ₁₂]` (`boundaryToInterior_succ_newRow`), and
`ℝ_{j+1} = z⁻¹(1 - (B_{j+1}ι*)ᴴ ι*ℝ_jN - C_fᴴ 𝒰_jN)`. -/
theorem boundaryToInterior_succ (b E : ℝ) {j : ℕ} (hj : 1 ≤ j) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1))
    (hG : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (Matrix.of fun (u v : Fin 1 × Fin W) => pathX b E W j ω u.2 v.2) (freshSample W j ω))) :
    (boundaryToInterior b E W (j + 1) ω).submatrix (headEquiv j W) id =
        Matrix.fromRows (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω)
          (boundaryToInterior b E W j ω * transportN b E W j ω) ∧
      boundaryResolvent b E W (j + 1) ω = (boundaryZ b E)⁻¹ • (1 -
        (ω.2 (j + 1) * nearSel W)ᴴ * (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω) -
        (farCoupling W j ω)ᴴ * (boundaryToInterior b E W j ω * transportN b E W j ω)) := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have hPS : PassiveSample b E (fun _ => 0) ω := ⟨hA, fun _ => le_rfl, hη⟩
  have hX := pathSchur_isHermitian E j ω hA
  have hD : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
      portBlock (pathSchur E (pathAt W j ω)) 1 1) :=
    portPencil_isUnit _ (by
      ext x y; simpa [portBlock, Matrix.conjTranspose_apply] using
        congrFun (congrFun hX (1, x)) (1, y)) hη
  have hK := isUnit_nearPencil b E j ω hPS
  rw [pathX_eq] at hK hG
  have hfresh := fresh_identity b E (pathSchur E (pathAt W j ω)) (ω.1 j) (ω.2 (j + 1)) hz hD hK hG
  rw [← boundaryResolvent_eq b E j ω hF] at hfresh
  obtain ⟨hU1, hU2⟩ := full_solution b E j ω (isUnit_fullPathMatrix b E j ω hA hη hF)
  rw [coupling_split] at hU1 hU2
  obtain ⟨c1, c2, c3⟩ := transport_algebra (pathMatrix (pathAt W j ω) - (E : ℂ) • 1)
    (nearCol W j ω) (farCoupling W j ω) (boundaryToInterior b E W j ω)
    (boundaryResolvent b E W j ω) (transportN b E W j ω) (nearSel W) (ω.1 j - (E : ℂ) • 1)
    (ω.2 (j + 1)) hz hU1 hU2 (nearSel_mul_farCoupling j ω) nearSel_mul_conjTranspose
    (farCoupling_mul_freshTransport b E j ω _ _) hfresh
  set e := headEquiv j W
  set Un := nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω
  set Uo := boundaryToInterior b E W j ω * transportN b E W j ω
  set R' := (boundaryZ b E)⁻¹ • (1 - (ω.2 (j + 1) * nearSel W)ᴴ * Un - (farCoupling W j ω)ᴴ * Uo)
  set U' : Matrix (Fin (j + 1) × Fin W) (Fin 2 × Fin W) ℂ :=
    (Matrix.fromRows Un Uo).submatrix e.symm id
  have hU'e : U'.submatrix e id = Matrix.fromRows Un Uo := by
    simp only [U', Matrix.submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id,
      Matrix.submatrix_id_id]
  have hrows : ∀ {q : Type} [Fintype q] (M : Matrix (Fin (j + 1) × Fin W) q ℂ)
      (Rm : Matrix q (Fin 2 × Fin W) ℂ), (M * Rm).submatrix e id = M.submatrix e id * Rm := by
    intro q _ M Rm
    have := Matrix.submatrix_mul_equiv M Rm e (Equiv.refl q) id
    simpa only [Equiv.coe_refl, Matrix.submatrix_id_id] using this.symm
  have h1 : (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) * U' +
      pathPortCoupling (pathAt W (j + 1) ω) * R' = 0 := by
    have hsub : ((pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) * U' +
        pathPortCoupling (pathAt W (j + 1) ω) * R').submatrix e id = 0 := by
      rw [show ∀ (X Y : Matrix (Fin (j + 1) × Fin W) (Fin 2 × Fin W) ℂ),
          (X + Y).submatrix e id = X.submatrix e id + Y.submatrix e id from fun _ _ => rfl,
        ← Matrix.submatrix_mul_equiv _ _ e e id, hrows,
        pathMatrix_succ_submatrix, coupling_succ_submatrix hj, hU'e,
        Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, fromRows_add', c1, c2,
        Matrix.fromRows_zero]
    have := congrArg (fun M => M.submatrix e.symm id) hsub
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Function.comp_id,
      Matrix.submatrix_id_id] at this
    rw [this]; rfl
  have h2 : (pathPortCoupling (pathAt W (j + 1) ω))ᴴ * U' + boundaryZ b E • R' = 1 := by
    have hC : (pathPortCoupling (pathAt W (j + 1) ω))ᴴ * U' =
        ((pathPortCoupling (pathAt W (j + 1) ω)).submatrix e id)ᴴ * U'.submatrix e id := by
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    rw [hC, coupling_succ_submatrix hj, hU'e,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
    exact c3
  obtain ⟨hUeq, hReq⟩ := full_unique b E (j + 1) ω (isUnit_fullPathMatrix b E (j + 1) ω hA hη hF')
    U' R' h1 h2
  exact ⟨by rw [← hUeq, hU'e], hReq.symm⟩

end BlockBand.Transmission.Bridge
