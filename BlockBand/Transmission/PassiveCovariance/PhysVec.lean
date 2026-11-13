module

public import BlockBand.Transmission.PassiveCovariance.SdQExpand
public import BlockBand.Transmission.SourceMixing.Weighted

/-!
# Physical vectors and block-diagonal weights,)

* `IsPhys w`: `w` vanishes on the port sites; `isPhys_physVec`.
* `isPhys_conjT_mulVec`: if `B₀₁ = 0` then `Bᴴw` is physical for physical `w`.
* `form_portProj_eq_zero`: `w*(Π R)y = 0` for physical `w` (`Π = portProj`).
* `form_dRow`: `w*(d_q Γ)y = s_q·w*Γy` for physical `w`, `s₀ = 1-2b`, `s₁ = b` (`sRow`).
* `form_bProj_phys`: `w*(P₁Γ)y = 0` and `w*(P₀Γ)y = w*Γy` for physical `w`.
* `kHat_mbar_blk`: `K̂M̄` is block diagonal (`blkAt _ 0 1 = 0`) when `H₀ - S̄` is invertible.
* `conj_form`: `conj(x*Ay) = y*Aᴴx`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- A vector supported on the physical sites. -/
def IsPhys (w : LayerSite W .oneBlockOnePort → ℂ) : Prop := ∀ x : Fin W, w (port x) = 0

theorem isPhys_physVec (v : Fin W → ℂ) : IsPhys (physVec v) := fun _ => rfl

theorem isPhys_conjT_mulVec {B : LayerMat W} (hB : blkAt B 0 1 = 0) {w : LayerSite W .oneBlockOnePort → ℂ}
    (hw : IsPhys w) : IsPhys (Bᴴ *ᵥ w) := by
  intro x
  rw [mulVec, dotProduct, sum_layerSite]
  have h : ∀ y, B (phys y) (port x) = 0 := fun y => by
    have := congrFun (congrFun hB y) x
    simpa [blkAt, siteOf] using this
  have hw' : ∀ y, w (port y) = 0 := hw
  simp [conjTranspose_apply, h, hw']

/-- The `(1, 2)` block of `K̂M̄` vanishes. -/
theorem kHat_mbar_blk (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (hW : 1 ≤ W)
    (hD : IsUnit (dressed b E X)) : blkAt (kHat b E X * mbarSide b E X false) 0 1 = 0 := by
  have hinv : dressed b E X * (dressed b E X)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  obtain ⟨-, -, -, -, h01, -⟩ := blkAt_dressed_inv b E X hW _ hinv
  obtain ⟨-, k01, -, -⟩ := SourceMixing.blkAt_kHat b E X
  have e : mbarSide b E X false = (dressed b E X)⁻¹ := rfl
  rw [e, blkAt_mul, Fin.sum_univ_two, h01, k01, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem portProj_mulVec_phys {w : LayerSite W .oneBlockOnePort → ℂ} (hw : IsPhys w) :
    (portProj : LayerMat W) *ᵥ w = 0 := by
  have hw' : ∀ p : Fin 1 × Fin W, w (Sum.inr p) = 0 := fun p => by
    obtain ⟨i, x⟩ := p; obtain rfl : i = 0 := Subsingleton.elim _ _; exact hw x
  funext α
  rcases α with α | α <;>
    simp [mulVec, dotProduct, portProj, fromBlocks, Fintype.sum_sum_type, hw']

theorem portProj_conjT : (portProj : LayerMat W)ᴴ = portProj := by
  rw [portProj, fromBlocks_conjTranspose]; simp

theorem star_form_eq (w y : LayerSite W .oneBlockOnePort → ℂ) (A : LayerMat W) :
    star w ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ w) ⬝ᵥ y := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

theorem form_portProj_eq_zero {w : LayerSite W .oneBlockOnePort → ℂ} (hw : IsPhys w)
    (R : LayerMat W) (y : LayerSite W .oneBlockOnePort → ℂ) :
    star w ⬝ᵥ ((portProj * R) *ᵥ y) = 0 := by
  rw [star_form_eq, conjTranspose_mul, portProj_conjT, ← mulVec_mulVec, portProj_mulVec_phys hw,
    mulVec_zero, star_zero, zero_dotProduct]

/-- The row weights on the physical block: `s₀ = 1 - 2b`, `s₁ = b`. -/
def sRow (b : ℝ) (q : Fin 2) : ℂ := if q = 0 then ((1 - 2 * b : ℝ) : ℂ) else (b : ℂ)

theorem form_diagonal_phys {d : LayerSite W .oneBlockOnePort → ℂ} {s : ℂ}
    (hd : ∀ x, d (phys x) = s) {w : LayerSite W .oneBlockOnePort → ℂ}
    (hw : IsPhys w) (Γ : LayerMat W) (y : LayerSite W .oneBlockOnePort → ℂ) :
    star w ⬝ᵥ ((diagonal d * Γ) *ᵥ y) = s * star w ⬝ᵥ (Γ *ᵥ y) := by
  have hw' : ∀ y, w (port y) = 0 := hw
  rw [← mulVec_mulVec, dotProduct, dotProduct, sum_layerSite, sum_layerSite]
  simp only [mulVec_diagonal, Pi.star_apply, hw', star_zero, zero_mul, Finset.sum_const_zero,
    add_zero, hd]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem form_dRow {b : ℝ} (q : Fin 2) {w : LayerSite W .oneBlockOnePort → ℂ} (hw : IsPhys w)
    (Γ : LayerMat W) (y : LayerSite W .oneBlockOnePort → ℂ) :
    star w ⬝ᵥ ((dRow b q * Γ) *ᵥ y) = sRow b q * star w ⬝ᵥ (Γ *ᵥ y) := by
  unfold dRow sRow
  split_ifs
  · exact form_diagonal_phys (fun _ => rfl) hw Γ y
  · exact form_diagonal_phys (fun _ => rfl) hw Γ y

theorem form_bProj_phys (p : Fin 2) {w : LayerSite W .oneBlockOnePort → ℂ} (hw : IsPhys w)
    (Γ : LayerMat W) (y : LayerSite W .oneBlockOnePort → ℂ) :
    star w ⬝ᵥ ((bProj p * Γ) *ᵥ y) = (if p = 0 then 1 else 0) * star w ⬝ᵥ (Γ *ᵥ y) := by
  refine form_diagonal_phys (fun x => ?_) hw Γ y
  simp [bInd, blkOf, eq_comm]

/-- `conj(x*Ay) = y*Aᴴx`. -/
theorem conj_form {n : Type*} [Fintype n] (x y : n → ℂ) (A : Matrix n n ℂ) :
    conj (star x ⬝ᵥ (A *ᵥ y)) = star y ⬝ᵥ (Aᴴ *ᵥ x) := by
  simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, conjTranspose_apply,
    Complex.star_def, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end BlockBand.Transmission.PassiveCovariance
