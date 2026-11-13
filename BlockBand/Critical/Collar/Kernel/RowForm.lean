module

public import BlockBand.Critical.Collar.Kernel.Row
public import BlockBand.Critical.Collar.Density.RowBound

/-!
# `q*𝒫(Ur)q = -η⁻¹ Im⟨ρ*q, 𝓗⁻¹ ρ*q⟩` (the three-block resolvent form of the collar kernel)

*Setting.* One collar sample `ω` with Hermitian `A_j, G`, real shift `s`, zero height,
`D = G - (e+s)` invertible, `X = X_h - iY` with `Y = -Im X ≻ 0`; `𝓗 = ℋ_X` at energy `e + s`,
`𝓡 = 𝓗⁻¹`, `Ŷ = diag(Y, 0)`, fresh row `ρ = (z_b + e + s - A, -B)`.

## Results

* `topInclusion_sandwich`, `collarResolvent_top_sandwich`: `E₁ Y E₁* = Ŷ` and the bridge
  `(𝓡E₁) Y (𝓡E₁)* = 𝓡 Ŷ 𝓡*` (rectangular products with the `Matrix` instance forced, avoiding
  the `CStarMatrix` default `HMul`).
* `collar_poissonKernel_eq_resolvent`: `𝒫(Ur) = η⁻¹ ρ ((2i)⁻¹(𝓡* - 𝓡)) ρ*`.
* `collar_poissonKernel_quad`: `q*𝒫(Ur)q = -η⁻¹ Im⟨ρ*q, 𝓡 ρ*q⟩` (a real number).
* `collarRow_conjTranspose_mulVec`: `ρ* q = collarRowVec (conj(z_b + e + s)) q ω`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec)
open scoped ComplexOrder

variable {W : ℕ}

/-- Rectangular matrix product with the `Matrix` instance forced. -/
local notation:70 A:70 " ⬝* " B:71 =>
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

theorem sandwich_assoc {k l m : Type*} [Fintype l] [Fintype m] (P : Matrix k l ℂ)
    (E : Matrix l m ℂ) (Y : Matrix m m ℂ) : (P * E) * Y * (P * E)ᴴ = P * (E * Y * Eᴴ) * Pᴴ := by
  rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem fromRows_one_zero_sandwich {m n : Type*} [Fintype m] [DecidableEq m] (Y : Matrix m m ℂ) :
    (Matrix.fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ)) * Y *
      (Matrix.fromRows (1 : Matrix m m ℂ) (0 : Matrix n m ℂ))ᴴ = Matrix.fromBlocks Y 0 0 0 := by
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
  simp

/-- `E₁ Y E₁* = Ŷ = diag(Y, 0)`. -/
theorem topInclusion_sandwich (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (topInclusion ⬝* Y) ⬝* (topInclusion (W := W))ᴴ = topLift Y :=
  fromRows_one_zero_sandwich Y

/-- **The bridge** `(𝓡E₁) Y (𝓡E₁)* = 𝓡 Ŷ 𝓡*` (any square `𝓡`). -/
theorem collarResolvent_top_sandwich (R : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ((R ⬝* topInclusion) ⬝* Y) ⬝* (R ⬝* topInclusion)ᴴ = R * topLift Y * Rᴴ := by
  rw [sandwich_assoc, topInclusion_sandwich]

/-- `star q ⬝ᵥ (P M P*) q = star (P* q) ⬝ᵥ M (P* q)`. -/
theorem dotProduct_sandwich {k l : Type*} [Fintype k] [Fintype l] (P : Matrix k l ℂ)
    (M : Matrix l l ℂ) (q : k → ℂ) :
    star q ⬝ᵥ ((P * M * Pᴴ) *ᵥ q) = star (Pᴴ *ᵥ q) ⬝ᵥ (M *ᵥ (Pᴴ *ᵥ q)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

/-- `⟨y, M* y⟩ = conj ⟨y, M y⟩`. -/
theorem dotProduct_conjTranspose_mulVec {l : Type*} [Fintype l] (M : Matrix l l ℂ) (y : l → ℂ) :
    star y ⬝ᵥ (Mᴴ *ᵥ y) = star (star y ⬝ᵥ (M *ᵥ y)) := by
  calc star y ⬝ᵥ (Mᴴ *ᵥ y) = (star y ᵥ* Mᴴ) ⬝ᵥ y := dotProduct_mulVec _ _ _
    _ = star (M *ᵥ y) ⬝ᵥ y := by rw [star_mulVec]
    _ = star (star y ⬝ᵥ (M *ᵥ y)) := by
        rw [star_dotProduct]

/-- `collarSchur` is invertible (Hermitian `A_j, G`, `Y ≻ 0`). -/
theorem isUnit_det_collarSchur (b e s : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosDef) :
    IsUnit (collarSchur e s X ω).det := by
  rw [← collarReaction_add b e s X ω]
  refine isUnit_det_herm_add_I_smul_posDef ((collarReaction_isHermitian b e s hA hG).add ?_) hY
  exact (by simp [IsHermitian, conjTranspose_smul] :
    (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
    (rePart_isHermitian X)

/-- **`𝒫(Ur)` through the full three-block resolvent**: for one collar sample (Hermitian `A_j`,
`G`, `D = G - (e+s)` invertible), real shift `s`, zero height and `Y = -Im X ≻ 0`:
`𝒫(Ur) = η⁻¹ ρ ((2i)⁻¹(𝓡* - 𝓡)) ρ*`, `𝓡 = ℋ_X⁻¹` at energy `e + s`. -/
theorem collar_poissonKernel_eq_resolvent (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : Critical.CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (hD : IsUnit (middleBlock e s ω).det) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosDef) :
    Critical.poissonKernel (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X) =
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) • (collarRow b e s ω *
        ((2 * Complex.I)⁻¹ • (((collarMatrix (e + s) X ω)⁻¹)ᴴ - (collarMatrix (e + s) X ω)⁻¹)) *
        (collarRow b e s ω)ᴴ) := by
  have hS := isUnit_det_collarSchur b e s hA hG hY
  have hH := isUnit_det_collarMatrix b e s hA hG hD hY
  rw [collar_poissonKernel_eq_row b e s hη hA hG hY,
    ← collarResolvent_mul_top e s X ω hD hS hH]
  congr 1
  rw [← collarResolvent_ward (e + s) hA hG hH, ← collarResolvent_top_sandwich]
  exact sandwich_assoc _ _ _

/-- **`q*𝒫(Ur)q = -η⁻¹ Im⟨ρ*q, 𝓡 ρ*q⟩`** (setting of `collar_poissonKernel_eq_resolvent`). -/
theorem collar_poissonKernel_quad (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : Critical.CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (hD : IsUnit (middleBlock e s ω).det) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosDef) (q : Fin 2 × Fin W → ℂ) :
    star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s 0 ω *
        Critical.oldScattering b e X) *ᵥ q) =
      (((boundaryZ b e).im⁻¹ * -(star ((collarRow b e s ω)ᴴ *ᵥ q) ⬝ᵥ
        ((collarMatrix (e + s) X ω)⁻¹ *ᵥ ((collarRow b e s ω)ᴴ *ᵥ q))).im : ℝ) : ℂ) := by
  rw [collar_poissonKernel_eq_resolvent b e s hη hA hG hD hY, smul_mulVec, dotProduct_smul,
    dotProduct_sandwich, smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub,
    dotProduct_conjTranspose_mulVec]
  set w := star ((collarRow b e s ω)ᴴ *ᵥ q) ⬝ᵥ
    ((collarMatrix (e + s) X ω)⁻¹ *ᵥ ((collarRow b e s ω)ᴴ *ᵥ q))
  have h : (2 * Complex.I)⁻¹ * (star w - w) = ((-w.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]; ring
  rw [smul_eq_mul, smul_eq_mul, h]
  push_cast
  ring

/-- `ρ* q = ((conj(z_b + e + s) - A) q, -B* q)`. -/
theorem collarRow_conjTranspose_mulVec (b e s : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (q : Fin 2 × Fin W → ℂ) :
    (collarRow b e s ω)ᴴ *ᵥ q =
      collarRowVec (star (boundaryZ b e + ((e + s : ℝ) : ℂ))) q ω := by
  have hD := blockDiag_isHermitian' hA
  rw [collarRow, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mulVec,
    collarRowVec, conjTranspose_sub, conjTranspose_smul, hD.eq, conjTranspose_one, sub_mulVec,
    smul_mulVec, one_mulVec, conjTranspose_neg, neg_mulVec]

end BlockBand.Critical.Collar.Kernel
