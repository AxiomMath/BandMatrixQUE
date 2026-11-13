module

public import BlockBand.Critical.MatrixClosing.MiddleShift.Statement
public import BlockBand.Critical.Collar.Kernel.Radial

/-!
# The middle-only shifted collar mean: the two kernels share one closed matrix

Deterministic, one collar sample with Hermitian blocks, `Y = -Im X ≻ 0`.

Shifting only the middle block `G - e ↦ G - (e+s)` is **not** a common shift. Writing the
middle-shifted collar matrix as the collar at energy `e' = e+s` with old response `X - s`
(`[[A-e-X, B],[B*, G-e-s]] = [[A-e'-(X-s), B],[B*, G-e']]`) keeps the closed matrix
`N = A - e - X - B(G-e-s)⁻¹B*` but changes the boundary reference `z_b(e) ↦ z_b(e')` and the outside
factor `Z = z_b(e) - X ↦ Z' = z_b(e') - (X - s)`:
* `commonKernel_eq`: `𝒫' = η'⁻¹(I - Z'N⁻¹)Y(I - Z'N⁻¹)*` (the kernel at `(e', X - s)`);
* `middleKernel_eq`: `𝒫(U_s𝔯) = η⁻¹(I - ZN⁻¹)Y(I - ZN⁻¹)*` (same `N`);
* `one_sub_mul_inv_split`: `I - ZN⁻¹ = (I - Z'N⁻¹) + ΔN⁻¹`, `Δ = z_b(e') + s - z_b(e)`.
Also `imPart_sub_smul_one`, `middleReaction_isHermitian`, `middleReaction_add`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Kernel
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## The two weighted boundary identities with the same closed matrix
-/

theorem imPart_sub_smul_one (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (s : ℝ) :
    imPart (X - (s : ℂ) • 1) = imPart X := by
  simp only [imPart, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]
  congr 1
  abel

theorem middleReaction_isHermitian (b e s : ℝ) {ω : CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian) :
    (middleReaction b e s ω).IsHermitian := by
  have hD := blockDiag_isHermitian' hA
  have hGi : ((ω.2 - ((e + s : ℝ) : ℂ) • 1)⁻¹).IsHermitian := by
    refine IsHermitian.inv (hG.sub ?_)
    simp [IsHermitian, conjTranspose_smul]
  have hBGB := isHermitian_mul_mul_conjTranspose (bondMatrix .common ω.1.2) hGi
  have : ((e : ℂ) + ((boundaryZ b e).re : ℂ)) = (((e + (boundaryZ b e).re : ℝ)) : ℂ) := by
    push_cast; ring
  rw [middleReaction, this]
  refine (hD.sub ?_).sub hBGB
  simp [IsHermitian, conjTranspose_smul]

/-- **Commonly shifted kernel at `(e+s, X - s)`** (the kernel of
`ExactBoundaryMeanContract` at energy `e+s`):
`𝒫' = η'⁻¹(I - Z'N⁻¹)Y(I - Z'N⁻¹)*`.
-/
theorem commonKernel_eq (b e s : ℝ) (hη' : 0 < (boundaryZ b (e + s)).im)
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef) :
    BlockBand.Internal.Contracts.Critical.poissonKernel (collarScattering b (e + s) 0 0 ω * oldScattering b (e + s) (X - (s : ℂ) • 1)) =
      (((boundaryZ b (e + s)).im⁻¹ : ℝ) : ℂ) •
        ((1 - (boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1)) *
            (collarSchur (e + s) 0 (X - (s : ℂ) • 1) ω)⁻¹) * (-imPart X) *
          (1 - (boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1)) *
            (collarSchur (e + s) 0 (X - (s : ℂ) • 1) ω)⁻¹)ᴴ) := by
  have hY' : (-imPart (X - (s : ℂ) • 1)).PosDef := by rwa [imPart_sub_smul_one]
  have h := (collar_poissonKernel_eq b (e + s) 0 hη' hA hG (X - (s : ℂ) • 1) hY').2.1
  rw [imPart_sub_smul_one] at h
  exact h

/-- The closed matrix of the middle-shifted collar is the commonly shifted one at `(e+s, X - s)`:
`K_c^{mid} + H_o + iY = A - e - X - B(G - (e+s))⁻¹B* = collarSchur (e+s) 0 (X - s)`. -/
theorem middleReaction_add (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) :
    middleReaction b e s ω + (((boundaryZ b e).re : ℂ) • 1 - rePart X) +
        Complex.I • (-imPart X) = collarSchur (e + s) 0 (X - (s : ℂ) • 1) ω := by
  have hX := rePart_sub_I_smul_neg_imPart X
  rw [middleReaction, collarSchur]
  generalize rePart X = Xh at *
  generalize imPart X = Ym at *
  subst hX
  simp only [add_zero]
  push_cast
  module

/-- **Middle-shifted kernel** (the weighted boundary identity for `K_c^{mid}`):
`𝒫(U_s𝔯) = η⁻¹(I - ZN⁻¹)Y(I - ZN⁻¹)*`, `Z = z_b(e) - X`, same `N` as `commonKernel_eq`. -/
theorem middleKernel_eq (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef) :
    middleKernel b e s 1 X ω =
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) •
        ((1 - (boundaryZ b e • 1 - X) * (collarSchur (e + s) 0 (X - (s : ℂ) • 1) ω)⁻¹) *
          (-imPart X) *
          (1 - (boundaryZ b e • 1 - X) * (collarSchur (e + s) 0 (X - (s : ℂ) • 1) ω)⁻¹)ᴴ) := by
  set Kc := middleReaction b e s ω
  set Ho := ((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - rePart X
  set Y := -imPart X
  have hKc : Kc.IsHermitian := middleReaction_isHermitian b e s hA hG
  have hHo : Ho.IsHermitian :=
    (by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X)
  have hYh : Y.IsHermitian := hY.isHermitian
  have hZ : IsUnit (boundaryZMat Ho Y (boundaryZ b e).im).det := by
    rw [boundaryZMat_eq b e X]; exact isUnit_det_boundaryZ_sub b e hη hY.posSemidef
  have hM : IsUnit (Kc + Ho + Complex.I • Y).det :=
    isUnit_det_herm_add_I_smul_posDef (hKc.add hHo) hY
  have h := (weightedBoundaryIdentity hKc hHo hYh hη hZ hM).2
  rw [middleReaction_add, boundaryZMat_eq b e X] at h
  rw [middleKernel, Complex.ofReal_one, one_smul]
  convert h using 2
  rfl

/-- `I - ZN⁻¹ = (I - Z'N⁻¹) + Δ N⁻¹`, `Z = Z' - Δ`, `Δ = z_b(e+s) + s - z_b(e)`. -/
theorem one_sub_mul_inv_split (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    1 - (boundaryZ b e • 1 - X) * R = (1 - (boundaryZ b (e + s) • 1 - (X - (s : ℂ) • 1)) * R) +
      (boundaryZ b (e + s) + s - boundaryZ b e) • R := by
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, add_smul, sub_smul]
  abel

end BlockBand.Critical.MatrixClosing
