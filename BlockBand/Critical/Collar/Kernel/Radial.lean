module

public import BlockBand.Critical.Collar.Kernel.Collar
public import BlockBand.Wegner.ProjectedWegnerBasic

/-!
# The radial regulator as a Cayley-inverse old response

Support for the boundary clause of the collar kernel theorem: the strict clause is applied at
the Cayley inverse `z_b - 2iη(1 - tr)⁻¹` of `tr`, using `g(tr) ≤ g(r) + 2W(1-t²)`.

*Setting.* Deterministic: `X` a `2W × 2W` complex matrix with `Y = -Im X ⪰ 0`, energy `e` with
`η = Im z_b > 0`, `r = oldScattering b e X`, radial parameter `0 ≤ t < 1`.

## Results

* `one_sub_oldScattering_mul_conjTranspose_posSemidef`: `r` is a contraction (`I - rr* ⪰ 0`).
* `isUnit_det_one_sub_smul`: `I - t r` is invertible for `0 ≤ t < 1`.
* `radialOld b e t X = z_b - 2iη(I - t r)⁻¹` satisfies `oldScattering b e (radialOld …) = t r`
  (`oldScattering_radialOld`) and `-Im(radialOld …) ≻ 0` (`posDef_neg_imPart_radialOld`).
* `expectedCollarKernel_radial`, `collarKernelIntegrable_radial`: the regulated expected kernel
  `E𝒫(tUr)` is the unregulated one at the old response `radialOld b e t X`.
* `conductance_smul`: `g(tr) = t² g(r) + (1 - t²)·2W`; hence `g(tr) ≤ g(r) + 2W(1-t²)` for
  `g(r) ≥ 0` (`conductance_radial_le`).
* `matchedDistance_radialOld_le`: `d(radialOld …) ≤ d(X) + (1 - t)/(2η)`.

Measure: none (deterministic). No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder

variable {W : ℕ}

/-- `z_b - X = H_o + i(ηI + Y)` is invertible when `Y = -Im X ⪰ 0` and `η > 0`. -/
theorem isUnit_det_boundaryZ_sub (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    IsUnit (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X).det := by
  rw [← boundaryZMat_eq b e X]
  have hHo : ((((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) -
      rePart X).IsHermitian :=
    (by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X)
  have hpd : (((boundaryZ b e).im : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      -Critical.imPart X).PosDef :=
    (Matrix.PosDef.one.smul (by exact_mod_cast hη)).add_posSemidef hY
  exact isUnit_det_herm_add_I_smul_posDef hHo hpd

/-- **The old scattering matrix is a contraction**: `I - rr* = 4η Z⁻¹YZ⁻* ⪰ 0`,
`r = oldScattering b e X`, `Y = -Im X ⪰ 0`, `η > 0`. -/
theorem one_sub_oldScattering_mul_conjTranspose_posSemidef (b e : ℝ)
    (hη : 0 < (boundaryZ b e).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosSemidef) :
    (1 - Critical.oldScattering b e X * (Critical.oldScattering b e X)ᴴ).PosSemidef := by
  set Z := boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  have hZ := isUnit_det_boundaryZ_sub b e hη hY
  have hZZ : Z - Zᴴ = (2 * Complex.I) • (((boundaryZ b e).im : ℂ) • (1 : Matrix (Fin 2 × Fin W)
      (Fin 2 × Fin W) ℂ) + -Critical.imPart X) := by
    rw [show Z = boundaryZMat (((boundaryZ b e).re : ℂ) • 1 - rePart X) (-Critical.imPart X)
      (boundaryZ b e).im from (boundaryZMat_eq b e X).symm]
    exact boundaryZMat_sub_conjTranspose
      ((by simp [IsHermitian, conjTranspose_smul] :
        (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
        (rePart_isHermitian X)) hY.isHermitian
  have h := one_sub_scattering_mul_conjTranspose hZ hZZ
  have hr : Critical.oldScattering b e X = 1 - twoIEta (boundaryZ b e).im • Z⁻¹ := rfl
  rw [hr, h, sub_sub_cancel]
  exact (hY.mul_mul_conjTranspose_same Z⁻¹).smul (by exact_mod_cast (by positivity : (0:ℝ) ≤ 4 * (boundaryZ b e).im))

/-- For a contraction `r` (`I - rr* ⪰ 0`) and `0 ≤ t < 1`, `I - t r` is invertible. -/
theorem isUnit_det_one_sub_smul {ι : Type} [Fintype ι] [DecidableEq ι] {r : Matrix ι ι ℂ}
    (hr : (1 - r * rᴴ).PosSemidef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsUnit (1 - (t : ℂ) • r).det := by
  have key : IsUnit (1 - (t : ℂ) • rᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    rw [← sub_eq_zero]
    set v := x - y
    have hv : v = (t : ℂ) • (rᴴ *ᵥ v) := by
      have : (1 - (t : ℂ) • rᴴ) *ᵥ v = 0 := by simp only [v, mulVec_sub, hxy, sub_self]
      rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_zero] at this
      exact this
    have hq := hr.dotProduct_mulVec_nonneg v
    -- `‖rᴴv‖² ≤ ‖v‖²`
    have hle : (star (rᴴ *ᵥ v) ⬝ᵥ (rᴴ *ᵥ v)).re ≤ (star v ⬝ᵥ v).re := by
      have e1 : star v ⬝ᵥ ((1 - r * rᴴ) *ᵥ v) = star v ⬝ᵥ v - star (rᴴ *ᵥ v) ⬝ᵥ (rᴴ *ᵥ v) := by
        rw [sub_mulVec, one_mulVec, dotProduct_sub, ← mulVec_mulVec, star_mulVec,
          conjTranspose_conjTranspose, ← dotProduct_mulVec]
      have := (RCLike.nonneg_iff.mp hq).1
      rw [e1] at this
      simp only [RCLike.re_to_complex, Complex.sub_re] at this
      linarith
    have hvv : (star v ⬝ᵥ v).re = t ^ 2 * (star (rᴴ *ᵥ v) ⬝ᵥ (rᴴ *ᵥ v)).re := by
      conv_lhs => rw [hv]
      rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      simp only [Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
        Complex.re_ofReal_mul]
      ring
    have hn : 0 ≤ (star (rᴴ *ᵥ v) ⬝ᵥ (rᴴ *ᵥ v)).re := by
      rw [BlockBand.Wegner.re_star_dotProduct_self]; positivity
    have ht2 : t ^ 2 < 1 := by nlinarith
    have h0 : (star v ⬝ᵥ v).re = 0 := by
      have := hvv ▸ hle
      nlinarith
    rw [BlockBand.Wegner.re_star_dotProduct_self] at h0
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖v j‖)).1 h0 i
      (Finset.mem_univ i)
    simpa using hi
  have : (1 - (t : ℂ) • r) = (1 - (t : ℂ) • rᴴ)ᴴ := by
    simp [conjTranspose_sub, conjTranspose_smul]
  rw [this, det_conjTranspose]
  exact key.star

/-- The Cayley inverse of the regulated old scattering matrix `t r`:
`radialOld b e t X = z_b - 2iη(I - t r)⁻¹`, `r = oldScattering b e X`. -/
def radialOld (b e t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  boundaryZ b e • 1 - twoIEta (boundaryZ b e).im • (1 - (t : ℂ) • Critical.oldScattering b e X)⁻¹

theorem boundaryZ_sub_radialOld (b e t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - radialOld b e t X =
      twoIEta (boundaryZ b e).im • (1 - (t : ℂ) • Critical.oldScattering b e X)⁻¹ := by
  simp [radialOld]

/-- `(z_b - X')⁻¹ = (2iη)⁻¹(I - t r)` for `X' = radialOld b e t X`. -/
theorem inv_boundaryZ_sub_radialOld (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - radialOld b e t X)⁻¹ =
      (twoIEta (boundaryZ b e).im)⁻¹ • (1 - (t : ℂ) • Critical.oldScattering b e X) := by
  have hu := isUnit_det_one_sub_smul
    (one_sub_oldScattering_mul_conjTranspose_posSemidef b e hη hY) ht0 ht1
  have ha : twoIEta (boundaryZ b e).im ≠ 0 := by
    simp only [twoIEta]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne'))
      Complex.I_ne_zero
  rw [boundaryZ_sub_radialOld]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul,
    mul_nonsing_inv _ hu]

/-- `oldScattering b e (radialOld b e t X) = t • oldScattering b e X`. -/
theorem oldScattering_radialOld (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Critical.oldScattering b e (radialOld b e t X) = (t : ℂ) • Critical.oldScattering b e X := by
  have ha : twoIEta (boundaryZ b e).im ≠ 0 := by
    simp only [twoIEta]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne'))
      Complex.I_ne_zero
  have h := inv_boundaryZ_sub_radialOld b e hη hY ht0 ht1
  change 1 - twoIEta (boundaryZ b e).im • (boundaryZ b e • 1 - radialOld b e t X)⁻¹ = _
  rw [h, smul_smul, mul_inv_cancel₀ ha, one_smul, sub_sub_cancel]

/-- **The regulated kernel is the unregulated kernel at the Cayley inverse**:
`E𝒫(tUr) = E𝒫(U r')`, `r' = oldScattering (radialOld b e t X)` (`expectedCollarKernel`). -/
theorem expectedCollarKernel_radial (b e s ν : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Critical.expectedCollarKernel b e s ν t X =
      Critical.expectedCollarKernel b e s ν 1 (radialOld b e t X) := by
  unfold Critical.expectedCollarKernel
  rw [oldScattering_radialOld b e hη hY ht0 ht1]
  congr 1
  funext ω
  rw [Complex.ofReal_one, one_smul, Matrix.mul_smul]

/-- Integrability transfers along the same identity. -/
theorem collarKernelIntegrable_radial (b e s ν : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Critical.CollarKernelIntegrable b e s ν t X ↔
      Critical.CollarKernelIntegrable b e s ν 1 (radialOld b e t X) := by
  unfold Critical.CollarKernelIntegrable
  rw [oldScattering_radialOld b e hη hY ht0 ht1]
  simp only [Complex.ofReal_one, one_smul, Matrix.mul_smul]

/-- `-Im(radialOld b e t X) ≻ 0` for `0 ≤ t < 1` (`Y ⪰ 0`): the regulated old response is
strictly dissipative. -/
theorem posDef_neg_imPart_radialOld (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (-Critical.imPart (radialOld b e t X)).PosDef := by
  set X' := radialOld b e t X
  set η := (boundaryZ b e).im
  set r := Critical.oldScattering b e X
  set Z' := boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X'
  set Y' := -Critical.imPart X'
  have hu := isUnit_det_one_sub_smul
    (one_sub_oldScattering_mul_conjTranspose_posSemidef b e hη hY) ht0 ht1
  have ha : twoIEta η ≠ 0 := by
    simp only [twoIEta]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne'))
      Complex.I_ne_zero
  have hZ'eq : Z' = twoIEta η • (1 - (t : ℂ) • r)⁻¹ := boundaryZ_sub_radialOld b e t X
  have hZ' : IsUnit Z'.det := by
    rw [hZ'eq, det_smul, det_nonsing_inv]
    exact ((isUnit_iff_ne_zero.mpr ha).pow _).mul hu.ringInverse
  -- `Z' - Z'ᴴ = 2i(η + Y')`
  have hZZ : Z' - Z'ᴴ = (2 * Complex.I) • ((η : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      + Y') := by
    have hX := rePart_sub_I_smul_neg_imPart X'
    rw [show Z' = boundaryZMat (((boundaryZ b e).re : ℂ) • 1 - rePart X') Y' η from
      (boundaryZMat_eq b e X').symm]
    exact boundaryZMat_sub_conjTranspose
      ((by simp [IsHermitian, conjTranspose_smul] :
        (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
        (rePart_isHermitian X')) (by simpa [Y'] using (imPart_isHermitian X').neg)
  have hdef := one_sub_scattering_mul_conjTranspose hZ' hZZ
  have hr' : 1 - twoIEta η • Z'⁻¹ = (t : ℂ) • r := oldScattering_radialOld b e hη hY ht0 ht1
  rw [hr'] at hdef
  -- `Y' = (4η)⁻¹ Z'(I - t² rrᴴ)Z'ᴴ`
  have hZi : Z' * Z'⁻¹ = 1 := mul_nonsing_inv _ hZ'
  have hZih : (Z'⁻¹)ᴴ * Z'ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ hZ', conjTranspose_one]
  have hY'eq : Y' = (((4 * η)⁻¹ : ℝ) : ℂ) •
      (Z' * (1 - ((t : ℂ) • r) * ((t : ℂ) • r)ᴴ) * Z'ᴴ) := by
    rw [hdef, sub_sub_cancel, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have : Z' * (Z'⁻¹ * Y' * (Z'⁻¹)ᴴ) * Z'ᴴ = Y' := by
      calc Z' * (Z'⁻¹ * Y' * (Z'⁻¹)ᴴ) * Z'ᴴ = (Z' * Z'⁻¹) * Y' * ((Z'⁻¹)ᴴ * Z'ᴴ) := by
            simp only [Matrix.mul_assoc]
        _ = Y' := by rw [hZi, hZih, Matrix.one_mul, Matrix.mul_one]
    rw [this, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_smul]
  -- `I - t² rrᴴ ⪰ (1 - t²) I ≻ 0`
  have hc := one_sub_oldScattering_mul_conjTranspose_posSemidef b e hη hY
  have hsplit : (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - ((t : ℂ) • r) * ((t : ℂ) • r)ᴴ =
      (((1 - t ^ 2 : ℝ)) : ℂ) • 1 + ((t ^ 2 : ℝ) : ℂ) • (1 - r * rᴴ) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    module
  have hpos : ((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      ((t : ℂ) • r) * ((t : ℂ) • r)ᴴ).PosDef := by
    rw [hsplit]
    have h1t : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
    exact (Matrix.PosDef.one.smul (by exact_mod_cast h1t)).add_posSemidef
      (hc.smul (by exact_mod_cast (sq_nonneg t)))
  rw [hY'eq]
  have hZh : Function.Injective (Z'ᴴ *ᵥ ·) := by
    have : IsUnit Z'ᴴ := by
      rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose]; exact hZ'.star
    exact Matrix.mulVec_injective_iff_isUnit.mpr this
  have := hpos.conjTranspose_mul_mul_same hZh
  rw [conjTranspose_conjTranspose] at this
  exact this.smul (by
    have : (0 : ℝ) < (4 * η)⁻¹ := by positivity
    exact_mod_cast this)

/-- `g(t r) = t² g(r) + (1 - t²)·card ι` (conductance `g = Re Tr(I - r*r)`). -/
theorem conductance_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (r : Matrix ι ι ℂ) (t : ℝ) :
    Critical.conductance ((t : ℂ) • r) =
      t ^ 2 * Critical.conductance r + (1 - t ^ 2) * Fintype.card ι := by
  unfold Critical.conductance
  have : (1 : Matrix ι ι ℂ) - ((t : ℂ) • r)ᴴ * ((t : ℂ) • r) =
      ((t ^ 2 : ℝ) : ℂ) • (1 - rᴴ * r) + ((1 - t ^ 2 : ℝ) : ℂ) • 1 := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    module
  rw [this, trace_add, trace_smul, trace_smul, trace_one, smul_eq_mul, smul_eq_mul,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp

/-- `g(t r) ≤ g(r) + 2W(1 - t²)` for `0 ≤ t ≤ 1` and `g(r) ≥ 0` (old ports `Fin 2 × Fin W`). -/
theorem conductance_radial_le (r : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {t : ℝ}
    (ht1 : t ^ 2 ≤ 1) (hg : 0 ≤ Critical.conductance r) :
    Critical.conductance ((t : ℂ) • r) ≤ Critical.conductance r + 2 * W * (1 - t ^ 2) := by
  rw [conductance_smul, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  nlinarith

/-- Diagonal entries of a contraction are bounded by one: `|r_ii| ≤ 1` when `I - rr* ⪰ 0`. -/
theorem norm_apply_self_le_one_of_contraction {ι : Type} [Fintype ι] [DecidableEq ι]
    {r : Matrix ι ι ℂ} (hr : (1 - r * rᴴ).PosSemidef) (i : ι) : ‖r i i‖ ≤ 1 := by
  have hd := hr.diag_nonneg (i := i)
  have hd' : 0 ≤ (1 - (r * rᴴ) i i).re := by
    have := (RCLike.nonneg_iff.mp hd).1
    simpa [Matrix.sub_apply] using this
  have hrr : (r * rᴴ) i i = ((∑ k, ‖r i k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.mul_apply, conjTranspose_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hrr, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hd'
  have hle : ‖r i i‖ ^ 2 ≤ 1 :=
    (Finset.single_le_sum (f := fun k => ‖r i k‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)).trans (by linarith)
  nlinarith [norm_nonneg (r i i)]

/-- **Scalar distance along the radial regulator**: `d(radialOld b e t X) ≤ d(X) + (1 - t)/(2η)`
for `0 ≤ t < 1`, `Y = -Im X ⪰ 0`, `η = Im z_b > 0`, `W > 0`. -/
theorem matchedDistance_radialOld_le (b e : ℝ) (hη : 0 < (boundaryZ b e).im) (hW : 0 < W)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    matchedDistance b e (radialOld b e t X) ≤
      matchedDistance b e X + (1 - t) / (2 * (boundaryZ b e).im) := by
  set η := (boundaryZ b e).im
  set r := Critical.oldScattering b e X
  have ha : twoIEta η ≠ 0 := by
    simp only [twoIEta]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne'))
      Complex.I_ne_zero
  have h' := inv_boundaryZ_sub_radialOld b e hη hY ht0 ht1
  have h0 : (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ =
      (twoIEta η)⁻¹ • (1 - r) := by
    change _ = (twoIEta η)⁻¹ • (1 - (1 - twoIEta η • (boundaryZ b e • 1 - X)⁻¹))
    rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hdiff : (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      radialOld b e t X)⁻¹ = (boundaryZ b e • 1 - X)⁻¹ +
        ((twoIEta η)⁻¹ * ((1 - t : ℝ) : ℂ)) • r := by
    rw [h', h0]
    push_cast
    module
  have hc := one_sub_oldScattering_mul_conjTranspose_posSemidef b e hη hY
  have hbt : ∀ j : Fin 2, ‖blockTrace r j‖ ≤ 1 := by
    intro j
    unfold blockTrace
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    rw [inv_mul_le_iff₀ hWr, mul_one]
    calc ‖∑ a : Fin W, r (j, a) (j, a)‖ ≤ ∑ a : Fin W, ‖r (j, a) (j, a)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : Fin W, (1 : ℝ) :=
          Finset.sum_le_sum fun a _ => norm_apply_self_le_one_of_contraction hc _
      _ = W := by simp
  have hcoef : ‖(twoIEta η)⁻¹ * ((1 - t : ℝ) : ℂ)‖ = (1 - t) / (2 * η) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    simp only [twoIEta, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg hη.le, Complex.norm_I, mul_one]
    field_simp
  have hbtr : ∀ j : Fin 2, blockTrace ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W)
      (Fin 2 × Fin W) ℂ) - radialOld b e t X)⁻¹) j = blockTrace ((boundaryZ b e • 1 - X)⁻¹) j +
        ((twoIEta η)⁻¹ * ((1 - t : ℝ) : ℂ)) * blockTrace r j := by
    intro j
    rw [hdiff]
    simp only [blockTrace, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  have hone : ∀ j : Fin 2, ‖blockTrace ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W)
      (Fin 2 × Fin W) ℂ) - radialOld b e t X)⁻¹) j - matchedA e‖ ≤
        ‖blockTrace ((boundaryZ b e • 1 - X)⁻¹) j - matchedA e‖ + (1 - t) / (2 * η) := by
    intro j
    rw [hbtr, add_sub_right_comm]
    refine (norm_add_le _ _).trans ?_
    gcongr
    rw [norm_mul, hcoef]
    have : 0 ≤ (1 - t) / (2 * η) := div_nonneg (by linarith) (by positivity)
    nlinarith [hbt j, norm_nonneg (blockTrace r j)]
  unfold matchedDistance
  refine max_le ((hone 0).trans ?_) ((hone 1).trans ?_)
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_right _ _

end BlockBand.Critical.Collar.Kernel
