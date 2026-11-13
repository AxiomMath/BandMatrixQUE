module

public import BlockBand.Critical.MatrixClosing.Boundary.RankOne
public import BlockBand.Critical.Collar.Kernel.Radial

/-!
# Matrix closing, boundary clause: the twisted old response

Deterministic. The old response `X` is Hermitian (lossless); `u` is a unit vector; `‖w‖ < 1`. The
Cayley inverse `X'` may be unbounded. No hypothesis is used.

* `oldScattering_mul_conjTranspose`, `conjTranspose_oldScattering_mul`: `r` is unitary.
* `twistOld b e w u X = z_b - 2iη(I - r(I - (1-w)uu*))⁻¹` (the Cayley inverse `X'`), with
  `oldScattering_twistOld` (`r(X') = r'`), `posSemidef_neg_imPart_twistOld` (`-Im X' ⪰ 0`),
  `conductance_twistOld` (`g(r') = 1 - |w|²`), `matchedDistance_twistOld_le`
  (`d(X') ≤ d(X) + 1/(ηW)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Boundary

open Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Kernel
open scoped ComplexOrder ComplexConjugate

variable {W : ℕ}

theorem imPart_eq_zero_of_isHermitian {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) : Critical.imPart X = 0 := by
  rw [Critical.imPart, hX.eq, sub_self, smul_zero]

theorem twoIEta_ne_zero {η : ℝ} (hη : 0 < η) : twoIEta η ≠ 0 := by
  simp only [twoIEta]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne')) Complex.I_ne_zero

/-- `1 - r = 2iη(z_b - X)⁻¹` is invertible (`Y = -Im X ⪰ 0`). -/
theorem isUnit_det_one_sub_oldScattering (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    IsUnit (1 - Critical.oldScattering b e X).det := by
  have hZ := isUnit_det_boundaryZ_sub b e hη hY
  have e1 : 1 - Critical.oldScattering b e X =
      twoIEta (boundaryZ b e).im • (boundaryZ b e • 1 - X)⁻¹ := by
    rw [Critical.oldScattering, sub_sub_cancel]
  rw [e1, det_smul, det_nonsing_inv]
  exact ((isUnit_iff_ne_zero.mpr (twoIEta_ne_zero hη)).pow _).mul hZ.ringInverse

/-- **The lossless old scattering matrix is unitary**: `rr* = 1` for Hermitian `X`. -/
theorem oldScattering_mul_conjTranspose (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    Critical.oldScattering b e X * (Critical.oldScattering b e X)ᴴ = 1 := by
  have h0 : Critical.imPart X = 0 := imPart_eq_zero_of_isHermitian hX
  have hY : (-Critical.imPart X).PosSemidef := by rw [h0, neg_zero]; exact PosSemidef.zero
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
  rw [hr, h, h0, neg_zero, Matrix.mul_zero, Matrix.zero_mul, smul_zero, sub_zero]

theorem conjTranspose_oldScattering_mul (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    (Critical.oldScattering b e X)ᴴ * Critical.oldScattering b e X = 1 :=
  mul_eq_one_comm.mp (oldScattering_mul_conjTranspose b e hη hX)

/-!
## The twisted old response
-/

/-- **The rank-one damped twist of the old response**: the Cayley inverse
`X' = z_b - 2iη(I - r')⁻¹` of `r' = r(I - (1-w)uu*)`, `r = oldScattering b e X`. -/
def twistOld (b e : ℝ) (w : ℂ) (u : Fin 2 × Fin W → ℂ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  boundaryZ b e • 1 - twoIEta (boundaryZ b e).im •
    (1 - Critical.oldScattering b e X * twist w u)⁻¹

variable {b e : ℝ} {w : ℂ} {u : Fin 2 × Fin W → ℂ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

theorem isUnit_det_one_sub_oldScattering_twist (hη : 0 < (boundaryZ b e).im) (hX : X.IsHermitian)
    (hu : star u ⬝ᵥ u = 1) (hw : ‖w‖ < 1) :
    IsUnit (1 - Critical.oldScattering b e X * twist w u).det := by
  have hY : (-Critical.imPart X).PosSemidef := by
    rw [imPart_eq_zero_of_isHermitian hX, neg_zero]; exact PosSemidef.zero
  exact isUnit_det_one_sub_mul_twist (conjTranspose_oldScattering_mul b e hη hX)
    (isUnit_det_one_sub_oldScattering b e hη hY) hu hw

theorem boundaryZ_sub_twistOld :
    boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - twistOld b e w u X =
      twoIEta (boundaryZ b e).im • (1 - Critical.oldScattering b e X * twist w u)⁻¹ := by
  simp [twistOld]

theorem inv_boundaryZ_sub_twistOld (hη : 0 < (boundaryZ b e).im) (hX : X.IsHermitian)
    (hu : star u ⬝ᵥ u = 1) (hw : ‖w‖ < 1) :
    (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - twistOld b e w u X)⁻¹ =
      (twoIEta (boundaryZ b e).im)⁻¹ • (1 - Critical.oldScattering b e X * twist w u) := by
  have hu' := isUnit_det_one_sub_oldScattering_twist hη hX hu hw
  have ha := twoIEta_ne_zero hη
  rw [boundaryZ_sub_twistOld]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul,
    mul_nonsing_inv _ hu']

/-- `oldScattering b e X' = r(I - (1-w)uu*)`. -/
theorem oldScattering_twistOld (hη : 0 < (boundaryZ b e).im) (hX : X.IsHermitian)
    (hu : star u ⬝ᵥ u = 1) (hw : ‖w‖ < 1) :
    Critical.oldScattering b e (twistOld b e w u X) = Critical.oldScattering b e X * twist w u := by
  have ha := twoIEta_ne_zero hη
  have h := inv_boundaryZ_sub_twistOld hη hX hu hw
  change 1 - twoIEta (boundaryZ b e).im • (boundaryZ b e • 1 - twistOld b e w u X)⁻¹ = _
  rw [h, smul_smul, mul_inv_cancel₀ ha, one_smul, sub_sub_cancel]

/-- **The twisted old response is passive**: `-Im X' = (4η)⁻¹ Z'(I - r'r'*)Z'* ⪰ 0`. -/
theorem posSemidef_neg_imPart_twistOld (hη : 0 < (boundaryZ b e).im) (hX : X.IsHermitian)
    (hu : star u ⬝ᵥ u = 1) (hw : ‖w‖ < 1) :
    (-Critical.imPart (twistOld b e w u X)).PosSemidef := by
  set X' := twistOld b e w u X
  set η := (boundaryZ b e).im
  set r' := Critical.oldScattering b e X * twist w u
  set Z' := boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X'
  set Y' := -Critical.imPart X'
  have hu' := isUnit_det_one_sub_oldScattering_twist hη hX hu hw
  have ha := twoIEta_ne_zero hη
  have hZ'eq : Z' = twoIEta η • (1 - r')⁻¹ := boundaryZ_sub_twistOld
  have hZ' : IsUnit Z'.det := by
    rw [hZ'eq, det_smul, det_nonsing_inv]
    exact ((isUnit_iff_ne_zero.mpr ha).pow _).mul hu'.ringInverse
  have hZZ : Z' - Z'ᴴ = (2 * Complex.I) • ((η : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      + Y') := by
    rw [show Z' = boundaryZMat (((boundaryZ b e).re : ℂ) • 1 - rePart X') Y' η from
      (boundaryZMat_eq b e X').symm]
    exact boundaryZMat_sub_conjTranspose
      ((by simp [IsHermitian, conjTranspose_smul] :
        (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
        (rePart_isHermitian X')) (by simpa [Y'] using (imPart_isHermitian X').neg)
  have hdef := one_sub_scattering_mul_conjTranspose hZ' hZZ
  have hr' : 1 - twoIEta η • Z'⁻¹ = r' := oldScattering_twistOld hη hX hu hw
  rw [hr'] at hdef
  have hZi : Z' * Z'⁻¹ = 1 := mul_nonsing_inv _ hZ'
  have hZih : (Z'⁻¹)ᴴ * Z'ᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv _ hZ', conjTranspose_one]
  have hY'eq : Y' = (((4 * η)⁻¹ : ℝ) : ℂ) • (Z' * (1 - r' * r'ᴴ) * Z'ᴴ) := by
    rw [hdef, sub_sub_cancel, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have : Z' * (Z'⁻¹ * Y' * (Z'⁻¹)ᴴ) * Z'ᴴ = Y' := by
      calc Z' * (Z'⁻¹ * Y' * (Z'⁻¹)ᴴ) * Z'ᴴ = (Z' * Z'⁻¹) * Y' * ((Z'⁻¹)ᴴ * Z'ᴴ) := by
            simp only [Matrix.mul_assoc]
        _ = Y' := by rw [hZi, hZih, Matrix.one_mul, Matrix.mul_one]
    rw [this, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_smul]
  have hc : (1 - r' * r'ᴴ).PosSemidef :=
    posSemidef_one_sub_mul_twist (oldScattering_mul_conjTranspose b e hη hX) hw hu
  rw [hY'eq]
  exact (hc.mul_mul_conjTranspose_same Z').smul (by
    have : (0 : ℝ) ≤ (4 * η)⁻¹ := by positivity
    exact_mod_cast this)

/-- `g(r') = 1 - |w|²`. -/
theorem conductance_twistOld (hη : 0 < (boundaryZ b e).im) (hX : X.IsHermitian)
    (hu : star u ⬝ᵥ u = 1) (hw : ‖w‖ < 1) :
    Critical.conductance (Critical.oldScattering b e (twistOld b e w u X)) =
      1 - Complex.normSq w := by
  rw [oldScattering_twistOld hη hX hu hw]
  exact conductance_mul_twist (conjTranspose_oldScattering_mul b e hη hX) w hu

/-- `|W⁻¹Tr_j (vu*)| ≤ W⁻¹` for unit vectors. -/
theorem norm_blockTrace_vecMulVec_le (hW : 0 < W) {v : Fin 2 × Fin W → ℂ}
    (hv : star v ⬝ᵥ v = 1) (hu : star u ⬝ᵥ u = 1) (j : Fin 2) :
    ‖blockTrace (vecMulVec v (star u)) j‖ ≤ (W : ℝ)⁻¹ := by
  unfold blockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hv' : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← BlockBand.Wegner.re_star_dotProduct_self, hv, Complex.one_re]
  have hu' : ∑ i, ‖u i‖ ^ 2 = 1 := by
    rw [← BlockBand.Wegner.re_star_dotProduct_self, hu, Complex.one_re]
  have hle : ‖∑ a : Fin W, vecMulVec v (star u) (j, a) (j, a)‖ ≤ 1 := by
    calc ‖∑ a : Fin W, vecMulVec v (star u) (j, a) (j, a)‖
        ≤ ∑ a : Fin W, ‖vecMulVec v (star u) (j, a) (j, a)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 2 × Fin W, ‖v i‖ * ‖u i‖ := by
          rw [Fintype.sum_prod_type]
          refine le_trans ?_ (Finset.single_le_sum (f := fun k : Fin 2 =>
            ∑ a : Fin W, ‖v (k, a)‖ * ‖u (k, a)‖) (fun k _ => Finset.sum_nonneg fun a _ => by
              positivity) (Finset.mem_univ j))
          refine Finset.sum_le_sum fun a _ => ?_
          rw [vecMulVec_apply, norm_mul, Pi.star_apply, norm_star]
      _ ≤ ∑ i : Fin 2 × Fin W, (‖v i‖ ^ 2 + ‖u i‖ ^ 2) / 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          nlinarith [sq_nonneg (‖v i‖ - ‖u i‖)]
      _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hv', hu']; norm_num
  calc (W : ℝ)⁻¹ * ‖∑ a : Fin W, vecMulVec v (star u) (j, a) (j, a)‖ ≤ (W : ℝ)⁻¹ * 1 := by
        gcongr
    _ = (W : ℝ)⁻¹ := mul_one _

/-- **The scalar traces move by `O(1/W)`** (the two normalized block traces
change by at most `C/W`, uniformly in `ρ` and `θ`): `d(X') ≤ d(X) + 1/(ηW)`. -/
theorem matchedDistance_twistOld_le (hW : 0 < W) (hη : 0 < (boundaryZ b e).im)
    (hX : X.IsHermitian) (hu : star u ⬝ᵥ u = 1) (hw : ‖w‖ < 1) :
    matchedDistance b e (twistOld b e w u X) ≤
      matchedDistance b e X + ((boundaryZ b e).im)⁻¹ * (W : ℝ)⁻¹ := by
  set η := (boundaryZ b e).im
  set r := Critical.oldScattering b e X
  have ha := twoIEta_ne_zero hη
  have h' := inv_boundaryZ_sub_twistOld hη hX hu hw
  have h0 : (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ =
      (twoIEta η)⁻¹ • (1 - r) := by
    change _ = (twoIEta η)⁻¹ • (1 - (1 - twoIEta η • (boundaryZ b e • 1 - X)⁻¹))
    rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hdiff : (boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      twistOld b e w u X)⁻¹ = (boundaryZ b e • 1 - X)⁻¹ +
        ((twoIEta η)⁻¹ * (1 - w)) • vecMulVec (r *ᵥ u) (star u) := by
    rw [h', h0, twist, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, mul_vecMulVec]
    module
  have hrr : rᴴ * r = 1 := conjTranspose_oldScattering_mul b e hη hX
  have hru : star (r *ᵥ u) ⬝ᵥ (r *ᵥ u) = 1 := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hrr, one_mulVec, hu]
  have hcoef : ‖(twoIEta η)⁻¹ * (1 - w)‖ ≤ η⁻¹ := by
    rw [norm_mul, norm_inv]
    have h2 : ‖twoIEta η‖ = 2 * η := by
      simp only [twoIEta, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hη.le, Complex.norm_I, mul_one]
    rw [h2]
    have h3 : ‖1 - w‖ ≤ 2 := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    rw [inv_mul_le_iff₀ (by positivity)]
    calc ‖1 - w‖ ≤ 2 := h3
      _ = 2 * η * η⁻¹ := by field_simp
  have hbtr : ∀ j : Fin 2, blockTrace ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W)
      (Fin 2 × Fin W) ℂ) - twistOld b e w u X)⁻¹) j = blockTrace ((boundaryZ b e • 1 - X)⁻¹) j +
        ((twoIEta η)⁻¹ * (1 - w)) * blockTrace (vecMulVec (r *ᵥ u) (star u)) j := by
    intro j
    rw [hdiff]
    simp only [blockTrace, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  have hone : ∀ j : Fin 2, ‖blockTrace ((boundaryZ b e • (1 : Matrix (Fin 2 × Fin W)
      (Fin 2 × Fin W) ℂ) - twistOld b e w u X)⁻¹) j - matchedA e‖ ≤
        ‖blockTrace ((boundaryZ b e • 1 - X)⁻¹) j - matchedA e‖ + η⁻¹ * (W : ℝ)⁻¹ := by
    intro j
    rw [hbtr, add_sub_right_comm]
    refine (norm_add_le _ _).trans ?_
    gcongr
    rw [norm_mul]
    exact mul_le_mul hcoef (norm_blockTrace_vecMulVec_le hW hru hu j) (norm_nonneg _)
      (by positivity)
  unfold matchedDistance
  refine max_le ?_ ?_
  · exact (hone 0).trans (by gcongr; exact le_max_left _ _)
  · exact (hone 1).trans (by gcongr; exact le_max_right _ _)

end BlockBand.Critical.MatrixClosing.Boundary
