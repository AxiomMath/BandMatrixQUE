module

public import BlockBand.Transmission.Bridge.TransportFull
public import BlockBand.SourceProcess.Closing.Defs

/-!
# Perfect far transmission forces a singular modified pencil

`modPencil E u v p = (H_p - E) - u C_nC_nᴴ - v C_fC_fᴴ` closes the near lead with `u` and the far
lead with `v`. With `z = z_∂`:

* **`farReflection_ker`** (deterministic, `𝓜` invertible, `z ≠ 0`): if `S_ff v = 0` and
  `modPencil E z⁻¹ (z̄)⁻¹` is invertible, then `v = 0`. Indeed, for the far input `w = (0, v)`
  with solution `(x, y) = (𝒰w, ℝw)`, `S_ff v = 0` reads `v = 2iη y_f`; the port rows give
  `C_nᴴx = -z y_n` and `C_fᴴx = -z̄ y_f` (since `z - 2iη = z̄`), so `modPencil · x = (H-E)x + Cy = 0`.
  Hence `x = 0`, then `y_f = 0` and `v = 0`.
* The growth step of `modPencil` is `det_modPencil_succ`, and its a.s. invertibility at every
  length is `ae_isUnit_modPencil`.

This is used to show that, almost surely, no far transmission eigenvalue equals `1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing

variable {W : ℕ}

/-- Port column `i` of a two-port coupling. -/
def colOf {r : ℕ} (C : Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    Matrix (Fin r × Fin W) (Fin W) ℂ :=
  Matrix.of fun a y => C a (i, y)

/-- The lead load `u C_nC_nᴴ + v C_fC_fᴴ`. -/
def portLoad {r : ℕ} (u v : ℂ) (p : PathSample W r) : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  u • (colOf (pathPortCoupling p) 0 * (colOf (pathPortCoupling p) 0)ᴴ) +
    v • (colOf (pathPortCoupling p) 1 * (colOf (pathPortCoupling p) 1)ᴴ)

/-- The pencil with the near lead closed by `u` and the far lead by `v`. -/
def modPencil {r : ℕ} (E : ℝ) (u v : ℂ) (p : PathSample W r) :
    Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  (pathMatrix p - (E : ℂ) • 1) - portLoad u v p

theorem modPencil_apply {r : ℕ} (E : ℝ) (u v : ℂ) (p : PathSample W r) (x y : Fin r × Fin W) :
    modPencil E u v p x y = (pathMatrix p - (E : ℂ) • 1) x y - portLoad u v p x y := rfl

theorem coupling_mulVec_split {r : ℕ} (C : Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ)
    (y : Fin 2 × Fin W → ℂ) :
    C *ᵥ y = colOf C 0 *ᵥ (fun a => y (0, a)) + colOf C 1 *ᵥ (fun a => y (1, a)) := by
  funext x
  simp [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, colOf]

theorem colOf_conj_mulVec {r : ℕ} (C : Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2)
    (x : Fin r × Fin W → ℂ) : (colOf C i)ᴴ *ᵥ x = fun a => (Cᴴ *ᵥ x) (i, a) := by
  funext a
  simp [mulVec, dotProduct, colOf, conjTranspose_apply]

end BlockBand.SourceProcess.ClosedSum

namespace BlockBand.SourceProcess.ClosedSum

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing

variable {W : ℕ}

theorem portLoad_mulVec {r : ℕ} (u v : ℂ) (p : PathSample W r) (x : Fin r × Fin W → ℂ) :
    portLoad u v p *ᵥ x = u • (colOf (pathPortCoupling p) 0 *ᵥ ((colOf (pathPortCoupling p) 0)ᴴ *ᵥ x)) +
      v • (colOf (pathPortCoupling p) 1 *ᵥ ((colOf (pathPortCoupling p) 1)ᴴ *ᵥ x)) := by
  simp only [portLoad, add_mulVec, smul_mulVec, mulVec_mulVec]

/-- `z - 2iη = z̄`. -/
theorem boundaryZ_sub_two_eta (b E : ℝ) :
    boundaryZ b E - ((2 * etaZ b E : ℝ) : ℂ) * Complex.I = star (boundaryZ b E) := by
  apply Complex.ext <;> simp [etaZ]; ring

/-- **A far kernel vector of `S_ff` is zero** when the modified pencil (near lead closed by
`z⁻¹`, far lead by `z̄⁻¹`) is invertible. -/
theorem farReflection_ker (b E : ℝ) {n : ℕ} (ω : GrowthPath W)
    (hM : IsUnit (fullPathMatrix b E W n ω)) (hz : boundaryZ b E ≠ 0)
    (hG : IsUnit (modPencil E (boundaryZ b E)⁻¹ (star (boundaryZ b E))⁻¹ (pathAt W n ω)))
    {v : Fin W → ℂ} (hv : farReflection b E W n ω *ᵥ v = 0) : v = 0 := by
  obtain ⟨h1, h2⟩ := full_solution b E n ω hM
  set z := boundaryZ b E with hzdef
  set C := pathPortCoupling (pathAt W n ω)
  set w : Fin 2 × Fin W → ℂ := fun y => if y.1 = 1 then v y.2 else 0 with hw
  set x := boundaryToInterior b E W n ω *ᵥ w
  set y := boundaryResolvent b E W n ω *ᵥ w
  have e1 : (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) *ᵥ x + C *ᵥ y = 0 := by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, h1, zero_mulVec]
  have e2 : Cᴴ *ᵥ x + z • y = w := by
    rw [mulVec_mulVec, ← smul_mulVec, ← add_mulVec, h2, one_mulVec]
  have hzs : star z ≠ 0 := star_ne_zero.2 hz
  -- `S_ff v = 0` reads `v = 2iη y_far`.
  have hvy : ∀ a, v a = (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) * y (1, a) := by
    intro a
    have := congrFun hv a
    simp only [farReflection, portBlock, scatteringMatrix, mulVec, dotProduct, of_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply] at this
    have hy : y (1, a) = ∑ c, boundaryResolvent b E W n ω (1, a) (1, c) * v c := by
      simp only [y, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, hw]
      simp
    rw [hy, Finset.mul_sum]
    have h1a : ∑ c, (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (1, a) (1, c) * v c = v a := by
      simp [one_apply]
    rw [h1a, sub_eq_zero] at this
    rw [this]; exact Finset.sum_congr rfl fun c _ => by ring
  have hy0 : ∀ a, y (0, a) = -z⁻¹ * (Cᴴ *ᵥ x) (0, a) := by
    intro a
    have := congrFun e2 (0, a)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw] at this
    simp at this
    field_simp
    linear_combination this
  have hy1 : ∀ a, y (1, a) = -(star z)⁻¹ * (Cᴴ *ᵥ x) (1, a) := by
    intro a
    have := congrFun e2 (1, a)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw] at this
    simp only [Fin.isValue, ↓reduceIte] at this
    rw [hvy a] at this
    have hs := boundaryZ_sub_two_eta b E
    rw [← hzdef] at hs
    field_simp
    linear_combination this - y (1, a) * hs
  have hCy : C *ᵥ y = -(portLoad z⁻¹ (star z)⁻¹ (pathAt W n ω) *ᵥ x) := by
    rw [coupling_mulVec_split, portLoad_mulVec, colOf_conj_mulVec, colOf_conj_mulVec]
    have e0 : (fun a => y (0, a)) = -z⁻¹ • fun a => (Cᴴ *ᵥ x) (0, a) := funext fun a => by
      rw [hy0]; simp
    have e1' : (fun a => y (1, a)) = -(star z)⁻¹ • fun a => (Cᴴ *ᵥ x) (1, a) := funext fun a => by
      rw [hy1]; simp
    rw [e0, e1', mulVec_smul, mulVec_smul, neg_add, neg_smul, neg_smul]
  have hx : x = 0 := by
    refine eq_zero_of_mulVec_eq_zero ((isUnit_iff_isUnit_det _).1 hG).ne_zero ?_
    rw [modPencil, sub_mulVec, sub_eq_add_neg, ← hCy]
    exact e1
  funext a
  rw [hvy a, hy1 a, hx, mulVec_zero]
  simp

end BlockBand.SourceProcess.ClosedSum
