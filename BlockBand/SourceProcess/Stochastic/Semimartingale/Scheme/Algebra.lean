module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Taylor
public import Mathlib.Analysis.Normed.Lp.PiLp
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Coordinate algebra for the Taylor scheme

Deterministic, on `ℝ^d = Fin d → ℝ` (sup norm). Linear and bilinear maps are expanded in the
coordinate basis `e_i = Pi.single i 1`, and the second-order Taylor step
`φ(z) - φ(y)` is split along a decomposition `z - y = a + c` (martingale part `a`,
drift part `c`) with an arbitrary matrix `J` subtracted from the quadratic martingale part.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open Finset

variable {d : ℕ}

/-- Coordinate vector `e_i`. -/
abbrev ev (i : Fin d) : Fin d → ℝ := Pi.single i 1

theorem eq_sum_ev (h : Fin d → ℝ) : h = ∑ i, h i • ev i := by
  funext j
  simp [ev, Finset.sum_apply, Pi.single_apply]

theorem clm_apply_eq_sum (L : (Fin d → ℝ) →L[ℝ] ℝ) (h : Fin d → ℝ) :
    L h = ∑ i, h i * L (ev i) := by
  calc L h = L (∑ i, h i • ev i) := by rw [← eq_sum_ev h]
    _ = ∑ i, h i * L (ev i) := by rw [map_sum]; simp [smul_eq_mul]

theorem clm_bilin_apply_eq_sum (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (h : Fin d → ℝ) :
    B h = ∑ i, h i • B (ev i) := by
  calc B h = B (∑ i, h i • ev i) := by rw [← eq_sum_ev h]
    _ = ∑ i, h i • B (ev i) := by rw [map_sum]; simp

theorem bilin_apply_eq_sum (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (h k : Fin d → ℝ) :
    B h k = ∑ i, ∑ j, h i * k j * B (ev i) (ev j) := by
  rw [clm_bilin_apply_eq_sum B h]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [clm_apply_eq_sum (B (ev i)) k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem norm_sq_le_sum_sq (h : Fin d → ℝ) : ‖h‖ ^ 2 ≤ ∑ i, h i ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Subsingleton.elim h 0]
  obtain ⟨i, hi⟩ : ∃ i, ‖h‖ = ‖h i‖ := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖h i‖) Finset.univ_nonempty
    refine ⟨i, le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j
      (Finset.mem_univ _)) (norm_le_pi_norm h i)⟩
  rw [hi, Real.norm_eq_abs, sq_abs]
  exact Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- **Taylor step split.** For `z - y = a + c` and any matrix `J`,
`φ z - φ y = Σ D_iφ a_i + Σ D_iφ c_i + ½ ΣΣ D_ijφ (a_i a_j - J_ij) + ½ ΣΣ D_ijφ J_ij
  + ½ ΣΣ D_ijφ (a_i c_j + c_i a_j + c_i c_j) + R(y, z)`. -/
theorem taylor_split (φ : (Fin d → ℝ) → ℝ) (y z a c : Fin d → ℝ) (hz : z - y = a + c)
    (J : Fin d → Fin d → ℝ) :
    φ z - φ y = ∑ i, fderiv ℝ φ y (ev i) * a i + ∑ i, fderiv ℝ φ y (ev i) * c i +
      (1 / 2) * ∑ i, ∑ j, fderiv ℝ (fderiv ℝ φ) y (ev i) (ev j) * (a i * a j - J i j) +
      (1 / 2) * ∑ i, ∑ j, fderiv ℝ (fderiv ℝ φ) y (ev i) (ev j) * J i j +
      (1 / 2) * ∑ i, ∑ j, fderiv ℝ (fderiv ℝ φ) y (ev i) (ev j) *
        (a i * c j + c i * a j + c i * c j) +
      taylorRem φ y z := by
  have hL : fderiv ℝ φ y (z - y) =
      ∑ i, fderiv ℝ φ y (ev i) * a i + ∑ i, fderiv ℝ φ y (ev i) * c i := by
    rw [clm_apply_eq_sum, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]; ring
  have hB : fderiv ℝ (fderiv ℝ φ) y (z - y) (z - y) =
      ∑ i, ∑ j, fderiv ℝ (fderiv ℝ φ) y (ev i) (ev j) * (a i * a j - J i j) +
      ∑ i, ∑ j, fderiv ℝ (fderiv ℝ φ) y (ev i) (ev j) * J i j +
      ∑ i, ∑ j, fderiv ℝ (fderiv ℝ φ) y (ev i) (ev j) * (a i * c j + c i * a j + c i * c j) := by
    rw [bilin_apply_eq_sum, hz, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply]; ring
  unfold taylorRem
  rw [hL, hB]
  ring

end BlockBand.SourceProcess.Stochastic.Semimartingale
