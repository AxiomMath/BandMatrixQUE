module
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Padding a rectangular factor to a square one

The reduction of `σ : ℝ^d → ℝ^{d×m}` to the square case in dimension `D = d + m` by the state
padding `y ↦ (y, 0)`.

* `padV y = (y, 0)`, `prj z = (z_i)_{i < d}`, `padB b z = (b (prj z), 0)`,
  `padM A = [[0, A], [0, 0]]` (a `D × D` matrix), `padS σ z = padM (σ (prj z))`.
* `padM_cov_*`: `padM A (padM A)ᵀ = diag(A Aᵀ, 0)`.
* `padW W = {z | prj z ∈ W, |z_{d+k}| < 1 ∀ k}`, `preimage_padV_padW : padV⁻¹' (padW W) = W`;
  `isInteriorDomain_padW` and `isInteriorDomain_slice` (interior domains correspond).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory Filter Topology Set

variable {d m : ℕ}

/-- The padded state `(y, 0)`. -/
def padV (y : Fin d → ℝ) : Fin (d + m) → ℝ := Fin.addCases y fun _ => 0

/-- The projection to the first `d` coordinates. -/
def prj (z : Fin (d + m) → ℝ) : Fin d → ℝ := fun i => z (Fin.castAdd m i)

/-- The padded drift. -/
def padB (b : (Fin d → ℝ) → Fin d → ℝ) (z : Fin (d + m) → ℝ) : Fin (d + m) → ℝ :=
  padV (b (prj z))

/-- The square padding `[[0, A], [0, 0]]` of a `d × m` matrix. -/
def padM (A : Matrix (Fin d) (Fin m) ℝ) : Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
  Matrix.of fun i j => Fin.addCases (fun i' => Fin.addCases (fun _ => 0) (fun k => A i' k) j)
    (fun _ => 0) i

/-- The padded factor. -/
def padS (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ) (z : Fin (d + m) → ℝ) :
    Matrix (Fin (d + m)) (Fin (d + m)) ℝ :=
  padM (σ (prj z))

@[simp] theorem padV_left (y : Fin d → ℝ) (i : Fin d) : padV (m := m) y (Fin.castAdd m i) = y i := by
  simp [padV]

@[simp] theorem padV_right (y : Fin d → ℝ) (k : Fin m) : padV (m := m) y (Fin.natAdd d k) = 0 := by
  simp [padV]

@[simp] theorem prj_padV (y : Fin d → ℝ) : prj (padV (m := m) y) = y := funext fun i => by simp [prj]

theorem padM_cov_left (A : Matrix (Fin d) (Fin m) ℝ) (i j : Fin d) :
    (padM A * (padM A).transpose) (Fin.castAdd m i) (Fin.castAdd m j) = (A * A.transpose) i j := by
  simp [padM, Matrix.mul_apply, Fin.sum_univ_add]

theorem padM_cov_right (A : Matrix (Fin d) (Fin m) ℝ) (k : Fin m) (j : Fin (d + m)) :
    (padM A * (padM A).transpose) (Fin.natAdd d k) j = 0 := by
  simp [padM, Matrix.mul_apply]

theorem padM_cov_right' (A : Matrix (Fin d) (Fin m) ℝ) (i : Fin (d + m)) (k : Fin m) :
    (padM A * (padM A).transpose) i (Fin.natAdd d k) = 0 := by
  simp [padM, Matrix.mul_apply]

theorem continuous_padV : Continuous (padV (d := d) (m := m)) :=
  continuous_pi fun i => by
    refine Fin.addCases (fun i => ?_) (fun k => ?_) i
    · simp only [padV_left]; exact continuous_apply i
    · simp only [padV_right]; exact continuous_const

theorem continuous_prj : Continuous (prj (d := d) (m := m)) :=
  continuous_pi fun _ => continuous_apply _

theorem norm_prj_le (z : Fin (d + m) → ℝ) : ‖prj z‖ ≤ ‖z‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_le_pi_norm z _

/-- The padded domain. -/
def padW (W : Set (Fin d → ℝ)) : Set (Fin (d + m) → ℝ) :=
  prj ⁻¹' W ∩ {z | ∀ k : Fin m, |z (Fin.natAdd d k)| < 1}

theorem preimage_padV_padW (W : Set (Fin d → ℝ)) : padV ⁻¹' (padW (m := m) W) = W := by
  ext y
  simp [padW]

theorem isInteriorDomain_padW {W U : Set (Fin d → ℝ)} (hWU : IsInteriorDomain W U) :
    IsInteriorDomain (padW (m := m) W) (prj ⁻¹' U) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (hWU.1.preimage continuous_prj).inter ?_
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt ((continuous_apply _).abs) continuous_const
  · obtain ⟨R, hR⟩ := hWU.2.1.isBounded.subset_closedBall 0
    refine Bornology.IsBounded.isCompact_closure (Metric.isBounded_iff_subset_closedBall 0 |>.2
      ⟨max R 1, fun z hz => ?_⟩)
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine Fin.addCases (fun i => ?_) (fun k => ?_) i
    · have h1 := hR (subset_closure hz.1)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact ((norm_le_pi_norm (prj z) i).trans h1).trans (le_max_left _ _)
    · rw [Real.norm_eq_abs]; exact (hz.2 k).le.trans (le_max_right _ _)
  · have hc : IsClosed (prj (m := m) ⁻¹' closure W) := isClosed_closure.preimage continuous_prj
    have hs : padW (m := m) W ⊆ prj ⁻¹' closure W := fun z hz => subset_closure hz.1
    exact (closure_minimal hs hc).trans (preimage_mono hWU.2.2)

theorem isInteriorDomain_slice {W : Set (Fin d → ℝ)} {W'' : Set (Fin (d + m) → ℝ)}
    (h : IsInteriorDomain W'' (padW (m := m) W)) : IsInteriorDomain (padV ⁻¹' W'') W := by
  have hsub : closure (padV ⁻¹' W'') ⊆ padV ⁻¹' closure W'' :=
    closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage continuous_padV)
  refine ⟨h.1.preimage continuous_padV, ?_, ?_⟩
  · refine (h.2.1.image continuous_prj).of_isClosed_subset isClosed_closure
      (hsub.trans fun y hy => ⟨padV y, hy, prj_padV y⟩)
  · refine hsub.trans ?_
    rw [← preimage_padV_padW (m := m) W]
    exact preimage_mono h.2.2

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
