module

public import BlockBand.DeterminantScore.BrascampLiebPiece
public import BlockBand.DeterminantScore.BrascampLiebLimit

/-!
# Convex exhaustion of an open convex set

A step towards `BrascampLiebStatement` in the indexed spectral convexity lemma.

`layer`, `isCompact_layer`, `convex_layer`, `layer_mono`, `exists_mem_interior_layer`: an open
convex `D ⊆ ℝ^m` is the increasing union of open convex
sets `P_n = int S_n` with `S_n = {x : ‖x‖ ≤ n, dist(x, Dᶜ) ≥ 1/(n+1)}` compact, `S_n ⊆ D`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb

open MeasureTheory Metric

variable {m : ℕ}

/-- The compact layers of the exhaustion. -/
def layer (D : Set (Fin m → ℝ)) (n : ℕ) : Set (Fin m → ℝ) :=
  closedBall 0 n ∩ ⋂ y ∈ Dᶜ, (ball y (1 / ((n : ℝ) + 1)))ᶜ

theorem mem_layer {D : Set (Fin m → ℝ)} {n : ℕ} {x : Fin m → ℝ} :
    x ∈ layer D n ↔ ‖x‖ ≤ n ∧ ∀ y, dist x y < 1 / ((n : ℝ) + 1) → y ∈ D := by
  simp only [layer, Set.mem_inter_iff, mem_closedBall, dist_zero_right, Set.mem_iInter,
    Set.mem_compl_iff, mem_ball]
  refine and_congr Iff.rfl ⟨fun h y hy => ?_, fun h y hy hxy => hy (h y hxy)⟩
  by_contra hyD
  exact h y hyD hy

theorem isCompact_layer (D : Set (Fin m → ℝ)) (n : ℕ) : IsCompact (layer D n) :=
  isCompact_of_isClosed_isBounded
    (isClosed_closedBall.inter (isClosed_biInter fun _ _ => isOpen_ball.isClosed_compl))
    (isBounded_closedBall.subset Set.inter_subset_left)

theorem layer_subset (D : Set (Fin m → ℝ)) (n : ℕ) : layer D n ⊆ D := fun x hx =>
  (mem_layer.1 hx).2 x (by rw [dist_self]; positivity)

theorem convex_layer {D : Set (Fin m → ℝ)} (hD : Convex ℝ D) (n : ℕ) :
    Convex ℝ (layer D n) := by
  intro x hx x' hx' a b ha hb hab
  rw [mem_layer] at hx hx' ⊢
  refine ⟨?_, fun y hy => ?_⟩
  · have := convex_closedBall (0 : Fin m → ℝ) n
      (show x ∈ closedBall 0 (n : ℝ) by simpa using hx.1)
      (show x' ∈ closedBall 0 (n : ℝ) by simpa using hx'.1) ha hb hab
    simpa using this
  · set v := y - (a • x + b • x')
    have hv : ‖v‖ < 1 / ((n : ℝ) + 1) := by rwa [dist_comm, dist_eq_norm] at hy
    have h1 : x + v ∈ D := hx.2 _ (by rw [dist_eq_norm]; simpa using hv)
    have h2 : x' + v ∈ D := hx'.2 _ (by rw [dist_eq_norm]; simpa using hv)
    have := hD h1 h2 ha hb hab
    have e : a • (x + v) + b • (x' + v) = y := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
      simp [v]
    rwa [e] at this

theorem layer_mono (D : Set (Fin m → ℝ)) : Monotone (layer D) := by
  refine monotone_nat_of_le_succ fun n x hx => ?_
  rw [mem_layer] at hx ⊢
  refine ⟨hx.1.trans (by push_cast; linarith), fun y hy => hx.2 y (hy.trans_le ?_)⟩
  push_cast
  gcongr
  linarith

theorem exists_mem_interior_layer {D : Set (Fin m → ℝ)} (hDo : IsOpen D) {x : Fin m → ℝ}
    (hx : x ∈ D) : ∃ n, x ∈ interior (layer D n) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hDo x hx
  obtain ⟨n, hn⟩ := exists_nat_gt (max (‖x‖ + 1) (2 / ε))
  have hn1 : ‖x‖ + 1 < n := (le_max_left _ _).trans_lt hn
  have hn2 : 2 / ε < n := (le_max_right _ _).trans_lt hn
  have hr : 1 / ((n : ℝ) + 1) ≤ ε / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    rw [div_lt_iff₀ hε] at hn2
    nlinarith
  refine ⟨n, mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset
    (ball_mem_nhds x (lt_min (half_pos hε) one_pos : 0 < min (ε / 2) 1)) fun z hz => ?_)⟩
  · have hz' : dist z x < min (ε / 2) 1 := hz
    rw [mem_layer]
    refine ⟨?_, fun y hy => hball ?_⟩
    · have : ‖z‖ ≤ ‖x‖ + dist z x := by
        rw [dist_eq_norm]
        calc ‖z‖ = ‖x + (z - x)‖ := by abel_nf
          _ ≤ _ := norm_add_le _ _
      have := min_le_right (ε / 2) 1
      linarith
    · rw [mem_ball]
      have := dist_triangle y z x
      rw [dist_comm y z] at this
      have := min_le_left (ε / 2) 1
      linarith

end BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb
