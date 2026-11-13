module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneMatrixCompactStrip
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Finite compact-strip topology for the CEH boundary branch

This module completes the purely topological last step once the locally lifted
matrix germs have been glued: entrywise continuity on one fixed closed strip
implies uniform convergence to the bottom edge in `matrixEntryDistance`.
The proof uses the compact product, Heine–Cantor, and the exact finite entry
sum; it introduces no norm equivalence or dimension-independent constant.

The preceding module proves all local agreements.  Constructing the single
piecewise strip map and verifying its `ContinuousOn` predicate from those local
agreements remains syntactic gluing work; no such predicate is postulated as a
CEH input and this module does not mark theta-one.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped BigOperators Topology

/-- Entry-sum displacement from the bottom edge of a closed strip. -/
def stripBottomDistance {N : ℕ} (G : ℝ × ℝ → LocalETHMatrix N)
    (p : ℝ × ℝ) : ℝ :=
  matrixEntryDistance (G p) (G (p.1, 0))

/-- If every entry of a matrix field is continuous on a closed strip, its
entry-sum displacement from the bottom edge is continuous there. -/
theorem continuousOn_stripBottomDistance
    {N : ℕ} {a b ηstar : ℝ} (hηstar : 0 ≤ ηstar)
    (G : ℝ × ℝ → LocalETHMatrix N)
    (hG : ∀ i j : Fin N,
      ContinuousOn (fun p => G p i j) (Icc a b ×ˢ Icc 0 ηstar)) :
    ContinuousOn (stripBottomDistance G) (Icc a b ×ˢ Icc 0 ηstar) := by
  let S : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 ηstar
  have hproj : Continuous (fun p : ℝ × ℝ => (p.1, (0 : ℝ))) := by fun_prop
  have hmaps : MapsTo (fun p : ℝ × ℝ => (p.1, (0 : ℝ))) S S := by
    intro p hp
    exact ⟨hp.1, ⟨le_rfl, hηstar⟩⟩
  have hentry : ∀ i j : Fin N, ContinuousOn (fun p =>
      dist (G p i j) (G (p.1, 0) i j)) S := by
    intro i j p hp
    change ContinuousWithinAt (fun p =>
      dist (G p i j) (G (p.1, 0) i j))
      (Icc a b ×ˢ Icc 0 ηstar) p
    simpa [dist_eq_norm] using ((hG i j p hp).sub
      (((hG i j).comp hproj.continuousOn hmaps) p hp)).norm
  unfold stripBottomDistance matrixEntryDistance
  change ContinuousOn (fun p => ∑ i : Fin N, ∑ j : Fin N,
    dist (G p i j) (G (p.1, 0) i j)) S
  have hj : ∀ i : Fin N, ContinuousOn (fun p => ∑ j : Fin N,
      dist (G p i j) (G (p.1, 0) i j)) S := by
    intro i
    simpa using continuousOn_finsetSum Finset.univ (fun j _ => hentry i j)
  simpa using continuousOn_finsetSum Finset.univ (fun i _ => hj i)

/-- Pure compact-strip theorem: a continuous finite matrix field converges to
its bottom edge uniformly in energy.  The cutoff may depend on `N`, the field,
and the strip. -/
theorem exists_uniform_bottom_cutoff_of_continuousOn
    {N : ℕ} {a b ηstar ε : ℝ} (hηstar : 0 < ηstar) (hε : 0 < ε)
    (G : ℝ × ℝ → LocalETHMatrix N)
    (hG : ∀ i j : Fin N,
      ContinuousOn (fun p => G p i j) (Icc a b ×ˢ Icc 0 ηstar)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ ηstar ∧
      ∀ x ∈ Icc a b, ∀ η : ℝ, 0 < η → η < η₀ →
        matrixEntryDistance (G (x, η)) (G (x, 0)) < ε := by
  let S : Set (ℝ × ℝ) := Icc a b ×ˢ Icc 0 ηstar
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcont := continuousOn_stripBottomDistance hηstar.le G hG
  have huc := hcompact.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc ε hε
  let η₀ := min δ ηstar
  have hη₀ : 0 < η₀ := lt_min hδ hηstar
  refine ⟨η₀, hη₀, min_le_right _ _, ?_⟩
  intro x hx η hη hηlt
  have hηstrip : η ≤ ηstar :=
    (le_of_lt hηlt).trans (min_le_right _ _)
  have hp : (x, η) ∈ S := ⟨hx, hη.le, hηstrip⟩
  have hq : (x, 0) ∈ S := ⟨hx, le_rfl, hηstar.le⟩
  have hpq : dist (x, η) (x, 0) < δ := by
    have : η < δ := hηlt.trans_le (min_le_left _ _)
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos hη, hδ] using
      (And.intro hδ this)
  have hd := hmod (x, η) hp (x, 0) hq hpq
  have hzero : stripBottomDistance G (x, 0) = 0 := by
    simp [stripBottomDistance]
  have hnonneg : 0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      dist (G (x, η) i j) (G (x, 0) i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  simpa [stripBottomDistance, matrixEntryDistance,
    abs_of_nonneg hnonneg] using hd

/-- Comparator-facing form of the compact theorem.  A concrete glued strip map
with the branch above and boundary witness below immediately
discharges the fixed-`N` residual.  This is a generic consequence, not a new
analytic assumption or input structure. -/
theorem uniformBoundaryToStripResidual_of_gluedStrip
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    {a b ηstar : ℝ} (hηstar : 0 < ηstar)
    (G : ℝ × ℝ → LocalETHMatrix N)
    (hG : ∀ i j : Fin N,
      ContinuousOn (fun p => G p i j) (Icc a b ×ˢ Icc 0 ηstar))
    (hbottom : ∀ x ∈ Icc a b, G (x, 0) = Mb x)
    (hupper : ∀ x ∈ Icc a b, ∀ η, 0 < η → η ≤ ηstar →
      G (x, η) = Mf ((x : ℂ) + (η : ℂ) * Complex.I)) :
    UniformBoundaryToStripResidual Mf Mb a b := by
  intro ε hε
  obtain ⟨η₀, hη₀, hη₀strip, hcut⟩ :=
    exists_uniform_bottom_cutoff_of_continuousOn hηstar hε G hG
  refine ⟨η₀, hη₀, ?_⟩
  intro x hx η hη hηlt
  rw [← hupper x hx η hη ((le_of_lt hηlt).trans hη₀strip),
    ← hbottom x hx]
  exact hcut x hx η hη hηlt

end CEHNative.BlockBand.CEH
