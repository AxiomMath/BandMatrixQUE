module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneUniformStability
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compact bootstrap for CEH mixed stability

This module carries out the fixed-dimension compact part of the bootstrap toward
the CEH `θ = 1` lemma.  On a closed inner regular window, ordinary boundary
stability implies a uniform lower bound for the *mixed* boundary denominator at
sufficiently close pairs of energies.  The proof uses the exact normalized trace,
entrywise boundary continuity, and Heine–Cantor compactness.

The conclusion is fixed in `N`.  It supplies no dimension-uniform modulus and no
uniform-in-`N` boundary convergence rate.  Thus it does not prove
`UniformBoundaryToStripResidual`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped BigOperators Topology

/-- The exact normalized mixed trace, expanded entrywise so that its boundary
continuity follows directly from the entrywise derivative contract. -/
def boundaryMixedTrace {N : ℕ} (Mb : ℝ → LocalETHMatrix N) (x y : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, Mb x i j * Mb y j i

/-- The mixed stability denominator on the boundary. -/
def boundaryMixedStabilityValue {N : ℕ} (s : ℝ)
    (Mb : ℝ → LocalETHMatrix N) (x y : ℝ) : ℝ :=
  ‖1 - (s : ℂ) * boundaryMixedTrace Mb x y‖

/-- The entrywise mixed trace is exactly the project normalized trace of the
matrix product; in particular, no normalization is lost in the compactness
argument. -/
theorem boundaryMixedTrace_eq_normalizedTrace_mul {N : ℕ}
    (Mb : ℝ → LocalETHMatrix N) (x y : ℝ) :
    boundaryMixedTrace Mb x y =
      Conventions.normalizedTrace (Mb x * Mb y) := by
  simp [boundaryMixedTrace, Conventions.normalizedTrace, Matrix.trace,
    Matrix.mul_apply]

/-- The mixed boundary denominator is continuous on the square of a compact
inner regular window. -/
theorem continuousOn_boundaryMixedStabilityValue
    {N : ℕ} {E₀ r a b s : ℝ} {Mb Mb' : ℝ → LocalETHMatrix N}
    (hderiv : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' x) x)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      boundaryMixedStabilityValue s Mb p.1 p.2) (Icc a b ×ˢ Icc a b) := by
  let S : Set (ℝ × ℝ) := Icc a b ×ˢ Icc a b
  have hprod : ∀ i j : Fin N,
      ContinuousOn (fun p : ℝ × ℝ => Mb p.1 i j * Mb p.2 j i) S := by
    intro i j p hp
    exact (((continuousAt_boundaryWitness_entry_of_regularWindow hderiv
      (hinner hp.1) i j).comp continuousAt_fst).continuousWithinAt).mul
      (((continuousAt_boundaryWitness_entry_of_regularWindow hderiv
        (hinner hp.2) j i).comp continuousAt_snd).continuousWithinAt)
  have hj : ∀ i : Fin N,
      ContinuousOn (fun p : ℝ × ℝ => ∑ j : Fin N,
        Mb p.1 i j * Mb p.2 j i) S := by
    intro i
    simpa using
      (continuousOn_finsetSum Finset.univ (fun j _ => hprod i j))
  have hi : ContinuousOn (fun p : ℝ × ℝ => ∑ i : Fin N, ∑ j : Fin N,
      Mb p.1 i j * Mb p.2 j i) S := by
    simpa using
      (continuousOn_finsetSum Finset.univ (fun i _ => hj i))
  unfold boundaryMixedStabilityValue boundaryMixedTrace
  exact (continuousOn_const.sub
    (continuousOn_const.mul (continuousOn_const.mul hi))).norm

/-- On the diagonal the mixed denominator is exactly the ordinary stability
value from the regular-boundary contract. -/
theorem boundaryMixedStabilityValue_diag {N : ℕ} (s : ℝ)
    (Mb : ℝ → LocalETHMatrix N) (x : ℝ) :
    boundaryMixedStabilityValue s Mb x x = matrixStabilityValue s (Mb x) := by
  simp [boundaryMixedStabilityValue, matrixStabilityValue,
    boundaryMixedTrace_eq_normalizedTrace_mul]

/-- Fixed-dimension compact bootstrap: a strictly reduced ordinary boundary
stability margin holds uniformly for mixed denominators at all sufficiently
nearby pairs in the compact inner window.  The resulting radius may depend on
`N`, the boundary branch, and the window. -/
theorem exists_uniform_boundaryMixedStability_radius
    {N : ℕ} {s E₀ r c K a b c₀ : ℝ}
    {Mf : ℂ → LocalETHMatrix N}
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∃ Mb Mb' : ℝ → LocalETHMatrix N, ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds (Mb x))) ∧
      (∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        HasLocalETHMatrixDerivAt Mb (Mb' x) x) ∧
      (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist x y < δ →
        c₀ ≤ boundaryMixedStabilityValue s Mb x y) := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  have hcont := continuousOn_boundaryMixedStabilityValue
    (Mb := Mb) (Mb' := Mb') (s := s)
    (fun x hx => (hdata x hx).2.1) hinner
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  have heps : 0 < c - c₀ := sub_pos.mpr hc₀
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc (c - c₀) heps
  refine ⟨Mb, Mb', δ, hδ, (fun x hx => (hdata x hx).1),
    (fun x hx => (hdata x hx).2.1), ?_⟩
  intro x hx y hy hxy
  have hp : (x, y) ∈ Icc a b ×ˢ Icc a b := ⟨hx, hy⟩
  have hq : (x, x) ∈ Icc a b ×ˢ Icc a b := ⟨hx, hx⟩
  have hdist : dist (x, y) (x, x) < δ := by
    simpa [Prod.dist_eq, dist_comm] using hxy
  have hclose := hmod (x, y) hp (x, x) hq hdist
  have hdiag : c ≤ boundaryMixedStabilityValue s Mb x x := by
    rw [boundaryMixedStabilityValue_diag]
    exact (hdata x (hinner hx)).2.2.2.2.2
  rw [Real.dist_eq] at hclose
  have hlower := neg_lt_of_abs_lt hclose
  linarith

end CEHNative.BlockBand.CEH
