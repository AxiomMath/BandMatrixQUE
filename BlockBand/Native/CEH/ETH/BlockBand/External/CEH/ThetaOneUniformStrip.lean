module

public import BlockBand.Native.CEH.BlockBand.External.CEH.TypicalSpacingLocalETHAssembly
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.RegularBoundaryPositiveHeight
public import Mathlib.Topology.MetricSpace.Cover
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compactness dependencies for the CEH theta-one strip

After typical-spacing existence, the next step is the CEH boundary-to-strip
and theta-one adapter. Its analytic core is a uniform
passage from the boundary value to positive heights on a compact energy
window. This file proves the unconditional compactness part of that passage:

* the boundary witness in `LocalETHRegularBoundaryWindow` is continuous;
* on every closed inner window it is uniformly continuous;
* every inner window has a finite internal energy net;
* pointwise positive-height convergence has a common cutoff on each such
  finite net.

Closeness of matrices is recorded by the finite sum of entrywise distances,
which induces the ordinary finite-dimensional matrix topology and avoids
choosing an auxiliary matrix norm. These results use the boundary
witness and the unconditional MDE branch. They do not assume the strip estimate.

The extension from the finite net to the continuum needs, in addition, a
height-uniform MDE energy modulus down to height zero. The general resolvent
modulus degenerates as the height vanishes, so it does not give that step.
Consequently this module does not prove `UniformBoundaryToStripResidual`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped BigOperators Topology

/-- A concrete metric-compatible gauge for convergence of finite matrices:
the sum of the distances of all entries. -/
def matrixEntryDistance {N : ℕ} (A B : LocalETHMatrix N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, dist (A i j) (B i j)

@[simp] theorem matrixEntryDistance_self {N : ℕ} (A : LocalETHMatrix N) :
    matrixEntryDistance A A = 0 := by
  simp [matrixEntryDistance]

/-- Entry-sum distance to a fixed matrix is continuous in the product matrix
topology. -/
theorem continuous_matrixEntryDistance_right {N : ℕ} (B : LocalETHMatrix N) :
    Continuous (fun A : LocalETHMatrix N => matrixEntryDistance A B) := by
  unfold matrixEntryDistance
  fun_prop

/-- The derivative field makes every boundary-matrix entry continuous at
every point of the regular open window. -/
theorem continuousAt_boundaryWitness_entry_of_regularWindow
    {N : ℕ} {E₀ r : ℝ} {Mb Mb' : ℝ → LocalETHMatrix N}
    (hderiv : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' x) x)
    {x : ℝ} (hx : x ∈ Ioo (E₀ - r) (E₀ + r))
    (i j : Fin N) :
    ContinuousAt (fun y => Mb y i j) x :=
  (hderiv x hx i j).continuousAt

/-- Every boundary-matrix entry is continuous on a closed inner interval. -/
theorem continuousOn_boundaryWitness_entry_on_innerWindow
    {N : ℕ} {E₀ r a b : ℝ} {Mb Mb' : ℝ → LocalETHMatrix N}
    (hderiv : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' x) x)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r))
    (i j : Fin N) :
    ContinuousOn (fun x => Mb x i j) (Icc a b) := by
  intro x hx
  exact (continuousAt_boundaryWitness_entry_of_regularWindow
    hderiv (hinner hx) i j).continuousWithinAt

/-- Heine–Cantor supplies a uniform modulus, simultaneously over the energy
variable, for each of the finitely many boundary-matrix entries. -/
theorem uniformContinuousOn_boundaryWitness_entries_on_innerWindow
    {N : ℕ} {E₀ r a b : ℝ} {Mb Mb' : ℝ → LocalETHMatrix N}
    (hderiv : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' x) x)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r)) :
    ∀ i j : Fin N,
      UniformContinuousOn (fun x => Mb x i j) (Icc a b) := by
  intro i j
  exact isCompact_Icc.uniformContinuousOn_of_continuous
    (continuousOn_boundaryWitness_entry_on_innerWindow
      hderiv hinner i j)

/-- Pointwise boundary convergence becomes simultaneous on a fixed finite
energy grid, measured in the entry-sum gauge. -/
theorem eventually_branch_close_boundary_on_finset
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    (grid : Finset ℝ)
    (hboundary : ∀ x ∈ grid,
      Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ x ∈ grid,
        matrixEntryDistance
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε := by
  classical
  induction grid using Finset.induction_on with
  | empty => simp
  | @insert x grid hx ih =>
      have hxlim :
          Tendsto
            (fun η : ℝ => matrixEntryDistance
              (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x))
            (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        change Tendsto
          ((fun A : LocalETHMatrix N => matrixEntryDistance A (Mb x)) ∘
            fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
          (nhdsWithin 0 (Ioi 0)) (nhds 0)
        have hcomp :=
          (continuous_matrixEntryDistance_right (Mb x)).continuousAt.tendsto.comp
            (hboundary x (by simp))
        rw [matrixEntryDistance_self] at hcomp
        exact hcomp
      have hxevent : ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
          matrixEntryDistance
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε :=
        hxlim.eventually (eventually_lt_nhds hε)
      have hboundary' : ∀ y ∈ grid,
          Tendsto (fun η : ℝ => Mf ((y : ℂ) + (η : ℂ) * Complex.I))
            (nhdsWithin 0 (Ioi 0)) (nhds (Mb y)) := by
        intro y hy
        exact hboundary y (by simp [hy])
      have hievent := ih hboundary'
      filter_upwards [hxevent, hievent] with η hxη hiη
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxη
      · exact hiη y hy

/-- Explicit common positive-height cutoff for a fixed finite energy grid. -/
theorem exists_heightCutoff_branch_close_boundary_on_finset
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    (grid : Finset ℝ)
    (hboundary : ∀ x ∈ grid,
      Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ x ∈ grid, ∀ η : ℝ, 0 < η → η < η₀ →
        matrixEntryDistance
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε := by
  have hevent :=
    eventually_branch_close_boundary_on_finset grid hboundary hε
  have hfull :
      ∀ᶠ η : ℝ in nhds 0, η ∈ Ioi (0 : ℝ) →
        ∀ x ∈ grid,
          matrixEntryDistance
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨η₀, hη₀, hcut⟩ := Metric.eventually_nhds_iff.mp hfull
  refine ⟨η₀, hη₀, ?_⟩
  intro x hx η hη hηlt
  exact hcut (by simpa [Real.dist_eq, abs_of_pos hη] using hηlt) hη x hx

/-- Every closed inner energy window admits a finite internal net. -/
theorem exists_finite_innerWindow_net {a b δ : ℝ} (hδ : 0 < δ) :
    ∃ grid : Set ℝ,
      grid ⊆ Icc a b ∧ grid.Finite ∧
      Icc a b ⊆ ⋃ x ∈ grid, Metric.ball x δ :=
  finite_cover_balls_of_compact isCompact_Icc hδ

/-- Combined finite-net assembly for a regular boundary witness. -/
theorem exists_finiteNet_and_commonBoundaryCutoff
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N}
    {E₀ r a b δ ε : ℝ} {Mb Mb' : ℝ → LocalETHMatrix N}
    (hboundary : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)))
    (_hderiv : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' x) x)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r))
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ grid : Finset ℝ,
      (∀ x ∈ grid, x ∈ Icc a b) ∧
      (Icc a b ⊆ ⋃ x ∈ (grid : Set ℝ), Metric.ball x δ) ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ x ∈ grid, ∀ η : ℝ, 0 < η → η < η₀ →
          matrixEntryDistance
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε := by
  obtain ⟨net, hnetsub, hnetfinite, hcover⟩ :=
    exists_finite_innerWindow_net (a := a) (b := b) hδ
  let grid : Finset ℝ := hnetfinite.toFinset
  have hgridset : (grid : Set ℝ) = net := by
    ext x
    simp [grid]
  have hgrid : ∀ x ∈ grid, x ∈ Icc a b := by
    intro x hx
    apply hnetsub
    apply hnetfinite.mem_toFinset.mp
    simpa [grid] using hx
  have hboundary' : ∀ x ∈ grid,
      Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) := by
    intro x hx
    exact hboundary x (hinner (hgrid x hx))
  obtain ⟨η₀, hη₀, hcut⟩ :=
    exists_heightCutoff_branch_close_boundary_on_finset
      grid hboundary' hε
  refine ⟨grid, hgrid, ?_, η₀, hη₀, hcut⟩
  simpa [hgridset] using hcover

/-- The compactness package is available for the unconditional CEH
branch and the witness from `LocalETHRegularBoundaryWindow`. -/
theorem cehBoundaryCompactnessPackage
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) {E₀ r c K a b δ ε : ℝ}
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    (hinner : Icc a b ⊆ Ioo (E₀ - r) (E₀ + r))
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ Mb Mb' : ℝ → LocalETHMatrix N,
      (∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        Tendsto
            (fun η : ℝ => hermitianMDEBranch hF hs
              ((x : ℂ) + (η : ℂ) * Complex.I))
            (nhdsWithin 0 (Ioi 0)) (nhds (Mb x))) ∧
      (∀ x ∈ Ioo (E₀ - r) (E₀ + r),
        HasLocalETHMatrixDerivAt Mb (Mb' x) x) ∧
      (∀ i j : Fin N,
        UniformContinuousOn (fun x => Mb x i j) (Icc a b)) ∧
      ∃ grid : Finset ℝ,
        (∀ x ∈ grid, x ∈ Icc a b) ∧
        (Icc a b ⊆ ⋃ x ∈ (grid : Set ℝ), Metric.ball x δ) ∧
        ∃ η₀ : ℝ, 0 < η₀ ∧
          ∀ x ∈ grid, ∀ η : ℝ, 0 < η → η < η₀ →
            matrixEntryDistance
              (hermitianMDEBranch hF hs
                ((x : ℂ) + (η : ℂ) * Complex.I))
              (Mb x) < ε := by
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  have hboundary : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      Tendsto
        (fun η : ℝ => hermitianMDEBranch hF hs
          ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)) :=
    fun x hx => (hdata x hx).1
  have hderiv : ∀ x ∈ Ioo (E₀ - r) (E₀ + r),
      HasLocalETHMatrixDerivAt Mb (Mb' x) x :=
    fun x hx => (hdata x hx).2.1
  refine ⟨Mb, Mb', hboundary, hderiv,
    uniformContinuousOn_boundaryWitness_entries_on_innerWindow hderiv hinner, ?_⟩
  exact exists_finiteNet_and_commonBoundaryCutoff
    hboundary hderiv hinner hδ hε

end CEHNative.BlockBand.CEH
