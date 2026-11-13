module

public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEMatrixAdapter
public import Mathlib.Topology.Instances.Matrix

/-!
# Pointwise positive-height consequence of a regular CEH boundary window

The regular-window contract records only pointwise convergence to the upper
boundary value.  Consequently its direct consequence is pointwise and
uses a strictly smaller density margin: at each fixed boundary energy, the
positive-height normalized trace eventually has imaginary part larger than any
`c₀ < c`.

This module intentionally makes no uniform claim in the energy, dimension,
variance, or deformation.  Such a claim needs a separate uniform boundary
convergence or equicontinuity argument.  In particular, the boundary lower
bound cannot hold with the same margin at every positive height, since a
Stieltjes transform decays at large imaginary part.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- The normalized trace is continuous in the finite-dimensional matrix
topology. -/
theorem continuous_normalizedTrace {N : ℕ} :
    Continuous (Conventions.normalizedTrace :
      LocalETHMatrix N → ℂ) := by
  unfold Conventions.normalizedTrace
  fun_prop

/-- A pointwise boundary limit induces convergence of the imaginary part of
the normalized trace along positive heights. -/
theorem tendsto_normalizedTrace_im_of_boundary
    {N : ℕ} (Mf : ℂ → LocalETHMatrix N) (Mb : ℝ → LocalETHMatrix N)
    (x : ℝ)
    (hboundary :
      Tendsto
        (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x))) :
    Tendsto
      (fun η : ℝ =>
        (Conventions.normalizedTrace
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im)
      (nhdsWithin 0 (Ioi 0))
      (nhds (Conventions.normalizedTrace (Mb x)).im) := by
  exact
    (Complex.continuous_im.tendsto
      (Conventions.normalizedTrace (Mb x))).comp
      (continuous_normalizedTrace.continuousAt.tendsto.comp hboundary)

/-- At a fixed energy in a regular boundary window, every strictly reduced
bulk margin holds eventually at positive height.

This is deliberately an `Eventually` statement at
`𝓝[Set.Ioi 0] 0`; it contains no unsupported uniform cutoff. -/
theorem eventually_normalizedTrace_im_gt_of_regularBoundaryWindow
    {N : ℕ} {s : ℝ} {Mf : ℂ → LocalETHMatrix N}
    {E₀ r c K x c₀ : ℝ}
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hx : x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
      c₀ <
        (Conventions.normalizedTrace
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im := by
  obtain ⟨Mb, Mb', hMb⟩ := hregular.boundary
  have hdata := hMb x hx
  have hlim :=
    tendsto_normalizedTrace_im_of_boundary Mf Mb x hdata.1
  have hc₀' : c₀ < (Conventions.normalizedTrace (Mb x)).im :=
    lt_of_lt_of_le hc₀ hdata.2.2.2.1
  exact hlim.eventually (eventually_gt_nhds hc₀')

/-- Non-strict form of the pointwise reduced-margin consequence, convenient
for the bulk mixed-denominator estimates. -/
theorem eventually_normalizedTrace_im_ge_of_regularBoundaryWindow
    {N : ℕ} {s : ℝ} {Mf : ℂ → LocalETHMatrix N}
    {E₀ r c K x c₀ : ℝ}
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hx : x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
      c₀ ≤
        (Conventions.normalizedTrace
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im :=
  (eventually_normalizedTrace_im_gt_of_regularBoundaryWindow
    hregular hx hc₀).mono
    (fun _ h => h.le)

/-- Explicit pointwise cutoff form of the reduced-margin statement.

The cutoff may depend on all data, including `x`, `N`, `s`, the deformation
encoded by `Mf`, and the chosen boundary witness.  No uniformity is asserted. -/
theorem exists_pointwiseHeightCutoff_normalizedTrace_im_ge
    {N : ℕ} {s : ℝ} {Mf : ℂ → LocalETHMatrix N}
    {E₀ r c K x c₀ : ℝ}
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hx : x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        c₀ ≤
          (Conventions.normalizedTrace
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im := by
  have hevent :=
    eventually_normalizedTrace_im_ge_of_regularBoundaryWindow
      hregular hx hc₀
  have hfull :
      ∀ᶠ η : ℝ in nhds 0, η ∈ Ioi (0 : ℝ) →
        c₀ ≤
          (Conventions.normalizedTrace
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨η₀, hη₀, hcut⟩ := Metric.eventually_nhds_iff.mp hfull
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηlt
  apply hcut
  · simpa [Real.dist_eq, abs_of_pos hη] using hηlt
  · exact hη

/-- Concrete scalar-MDE form of the pointwise reduced-margin result.

This supplies exactly the positive-height `upperBranch.im` hypothesis consumed
by the bulk mixed-denominator bootstrap, but only below a cutoff depending on
the fixed energy and all ambient data. -/
theorem exists_pointwiseHeightCutoff_upperBranch_im_ge
    {N : ℕ} (hN : 0 < N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {E₀ r c K x c₀ : ℝ}
    (hregular :
      LocalETHRegularBoundaryWindow s
        (hermitianMDEBranch hF hs) E₀ r c K)
    (hx : x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        c₀ ≤
          (upperBranch hN (hermitianSpectrum hF) hs
            ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
  obtain ⟨η₀, hη₀, hcut⟩ :=
    exists_pointwiseHeightCutoff_normalizedTrace_im_ge
      hregular hx hc₀
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη hηlt
  have htrace := hcut η hη hηlt
  have hz :
      (((x : ℂ) + (η : ℂ) * Complex.I).im) = η := by simp
  rw [normalizedTrace_hermitianMDEBranch hF hN hs
    (by simpa [hz] using hη.ne')] at htrace
  rw [hermitianMDEMean_of_im_pos hF hN hs
    (by simpa [hz] using hη)] at htrace
  exact htrace

/-- A finite energy grid admits a common reduced-margin neighborhood.

This is the strongest uniformity obtainable from the pointwise boundary
contract alone without compactness/equicontinuity input: the grid must be
fixed and finite. -/
theorem eventually_normalizedTrace_im_ge_on_finset
    {N : ℕ} {s : ℝ} {Mf : ℂ → LocalETHMatrix N}
    {E₀ r c K c₀ : ℝ} (grid : Finset ℝ)
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hgrid : ∀ x ∈ grid, x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ x ∈ grid,
        c₀ ≤
          (Conventions.normalizedTrace
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im := by
  classical
  induction grid using Finset.induction_on with
  | empty =>
      simp
  | @insert x grid hx ih =>
      have hxevent :=
        eventually_normalizedTrace_im_ge_of_regularBoundaryWindow
          hregular (hgrid x (by simp)) hc₀
      have hgrid' : ∀ y ∈ grid, y ∈ Ioo (E₀ - r) (E₀ + r) := by
        intro y hy
        exact hgrid y (by simp [hy])
      have hievent := ih hgrid'
      filter_upwards [hxevent, hievent] with η hxη hiη
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxη
      · exact hiη y hy

/-- Explicit common cutoff for a fixed finite energy grid.

The cutoff still depends on the grid and all ambient data; this theorem does
not upgrade pointwise boundary convergence to a continuum-uniform statement. -/
theorem exists_heightCutoff_normalizedTrace_im_ge_on_finset
    {N : ℕ} {s : ℝ} {Mf : ℂ → LocalETHMatrix N}
    {E₀ r c K c₀ : ℝ} (grid : Finset ℝ)
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hgrid : ∀ x ∈ grid, x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ x ∈ grid, ∀ η : ℝ, 0 < η → η < η₀ →
        c₀ ≤
          (Conventions.normalizedTrace
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im := by
  have hevent :=
    eventually_normalizedTrace_im_ge_on_finset
      grid hregular hgrid hc₀
  have hfull :
      ∀ᶠ η : ℝ in nhds 0, η ∈ Ioi (0 : ℝ) →
        ∀ x ∈ grid,
          c₀ ≤
            (Conventions.normalizedTrace
              (Mf ((x : ℂ) + (η : ℂ) * Complex.I))).im :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨η₀, hη₀, hcut⟩ := Metric.eventually_nhds_iff.mp hfull
  refine ⟨η₀, hη₀, ?_⟩
  intro x hx η hη hηlt
  exact hcut (by simpa [Real.dist_eq, abs_of_pos hη] using hηlt) hη x hx

end CEHNative.BlockBand.CEH
