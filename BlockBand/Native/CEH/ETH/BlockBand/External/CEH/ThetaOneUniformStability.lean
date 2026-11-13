module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneUniformStrip
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.OneResolventExpectationMDEVerticalStep

/-!
# Stability dependencies for the CEH theta-one strip

This module isolates the stability mechanism needed to upgrade the finite-net
boundary package to a continuum strip.  It proves an exact two-parameter
implicit-function modulus from a lower bound on the mixed MDE stability
denominator, propagates the regular boundary stability bound simultaneously on
finite grids, and proves the scalar comparison which puts the canonical CEH
height inside a strip once a density lower bound is available.

The continuum statement is recorded as a proposition:
`UniformBoundaryToStripResidual` is the assertion that the unconditional branch
converges to the boundary witness uniformly on a closed inner energy window.  The
regular-boundary hypothesis `LocalETHRegularBoundaryWindow` and the MDE estimates
here prove this on every fixed finite net, but do not supply the height-uniform
energy modulus needed between net points.  This module does not prove it, and
no theorem below assumes it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped BigOperators ComplexConjugate Topology

/-- Exact stability value occurring in `LocalETHRegularBoundaryWindow`. -/
def matrixStabilityValue {N : ℕ} (s : ℝ) (M : LocalETHMatrix N) : ℝ :=
  ‖1 - (s : ℂ) * Conventions.normalizedTrace (M * M)‖

/-- The stability value is continuous in the finite-dimensional matrix
topology. -/
theorem continuous_matrixStabilityValue {N : ℕ} (s : ℝ) :
    Continuous (matrixStabilityValue (N := N) s) := by
  unfold matrixStabilityValue
  apply continuous_norm.comp
  exact continuous_const.sub
    (continuous_const.mul
      (continuous_normalizedTrace.comp (continuous_id.mul continuous_id)))

/-- A lower bound for the mixed stability denominator gives a
nondegenerate implicit-function modulus.  This is the sharp algebraic step:
no reciprocal height bound is used. -/
theorem norm_upperBranch_sub_le_of_mixedStability
    {N : ℕ} (hN : 0 < N) (f : DeformationSpectrum N)
    {s γ B : ℝ} (hs : 0 < s) (hγ : 0 < γ)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hdenom : γ ≤ ‖fourAdjointDenominator false false f s
      z₁ (upperBranch hN f hs z₁) z₂ (upperBranch hN f hs z₂)‖)
    (hpair : ‖average (fun i =>
      entry f s z₁ (upperBranch hN f hs z₁) i *
      entry f s z₂ (upperBranch hN f hs z₂) i)‖ ≤ B) :
    ‖upperBranch hN f hs z₁ - upperBranch hN f hs z₂‖ ≤
      ‖z₁ - z₂‖ * B / γ := by
  let D := fourAdjointDenominator false false f s
    z₁ (upperBranch hN f hs z₁) z₂ (upperBranch hN f hs z₂)
  let dm := upperBranch hN f hs z₁ - upperBranch hN f hs z₂
  let A := average (fun i =>
    entry f s z₁ (upperBranch hN f hs z₁) i *
    entry f s z₂ (upperBranch hN f hs z₂) i)
  have hid : D * dm = (z₁ - z₂) * A := by
    exact CEHNative.BlockBand.External.CEH.upperBranch_twoParameter_difference_identity
      hN f hs hz₁ hz₂
  have hleft : γ * ‖dm‖ ≤ ‖D‖ * ‖dm‖ :=
    mul_le_mul_of_nonneg_right hdenom (norm_nonneg dm)
  have hright : ‖D‖ * ‖dm‖ ≤ ‖z₁ - z₂‖ * B := by
    rw [← norm_mul, hid, norm_mul]
    exact mul_le_mul_of_nonneg_left hpair (norm_nonneg (z₁ - z₂))
  apply (le_div_iff₀ hγ).2
  calc
    ‖dm‖ * γ = γ * ‖dm‖ := by ring
    _ ≤ ‖D‖ * ‖dm‖ := hleft
    _ ≤ ‖z₁ - z₂‖ * B := hright

/-- Pointwise boundary convergence transports the stability expression
to its boundary value. -/
theorem tendsto_matrixStabilityValue_of_boundary
    {N : ℕ} {s x : ℝ} {Mf : ℂ → LocalETHMatrix N}
    {Mb : ℝ → LocalETHMatrix N}
    (hboundary : Tendsto
      (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Mb x))) :
    Tendsto
      (fun η : ℝ => matrixStabilityValue s
        (Mf ((x : ℂ) + (η : ℂ) * Complex.I)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (matrixStabilityValue s (Mb x))) := by
  change Tendsto
    (matrixStabilityValue s ∘
      fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
    (nhdsWithin 0 (Ioi 0)) (nhds (matrixStabilityValue s (Mb x)))
  exact (continuous_matrixStabilityValue s).continuousAt.tendsto.comp hboundary

/-- On a fixed finite grid, every strictly reduced boundary stability margin
holds at a common sufficiently small positive height. -/
theorem eventually_matrixStability_ge_on_finset
    {N : ℕ} {s E₀ r c K c₀ : ℝ}
    {Mf : ℂ → LocalETHMatrix N} (grid : Finset ℝ)
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hgrid : ∀ x ∈ grid, x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ x ∈ grid,
        c₀ ≤ matrixStabilityValue s
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) := by
  classical
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  induction grid using Finset.induction_on with
  | empty => simp
  | @insert x grid hx ih =>
      have hxdata := hdata x (hgrid x (by simp))
      have hxlim := tendsto_matrixStabilityValue_of_boundary
        (s := s) hxdata.1
      have hxmargin : c₀ < matrixStabilityValue s (Mb x) :=
        lt_of_lt_of_le hc₀ hxdata.2.2.2.2.2
      have hxevent : ∀ᶠ η : ℝ in nhdsWithin 0 (Ioi 0),
          c₀ ≤ matrixStabilityValue s
            (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) :=
        (hxlim.eventually (eventually_gt_nhds hxmargin)).mono
          (fun _ h => h.le)
      have hgrid' : ∀ y ∈ grid, y ∈ Ioo (E₀ - r) (E₀ + r) := by
        intro y hy
        exact hgrid y (by simp [hy])
      have hievent := ih hgrid'
      filter_upwards [hxevent, hievent] with η hxη hiη
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hxη
      · exact hiη y hy

/-- Explicit common cutoff form of finite-grid stability propagation. -/
theorem exists_heightCutoff_matrixStability_ge_on_finset
    {N : ℕ} {s E₀ r c K c₀ : ℝ}
    {Mf : ℂ → LocalETHMatrix N} (grid : Finset ℝ)
    (hregular : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hgrid : ∀ x ∈ grid, x ∈ Ioo (E₀ - r) (E₀ + r))
    (hc₀ : c₀ < c) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ x ∈ grid, ∀ η : ℝ, 0 < η → η < η₀ →
        c₀ ≤ matrixStabilityValue s
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) := by
  have hevent := eventually_matrixStability_ge_on_finset
    grid hregular hgrid hc₀
  have hfull : ∀ᶠ η : ℝ in nhds 0, η ∈ Ioi (0 : ℝ) →
      ∀ x ∈ grid,
        c₀ ≤ matrixStabilityValue s
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨η₀, hη₀, hcut⟩ := Metric.eventually_nhds_iff.mp hfull
  refine ⟨η₀, hη₀, ?_⟩
  intro x hx η hη hηlt
  exact hcut (by simpa [Real.dist_eq, abs_of_pos hη] using hηlt) hη x hx

/-- Narrow analytic residual for the continuum upgrade.  It refers only to the
branch, its boundary witness, and the exact inner window.  It is
a proposition rather than a structure carrying a substitute hypothesis. -/
def UniformBoundaryToStripResidual
    {N : ℕ} (Mf : ℂ → LocalETHMatrix N) (Mb : ℝ → LocalETHMatrix N)
    (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ x ∈ Icc a b, ∀ η : ℝ, 0 < η → η < η₀ →
        matrixEntryDistance
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε

/-- Finite-net convergence is the proved restriction of the continuum
residual. -/
theorem uniformBoundaryToStripResidual_on_finset
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    {a b : ℝ} (grid : Finset ℝ)
    (hgrid : ∀ x ∈ grid, x ∈ Icc a b)
    (hboundary : ∀ x ∈ Icc a b,
      Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
        (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ x ∈ grid, ∀ η : ℝ, 0 < η → η < η₀ →
        matrixEntryDistance
          (Mf ((x : ℂ) + (η : ℂ) * Complex.I)) (Mb x) < ε := by
  apply exists_heightCutoff_branch_close_boundary_on_finset grid
  · intro x hx
    exact hboundary x (hgrid x hx)
  · exact hε

/-- If the exact spacing quantity already exceeds one at a positive test
height, the canonical solution lies below that height. -/
theorem cehTypicalSpacing_lt_of_one_lt_spacingQuantity
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x H : ℝ) (hH : 0 < H)
    (hone : 1 < spacingQuantity (by omega) f hs x H) :
    cehTypicalSpacing N hN f hs x < H := by
  have heta := (cehTypicalSpacing_spec N hN f hs x).1
  by_contra hnot
  have hHeta : H ≤ cehTypicalSpacing N hN f hs x := le_of_not_gt hnot
  rcases hHeta.eq_or_lt with heq | hlt
  · rw [heq, (cehTypicalSpacing_spec N hN f hs x).2] at hone
    exact lt_irrefl 1 hone
  · have hmono := (spacingRegularity (by omega) f hs).strictMono_height
      x hH heta hlt
    rw [(cehTypicalSpacing_spec N hN f hs x).2] at hmono
    linarith

/-- Exact canonical-height inclusion from a density lower bound at the test
height `H / N^ξ`.  This preserves the CEH scaling without replacing it by an
asymptotic notation. -/
theorem rpow_mul_cehTypicalSpacing_lt_of_density_lower
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s : ℝ} (hs : 0 < s) (x ξ H ρ₀ : ℝ)
    (hH : 0 < H)
    (hdensity : ρ₀ ≤ density (upperBranch (by omega) f hs
      ((x : ℂ) + ((H / (N : ℝ) ^ ξ : ℝ) : ℂ) * Complex.I)))
    (hlarge : 1 < (N : ℝ) * (H / (N : ℝ) ^ ξ) * ρ₀) :
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x < H := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < (N : ℝ) ^ ξ := Real.rpow_pos_of_pos hNpos ξ
  have htest : 0 < H / (N : ℝ) ^ ξ := div_pos hH hpow
  have hq : 1 < spacingQuantity (by omega) f hs x
      (H / (N : ℝ) ^ ξ) := by
    rw [spacingQuantity, ite_eq_left htest]
    exact hlarge.trans_le (mul_le_mul_of_nonneg_left hdensity
      (mul_nonneg (Nat.cast_nonneg N) htest.le))
  have heta := cehTypicalSpacing_lt_of_one_lt_spacingQuantity
    hN f hs x (H / (N : ℝ) ^ ξ) htest hq
  calc
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x <
        (N : ℝ) ^ ξ * (H / (N : ℝ) ^ ξ) :=
      mul_lt_mul_of_pos_left heta hpow
    _ = H := by field_simp

end CEHNative.BlockBand.CEH
