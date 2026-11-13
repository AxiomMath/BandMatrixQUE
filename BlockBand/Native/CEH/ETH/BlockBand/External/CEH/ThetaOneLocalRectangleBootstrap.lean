module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOnePositiveHeightDerivative

/-!
# Local-rectangle bootstrap for the CEH theta-one strip

This module isolates the exact non-circular inequality needed by a fixed-`N`
open/closed continuation.  A mixed boundary denominator remains nondegenerate
at positive height whenever the corresponding normalized mixed trace has moved
by less than the available stability margin.  The statement uses the matrix
MDE branch and the exact normalized trace.

The pointwise vertical boundary limits do not imply the required trace
discrepancy uniformly on an energy rectangle.  Positive-height derivative
control applies only after nondegeneracy has been propagated, so using it to
establish that discrepancy without a separate scalar closure estimate is
circular.  We therefore state the missing estimate as a `Prop` (a hypothesis
here); this module does not prove `UniformBoundaryToStripResidual`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology

/-- Exact positive-height mixed trace for two energies at one common height. -/
def positiveHeightMixedTrace {N : ℕ} (Mf : ℂ → LocalETHMatrix N)
    (x y η : ℝ) : ℂ :=
  Conventions.normalizedTrace
    (Mf ((x : ℂ) + (η : ℂ) * Complex.I) *
     Mf ((y : ℂ) + (η : ℂ) * Complex.I))

/-- Exact positive-height mixed stability value. -/
def positiveHeightMixedStabilityValue {N : ℕ} (s : ℝ)
    (Mf : ℂ → LocalETHMatrix N) (x y η : ℝ) : ℝ :=
  ‖1 - (s : ℂ) * positiveHeightMixedTrace Mf x y η‖

/-- For each fixed pair of energies, the available vertical boundary limits do
transport the exact mixed trace to its boundary value.  The missing step below
is uniformity as the first energy ranges over a neighborhood. -/
theorem tendsto_positiveHeightMixedTrace_of_boundary
    {N : ℕ} {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    {x y : ℝ}
    (hx : Tendsto (fun η : ℝ => Mf ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Mb x)))
    (hy : Tendsto (fun η : ℝ => Mf ((y : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds (Mb y))) :
    Tendsto (fun η : ℝ => positiveHeightMixedTrace Mf x y η)
      (nhdsWithin 0 (Ioi 0)) (nhds (boundaryMixedTrace Mb x y)) := by
  rw [boundaryMixedTrace_eq_normalizedTrace_mul]
  change Tendsto
    ((fun p : LocalETHMatrix N × LocalETHMatrix N =>
      Conventions.normalizedTrace (p.1 * p.2)) ∘
      fun η : ℝ =>
        (Mf ((x : ℂ) + (η : ℂ) * Complex.I),
         Mf ((y : ℂ) + (η : ℂ) * Complex.I)))
    (nhdsWithin 0 (Ioi 0))
    (nhds (Conventions.normalizedTrace (Mb x * Mb y)))
  exact (continuous_normalizedTrace.comp
    (continuous_fst.mul continuous_snd)).continuousAt.tendsto.comp
      (hx.prodMk_nhds hy)

/-- The elementary local bootstrap inequality.  Moving the normalized mixed
trace by `q` can consume at most `|s| q` of the boundary stability
margin.  No matrix norm or dimension-dependent comparison is hidden here. -/
theorem boundaryMixedStability_sub_traceError_le_positiveHeight
    {N : ℕ} (s : ℝ) (Mf : ℂ → LocalETHMatrix N)
    (Mb : ℝ → LocalETHMatrix N) (x y η : ℝ) :
    boundaryMixedStabilityValue s Mb x y -
        |s| * ‖positiveHeightMixedTrace Mf x y η -
          boundaryMixedTrace Mb x y‖ ≤
      positiveHeightMixedStabilityValue s Mf x y η := by
  let tb := boundaryMixedTrace Mb x y
  let tp := positiveHeightMixedTrace Mf x y η
  let ub : ℂ := 1 - (s : ℂ) * tb
  let up : ℂ := 1 - (s : ℂ) * tp
  have htri : ‖ub‖ ≤ ‖ub - up‖ + ‖up‖ := by
    calc
      ‖ub‖ = ‖(ub - up) + up‖ := by ring
      _ ≤ ‖ub - up‖ + ‖up‖ := norm_add_le _ _
  have herr : ‖ub - up‖ = |s| * ‖tp - tb‖ := by
    have heq : ub - up = (s : ℂ) * (tp - tb) := by
      dsimp only [ub, up]
      ring
    rw [heq, norm_mul]
    simp [Real.norm_eq_abs]
  dsimp only [boundaryMixedStabilityValue,
    positiveHeightMixedStabilityValue]
  dsimp only [tb, tp] at htri herr
  rw [herr] at htri
  linarith

/-- Quantitative closure of one local rectangle: a strict trace-discrepancy
budget below the unused boundary margin forces the desired positive-height
mixed denominator bound throughout that rectangle. -/
theorem positiveHeightMixedStability_gt_of_local_trace_budget
    {N : ℕ} {s c₀ c₁ q : ℝ}
    {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    {x y η : ℝ}
    (hboundary : c₀ ≤ boundaryMixedStabilityValue s Mb x y)
    (htrace : ‖positiveHeightMixedTrace Mf x y η -
      boundaryMixedTrace Mb x y‖ < q)
    (hbudget : |s| * q < c₀ - c₁) :
    c₁ < positiveHeightMixedStabilityValue s Mf x y η := by
  by_cases hs0 : s = 0
  · simp [hs0, positiveHeightMixedStabilityValue,
      boundaryMixedStabilityValue] at hboundary hbudget ⊢
    linarith
  · have hboot := boundaryMixedStability_sub_traceError_le_positiveHeight
      s Mf Mb x y η
    have hsq : |s| * ‖positiveHeightMixedTrace Mf x y η -
        boundaryMixedTrace Mb x y‖ < |s| * q :=
      mul_lt_mul_of_pos_left htrace (abs_pos.mpr hs0)
    linarith

/-- The scalar closure condition needed by the fixed-`N` local-rectangle continuation (a
hypothesis here).  Around a boundary center `x₀`, it asks for one
common height cutoff and one neighboring energy radius controlling the exact
mixed trace against the boundary mixed trace.  This is a proposition,
not a substituted local law. -/
def LocalRectangleTraceClosure {N : ℕ}
    (Mf : ℂ → LocalETHMatrix N) (Mb : ℝ → LocalETHMatrix N)
    (a b x₀ q : ℝ) : Prop :=
  ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧
    ∀ x ∈ Icc a b, dist x x₀ < δ →
      ∀ η : ℝ, 0 < η → η < η₀ →
        ‖positiveHeightMixedTrace Mf x x₀ η -
          boundaryMixedTrace Mb x x₀‖ < q

/-- If the missing scalar closure holds at one center, the compact boundary
mixed-stability radius immediately gives a positive-height rectangle
with a reduced denominator margin.  All constants are fixed-`N` and explicit. -/
theorem exists_localRectangle_positiveHeightMixedStability
    {N : ℕ} {s a b x₀ c₀ c₁ q δb : ℝ}
    {Mf : ℂ → LocalETHMatrix N} {Mb : ℝ → LocalETHMatrix N}
    (hδb : 0 < δb)
    (hboundary : ∀ x ∈ Icc a b, dist x x₀ < δb →
      c₀ ≤ boundaryMixedStabilityValue s Mb x x₀)
    (hclosure : LocalRectangleTraceClosure Mf Mb a b x₀ q)
    (hbudget : |s| * q < c₀ - c₁) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ δ ≤ δb ∧
      ∀ x ∈ Icc a b, dist x x₀ < δ →
        ∀ η : ℝ, 0 < η → η < η₀ →
          c₁ < positiveHeightMixedStabilityValue s Mf x x₀ η := by
  obtain ⟨δ, η₀, hδ, hη₀, hclose⟩ := hclosure
  let δ' := min δ δb
  have hδ' : 0 < δ' := by
    dsimp only [δ']
    exact lt_min hδ hδb
  refine ⟨δ', η₀, hδ', hη₀, min_le_right _ _, ?_⟩
  intro x hx hxx η hη hηlt
  apply positiveHeightMixedStability_gt_of_local_trace_budget
    (hboundary x hx (lt_of_lt_of_le hxx (min_le_right _ _)))
    (hclose x hx (lt_of_lt_of_le hxx (min_le_left _ _)) η hη hηlt)
    hbudget

end CEHNative.BlockBand.CEH
