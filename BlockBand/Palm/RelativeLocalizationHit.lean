module

public import BlockBand.Palm.RelativeLocalizationStopped
public import BlockBand.Palm.RelativeLocalizationFailure

/-!
# Relative localization: the concrete raw-filtration stopping time

`stopSet N ℓ E r₀ c₁ C₁ g = failSet N ℓ E r₀ c₁ C₁ ∪ {λ | ∃ i ≠ j, |λ_i - λ_j| ≤ g}` is closed;
`flowStop` is its first entrance time by `u ↦ flowLam F (s+u)`, a stopping time of the raw
shifted filtration (`isStoppingTime_flowStop`, from `isStoppingTime_hitTime`). Before it, the
relaxed clauses (`c₁/2`, `2C₁`) and all gaps `> g` hold (`good_before_flowStop`), so
`flow_tilted_expectation_le` applies with `ρ = flowStop` (`flow_tilted_expectation_flowStop`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-- Small-gap set. -/
def gapSet (N : ℕ) (g : ℝ) : Set (Fin N → ℝ) := {lam | ∃ i j : Fin N, i ≠ j ∧ |lam i - lam j| ≤ g}

theorem isClosed_gapSet (N : ℕ) (g : ℝ) : IsClosed (gapSet N g) := by
  have : gapSet N g = ⋃ i : Fin N, ⋃ j : Fin N, {lam : Fin N → ℝ | i ≠ j ∧ |lam i - lam j| ≤ g} := by
    ext lam; simp [gapSet]
  rw [this]
  refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j => ?_
  by_cases hij : i ≠ j
  · simp only [hij, true_and, ne_eq, not_false_eq_true]
    exact isClosed_le (((continuous_apply i).sub (continuous_apply j)).abs) continuous_const
  · simp [hij]

/-- The stopping set. -/
def stopSet (N ℓ : ℕ) (E r₀ c₁ C₁ g : ℝ) : Set (Fin N → ℝ) :=
  failSet N ℓ E r₀ c₁ C₁ ∪ gapSet N g

/-- The stopping time: first entrance of `flowLam F (s + ·)` into the stopping set. -/
def flowStop (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (E r₀ c₁ C₁ g : ℝ) :
    FlowSample N → WithTop ℝ≥0 :=
  hitTime (fun u ω => flowLam F (s + u) ω) (stopSet N ℓ E r₀ c₁ C₁ g)

theorem isStoppingTime_flowStop {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (s : ℝ≥0) (ℓ : ℕ) (E r₀ c₁ C₁ g : ℝ) :
    IsStoppingTime (shiftFiltration (flowFiltration N) s) (flowStop F s ℓ E r₀ c₁ C₁ g) :=
  isStoppingTime_hitTime (shiftFiltration (flowFiltration N) s) _
    (fun u => flowLam_adapted F (s + u))
    (fun ω => (flowLam_continuous hF ω).comp (continuous_const.add continuous_id))
    ((isClosed_failSet N ℓ E r₀ c₁ C₁).union (isClosed_gapSet N g))

theorem good_before_flowStop {F : Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0} {ℓ : ℕ}
    {E r₀ c₁ C₁ g : ℝ} {ω : FlowSample N} {u : ℝ≥0}
    (hu : (u : WithTop ℝ≥0) < flowStop F s ℓ E r₀ c₁ C₁ g ω) :
    (∀ i j : Fin N, ℓ ≤ labelDist i j →
        c₁ / 2 * labelDist i j / N ≤ |flowLam F (s + u) ω i - flowLam F (s + u) ω j|) ∧
      (∀ i j : Fin N, labelDist i j < ℓ →
        min |flowLam F (s + u) ω i - E| |flowLam F (s + u) ω j - E| ≤ r₀ / 8 →
        |flowLam F (s + u) ω i - flowLam F (s + u) ω j| ≤ 2 * C₁ * ℓ / N) ∧
      (∀ i j : Fin N, i ≠ j → g ≤ |flowLam F (s + u) ω i - flowLam F (s + u) ω j|) := by
  have h := notMem_of_lt_hitTime hu
  simp only [stopSet, Set.mem_union, not_or] at h
  obtain ⟨h1, h2⟩ := relaxed_of_not_mem_failSet h.1
  refine ⟨h1, h2, fun i j hij => ?_⟩
  by_contra hlt
  push Not at hlt
  exact h.2 ⟨i, j, hij, hlt.le⟩

/-- The tilted expectation bound with the concrete stopping time `flowStop`. -/
theorem flow_tilted_expectation_flowStop (hIto : SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) {v₀ : FlowSample N → Fin N → ℝ}
    (hv₀m : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {ν E d R r₀ c₁ C₁ K : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (hρ : d + 2 * R ≤ r₀ / 8)
    (hc₁ : 0 < c₁) (hK0 : 0 ≤ K)
    (hK : 2 * ℓ * (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) +
          (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N) ≤ K)
    (T : ℝ≥0) :
    ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => tiltedMass K (rlPhi ν E d R)
        ((u : ℝ), sumVec (flowLam F (s + u) ω) (flowMass F s ℓ b₀ g v₀ u ω)))
        (flowStop F s ℓ E r₀ c₁ C₁ g) T ω ∂flowLaw N a ≤
      ∫ ω, tiltedMass K (rlPhi ν E d R)
        (0, sumVec (flowLam F s ω) (flowMass F s ℓ b₀ g v₀ 0 ω)) ∂flowLaw N a := by
  refine flow_tilted_expectation_le hIto hStop hDBM hF a s hs hℓ b₀ hg hv₀m hv₀ hν hd hR hρ
    (c₁ := c₁ / 2) (C₁ := 2 * C₁) (by positivity) hK0 ?_ _ (isStoppingTime_flowStop hF s ℓ E r₀ c₁ C₁ g)
    (fun ω u hu => ?_) T
  · exact hK
  · obtain ⟨h1, h2, h3⟩ := good_before_flowStop hu
    exact ⟨h1, fun i j hij hm => (h2 i j hij hm).trans_eq (by ring), h3⟩

end BlockBand.Palm.RelativeLocalization
