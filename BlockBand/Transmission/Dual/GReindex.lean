module

public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Martingale problems under a relabelling of the coordinates

For `e : Fin d' ≃ Fin d`, the relabelled path `Y' = Y ∘ e` solves the relabelled problem: drift
`b'(y')_i = b(y' ∘ e⁻¹)_{e i}`, covariance `a'(y')_{ij} = a(y' ∘ e⁻¹)_{e i, e j}`, domain
`{y' | y' ∘ e⁻¹ ∈ U}` (`isMPSolutionOn_reindex`). This puts a product of a pair and a rest into
the `ofFlat` layout of the next level, with the pair in the slots `(x₀, y_j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal

variable {d d' : ℕ} (e : Fin d' ≃ Fin d)

/-- The relabelling homeomorphism `y ↦ y ∘ e`. -/
def reindexHomeo : (Fin d → ℝ) ≃ₜ (Fin d' → ℝ) where
  toFun y := y ∘ e
  invFun y' := y' ∘ e.symm
  left_inv y := funext fun i => by simp
  right_inv y' := funext fun i => by simp
  continuous_toFun := continuous_pi fun i => continuous_apply (e i)
  continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i)

@[simp] theorem reindexHomeo_apply (y : Fin d → ℝ) : reindexHomeo e y = y ∘ e := rfl

@[simp] theorem reindexHomeo_symm_apply (y' : Fin d' → ℝ) :
    (reindexHomeo e).symm y' = y' ∘ e.symm := rfl

/-- The relabelled drift. -/
def reindexDrift (b : (Fin d → ℝ) → Fin d → ℝ) (y' : Fin d' → ℝ) : Fin d' → ℝ :=
  fun i => b (y' ∘ e.symm) (e i)

/-- The relabelled covariance. -/
def reindexDiff (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (y' : Fin d' → ℝ) :
    Matrix (Fin d') (Fin d') ℝ :=
  Matrix.of fun i j => a (y' ∘ e.symm) (e i) (e j)

/-- The relabelled domain. -/
def reindexDomain (U : Set (Fin d → ℝ)) : Set (Fin d' → ℝ) := {y' | y' ∘ e.symm ∈ U}

theorem comp_symm_comp (y : Fin d → ℝ) : (y ∘ e) ∘ e.symm = y := funext fun i => by simp

theorem isInteriorDomain_reindex {U : Set (Fin d → ℝ)} {W' : Set (Fin d' → ℝ)}
    (hW : IsInteriorDomain W' (reindexDomain e U)) :
    IsInteriorDomain (reindexHomeo e ⁻¹' W') U := by
  refine ⟨hW.1.preimage (reindexHomeo e).continuous, ?_, ?_⟩
  · rw [← (reindexHomeo e).preimage_closure]
    exact (reindexHomeo e).isCompact_preimage.2 hW.2.1
  · rw [← (reindexHomeo e).preimage_closure]
    intro y hy
    have := hW.2.2 hy
    simpa [reindexDomain, comp_symm_comp] using this

variable {Ω : Type*}

theorem exitTimeFrom_reindex (W' : Set (Fin d' → ℝ)) (Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) :
    exitTimeFrom W' (fun t ω => Y t ω ∘ e) ω = exitTimeFrom (reindexHomeo e ⁻¹' W') Y ω := rfl

theorem mpCompensated_reindex (b : (Fin d → ℝ) → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (i : Fin d') (t : ℝ≥0) (ω : Ω) :
    mpCompensated (reindexDrift e b) (fun t ω => Y t ω ∘ e) i t ω = mpCompensated b Y (e i) t ω := by
  simp only [mpCompensated, reindexDrift, comp_symm_comp, Function.comp_apply]

variable [MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}

/-- **Relabelling the coordinates of a martingale-problem solution.** -/
theorem isMPSolutionOn_reindex (h : IsMPSolutionOn Q 𝓖 b a U Y) :
    IsMPSolutionOn Q 𝓖 (reindexDrift e b) (reindexDiff e a) (reindexDomain e U)
      (fun t ω => Y t ω ∘ e) := by
  refine ⟨fun t => (reindexHomeo e).continuous.comp_stronglyMeasurable (h.adapted t), ?_,
    fun W' hW' i => ?_, fun W' hW' i j => ?_⟩
  · filter_upwards [h.continuous] with ω hω
    exact (reindexHomeo e).continuous.comp hω
  · obtain ⟨N, hN, hNe⟩ := h.drift _ (isInteriorDomain_reindex e hW') (e i)
    refine ⟨N, hN, fun t => (hNe t).trans (Eventually.of_forall fun ω => ?_)⟩
    simp only [stoppedProcess, exitTimeFrom_reindex, mpCompensated_reindex]
  · obtain ⟨N, hN, hNe⟩ := h.bracket _ (isInteriorDomain_reindex e hW') (e i) (e j)
    refine ⟨N, hN, fun t => (hNe t).trans (Eventually.of_forall fun ω => ?_)⟩
    simp only [stoppedProcess, exitTimeFrom_reindex, mpCompensated_reindex, reindexDiff,
      comp_symm_comp, Matrix.of_apply]

omit [MeasurableSpace Ω] in
theorem mpCompensated_congr_path {Y Y' : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (h : ∀ t, Y' t ω = Y t ω)
    (b : (Fin d → ℝ) → Fin d → ℝ) (i : Fin d) (t : ℝ≥0) :
    mpCompensated b Y' i t ω = mpCompensated b Y i t ω := by
  simp only [mpCompensated, h]

omit [MeasurableSpace Ω] in
theorem exitTimeFrom_congr_path {Y Y' : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (h : ∀ t, Y' t ω = Y t ω)
    (W : Set (Fin d → ℝ)) : exitTimeFrom W Y' ω = exitTimeFrom W Y ω := by
  simp only [exitTimeFrom, h]

/-- **Indistinguishable adapted versions** solve the same martingale problem. -/
theorem isMPSolutionOn_congr_indist (h : IsMPSolutionOn Q 𝓖 b a U Y) {Y' : ℝ≥0 → Ω → Fin d → ℝ}
    (hY' : ∀ t, StronglyMeasurable[𝓖 t] (Y' t)) (he : ∀ᵐ ω ∂Q, ∀ t, Y' t ω = Y t ω) :
    IsMPSolutionOn Q 𝓖 b a U Y' := by
  refine ⟨hY', ?_, fun W hW i => ?_, fun W hW i j => ?_⟩
  · filter_upwards [h.continuous, he] with ω hω he
    simpa only [he] using hω
  · obtain ⟨N, hN, hNe⟩ := h.drift W hW i
    refine ⟨N, hN, fun t => (hNe t).trans (he.mono fun ω hω => ?_)⟩
    simp only [stoppedProcess, exitTimeFrom_congr_path hω, mpCompensated_congr_path hω]
  · obtain ⟨N, hN, hNe⟩ := h.bracket W hW i j
    refine ⟨N, hN, fun t => (hNe t).trans (he.mono fun ω hω => ?_)⟩
    simp only [stoppedProcess, exitTimeFrom_congr_path hω, mpCompensated_congr_path hω, hω]

end BlockBand.Transmission.Dual.G
