module

public import BlockBand.Transmission.Dual.Unique
public import BlockBand.Transmission.Dual.GCPath
public import BlockBand.Transmission.Dual.GChartQ

/-!
# The random-start deletion statement `DelFrom` and the top of the assembly

* **`DelFrom D₀ q`**: for every old-state space `(S, μ)` (`S : Type`, `μ` a probability) and
  every measurable flat start `ξ : S → 𝒞_q`, there are a filtered probability space
  `(Ω, 𝓖, P)`, a map `π : Ω → S` with `P ∘ π⁻¹ = μ` and `σ(π) ≤ 𝓖₀`, and a realization
  `(N, X, Y)` of the class `IsDualFrom` (adapted, deletion paths at **every** `ω`, martingale
  clauses at every level `1 ≤ q' ≤ q`) that starts at `(q; ξ ∘ π)` at every `ω`.
  Measurability in the start is carried by `π` and `S`; no measurable choice of laws is used.
* `delFrom_zero`: the absorbed empty state.
* **`dualBoundaryLaw_of_delStep`**: the induction step `DelFrom D₀ k → DelFrom D₀ (k+1)` for
  `D₀ > 0` gives the whole `DualBoundaryLawStatement` (`dualBoundaryLaw_of_exists`). The step
  itself, the gluing of levels, is `delFrom_succ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- **The random-start deletion process at level `q`** (existence statement). -/
def DelFrom (D0 : ℝ) (q : ℕ) : Prop :=
  ∀ (S : Type) (_ : MeasurableSpace S) (μ : Measure S), IsProbabilityMeasure μ →
    ∀ ξ : S → Fin (q + q) → ℝ, Measurable ξ → (∀ s, ξ s ∈ flatChamber q) →
      ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω) (π : Ω → S)
        (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ),
        IsDualFrom P 𝓖 D0 q N X Y ∧ P.map π = μ ∧ MeasurableSpace.comap π inferInstance ≤ 𝓖 0 ∧
          ∀ ω, N 0 ω = q ∧ dualCoordOf q (X 0 ω) (Y 0 ω) = ofFlat q (ξ (π ω))

/-- `DelFrom 0`: the empty state, on the old-state space itself. -/
theorem delFrom_zero (D0 : ℝ) : DelFrom D0 0 := by
  intro S _ μ hμ ξ _ _
  refine ⟨S, inferInstance, topFiltration S, μ, id, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
    ⟨hμ, fun _ => ⟨measurable_const, measurable_const, measurable_const⟩,
      Eventually.of_forall fun _ => rfl, fun _ => le_rfl, fun _ => isDeletionPath_empty _ _,
      fun q hq hq0 => absurd (hq.trans hq0) (by omega)⟩, Measure.map_id,
    (MeasurableSpace.comap_id (m := (inferInstance : MeasurableSpace S))).le, fun _ => ⟨rfl, Subsingleton.elim _ _⟩⟩

/-- The flat point of an ordered interior start. -/
theorem append_mem_flatChamber {p : ℕ} {x y : Fin p → ℝ} (hxy : IsRatioParameter x y) :
    Fin.append x y ∈ flatChamber p := by
  show ofFlat p (Fin.append x y) ∈ dualChamber p
  rw [ofFlat_append]; exact hxy

/-- **`DelFrom p` gives the existence statement** at every ordered interior start. -/
theorem hasDualDeletionProcess_of_delFrom {D0 : ℝ} {p : ℕ} (h : DelFrom D0 p) (x y : Fin p → ℝ)
    (hxy : IsRatioParameter x y) : HasDualDeletionProcess D0 x y := by
  obtain ⟨Ω, m, 𝓖, P, π, N, X, Y, hD, -, -, h0⟩ := h Unit inferInstance (Measure.dirac ())
    inferInstance (fun _ => Fin.append x y) measurable_const (fun _ => append_mem_flatChamber hxy)
  refine ⟨Ω, m, 𝓖, P, N, X, Y, hD.prob, hD.adapted, Eventually.of_forall fun ω => ?_,
    Eventually.of_forall hD.paths, hD.martingale⟩
  obtain ⟨hN, hc⟩ := h0 ω
  rw [ofFlat_append] at hc
  exact ⟨hN, fun i => ⟨congrFun (congrArg Prod.fst hc) i, congrFun (congrArg Prod.snd hc) i⟩⟩

/-- **The assembly**: the gluing step `DelFrom D₀ k → DelFrom D₀ (k+1)` gives the law clauses
of the dual boundary lemma (`DualBoundaryLawStatement`). -/
theorem dualBoundaryLaw_of_delStep
    (hstep : ∀ D0 : ℝ, 0 < D0 → ∀ k : ℕ, DelFrom D0 k → DelFrom D0 (k + 1)) :
    DualBoundaryLawStatement := by
  refine dualBoundaryLaw_of_exists fun D0 hD0 p x y hxy => ?_
  have h : ∀ k, DelFrom D0 k := fun k => by
    induction k with
    | zero => exact delFrom_zero D0
    | succ k ih => exact hstep D0 hD0 k ih
  exact hasDualDeletionProcess_of_delFrom (h p) x y hxy

end BlockBand.Transmission.Dual.G
