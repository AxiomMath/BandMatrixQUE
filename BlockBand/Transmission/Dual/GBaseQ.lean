module

public import BlockBand.Transmission.Dual.GLayout
public import BlockBand.Transmission.Dual.GPairBase
public import BlockBand.Transmission.Dual.GProductMP

/-!
# The product base process `P⁰` at every level

`IsBaseSol D₀ q P 𝓖 Z z`: `Z` solves the flat base martingale problem
`(flatBaseDrift D₀ q, flatDiff D₀ q)` on all of `ℝ^{q+q}`, starts at `z` a.s., and stays in
the open orthant `O_q = (0,∞)^q × (0,1)^q`; its paths are continuous and start at `z` at every `ω`.
* `IsBaseSol.slot`: a pair solution and a level-`q` solution give, on the product space with the
  product filtration, a level-`(q+1)` solution, with the pair in the slots `(x₀, y_j)`
  (`isMPSolutionOn_prod`, `isMPSolutionOn_reindex`, `reindexDrift_slot_base`,
  `reindexDiff_slot_base`). This is the grouping `P⁰ = P⁰_pair ⊗ P⁰_rest`.
* `isBaseSol_pair`: the pair base of `GPairBase` (`Exists.Ω₁`).
* **`exists_baseSol`**: for `D₀ > 0`, every `z ∈ O_q` and every `q`, a base solution exists on a
  probability space in `Type` (induction on `q`, pair in the slot `(x₀, y₀)`).
* `IsBaseSol.chamber`: restricted to the flat chamber, the hypothesis of `GLemma1Mart`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Levy BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ}

/-- `Z` is a flat base solution of level `q` from `z`. -/
structure IsBaseSol (D0 : ℝ) (q : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Z : ℝ≥0 → Ω → Fin (q + q) → ℝ)
    (z : Fin (q + q) → ℝ) : Prop where
  sol : IsMPSolutionOn P 𝓖 (flatBaseDrift D0 q) (flatDiff D0 q) univ Z
  start : ∀ ω, Z 0 ω = z
  cont : ∀ ω, Continuous fun t => Z t ω
  mem : ∀ t ω, Z t ω ∈ flatO q

/-- The level-`(q+1)` path with the pair in the slots `(x₀, y_j)`. -/
def slotPath {Ω₁ Ω₂ : Type*} (j : Fin (q + 1)) (Y₁ : ℝ≥0 → Ω₁ → Fin (1 + 1) → ℝ)
    (Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ) : ℝ≥0 → Ω₁ × Ω₂ → Fin ((q + 1) + (q + 1)) → ℝ :=
  fun t x => prodPath Y₁ Y₂ t x ∘ slotEquiv j

theorem reindexDomain_univ {d₁ d₂ d' : ℕ} (e : Fin d' ≃ Fin (d₁ + d₂)) :
    reindexDomain e (prodDomain (univ : Set (Fin d₁ → ℝ)) (univ : Set (Fin d₂ → ℝ))) = univ := by
  ext; simp only [reindexDomain, prodDomain, mem_univ, and_self, ofPred_true]

/-- **Grouping**: a pair solution and a level-`q` solution give a level-`(q+1)` solution. -/
theorem IsBaseSol.slot {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {Y₁ : ℝ≥0 → Ω₁ → Fin (1 + 1) → ℝ} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
    {p : Fin (1 + 1) → ℝ} {r : Fin (q + q) → ℝ} (h₁ : IsBaseSol D0 1 Q₁ 𝓖₁ Y₁ p)
    (h₂ : IsBaseSol D0 q Q₂ 𝓖₂ Y₂ r) (j : Fin (q + 1)) :
    IsBaseSol D0 (q + 1) (Q₁.prod Q₂) (prodFiltration 𝓖₁ 𝓖₂) (slotPath j Y₁ Y₂)
      (Fin.append p r ∘ slotEquiv j) := by
  have H := isMPSolutionOn_reindex (slotEquiv j) (isMPSolutionOn_prod h₁.sol h₂.sol isOpen_univ
    isOpen_univ (continuous_flatBaseDrift D0).continuousOn
    (contDiff_flatDiff D0).continuous.continuousOn (continuous_flatBaseDrift D0).continuousOn
    (contDiff_flatDiff D0).continuous.continuousOn)
  rw [reindexDrift_slot_base, reindexDiff_slot_base, reindexDomain_univ] at H
  refine ⟨H, fun x => ?_, fun x => ?_, fun t x => append_comp_mem_flatO (h₁.mem t x.1)
    (h₂.mem t x.2) j⟩
  · simp only [slotPath, prodPath, h₁.start, h₂.start]
  · have hc : Continuous fun t => prodPath Y₁ Y₂ t x := by
      refine continuous_pi fun k => Fin.addCases (fun i => ?_) (fun i => ?_) k
      · simp only [prodPath, Fin.append_left]; exact (continuous_apply i).comp (h₁.cont x.1)
      · simp only [prodPath, Fin.append_right]; exact (continuous_apply i).comp (h₂.cont x.2)
    exact (reindexHomeo (slotEquiv j)).continuous.comp hc

/-- The pair base of `GPairBase` is a level-one base solution. -/
theorem isBaseSol_pair (hD0 : 0 < D0) {z : Fin 2 → ℝ} (hz : z ∈ flatO 1) {X : ℝ≥0 → Ω₁ → Fin 2 → ℝ}
    (hX : IsSDESolution μ₁ (uvBaseDrift D0) (uvDiff D0) (fun _ => fromFlat z) X) :
    IsBaseSol D0 1 P₁ 𝓖₁ (pairPath z X) z :=
  ⟨isMPSolutionOn_pairPath hD0 hX, pairPath_zero (hz 0) (hz 1).1 (hz 1).2, continuous_pairPath,
    fun _ _ => flatChamber_subset_flatO 1 (toFlat_mem _)⟩

/-- The constant filtration. -/
def constFiltration (Ω : Type*) [MeasurableSpace Ω] :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

theorem isBaseSol_zero {z : Fin (0 + 0) → ℝ} (hz : z ∈ flatO 0) :
    IsBaseSol D0 0 (Measure.dirac ()) (constFiltration Unit) (fun _ _ => z) z := by
  refine ⟨⟨fun _ => stronglyMeasurable_const, Eventually.of_forall fun _ => continuous_const,
    fun _ _ i => (Nat.not_lt_zero _ i.2).elim, fun _ _ i => (Nat.not_lt_zero _ i.2).elim⟩,
    fun _ => rfl, fun _ => continuous_const, fun _ _ => hz⟩

/-- **Existence of the base process** at every level, from every point of `O_q`. -/
theorem exists_baseSol (hD0 : 0 < D0) : ∀ (q : ℕ) (z : Fin (q + q) → ℝ), z ∈ flatO q →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Z : ℝ≥0 → Ω → Fin (q + q) → ℝ),
      IsBaseSol D0 q P 𝓖 Z z
  | 0, z, hz => ⟨Unit, inferInstance, _, inferInstance, _, _, isBaseSol_zero hz⟩
  | q + 1, z, hz => by
    obtain ⟨Ω, _, P, _, 𝓖, Z, hZ⟩ :=
      exists_baseSol hD0 q (rightPart (z ∘ slot 0)) (rightPart_mem_flatO hz 0)
    have hp := leftPart_mem_flatO hz 0
    obtain ⟨X, hX⟩ := exists_pairBase_sde hD0 (leftPart (z ∘ slot 0))
    have H := (isBaseSol_pair hD0 hp hX).slot hZ 0
    rw [append_slot_comp] at H
    exact ⟨Ω₁ × Ω, inferInstance, _, inferInstance, _, _, H⟩

/-- On the flat chamber: the hypothesis of `GLemma1Mart`. -/
theorem IsBaseSol.chamber {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
    {z : Fin (q + q) → ℝ} (h : IsBaseSol D0 q P 𝓖 Z z) :
    IsMPSolutionOn P 𝓖 (flatBaseDrift D0 q) (flatDiff D0 q) (flatChamber q) Z :=
  isMPSolutionOn_mono h.sol (subset_univ _)

end BlockBand.Transmission.Dual.G
