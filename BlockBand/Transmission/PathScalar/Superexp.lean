module

public import BlockBand.Transmission.PathScalar.Exit

/-!
# Superexponential exit of the near-end scalar `δ_{0,r}`

Statement (`passiveInitialScalar_superexp`): for `0 < b < 1/2`, `κ > 0`, `T`, every radius
`d > 0` there are `c > 0`, `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ`,
`P(∃ r, 1 ≤ r ≤ TW, δ_{0,r} > d) ≤ ⌊TW⌋₊ · exp(-c W log W)` under `growthPathLaw W b`.

Inputs (explicit hypotheses):
* `CentreGrowthMarginal b E` (defined here): the law of the centre-grown two-port Schur matrix
  `grownSchur E · L` under `growthLaw W r₀ L b` is the law of `pathSchur E` under
  `pathLaw W (r₀ + 2L) b` (at each fixed length the centre-grown path consists of the same
  independent Gaussian blocks and bonds). It is the centre-growth analogue of the near-end bridge
  `growthPathLaw_map_pathAt`, taken here as a hypothesis and proved for `b < 1/2` by
  `centreGrowthMarginal_holds`; the unconditional form is
  `passiveInitialScalar_superexp_of_scalarRecursion`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge
open scoped ENNReal NNReal Matrix

variable {W : ℕ}

/-!
## Measurability of the centre-grown Schur matrix
-/

theorem measurable_blockDiag {α : Type*} [MeasurableSpace α] {k : ℕ}
    {A : α → Fin k → Matrix (Fin W) (Fin W) ℂ} (hA : Measurable A) :
    Measurable fun x => BlockBand.Internal.Contracts.Layers.blockDiag (A x) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [BlockBand.Internal.Contracts.Layers.blockDiag]
  split_ifs
  · exact Matrix.measurable_apply.comp (measurable_pi_apply _ |>.comp hA)
  · exact measurable_const

theorem measurable_bondMatrix {α : Type*} [MeasurableSpace α] (σ : LayerShape)
    {B : α → Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ} (hB : Measurable B) :
    Measurable fun x => bondMatrix σ (B x) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [bondMatrix]
  split_ifs
  · exact Matrix.measurable_apply.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hB))
  · exact measurable_const

theorem measurable_layerSchur {α : Type*} [MeasurableSpace α] (σ : LayerShape) (E : ℝ)
    {X : α → Matrix (PhysSite W σ) (PhysSite W σ) ℂ} {ω : α → LayerSample W σ}
    (hX : Measurable X) (hω : Measurable ω) :
    Measurable fun x => layerSchur σ E (X x) (ω x) := by
  have hB := measurable_bondMatrix σ (measurable_snd.comp hω)
  have hP : Measurable fun x => BlockBand.Internal.Contracts.Layers.blockDiag (ω x).1 - (E : ℂ) • 1 - X x := by
    refine Measurable.of_eval_matrix _ fun i j => ?_
    simp only [Matrix.sub_apply]
    exact ((measurable_blockDiag (measurable_fst.comp hω)).eval_matrix.sub measurable_const).sub
      hX.eval_matrix
  exact measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hB)
    (measurable_matrix_inv.comp hP)) hB

theorem measurable_grownSchur (E : ℝ) (r₀ L k : ℕ) :
    Measurable fun ω : GrowthSample W r₀ L => grownSchur E ω k := by
  induction k with
  | zero => exact (measurable_pathSchur E r₀).comp measurable_fst
  | succ k ih =>
    by_cases h : k < L
    · simp only [grownSchur, h, dite_true]
      exact measurable_layerSchur .separate E ih ((measurable_pi_apply _).comp measurable_snd)
    · simpa only [grownSchur, h, dite_false] using ih

theorem measurable_matchedDistance (b E : ℝ) :
    Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => matchedDistance b E X := by
  have hR : Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ := by
    refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
    simp only [Matrix.sub_apply]
    exact measurable_const.sub (measurable_id.eval_matrix)
  have ht : ∀ j : Fin 2, Measurable fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      ‖blockTrace ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) j -
        matchedA E‖ := fun j => by
    simp only [blockTrace]
    exact ((measurable_const.mul (Finset.measurable_sum _ fun a _ => hR.eval_matrix)).sub
      measurable_const).norm
  exact (ht 0).max (ht 1)

/-!
## The centre-growth marginal identity (hypothesis)
-/

/-- **Centre-growth marginal identity**: for
`W ≥ 1`, cores `r₀ ∈ {1,2}` and every `L`, the two-port Schur matrix of the centre-grown path
after `L` layers has the law of the two-port Schur matrix of the path of length
`r₀ + 2L`.
Both maps are measurable (`measurable_grownSchur`, `measurable_pathSchur`), so the
pushforwards are laws.
Proved for `b < 1/2` as `centreGrowthMarginal_holds`.
-/
def CentreGrowthMarginal (b E : ℝ) : Prop :=
  ∀ W : ℕ, 0 < W → ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ,
    (growthLaw W r₀ L b).map (fun ω => grownSchur E ω L) =
      (pathLaw W (r₀ + 2 * L) b).map (pathSchur E)

/-- `δ_{0,r} ≤ d(𝕏_r)`: the near-port distance is the first component of `matchedDistance`. -/
theorem nearPortDistance_le_matchedDistance (b E : ℝ) {r : ℕ} (p : PathSample W r) :
    nearPortDistance b E p ≤ matchedDistance b E (pathSchur E p) :=
  le_max_left _ _

/-- One length: `P(d < δ_{0,r}) = pathLaw W r b (d < near-port distance)` (`r ≥ 1`). -/
theorem growth_jetDistance0_gt_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {r : ℕ}
    (hr : 1 ≤ r) (d : ℝ) :
    growthPathLaw W b {ω | d < jetDistance0 b E (pathX b E W r ω)} =
      pathLaw W r b {p | d < nearPortDistance b E p} := by
  have hS : MeasurableSet {p : PathSample W r | d < nearPortDistance b E p} :=
    measurableSet_lt measurable_const (measurable_nearPortDistance b E r)
  rw [← growthPathLaw_map_pathAt W b hr, Measure.map_apply (measurable_pathAt W r) hS]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2] with ω h
  simp only [Set.mem_preimage, jetDistance0_pathX_eq h r]
  rfl

/-- Parity split `r = r₀ + 2L`, `r₀ ∈ {1, 2}`, for `r ≥ 1`. -/
theorem exists_core_split {r : ℕ} (hr : 1 ≤ r) :
    ∃ r₀ L : ℕ, (r₀ = 1 ∨ r₀ = 2) ∧ r = r₀ + 2 * L := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' r
  · exact ⟨2, k - 1, Or.inr rfl, by omega⟩
  · exact ⟨1, k, Or.inl rfl, by omega⟩

/-- **Superexponential exit** of the near-end scalar along all lengths `r ≤ TW`, from
`ScalarRecursionContract` and the centre-growth marginal identity `CentreGrowthMarginal`. -/
theorem passiveInitialScalar_superexp (hSR : ScalarRecursionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
      (∀ E ∈ bulkInterval κ, CentreGrowthMarginal b E) →
      ∀ d : ℝ, 0 < d → ∃ (c : ℝ) (W₀ : ℕ), 0 < c ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
          d < jetDistance0 b E (pathX b E W r ω)} ≤
          ENNReal.ofReal ((⌊T * W⌋₊ : ℝ) * Real.exp (-(c * W * Real.log W))) := by
  intro b hb hb' κ T hκ hCG d hd
  obtain ⟨d₀, hd₀, hexit⟩ := hSR.exit b hb hb' κ T hκ
  obtain ⟨c, W₁, hc, hW₁⟩ := hexit (min d d₀) (lt_min hd hd₀) (min_le_right _ _)
  refine ⟨c, max W₁ 1, hc, fun W hW E hE => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW0 : 0 < W := by have := le_max_right W₁ 1; omega
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  refine union_lengths_le (growthPathLaw W b)
    (fun r => {ω | d < jetDistance0 b E (pathX b E W r ω)}) fun r hr hrT => ?_
  obtain ⟨r₀, L, hr₀, rfl⟩ := exists_core_split hr
  have hSm : MeasurableSet {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ |
      min d d₀ < matchedDistance b E X} :=
    measurableSet_lt measurable_const (measurable_matchedDistance b E)
  have h1 : pathLaw W (r₀ + 2 * L) b {p | d < nearPortDistance b E p} ≤
      pathLaw W (r₀ + 2 * L) b {p | min d d₀ < matchedDistance b E (pathSchur E p)} :=
    measure_mono fun p hp => lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le hp (nearPortDistance_le_matchedDistance b E p))
  have h2 : pathLaw W (r₀ + 2 * L) b {p | min d d₀ < matchedDistance b E (pathSchur E p)} =
      growthLaw W r₀ L b {ω | min d d₀ < matchedDistance b E (grownSchur E ω L)} := by
    have := congrArg (fun μ : Measure (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =>
      μ {X | min d d₀ < matchedDistance b E X}) (hCG E hE W hW0 r₀ hr₀ L)
    rw [Measure.map_apply (measurable_grownSchur E r₀ L L) hSm,
      Measure.map_apply (measurable_pathSchur E _) hSm] at this
    exact this.symm
  have h3 : growthLaw W r₀ L b {ω | min d d₀ < matchedDistance b E (grownSchur E ω L)} ≤
      growthLaw W r₀ L b {ω | ∃ k ≤ L, min d d₀ < matchedDistance b E (grownSchur E ω k)} :=
    measure_mono fun ω hω => ⟨L, le_rfl, hω⟩
  rw [growth_jetDistance0_gt_eq (by linarith) hE1 hE2 hr]
  exact h1.trans (h2.le.trans (h3.trans
    (hW₁ W hW1 hW0 r₀ hr₀ L (by exact_mod_cast hrT) E hE)))

end BlockBand.Transmission.PathScalar
