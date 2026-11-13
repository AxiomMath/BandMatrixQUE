module

public import BlockBand.Transmission.DualBoundary.Coupling
public import BlockBand.SourceProcess.Stochastic.Uniqueness.BrownianLaw
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Uniqueness at a boundary start: reduction to Lipschitz tests of the `Z̄` path

Setting: one-pair boundary realizations `IsBoundaryDualProcess P 𝓖 D₀ ![x] ![y] N X Y` (any
filtered probability space) with `x + y > 0`.
* `zbarTr N X Y ω t = (X̄_t 0, Ȳ_t 0)`: the read-out `Z̄_t` of the truncated state.
* `psiState`: `0 ↦` the empty state, `z ≠ 0 ↦` the level-one state at `z`.
* **`ae_truncDualState_eq_psi`**: a.s. `truncDualState = psiState ∘ Z̄` at every time (on level
  one `Z̄_t ≠ 0`: at `t = 0` because `x + y > 0`, at `t > 0` by the chamber condition).
* **`ext_of_forall_lipschitz`**: finite Borel measures on a pseudo-metric space agreeing on all
  `[0,1]`-valued Lipschitz functions agree (thickened indicators of closed sets).
* **`map_trunc_eq_of_tests`**: if the `[0,1]`-valued Lipschitz tests of the restrictions of
  `Z̄` to every finite time set have the same expectations for two realizations, the laws of
  their truncated state paths agree (`map_eq_of_fdd_eq₂'`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- The read-out path `t ↦ Z̄_t` of the truncated state. -/
def zbarTr {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) :
    ℝ≥0 → Fin 2 → ℝ :=
  zbarPath (truncDualState N X Y ω)

open scoped Classical in
/-- The state with read-out `z` (empty for `z = 0`, level one otherwise). -/
def psiState (z : Fin 2 → ℝ) : DualState :=
  if z = 0 then ((0 : ℕ), (0 : ℕ → ℝ), (0 : ℕ → ℝ)) else startState z

theorem measurable_psiState : Measurable psiState :=
  Measurable.ite (measurableSet_singleton (0 : Fin 2 → ℝ)) measurable_const measurable_startState

/-- The state path with read-out path `z`. -/
def psiPath (z : ℝ≥0 → Fin 2 → ℝ) : DPath := fun t => psiState (z t)

theorem measurable_psiPath : Measurable psiPath :=
  measurable_pi_iff.2 fun t => measurable_psiState.comp (measurable_pi_apply t)

theorem zbarTr_apply {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω)
    (t : ℝ≥0) :
    zbarTr N X Y ω t = ![truncDualCoord (N t ω) (X t ω) 0, truncDualCoord (N t ω) (Y t ω) 0] :=
  rfl

section Real

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

omit m in
/-- At a positive time of level one the `x`-coordinate is positive (chamber condition). -/
theorem chamber_one {ω : Ω}
    (hP : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    {t : ℝ≥0} (ht : 0 < t) (h1 : N t ω = 1) :
    0 < X t ω 0 ∧ 0 < Y t ω 0 ∧ Y t ω 0 < 1 := by
  have hc := hP.chamber t ht
  rw [h1] at hc
  exact ⟨by simpa [dualCoordOf] using hc.2.2.1 0, by simpa [dualCoordOf] using (hc.2.2.2 0).1,
    by simpa [dualCoordOf] using (hc.2.2.2 0).2⟩

omit m in
/-- **Pathwise: the truncated state is `psiState` of its read-out.** -/
theorem truncDualState_eq_psi {ω : Ω}
    (hP : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) (hz0 : X 0 ω 0 ≠ 0 ∨ Y 0 ω 0 ≠ 0) (t : ℝ≥0) :
    truncDualState N X Y ω t = psiState (zbarTr N X Y ω t) := by
  rcases level_eq_one_or_zero hP h0 t with ht | ht
  · have hz : zbarTr N X Y ω t = ![X t ω 0, Y t ω 0] := by
      rw [zbarTr_apply, ht]; simp [truncDualCoord]
    have hne : (![X t ω 0, Y t ω 0] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      have h0' := congrFun h 0
      have h1' := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0' h1'
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
      · subst h; rcases hz0 with h | h <;> contradiction
      · linarith [(chamber_one hP h ht).1]
    simp only [hz, psiState, hne, ↓reduceIte]
    simp only [truncDualState, startState, ht]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext i <;>
      by_cases hi : i = 0 <;> simp [truncDualCoord, truncCoord, hi]
  · have hz : zbarTr N X Y ω t = 0 := by
      rw [zbarTr_apply, ht]; funext i; fin_cases i <;> simp [truncDualCoord]
    simp only [hz, psiState, ↓reduceIte]
    simp only [truncDualState, ht]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext i <;> simp [truncDualCoord]

/-- **A.s. the truncated state path is `psiPath` of the read-out path.** -/
theorem ae_truncDualState_eq_psi (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (hxy : 0 < x + y) :
    ∀ᵐ ω ∂P, truncDualState N X Y ω = psiPath (zbarTr N X Y ω) := by
  filter_upwards [h.start, h.paths] with ω hs hp
  have hX : X 0 ω 0 = x := by simpa using (hs.2 0).1
  have hY : Y 0 ω 0 = y := by simpa using (hs.2 0).2
  have hz0 : X 0 ω 0 ≠ 0 ∨ Y 0 ω 0 ≠ 0 := by
    by_contra hc; push Not at hc; linarith [hc.1 ▸ hX, hc.2 ▸ hY]
  have h0 : N 0 ω = 1 := by simpa using hs.1
  funext t
  exact truncDualState_eq_psi hp h0 hz0 t

theorem measurable_zbarTr (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    Measurable (zbarTr N X Y) :=
  measurable_zbarPath.comp (measurable_truncDualState h)

end Real

/-- **Law determination by `[0,1]`-valued Lipschitz tests.** -/
theorem ext_of_forall_lipschitz {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [BorelSpace α] {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : α → ℝ, (∃ L, LipschitzWith L g) → (∀ a, 0 ≤ g a ∧ g a ≤ 1) →
      ∫ a, g a ∂μ = ∫ a, g a ∂ν) : μ = ν := by
  have key : ∀ F : Set α, IsClosed F → μ F = ν F := fun F hF => by
    have hδ : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := fun _ => Nat.one_div_pos_of_nat
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed μ hF hδ
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ν hF hδ
      tendsto_one_div_add_atTop_nhds_zero_nat
    have he : ∀ n, (∫⁻ a, (thickenedIndicator (hδ n) F a : ℝ≥0∞) ∂μ) =
        ∫⁻ a, (thickenedIndicator (hδ n) F a : ℝ≥0∞) ∂ν := fun n => by
      rw [lintegral_coe_eq_integral _ (integrable_thickenedIndicator F (hδ n)),
        lintegral_coe_eq_integral _ (integrable_thickenedIndicator F (hδ n))]
      congr 1
      refine h _ ⟨(1 / ((n : ℝ) + 1)).toNNReal⁻¹, ?_⟩ fun a => ⟨NNReal.coe_nonneg _, ?_⟩
      · refine LipschitzWith.of_dist_le_mul fun a b => ?_
        have := (lipschitzWith_thickenedIndicator (hδ n) F).dist_le_mul a b
        rw [Real.dist_eq]; simpa [NNReal.dist_eq] using this
      · exact_mod_cast thickenedIndicator_le_one (hδ n) F a
    simp_rw [he] at h1
    exact tendsto_nhds_unique h1 h2
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun F hF => key F hF)
    (key _ isClosed_univ)
  rw [BorelSpace.measurable_eq (α := α), borel_eq_generateFrom_isClosed]

section Two

variable {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
  {P₂ : Measure Ω₂} {𝓖₁ : Filtration ℝ≥0 m₁} {𝓖₂ : Filtration ℝ≥0 m₂} {D0 : ℝ} {x y : ℝ}
  {N₁ : ℝ≥0 → Ω₁ → ℕ} {X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ} {N₂ : ℝ≥0 → Ω₂ → ℕ}
  {X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ}

/-- **`unique` from Lipschitz tests of the finite-dimensional read-outs.** -/
theorem map_trunc_eq_of_tests (h₁ : IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁)
    (h₂ : IsBoundaryDualProcess P₂ 𝓖₂ D0 ![x] ![y] N₂ X₂ Y₂) (hxy : 0 < x + y)
    (htest : ∀ (I : Finset ℝ≥0) (g : (I → Fin 2 → ℝ) → ℝ), (∃ L, LipschitzWith L g) →
      (∀ a, 0 ≤ g a ∧ g a ≤ 1) →
      ∫ ω, g (I.restrict (zbarTr N₁ X₁ Y₁ ω)) ∂P₁ = ∫ ω, g (I.restrict (zbarTr N₂ X₂ Y₂ ω)) ∂P₂) :
    P₁.map (truncDualState N₁ X₁ Y₁) = P₂.map (truncDualState N₂ X₂ Y₂) := by
  have := h₁.prob
  have := h₂.prob
  have hm₁ := measurable_zbarTr h₁
  have hm₂ := measurable_zbarTr h₂
  have hZ : P₁.map (zbarTr N₁ X₁ Y₁) = P₂.map (zbarTr N₂ X₂ Y₂) := by
    refine BlockBand.SourceProcess.Stochastic.Uniqueness.map_eq_of_fdd_eq₂' (X := fun _ : ℝ≥0 => Fin 2 → ℝ) hm₁.aemeasurable
      hm₂.aemeasurable fun I => ?_
    have hr₁ : Measurable fun ω => I.restrict (zbarTr N₁ X₁ Y₁ ω) :=
      (Finset.measurable_restrict I).comp hm₁
    have hr₂ : Measurable fun ω => I.restrict (zbarTr N₂ X₂ Y₂ ω) :=
      (Finset.measurable_restrict I).comp hm₂
    refine ext_of_forall_lipschitz fun g hg h01 => ?_
    obtain ⟨L, hL⟩ := hg
    have hgm : Measurable g := hL.continuous.measurable
    rw [integral_map hr₁.aemeasurable hgm.aestronglyMeasurable,
      integral_map hr₂.aemeasurable hgm.aestronglyMeasurable]
    exact htest I g ⟨L, hL⟩ h01
  rw [Measure.map_congr (ae_truncDualState_eq_psi h₁ hxy),
    Measure.map_congr (ae_truncDualState_eq_psi h₂ hxy)]
  have e₁ : (fun ω => psiPath (zbarTr N₁ X₁ Y₁ ω)) = psiPath ∘ zbarTr N₁ X₁ Y₁ := rfl
  have e₂ : (fun ω => psiPath (zbarTr N₂ X₂ Y₂ ω)) = psiPath ∘ zbarTr N₂ X₂ Y₂ := rfl
  rw [e₁, e₂, ← Measure.map_map measurable_psiPath hm₁, ← Measure.map_map measurable_psiPath hm₂,
    hZ]

end Two

end BlockBand.Transmission.DualBoundary
