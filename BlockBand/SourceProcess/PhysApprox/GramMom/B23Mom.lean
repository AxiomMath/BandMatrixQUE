module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMomDefs
public import BlockBand.SourceProcess.PhysApprox.B3MomTight
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability

/-!
# The cube and single-step moments `GramMomSumCube`, `GramMomSingle`

* `gramMomSumCube_of`: `GramMomSumCube` from `GramMomSumSq` (a hypothesis). Pointwise
  `η³ ≤ ε η² + η⁴ ε⁻¹` (`η ≥ 0`, `0 < ε < ∞`, in `ℝ≥0∞`), integrated on the alive set and summed
  over `nbSteps`. The `η²` sum is bounded by `GramMomSumSq` (same antecedents), the `η⁴` sum is
  `b3LindebergErr … (Sum.inl c)` (definitionally, same step set and indicator), which tends to
  `0` by `ComplexClosedLindeberg`. Splitting the lintegral of the sum uses a.e.-measurability of
  `1_A η²` (Borel alive set `b3AliveM`, `b3Alive_ae_eq`, measurability of `b3ClosedGramAt`), which
  needs `b < 1`, `-2 < E < 2` and the measurability of the eventual time-`s` frame
  (`FrameDomain`).
* `gramMomSingle_holds`: pointwise `η ≤ ε + η⁴ (ε³)⁻¹`; since `closedLaw` is a probability
  measure, `E[1_A η] ≤ ε + E[1_A η⁴]/ε³`, and a single nonnegative summand is at most the sum
  `b3LindebergErr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

namespace GM2

/-!
## Pointwise inequalities in `ℝ≥0∞`
-/

/-- `x³ ≤ ε x² + x⁴ ε⁻¹` for `0 < ε < ∞`. -/
theorem pow_three_le (x ε : ℝ≥0∞) (h0 : ε ≠ 0) (ht : ε ≠ ⊤) :
    x ^ 3 ≤ ε * x ^ 2 + x ^ 4 * ε⁻¹ := by
  rcases le_total x ε with h | h
  · calc x ^ 3 = x * x ^ 2 := by ring
      _ ≤ ε * x ^ 2 := by gcongr
      _ ≤ _ := le_self_add
  · have : x ^ 3 ≤ x ^ 4 * ε⁻¹ := by
      rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)]
      calc x ^ 3 * ε ≤ x ^ 3 * x := by gcongr
        _ = x ^ 4 := by ring
    exact this.trans le_add_self

/-- `x ≤ ε + x⁴ (ε³)⁻¹` for `0 < ε < ∞`. -/
theorem le_add_pow_four (x ε : ℝ≥0∞) (h0 : ε ≠ 0) (ht : ε ≠ ⊤) :
    x ≤ ε + x ^ 4 * (ε ^ 3)⁻¹ := by
  rcases le_total x ε with h | h
  · exact h.trans le_self_add
  · have h30 : ε ^ 3 ≠ 0 := pow_ne_zero 3 h0
    have h3t : ε ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ht
    have : x ≤ x ^ 4 * (ε ^ 3)⁻¹ := by
      rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl h30) (Or.inl h3t)]
      calc x * ε ^ 3 ≤ x * x ^ 3 := by gcongr
        _ = x ^ 4 := by ring
    exact this.trans le_add_self

/-!
## Measurability of the Gram moments on the alive set
-/

theorem measurable_b3dX_inl {np K : ℕ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W j : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    Measurable (b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np)) := by
  have h1 := (ClosedSumProof.measurable_gramEntry c).comp
    (measurable_b3ClosedGramAt b E s h τ m W (j + 1) hV)
  have h2 := (ClosedSumProof.measurable_gramEntry c).comp
    (measurable_b3ClosedGramAt b E s h τ m W j hV)
  exact h1.sub h2

theorem aemeasurable_alive_pow {np K : ℕ} {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {s h : ℝ} {τ m : Fin np → ℝ} (R : ℝ) {W : ℕ} (j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (k : ℕ) :
    AEMeasurable ((b3Alive b E s h τ m R W j Vs).indicator
      (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c) y‖ₑ ^ k)) (closedLaw b W np) := by
  have hf : Measurable fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c) y‖ₑ ^ k :=
    (measurable_b3dX_inl hV c).enorm.pow_const k
  exact ((hf.indicator (measurableSet_b3AliveM b E s h τ m R W j hV)).aemeasurable).congr
    (indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs)).symm

/-!
## The cube sum `GramMomSumCube`
-/

/-- The cube sum is at most `ε` times the square sum plus `ε⁻¹` times the Lindeberg sum. -/
theorem cube_sum_le {np K : ℕ} {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {s T h : ℝ} {τ m : Fin np → ℝ} (R : ℝ) {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (ε : ℝ≥0∞) (h0 : ε ≠ 0)
    (ht : ε ≠ ⊤) :
    ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
        (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np ≤
      ε * ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
        (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c) y‖ₑ ^ 2) y ∂closedLaw b W np +
      b3LindebergErr b E s T h τ m R W Vs (Sum.inl c) * ε⁻¹ := by
  have hLin : b3LindebergErr b E s T h τ m R W Vs (Sum.inl c) =
      ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
        (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np := rfl
  rw [hLin, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  set A := b3Alive b E s h τ m R W j Vs
  set η : ProbedPath W np × ℝ → ℝ≥0∞ := fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c) y‖ₑ
  have hpt : ∀ y, A.indicator (fun y => η y ^ 3) y ≤
      ε * A.indicator (fun y => η y ^ 2) y + A.indicator (fun y => η y ^ 4) y * ε⁻¹ := by
    intro y
    by_cases hy : y ∈ A
    · simp only [indicator_of_mem hy]
      exact pow_three_le (η y) ε h0 ht
    · simp only [indicator_of_notMem hy, mul_zero, zero_mul, add_zero, le_refl]
  calc ∫⁻ y, A.indicator (fun y => η y ^ 3) y ∂closedLaw b W np
      ≤ ∫⁻ y, (ε * A.indicator (fun y => η y ^ 2) y +
          A.indicator (fun y => η y ^ 4) y * ε⁻¹) ∂closedLaw b W np := lintegral_mono hpt
    _ = ε * ∫⁻ y, A.indicator (fun y => η y ^ 2) y ∂closedLaw b W np +
          (∫⁻ y, A.indicator (fun y => η y ^ 4) y ∂closedLaw b W np) * ε⁻¹ := by
      rw [lintegral_add_left' ((aemeasurable_alive_pow hb hE1 hE2 R j hV c 2).const_mul ε),
        lintegral_const_mul' ε _ ht, lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 h0)]

end GM2

open GM2 in

/-- **`GramMomSumCube` from `GramMomSumSq`.** -/
theorem gramMomSumCube_of (h1 : GramMomSumSq) : GramMomSumCube := by
  intro hS hL b E np τ m T s h K Vs hD R c
  obtain ⟨⟨_, hb, hE1, hE2, -⟩, -, -, -, -, hF⟩ := id hD
  have hb1 : b < 1 := by linarith
  obtain ⟨C, hC⟩ := h1 hS hL b E np τ m T s h K Vs hD R c
  have hLin := hL b E np τ m T s h K Vs hD R (Sum.inl c)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδt | hδt
  · exact Eventually.of_forall fun _ => by rw [hδt]; exact le_top
  have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ.ne').ne'
  obtain ⟨ε, hε0, hεC⟩ := ENNReal.exists_nnreal_pos_mul_lt (ENNReal.ofReal_ne_top (r := C)) hδ2
  have hε0' : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε0.ne'
  have hεpos : 0 < δ / 2 * (ε : ℝ≥0∞) := ENNReal.mul_pos hδ2 hε0'
  filter_upwards [hF, hC, (ENNReal.tendsto_nhds_zero.1 hLin) _ hεpos] with W hFW hCW hLW
  have hV : Measurable (Vs W) :=
    hFW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  refine (cube_sum_le hb1 hE1 hE2 R hV c ε hε0' ENNReal.coe_ne_top).trans ?_
  calc _ ≤ (ε : ℝ≥0∞) * ENNReal.ofReal C + δ / 2 := by
        gcongr
        exact ENNReal.div_le_of_le_mul hLW
    _ ≤ δ / 2 + δ / 2 := by gcongr
    _ = δ := ENNReal.add_halves δ

/-!
## The single-step moment `GramMomSingle`
-/

open GM2 in

/-- **`GramMomSingle`**: under `ComplexClosedLindeberg`, the first moment of one Gram increment
on the alive set, at any no-birth step, tends to `0`. -/
theorem gramMomSingle_holds : GramMomSingle := by
  intro _ hL b E np τ m T s h K Vs hD R c jW hjW
  have hLin := hL b E np τ m T s h K Vs hD R (Sum.inl c)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  rcases eq_or_ne δ ⊤ with hδt | hδt
  · exact Eventually.of_forall fun _ => by rw [hδt]; exact le_top
  set ε : ℝ≥0∞ := δ / 2 with hε
  have hε0 : ε ≠ 0 := (ENNReal.half_pos hδ.ne').ne'
  have hεt : ε ≠ ⊤ := ENNReal.div_ne_top hδt two_ne_zero
  have hεpos : 0 < ε * ε ^ 3 := ENNReal.mul_pos hε0 (pow_ne_zero 3 hε0)
  filter_upwards [hjW, (ENNReal.tendsto_nhds_zero.1 hLin) _ hεpos] with W hjW hLW
  set A := b3Alive b E s h τ m R W (jW W) (Vs W)
  set η : ProbedPath W np × ℝ → ℝ≥0∞ :=
    fun y => ‖b3dX b E s h τ m W (jW W) (Vs W) (Sum.inl c) y‖ₑ
  have hpt : ∀ y, A.indicator η y ≤ ε + A.indicator (fun y => η y ^ 4) y * (ε ^ 3)⁻¹ := by
    intro y
    by_cases hy : y ∈ A
    · simp only [indicator_of_mem hy]
      exact le_add_pow_four (η y) ε hε0 hεt
    · simp only [indicator_of_notMem hy, zero_mul, add_zero]
      exact zero_le
  have hsingle : ∫⁻ y, A.indicator (fun y => η y ^ 4) y ∂closedLaw b W np ≤
      b3LindebergErr b E s T h τ m R W (Vs W) (Sum.inl c) :=
    Finset.single_le_sum (f := fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np)
      (fun _ _ => zero_le) hjW
  calc ∫⁻ y, A.indicator η y ∂closedLaw b W np
      ≤ ∫⁻ y, (ε + A.indicator (fun y => η y ^ 4) y * (ε ^ 3)⁻¹) ∂closedLaw b W np :=
        lintegral_mono hpt
    _ = ε + (∫⁻ y, A.indicator (fun y => η y ^ 4) y ∂closedLaw b W np) * (ε ^ 3)⁻¹ := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (pow_ne_zero 3 hε0))]
    _ ≤ ε + b3LindebergErr b E s T h τ m R W (Vs W) (Sum.inl c) * (ε ^ 3)⁻¹ := by gcongr
    _ ≤ ε + ε := by
      gcongr
      exact ENNReal.div_le_of_le_mul hLW
    _ = δ := ENNReal.add_halves δ

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
