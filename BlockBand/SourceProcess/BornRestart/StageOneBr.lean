module

public import BlockBand.SourceProcess.BornRestart.StageOne

/-!
# Stage one for the compensated products, and the restart value `C_e(a)`

Setting of `StageOne`. `C_e(a)` and the
products at `a` are not bounded, so they are cut off on the `𝓖₀`-event `{a ≤ k}`
(`rsInd`).

* `exists_rs_cross`: an `𝓗₀`-measurable, a.e. bounded version of `1{a ≤ k} C_e(a ∧ θ_k)`. It is
  the value at `u = 0` of a restarted martingale.
* `exists_rs_bracket`: an `𝓗`-martingale modification of
  `1{a ≤ k} (P((a + u) ∧ θ_k) - P(a ∧ θ_k))`, where `P = pBr` is the compensated product of `G`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ}
  {j : F → GramState c} {α : (F → ℝ) → ℝ≥0} {Ω : Type} {m : MeasurableSpace Ω}
  {𝓖 : Filtration ℝ≥0 m} {Q : Measure Ω} [IsProbabilityMeasure Q] {β : Ω → F → ℝ}
  {G : ℝ≥0 → Ω → GramState c}

/-- The cutoff `1{a ≤ k}`. -/
def rsInd (α : (F → ℝ) → ℝ≥0) (β : Ω → F → ℝ) (k : ℕ) (ω : Ω) : ℂ :=
  if α (β ω) ≤ (k : ℝ≥0) then 1 else 0

omit [Fintype F] in
theorem stronglyMeasurable_rsInd (hα : Measurable α) (hβ : Measurable[𝓖 0] β) (k : ℕ) :
    StronglyMeasurable[𝓖 0] (rsInd α β k) :=
  StronglyMeasurable.ite (measurableSet_le (measurable_rsTime hα hβ) measurable_const)
    stronglyMeasurable_const stronglyMeasurable_const

omit [Fintype F] in
theorem norm_rsInd_le (k : ℕ) (ω : Ω) : ‖rsInd α β k ω‖ ≤ 1 := by
  unfold rsInd; split_ifs <;> simp

/-- **The restart value `C_e(a)`, cut off and `𝓗₀`-measurable.** -/
theorem exists_rs_cross (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    (e : Fin 2 × c × c) (k : ℕ) :
    ∃ ζ : Ω → ℂ, StronglyMeasurable[rsFil hα hβ 0] ζ ∧ (∃ C, ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) ∧
      ∀ᵐ ω ∂Q, ζ ω = rsInd α β k ω *
        pComp D0 D j (fun t => G t ω) (β ω) e (stopTime (locStop j G β k ω) (α (β ω))) := by
  have ha := measurable_rsTime hα hβ
  have hθ := isStoppingTime_locStop' hG k
  obtain ⟨M1, hM1, hM1X⟩ := exists_mart_locStop hG k (hG.drift (locLevel j k) e)
    (continuous_bornCompensated_ae hG e) hθ fun _ => le_rfl
  obtain ⟨C, hC0, hC⟩ := exists_pComp_stop_bound (D0 := D0) (D := D) (j := j) e k
  have hbd : ∀ (ω : Ω), Continuous (fun t => G t ω - birthSum j (β ω) (t : ℝ)) →
      ∀ (T r : ℝ≥0), r ≤ α (β ω) + T → ‖rsInd α β k ω *
        pComp D0 D j (fun t => G t ω) (β ω) e (stopTime (locStop j G β k ω) r)‖ ≤
          C * (1 + k + T) := fun ω hc T r hr => by
    unfold rsInd
    split_ifs with h
    · rw [one_mul]
      refine (hC _ _ _ r hc fun s hs => norm_le_of_lt_locStop hc hs).trans ?_
      have h1 : (r : ℝ) ≤ α (β ω) + T := by exact_mod_cast hr
      have h2 : ((α (β ω) : ℝ≥0) : ℝ) ≤ k := by exact_mod_cast h
      exact mul_le_mul_of_nonneg_left (by linarith) hC0
    · rw [zero_mul, norm_zero]; positivity
  obtain ⟨N, hN, hNX⟩ := exists_martingale_restart (ha := ha)
    (martingale_const_mul (𝓗 := 𝓖) hM1 (stronglyMeasurable_rsInd hα hβ k)
      (ae_of_all _ (norm_rsInd_le k)))
    (X := fun t ω => rsInd α β k ω *
      stoppedProcess (bornCompensated D0 D G (fun t ω => birthSum j (β ω) (t : ℝ)) e)
        (locStop j G β k) t ω)
    (fun t => by
      filter_upwards [hM1X t] with ω h1
      simp only [h1])
    (by
      filter_upwards [continuous_bornCompensated_ae hG e] with ω hc
      exact continuous_const.mul (hc.comp (continuous_stopTime _)))
    (fun u => ⟨C * (1 + k + (u + 1)), by
      filter_upwards [hG.continuous] with ω hc v hv
      exact hbd ω hc (u + 1) _ (add_le_add le_rfl hv)⟩)
  refine ⟨N 0, hN.1 0, ⟨C * (1 + k + 0), ?_⟩, ?_⟩
  · filter_upwards [hNX 0, hG.continuous] with ω h hc
    rw [h]
    exact hbd ω hc 0 _ le_rfl
  · filter_upwards [hNX 0] with ω h
    rw [h, add_zero]
    rfl

/-- **Stage one, compensated products** (cut off at `{a ≤ k}`). -/
theorem exists_rs_bracket (hα : Measurable α) (hβ : Measurable[𝓖 0] β)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t ω => birthSum j (β ω) (t : ℝ)) G)
    (e e' : Fin 2 × c × c) (k : ℕ) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (rsFil hα hβ) Q ∧ ∀ u, N u =ᵐ[Q] fun ω =>
      rsInd α β k ω * (pBr D0 D j (fun t => G t ω) (β ω) e e'
          (stopTime (locStop j G β k ω) (α (β ω) + u)) -
        pBr D0 D j (fun t => G t ω) (β ω) e e' (stopTime (locStop j G β k ω) (α (β ω)))) := by
  have ha := measurable_rsTime hα hβ
  have hθ := isStoppingTime_locStop' hG k
  have hXc : ∀ᵐ ω ∂Q, Continuous fun t => pBr D0 D j (fun t => G t ω) (β ω) e e' t := by
    filter_upwards [hG.continuous] with ω hc
    exact continuous_pBr hc e e'
  obtain ⟨M1, hM1, hM1X⟩ := exists_mart_locStop
    (X := fun t ω => pBr D0 D j (fun t => G t ω) (β ω) e e' t) hG k
    (hG.bracket (locLevel j k) e e') hXc hθ fun _ => le_rfl
  obtain ⟨M2, hM2, hM2X⟩ := exists_mart_locStop
    (X := fun t ω => pBr D0 D j (fun t => G t ω) (β ω) e e' t) hG k
    (hG.bracket (locLevel j k) e e') hXc ((isStoppingTime_of_zero ha).min hθ)
    fun _ => min_le_right _ _
  obtain ⟨C, hC0, hC⟩ := exists_pBr_stop_bound (D0 := D0) (D := D) (j := j) e e' k
  obtain ⟨N, hN, hNX⟩ := exists_martingale_restart (ha := ha)
    (martingale_const_mul (𝓗 := 𝓖) (hM1.sub hM2) (stronglyMeasurable_rsInd hα hβ k)
      (ae_of_all _ (norm_rsInd_le k)))
    (X := fun t ω => rsInd α β k ω *
      (pBr D0 D j (fun t => G t ω) (β ω) e e' (stopTime (locStop j G β k ω) t) -
        pBr D0 D j (fun t => G t ω) (β ω) e e'
          (stopTime (min ((α (β ω) : ℝ≥0) : WithTop ℝ≥0) (locStop j G β k ω)) t)))
    (fun t => by
      filter_upwards [hM1X t, hM2X t] with ω h1 h2
      simp only [Pi.sub_apply, h1, h2, stoppedProcess_eq_stopTime])
    (by
      filter_upwards [hXc] with ω hc
      exact continuous_const.mul ((hc.comp (continuous_stopTime _)).sub
        (hc.comp (continuous_stopTime _))))
    (fun u => ⟨2 * (C * (2 + k + u) ^ 2), by
      filter_upwards [hG.continuous] with ω hc v hv
      simp only [stopTime_min_coe]
      unfold rsInd
      split_ifs with h
      · rw [one_mul]
        have h1 : (v : ℝ) ≤ u + 1 := by exact_mod_cast hv
        have h2 : ((α (β ω) : ℝ≥0) : ℝ) ≤ k := by exact_mod_cast h
        have hb1 := hC _ _ _ (α (β ω) + v) hc fun s hs => norm_le_of_lt_locStop hc hs
        have hb2 := hC _ _ _ (α (β ω)) hc fun s hs => norm_le_of_lt_locStop hc hs
        have hu : (0 : ℝ) ≤ u := u.coe_nonneg
        have ha0 : (0 : ℝ) ≤ α (β ω) := (α (β ω)).coe_nonneg
        have hv0 : (0 : ℝ) ≤ v := v.coe_nonneg
        push_cast at hb1
        have e1 : (1 + ((α (β ω) : ℝ) + v)) ^ 2 ≤ (2 + k + u) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        have e2 : (1 + (α (β ω) : ℝ)) ^ 2 ≤ (2 + k + u) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        refine (norm_sub_le _ _).trans ?_
        nlinarith [mul_le_mul_of_nonneg_left e1 hC0, mul_le_mul_of_nonneg_left e2 hC0]
      · rw [zero_mul, norm_zero]; positivity⟩)
  refine ⟨N, hN, fun u => ?_⟩
  filter_upwards [hNX u] with ω h
  rw [h]
  simp only [stopTime_min_coe]

end BlockBand.SourceProcess.BornRestart
