module

public import BlockBand.SourceProcess.ComplexUnique.BridgeLoc

/-!
# The restarted real martingale problem

`isMPSolutionOn_rsY`, proved in the sibling module `BridgeMain`: let `X + c` solve a localized complex martingale problem
(`IsCLocSol`, deterministic jumps `c`, measurable and bounded) and let `c` be constant on
`[a, a + h)`. Then the restarted real process `rsY X c a h : u ↦ (u ∧ h, X(a + u ∧ h) + c(a))`
solves the `(realDrift β, realCov Γ Γ')` martingale problem in `{t < h}` for the shifted filtration
`𝓖_{a+·}`.

Proof: for each relatively compact `W ⊆ {t < h}` and level `k`, restart every clause at `a` and
stop it at the restarted exit (`exists_restart`, on the `𝓖_a`-event `evK X a k`, where the
continuous part has not reached level `k` before `a`); products are decomposed as increments of
`lBr` minus `lComp(a)`-weighted increments of `lComp`, the weights replaced by bounded
`𝓖_a`-measurable versions (`exists_factor`); then `k → ∞` (`exists_martingale_of_ind`, with
uniform bounds on the coefficients); finally `isMPSolutionOn_of_complex`. This file contains the
restart of one clause (`restart_clause`) and the regularity of the restarted process
(`stronglyMeasurable_rsY`, `continuous_rsY`, `stop_le_h`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.BornRestart
open scoped NNReal

variable {κ : Type*} [Fintype κ] {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {β : (κ → ℂ) → κ → ℂ} {Γ Γ' : (κ → ℂ) → κ → κ → ℂ} {c : ℝ≥0 → κ → ℂ}
  {X : ℝ≥0 → Ω → κ → ℂ} {σ : ℝ → Ω → WithTop ℝ≥0}

theorem continuous_toR_const (t : ℝ) : Continuous fun z : κ → ℂ => toR t z :=
  continuous_toR.comp (continuous_const.prodMk continuous_id)

theorem stronglyMeasurable_rsY (hXa : ∀ t, StronglyMeasurable[𝓖 t] (X t)) (a h u : ℝ≥0) :
    StronglyMeasurable[shiftFil 𝓖 a u] (rsY X c a h u) := by
  have h1 : StronglyMeasurable[𝓖 (a + u)] (X (a + min u h)) :=
    (hXa _).mono (𝓖.mono (add_le_add le_rfl (min_le_left u h)))
  exact ((continuous_toR_const _).comp (continuous_id.add continuous_const)).comp_stronglyMeasurable h1

omit [MeasurableSpace Ω] in
theorem continuous_rsY {ω : Ω} (hx : Continuous fun t => X t ω) (a h : ℝ≥0) :
    Continuous fun u => rsY X c a h u ω := by
  have hm : Continuous fun u : ℝ≥0 => min u h := continuous_id.min continuous_const
  exact continuous_toR.comp ((NNReal.continuous_coe.comp hm).prodMk
    ((hx.comp (continuous_const.add hm)).add continuous_const))

omit [MeasurableSpace Ω] in
/-- Before the exit from `W ⊆ {t < h}` the restarted time is below `h`. -/
theorem stop_le_h {ω : Ω} (hx : Continuous fun t => X t ω) {a h : ℝ≥0}
    {W : Set (Fin (rDim κ) → ℝ)} (hW : IsInteriorDomain W {y | tOf y < h}) (u : ℝ≥0) :
    stopTime (exitTimeFrom W (rsY X c a h) ω) u ≤ h := by
  by_cases h0 : rsY X c a h 0 ω ∈ W
  · have hm := hW.2.2 (stop_mem_closure hW.1 (continuous_rsY hx a h) h0 u)
    simp only [mem_ofPred_eq, tOf_rsY] at hm
    by_contra hv; push Not at hv
    rw [min_eq_right hv.le] at hm; exact lt_irrefl _ hm
  · rw [exitTimeFrom_eq_zero h0, stopTime_zero_left]; exact zero_le

/-- **Restart of one clause**, localized on `evK X a k`. -/
theorem restart_clause (hX : IsCLocSol Q 𝓖 β Γ Γ' c X σ) {Z : ℝ≥0 → Ω → ℂ}
    (hZ : ∀ L, ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] stoppedProcess Z (σ L) t)
    (hZc : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω) {C : ℝ} (hC : ∀ t, ‖c t‖ ≤ C) (a h : ℝ≥0)
    {W : Set (Fin (rDim κ) → ℝ)} (hW : IsInteriorDomain W {y | tOf y < h}) {Rz : ℝ}
    (hRz : ∀ y ∈ W, ‖zOf y‖ ≤ Rz) {k : ℕ} (hk : Rz + C < k) :
    ∃ M : ℝ≥0 → Ω → ℂ, Martingale M (shiftFil 𝓖 a) Q ∧ ∀ u, M u =ᵐ[Q] fun ω =>
      (evK X a k).indicator (fun _ => (1 : ℂ)) ω *
        (Z (a + stopTime (exitTimeFrom W (rsY X c a h) ω) u) ω - Z a ω) := by
  have hXm : ∀ t, Measurable[𝓖 t] (X t) := fun t => (hX.adapted t).measurable
  have hYm : ∀ u, Measurable[shiftFil 𝓖 a u] (rsY X c a h u) := fun u =>
    (stronglyMeasurable_rsY hX.adapted a h u).measurable
  have hθ := isStoppingTime_rawHit (F := Wᶜ) hYm
  have hθeq : ∀ᵐ ω ∂Q, exitTimeFrom W (rsY X c a h) ω = rawHit Wᶜ (rsY X c a h) ω := by
    filter_upwards [hX.continuous] with ω hx
    rw [rawHit_eq_hitTime hW.1.isClosed_compl (continuous_rsY hx a h)]; rfl
  obtain ⟨L, hL⟩ := hX.loc k
  obtain ⟨N, hN, hNX⟩ := hZ L
  obtain ⟨M, hM, hMX⟩ := exists_restart hN hNX hZc a hθ (isStoppingTime_hitK hXm k) hL
    (measurableSet_evK hXm a k) (by
      filter_upwards [hX.continuous, hθeq] with ω hx he hω
      rw [← he]
      exact add_exit_le_hitK hx (fun y hy => subset_closure hy |> hW.2.2) hRz (hC a) hk hω)
  refine ⟨M, hM, fun u => ?_⟩
  filter_upwards [hMX u, hθeq] with ω h1 h2
  rw [h1, h2]

end BlockBand.SourceProcess.ComplexUnique
