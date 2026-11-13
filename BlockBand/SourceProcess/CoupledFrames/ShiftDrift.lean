module

public import BlockBand.SourceProcess.CoupledFrames.ShiftLoc

/-!
# Pathwise identities for increments after a stopping time

* `stoppedDrift_onAfter`: `∫_0^{t∧ρ} 1{θ < s} ξ b_s ds = ξ (∫_0^{t∧ρ} b − ∫_0^{t∧ρ∧θ} b)` for a path
  `b` integrable on `(0,t]`.
* `stoppedProcess_shiftProc`: `Z_{t∧ρ} = ξ (Y_{t∧ρ} − Y_{t∧ρ∧θ})` for `Z = shiftProc Y θ ξ`;
  `shiftProc_zero`: `Z_0 = 0`.
* `stoppedDrift_congr_min`, `stoppedProcess_congr_min`: the stopped values at time `t` only see
  `t ∧ ρ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.ItoNative
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {S κ : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stoppedDrift_onAfter {b : ℝ≥0 → DriverSample S κ → E} {x : DriverSample S κ} {t : ℝ≥0}
    (hb : IntegrableOn (fun s : ℝ => b s.toNNReal x) (Ioc 0 t))
    (ρ θ : DriverSample S κ → WithTop ℝ≥0) (ξ : DriverSample S κ → ℝ) :
    stoppedDrift ρ (onAfter θ ξ b) t x =
      ξ x • (stoppedDrift ρ b t x - stoppedDrift (fun x => min (ρ x) (θ x)) b t x) := by
  unfold stoppedDrift
  rw [← integral_sub (integrableOn_switch hb (ρ x)) (integrableOn_switch hb (min (ρ x) (θ x))),
    ← integral_smul]
  congr 1
  funext s
  simp only [onAfter, le_min_iff]
  by_cases h1 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ x
  · by_cases h2 : θ x < ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0)
    · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1, ite_eq_right (fun h => not_le.2 h2 h.2),
        sub_zero]
    · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_left ⟨h1, not_lt.1 h2⟩, sub_self,
        smul_zero]
  · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right (fun h => h1 h.1), sub_self, smul_zero]

theorem stoppedProcess_shiftProc (Y : ℝ≥0 → DriverSample S κ → E)
    (ρ θ : DriverSample S κ → WithTop ℝ≥0) (ξ : DriverSample S κ → ℝ) (t : ℝ≥0)
    (x : DriverSample S κ) :
    stoppedProcess (shiftProc Y θ ξ) ρ t x =
      ξ x • (stoppedProcess Y ρ t x - stoppedProcess Y (fun x => min (ρ x) (θ x)) t x) := by
  rw [← stoppedProcess_stoppedProcess']
  rfl

theorem shiftProc_zero (Y : ℝ≥0 → DriverSample S κ → E) (θ : DriverSample S κ → WithTop ℝ≥0)
    (ξ : DriverSample S κ → ℝ) (x : DriverSample S κ) : shiftProc Y θ ξ 0 x = 0 := by
  have h0 : stoppedProcess Y θ 0 x = Y 0 x := stoppedProcess_eq_of_le (by simp)
  simp only [shiftProc, h0, sub_self, smul_zero]

theorem stoppedDrift_congr_min {f : ℝ≥0 → DriverSample S κ → E}
    {ρ ρ' : DriverSample S κ → WithTop ℝ≥0} {t : ℝ≥0} {x : DriverSample S κ}
    (h : min (t : WithTop ℝ≥0) (ρ x) = min (t : WithTop ℝ≥0) (ρ' x)) :
    stoppedDrift ρ f t x = stoppedDrift ρ' f t x := by
  unfold stoppedDrift
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hst : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) := by
    rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
    exact hs.2
  have e : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ x ↔ ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ' x := by
    constructor
    · intro h1
      have := le_min hst h1
      rw [h] at this
      exact this.trans (min_le_right _ _)
    · intro h1
      have := le_min hst h1
      rw [← h] at this
      exact this.trans (min_le_right _ _)
  simp only [e]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem stoppedProcess_congr_min (Y : ℝ≥0 → DriverSample S κ → E)
    {ρ ρ' : DriverSample S κ → WithTop ℝ≥0} {t : ℝ≥0} {x : DriverSample S κ}
    (h : min (t : WithTop ℝ≥0) (ρ x) = min (t : WithTop ℝ≥0) (ρ' x)) :
    stoppedProcess Y ρ t x = stoppedProcess Y ρ' t x := by
  rw [stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
  unfold stopTime
  rw [h]

end BlockBand.SourceProcess.CoupledFrames
