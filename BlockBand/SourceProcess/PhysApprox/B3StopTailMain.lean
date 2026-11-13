module

public import BlockBand.SourceProcess.PhysApprox.B3StopTailFixed
public import BlockBand.SourceProcess.PhysApprox.B3ModulMain

/-!
# `ComplexClosedStopTail` from `ComplexClosedSummed` and the fourth moments

* **`complexClosedStopTail_of_fourth (hS : ComplexClosedSummed) (hF : ComplexClosedFourth) :
  ComplexClosedStopTail`** and **`complexClosedStopTail_of (hS) (hL : ComplexClosedLindeberg)`**.
  Given `θ > 0`, `R = (4K + birthC + 1)/θ`. Eventually in `W`:
  `R · P(stop) ≤ 4K + birthC + Σ_x b3SummedErr (dg x) (dg x) ≤ 4K + birthC + 1`
  (`fixedW_bound`, `sum_errT_le`). Adaptedness of the alive sets:
  `measurableSet_b3AliveM_past`. Integrability of the stopped steps: `ComplexClosedFourth` at
  steps without a birth, the birth error of `ComplexClosedSummed` at birth steps.
* `complexClosedTight_of_summed`: hence `ComplexClosedTight` from `ComplexKStoppedMomentMax`,
  `ComplexClosedSummed` and `ComplexClosedLindeberg` (with `targetModulus_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.StopTail

open MeasureTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum
open scoped ENNReal

variable {W np K : ℕ}

/-- Integrability of a stopped trace-coordinate step at a birth step, from a finite birth error. -/
theorem integrable_stepX_birth {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (x : SrcCol K (Fin np))
    (j : ℕ) (hm : AEStronglyMeasurable (stepX b E s h τ m R W Vs x j) (closedLaw b W np))
    (hB : birthT b E s h τ m R W Vs x j ≠ ⊤) :
    Integrable (stepX b E s h τ m R W Vs x j) (closedLaw b W np) := by
  refine ⟨hm, ?_⟩
  have := lintegral_indicator_le_sub (μ := closedLaw b W np) (b3Alive b E s h τ m R W j Vs)
    (b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np))
    (cEntry (Sum.inl (dg x) : CIdx K np) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j))
  exact this.trans_lt (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hB, enorm_lt_top⟩)

/-- Integrability of a stopped trace-coordinate step from a finite fourth moment. -/
theorem integrable_stepX_four {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (x : SrcCol K (Fin np))
    (j : ℕ) (hm : AEStronglyMeasurable (stepX b E s h τ m R W Vs x j) (closedLaw b W np))
    (h4 : ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
      (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl (dg x) : CIdx K np) y‖ₑ ^ 4) y
        ∂closedLaw b W np ≠ ⊤) :
    Integrable (stepX b E s h τ m R W Vs x j) (closedLaw b W np) := by
  refine ClosedSumProof.integrable_of_pow4 hm ⟨hm.norm.pow 4, ?_⟩
  show ∫⁻ y, ‖‖stepX b E s h τ m R W Vs x j y‖ ^ 4‖ₑ ∂closedLaw b W np < ⊤
  simp_rw [enorm_pow, enorm_norm]
  refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.2 h4)
  exact lintegral_congr fun y => (Modul.indicator_enorm_pow4 _ _ y).symm

/-- **`ComplexClosedStopTail` from `ComplexClosedSummed` and `ComplexClosedFourth`.** -/
theorem complexClosedStopTail_of_fourth (hS : ComplexClosedSummed) (hF : ComplexClosedFourth) :
    ComplexClosedStopTail := by
  intro b E np τ m T s h K Vs hFD θ hθ
  obtain ⟨hD, -, hτ, -, -, hVs⟩ := id hFD
  have hb : b < 1 / 2 := hD.2.1
  have hb1 : b < 1 := by linarith
  have hE1 : -2 < E := hD.2.2.1
  have hE2 : E < 2 := hD.2.2.2.1
  set L : ℝ := 4 * K + birthC b m
  have hL : 0 ≤ L := add_nonneg (by positivity) (birthC_nonneg b m)
  set R : ℝ := (L + 1) / θ
  have hR : 0 < R := by positivity
  refine ⟨R, ?_⟩
  have hErr : ∀ᶠ W : ℕ in atTop, ∑ x : SrcCol K (Fin np),
      b3SummedErr b E s T h τ m R W (Vs W) (Sum.inl (dg x)) (Sum.inl (dg x)) ≤ 1 := by
    have ht := tendsto_finsetSum (univ : Finset (SrcCol K (Fin np))) fun x _ =>
      (hS b E np τ m T s h K Vs hFD R).1 (Sum.inl (dg x)) (Sum.inl (dg x))
    simp only [sum_const_zero] at ht
    exact (ENNReal.tendsto_nhds_zero.1 ht) 1 one_pos
  have hFour := eventually_all.2 fun x : SrcCol K (Fin np) =>
    (ENNReal.tendsto_nhds_zero.1 (hF b E np τ m T s h K Vs hFD R (Sum.inl (dg x)))) 1 one_pos
  filter_upwards [hVs, hErr, hFour, eventually_ge_atTop 1] with W hV hE hF4 hW1
  have hVm : Measurable (Vs W) :=
    hV.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set I := Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊
  have hAd : ∀ j, closeLen s W ≤ j →
      MeasurableSet[b3Sigma W j np] (b3AliveM b E s h τ m R W j (Vs W)) := fun j hj =>
    Modul.measurableSet_b3AliveM_past s h τ m R hj le_rfl hV.1
  have hI : ∀ j ∈ I, ∀ x : SrcCol K (Fin np),
      Integrable (stepX b E s h τ m R W (Vs W) x j) (closedLaw b W np) := by
    intro j hj x
    have hm := aestronglyMeasurable_stepX hb1 hE1 hE2 hVm x j (R := R) (τ := τ) (m := m)
      (s := s) (h := h)
    by_cases hB : IsBirthStep τ W j
    · have hle : errT b E s h τ m R W (Vs W) x j ≤ 1 :=
        (single_le_sum (f := fun j => errT b E s h τ m R W (Vs W) x j) (fun _ _ => zero_le)
          hj).trans ((sum_errT_le b E s h τ m R W (Vs W) T x).trans
          ((single_le_sum (f := fun x : SrcCol K (Fin np) =>
            b3SummedErr b E s T h τ m R W (Vs W) (Sum.inl (dg x)) (Sum.inl (dg x)))
            (fun _ _ => zero_le) (mem_univ x)).trans hE))
      unfold errT at hle
      rw [ite_eq_left hB] at hle
      exact integrable_stepX_birth x j hm (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
    · have hjf : j ∈ I.filter (fun j => ¬ IsBirthStep τ W j) := mem_filter.2 ⟨hj, hB⟩
      have hle := (single_le_sum (f := fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl (dg x) : CIdx K np) y‖ₑ ^ 4) y
          ∂closedLaw b W np) (fun _ _ => zero_le) hjf).trans (hF4 x)
      exact integrable_stepX_four x j hm (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  have hfix := fixedW_bound hb hE1 hE2 hW1 hτ hV hAd hI
  have hsum : ∑ x : SrcCol K (Fin np), ∑ j ∈ I, errT b E s h τ m R W (Vs W) x j ≤ 1 :=
    (sum_le_sum fun x _ => sum_errT_le b E s h τ m R W (Vs W) T x).trans hE
  change closedLaw b W np (stopSet b E s h τ m T R W (Vs W)) ≤ _
  have h1 : ENNReal.ofReal R * closedLaw b W np (stopSet b E s h τ m T R W (Vs W)) ≤
      ENNReal.ofReal (L + 1) := by
    refine hfix.trans ((add_le_add le_rfl hsum).trans (le_of_eq ?_))
    rw [ENNReal.ofReal_add hL zero_le_one, ENNReal.ofReal_one]
  have hR0 : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.2 hR).ne'
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hR0) (Or.inl ENNReal.ofReal_ne_top)] at h1
  refine h1.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_div_of_pos hR]
  congr 1
  have hpos : 0 < L + 1 := by positivity
  simp only [R]
  field_simp

/-- **`ComplexClosedStopTail` from `ComplexClosedSummed` and `ComplexClosedLindeberg`.** -/
theorem complexClosedStopTail_of (hS : ComplexClosedSummed) (hL : ComplexClosedLindeberg) :
    ComplexClosedStopTail :=
  complexClosedStopTail_of_fourth hS (Modul.complexClosedFourth_iff_lindeberg.2 hL)

/-- **`ComplexClosedTight` from the maximal stopped `𝒦` moment, `ComplexClosedSummed` and
`ComplexClosedLindeberg`** (stop tail here, modulus by `targetModulus_holds`). -/
theorem complexClosedTight_of_summed (hK : ComplexKStoppedMomentMax) (hS : ComplexClosedSummed)
    (hL : ComplexClosedLindeberg) : ComplexClosedTight :=
  complexClosedTight_of_max hK (complexClosedStopTail_of hS hL)
    (Modul.targetModulus_holds hS (Modul.complexClosedFourth_iff_lindeberg.2 hL)
      (complexClosedStopTail_of hS hL))

end BlockBand.SourceProcess.PhysApprox.B3.StopTail
