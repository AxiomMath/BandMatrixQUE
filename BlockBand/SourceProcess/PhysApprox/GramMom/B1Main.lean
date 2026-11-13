module

public import BlockBand.SourceProcess.PhysApprox.GramMom.B1Coef
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMomDefs

/-!
# The summed second moments `GramMomSumSq`

Measure `closedLaw b W np`; steps `j ∈ nbSteps s T τ W`; coordinate `Sum.inl c`, `c* = swapE c`;
`A_j = b3Alive … R W j`, a.e. equal to the `b3Sigma W j`-event `b3AliveM … j`.
* `step_le`: `E[1_{A_j}|ΔX_c|²] ≤ brErr j + W⁻¹ max(covC R, 0)`, where `brErr j` is the
  bracket integrand of `b3SummedErr (inl c) (inl c*)` (`|ΔX_c|² = ΔX_c ΔX_{c*}`, `b3dX_swapE`;
  `lintegral_indicator_sq_le`); integrability of `1_{A_j}ΔX_cΔX_{c*}` from a finite
  fourth moment.
* **`gramMomSumSq_holds`**: eventually `ComplexClosedSummed` gives `Σ_j brErr j ≤ 1`,
  `ComplexClosedLindeberg` gives the finite fourth moments, and `#nbSteps ≤ W max(T, 0)`; the
  constant is `1 + max(T, 0) max(covC R, 0)`.
Inputs: the antecedents `ComplexClosedSummed`, `ComplexClosedLindeberg` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedSumProof (swapE)
open GramMom
open scoped NNReal ENNReal ComplexConjugate

variable {W np K : ℕ}

/-- The bracket integrand of `b3SummedErr (inl c) (inl c*)` at step `j`. -/
def brErr (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) : ℝ≥0∞ :=
  ∫⁻ y, ‖(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j Vs).indicator (fun y =>
          b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y *
            b3dX b E s h τ m W j Vs (Sum.inl (swapE c) : CIdx K np) y) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * cCov b E (Sum.inl c : CIdx K np) (Sum.inl (swapE c))
          (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂closedLaw b W np

/-- The bracket integrands are part of `b3SummedErr`. -/
theorem sum_brErr_le (b E s T h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) :
    ∑ j ∈ nbSteps s T τ W, brErr b E s h τ m R W j Vs c ≤
      b3SummedErr b E s T h τ m R W Vs (Sum.inl c) (Sum.inl (swapE c)) := by
  unfold b3SummedErr
  exact le_add_right (le_add_left le_rfl)

/-- **One step**: the second moment is bounded by the bracket integrand and `W⁻¹ covC`. -/
theorem step_le {b E s h : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {τ m : Fin np → ℝ}
    {R : ℝ} {W j : ℕ} {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : IsTimeSFrame b E s h K W Vs) (hj : closeLen s W ≤ j)
    (c : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np))
    (h4 : ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
      (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y‖ₑ ^ 4) y
        ∂closedLaw b W np ≠ ∞) :
    ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
      (fun y => ‖b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y‖ₑ ^ 2) y ∂closedLaw b W np ≤
      brErr b E s h τ m R W j Vs c +
        ENNReal.ofReal ((W : ℝ)⁻¹ * max (covC b E K np R) 0) := by
  have hVm : Measurable Vs :=
    hV.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs
  have hδ : Measurable (b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np)) :=
    (Modul.measurable_b3X s h τ m hVm _).sub (Modul.measurable_b3X s h τ m hVm _)
  have hsw := b3dX_swapE b E s h τ m W j Vs c
  have hI := integrable_indicator_mul_conj (measurableSet_b3AliveM b E s h τ m R W j hVm) hAA
    hδ h4
  have e : (fun y => b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y *
      conj (b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y)) = fun y =>
      b3dX b E s h τ m W j Vs (Sum.inl c : CIdx K np) y *
        b3dX b E s h τ m W j Vs (Sum.inl (swapE c) : CIdx K np) y :=
    funext fun y => by rw [hsw]
  rw [e] at hI
  exact lintegral_indicator_sq_le (gen_sigma_le W j np)
    (Modul.measurableSet_b3AliveM_past s h τ m R hj le_rfl hV.1) hAA hsw hI (norm_beta_le hj c (swapE c))

/-- `#nbSteps ≤ W max(T, 0)`. -/
theorem card_nbSteps_le (s T : ℝ) (τ : Fin np → ℝ) (W : ℕ) :
    ((nbSteps s T τ W).card : ℝ) ≤ (W : ℝ) * max T 0 := by
  have h1 : (nbSteps s T τ W).card ≤ ⌊(W : ℝ) * T⌋₊ :=
    (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ico]; exact Nat.sub_le _ _)
  have h0 : 0 ≤ (W : ℝ) * max T 0 := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  calc ((nbSteps s T τ W).card : ℝ) ≤ (⌊(W : ℝ) * T⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ (⌊(W : ℝ) * max T 0⌋₊ : ℝ) := by
        exact_mod_cast Nat.floor_mono
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _))
    _ ≤ _ := Nat.floor_le h0

/-- **`GramMomSumSq` holds.** -/
theorem gramMomSumSq_holds : GramMomSumSq := by
  intro hS hL b E np τ m T s h K Vs hD R c
  obtain ⟨⟨-, hb, hE1, hE2, -⟩, -, -, -, -, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  set Cc := max (covC b E K np R) 0
  have hCc : 0 ≤ Cc := le_max_right _ _
  refine ⟨1 + max T 0 * Cc, ?_⟩
  have h1 := (ENNReal.tendsto_nhds_zero.mp
    ((hS b E np τ m T s h K Vs hD R).1 (Sum.inl c) (Sum.inl (swapE c)))) 1 one_pos
  have h2 := (ENNReal.tendsto_nhds_zero.mp (hL b E np τ m T s h K Vs hD R (Sum.inl c))) 1 one_pos
  filter_upwards [hVs, h1, h2, eventually_ge_atTop 1] with W hV hW1 hW2 hW
  have hstep : ∀ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 2) y ∂closedLaw b W np ≤
      brErr b E s h τ m R W j (Vs W) c + ENNReal.ofReal ((W : ℝ)⁻¹ * Cc) := by
    intro j hj
    have hjs : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
    have hle : ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c : CIdx K np) y‖ₑ ^ 4) y
          ∂closedLaw b W np ≤ 1 :=
      (Finset.single_le_sum (f := fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c : CIdx K np) y‖ₑ ^ 4) y
          ∂closedLaw b W np) (fun _ _ => zero_le) hj).trans hW2
    exact step_le hb1 hE1 hE2 hV hjs c (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hcard : ((nbSteps s T τ W).card : ℝ) * ((W : ℝ)⁻¹ * Cc) ≤ max T 0 * Cc := by
    calc ((nbSteps s T τ W).card : ℝ) * ((W : ℝ)⁻¹ * Cc)
        ≤ ((W : ℝ) * max T 0) * ((W : ℝ)⁻¹ * Cc) :=
          mul_le_mul_of_nonneg_right (card_nbSteps_le s T τ W)
            (mul_nonneg (inv_nonneg.2 hWpos.le) hCc)
      _ = max T 0 * Cc := by field_simp
  calc ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 2) y ∂closedLaw b W np
      ≤ ∑ j ∈ nbSteps s T τ W,
          (brErr b E s h τ m R W j (Vs W) c + ENNReal.ofReal ((W : ℝ)⁻¹ * Cc)) :=
        Finset.sum_le_sum hstep
    _ = ∑ j ∈ nbSteps s T τ W, brErr b E s h τ m R W j (Vs W) c +
          ((nbSteps s T τ W).card : ℝ≥0∞) * ENNReal.ofReal ((W : ℝ)⁻¹ * Cc) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 + ENNReal.ofReal (max T 0 * Cc) := by
        refine add_le_add ((sum_brErr_le b E s T h τ m R W (Vs W) c).trans hW1) ?_
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = ENNReal.ofReal (1 + max T 0 * Cc) := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (le_max_right _ _) hCc),
          ENNReal.ofReal_one]

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
