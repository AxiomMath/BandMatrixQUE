module

public import BlockBand.Transmission.LawFinite.Interface
public import BlockBand.Model.Construction.OrderedSpectrum

/-!
# Bulk-uniform ⇒ along moving energies; Markov form of the Ginibre fraction

* `eventually_mem_bulkInterval`: a moving energy `e W → E ∈ (-2,2)` lies eventually in
  `bulkInterval ((2 - |E|)/2)`.
* `entranceAlong_of_bulk`: `TransmissionEntranceBulk → TransmissionEntranceAlong`
  (the finite-`W` constants, chosen before `E`, give the along-energy `limsup` form).
* `smallFraction_prob_le`: Markov, `P(#{s_i(B)² < a} > εW) ≤ C_b/(ε log(1/a))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-- A moving energy lies eventually in the bulk interval of margin `(2 - |E|)/2`. -/
theorem eventually_mem_bulkInterval {E Ce : ℝ} {e : ℕ → ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) : ∀ᶠ W : ℕ in atTop, e W ∈ bulkInterval ((2 - |E|) / 2) := by
  have hκ : 0 < (2 - |E|) / 2 := by
    have : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (Ce / ((2 - |E|) / 2))
  filter_upwards [eventually_ge_atTop (N + 1)] with W hW
  have hW0 : (0 : ℝ) < W := by exact_mod_cast (show 0 < W by omega)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast (show 1 ≤ W by omega)
  have hNW : (N : ℝ) + 1 ≤ W := by exact_mod_cast hW
  have hd := he W (by omega)
  rw [IsNearEnergy] at hd
  have hsmall : Ce / (W : ℝ) ^ 2 ≤ (2 - |E|) / 2 := by
    rcases le_or_gt Ce 0 with hc | hc
    · exact (div_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _)).trans hκ.le
    · have h1 : Ce / (W : ℝ) ^ 2 ≤ Ce / W := by
        apply div_le_div_of_nonneg_left hc.le hW0
        nlinarith
      have h2 : Ce / (W : ℝ) ≤ (2 - |E|) / 2 := by
        rw [div_le_iff₀ hW0]
        have := (div_lt_iff₀ hκ).1 hN
        nlinarith
      exact h1.trans h2
  have habs := abs_le.1 (hd.trans hsmall)
  have hE := abs_le.1 (le_refl |E|)
  rw [bulkInterval, Set.mem_Icc]
  constructor <;> linarith [hE.1, hE.2, habs.1, habs.2]

/-- `limsup` bound from bounds with arbitrarily small slack holding eventually. -/
theorem limsup_le_of_eventually_slack {f : ℕ → ℝ≥0∞} {x : ℝ}
    (h : ∀ θ : ℝ, 0 < θ → ∀ᶠ W : ℕ in atTop, f W ≤ ENNReal.ofReal (x + θ)) :
    limsup f atTop ≤ ENNReal.ofReal x := by
  refine ENNReal.le_of_forall_pos_le_add fun θ hθ _ => ?_
  have hθ' : (0 : ℝ) < θ := by exact_mod_cast hθ
  refine (limsup_le_of_le (by isBoundedDefault) (h θ hθ')).trans ?_
  calc ENNReal.ofReal (x + θ) ≤ ENNReal.ofReal x + ENNReal.ofReal θ := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal x + θ := by rw [ENNReal.ofReal_coe_nnreal]

/-- **Bulk-uniform entrance ⇒ entrance along every moving energy.** -/
theorem entranceAlong_of_bulk (h : TransmissionEntranceBulk) : TransmissionEntranceAlong := by
  intro b hb0 hb E hE1 hE2 κ hκ
  have hκI : 0 < (2 - |E|) / 2 := by
    have : |E| < 2 := abs_lt.2 ⟨hE1, hE2⟩
    linarith
  obtain ⟨C, hC⟩ := h b hb0 hb _ hκI κ hκ
  refine ⟨C, fun K t hK ht0 ht1 Ce e he => limsup_le_of_eventually_slack fun θ hθ => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC K t θ hK ht0 ht1 hθ
  filter_upwards [eventually_mem_bulkInterval hE1 hE2 he, eventually_ge_atTop W₀] with W hW hW'
  exact hW₀ W hW' (e W) hW

/-- The small-singular-value count is Borel in the matrix. -/
theorem measurable_smallSingularCount {W : ℕ} (a : ℝ) :
    Measurable fun B : Matrix (Fin W) (Fin W) ℂ => smallSingularCount a B := by
  classical
  have hc : ∀ i : Fin (Fintype.card (Fin W)), Continuous fun B : Matrix (Fin W) (Fin W) ℂ =>
      BlockBand.Foundations.Spectral.increasingEigenvalue
        (isHermitian_conjTranspose_mul_self B) i := fun i =>
    (BlockBand.Model.Construction.continuous_increasingEigenvalue (ι := Fin W) i).comp
      (Continuous.subtype_mk (f := fun B : Matrix (Fin W) (Fin W) ℂ => Bᴴ * B)
        ((continuous_id.matrix_conjTranspose).matrix_mul continuous_id)
        fun B => isHermitian_conjTranspose_mul_self B)
  have heq : (fun B : Matrix (Fin W) (Fin W) ℂ => smallSingularCount a B) = fun B =>
      ∑ i : Fin (Fintype.card (Fin W)), if BlockBand.Foundations.Spectral.increasingEigenvalue
        (isHermitian_conjTranspose_mul_self B) i < a then 1 else 0 := by
    funext B; simp [smallSingularCount, Finset.sum_boole]
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite
    (measurableSet_lt (hc i).measurable measurable_const) measurable_const measurable_const

/-- **Markov form**: `P(#{i : s_i(B)² < a} > εW) ≤ C_b/(ε log(1/a))`. -/
theorem smallFraction_prob_le (h : GinibreSmallSingularFraction) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) : ∃ C : ℝ, ∀ W : ℕ, 0 < W → ∀ a ε : ℝ, 0 < a → a < 1 → 0 < ε →
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
          {B | ε * W < (smallSingularCount a B : ℝ)} ≤
        ENNReal.ofReal (C / (ε * Real.log a⁻¹)) := by
  obtain ⟨C, hC⟩ := h b hb0 hb
  refine ⟨C, fun W hW a ε ha0 ha1 hε => ?_⟩
  set μ := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hεW : 0 < ε * W := mul_pos hε hW0
  have hlog : 0 < Real.log a⁻¹ := Real.log_pos ((one_lt_inv₀ ha0).2 ha1)
  have hsub : {B : Matrix (Fin W) (Fin W) ℂ | ε * W < (smallSingularCount a B : ℝ)} ⊆
      {B | ENNReal.ofReal (ε * W) ≤ (smallSingularCount a B : ℝ≥0∞)} := fun B hB => by
    simp only [Set.mem_ofPred_eq] at hB ⊢
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hB.le
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div
    ((measurable_from_nat.comp (measurable_smallSingularCount (W := W) a)).aemeasurable)
    (by simpa using hεW) ENNReal.ofReal_ne_top).trans ?_
  refine (ENNReal.div_le_div_right (hC W hW a ha0 ha1) _).trans ?_
  rw [← ENNReal.ofReal_div_of_pos hεW]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  field_simp

end BlockBand.Transmission.LawFinite
