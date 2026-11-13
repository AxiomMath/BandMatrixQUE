module

public import BlockBand.Endpoints.Clock.OpenInputsBUniformClockStep

/-!
# The open-inputs lemma, uniformly in `b`: clock moments with a `b`-uniform radius

This is the clock-moment part (Steps 6–7 of the paper's proof) of the open-inputs lemma, uniformly
in `b ∈ Icc β (1/2-β)` and `E ∈ bulkInterval κ`. `clock_moment_unifB` is `clock_moment_unif` with
the weighted step `clockStep_weighted_unif` replaced by `clockStep_weighted_unifB`: the radius `r₁`
is chosen before `b`; for each `b`, each `r₀ ≤ r₁` and each `J`, the constants `A, G, W₀` are those
of the energy-uniform proof (they may depend on `b`). The crude bounds (`crude_bound_unif`), the
helpers `weighted_max`, `entrance_weight_le`, `good_part_le` and the iteration lemmas are reused.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

namespace MovingEnergy

open OpenInputsProof

/-- **Clock moments of the open-inputs lemma with the radius `r₁` uniform in `b ∈ Icc β (1/2-β)`**
(the `b`-uniform version of `clock_moment_unif`): `r₁` depends only on `(β, κ, q, P)`; for each `b`, `r₀ ≤ r₁` and
`J`, the constants `A, G, W₀` depend on `b` and are uniform in `E ∈ bulkInterval κ` and in the
Hermitian initial `D`. -/
theorem clock_moment_unifB (hB : LayersBUniformHyp) (hWL : WeightedLayerContract)
    (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract) {β : ℝ} (hβ : 0 < β)
    (hβ4 : β < 1 / 4) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {q : ℝ → ℝ} (hq : IsClockWeight q)
    (T : ℝ) {P : ℕ} (hP : 2 ≤ P) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ r₀ : ℝ, 0 < r₀ → r₀ ≤ r₁ → ∀ J : ℕ,
      ∃ (A G : ℝ) (W₀ : ℕ), 0 ≤ A ∧ 1 ≤ G ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ∀ j : ℕ, (j : ℝ) ≤ T * W →
        ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j ≤
          ENNReal.ofReal ((A * ((j : ℝ) + 1)) ^ P) +
            ENNReal.ofReal (G ^ j) * oneEndedLaw W b j (goodSet b E D r₀ J j)ᶜ ^ (1 / 2 : ℝ) := by
  have hκ4 : κ < 4 := by linarith
  obtain ⟨-, hq0, Kq₀, hqK₀⟩ := hq
  have hqK : ∀ x, q x ≤ max Kq₀ 0 := fun x => (hqK₀ x).trans (le_max_left _ _)
  have hKq : 0 ≤ max Kq₀ 0 := le_max_right _ _
  obtain ⟨r₁, hr₁, hwtB⟩ := clockStep_weighted_unifB hB hWL hGA hTM hβ hβ4 hκ hκ1 hKq hP
  refine ⟨r₁, hr₁, fun b hb r₀ hr₀ hr₀₁ J => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  have hW1 := onePortWeighted_of hWL hGA
  obtain ⟨C₁, W₁, -, hcr1⟩ := crude_bound_unif hW1 hGA hb0 hb1 hκ hκ4 hKq (P := P) (by omega)
  obtain ⟨K, Cw, W₃, hK, hwt⟩ := hwtB b hb
  obtain ⟨C₂, W₂, -, hcr2⟩ := crude_bound_unif hW1 hGA hb0 hb1 hκ hκ4 hKq (P := 2 * P) (by omega)
  have hη0 := etaLow_pos hb1 hκ hκ4
  have hG₁1 : 1 ≤ 2 * max C₁ 1 := by have := le_max_right C₁ 1; linarith
  have hG₂1 : 1 ≤ 2 * max C₂ 1 := by have := le_max_right C₂ 1; linarith
  have hCw'0 : 0 ≤ max Cw 0 := le_max_right _ _
  have hPr : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hC'0 : 0 ≤ 3 * max Cw 0 / P := by positivity
  have hPC : 3 * max Cw 0 ≤ P * (3 * max Cw 0 / P) := by field_simp; exact le_rfl
  have hB₀0 : 0 ≤ 1 / etaLow b κ + 1 := by positivity
  have hA₀1 : 1 ≤ max 1 ((1 + K * (1 / etaLow b κ + 1)) * (2 * max C₁ 1) ^ J) := le_max_left _ _
  refine ⟨max (Real.exp (max Cw 0 * max T 0) *
      (max 1 ((1 + K * (1 / etaLow b κ + 1)) * (2 * max C₁ 1) ^ J) + 3 * max Cw 0 / P))
      ((2 * max C₁ 1) ^ J), 2 * max C₂ 1, max (max W₁ W₂) (max W₃ 1), by positivity, hG₂1, ?_⟩
  intro W hW E hEκ D hD j hj
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have hzB : 1 / (boundaryZ b E).im + 1 ≤ 1 / etaLow b κ + 1 := by
    have := one_div_le_one_div_of_le hη0 (etaLow_le_im hb1 hκ hEκ)
    linarith
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW0 : 0 < W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hcrude1 := crude_iter (q := q) (D := D) (b := b) (E := E) hq0 hqK
    (fun X hX Y hY w hw0 hw1 => hcr1 W hW0 hW1' E hEκ X hX Y hY w hw0 hw1) hD
  have hcrude2 := crude_iter (q := q) (D := D) (b := b) (E := E) hq0 hqK
    (fun X hX Y hY w hw0 hw1 => hcr2 W hW0 hW2 E hEκ X hX Y hY w hw0 hw1) hD
  have hAj : 1 ≤ max (Real.exp (max Cw 0 * max T 0) *
      (max 1 ((1 + K * (1 / etaLow b κ + 1)) * (2 * max C₁ 1) ^ J) + 3 * max Cw 0 / P))
      ((2 * max C₁ 1) ^ J) * ((j : ℝ) + 1) := by
    have h1 := (one_le_pow₀ (n := J) hG₁1).trans (le_max_right (Real.exp (max Cw 0 * max T 0) *
      (max 1 ((1 + K * (1 / etaLow b κ + 1)) * (2 * max C₁ 1) ^ J) + 3 * max Cw 0 / P)) _)
    have : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    nlinarith
  rcases lt_or_ge j J with hjJ | hjJ
  · refine le_add_right ((hcrude1 j).trans (ENNReal.ofReal_le_ofReal ?_))
    have h1 : (2 * max C₁ 1) ^ j ≤ (2 * max C₁ 1) ^ J := pow_le_pow_right₀ hG₁1 hjJ.le
    have h2 := le_max_right (Real.exp (max Cw 0 * max T 0) *
      (max 1 ((1 + K * (1 / etaLow b κ + 1)) * (2 * max C₁ 1) ^ J) + 3 * max Cw 0 / P))
      ((2 * max C₁ 1) ^ J)
    have h3 : (1 : ℝ) ≤ (j : ℝ) + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    have h4 := le_mul_of_one_le_right (zero_le_one.trans ((one_le_pow₀ hG₁1).trans h2)) h3
    exact (h1.trans (h2.trans h4)).trans (le_self_pow₀ hAj (by omega))
  · obtain ⟨n, rfl⟩ : ∃ n, j = J + n := ⟨j - J, by omega⟩
    have hm := measurableSet_goodSet (b := b) (E := E) (D := D) r₀ J (J + n)
    rw [← lintegral_add_compl _ hm]
    refine add_le_add ?_ (exceptional_part hq0 hG₂1 (hcrude2 (J + n)))
    have hwt' : ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ r₀ →
        ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ max Kq₀ 0 →
          ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
              nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
            ENNReal.ofReal ((1 + max Cw 0 / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
              max Cw 0 * (clockU Y ^ (P - 1) + 1)) := fun X hX hδ Y hY w hw0 hw1 =>
      weighted_max hK hWr hY (hwt W hW0 hW3 E hEκ X hX (hδ.trans hr₀₁) Y hY w hw0 hw1)
    have h0 := entrance_weight_le (r₀ := r₀) hq0 hW0 hD hzpos hE hK hB₀0 hzB J P (by omega)
      (hcrude1 J)
    have hit := weighted_iter hq0 hqK hK hCw'0 hW0 (by omega) hwt' hD J hA₀1 hC'0 hPC h0 n
    rw [← lintegral_indicator hm]
    have hn : (n : ℝ) ≤ T * W := by
      have : (n : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ J + n)
      linarith
    exact good_part_le hK hCw'0 hWr hA₀1 hC'0 hn hq0 (le_max_left _ _) hit

end MovingEnergy

end BlockBand.Endpoints.Clock
