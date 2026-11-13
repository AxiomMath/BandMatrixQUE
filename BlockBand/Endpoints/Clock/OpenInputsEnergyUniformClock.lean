module

public import BlockBand.Endpoints.Clock.OpenInputsEnergyUniformClockStep

/-!
# The open-inputs lemma, energy-uniform: clock moments along the one-ended path

This is the clock-moment part (Steps 6–7 of the paper's proof) of the open-inputs lemma, uniformly
for `E ∈ bulkInterval κ`, `b` fixed. `clock_moment_unif` is `OpenInputsProof.clock_moment_raw`
with the constants of `ClockStepBound` replaced by the energy-uniform `crude_bound_unif` and
`clockStep_weighted_unif`, and the deterministic bound `δ₀ ≤ (Im z)⁻¹ + 1` of the entrance block
replaced by `δ₀ ≤ η_κ⁻¹ + 1` (`η_κ = etaLow b κ ≤ Im z`). The iteration lemmas `crude_iter`,
`weighted_iter`, `exceptional_part`, `growth_le` are reused at each energy.
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

variable {b κ : ℝ}

section Helpers

variable {W : ℕ} {E : ℝ} {q : ℝ → ℝ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- The weighted step with its constant replaced by `max C 0`. -/
theorem weighted_max {K C : ℝ} (hK : 0 ≤ K) (hW : (0 : ℝ) < W) {P : ℕ}
    {X Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.PosSemidef) {I : ℝ≥0∞}
    (h : I ≤ ENNReal.ofReal ((1 + C / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
      C * (clockU Y ^ (P - 1) + 1))) :
    I ≤ ENNReal.ofReal ((1 + max C 0 / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
      max C 0 * (clockU Y ^ (P - 1) + 1)) := by
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hu := clockU_nonneg' hY
  have h1 : 0 ≤ (1 + K * jetDistance0 b E X) * clockU Y ^ P := by
    have h0 : 0 ≤ K * jetDistance0 b E X := mul_nonneg hK (norm_nonneg _)
    have : 0 ≤ 1 + K * jetDistance0 b E X := by linarith
    positivity
  have h2 : 0 ≤ clockU Y ^ (P - 1) + 1 := by positivity
  have h3 : C / W ≤ max C 0 / W := div_le_div_of_nonneg_right (le_max_left _ _) hW.le
  have h4 : (1 + C / W) * ((1 + K * jetDistance0 b E X) * clockU Y ^ P) ≤
      (1 + max C 0 / W) * ((1 + K * jetDistance0 b E X) * clockU Y ^ P) :=
    mul_le_mul_of_nonneg_right (by linarith) h1
  have h5 : C * (clockU Y ^ (P - 1) + 1) ≤ max C 0 * (clockU Y ^ (P - 1) + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) h2
  have e1 : (1 + C / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P =
      (1 + C / W) * ((1 + K * jetDistance0 b E X) * clockU Y ^ P) := by ring
  have e2 : (1 + max C 0 / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P =
      (1 + max C 0 / W) * ((1 + K * jetDistance0 b E X) * clockU Y ^ P) := by ring
  rw [e1, e2]
  linarith

/-- The entrance block of the weighted moment: `M_J ≤ max(1, (1 + K B₀) G₁^J)^P`, with the
deterministic bound `δ₀ ≤ (Im z)⁻¹ + 1 ≤ B₀`. -/
theorem entrance_weight_le (hq0 : ∀ x, 0 ≤ q x) (hW0 : 0 < W) (hD : D.IsHermitian)
    (hzpos : 0 < (boundaryZ b E).im) (hE : |E| ≤ 2) {K B₀ G₁ r₀ : ℝ} (hK : 0 ≤ K)
    (hB₀ : 0 ≤ B₀) (hzB : 1 / (boundaryZ b E).im + 1 ≤ B₀) (J P : ℕ)
    (hP : 1 ≤ P)
    (hcr : ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D J ω) ^ P) ∂oneEndedLaw W b J ≤
      ENNReal.ofReal (G₁ ^ J)) :
    ∫⁻ ω, weightFun b E q D r₀ J K P J ω ∂oneEndedLaw W b J ≤
      ENNReal.ofReal (max 1 ((1 + K * B₀) * G₁ ^ J) ^ P) := by
  have hpt : ∀ᵐ ω ∂oneEndedLaw W b J, weightFun b E q D r₀ J K P J ω ≤
      ENNReal.ofReal (1 + K * B₀) * ENNReal.ofReal (clockU (oneEndedY b E q D J ω) ^ P) := by
    filter_upwards [ZeroEntranceProb.ae_X_isHermitian b E hD J] with ω hω
    unfold weightFun
    by_cases hg : ω ∈ goodSet b E D r₀ J J
    · rw [Set.indicator_of_mem hg, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
        (pow_nonneg (clockU_chain_nonneg hq0 J ω) P))
      have := (jetDistance0_le hW0 hω hzpos hE (b := b)).trans hzB
      have : K * chainD0 b E D J ω ≤ K * B₀ := mul_le_mul_of_nonneg_left this hK
      linarith
    · rw [Set.indicator_of_notMem hg]; exact zero_le
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_of_nonneg_left hcr zero_le).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((le_max_right (1 : ℝ) ((1 + K * B₀) * G₁ ^ J)).trans ?_)
  exact le_self_pow₀ (le_max_left _ _) (by omega)

/-- From the iterated weighted moment to the good part of the clock moment. -/
theorem good_part_le {K r₀ Cw A₀ C' A T : ℝ} (hK : 0 ≤ K) (hCw : 0 ≤ Cw) (hW : (0 : ℝ) < W)
    (hA₀ : 1 ≤ A₀) (hC' : 0 ≤ C') {J n P : ℕ} (hn : (n : ℝ) ≤ T * W) (hq0 : ∀ x, 0 ≤ q x)
    (hA : Real.exp (Cw * max T 0) * (A₀ + C') ≤ A)
    (hit : ∫⁻ ω, weightFun b E q D r₀ J K P (J + n) ω ∂oneEndedLaw W b (J + n) ≤
      ENNReal.ofReal (((1 + Cw / W) ^ n * (A₀ + n * C')) ^ P)) :
    ∫⁻ ω, (goodSet b E D r₀ J (J + n)).indicator
        (fun ω => ENNReal.ofReal (clockU (oneEndedY b E q D (J + n) ω) ^ P)) ω
        ∂oneEndedLaw W b (J + n) ≤
      ENNReal.ofReal ((A * (((J + n : ℕ) : ℝ) + 1)) ^ P) := by
  refine le_trans (lintegral_mono fun ω => ?_) (hit.trans (ENNReal.ofReal_le_ofReal ?_))
  · unfold weightFun
    by_cases hg : ω ∈ goodSet b E D r₀ J (J + n)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
      refine ENNReal.ofReal_le_ofReal ?_
      have hu := pow_nonneg (clockU_chain_nonneg (b := b) (E := E) (D := D) hq0 (J + n) ω) P
      have : 0 ≤ K * chainD0 b E D (J + n) ω := mul_nonneg hK (norm_nonneg _)
      have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + K * chainD0 b E D (J + n) ω)
        hu
      linarith
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]
  · refine pow_le_pow_left₀ (by positivity) ?_ P
    have hg := growth_le hCw hW hn
    have h1 : (n : ℝ) ≤ ((J + n : ℕ) : ℝ) + 1 := by push_cast; linarith
    have h2 : (1 : ℝ) ≤ ((J + n : ℕ) : ℝ) + 1 := by
      have := (Nat.cast_nonneg (J + n) : (0 : ℝ) ≤ _); linarith
    have hj1 : (A₀ + n * C') ≤ (A₀ + C') * (((J + n : ℕ) : ℝ) + 1) := by
      have e1 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ A₀)
      have e2 := mul_le_mul_of_nonneg_left h1 hC'
      linarith
    calc (1 + Cw / W) ^ n * (A₀ + n * C')
        ≤ Real.exp (Cw * max T 0) * ((A₀ + C') * (((J + n : ℕ) : ℝ) + 1)) :=
          mul_le_mul hg hj1 (by positivity) (by positivity)
      _ = Real.exp (Cw * max T 0) * (A₀ + C') * (((J + n : ℕ) : ℝ) + 1) := by ring
      _ ≤ A * (((J + n : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_right hA (by positivity)

end Helpers

/-- **Clock moments of the open-inputs lemma, uniformly on `bulkInterval κ`**
(`OpenInputsProof.clock_moment_raw` with constants depending only on `(b, κ, q, T, P)`, and on
`r₀, J` for `A, G, W₀`). -/
theorem clock_moment_unif (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ) (hκ4 : κ < 4)
    {q : ℝ → ℝ} (hq : IsClockWeight q) (T : ℝ) {P : ℕ} (hP : 2 ≤ P) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r₀ : ℝ, 0 < r₀ → r₀ ≤ r₁ → ∀ J : ℕ, ∃ (A G : ℝ) (W₀ : ℕ), 0 ≤ A ∧
      1 ≤ G ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ D : Matrix (Fin W) (Fin W) ℂ,
        D.IsHermitian → ∀ j : ℕ, (j : ℝ) ≤ T * W →
        ∫⁻ ω, ENNReal.ofReal (clockU (oneEndedY b E q D j ω) ^ P) ∂oneEndedLaw W b j ≤
          ENNReal.ofReal ((A * ((j : ℝ) + 1)) ^ P) +
            ENNReal.ofReal (G ^ j) * oneEndedLaw W b j (goodSet b E D r₀ J j)ᶜ ^ (1 / 2 : ℝ) := by
  obtain ⟨-, hq0, Kq₀, hqK₀⟩ := hq
  have hqK : ∀ x, q x ≤ max Kq₀ 0 := fun x => (hqK₀ x).trans (le_max_left _ _)
  have hKq : 0 ≤ max Kq₀ 0 := le_max_right _ _
  obtain ⟨C₁, W₁, -, hcr1⟩ := crude_bound_unif hW1 hGA hb0 hb1 hκ hκ4 hKq (P := P) (by omega)
  obtain ⟨r₁, K, Cw, W₃, hr₁, hK, hwt⟩ := clockStep_weighted_unif hW1 hGA hTM hb0 hb1 hκ hκ4 hKq hP
  obtain ⟨C₂, W₂, -, hcr2⟩ := crude_bound_unif hW1 hGA hb0 hb1 hκ hκ4 hKq (P := 2 * P) (by omega)
  refine ⟨r₁, hr₁, fun r₀ hr₀ hr₀₁ J => ?_⟩
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
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hW2 : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hW3 : W₃ ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have hW0 : 0 < W := (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hcrude1 := crude_iter (q := q) (D := D) (b := b) (E := E) hq0 hqK
    (fun X hX Y hY w hw0 hw1 => hcr1 W hW0 hW1 E hEκ X hX Y hY w hw0 hw1) hD
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
    have h0 := entrance_weight_le (r₀ := r₀) hq0 hW0 hD hzpos hE hK hB₀0 hzB J P (by omega) (hcrude1 J)
    have hit := weighted_iter hq0 hqK hK hCw'0 hW0 (by omega) hwt' hD J hA₀1 hC'0 hPC h0 n
    rw [← lintegral_indicator hm]
    have hn : (n : ℝ) ≤ T * W := by
      have : (n : ℝ) ≤ ((J + n : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ J + n)
      linarith
    exact good_part_le hK hCw'0 hWr hA₀1 hC'0 hn hq0 (le_max_left _ _) hit

end MovingEnergy

end BlockBand.Endpoints.Clock
