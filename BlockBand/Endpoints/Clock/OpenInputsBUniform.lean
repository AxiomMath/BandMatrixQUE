module

public import BlockBand.Endpoints.Clock.OpenInputsBUniformClock
public import BlockBand.Endpoints.Clock.MovingEnergyLabels

/-!
# The open-inputs lemma on compact parameter sets: `OpenInputsMomentsBulk`

`openInputsMomentsBulk_of` proves `MovingEnergy.OpenInputsMomentsBulk`: `β, κ, T, q, p` first;
then `ε > 0`; for each `b ∈ Icc β (1/2-β)` there are `C, W₀`, uniform in `E ∈ bulkInterval κ` and
in Hermitian `‖D‖ ≤ ε`.

## Where `ε` comes from, and why it does not depend on `b`
The proof is that of `openInputsMomentsEnergyUniform_core` with `ε` chosen before `b`. As there,
`ε` is the radius of the entrance bound at the scalar radius `min r_s r₁`:
* `r_s` (`oneStepFacts_unifB`) is the radius of the deterministic `step_bound_unifB`;
* `r₁` (`clock_moment_unifB` from `clockStep_weighted_unifB`) is `min(r₀, dstar, 1, 1/(K+1))`
  with `r₀, q` from `step_bound_unifB`, `K = 2A₁/(1-q)`, `A₁ = (n+2)2^{n+2} max(C₁,0)` and
  `dstar ≤ min(dstar₀, 1/(2 max(C₁,0)+1))`, where `dstar₀, C₁` are the constants of
  `LayersBUniformHyp.weightedLayerClockMean` (via `onePortClockMeanB`); the
  `clockNoise`/`unrestricted` constant of `WeightedLayerContract` enters only the `1/W`
  coefficient `A₂` (`main_moment_unifB`), hence only `C` and `W₀`;
* the entrance (`entrance_bound_unifB`) turns the radius into `ε = r/(4C_J)` with `J, C_J` from
  the `zeParam`-uniform clauses of the zero-entrance lemma at `kappaBulkB β κ`.

Everything else (the constants `C₀, a₀, C₂, Cn` of `CavityMeanStatement`, the constants of
`GaussianAbsorptionContract` and `TraceMatrixContract`, the weighted-layer noise constants, the
crude-bound constants and every `W₀`) is chosen after `b` and enters only `C, W₀`.

Of `LayersBUniformHyp` only the field `weightedLayerClockMean` is used. The other hypotheses are
`GaussianAbsorptionContract`, `TraceMatrixContract` and `WeightedLayerContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof CavityMeanProb ZeroEntranceProb

/-- **The assembly at `0 < κ ≤ 1`**, with `ε` chosen before `b ∈ Icc β (1/2-β)` (the proof of
`openInputsMomentsEnergyUniform_core` with the `b`-uniform radii `r_s`, `r₁` and the
`b`-uniform entrance). Every real `p` is allowed: the jet clause is proved at order `max p 2`
and the clock clause at the integer order `⌈p⌉₊ + 2`, then lowered by monotonicity. -/
theorem openInputsMomentsBulk_core (hB : LayersBUniformHyp) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract) {β : ℝ} (hβ : 0 < β)
    (hβ4 : β < 1 / 4) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (T : ℝ) {q : ℝ → ℝ}
    (hq : IsClockWeight q) (p : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
          (∀ s : ℂ, IsStationaryJet b E s → ∀ j : ℕ, openEntranceTime W ≤ j →
              (j : ℝ) ≤ T * W →
              eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) +
                eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) ≤ ENNReal.ofReal (C / W)) ∧
          ∀ j : ℕ, (j : ℝ) ≤ T * W →
            eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
              ENNReal.ofReal (C * ((j : ℝ) + 1) / W) := by
  have hκ4 : κ < 4 := by linarith
  have hq0 : ∀ x, 0 ≤ q x := hq.2.1
  have hp'2 : 2 ≤ max p 2 := le_max_right _ _
  have hpp' : p ≤ max p 2 := le_max_left _ _
  have hP2 : 2 ≤ ⌈p⌉₊ + 2 := by omega
  have hpP : p ≤ ((⌈p⌉₊ + 2 : ℕ) : ℝ) := by
    have := Nat.le_ceil p
    push_cast; linarith
  obtain ⟨rs, qq, Cst, hrs, hFu⟩ := oneStepFacts_unifB (cavityMean_of hGA hTM) hβ hκ hκ1
  obtain ⟨r₁, hr₁, hclock⟩ := clock_moment_unifB hB hWL hGA hTM hβ hβ4 hκ hκ1 hq T hP2
  have hr₀ : 0 < min rs r₁ := lt_min hrs hr₁
  obtain ⟨J, ε, ae, Ke, We, hε, hae, hKe0, hent⟩ :=
    entrance_bound_unifB (zeroEntrance_of_contracts hGA hTM) hβ hκ hκ4 hr₀
  refine ⟨ε, hε, fun b hb => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  have hη0 := etaLow_pos hb1 hκ hκ4
  obtain ⟨C₀, a₀, hFb⟩ := hFu b hb
  obtain ⟨-, hqq0, hqq1, hCst, hC₀, ha₀, -⟩ := hFb 0 (zero_mem_bulkInterval hκ1)
  obtain ⟨A, G, Wc, hA, hG, hclk⟩ := hclock b hb (min rs r₁) hr₀ (min_le_right _ _) J
  have hθ0 : 0 < (1 + qq) / 2 := by linarith
  have hθ1 : (1 + qq) / 2 < 1 := by linarith
  have hlam0 : 0 < (1 - qq) / (2 * (Cst + 1)) := div_pos (by linarith) (by positivity)
  have hρ0 : 0 < (1 - qq) * min rs r₁ / 2 := by
    have : 0 < 1 - qq := by linarith
    positivity
  have ha : 0 < min a₀ ae := lt_min ha₀ hae
  have hKt0 : 0 ≤ max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) := hKe0.trans (le_max_left _ _)
  have hκ0 : 0 < max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1 := by
    positivity
  have hT'0 : 0 ≤ max T 0 := le_max_right _ _
  have hdS : 0 ≤ dStar b := by unfold dStar; have : 0 < 1 - b := by linarith
                               positivity
  have hB0 : 0 < 1 / etaLow b κ + 1 + (1 - qq) / (2 * (Cst + 1)) *
      (1 / etaLow b κ ^ 2 + dStar b) := by positivity
  obtain ⟨Wg, hWg⟩ := geom_small hθ0 hθ1 J
  obtain ⟨Wt1, hWt1⟩ := tail_small hB0 (by linarith : (0 : ℝ) ≤ max p 2) le_rfl hT'0 hκ0 ha
  obtain ⟨Wt2, hWt2⟩ := tail_small (B := 1) (m := 0) (L := G ^ (2 * ⌈max T 0⌉₊)) one_pos le_rfl
    (one_le_pow₀ hG) hT'0 hκ0 ha
  have hgap : 0 < 1 - (1 + qq) / 2 := by linarith
  refine ⟨max ((1 + 1 / ((1 - qq) / (2 * (Cst + 1)))) *
      ((1 / etaLow b κ + 1 + (1 - qq) / (2 * (Cst + 1)) *
          (1 / etaLow b κ ^ 2 + dStar b)) +
        (1 + (1 - qq) / (2 * (Cst + 1))) * C₀ * (1 + Real.sqrt (max p 2)) /
          (1 - (1 + qq) / 2) + 1)) (A + 1),
    max (max (max We Wc) (max Wg (max Wt1 Wt2)))
      (⌈2 / min a₀ ae⌉₊ + ⌈max p 2 / a₀⌉₊ + ⌈C₀ / ((1 - qq) * min rs r₁ / 2)⌉₊ + 1), ?_⟩
  intro W hW E hEκ D hD hDε
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have hBE := jetBound_le (d := dStar b) hη0 (etaLow_le_im hb1 hκ hEκ) hlam0.le
  have hF0 := (hFb E hEκ).mono hr₀ (min_le_left _ _)
  have hWe : We ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hW))
  have hWc : Wc ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hW))
  have hWg' : Wg ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hW))
  have hWt1' : Wt1 ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)))
  have hWt2' : Wt2 ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)))
  obtain ⟨hW1, hP2W, hPa₀, hPae, hp'a, hCW⟩ := large_W_facts ha ha₀ hρ0 (min_le_left _ _)
    (min_le_right _ _) hC₀ (le_trans (le_max_right _ _) hW)
  have hWr : (0 : ℝ) < W := by linarith
  have hW0 : 0 < W := by exact_mod_cast hWr
  have hρW : (1 - qq) * min rs r₁ / 2 + C₀ / (W : ℝ) ^ 2 ≤ (1 - qq) * min rs r₁ := by
    linarith
  have hentW := hent b hb W hWe E hEκ D hD hDε (min a₀ ae * W) hP2W hPae
  have hτ0 : 0 ≤ (1 + max T 0 * W) *
      ((max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1) / Real.sqrt W) ^
        (min a₀ ae * W) := by positivity
  have hβ' : ∀ j : ℕ, (j : ℝ) ≤ T * W →
      oneEndedLaw W b j (goodSet b E D (min rs r₁) J j)ᶜ ≤ ENNReal.ofReal ((1 + max T 0 * W) *
        ((max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1) / Real.sqrt W) ^
          (min a₀ ae * W)) := by
    intro j hj
    have hj' : (j : ℝ) ≤ max T 0 * W :=
      hj.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)
    refine (beta_bound hF0 hW0 hD J hρ0 hρW hP2W hPa₀ hentW hKe0
      (le_max_left _ _) (le_max_right _ _) j hj').trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (base_comp ha hWr) (by positivity)) (by positivity)
  refine ⟨fun s hs j hj0 hjT => ?_, fun j hjT => ?_⟩
  · obtain ⟨hJj0, hgeom⟩ := hWg W hWg'
    obtain ⟨n, rfl⟩ : ∃ n, j = J + n := ⟨j - J, by omega⟩
    have ht := hWt1 W hWt1'
    rw [one_pow, mul_one, mul_assoc] at ht
    have hroot := tail_root_le hB0 hWr hτ0 (by linarith) ht
    have hτp := (mul_le_mul_of_nonneg_right hBE (Real.rpow_nonneg hτ0 (1 / max p 2))).trans
      hroot
    refine (jet_final hF0 hW0 hW1 hD hzpos hE hs J n hpp' hp'2 hp'a hτ0 (hgeom n hj0)
      (hβ' (J + n) hjT) hτp).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right (le_trans ?_ (le_max_left _ _)) hWr.le
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  · have hjN : j ≤ ⌈max T 0⌉₊ * W := by
      have h1 : (j : ℝ) ≤ max T 0 * W :=
        hjT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)
      have h2 : max T 0 * W ≤ (⌈max T 0⌉₊ : ℝ) * W :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hWr.le
      exact_mod_cast h1.trans h2
    have ht := hWt2 W hWt2'
    rw [Real.rpow_zero, one_mul, mul_assoc] at ht
    have hGτ := clock_tail_le hG hτ0 hjN ht
    refine (clock_final hW0 hq0 j (by omega) hpP hA hτ0 (hclk W hWc E hEκ D hD j hjT)
      (hβ' j hjT) (by linarith) hGτ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **The input moments of the open-inputs lemma on compact parameter sets**
(`MovingEnergy.OpenInputsMomentsBulk`), with `ε` depending only on `(β, κ, T, q, p)` and `C, W₀`
depending on `b`, uniform in `E ∈ bulkInterval κ` and in Hermitian `‖D‖ ≤ ε`. Proved from
`LayersBUniformHyp` (field `weightedLayerClockMean` only), `GaussianAbsorptionContract`,
`TraceMatrixContract` and `WeightedLayerContract`.
-/
theorem openInputsMomentsBulk_of (hB : LayersBUniformHyp) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract) : OpenInputsMomentsBulk := by
  intro β κ hβ hβ4 hκ T q hq p _hp
  obtain ⟨ε, hε, h⟩ := openInputsMomentsBulk_core hB hGA hTM hWL hβ hβ4 (lt_min hκ one_pos)
    (min_le_right κ 1) T hq p
  refine ⟨ε, hε, fun b hb => ?_⟩
  obtain ⟨C, W₀, hC⟩ := h b hb
  exact ⟨C, W₀, fun W hW E hE => hC W hW E (bulkInterval_mono (min_le_left κ 1) hE)⟩

end MovingEnergy

end BlockBand.Endpoints.Clock
