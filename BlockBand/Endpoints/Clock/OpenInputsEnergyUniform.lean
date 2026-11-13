module

public import BlockBand.Endpoints.Clock.OpenInputsEnergyUniformClock
public import BlockBand.Endpoints.Clock.OpenInputsEnergyUniformEntrance
public import BlockBand.Endpoints.Clock.MovingEnergyLabels

/-!
# The open-inputs lemma, energy-uniform at fixed `b`

`OpenInputsMomentsEnergyUniform` is `OpenInputsMoments` with the energy quantifier `-2 < E < 2`
replaced by `κ > 0` before the constants and `E ∈ bulkInterval κ` after `W ≥ W₀` (the two clauses
are unchanged). `b`, `T`, `q`, `p` are still fixed before the constants; the `b`-uniform form is
`OpenInputsMomentsBulk`.

`openInputsMomentsEnergyUniform_of` proves it from the same three contracts as
`OpenInputsProof.openInputsMoments_of`:
* `GaussianAbsorptionContract` (the Gaussian absorption lemma),
* `TraceMatrixContract` (the trace-matrix lemma),
* `WeightedLayerContract` (the weighted-layer lemma, through `onePortWeighted_of`),
via the cavity-mean lemma (`cavityMean_of`) and the zero-entrance lemma
(`zeroEntrance_of_contracts`).

## Structure (the steps of the paper's proof)
* `…Step`: Steps 2–5 (`step_bound_unif`, `oneStepFacts_unif`, `delta_next_unif`).
* `…ClockStep`: Step 6 (`ingredients_unif`, `crude_bound_unif`, `main_moment_unif`,
  `clockStep_weighted_unif`).
* `…Clock`: Steps 6–7 iterated (`clock_moment_unif`).
* `…Entrance`: Step 1 (`entrance_bound_unif`).
* this file: the assembly (`openInputsMoments_of` with `E` introduced after the constants), and
  the adapter `openInputsMoments_of_energyUniform`.

## The constants (all chosen after `κ`; reduction to `κ ≤ 1`)
`κ` is first replaced by `min κ 1` (`bulkInterval` is antitone in `κ`), so `0 < κ ≤ 1 < 4`.
The radius of `D` is `ε` of `entrance_bound_unif` at the scalar radius `min r_s r₁`, with `r_s`
from `oneStepFacts_unif` (worst case of `step_bound` on `bulkInterval κ`) and `r₁` from
`clock_moment_unif` (`clockStep_weighted_unif`, from the `E`-uniform `OnePortWeighted` and
`delta_next_unif`). The `E`-dependent deterministic jet bound
`B(E) = (Im z)⁻¹ + 1 + λ((Im z)⁻² + d_*)` is dominated by its value at `Im z = η_κ = etaLow b κ`.
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

/-- **The input moments of the open-inputs lemma, uniformly in the energy** (`b` fixed).
`b, κ, T, q, p` first; then `ε > 0`, `C`, `W₀`; for every `W ≥ W₀`, every `E ∈ bulkInterval κ`
and every Hermitian initial `X₀ = D` with `‖D‖ ≤ ε` (operator norm; `Y₀ = 0`) the two clauses of
`OpenInputsMoments` hold.
-/
def OpenInputsMomentsEnergyUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (T : ℝ) (q : ℝ → ℝ), IsClockWeight q →
    ∀ p : ℝ, 1 ≤ p → ∃ (ε C : ℝ) (W₀ : ℕ), 0 < ε ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
          (∀ s : ℂ, IsStationaryJet b E s → ∀ j : ℕ, openEntranceTime W ≤ j →
              (j : ℝ) ≤ T * W →
              eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) +
                eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal p)
                  (oneEndedLaw W b j) ≤ ENNReal.ofReal (C / W)) ∧
          ∀ j : ℕ, (j : ℝ) ≤ T * W →
            eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
              ENNReal.ofReal (C * ((j : ℝ) + 1) / W)

/-- `bulkInterval` is antitone in `κ`. -/
theorem bulkInterval_mono {κ κ' : ℝ} (h : κ' ≤ κ) {E : ℝ} (hE : E ∈ bulkInterval κ) :
    E ∈ bulkInterval κ' :=
  ⟨by linarith [hE.1], by linarith [hE.2]⟩

/-- `0 ∈ bulkInterval κ` for `κ ≤ 1`. -/
theorem zero_mem_bulkInterval {κ : ℝ} (h : κ ≤ 1) : (0 : ℝ) ∈ bulkInterval κ :=
  ⟨by linarith, by linarith⟩

/-- The deterministic jet bound `B(E)` of the fixed-energy proof is dominated by its value at the
worst imaginary part `η ≤ Im z`. -/
theorem jetBound_le {η y lam d : ℝ} (hη : 0 < η) (hy : η ≤ y) (hlam : 0 ≤ lam) :
    1 / y + 1 + lam * (1 / y ^ 2 + d) ≤ 1 / η + 1 + lam * (1 / η ^ 2 + d) := by
  have h1 : 1 / y ≤ 1 / η := one_div_le_one_div_of_le hη hy
  have h2 : 1 / y ^ 2 ≤ 1 / η ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hη.le hy 2)
  have h3 := mul_le_mul_of_nonneg_left (by linarith : 1 / y ^ 2 + d ≤ 1 / η ^ 2 + d) hlam
  linarith

/-- **The assembly at `0 < κ ≤ 1`** (`openInputsMoments_of` with the energy
introduced after the constants). Every real `p` is allowed here: the jet clause is proved at
order `max p 2` and the clock clause at the integer order `⌈p⌉₊ + 2`, then lowered by
monotonicity of `L^p` norms (as in the fixed-energy proof). -/
theorem openInputsMomentsEnergyUniform_core (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (T : ℝ) {q : ℝ → ℝ}
    (hq : IsClockWeight q) (p : ℝ) :
    ∃ (ε C : ℝ) (W₀ : ℕ), 0 < ε ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
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
  have hη0 := etaLow_pos hb1 hκ hκ4
  obtain ⟨rs, qq, Cst, C₀, a₀, hFu⟩ := oneStepFacts_unif (cavityMean_of hGA hTM) hb0 hb1 hκ hκ4
  obtain ⟨r₁, hr₁, hclock⟩ := clock_moment_unif (onePortWeighted_of hWL hGA) hGA hTM hb0 hb1 hκ
    hκ4 hq T hP2
  obtain ⟨hrs, hqq0, hqq1, hCst, hC₀, ha₀, -⟩ := hFu 0 (zero_mem_bulkInterval hκ1)
  have hr₀ : 0 < min rs r₁ := lt_min hrs hr₁
  obtain ⟨J, ε, ae, Ke, We, hε, hae, hKe0, hent⟩ :=
    entrance_bound_unif (zeroEntrance_of_contracts hGA hTM) hb0 hb1 hκ hκ4 hr₀
  obtain ⟨A, G, Wc, hA, hG, hclk⟩ := hclock (min rs r₁) hr₀ (min_le_right _ _) J
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
  refine ⟨ε, max ((1 + 1 / ((1 - qq) / (2 * (Cst + 1)))) *
      ((1 / etaLow b κ + 1 + (1 - qq) / (2 * (Cst + 1)) *
          (1 / etaLow b κ ^ 2 + dStar b)) +
        (1 + (1 - qq) / (2 * (Cst + 1))) * C₀ * (1 + Real.sqrt (max p 2)) /
          (1 - (1 + qq) / 2) + 1)) (A + 1),
    max (max (max We Wc) (max Wg (max Wt1 Wt2)))
      (⌈2 / min a₀ ae⌉₊ + ⌈max p 2 / a₀⌉₊ + ⌈C₀ / ((1 - qq) * min rs r₁ / 2)⌉₊ + 1), hε, ?_⟩
  intro W hW E hEκ D hD hDε
  obtain ⟨hE0, hE1⟩ := mem_bulk_lt hκ hEκ
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have hBE := jetBound_le (d := dStar b) hη0 (etaLow_le_im hb1 hκ hEκ) hlam0.le
  have hF0 := (hFu E hEκ).mono hr₀ (min_le_left _ _)
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
  have hentW := hent W hWe E hEκ D hD hDε (min a₀ ae * W) hP2W hPae
  have hτ0 : 0 ≤ (1 + max T 0 * W) *
      ((max Ke (C₀ / ((1 - qq) * min rs r₁ / 2)) * Real.sqrt (min a₀ ae) + 1) / Real.sqrt W) ^
        (min a₀ ae * W) := by positivity
  have hβ : ∀ j : ℕ, (j : ℝ) ≤ T * W →
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
      (hβ (J + n) hjT) hτp).trans (ENNReal.ofReal_le_ofReal ?_)
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
    refine (clock_final hW0 hq0 j (by omega) hpP hA hτ0 (hclk W hWc E hEκ D hD j hjT) (hβ j hjT)
      (by linarith) hGτ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **The input moments, uniformly in `E ∈ bulkInterval κ` at fixed `b`**, proved from
`GaussianAbsorptionContract`, `TraceMatrixContract` and `WeightedLayerContract`.
-/
theorem openInputsMomentsEnergyUniform_of (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) (hWL : WeightedLayerContract) :
    OpenInputsMomentsEnergyUniform := by
  intro b hb0 hb1 κ hκ T q hq p hp
  obtain ⟨ε, C, W₀, hε, h⟩ := openInputsMomentsEnergyUniform_core hGA hTM hWL hb0 hb1
    (lt_min hκ one_pos) (min_le_right κ 1) T hq p
  exact ⟨ε, C, W₀, hε, fun W hW E hE => h W hW E (bulkInterval_mono (min_le_left κ 1) hE)⟩

/-- `OpenInputsMomentsEnergyUniform` implies the fixed-energy statement
`OpenInputsMoments` (with `κ` from `MovingEnergy.exists_kappa`). -/
theorem openInputsMoments_of_energyUniform (h : OpenInputsMomentsEnergyUniform) :
    OpenInputsMoments := by
  intro b hb0 hb1 E hE0 hE1 T q hq p hp
  obtain ⟨κ, hκ, hE⟩ := exists_kappa hE0 hE1
  obtain ⟨ε, C, W₀, hε, hC⟩ := h b hb0 hb1 κ hκ T q hq p hp
  exact ⟨ε, C, W₀, hε, fun W hW D hD hDε => hC W hW E hE D hD hDε⟩

end MovingEnergy

end BlockBand.Endpoints.Clock
