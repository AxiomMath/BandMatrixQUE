module

public import BlockBand.Endpoints.Clock.ClockMixingRecursion

/-!
# The clock-mixing lemma: complete clock source mixing on the one-ended path

We prove the clock-mixing bound `‖Z_j‖_p + ‖√S_j‖_p ≤ C W^{-1/2}` on the one-ended path from three
hypotheses (`clockMixing_of`).

## Statement (`ClockMixingBound`)

Fixed `0 < b < 1/2`, bulk `-2 < E < 2`, horizon `T`, admissible clock weight `q` and moment
order `p ≥ 1`; then `C = C_{p,T,q}` and `W₀`; for `W ≥ W₀` and every `j₀ ≤ j ≤ TW`
(`j₀ = ⌈(log W)²⌉`), for the one-ended path with `X_0 = 0`, `Y_0 = 0`:
`‖Z_j‖_p + ‖√S_j‖_p ≤ C W^{-1/2}`, `Z_j = Tr(Q_j^q f(X_j))`,
`S_j = Tr(Q_j^q f(X_j) Q_j^q f(X_j)*)`, `f(X) = (z-X)⁻¹ - (z-z̄)⁻¹I`. `L^p` norms are under
the law of the first `j` fresh layers. `ClockMixingUniformBound` is the same, uniformly in a
deterministic Hermitian initial `X_0 = D` with `‖D‖ ≤ ε` (as in `OpenInputsMoments`).

## Hypotheses (`clockMixing_of`)

* `PassiveSourceMixingContract`, only `oneStepMean` and `oneStepFluctuation`. On the one-ended path
  every `X_j` is Hermitian, so the passive mass `q(X) = Tr R*(-Im X)R` vanishes and `oneStepMean`
  gives `E(T₊|𝓕) = θ_* f(X) + R`, `‖R‖ ≤ C(δ₀ + δ₁ + W⁻²)`; `|θ_*| < 1` is
  `norm_thetaStar_lt_one`.
* `GaussianAbsorptionContract` (constructed by `Layers.gaussianAbsorption_holds` from
  `ConditionalBlockGUECount`): the fresh bound `‖‖𝒢‖‖_{2p} ≤ C`, which gives the injection
  estimate `‖Tr C₊‖_p ≤ CW`.
* `OpenInputsMoments`, the input moments of the one-ended path, at moment order `2p` (proved from
  `GaussianAbsorptionContract`, `TraceMatrixContract` and `WeightedLayerContract` as
  `openInputsMoments_of`).

## Proof

Condition on the past (`ClockMixingProb.eLpNorm_initLast_le`), split
`T₊ = θ f + (E T₊ - θ f) + (T₊ - E T₊)`, Minkowski over the eigenbasis of `Q`
(`condTrace_le`, `condHS_le`), the injection identity (`hsSandwich_add_le_injection`), Hölder on
the jet errors, the geometric recursion with `|θ| < 1` (`geom_bound`) and the trivial initial
bound `|Z|, √S ≤ ‖f‖γ` at `j₀` with `(j₀+1)/W ≤ 18 W^{-1/2}`. The scalar exceptional sets of
the paper's proof do not appear: `oneStepMean` and `oneStepFluctuation` are uniform in the Hermitian past,
and `OpenInputsMoments` is unstopped.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexConjugate Matrix Matrix.Norms.L2Operator ComplexOrder

/-- **The clock-mixing lemma**, uniform in a small
deterministic Hermitian initial matrix `X_0 = D` (`‖D‖ ≤ ε`, operator norm). For fixed
`0 < b < 1/2`, bulk `-2 < E < 2`, `T`, admissible `q` and `p ≥ 1`, there are `ε > 0`, `C`
and `W₀` such that for `W ≥ W₀`, `j₀ = ⌈(log W)²⌉ ≤ j ≤ TW`:
`‖Z_j‖_p + ‖√S_j‖_p ≤ C W^{-1/2}`. -/
def ClockMixingUniformBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (q : ℝ → ℝ),
    IsClockWeight q → ∀ p : ℝ, 1 ≤ p →
      ∃ (ε C : ℝ) (W₀ : ℕ), 0 < ε ∧ ∀ W : ℕ, W₀ ≤ W →
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
          ∀ j : ℕ, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W →
            eLpNorm (openClockZ b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) +
                eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
              ENNReal.ofReal (C / Real.sqrt W)

/-- **The clock-mixing lemma** on
the one-ended path with `X_0 = 0`, `Y_0 = 0`. For every fixed finite `p ≥ 1`
(and fixed `0 < b < 1/2`, bulk `E`, `T`, admissible `q`), uniformly on `j₀ ≤ j ≤ TW` for
`W ≥ W₀`: `‖Z_j‖_p + ‖√S_j‖_p ≤ C_{p,T,q} W^{-1/2}`. -/
def ClockMixingBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (q : ℝ → ℝ),
    IsClockWeight q → ∀ p : ℝ, 1 ≤ p →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        ∀ j : ℕ, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W →
          eLpNorm (openClockZ b E q (0 : Matrix (Fin W) (Fin W) ℂ) j) (ENNReal.ofReal p)
              (oneEndedLaw W b j) +
            eLpNorm (openClockSqrtS b E q (0 : Matrix (Fin W) (Fin W) ℂ) j) (ENNReal.ofReal p)
              (oneEndedLaw W b j) ≤
            ENNReal.ofReal (C / Real.sqrt W)

namespace ClockMixingProb

open ClockMixingAlg

/-- Hölder with exponents `(2p, 2p; p)`. -/
theorem eLpNorm_mul_le_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun x => f x * g x) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ := by
  have : ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := ENNReal.ofReal (2 * p))
    (q := ENNReal.ofReal (2 * p)) (r := ENNReal.ofReal p) (fun a c : ℝ => a * c) 1
    continuous_mul hf hg (Filter.Eventually.of_forall fun x => by simp [norm_mul])
  simpa using h

/-- `(j₀ + 1)/W ≤ 18 W^{-1/2}` for `W ≥ 1`, `j₀ = ⌈(log W)²⌉`. -/
theorem entrance_le {W : ℕ} (hW : 1 ≤ (W : ℝ)) :
    ((openEntranceTime W : ℝ) + 1) / W ≤ 18 / Real.sqrt W := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hs1 : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW
  have hlog : Real.log W ≤ 4 * (W : ℝ) ^ (1 / 4 : ℝ) := by
    have := Real.log_le_rpow_div hW0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [show (W : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (W : ℝ) ^ (1 / 4 : ℝ) by ring]
  have hpow : ((W : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, Real.sqrt_eq_rpow]
    norm_num
  have hlog2 : Real.log W ^ 2 ≤ 16 * Real.sqrt W := by
    have h1 : Real.log W ^ 2 ≤ (4 * (W : ℝ) ^ (1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    rw [mul_pow, hpow] at h1
    linarith
  have hceil : (openEntranceTime W : ℝ) < Real.log W ^ 2 + 1 :=
    Nat.ceil_lt_add_one (sq_nonneg _)
  have hnum : (openEntranceTime W : ℝ) + 1 ≤ 18 * Real.sqrt W := by linarith
  have hsW : 0 < Real.sqrt W := by linarith
  rw [div_le_div_iff₀ hW0 hsW]
  calc ((openEntranceTime W : ℝ) + 1) * Real.sqrt W ≤ 18 * Real.sqrt W * Real.sqrt W :=
        mul_le_mul_of_nonneg_right hnum hsW.le
    _ = 18 * W := by rw [mul_assoc, Real.mul_self_sqrt hW0.le]

/-- `(i+1)/W ≤ |T| + 1` for `i ≤ TW`, `W ≥ 1`. -/
theorem time_le {W : ℕ} (hW : 1 ≤ (W : ℝ)) {T : ℝ} {i : ℕ} (hi : (i : ℝ) ≤ T * W) :
    ((i : ℝ) + 1) / W ≤ |T| + 1 := by
  have hW0 : (0 : ℝ) < W := by linarith
  rw [div_le_iff₀ hW0]
  have : T * W ≤ |T| * W := mul_le_mul_of_nonneg_right (le_abs_self T) hW0.le
  nlinarith

variable {W : ℕ} {b E : ℝ} {q : ℝ → ℝ} {D : Matrix (Fin W) (Fin W) ℂ}

/-- The trivial bounds at `j₀`: `|Z_j|, √S_j ≤ ‖f‖ γ_j`. -/
theorem init_bound (hD : D.IsHermitian) (hq0 : ∀ x, 0 ≤ q x) (hz : 0 < (boundaryZ b E).im)
    (j : ℕ) (p : ℝ≥0∞) :
    eLpNorm (openClockZ b E q D j) p (oneEndedLaw W b j) ≤
        ENNReal.ofReal ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) *
          eLpNorm (oneEndedGamma b E q D j) p (oneEndedLaw W b j) ∧
      eLpNorm (openClockSqrtS b E q D j) p (oneEndedLaw W b j) ≤
        ENNReal.ofReal ((boundaryZ b E).im⁻¹ + ‖cZero b E‖) *
          eLpNorm (oneEndedGamma b E q D j) p (oneEndedLaw W b j) := by
  set Kf := (boundaryZ b E).im⁻¹ + ‖cZero b E‖
  have hKf : 0 ≤ Kf := by positivity
  have hpt : ∀ᵐ x ∂oneEndedLaw W b j,
      ‖openClockZ b E q D j x‖ ≤ Kf * oneEndedGamma b E q D j x ∧
        ‖openClockSqrtS b E q D j x‖ ≤ Kf * oneEndedGamma b E q D j x := by
    refine (ae_blocks_isHermitian b j).mono fun x hx => ?_
    have hX := X_isHermitian E hD j x hx
    have hQ := Q_posSemidef b E hq0 D j x
    have hf := norm_passiveF_le b E hz hX
    have hγ : 0 ≤ oneEndedGamma b E q D j x := trace_re_nonneg hQ
    refine ⟨?_, ?_⟩
    · refine (norm_trace_mul_le hQ _).trans ?_
      exact mul_le_mul_of_nonneg_right hf hγ
    · rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ openClockSqrtS b E q D j x from
        hsSandwich_nonneg _ _)]
      exact (hsSandwich_le hQ _).trans (mul_le_mul_of_nonneg_right hf hγ)
  refine ⟨?_, ?_⟩
  · refine (eLpNorm_mono_ae_real (meas_openClockZ b E q D j).aestronglyMeasurable
      (hpt.mono fun x hx => hx.1)).trans ?_
    rw [eLpNorm_real_mul_le, abs_of_nonneg hKf]
  · refine (eLpNorm_mono_ae_real (meas_openClockSqrtS b E q D j).aestronglyMeasurable
      (hpt.mono fun x hx => hx.2)).trans ?_
    rw [eLpNorm_real_mul_le, abs_of_nonneg hKf]

/-- The error weight in `L^p`, by Hölder and the input moments `OpenInputsMoments` at order `2p`. -/
theorem errWeight_le {s : ℂ} {Cm c Co G p : ℝ} (hCm : 0 ≤ Cm) (hc : 0 ≤ c) (hCo : 0 ≤ Co)
    (hG : 0 ≤ G) (hp : 1 ≤ p) (j : ℕ)
    (hδ : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal (2 * p))
        (oneEndedLaw W b j) +
      eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal (2 * p))
        (oneEndedLaw W b j) ≤ ENNReal.ofReal Co)
    (hγ : eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal (2 * p)) (oneEndedLaw W b j) ≤
      ENNReal.ofReal G) :
    eLpNorm (errWeight b E q D s Cm c j) (ENNReal.ofReal p) (oneEndedLaw W b j) ≤
      ENNReal.ofReal (Cm * (Co * G) + Cm * (Co * G) + (Cm * (W : ℝ)⁻¹ ^ 2 + c) * G) := by
  set μ := oneEndedLaw W b j
  set d0 : (Fin j → OneEndedLayer W) → ℝ := fun ω => jetDistance0 b E (oneEndedX E D j ω)
  set d1 : (Fin j → OneEndedLayer W) → ℝ := fun ω => jetDistance1 b E s (oneEndedX E D j ω)
  set γ := oneEndedGamma b E q D j
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hd0 : eLpNorm d0 (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal Co := le_trans le_self_add hδ
  have hd1 : eLpNorm d1 (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal Co := le_trans le_add_self hδ
  have hd0m := aestronglyMeasurable_of_eLpNorm_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd0)
  have hd1m := aestronglyMeasurable_of_eLpNorm_ne_top
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd1)
  have hγm : AEStronglyMeasurable γ μ := (meas_gamma b E q D j).aestronglyMeasurable
  have hK2 : 0 ≤ Cm * (W : ℝ)⁻¹ ^ 2 + c := by positivity
  set F1 : (Fin j → OneEndedLayer W) → ℝ := fun x => Cm * (d0 x * γ x) with hF1
  set F2 : (Fin j → OneEndedLayer W) → ℝ := fun x => Cm * (d1 x * γ x) with hF2
  set F3 : (Fin j → OneEndedLayer W) → ℝ := fun x => (Cm * (W : ℝ)⁻¹ ^ 2 + c) * γ x with hF3
  have hfun : errWeight b E q D s Cm c j = F1 + F2 + F3 := by
    funext x
    simp only [errWeight, Pi.add_apply, F1, F2, F3, d0, d1, γ]
    ring
  rw [hfun]
  have e1 := eLpNorm_add_le (μ := μ) (f := F1 + F2) (g := F3) hp1
  have e2 := eLpNorm_add_le (μ := μ) (f := F1) (g := F2) hp1
  have hγp : eLpNorm γ (ENNReal.ofReal p) μ ≤ ENNReal.ofReal G :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans hγ
  have b1 : eLpNorm F1 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cm * (Co * G)) := by
    rw [hF1, eLpNorm_real_mul_le, abs_of_nonneg hCm, ENNReal.ofReal_mul hCm,
      ENNReal.ofReal_mul hCo]
    gcongr
    exact (eLpNorm_mul_le_two hd0m hγm hp0).trans (mul_le_mul' hd0 hγ)
  have b2 : eLpNorm F2 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (Cm * (Co * G)) := by
    rw [hF2, eLpNorm_real_mul_le, abs_of_nonneg hCm, ENNReal.ofReal_mul hCm,
      ENNReal.ofReal_mul hCo]
    gcongr
    exact (eLpNorm_mul_le_two hd1m hγm hp0).trans (mul_le_mul' hd1 hγ)
  have b3 : eLpNorm F3 (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((Cm * (W : ℝ)⁻¹ ^ 2 + c) * G) := by
    rw [hF3, eLpNorm_real_mul_le, abs_of_nonneg hK2, ENNReal.ofReal_mul hK2]
    gcongr
  refine e1.trans ((add_le_add (e2.trans (add_le_add b1 b2)) b3).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end ClockMixingProb

/-!
## The theorem
-/

open ClockMixingAlg ClockMixingProb in

/-- **The clock-mixing bound, uniform in the initial matrix** (`ClockMixingUniformBound`), from
`PassiveSourceMixingContract` (`oneStepMean`, `oneStepFluctuation`), `GaussianAbsorptionContract`
and `OpenInputsMoments`.
-/
theorem clockMixingUniform_of (hPSM : PassiveSourceMixingContract)
    (hGA : GaussianAbsorptionContract) (hOI : OpenInputsMoments) : ClockMixingUniformBound := by
  intro b hb0 hb1 E hE1 hE2 T q hq p hp
  have hE : |E| < 2 := abs_lt.mpr ⟨hE1, hE2⟩
  have hz : 0 < (boundaryZ b E).im := by
    rw [BlockBand.Layers.boundaryZ_im hE.le]
    have := BlockBand.Layers.matchedA_im_neg hE
    nlinarith
  set Kf := (boundaryZ b E).im⁻¹ + ‖cZero b E‖ with hKfdef
  have hKf : 0 ≤ Kf := by positivity
  obtain ⟨hqc, hq0, Kq, hqK⟩ := hq
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  obtain ⟨⟨s, hs⟩, hmeanAll⟩ := hPSM.oneStepMean b hb0 hb1 E hE1 hE2
  obtain ⟨Cm, Wm, hm⟩ := hmeanAll s hs
  set θ := thetaStar b E s with hθdef
  have hθ : ‖θ‖ < 1 := norm_thetaStar_lt_one hb0 hb1 hE1 hE2 hs
  have hθ0 : 0 ≤ ‖θ‖ := norm_nonneg _
  obtain ⟨Cf, Wf, hf⟩ := hPSM.oneStepFluctuation b hb0 hb1 E hE1 hE2 (max p 2)
    (le_trans hp (le_max_left _ _))
  obtain ⟨ε₁, Cg, hε₁, hCg, hga⟩ := hGA b hb0 hb1 (boundaryZ b E).im ‖boundaryZ b E‖ hz
  obtain ⟨ε, Co, Wo, hε, hoi⟩ := hOI b hb0 hb1 E hE1 hE2 T q ⟨hqc, hq0, Kq, hqK⟩ (2 * p)
    (by linarith)
  set Cm' := max Cm 0
  set Cf' := max Cf 0
  set Co' := max Co 0
  have hCm' : 0 ≤ Cm' := le_max_right _ _
  have hCf' : 0 ≤ Cf' := le_max_right _ _
  have hCo' : 0 ≤ Co' := le_max_right _ _
  set Tb := |T| + 1
  have hTb : 0 ≤ Tb := by positivity
  set H0 := Cm' * (Co' * (Co' * Tb)) + Cm' * (Co' * (Co' * Tb)) + (Cm' + Cf') * (Co' * Tb)
  set FZ := H0 + Kf * Kq * Cg ^ 2
  set FS := H0 + Kf * Kq * Cg ^ 2 + Kf * (Co' * Tb)
  set A0 := Kf * (Co' * 18)
  have hH0 : 0 ≤ H0 := by positivity
  have hFZ : 0 ≤ FZ := by positivity
  have hFS : 0 ≤ FS := by positivity
  have hA0 : 0 ≤ A0 := by positivity
  have h1θ : 0 < 1 - ‖θ‖ := by linarith
  refine ⟨ε, (A0 + FZ / (1 - ‖θ‖)) + (A0 + FS / (1 - ‖θ‖)),
    max (max (max Wm Wf) Wo) (max 1 ⌈2 * p / ε₁⌉₊), hε, ?_⟩
  intro W hW D hD hDε j hj0 hjT
  have hWm : Wm ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hW)
  have hWf : Wf ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hW)
  have hWo : Wo ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
  have hW1n : 1 ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hWc : ⌈2 * p / ε₁⌉₊ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1n
  have hW0 : (0 : ℝ) < W := by linarith
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
  have hs1 : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  have hinvW : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := by
    rw [inv_le_inv₀ hW0 hsW]
    calc Real.sqrt W ≤ Real.sqrt W * Real.sqrt W := le_mul_of_one_le_right hsW.le hs1
      _ = W := Real.mul_self_sqrt hW0.le
  have hinvW2 : (W : ℝ)⁻¹ ^ 2 ≤ (Real.sqrt W)⁻¹ := by
    have : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
      rw [sq]; exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hW1)
    exact this.trans hinvW
  have h2p : 2 * p ≤ ε₁ * W := by
    have h1 : 2 * p / ε₁ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWc)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  -- the one-layer hypotheses at this width
  have H : StepHyp W b E θ s Cm' Cf' Cg p := by
    refine ⟨fun X hX => ?_, fun X hX u v => ?_, fun X hX => ?_⟩
    · have h := hm W hWm X (passiveY_posSemidef hX)
      rw [passiveMass_eq_zero b E hX] at h
      simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero, div_one] at h
      refine h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
      unfold jetDistance0 jetDistance1
      positivity
    · refine (hf W hWf X (passiveY_posSemidef hX) u v).2.trans (ENNReal.ofReal_le_ofReal ?_)
      have hu : 0 ≤ vecNorm u := Real.sqrt_nonneg _
      have hv : 0 ≤ vecNorm v := Real.sqrt_nonneg _
      gcongr
      exact le_max_left _ _
    · exact (hga W (by exact_mod_cast hW1n) .oneBlockOnePort (physEmbed X)
        (physEmbed_isHermitian hX) E (boundaryZ b E) le_rfl le_rfl).2 (2 * p) (by linarith) h2p
  obtain ⟨hδ, hγ⟩ := hoi W hWo D hD hDε
  -- ranges
  set N := ⌊T * W⌋₊
  have hTW0 : 0 ≤ T * W := le_trans (Nat.cast_nonneg j) hjT
  have hjN : j ≤ N := Nat.le_floor hjT
  have hiT : ∀ i, i ≤ N → (i : ℝ) ≤ T * W := fun i hi =>
    le_trans (by exact_mod_cast hi) (Nat.floor_le hTW0)
  have hγ2 : ∀ i, i ≤ N →
      eLpNorm (oneEndedGamma b E q D i) (ENNReal.ofReal (2 * p)) (oneEndedLaw W b i) ≤
        ENNReal.ofReal (Co' * Tb) := by
    intro i hi
    refine (hγ i (hiT i hi)).trans (ENNReal.ofReal_le_ofReal ?_)
    have ht := time_le hW1 (hiT i hi)
    calc Co * ((i : ℝ) + 1) / W ≤ Co' * (((i : ℝ) + 1) / W) := by
          rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ Co' * Tb := mul_le_mul_of_nonneg_left ht hCo'
  have hγp : ∀ i, i ≤ N →
      eLpNorm (oneEndedGamma b E q D i) (ENNReal.ofReal p) (oneEndedLaw W b i) ≤
        ENNReal.ofReal (Co' * Tb) := fun i hi =>
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans (hγ2 i hi)
  have hEW : ∀ i, openEntranceTime W ≤ i → i ≤ N →
      eLpNorm (errWeight b E q D s Cm' (Cf' / Real.sqrt W) i) (ENNReal.ofReal p)
        (oneEndedLaw W b i) ≤ ENNReal.ofReal (H0 / Real.sqrt W) := by
    intro i hi0 hiN
    have hδi : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D i ω)) (ENNReal.ofReal (2 * p))
          (oneEndedLaw W b i) +
        eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D i ω)) (ENNReal.ofReal (2 * p))
          (oneEndedLaw W b i) ≤ ENNReal.ofReal (Co' / W) :=
      (hδ s hs i hi0 (hiT i hiN)).trans (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
    refine (errWeight_le hCm' (by positivity) (by positivity) (by positivity) hp i hδi
      (hγ2 i hiN)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc1 : Co' / W ≤ Co' / Real.sqrt W := by
      rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hinvW hCo'
    have e1 : Cm' * (Co' / W * (Co' * Tb)) ≤ Cm' * (Co' * (Co' * Tb)) / Real.sqrt W := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hCm'
      calc Co' / W * (Co' * Tb) ≤ Co' / Real.sqrt W * (Co' * Tb) :=
            mul_le_mul_of_nonneg_right hc1 (by positivity)
        _ = Co' * (Co' * Tb) / Real.sqrt W := by ring
    have e3 : (Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W) * (Co' * Tb) ≤
        (Cm' + Cf') * (Co' * Tb) / Real.sqrt W := by
      have : Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W ≤ (Cm' + Cf') / Real.sqrt W := by
        rw [add_div, div_eq_mul_inv Cm']
        exact add_le_add (mul_le_mul_of_nonneg_left hinvW2 hCm') le_rfl
      calc (Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W) * (Co' * Tb)
          ≤ (Cm' + Cf') / Real.sqrt W * (Co' * Tb) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = _ := by ring
    calc Cm' * (Co' / W * (Co' * Tb)) + Cm' * (Co' / W * (Co' * Tb)) +
          (Cm' * (W : ℝ)⁻¹ ^ 2 + Cf' / Real.sqrt W) * (Co' * Tb)
        ≤ Cm' * (Co' * (Co' * Tb)) / Real.sqrt W + Cm' * (Co' * (Co' * Tb)) / Real.sqrt W +
            (Cm' + Cf') * (Co' * Tb) / Real.sqrt W := add_le_add (add_le_add e1 e1) e3
      _ = H0 / Real.sqrt W := by simp only [H0]; ring
  have hinj : Kf * Kq / W * Cg ^ 2 ≤ Kf * Kq * Cg ^ 2 / Real.sqrt W := by
    rw [div_eq_mul_inv (Kf * Kq), div_eq_mul_inv (Kf * Kq * Cg ^ 2)]
    have := mul_le_mul_of_nonneg_left hinvW (by positivity : 0 ≤ Kf * Kq * Cg ^ 2)
    linarith [this, show Kf * Kq * (W : ℝ)⁻¹ * Cg ^ 2 = Kf * Kq * Cg ^ 2 * (W : ℝ)⁻¹ by ring]
  -- the two recursions
  set aZ : ℕ → ℝ≥0∞ := fun i => eLpNorm (openClockZ b E q D i) (ENNReal.ofReal p) (oneEndedLaw W b i)
  set aS : ℕ → ℝ≥0∞ := fun i =>
    eLpNorm (openClockSqrtS b E q D i) (ENNReal.ofReal p) (oneEndedLaw W b i)
  have hstepZ : ∀ i, openEntranceTime W ≤ i → i < N →
      aZ (i + 1) ≤ ENNReal.ofReal ‖θ‖ * aZ i + ENNReal.ofReal (FZ / Real.sqrt W) := by
    intro i hi0 hiN
    refine (stepZ hD hq0 hqK hW1 hz θ hCf' hCg.le hp H i).trans ?_
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    calc eLpNorm (errWeight b E q D s Cm' (Cf' / Real.sqrt W) i) (ENNReal.ofReal p)
          (oneEndedLaw W b i) + ENNReal.ofReal (Kf * Kq / W * Cg ^ 2)
        ≤ ENNReal.ofReal (H0 / Real.sqrt W) + ENNReal.ofReal (Kf * Kq * Cg ^ 2 / Real.sqrt W) :=
          add_le_add (hEW i hi0 hiN.le) (ENNReal.ofReal_le_ofReal hinj)
      _ = ENNReal.ofReal (FZ / Real.sqrt W) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; simp only [FZ]; ring
  have hstepS : ∀ i, openEntranceTime W ≤ i → i < N →
      aS (i + 1) ≤ ENNReal.ofReal ‖θ‖ * aS i + ENNReal.ofReal (FS / Real.sqrt W) := by
    intro i hi0 hiN
    refine (stepS hD hq0 hqK hW1 hz θ hCf' hCg.le hp H i).trans ?_
    rw [add_assoc, add_assoc]
    refine add_le_add le_rfl ?_
    have hg : ENNReal.ofReal (Kf / Real.sqrt W) *
        eLpNorm (oneEndedGamma b E q D (i + 1)) (ENNReal.ofReal p) (oneEndedLaw W b (i + 1)) ≤
        ENNReal.ofReal (Kf * (Co' * Tb) / Real.sqrt W) := by
      rw [show Kf * (Co' * Tb) / Real.sqrt W = Kf / Real.sqrt W * (Co' * Tb) by ring,
        ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact hγp (i + 1) hiN
    calc eLpNorm (errWeight b E q D s Cm' (Cf' / Real.sqrt W) i) (ENNReal.ofReal p)
          (oneEndedLaw W b i) + (ENNReal.ofReal (Kf * Kq / Real.sqrt W * Cg ^ 2) +
          ENNReal.ofReal (Kf / Real.sqrt W) *
            eLpNorm (oneEndedGamma b E q D (i + 1)) (ENNReal.ofReal p) (oneEndedLaw W b (i + 1)))
        ≤ ENNReal.ofReal (H0 / Real.sqrt W) + (ENNReal.ofReal (Kf * Kq * Cg ^ 2 / Real.sqrt W) +
            ENNReal.ofReal (Kf * (Co' * Tb) / Real.sqrt W)) :=
          add_le_add (hEW i hi0 hiN.le) (add_le_add (le_of_eq (by congr 1; ring)) hg)
      _ = ENNReal.ofReal (FS / Real.sqrt W) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; simp only [FS]; ring
  -- the initial bound at `j₀`
  set j₀ := openEntranceTime W
  have hj0N : j₀ ≤ N := le_trans hj0 hjN
  have hinit : ∀ a : ℕ → ℝ≥0∞, (a = aZ ∨ a = aS) → a j₀ ≤ ENNReal.ofReal (A0 / Real.sqrt W) := by
    intro a ha
    have hib := init_bound (W := W) (b := b) (E := E) (q := q) hD hq0 hz j₀ (ENNReal.ofReal p)
    have hg0 : eLpNorm (oneEndedGamma b E q D j₀) (ENNReal.ofReal p) (oneEndedLaw W b j₀) ≤
        ENNReal.ofReal (Co' * (((j₀ : ℝ) + 1) / W)) := by
      refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans
        ((hγ j₀ (hiT j₀ hj0N)).trans (ENNReal.ofReal_le_ofReal ?_))
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hfin : ENNReal.ofReal Kf * ENNReal.ofReal (Co' * (((j₀ : ℝ) + 1) / W)) ≤
        ENNReal.ofReal (A0 / Real.sqrt W) := by
      rw [← ENNReal.ofReal_mul hKf]
      refine ENNReal.ofReal_le_ofReal ?_
      have he := entrance_le hW1
      calc Kf * (Co' * (((j₀ : ℝ) + 1) / W)) ≤ Kf * (Co' * (18 / Real.sqrt W)) := by gcongr
        _ = A0 / Real.sqrt W := by simp only [A0]; ring
    rcases ha with rfl | rfl
    · exact hib.1.trans ((mul_le_mul_of_nonneg_left hg0 zero_le).trans hfin)
    · exact hib.2.trans ((mul_le_mul_of_nonneg_left hg0 zero_le).trans hfin)
  have hZ := geom_bound hθ0 hθ (by positivity) (by positivity) (hinit aZ (Or.inl rfl)) hstepZ j hj0
    hjN
  have hS := geom_bound hθ0 hθ (by positivity) (by positivity) (hinit aS (Or.inr rfl)) hstepS j hj0
    hjN
  calc aZ j + aS j
      ≤ ENNReal.ofReal (A0 / Real.sqrt W + FZ / Real.sqrt W / (1 - ‖θ‖)) +
          ENNReal.ofReal (A0 / Real.sqrt W + FS / Real.sqrt W / (1 - ‖θ‖)) := add_le_add hZ hS
    _ = ENNReal.ofReal (((A0 + FZ / (1 - ‖θ‖)) + (A0 + FS / (1 - ‖θ‖))) / Real.sqrt W) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The clock-mixing bound** (`ClockMixingBound`) for the one-ended path (`X_0 = 0`), from
`PassiveSourceMixingContract`, `GaussianAbsorptionContract` and `OpenInputsMoments`.
-/
theorem clockMixing_of (hPSM : PassiveSourceMixingContract) (hGA : GaussianAbsorptionContract)
    (hOI : OpenInputsMoments) : ClockMixingBound := by
  intro b hb0 hb1 E hE1 hE2 T q hq p hp
  obtain ⟨ε, C, W₀, hε, h⟩ := clockMixingUniform_of hPSM hGA hOI b hb0 hb1 E hE1 hE2 T q hq p hp
  refine ⟨C, W₀, fun W hW j hj0 hjT => ?_⟩
  refine h W hW 0 isHermitian_zero ?_ j hj0 hjT
  rw [norm_zero]; exact hε.le

end BlockBand.Endpoints.Clock
