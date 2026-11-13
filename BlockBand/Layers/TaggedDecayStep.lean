module

public import BlockBand.Layers.TaggedDecayClock

/-!
# Tagged decay along the growing path: one step, the recursion and exit removal

Part of the proof of the tagged decay bound: the path-level decay of the derivative trace
`D(X, Y)` of `TaggedDecayClock` along the two-ended growth.

## The one-step mean bound

`TdcLayerMean` (a named statement, proved by `tdcLayerMean_holds`): the differentiated mean equation of one untagged separate-port layer,
"`|E(d₊ | X, S)| ≤ q_* |d| + Cδu + Cu/W`". `D_j(X₊, Y₊)` is the derivative of the
outgoing port trace and `D_i(X, Y)` that of the incoming one along `X - hS`
(`tdc_D_step_eq_gdot`, `tdc_hasDerivAt_input`); `δ = d(X)` the scalar error.

## Proved here

* `tdc_noise` — the conditional fluctuation `‖d₊ - E(d₊ | X, S)‖_p ≤ C_p u/√W`, from
  the noise clause of `DiffCovarianceFamilyStatement` (`tgtNoiseClause`, `D = Q_j`) and the
  identity `D_j(X₊, Y₊) = -ġ_j`;
* `tdc_step_Lp` — the conditional `L^p` one-step bound
  `‖max_j |D_j(X₊, Y₊)|‖_p ≤ q max_i |D_i(X, Y)| + C(d(X) + W^{-1/2})u` from `TdcLayerMean`;
* `tdc_iter_step` — one growth step of `a_k = ‖1_{reg_k} max |D|‖_{L^p(growthLaw k)}` by Fubini;
* `tdc_growth_decay` — iterating from the last tagged layer (in the paper:
  "Iterating from the last tagged layer gives `C_p(q_*^ℓ + W^{-1/2})` after `ℓ` untagged layers"),
  with the scalar moments from the matched-traces theorem and the clock moments of
  the clock-moments lemma (Hölder), and exit removal as in the clock-moments lemma (the scalar
  exit bound);
* `tdc_path_decay` — the same under `pathLaw W r b` for the source of the final path with an
  arbitrary position tag on at most two blocks, and `tdc_path_clock`
  (moments of the clock under `pathLaw`).

Constants: `q` after `b, κ` only (it is `ρ` of the tagged decay bound); `C, W₀` after `b, κ, T, p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. The one-step mean bound
-/

/-- **The differentiated mean equation of one untagged layer** (named statement;
"`|E(d₊ | X, S)| ≤ q_*|d| + Cδu + Cu/W`"). Law: one fresh separate-port layer
`layerLaw W b .separate` at `z = z_∂(E)`, conditional on the deterministic old input `X`
(Hermitian, two-port) and the deterministic clock `Y ⪰ 0` (the incoming source is `S = K*YK`,
`K = z_∂ - X`). Objects: `X₊ = B*(A - E - X)⁻¹B`, `Y₊ = L*YL` (untagged step of
the tagged clock identity), `u = W⁻¹ Tr Y` (`clkTrace`), `δ = d(X)` (`matchedDistance`). The outgoing
derivative of the port traces along `X - hS` is `-D_j(X₊, Y₊)` (`tdc_D_step`,
`tdc_D_step_eq_gdot`), the incoming one `-D_i(X, Y)` (`tdc_hasDerivAt_input`).
Quantifiers: `b ∈ (0, 1/2)` and `κ > 0` first; then `d₀ > 0`, `0 ≤ q < 1`, `C ≥ 0`, `W₀`;
uniformly in `W ≥ W₀`, Hermitian `X` with `d(X) ≤ d₀`, `Y ⪰ 0`, `E ∈ bulkInterval κ` and the port
`j`: `|E D_j(X₊, Y₊)| ≤ q max_i |D_i(X, Y)| + C (d(X) + 1/W) u`.
Proof idea: differentiate the exact mean identity `(D - 𝒮(ḡ)) E𝒢 = I + Σ σ_j Cov(g_j, 𝒢)`
(`meanEquation_holds`) along `X - hS`; the source is `Ŝ`, the scalar feedback `𝒮(ḡ̇)`, the
covariance derivative is bounded by the differentiated-covariance lemma (`tgtCurvedClause`),
`M̄ → R` costs `Cδu`, and the strict contraction (`StrictContractionContract.margin`) gives `q`. -/
def TdcLayerMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d₀ q C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → Y.PosSemidef →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ d₀ → ∀ j : Fin 2,
        ‖∫ ℓ, tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j
            ∂layerLaw W b .separate‖ ≤
          q * tdcMaxD b E X Y + C * (matchedDistance b E X + 1 / W) * clkTrace Y

/-!
## 2. Elementary `L^p` facts
-/

section Lp

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tdc_eLpNorm_const {ν : Measure Ω} [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 < p) {A : ℝ}
    (hA : 0 ≤ A) : eLpNorm (fun _ : Ω => A) (ENNReal.ofReal p) ν = ENNReal.ofReal A := by
  rw [eLpNorm_const _ (by simpa using hp) (IsProbabilityMeasure.ne_zero ν), measure_univ,
    ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hA]

/-- `‖f‖_p ≤ A + B` if `|f| ≤ A + |g|` a.e. and `‖g‖_p ≤ B` (probability measure). -/
theorem tdc_eLpNorm_le_const_add {ν : Measure Ω} [IsProbabilityMeasure ν] {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) {p : ℝ} (hp : 1 ≤ p)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hfg : ∀ᵐ x ∂ν, ‖f x‖ ≤ A + ‖g x‖)
    (hgB : eLpNorm g (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B) :
    eLpNorm f (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (A + B) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  refine (eLpNorm_mono_ae_real hf hfg).trans ?_
  have e : (fun x => A + ‖g x‖) = (fun _ : Ω => A) + fun x => ‖g x‖ := rfl
  rw [e]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [tdc_eLpNorm_const (by linarith) hA, eLpNorm_norm _ hg, ENNReal.ofReal_add hA hB]
  gcongr

/-- `‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p` for nonnegative real functions with real bounds. -/
theorem tdc_eLpNorm_add_le {ν : Measure Ω} {f g : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : eLpNorm f (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A)
    (hgB : eLpNorm g (ENNReal.ofReal p) ν ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => f x + g x) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (A + B) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e]
  refine (eLpNorm_add_le hp1).trans ?_
  rw [ENNReal.ofReal_add hA hB]
  exact add_le_add hfA hgB

/-- `‖c f‖_p = c ‖f‖_p` for `c ≥ 0`. -/
theorem tdc_eLpNorm_smul_le {ν : Measure Ω} {f : Ω → ℝ} {p : ℝ} {c A : ℝ} (hc : 0 ≤ c)
    (hfA : eLpNorm f (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A) :
    eLpNorm (fun x => c * f x) (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (c * A) := by
  have e : (fun x => c * f x) = c • f := rfl
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  rcases le_or_gt A 0 with hA | hA
  · rw [ENNReal.ofReal_of_nonpos hA] at hfA
    rw [nonpos_iff_eq_zero.mp hfA, mul_zero]
    exact bot_le
  · rw [ENNReal.ofReal_mul hc]
    gcongr

end Lp

/-!
## 3. The fluctuation of one step
-/

/-- **The conditional fluctuation of the outgoing derivative**
(`‖d₊ - E(d₊ | X, S)‖_{p | X, S} ≤ C_p u/√W`): from `tgtNoiseClause` with `D = Q_j` and
`D_j(X₊, Y₊) = -ġ_j` (a.s.). -/
theorem tdc_noise (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), 0 ≤ Cp ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → Y.PosSemidef →
      ∀ E ∈ bulkInterval κ, ∀ j : Fin 2,
        eLpNorm (fun ℓ => tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j -
            ∫ ℓ', tdcD b E (layerSchur .separate E X ℓ') (clkStep b E (fun _ => false) X Y ℓ') j
              ∂layerLaw W b .separate) (ENNReal.ofReal p) (layerLaw W b .separate) ≤
          ENNReal.ofReal (Cp * clkTrace Y / Real.sqrt W) := by
  intro b hb0 hb1 κ hκ p hp
  have hN := ((diffCovarianceFamily_holds' hcount hgrad) b hb0 hb1 κ hκ).2.2 p hp
  obtain ⟨Cp, W₀, hC⟩ := hN
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  refine ⟨max Cp 0, W₀, le_max_right _ _, fun W hW0 hW X Y hX hY E hE j => ?_⟩
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη (hbulk E hE).1
  set K := tdcK b E X with hKdef
  set S := Kᴴ * Y * K with hSdef
  have hS : S.PosSemidef := hY.conjTranspose_mul_mul_same K
  have hYS : (K⁻¹)ᴴ * S * K⁻¹ = Y := by
    have h1 := tdc_K_mul_inv hz hX
    calc (K⁻¹)ᴴ * S * K⁻¹ = (K * K⁻¹)ᴴ * Y * (K * K⁻¹) := by
          rw [hSdef, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hD : ‖(meqPortProj (σ := .separate) j : Matrix (LayerSite W .separate)
      (LayerSite W .separate) ℂ)‖ ≤ 1 := meq_norm_portProj_le (σ := .separate) j
  have h := hC W hW0 hW X S hX hS E hE _ hD
  obtain ⟨h1, h2, -⟩ := h
  have hu : (W : ℝ)⁻¹ * ((K⁻¹)ᴴ * S * K⁻¹).trace.re = clkTrace Y := by rw [hYS]; rfl
  set μ := layerLaw W b .separate
  set G := fun ℓ => layerResolvent .separate E (boundaryZ b E) X ℓ
  set gd := fun ℓ => -((W : ℂ)⁻¹ * (meqPortProj (σ := .separate) j * (G ℓ * dcvHat S * G ℓ)).trace)
  have hae : ∀ᵐ ℓ ∂μ,
      tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j = -gd ℓ := by
    filter_upwards [lct_ae_blocks_isHermitian W b .separate,
      srec_ae_isUnit_top hb1 .separate E X] with ℓ hℓ hSℓ
    have hNℓ := clk_layerMatrix_isUnit E (boundaryZ b E) X ℓ hSℓ
      (clk_K_isUnit (srec_layerSchur_isHermitian E hX ℓ hℓ) hz)
    rw [tdc_D_step hz hX Y ℓ hℓ hSℓ hNℓ j, tdc_D_step_eq_gdot]
    simp only [gd, neg_neg]
    rfl
  have hint : ∫ ℓ, tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j ∂μ =
      -∫ ℓ, gd ℓ ∂μ := by
    rw [integral_congr_ae hae, integral_neg]
  have hfun : (fun ℓ => tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j -
      ∫ ℓ', tdcD b E (layerSchur .separate E X ℓ') (clkStep b E (fun _ => false) X Y ℓ') j ∂μ) =ᵐ[μ]
      fun ℓ => -(gd ℓ - ∫ ℓ', gd ℓ' ∂μ) := by
    filter_upwards [hae] with ℓ hℓ
    rw [hℓ, hint]; ring
  rw [eLpNorm_congr_ae hfun, show (fun ℓ => -(gd ℓ - ∫ ℓ', gd ℓ' ∂μ)) =
    -(fun ℓ => gd ℓ - ∫ ℓ', gd ℓ' ∂μ) from rfl, eLpNorm_neg]
  refine h1.trans (ENNReal.ofReal_le_ofReal (h2.trans ?_))
  change Cp * ((W : ℝ)⁻¹ * ((K⁻¹)ᴴ * S * K⁻¹).trace.re) / Real.sqrt W ≤ _
  rw [hu]
  have hu0 : 0 ≤ clkTrace Y := clkTrace_nonneg hY
  have hsq : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hsq with h0 | h0
  · rw [← h0]; simp
  · rw [div_le_div_iff_of_pos_right h0]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu0

/-!
## 4. The conditional one-step bound
-/

theorem tdc_rpow_half (W : ℕ) : (W : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt W)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), Real.sqrt_eq_rpow]

theorem tdc_inv_le_rpow_half {W : ℕ} (hW : 0 < W) : 1 / (W : ℝ) ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [tdc_rpow_half W]
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs : Real.sqrt W ≤ W := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr (by linarith)
  rw [one_div]
  exact inv_anti₀ hs0 hs

theorem tdc_rpow_half_nonneg (W : ℕ) : 0 ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **The conditional one-step bound**: for one fresh untagged layer, on the
scalar domain, `‖max_j |D_j(X₊, Y₊)|‖_p ≤ q max_i |D_i(X, Y)| + C(d(X) + W^{-1/2}) u`; `q` from
`TdcLayerMean` (after `b, κ`), `C, W₀` after `p`. -/
theorem tdc_step_Lp (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hM : TdcLayerMean) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ d₀ q : ℝ, 0 < d₀ ∧ 0 ≤ q ∧ q < 1 ∧ ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W →
      ∀ X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → Y.PosSemidef →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ d₀ →
        eLpNorm (fun ℓ => tdcMaxD b E (layerSchur .separate E X ℓ)
            (clkStep b E (fun _ => false) X Y ℓ)) (ENNReal.ofReal p) (layerLaw W b .separate) ≤
          ENNReal.ofReal (q * tdcMaxD b E X Y +
            C * (matchedDistance b E X + (W : ℝ) ^ (-(1 / 2 : ℝ))) * clkTrace Y) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨d₀, q, C, W₁, hd₀, hq0, hq1, hC, hmean⟩ := hM b hb0 hb1 κ hκ
  refine ⟨d₀, q, hd₀, hq0, hq1, fun p hp => ?_⟩
  obtain ⟨Cp, W₂, hCp, hnoise⟩ := tdc_noise hcount hgrad b hb0 hb1 κ hκ p hp
  refine ⟨C + 2 * Cp, max W₁ W₂, by positivity, fun W hW0 hW X Y hX hY E hE hd => ?_⟩
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  set μ := layerLaw W b .separate
  set Dj := fun (j : Fin 2) (ℓ : LayerSample W .separate) =>
    tdcD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ) j with hDj
  have hmeas : ∀ j, Measurable (Dj j) := fun j =>
    tdc_measurable_D b E (srec_measurable_layerSchur E measurable_const measurable_id)
      (clk_measurable_step b E _ measurable_const measurable_const measurable_id) j
  set ξ := fun ℓ => ‖Dj 0 ℓ - ∫ ℓ', Dj 0 ℓ' ∂μ‖ + ‖Dj 1 ℓ - ∫ ℓ', Dj 1 ℓ' ∂μ‖ with hξ
  have hu0 : 0 ≤ clkTrace Y := clkTrace_nonneg hY
  have hdX := clk_matchedDistance_nonneg b E X
  have hW1 : (0 : ℝ) < W := by exact_mod_cast hW0
  set A := q * tdcMaxD b E X Y + C * (matchedDistance b E X + 1 / W) * clkTrace Y with hAdef
  have hA0 : 0 ≤ A := by
    have := tdcMaxD_nonneg b E X Y; positivity
  have hpt : ∀ ℓ, ‖tdcMaxD b E (layerSchur .separate E X ℓ) (clkStep b E (fun _ => false) X Y ℓ)‖ ≤
      A + ‖ξ ℓ‖ := by
    intro ℓ
    have hm := hmean W hW0 (le_of_max_le_left hW) X Y hX hY E hE hd
    rw [Real.norm_of_nonneg (tdcMaxD_nonneg _ _ _ _), Real.norm_of_nonneg (by positivity)]
    have hj : ∀ j : Fin 2, ‖Dj j ℓ‖ ≤ A + ‖Dj j ℓ - ∫ ℓ', Dj j ℓ' ∂μ‖ := by
      intro j
      calc ‖Dj j ℓ‖ ≤ ‖∫ ℓ', Dj j ℓ' ∂μ‖ + ‖Dj j ℓ - ∫ ℓ', Dj j ℓ' ∂μ‖ := by
            have := norm_add_le (∫ ℓ', Dj j ℓ' ∂μ) (Dj j ℓ - ∫ ℓ', Dj j ℓ' ∂μ)
            rwa [add_sub_cancel] at this
        _ ≤ A + _ := by gcongr; exact hm j
    refine max_le ((hj 0).trans ?_) ((hj 1).trans ?_)
    · simp only [hξ]; linarith [norm_nonneg (Dj 1 ℓ - ∫ ℓ', Dj 1 ℓ' ∂μ)]
    · simp only [hξ]; linarith [norm_nonneg (Dj 0 ℓ - ∫ ℓ', Dj 0 ℓ' ∂μ)]
  have hcu : 0 ≤ Cp * clkTrace Y / Real.sqrt W := by positivity
  have hξm : ∀ j, AEStronglyMeasurable (fun ℓ => Dj j ℓ - ∫ ℓ', Dj j ℓ' ∂μ) μ :=
    fun j => ((hmeas j).sub measurable_const).aestronglyMeasurable
  have hξB : eLpNorm ξ (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (Cp * clkTrace Y / Real.sqrt W + Cp * clkTrace Y / Real.sqrt W) := by
    refine tdc_eLpNorm_add_le hp hcu hcu ?_ ?_
    · rw [eLpNorm_norm _ (hξm 0)]
      exact hnoise W hW0 (le_of_max_le_right hW) X Y hX hY E hE 0
    · rw [eLpNorm_norm _ (hξm 1)]
      exact hnoise W hW0 (le_of_max_le_right hW) X Y hX hY E hE 1
  have hmeasMax : AEStronglyMeasurable (fun ℓ => tdcMaxD b E (layerSchur .separate E X ℓ)
      (clkStep b E (fun _ => false) X Y ℓ)) μ :=
    (tdc_measurable_maxD b E (srec_measurable_layerSchur E measurable_const measurable_id)
      (clk_measurable_step b E _ measurable_const measurable_const measurable_id)).aestronglyMeasurable
  refine (tdc_eLpNorm_le_const_add hmeasMax ((hξm 0).norm.add (hξm 1).norm) hp hA0 (by positivity)
    (Filter.Eventually.of_forall hpt) hξB).trans (ENNReal.ofReal_le_ofReal ?_)
  have hiw := tdc_inv_le_rpow_half hW0
  rw [tdc_rpow_half W] at hiw ⊢
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW1
  have e : Cp * clkTrace Y / Real.sqrt W = Cp * (Real.sqrt W)⁻¹ * clkTrace Y := by
    rw [div_eq_mul_inv]; ring
  rw [hAdef, e]
  have hsi : 0 ≤ (Real.sqrt W)⁻¹ := inv_nonneg.mpr hs0.le
  nlinarith [mul_le_mul_of_nonneg_left hiw hC, mul_nonneg hCp hsi, mul_nonneg hdX hu0,
    mul_nonneg (mul_nonneg hCp hdX) hu0, mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hiw hC) hu0]

/-!
## 5. One growth step and the recursion
-/

section Growth

variable {W r₀ : ℕ}

/-- `Z_k = 1_{reg_k} max_i |D_i(X_k, Y_k)|` along the growth. -/
def tdcZ {L : ℕ} (b E d' : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ L) (k : ℕ) : ℝ :=
  {ω : GrowthSample W r₀ L | clkReg b E d' ω k}.indicator
    (fun ω => tdcMaxD b E (grownSchur E ω k) (clkClock b E τ₀ τ ω k)) ω

theorem tdcZ_nonneg {L : ℕ} (b E d' : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ L) (k : ℕ) : 0 ≤ tdcZ b E d' τ₀ τ ω k :=
  Set.indicator_nonneg (fun _ _ => tdcMaxD_nonneg _ _ _ _) _

theorem tdc_measurable_maxD_k {L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (k : ℕ) : Measurable (fun ω : GrowthSample W r₀ L =>
      tdcMaxD b E (grownSchur E ω k) (clkClock b E τ₀ τ ω k)) :=
  tdc_measurable_maxD b E (clk_measurable_grownSchur E k) (clk_measurable_clock b E τ₀ τ k)

theorem tdc_measurable_Z {L : ℕ} (b E d' : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (k : ℕ) : Measurable (fun ω : GrowthSample W r₀ L => tdcZ b E d' τ₀ τ ω k) :=
  (tdc_measurable_maxD_k b E τ₀ τ k).indicator (clk_measurableSet_reg b E d' k)

/-- **One growth step** (Fubini over the fresh layer `k`): if layer `k` is untagged and the
conditional one-step bound holds on `d ≤ d'`, then
`‖Z_{k+1}‖_p ≤ q ‖Z_k‖_p + C ‖(d_k + w) u_k‖_p`. -/
theorem tdc_iter_step {k : ℕ} {b E d' q C w p : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hp : 1 ≤ p) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (hτ : τ k = fun _ => false)
    (hstep : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b E X ≤ d' → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        eLpNorm (fun ℓ => tdcMaxD b E (layerSchur .separate E X ℓ)
            (clkStep b E (fun _ => false) X Y ℓ)) (ENNReal.ofReal p) (layerLaw W b .separate) ≤
          ENNReal.ofReal (q * tdcMaxD b E X Y + C * (matchedDistance b E X + w) * clkTrace Y)) :
    eLpNorm (fun ω : GrowthSample W r₀ (k + 1) => tdcZ b E d' τ₀ τ ω (k + 1)) (ENNReal.ofReal p)
        (growthLaw W r₀ (k + 1) b) ≤
      ENNReal.ofReal q * eLpNorm (fun ω : GrowthSample W r₀ k => tdcZ b E d' τ₀ τ ω k)
          (ENNReal.ofReal p) (growthLaw W r₀ k b) +
        ENNReal.ofReal C * eLpNorm (fun ω : GrowthSample W r₀ k =>
          (matchedDistance b E (grownSchur E ω k) + w) * clkTrace (clkClock b E τ₀ τ ω k))
          (ENNReal.ofReal p) (growthLaw W r₀ k b) := by
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set Xk := fun a : GrowthSample W r₀ k => grownSchur E a k
  set Yk := fun a : GrowthSample W r₀ k => clkClock b E τ₀ τ a k
  have hXm : Measurable Xk := clk_measurable_grownSchur E k
  have hYm : Measurable Yk := clk_measurable_clock b E τ₀ τ k
  set R := {a : GrowthSample W r₀ k | clkReg b E d' a k}
  have hRm : MeasurableSet R := clk_measurableSet_reg b E d' k
  set F : GrowthSample W r₀ k × LayerSample W .separate → ℝ := fun x =>
    (Prod.fst ⁻¹' R).indicator (fun x => tdcMaxD b E (layerSchur .separate E (Xk x.1) x.2)
      (clkStep b E (fun _ => false) (Xk x.1) (Yk x.1) x.2)) x with hFdef
  have hFm : Measurable F :=
    (tdc_measurable_maxD b E (srec_measurable_layerSchur E (hXm.comp measurable_fst) measurable_snd)
      (clk_measurable_step b E _ (hXm.comp measurable_fst) (hYm.comp measurable_fst)
        measurable_snd)).indicator (measurable_fst hRm)
  set G : GrowthSample W r₀ k → ℝ := fun a => R.indicator (fun a => q * tdcMaxD b E (Xk a) (Yk a) +
    C * (matchedDistance b E (Xk a) + w) * clkTrace (Yk a)) a with hGdef
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hRm
    exact (measurable_const.mul (tdc_measurable_maxD b E hXm hYm)).add
      ((measurable_const.mul ((srec_measurable_matchedDistance b E W).comp hXm |>.add
        measurable_const)).mul (clk_measurable_trace hYm))
  have hG0 : ∀ a, 0 ≤ G a := by
    intro a
    refine Set.indicator_nonneg (fun a _ => ?_) a
    have := tdcMaxD_nonneg b E (Xk a) (Yk a)
    have := clk_matchedDistance_nonneg b E (Xk a)
    have := clkTrace_nonneg (clkClock_posSemidef b E τ₀ τ a k)
    positivity
  -- (i) pointwise domination of `Z_{k+1}` by `F ∘ split`
  have hpt : ∀ ω : GrowthSample W r₀ (k + 1),
      ‖tdcZ b E d' τ₀ τ ω (k + 1)‖ ≤ F (pgTrunc ω, ω.2 (Fin.last k)) := by
    intro ω
    rw [Real.norm_of_nonneg (tdcZ_nonneg _ _ _ _ _ _ _)]
    unfold tdcZ
    by_cases hω : clkReg b E d' ω (k + 1)
    · have hω' : (pgTrunc ω, ω.2 (Fin.last k)) ∈ Prod.fst ⁻¹' R := clkReg_pgTrunc hω
      rw [Set.indicator_of_mem (show ω ∈ {ω | clkReg b E d' ω (k + 1)} from hω)]
      simp only [hFdef]
      rw [Set.indicator_of_mem hω', clk_grownSchur_last, clkClock_last, hτ]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | clkReg b E d' ω (k + 1)} from hω)]
      exact Set.indicator_nonneg (fun _ _ => tdcMaxD_nonneg _ _ _ _) _
  -- (ii) transfer to the product law
  have hsplit := pg_mp_splitLast W r₀ k b
  have h1 : eLpNorm (fun ω : GrowthSample W r₀ (k + 1) => tdcZ b E d' τ₀ τ ω (k + 1))
      (ENNReal.ofReal p) (growthLaw W r₀ (k + 1) b) ≤
        eLpNorm F (ENNReal.ofReal p) ((growthLaw W r₀ k b).prod (layerLaw W b .separate)) := by
    rw [← eLpNorm_comp_measurePreserving hFm.aestronglyMeasurable hsplit]
    exact eLpNorm_mono_real (tdc_measurable_Z b E d' τ₀ τ (k + 1)).aestronglyMeasurable hpt
  -- (iii) the conditional bound integrates
  have h2 : eLpNorm F (ENNReal.ofReal p) ((growthLaw W r₀ k b).prod (layerLaw W b .separate)) ≤
      ENNReal.ofReal 1 * eLpNorm G (ENNReal.ofReal p) (growthLaw W r₀ k b) := by
    refine clk_eLpNorm_prod_le hFm hGm hp0 ?_
    filter_upwards [clk_ae_good W r₀ k b] with a hga
    rw [ENNReal.ofReal_one, one_mul, Real.enorm_eq_ofReal (hG0 a)]
    by_cases ha : a ∈ R
    · have hF' : (fun y => F (a, y)) = fun ℓ => tdcMaxD b E (layerSchur .separate E (Xk a) ℓ)
          (clkStep b E (fun _ => false) (Xk a) (Yk a) ℓ) := by
        funext y; simp only [hFdef]; rw [Set.indicator_of_mem (show (a, y) ∈ Prod.fst ⁻¹' R from ha)]
      rw [hF', hGdef]
      simp only
      rw [Set.indicator_of_mem ha]
      exact hstep (Xk a) (clk_grownSchur_isHermitian E hga k) (ha k le_rfl) (Yk a)
        (clkClock_posSemidef b E τ₀ τ a k)
    · have hF' : (fun y => F (a, y)) = fun _ => 0 := by
        funext y; simp only [hFdef]
        rw [Set.indicator_of_notMem (show (a, y) ∉ Prod.fst ⁻¹' R from ha)]
      rw [hF', eLpNorm_fun_zero]
      exact bot_le
  -- (iv) Minkowski
  have h3 : eLpNorm G (ENNReal.ofReal p) (growthLaw W r₀ k b) ≤
      ENNReal.ofReal q * eLpNorm (fun ω : GrowthSample W r₀ k => tdcZ b E d' τ₀ τ ω k)
          (ENNReal.ofReal p) (growthLaw W r₀ k b) +
        ENNReal.ofReal C * eLpNorm (fun ω : GrowthSample W r₀ k =>
          (matchedDistance b E (grownSchur E ω k) + w) * clkTrace (clkClock b E τ₀ τ ω k))
          (ENNReal.ofReal p) (growthLaw W r₀ k b) := by
    have hle : ∀ a, ‖G a‖ ≤ (q • fun ω : GrowthSample W r₀ k => tdcZ b E d' τ₀ τ ω k) a +
        (C • fun ω : GrowthSample W r₀ k => (matchedDistance b E (grownSchur E ω k) + w) *
          clkTrace (clkClock b E τ₀ τ ω k)) a := by
      intro a
      rw [Real.norm_of_nonneg (hG0 a)]
      simp only [Pi.smul_apply, smul_eq_mul, hGdef, tdcZ]
      have hd := clk_matchedDistance_nonneg b E (grownSchur E a k)
      have hu := clkTrace_nonneg (clkClock_posSemidef b E τ₀ τ a k)
      by_cases ha : a ∈ R
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (show a ∈ {ω | clkReg b E d' ω k} from ha)]
        exact le_of_eq (by simp only [Xk, Yk]; ring)
      · rw [Set.indicator_of_notMem ha,
          Set.indicator_of_notMem (show a ∉ {ω | clkReg b E d' ω k} from ha), mul_zero, zero_add]
        positivity
    refine (eLpNorm_mono_real hGm.aestronglyMeasurable hle).trans ?_
    refine (eLpNorm_add_le hp1).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal hq, Real.enorm_eq_ofReal hC]
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = eLpNorm G (ENNReal.ofReal p) (growthLaw W r₀ k b) := by rw [ENNReal.ofReal_one, one_mul]
    _ ≤ _ := h3

/-- **The recursion** `a_{k+1} ≤ q a_k + β` for `k₁ ≤ k < k₁ + m` gives
`a_{k₁+m} ≤ q^m A₀ + β/(1-q)` from `a_{k₁} ≤ A₀`. -/
theorem tdc_iter {a : ℕ → ℝ≥0∞} {q β A₀ : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (hβ : 0 ≤ β)
    (hA₀ : 0 ≤ A₀) {k₁ : ℕ} (h0 : a k₁ ≤ ENNReal.ofReal A₀) (m : ℕ)
    (h : ∀ i, i < m → a (k₁ + i + 1) ≤ ENNReal.ofReal q * a (k₁ + i) + ENNReal.ofReal β) :
    a (k₁ + m) ≤ ENNReal.ofReal (q ^ m * A₀ + β / (1 - q)) := by
  have hq' : 0 < 1 - q := by linarith
  induction m with
  | zero =>
    simp only [add_zero, pow_zero, one_mul]
    exact h0.trans (ENNReal.ofReal_le_ofReal (by linarith [div_nonneg hβ hq'.le]))
  | succ m ih =>
    have ih' := ih (fun i hi => h i (by omega))
    calc a (k₁ + (m + 1)) = a (k₁ + m + 1) := rfl
      _ ≤ ENNReal.ofReal q * a (k₁ + m) + ENNReal.ofReal β := h m (by omega)
      _ ≤ ENNReal.ofReal q * ENNReal.ofReal (q ^ m * A₀ + β / (1 - q)) + ENNReal.ofReal β := by
          gcongr
      _ = ENNReal.ofReal (q ^ (m + 1) * A₀ + β / (1 - q)) := by
          rw [← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_add (by positivity) hβ]
          congr 1
          field_simp
          ring

end Growth

/-!
## 6. Moments along the growth and exit removal
-/

section Moments

variable {W r₀ : ℕ}

/-- **Scalar moments along the growth** (the matched-traces theorem, path clause): under
`growthLaw W r₀ k b`, `‖d(X_k)‖_p ≤ C √p / W` for `2 ≤ p ≤ ε₀ W`, `r₀ + 2k ≤ TW`. -/
theorem tdc_distance_growth (hmt : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
      ∀ r₀ k : ℕ, 1 ≤ r₀ → ((r₀ + 2 * k : ℕ) : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω : GrowthSample W r₀ k => matchedDistance b E (grownSchur E ω k))
          (ENNReal.ofReal p) (growthLaw W r₀ k b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨ε₀, C, hε₀, hpath⟩ := hmt.path b hb0 hb1 κ T hκ
  refine ⟨ε₀, C, hε₀, fun W hW0 p hp2 hpε r₀ k hr₀ hrT E hE => ?_⟩
  have hP := measurePreserving_pgPath (W := W) b hr₀ k k le_rfl
  have hm : Measurable (fun π : PathSample W (r₀ + 2 * k) => matchedDistance b E (pathSchur E π)) :=
    (srec_measurable_matchedDistance b E W).comp (measurable_pathSchur W _ E)
  have hae : (fun ω : GrowthSample W r₀ k => matchedDistance b E (grownSchur E ω k)) =ᵐ[growthLaw W r₀ k b]
      (fun π => matchedDistance b E (pathSchur E π)) ∘ (fun ω => pgPath ω k) := by
    filter_upwards [ae_grownSchur_eq_pathSchur_of_lt hb1 E hr₀ (L := k) le_rfl] with ω hω
    simp only [Function.comp_apply, hω]
  rw [eLpNorm_congr_ae hae, eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hP]
  exact hpath W hW0 p hp2 hpε (r₀ + 2 * k) (by omega) (by exact_mod_cast hrT) E hE

/-- The exit event, the complement of `clkReg b E d' · L`. -/
theorem tdc_not_reg_eq {L : ℕ} (b E d' : ℝ) :
    {ω : GrowthSample W r₀ L | ¬ clkReg b E d' ω L} =
      {ω | ∃ k ≤ L, d' < matchedDistance b E (grownSchur E ω k)} := by
  ext ω
  simp only [clkReg, Set.mem_ofPred_eq, not_forall, not_le, exists_prop]

/-- `‖1_A f‖_p ≤ μ(A)^{1/(2p)} ‖f‖_{2p}`. -/
theorem tdc_eLpNorm_indicator_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {A : Set Ω}
    (hA : MeasurableSet A) {f : Ω → ℝ} (hf : AEStronglyMeasurable f ν) {p : ℝ} (hp : 0 < p) :
    eLpNorm (A.indicator f) (ENNReal.ofReal p) ν ≤
      ν A ^ (1 / (2 * p)) * eLpNorm f (ENNReal.ofReal (2 * p)) ν := by
  have e : A.indicator f = fun ω => A.indicator (fun _ => (1 : ℝ)) ω * f ω := by
    funext ω
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  rw [e]
  refine (wl_eLpNorm_mul_le (measurable_const.indicator hA).aestronglyMeasurable hf hp).trans
    (mul_le_mul' (le_of_eq ?_) le_rfl)
  have h2p : ENNReal.ofReal (2 * p) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [eLpNorm_indicator_const hA.nullMeasurableSet h2p ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [enorm_one, one_mul]

/-- **Exit arithmetic**: `exp(-cW log W)^{1/(2p)} ≤ W^{-1/2}` for `W ≥ max 1 ⌈p/c⌉`. -/
theorem tdc_exit_le {c p : ℝ} (hc : 0 < c) (hp : 0 < p) {W : ℕ} (hW1 : 1 ≤ W)
    (hW : p / c ≤ W) :
    Real.exp (-(c * W * Real.log W)) ^ (1 / (2 * p)) ≤ (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW1
  rw [← Real.exp_mul, Real.rpow_def_of_pos hWr]
  refine Real.exp_le_exp.mpr ?_
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW1)
  have hcW : 1 ≤ c * W / p := by
    rw [le_div_iff₀ hp]; rw [div_le_iff₀ hc] at hW; linarith
  have e : -(c * W * Real.log W) * (1 / (2 * p)) = -(c * W / p) * Real.log W / 2 := by
    field_simp
  rw [e]
  nlinarith

end Moments

/-!
## 7. Decay along the growth
-/

/-- **Tagged decay along the growth**: `q < 1` after `b, κ`; then for each
`p ≥ 1` there are `C, W₀` such that, for `W ≥ W₀`, both cores, `r₀ + 2L ≤ TW`, `E ∈ I`, and every
final position tag `T` on at most two positions `j₁, j₂` whose tagged positions are at distance
`≥ ℓ` from both ends of the final path, under `growthLaw W r₀ L b`:
`‖max_i |D_i(X_L, Y_L)|‖_p ≤ C (q^ℓ + W^{-1/2})`, `Y_L` the clock with the induced tags. -/
theorem tdc_growth_decay (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hM : TdcLayerMean) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
      ∀ (W : ℕ), W₀ ≤ W → 0 < W → ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ,
      ((r₀ + 2 * L : ℕ) : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      ∀ (Tg : ℕ → Bool) (j₁ j₂ ℓ : ℕ), (∀ j, Tg j = true → j = j₁ ∨ j = j₂) →
        (∀ j, j < r₀ + 2 * L → Tg j = true → ℓ ≤ j ∧ ℓ + j + 1 ≤ r₀ + 2 * L) →
        eLpNorm (fun ω : GrowthSample W r₀ L => tdcMaxD b E (grownSchur E ω L)
            (clkClock b E (tdcCoreTag L Tg) (tdcLayerTag r₀ L Tg) ω L)) (ENNReal.ofReal p)
          (growthLaw W r₀ L b) ≤ ENNReal.ofReal (C * (q ^ ℓ + (W : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨d₀, q, hd₀, hq0, hq1, hstepLp⟩ := tdc_step_Lp hcount hgrad hM b hb0 hb1 κ hκ
  have hsr := scalarRecursionContract_holds hcount hgrad
  obtain ⟨d₀ₑ, hd₀ₑ, hexit⟩ := hsr.exit b hb0 hb1 κ T hκ
  set d' := min d₀ d₀ₑ with hd'
  have hd'0 : 0 < d' := lt_min hd₀ hd₀ₑ
  obtain ⟨c, We, hc, hexit'⟩ := hexit d' hd'0 (min_le_right _ _)
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  refine ⟨q, hq0, hq1, fun p hp => ?_⟩
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨C₁, W₁, hC₁, hstep⟩ := hstepLp p hp
  obtain ⟨Cu, Wu, hCu, hclk⟩ := taggedClockInput_holds hcount hgrad b hb0 hb1 κ T hκ (2 * p)
    (by linarith)
  obtain ⟨ε₀, Cd, hε₀, hdist⟩ := tdc_distance_growth (matchedTraces_holds hcount hgrad)
    b hb0 hb1 κ T hκ
  set w0 : ℕ := max (max W₁ Wu) (max We (max ⌈2 * p / ε₀⌉₊ (max 1 ⌈p / c⌉₊)))
  set Cd' := max Cd 0
  set β₀ := (Cd' * Real.sqrt (2 * p) + 1) * Cu
  have hq' : 0 < 1 - q := by linarith
  refine ⟨max (3 * Cu) (C₁ * β₀ / (1 - q) + 3 * Cu), w0, by positivity, ?_⟩
  intro W hW hW0 r₀ hr₀ L hL E hE Tg j₁ j₂ ℓ hT hℓ
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW₁ : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWu : Wu ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hWe : We ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hWε : 2 * p / ε₀ ≤ W := by
    have : ⌈2 * p / ε₀⌉₊ ≤ W := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))) hW
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hWc : p / c ≤ W := by
    have : ⌈p / c⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hW
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη (hbulk E hE).1
  have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
  have hr₀2 : r₀ ≤ 2 := by rcases hr₀ with h | h <;> omega
  set τ₀ : Fin r₀ → Bool := tdcCoreTag L Tg
  set τ := tdcLayerTag r₀ L Tg
  have hcount2 : clkTagCount τ L ≤ 2 := tdc_tagCount_le hT
  set w := (W : ℝ) ^ (-(1 / 2 : ℝ)) with hw
  have hw0 : 0 ≤ w := tdc_rpow_half_nonneg W
  have hinvw : 1 / (W : ℝ) ≤ w := tdc_inv_le_rpow_half hW0
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hp2p : ENNReal.ofReal p ≤ ENNReal.ofReal (2 * p) := ENNReal.ofReal_le_ofReal (by linarith)
  -- the case without any tag
  by_cases htag : ∃ j, j < r₀ + 2 * L ∧ Tg j = true
  swap
  · push Not at htag
    have h0 : ∀ i : Fin r₀, τ₀ i = false := by
      intro i
      have := htag (i.val + L) (by omega)
      simpa [τ₀, tdcCoreTag] using this
    have h1 : ∀ k, k < L → ∀ i, τ k i = false := by
      intro k hk i
      simp only [τ, tdcLayerTag]
      split_ifs
      · simpa using htag _ (by omega)
      · simpa using htag _ (by omega)
    have hz0 : (fun ω : GrowthSample W r₀ L => tdcMaxD b E (grownSchur E ω L)
        (clkClock b E τ₀ τ ω L)) = fun _ => 0 := by
      funext ω
      rw [tdc_clock_untagged b E h0 h1 ω L le_rfl, tdc_maxD_zero]
    rw [hz0, eLpNorm_fun_zero]
    exact bot_le
  obtain ⟨j₀, hj₀, hTj₀⟩ := htag
  have hℓL : ℓ ≤ L := tdc_le_of_tagged hr₀2 hℓ hj₀ hTj₀
  set k₁ := L - ℓ with hk₁def
  have hk₁ : k₁ + ℓ = L := by omega
  have huntag : ∀ k, k₁ ≤ k → k < L → τ k = fun _ => false := fun k hk hkL =>
    funext fun i => tdc_layerTag_false hℓ (by omega) hkL i
  have hLT : ∀ k, k ≤ L → ((r₀ + 2 * k : ℕ) : ℝ) ≤ T * W := fun k hk =>
    le_trans (by exact_mod_cast (by omega : r₀ + 2 * k ≤ r₀ + 2 * L)) hL
  have hu : ∀ k, k ≤ L → eLpNorm (fun ω : GrowthSample W r₀ k => clkTrace (clkClock b E τ₀ τ ω k))
      (ENNReal.ofReal (2 * p)) (growthLaw W r₀ k b) ≤ ENNReal.ofReal Cu := fun k hk =>
    (hclk W hWu hW0).2 r₀ hr₀ k (hLT k hk) E hE τ₀ τ ((clkTagCount_mono τ hk).trans hcount2) k
      le_rfl
  have hum : ∀ k, Measurable (fun ω : GrowthSample W r₀ k => clkTrace (clkClock b E τ₀ τ ω k)) :=
    fun k => clk_measurable_trace (clk_measurable_clock b E τ₀ τ k)
  have hdm : ∀ k, Measurable (fun ω : GrowthSample W r₀ k =>
      matchedDistance b E (grownSchur E ω k)) :=
    fun k => (srec_measurable_matchedDistance b E W).comp (clk_measurable_grownSchur E k)
  have hCd' : 0 ≤ Cd' := le_max_right _ _
  have hβ₀ : 0 ≤ β₀ := by positivity
  -- the forcing term
  have hβ : ∀ k, k ≤ L → eLpNorm (fun ω : GrowthSample W r₀ k =>
      (matchedDistance b E (grownSchur E ω k) + w) * clkTrace (clkClock b E τ₀ τ ω k))
        (ENNReal.ofReal p) (growthLaw W r₀ k b) ≤ ENNReal.ofReal (β₀ * w) := by
    intro k hk
    have := clk_isProb_growthLaw W r₀ k b
    have hd := hdist W hW0 (2 * p) (by linarith) (by
      rw [div_le_iff₀ hε₀] at hWε; linarith) r₀ k hr₀1 (hLT k hk) E hE
    have hdu : eLpNorm (fun ω : GrowthSample W r₀ k => matchedDistance b E (grownSchur E ω k) *
        clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal p) (growthLaw W r₀ k b) ≤
          ENNReal.ofReal (Cd' * Real.sqrt (2 * p) * w * Cu) := by
      refine (wl_eLpNorm_mul_le (hdm k).aestronglyMeasurable (hum k).aestronglyMeasurable
        hp0).trans ?_
      have h1 : ENNReal.ofReal (Cd * Real.sqrt (2 * p) / W) ≤
          ENNReal.ofReal (Cd' * Real.sqrt (2 * p) * w) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hs := Real.sqrt_nonneg (2 * p)
        calc Cd * Real.sqrt (2 * p) / W ≤ Cd' * Real.sqrt (2 * p) / W := by
              gcongr; exact le_max_left _ _
          _ = Cd' * Real.sqrt (2 * p) * (1 / W) := by ring
          _ ≤ Cd' * Real.sqrt (2 * p) * w := by gcongr
      calc _ ≤ ENNReal.ofReal (Cd' * Real.sqrt (2 * p) * w) * ENNReal.ofReal Cu :=
            mul_le_mul' (hd.trans h1) (hu k hk)
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    have hwu : eLpNorm (fun ω : GrowthSample W r₀ k => w * clkTrace (clkClock b E τ₀ τ ω k))
        (ENNReal.ofReal p) (growthLaw W r₀ k b) ≤ ENNReal.ofReal (w * Cu) :=
      tdc_eLpNorm_smul_le hw0 ((eLpNorm_le_eLpNorm_of_exponent_le hp2p).trans (hu k hk))
    have e : (fun ω : GrowthSample W r₀ k =>
        (matchedDistance b E (grownSchur E ω k) + w) * clkTrace (clkClock b E τ₀ τ ω k)) =
          fun ω => matchedDistance b E (grownSchur E ω k) * clkTrace (clkClock b E τ₀ τ ω k) +
            w * clkTrace (clkClock b E τ₀ τ ω k) := by
      funext ω; ring
    rw [e]
    refine (tdc_eLpNorm_add_le hp (by positivity) (by positivity) hdu hwu).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  -- the recursion
  set a : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun ω : GrowthSample W r₀ k => tdcZ b E d' τ₀ τ ω k)
    (ENNReal.ofReal p) (growthLaw W r₀ k b) with ha
  have ha0 : a k₁ ≤ ENNReal.ofReal (3 * Cu) := by
    have := clk_isProb_growthLaw W r₀ k₁ b
    refine (eLpNorm_mono_ae_real (tdc_measurable_Z b E d' τ₀ τ k₁).aestronglyMeasurable ?_).trans
      (tdc_eLpNorm_smul_le (by norm_num) ((eLpNorm_le_eLpNorm_of_exponent_le hp2p).trans
        (hu k₁ (by omega))))
    filter_upwards [clk_ae_good W r₀ k₁ b] with ω hω
    rw [Real.norm_of_nonneg (tdcZ_nonneg _ _ _ _ _ _ _)]
    unfold tdcZ
    refine (Set.indicator_le_self' (fun _ _ => tdcMaxD_nonneg _ _ _ _) ω).trans ?_
    exact tdc_maxD_le hz (clk_grownSchur_isHermitian E hω k₁) (clkClock_posSemidef b E τ₀ τ ω k₁)
  have hrec : ∀ i, i < ℓ → a (k₁ + i + 1) ≤ ENNReal.ofReal q * a (k₁ + i) +
      ENNReal.ofReal (C₁ * (β₀ * w)) := by
    intro i hi
    have hkL : k₁ + i < L := by omega
    have h := tdc_iter_step (k := k₁ + i) (b := b) (E := E) (d' := d') (W := W) (r₀ := r₀) hq0 hC₁
      hw0 hp τ₀ τ (huntag _ (by omega) hkL) (fun X hX hdX Y hY =>
        hstep W hW0 hW₁ X Y hX hY E hE (hdX.trans (min_le_left _ _)))
    refine h.trans (add_le_add le_rfl ?_)
    rw [ENNReal.ofReal_mul hC₁]
    exact mul_le_mul' le_rfl (hβ _ (by omega))
  have haL := tdc_iter (a := a) hq0 hq1 (by positivity) (by positivity) ha0 ℓ hrec
  rw [hk₁] at haL
  -- exit removal
  have := clk_isProb_growthLaw W r₀ L b
  set u := fun ω : GrowthSample W r₀ L => clkTrace (clkClock b E τ₀ τ ω L)
  set Rc := {ω : GrowthSample W r₀ L | ¬ clkReg b E d' ω L} with hRc
  have hRcm : MeasurableSet Rc := (clk_measurableSet_reg b E d' L).compl
  have hpt : ∀ᵐ ω ∂growthLaw W r₀ L b, ‖tdcMaxD b E (grownSchur E ω L) (clkClock b E τ₀ τ ω L)‖ ≤
      tdcZ b E d' τ₀ τ ω L + Rc.indicator (fun ω => 3 * u ω) ω := by
    filter_upwards [clk_ae_good W r₀ L b] with ω hω
    rw [Real.norm_of_nonneg (tdcMaxD_nonneg _ _ _ _)]
    have hle := tdc_maxD_le hz (clk_grownSchur_isHermitian E hω L) (clkClock_posSemidef b E τ₀ τ ω L)
    unfold tdcZ
    by_cases hr : clkReg b E d' ω L
    · rw [Set.indicator_of_mem (show ω ∈ {ω | clkReg b E d' ω L} from hr),
        Set.indicator_of_notMem (show ω ∉ Rc from fun h => h hr), add_zero]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | clkReg b E d' ω L} from hr),
        Set.indicator_of_mem (show ω ∈ Rc from hr), zero_add]
      exact hle
  have hexitm : growthLaw W r₀ L b Rc ≤ ENNReal.ofReal (Real.exp (-(c * W * Real.log W))) := by
    rw [hRc, tdc_not_reg_eq]
    exact hexit' W hWe hW0 r₀ hr₀ L hL E hE
  have hind : eLpNorm (Rc.indicator (fun ω => 3 * u ω)) (ENNReal.ofReal p) (growthLaw W r₀ L b) ≤
      ENNReal.ofReal (w * (3 * Cu)) := by
    refine (tdc_eLpNorm_indicator_le hRcm ((hum L).const_mul 3).aestronglyMeasurable hp0).trans ?_
    rw [ENNReal.ofReal_mul hw0]
    refine mul_le_mul' ?_ (tdc_eLpNorm_smul_le (by norm_num) (hu L le_rfl))
    calc growthLaw W r₀ L b Rc ^ (1 / (2 * p))
        ≤ ENNReal.ofReal (Real.exp (-(c * W * Real.log W))) ^ (1 / (2 * p)) :=
          ENNReal.rpow_le_rpow hexitm (by positivity)
      _ = ENNReal.ofReal (Real.exp (-(c * W * Real.log W)) ^ (1 / (2 * p))) :=
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity)
      _ ≤ ENNReal.ofReal w := ENNReal.ofReal_le_ofReal (tdc_exit_le hc hp0 (by
          have : 1 ≤ max 1 ⌈p / c⌉₊ := le_max_left _ _
          have h2 : max 1 ⌈p / c⌉₊ ≤ W := le_trans (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _))) hW
          omega) hWc)
  have hmZ := tdc_measurable_Z (W := W) (r₀ := r₀) (L := L) b E d' τ₀ τ L
  calc eLpNorm (fun ω : GrowthSample W r₀ L => tdcMaxD b E (grownSchur E ω L)
          (clkClock b E τ₀ τ ω L)) (ENNReal.ofReal p) (growthLaw W r₀ L b)
      ≤ eLpNorm (fun ω => tdcZ b E d' τ₀ τ ω L + Rc.indicator (fun ω => 3 * u ω) ω)
          (ENNReal.ofReal p) (growthLaw W r₀ L b) :=
        eLpNorm_mono_ae_real (tdc_measurable_maxD_k b E τ₀ τ L).aestronglyMeasurable hpt
    _ ≤ ENNReal.ofReal (q ^ ℓ * (3 * Cu) + C₁ * (β₀ * w) / (1 - q) + w * (3 * Cu)) :=
        tdc_eLpNorm_add_le hp (by positivity) (by positivity) haL hind
    _ ≤ ENNReal.ofReal (max (3 * Cu) (C₁ * β₀ / (1 - q) + 3 * Cu) * (q ^ ℓ + w)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm1 := le_max_left (3 * Cu) (C₁ * β₀ / (1 - q) + 3 * Cu)
        have hm2 := le_max_right (3 * Cu) (C₁ * β₀ / (1 - q) + 3 * Cu)
        have hqℓ : 0 ≤ q ^ ℓ := pow_nonneg hq0 ℓ
        have e : C₁ * (β₀ * w) / (1 - q) + w * (3 * Cu) = (C₁ * β₀ / (1 - q) + 3 * Cu) * w := by
          field_simp
        nlinarith [mul_le_mul_of_nonneg_right hm1 hqℓ, mul_le_mul_of_nonneg_right hm2 hw0]

/-!
## 8. Path-level statements
-/

/-- Every `r ≥ 1` is `r₀ + 2L` with `r₀ ∈ {1, 2}`. -/
theorem tdc_core_decomp {r : ℕ} (hr : 1 ≤ r) : ∃ r₀ L : ℕ, (r₀ = 1 ∨ r₀ = 2) ∧ r = r₀ + 2 * L := by
  rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨2, t - 1, Or.inr rfl, by omega⟩
  · exact ⟨1, t, Or.inl rfl, by omega⟩

/-- Under `growthLaw`, almost surely the final path quantities are the grown ones: `X_L` is the
Schur matrix of `pgPath ω L` and the clock with the induced tags is its tagged source. -/
theorem tdc_ae_final {W r₀ L : ℕ} {b : ℝ} (hb1 : b < 1 / 2) (E : ℝ) (hz : 0 < (boundaryZ b E).im)
    (hr₀ : 1 ≤ r₀) (Tg : ℕ → Bool) :
    ∀ᵐ ω ∂growthLaw W r₀ L b, pathSchur E (pgPath ω L) = grownSchur E ω L ∧
      clkCoreSource b E (fun j : Fin (r₀ + 2 * L) => Tg j) (pgPath ω L) =
        clkClock b E (tdcCoreTag L Tg) (tdcLayerTag r₀ L Tg) ω L := by
  filter_upwards [ae_grownSchur_eq_pathSchur_of_lt hb1 E hr₀ (L := L) le_rfl,
    tdc_clock_eq_source (W := W) (L := L) hb1 E hz hr₀ Tg] with ω h1 h2
  refine ⟨h1.symm, ?_⟩
  rw [h2 L le_rfl]
  congr 1
  funext j
  simp [tdcStageTag]

/-- **Tagged decay under `pathLaw`** (the exterior path of the tagged-trace lemma): `q < 1` after
`b, κ`; for each `p ≥ 1` there are `C, W₀`; for `W ≥ W₀`, `1 ≤ r ≤ TW`, `E ∈ I`, and every
position tag `T` on at most two positions whose tagged positions are at distance `≥ ℓ` from both
path ends, `‖max_i |D_i(X_r, Y)|‖_{L^p(pathLaw W r b)} ≤ C(q^ℓ + W^{-1/2})`, where `X_r = pathSchur`
and `Y = clkCoreSource b E T` is the tagged source. -/
theorem tdc_path_decay (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hM : TdcLayerMean) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
      ∀ (W : ℕ), W₀ ≤ W → 0 < W → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      ∀ (Tg : ℕ → Bool) (j₁ j₂ ℓ : ℕ), (∀ j, Tg j = true → j = j₁ ∨ j = j₂) →
        (∀ j, j < r → Tg j = true → ℓ ≤ j ∧ ℓ + j + 1 ≤ r) →
        eLpNorm (fun π : PathSample W r => tdcMaxD b E (pathSchur E π)
            (clkCoreSource b E (fun j : Fin r => Tg j) π)) (ENNReal.ofReal p) (pathLaw W r b) ≤
          ENNReal.ofReal (C * (q ^ ℓ + (W : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨q, hq0, hq1, hG⟩ := tdc_growth_decay hcount hgrad hM b hb0 hb1 κ T hκ
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  refine ⟨q, hq0, hq1, fun p hp => ?_⟩
  obtain ⟨C, W₀, hC, hGW⟩ := hG p hp
  refine ⟨C, W₀, hC, fun W hW hW0 r hr hrT E hE Tg j₁ j₂ ℓ hT hℓ => ?_⟩
  obtain ⟨r₀, L, hr₀, rfl⟩ := tdc_core_decomp hr
  have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη (hbulk E hE).1
  have hP := measurePreserving_pgPath (W := W) b hr₀1 L L le_rfl
  have hm : Measurable (fun π : PathSample W (r₀ + 2 * L) => tdcMaxD b E (pathSchur E π)
      (clkCoreSource b E (fun j : Fin (r₀ + 2 * L) => Tg j) π)) :=
    tdc_measurable_maxD b E (measurable_pathSchur W _ E) (clk_measurable_coreSource W _ b E _)
  rw [← eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hP]
  have hae : (fun π : PathSample W (r₀ + 2 * L) => tdcMaxD b E (pathSchur E π)
      (clkCoreSource b E (fun j : Fin (r₀ + 2 * L) => Tg j) π)) ∘ (fun ω => pgPath ω L) =ᵐ[growthLaw W r₀ L b]
      fun ω => tdcMaxD b E (grownSchur E ω L)
        (clkClock b E (tdcCoreTag L Tg) (tdcLayerTag r₀ L Tg) ω L) := by
    filter_upwards [tdc_ae_final (W := W) (L := L) hb1 E hz hr₀1 Tg] with ω h
    simp only [Function.comp_apply, h.1, h.2]
  rw [eLpNorm_congr_ae hae]
  exact hGW W hW hW0 r₀ hr₀ L (by exact_mod_cast hrT) E hE Tg j₁ j₂ ℓ hT hℓ

/-- **Clock moments of a tagged source under `pathLaw`** (the clock-moments lemma through the growth):
for each `p ≥ 1` there are `C, W₀`; for `W ≥ W₀`, `1 ≤ r ≤ TW`, `E ∈ I` and a tag on at most two
positions, `‖W⁻¹ Tr Y‖_{L^p(pathLaw W r b)} ≤ C`, `Y = clkCoreSource b E T`. -/
theorem tdc_path_clock (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧
      ∀ (W : ℕ), W₀ ≤ W → 0 < W → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      ∀ (Tg : ℕ → Bool) (j₁ j₂ : ℕ), (∀ j, Tg j = true → j = j₁ ∨ j = j₂) →
        eLpNorm (fun π : PathSample W r => clkTrace (clkCoreSource b E (fun j : Fin r => Tg j) π))
          (ENNReal.ofReal p) (pathLaw W r b) ≤ ENNReal.ofReal C := by
  intro b hb0 hb1 κ T hκ p hp
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  obtain ⟨C, W₀, hC, hclk⟩ := taggedClockInput_holds hcount hgrad b hb0 hb1 κ T hκ p hp
  refine ⟨C, W₀, hC, fun W hW hW0 r hr hrT E hE Tg j₁ j₂ hT => ?_⟩
  obtain ⟨r₀, L, hr₀, rfl⟩ := tdc_core_decomp hr
  have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη (hbulk E hE).1
  have hP := measurePreserving_pgPath (W := W) b hr₀1 L L le_rfl
  have hm : Measurable (fun π : PathSample W (r₀ + 2 * L) =>
      clkTrace (clkCoreSource b E (fun j : Fin (r₀ + 2 * L) => Tg j) π)) :=
    clk_measurable_trace (clk_measurable_coreSource W _ b E _)
  rw [← eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hP]
  have hae : (fun π : PathSample W (r₀ + 2 * L) =>
      clkTrace (clkCoreSource b E (fun j : Fin (r₀ + 2 * L) => Tg j) π)) ∘ (fun ω => pgPath ω L)
      =ᵐ[growthLaw W r₀ L b]
      fun ω => clkTrace (clkClock b E (tdcCoreTag L Tg) (tdcLayerTag r₀ L Tg) ω L) := by
    filter_upwards [tdc_ae_final (W := W) (L := L) hb1 E hz hr₀1 Tg] with ω h
    simp only [Function.comp_apply, h.2]
  rw [eLpNorm_congr_ae hae]
  exact (hclk W hW hW0).2 r₀ hr₀ L (by exact_mod_cast hrT) E hE _ _ (tdc_tagCount_le hT) L le_rfl

end BlockBand.Layers
