module

public import BlockBand.SourceProcess.PhysApprox.B3BirthClose
public import BlockBand.SourceProcess.PhysApprox.ClosingGramInt
public import BlockBand.SourceProcess.ClosedPath.Commute
public import BlockBand.SourceProcess.ClosedPath.FarPort
public import BlockBand.SourceProcess.Closing.PhysHardy
public import BlockBand.SourceProcess.Closing.PhaseAvg
public import BlockBand.SourceProcess.ClosingAux.Meas
public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.Transmission.Bridge.AlmostSure

/-!
# The closing correction of the newborn `𝒦` entries

At length `n`, with `A = farEmbed A_-`, `Π = farEmbed Π`, `𝕊 = 𝕊_n`, `N = Π𝕊A` and
`R(z) = (1 − zN)⁻¹` (`birthKRes`), the correction is `2iηz V_nᴴR(z)Π𝕊V_n` (`birthKCorrAt`).
* **`birthKCorr_eq_in`, `birthKCorr_eq_out`** (algebra, every `ω`, every `z`): `A` commutes
  with `R(z)` and `AΠ = Π`, `Aᴴ = A`, so
  `V_nᴴR(z)Π𝕊V_n = (AV_n)ᴴ(R(z)Π𝕊V_n) = (R(z)ᴴAV_n)ᴴ(Π𝕊V_n)`: the correction only sees the
  omitted far input `AV_n` (`birthKIn`) and the paired omitted far output `Π𝕊V_n`
  (`birthKOut`) of each probe column.
* **`norm_birthKCorr_le_in`, `norm_birthKCorr_le_out`** (Cauchy–Schwarz):
  `|corr_ab| ≤ 2η ‖(AV)_a‖ ‖(RΠ𝕊V)_b‖` and `|corr_ab| ≤ 2η ‖(RᴴAV)_a‖ ‖(Π𝕊V)_b‖`.
* **`lintegral_indicator_le_split`** (measure theory): Tonelli in the phase, then
  `2uv ≤ εu² + v²/ε` in the path.
* **`complexBirthKClosing_of_parts`**: `ComplexBirthKClosing` from four estimates, stated here as
  hypotheses:
  - `BirthKFarIn`, `BirthKFarOut`: the newborn's omitted far input mass `E‖(AV)_i‖²` and its
    paired omitted far output mass `E‖(Π𝕊V)_i‖²` tend to `0` one step after its birth (the far birth
    mass is `O(g_A^in/W)`);
  - `BirthKResIn`, `BirthKResOut`: on the physical cap event, the path second moment of the
    **phase mean** `E_z‖R(z)ᴴ(AV)_c‖`, resp. `E_z‖R(z)(Π𝕊V)_c‖`, is bounded at birth steps,
    for every probe column `c` (the phase mean of `|1/(1 − √(1−t)z)|` is
    `≍ log(1/t)`, paid by an omitted far amplitude `O(t^{1/2})` per mode).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal

variable {np : ℕ}

/-!
## The omitted far input, the paired omitted far output and the resolvent
-/

/-- The omitted far input `AV_n` of the probe frame at length `n` (`A = farEmbed A_-`, omitted
channels chosen at `n_s = closeLen s W`). -/
def birthKIn (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (x : ProbedPath W np) :
    Matrix (Fin 2 × Fin W) (Fin np) ℂ :=
  farEmbed (omittedProj b E h W (closeLen s W) x.1) * probeFrame b E W n τ m x

/-- The paired omitted far output `Π𝕊_nV_n` of the probe frame at length `n`. -/
def birthKOut (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) (x : ProbedPath W np) :
    Matrix (Fin 2 × Fin W) (Fin np) ℂ :=
  farEmbed (closingPairing b E h W (closeLen s W) x.1) * scatteringMatrix b E W n x.1 *
    probeFrame b E W n τ m x

/-- The omitted-mode resolvent `R(z) = (1 − zN_n)⁻¹`, `N_n = Π𝕊_nA`, `z = e^{iθ}`. -/
def birthKRes (b E s h : ℝ) (W n : ℕ) (ω : GrowthPath W) (θ : ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (1 - phase θ • closingN (scatteringMatrix b E W n ω)
    (farEmbed (omittedProj b E h W (closeLen s W) ω))
    (farEmbed (closingPairing b E h W (closeLen s W) ω)))⁻¹

/-!
## Algebra
-/

section Algebra

variable {ι c : Type*} [Fintype ι] [DecidableEq ι]

/-- `VᴴR(z)Π𝕊V = (AV)ᴴ(R(z)Π𝕊V)` when `A² = A`, `Aᴴ = A`, `AΠ = Π`. -/
theorem corr_core_eq_in {S A Pi : Matrix ι ι ℂ} (V : Matrix ι c ℂ) (z : ℂ) (hAA : A * A = A)
    (hAH : Aᴴ = A) (hAP : A * Pi = Pi) :
    Vᴴ * (1 - z • closingN S A Pi)⁻¹ * Pi * S * V =
      (A * V)ᴴ * ((1 - z • closingN S A Pi)⁻¹ * (Pi * S * V)) := by
  have hc := A_mul_inv (S := S) (z := z) hAA hAP
  rw [conjTranspose_mul, hAH]
  symm
  calc Vᴴ * A * ((1 - z • closingN S A Pi)⁻¹ * (Pi * S * V))
      = Vᴴ * (A * (1 - z • closingN S A Pi)⁻¹) * Pi * S * V := by
        simp only [Matrix.mul_assoc]
    _ = Vᴴ * (1 - z • closingN S A Pi)⁻¹ * (A * Pi) * S * V := by
        rw [hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAP]

omit [DecidableEq ι] in
/-- `(AV)ᴴ(RY) = (RᴴAV)ᴴY`. -/
theorem corr_core_eq_out {A R : Matrix ι ι ℂ} (V Y : Matrix ι c ℂ) :
    (A * V)ᴴ * (R * Y) = (Rᴴ * (A * V))ᴴ * Y := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

end Algebra

variable {W : ℕ}

theorem omittedEmbed_mul_self (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    farEmbed (omittedProj b E h W n ω) * farEmbed (omittedProj b E h W n ω) =
      farEmbed (omittedProj b E h W n ω) := by
  rw [farEmbed_mul, omittedProj_mul_self]

theorem omittedEmbed_conjTranspose (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    (farEmbed (omittedProj b E h W n ω))ᴴ = farEmbed (omittedProj b E h W n ω) := by
  rw [farEmbed_conjTranspose, omittedProj_conjTranspose]

theorem omittedEmbed_mul_pairing (b E h : ℝ) (n : ℕ) (ω : GrowthPath W) :
    farEmbed (omittedProj b E h W n ω) * farEmbed (closingPairing b E h W n ω) =
      farEmbed (closingPairing b E h W n ω) := by
  rw [farEmbed_mul, omittedProj_mul_closingPairing]

/-- **The correction through the omitted far input.** -/
theorem birthKCorr_eq_in (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (y : ProbedPath W np × ℝ) :
    birthKCorrAt b E s h τ m W n y =
      ((2 * etaZ b E : ℝ) * Complex.I * phase y.2) •
        ((birthKIn b E s h τ m W n y.1)ᴴ *
          (birthKRes b E s h W n y.1.1 y.2 * birthKOut b E s h τ m W n y.1)) := by
  unfold birthKCorrAt birthKIn birthKOut birthKRes
  rw [corr_core_eq_in _ _ (omittedEmbed_mul_self b E h _ _)
    (omittedEmbed_conjTranspose b E h _ _) (omittedEmbed_mul_pairing b E h _ _)]

/-- **The correction through the paired omitted far output.** -/
theorem birthKCorr_eq_out (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ) (y : ProbedPath W np × ℝ) :
    birthKCorrAt b E s h τ m W n y =
      ((2 * etaZ b E : ℝ) * Complex.I * phase y.2) •
        (((birthKRes b E s h W n y.1.1 y.2)ᴴ * birthKIn b E s h τ m W n y.1)ᴴ *
          birthKOut b E s h τ m W n y.1) := by
  rw [birthKCorr_eq_in, birthKIn, corr_core_eq_out, ← birthKIn]

theorem norm_corrCoeff (b E : ℝ) (θ : ℝ) :
    ‖((2 * etaZ b E : ℝ) : ℂ) * Complex.I * phase θ‖ = |2 * etaZ b E| := by
  rw [norm_mul, norm_mul, Complex.norm_I, norm_phase, mul_one, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

/-- `|corr_ab| ≤ 2η ‖(AV)_a‖ ‖(RΠ𝕊V)_b‖`. -/
theorem norm_birthKCorr_le_in (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ)
    (y : ProbedPath W np × ℝ) (a a' : Fin np) :
    ‖birthKCorrAt b E s h τ m W n y a a'‖ ≤ |2 * etaZ b E| *
      (l2 ((birthKIn b E s h τ m W n y.1)ᵀ a) *
        l2 ((birthKRes b E s h W n y.1.1 y.2 * birthKOut b E s h τ m W n y.1)ᵀ a')) := by
  rw [birthKCorr_eq_in, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_corrCoeff]
  exact mul_le_mul_of_nonneg_left (norm_conjTranspose_mul_apply_le _ _ _ _) (abs_nonneg _)

/-- `|corr_ab| ≤ 2η ‖(RᴴAV)_a‖ ‖(Π𝕊V)_b‖`. -/
theorem norm_birthKCorr_le_out (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ)
    (y : ProbedPath W np × ℝ) (a a' : Fin np) :
    ‖birthKCorrAt b E s h τ m W n y a a'‖ ≤ |2 * etaZ b E| *
      (l2 (((birthKRes b E s h W n y.1.1 y.2)ᴴ * birthKIn b E s h τ m W n y.1)ᵀ a) *
        l2 ((birthKOut b E s h τ m W n y.1)ᵀ a')) := by
  rw [birthKCorr_eq_out, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_corrCoeff]
  exact mul_le_mul_of_nonneg_left (norm_conjTranspose_mul_apply_le _ _ _ _) (abs_nonneg _)

theorem measurable_birthKIn (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    Measurable fun x : ProbedPath W np => birthKIn b E s h τ m W n x :=
  measurable_matrix_mul'
    (measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp measurable_fst))
    (measurable_probeFrame b E W n τ m)

theorem measurable_birthKOut (b E s h : ℝ) (τ m : Fin np → ℝ) (W n : ℕ) :
    Measurable fun x : ProbedPath W np => birthKOut b E s h τ m W n x :=
  measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp measurable_fst))
    ((measurable_scatteringMatrix b E n).comp measurable_fst))
    (measurable_probeFrame b E W n τ m)

/-!
## The integral bound
-/

/-- `u v ≤ (ε/2)u² + v²/(2ε)` in `ℝ≥0∞`. -/
theorem ofReal_mul_le_amgm {u : ℝ} (hu : 0 ≤ u) (v : ℝ≥0∞) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal u * v ≤
      ENNReal.ofReal (ε / 2 * u ^ 2) + ENNReal.ofReal (1 / (2 * ε)) * v ^ 2 := by
  rcases eq_or_ne v ⊤ with rfl | hv
  · rw [ENNReal.top_pow two_ne_zero,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (show (0 : ℝ) < 1 / (2 * ε) by positivity)).ne',
      add_top]
    exact le_top
  · lift v to ℝ≥0 using hv
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hu,
      ← ENNReal.ofReal_pow (NNReal.coe_nonneg v), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    set w : ℝ := (v : ℝ)
    have key : (ε * u - w) ^ 2 / (2 * ε) = ε / 2 * u ^ 2 + 1 / (2 * ε) * w ^ 2 - u * w := by
      field_simp
      ring
    have : 0 ≤ (ε * u - w) ^ 2 / (2 * ε) := by positivity
    linarith

/-- **The split bound.** If `|f(x, θ)| ≤ k F(x) G(x, θ)` on `A ⊆ Cap × ℝ`, then
`E[1_A|f|] ≤ (εk²/2) E F² + (2ε)⁻¹ E[1_Cap (E_θ G)²]` (Tonelli in `θ`, then AM–GM). -/
theorem lintegral_indicator_le_split {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ν : Measure ℝ} [SFinite ν] (A : Set (α × ℝ)) (Cap : Set α) (hA : ∀ y ∈ A, y.1 ∈ Cap)
    (f : α × ℝ → ℂ) (F : α → ℝ) (G : α → ℝ → ℝ) (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    {k : ℝ} (hk : 0 ≤ k)
    (hpt : ∀ y ∈ A, ‖f y‖ ≤ k * (F y.1 * G y.1 y.2)) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ.prod ν ≤
      ENNReal.ofReal (ε / 2 * k ^ 2) * ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ +
        ENNReal.ofReal (1 / (2 * ε)) *
          ∫⁻ x, Cap.indicator (fun x => (∫⁻ θ, ENNReal.ofReal (G x θ) ∂ν) ^ 2) x ∂μ := by
  set Gh : α → ℝ≥0∞ := fun x => ∫⁻ θ, ENNReal.ofReal (G x θ) ∂ν
  have h1 : ∀ y : α × ℝ, ‖A.indicator f y‖ₑ ≤
      Cap.indicator (fun x => ENNReal.ofReal (k * F x)) y.1 * ENNReal.ofReal (G y.1 y.2) := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hA y hy),
        ← ENNReal.ofReal_mul (mul_nonneg hk (hF0 _)), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hpt y hy).trans_eq (by ring))
    · rw [Set.indicator_of_notMem hy, enorm_zero]
      exact zero_le
  have h2 : ∀ x, Cap.indicator (fun x => ENNReal.ofReal (k * F x)) x ≠ ⊤ := by
    intro x
    by_cases hx : x ∈ Cap
    · rw [Set.indicator_of_mem hx]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem hx]; exact ENNReal.zero_ne_top
  have h3 : ∀ x, Cap.indicator (fun x => ENNReal.ofReal (k * F x)) x * Gh x ≤
      ENNReal.ofReal (ε / 2 * k ^ 2) * ENNReal.ofReal (F x ^ 2) +
        ENNReal.ofReal (1 / (2 * ε)) * Cap.indicator (fun x => Gh x ^ 2) x := by
    intro x
    by_cases hx : x ∈ Cap
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        ← ENNReal.ofReal_mul (by positivity)]
      refine (ofReal_mul_le_amgm (mul_nonneg hk (hF0 x)) (Gh x) hε).trans_eq ?_
      congr 2
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, mul_zero,
        add_zero]
      exact zero_le
  have hm : Measurable fun x => ENNReal.ofReal (ε / 2 * k ^ 2) * ENNReal.ofReal (F x ^ 2) :=
    ((hF.pow_const 2).ennreal_ofReal).const_mul _
  calc ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ.prod ν
      ≤ ∫⁻ y, Cap.indicator (fun x => ENNReal.ofReal (k * F x)) y.1 *
          ENNReal.ofReal (G y.1 y.2) ∂μ.prod ν := lintegral_mono h1
    _ ≤ ∫⁻ x, ∫⁻ θ, Cap.indicator (fun x => ENNReal.ofReal (k * F x)) x *
          ENNReal.ofReal (G x θ) ∂ν ∂μ := lintegral_prod_le _
    _ = ∫⁻ x, Cap.indicator (fun x => ENNReal.ofReal (k * F x)) x * Gh x ∂μ := by
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul' _ _ (h2 x)
    _ ≤ ∫⁻ x, (ENNReal.ofReal (ε / 2 * k ^ 2) * ENNReal.ofReal (F x ^ 2) +
          ENNReal.ofReal (1 / (2 * ε)) * Cap.indicator (fun x => Gh x ^ 2) x) ∂μ :=
        lintegral_mono h3
    _ = _ := by
        rw [lintegral_add_left hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The final arithmetic with `ε = C/θ` and `δ = θ²/(C(k² + 1))`. -/
theorem split_arith {k C C' θ : ℝ} (hθ : 0 < θ) (hC : 1 ≤ C) (hC' : C' ≤ C) {X Y : ℝ≥0∞}
    (hX : X ≤ ENNReal.ofReal (θ ^ 2 / (C * (k ^ 2 + 1)))) (hY : Y ≤ ENNReal.ofReal C') :
    ENNReal.ofReal (C / θ / 2 * k ^ 2) * X + ENNReal.ofReal (1 / (2 * (C / θ))) * Y ≤
      ENNReal.ofReal θ := by
  have hC0 : 0 < C := by linarith
  have hk : 0 < k ^ 2 + 1 := by positivity
  calc ENNReal.ofReal (C / θ / 2 * k ^ 2) * X + ENNReal.ofReal (1 / (2 * (C / θ))) * Y
      ≤ ENNReal.ofReal (C / θ / 2 * k ^ 2) * ENNReal.ofReal (θ ^ 2 / (C * (k ^ 2 + 1))) +
          ENNReal.ofReal (1 / (2 * (C / θ))) * ENNReal.ofReal C := by
        gcongr
        exact hY.trans (ENNReal.ofReal_le_ofReal hC')
    _ = ENNReal.ofReal (C / θ / 2 * k ^ 2 * (θ ^ 2 / (C * (k ^ 2 + 1))) +
          1 / (2 * (C / θ)) * C) := by
        rw [← ENNReal.ofReal_mul (p := C / θ / 2 * k ^ 2) (by positivity),
          ← ENNReal.ofReal_mul (p := 1 / (2 * (C / θ))) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal θ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : C / θ / 2 * k ^ 2 * (θ ^ 2 / (C * (k ^ 2 + 1))) =
            θ / 2 * (k ^ 2 / (k ^ 2 + 1)) := by
          field_simp
        have e2 : 1 / (2 * (C / θ)) * C = θ / 2 := by
          field_simp
        have hq : k ^ 2 / (k ^ 2 + 1) ≤ 1 := (div_le_one hk).2 (by linarith)
        rw [e1, e2]
        nlinarith

/-!
## The estimates
-/

/-- **Far input mass at birth** (a normalized tag's far birth mass is `O(g_A^in/W)`): one step after
its birth, the omitted far input mass `‖(AV)_i‖²` of a newborn probe column tends to `0` in mean,
uniformly over its birth step in `[n_s, ⌊WT⌋)`. -/
def BirthKFarIn : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∀ δ : ℝ, 0 < δ → ∀ i : Fin np, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
        ∫⁻ x, ENNReal.ofReal (l2 ((birthKIn b E s h τ m W (j + 1) x)ᵀ i) ^ 2)
          ∂probedPathLaw W np b ≤ ENNReal.ofReal δ

/-- **Far output mass at birth**: one step after its birth, the
paired omitted far output mass `‖(Π𝕊V)_i‖²` of a newborn probe column tends to `0` in mean,
uniformly over its birth step. -/
def BirthKFarOut : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∀ δ : ℝ, 0 < δ → ∀ i : Fin np, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ⌊(W : ℝ) * τ i⌋₊ = j →
        ∫⁻ x, ENNReal.ofReal (l2 ((birthKOut b E s h τ m W (j + 1) x)ᵀ i) ^ 2)
          ∂probedPathLaw W np b ≤ ENNReal.ofReal δ

/-- **Resolvent phase mean, input side** (the phase mean `≍ log(1/t)` of the omitted-mode
resolvent against an omitted amplitude `O(t^{1/2})`, `t(1 + |log t|) ≤ C_p t^p`): on the physical
cap event, the path second moment of the phase mean `E_z‖R(z)ᴴ(AV)_c‖` is bounded at birth steps,
for every probe column `c`. -/
def BirthKResIn : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j → ∀ c : Fin np,
        ∫⁻ x, {x : ProbedPath W np | x.1 ∈ physCapEventC b E s h K W}.indicator (fun x =>
            (∫⁻ θ, ENNReal.ofReal (l2 (((birthKRes b E s h W (j + 1) x.1 θ)ᴴ *
              birthKIn b E s h τ m W (j + 1) x)ᵀ c)) ∂phaseLaw) ^ 2) x
          ∂probedPathLaw W np b ≤ ENNReal.ofReal C

/-- **Resolvent phase mean, output side**: on the physical cap event, the path second
moment of the phase mean `E_z‖R(z)(Π𝕊V)_c‖` is bounded at birth steps, for every probe
column `c`. -/
def BirthKResOut : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ), ComplexSourceLawDomain b E τ m T → 0 < s →
    (∀ j, s < τ j) → 0 < h → h < 1 → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → IsBirthStep τ W j → ∀ c : Fin np,
        ∫⁻ x, {x : ProbedPath W np | x.1 ∈ physCapEventC b E s h K W}.indicator (fun x =>
            (∫⁻ θ, ENNReal.ofReal (l2 ((birthKRes b E s h W (j + 1) x.1 θ *
              birthKOut b E s h τ m W (j + 1) x)ᵀ c)) ∂phaseLaw) ^ 2) x
          ∂probedPathLaw W np b ≤ ENNReal.ofReal C

/-!
## The reduction
-/

/-- **`ComplexBirthKClosing` from the far birth masses and the resolvent phase means.** -/
theorem complexBirthKClosing_of_parts (hFI : BirthKFarIn) (hFO : BirthKFarOut)
    (hRI : BirthKResIn) (hRO : BirthKResOut) : ComplexBirthKClosing := by
  intro b E np τ m T s h K Vs hD R θ hθ a a'
  obtain ⟨hCSL, hs, hsτ, hh0, hh1, -⟩ := hD
  obtain ⟨C₁, hC₁⟩ := hRI b E np τ m T s h K hCSL hs hsτ hh0 hh1
  obtain ⟨C₂, hC₂⟩ := hRO b E np τ m T s h K hCSL hs hsτ hh0 hh1
  set C : ℝ := max (max C₁ C₂) 0 + 1 with hCdef
  set k : ℝ := |2 * etaZ b E| with hkdef
  have hC1 : 1 ≤ C := by have := le_max_right (max C₁ C₂) 0; linarith
  have hC0 : 0 < C := by linarith
  have hk0 : 0 ≤ k := abs_nonneg _
  have hδ : 0 < θ ^ 2 / (C * (k ^ 2 + 1)) := by positivity
  have hε : 0 < C / θ := by positivity
  have hle1 : C₁ ≤ C := by
    have := le_max_left C₁ C₂; have := le_max_left (max C₁ C₂) 0; linarith
  have hle2 : C₂ ≤ C := by
    have := le_max_right C₁ C₂; have := le_max_left (max C₁ C₂) 0; linarith
  filter_upwards [hFI b E np τ m T s h hCSL hs hsτ hh0 hh1 _ hδ a,
    hFO b E np τ m T s h hCSL hs hsτ hh0 hh1 _ hδ a', hC₁, hC₂] with W hWa hWa' hW1 hW2
  intro j hj1 hj2 hnew
  have hbirth : IsBirthStep τ W j := hnew.elim (fun e => ⟨a, e⟩) (fun e => ⟨a', e⟩)
  have hA : ∀ y ∈ b3Alive b E s h τ m R W j (Vs W),
      y.1 ∈ {x : ProbedPath W np | x.1 ∈ physCapEventC b E s h K W} := fun y hy => hy.1
  rcases hnew with hna | hna'
  · refine (lintegral_indicator_le_split (μ := probedPathLaw W np b) (ν := phaseLaw)
      (b3Alive b E s h τ m R W j (Vs W)) _ hA
      (fun y => birthKCorrAt b E s h τ m W (j + 1) y a a')
      (fun x => l2 ((birthKIn b E s h τ m W (j + 1) x)ᵀ a))
      (fun x θ => l2 ((birthKRes b E s h W (j + 1) x.1 θ *
        birthKOut b E s h τ m W (j + 1) x)ᵀ a'))
      (measurable_l2_col (measurable_birthKIn b E s h τ m W (j + 1)) a)
      (fun _ => l2_nonneg _) hk0
      (fun y _ => norm_birthKCorr_le_in b E s h τ m (j + 1) y a a') hε).trans ?_
    exact split_arith hθ hC1 hle2 (hWa j hj1 hj2 hna) (hW2 j hj1 hj2 hbirth a')
  · refine (lintegral_indicator_le_split (μ := probedPathLaw W np b) (ν := phaseLaw)
      (b3Alive b E s h τ m R W j (Vs W)) _ hA
      (fun y => birthKCorrAt b E s h τ m W (j + 1) y a a')
      (fun x => l2 ((birthKOut b E s h τ m W (j + 1) x)ᵀ a'))
      (fun x θ => l2 (((birthKRes b E s h W (j + 1) x.1 θ)ᴴ *
        birthKIn b E s h τ m W (j + 1) x)ᵀ a))
      (measurable_l2_col (measurable_birthKOut b E s h τ m W (j + 1)) a')
      (fun _ => l2_nonneg _) hk0
      (fun y _ => (norm_birthKCorr_le_out b E s h τ m (j + 1) y a a').trans_eq
        (by ring)) hε).trans ?_
    exact split_arith hθ hC1 hle1 (hWa' j hj1 hj2 hna') (hW1 j hj1 hj2 hbirth a)

end BlockBand.SourceProcess.PhysApprox.B3
