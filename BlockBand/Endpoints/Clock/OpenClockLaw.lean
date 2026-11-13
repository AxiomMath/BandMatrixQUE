module

public import BlockBand.Endpoints.Clock.OpenClockProbe
public import BlockBand.Endpoints.Clock.NegativeClock

/-!
# The open-clock law theorem: the Laplace limit of the one-ended clock

We derive the Laplace limit of the one-ended clock from the deterministic-clock lemma and the
entrance bound `E γ_{j₀}^q ≤ C j₀/W = o(1)` of the open-inputs lemma. The normalisation is
`Y_j = q(j/W) C_j + L_j* Y_{j-1} L_j`, `Q_j = W⁻² Y_j`, `d = (1-b)⁻¹ = dStar b`,
`D₀ = 2/(b(4-e²)) = transportD0 b e`, for the one-ended chain started at `X_0 = 0`.

## Fixed energy

* `DetClockEvolution`: the deterministic-clock lemma at fixed `(b, E)`, uniformly for `a` in
  compact subsets of `(0,∞)`, with remainder summable over `j₀ ≤ j ≤ TW`.
* `OpenInputsMoments` (the open-inputs lemma); from it the entrance `E γ_{j₀}^q → 0` follows
  (`openClockEntrance_const_of_openInputsMoments`).
* `tendsto_openClockLaplaceW`: `E F_a(Q_{n_W}^q) → openClockLaplace D₀ d q t a` (the clock
  Laplace transform) for every `a > 0`, `n_W/W → t ∈ (0,T]`, `n_W ≤ TW`.

## Energy-uniform form (moving energies `E_W → E`)

`tendsto_openClockLaplaceW_uniform` is the same conclusion along moving energies with the limit at
the base energy, from `DetClockEvolutionUniform` and `OpenClockEntranceUniform`. Both forms are
proved from the same core `tendsto_openClockLaplaceW_of_seq`. Continuity of the limit in the
energy: `tendsto_openClockLaplace_of_tendsto` (in `D₀`; `E ↦ D₀(b, E)` is continuous on the bulk,
`OpenClockLawProof.tendsto_transportD0`).

## Also

`openClockLaplace_one_eq`: for `q ≡ 1` the limit is the Laplace transform of `openClockLaw b E τ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open OpenClock
open scoped NNReal ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

/-- `f_{W,j}(a) = E F_a(Q_j^q)` for the one-ended chain started at `X_0 = 0`, energy `E`
(so that `f_W(t, a) = E F_a(Q^q_{⌊Wt⌋})`). -/
def openClockLaplaceW (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  ∫ ω, detLaplace (oneEndedQ b E q 0 j ω) a ∂oneEndedLaw W b j

/-- The remainder `r_{W,j}(a)` of the deterministic clock step, with the ordinary
second derivative of the finite expectation `a ↦ E F_a(Q_j^q)`, `D₀ = transportD0 b E`,
`d = dStar b`. -/
def detClockRemainder (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  openClockLaplaceW W b E q (j + 1) a - openClockLaplaceW W b E q j a -
    (W : ℝ)⁻¹ * (transportD0 b E / 2 * a ^ 2 * deriv (deriv (openClockLaplaceW W b E q j)) a -
      dStar b * q (((j + 1 : ℕ) : ℝ) / W) * a * openClockLaplaceW W b E q j a)

/-- **The deterministic-clock lemma at a fixed energy** (derived from its hypotheses in
`detClockEvolution_of`). For `0 < b < 1/2`, `-2 < E < 2`, every horizon `T`, every admissible clock weight `q` and every `K ≥ 1` (every compact subset of
`(0,∞)` lies in some `[K⁻¹, K]`): there are `δ_{W,j}` with `|r_{W,j}(a)| ≤ δ_{W,j}` for
`j₀ ≤ j ≤ TW`, `a ∈ [K⁻¹, K]`, and `Σ_{j=j₀}^{⌊TW⌋} δ_{W,j} → 0`, where
`j₀ = openEntranceTime W = ⌈(log W)²⌉`.
-/
def DetClockEvolution : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ (T : ℝ) (q : ℝ → ℝ),
    IsClockWeight q → ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
      (∀ W j, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
        |detClockRemainder W b E q j a| ≤ δ W j) ∧
      Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0)

/-- **The deterministic-clock lemma along moving bulk energies** `E_W → E ∈ (-2,2)` (coefficient
`D₀(b, E_W)` at width `W`). It is what an energy-uniform open-clock law (used for
`RobinEntranceLimit`, moving energies of `ClockSequence`) needs; a proof needs the one-step bounds
with constants uniform for `E` in compact bulk sets. A hypothesis here; not used by the
fixed-energy theorem `tendsto_openClockLaplaceW`.
-/
def DetClockEvolutionUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ (T : ℝ) (q : ℝ → ℝ), IsClockWeight q →
    ∀ (Es : ℕ → ℝ) (E : ℝ), -2 < E → E < 2 → Tendsto Es atTop (𝓝 E) →
      ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
        (∀ W j, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainder W b (Es W) q j a| ≤ δ W j) ∧
        Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0)

/-- **Entrance bound along moving bulk energies** `E γ_{j₀}^q → 0` (a consequence of the input
moments `E γ_{j₀}^q ≤ C j₀/W = o(1)`), with eventual integrability. A hypothesis here; at a fixed
energy it is proved from `OpenInputsMoments` (`openClockEntrance_const_of_openInputsMoments`). Not
used by the fixed-energy theorem. -/
def OpenClockEntranceUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ q : ℝ → ℝ, IsClockWeight q →
    ∀ (Es : ℕ → ℝ) (E : ℝ), -2 < E → E < 2 → Tendsto Es atTop (𝓝 E) →
      (∀ᶠ W in atTop, Integrable (oneEndedGamma b (Es W) q 0 (openEntranceTime W))
        (oneEndedLaw W b (openEntranceTime W))) ∧
      Tendsto (fun W => ∫ ω, oneEndedGamma b (Es W) q 0 (openEntranceTime W) ω
        ∂oneEndedLaw W b (openEntranceTime W)) atTop (𝓝 0)

namespace OpenClockLawProof

theorem tendsto_openEntranceTime_div :
    Tendsto (fun W : ℕ => (openEntranceTime W : ℝ) / W) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 2 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun W : ℕ => (W : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h4 := h2.add h3
  rw [add_zero] at h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun W => by positivity)
    fun W => ?_
  simp only [Function.comp_apply, one_mul, add_zero]
  rcases Nat.eq_zero_or_pos W with h0 | h0
  · subst h0; simp
  · have hW : (0 : ℝ) < W := by exact_mod_cast h0
    have hc : (openEntranceTime W : ℝ) ≤ Real.log W ^ 2 + 1 := by
      unfold openEntranceTime
      have := Nat.ceil_lt_add_one (sq_nonneg (Real.log W))
      linarith
    calc (openEntranceTime W : ℝ) / W ≤ (Real.log W ^ 2 + 1) / W :=
          div_le_div_of_nonneg_right hc hW.le
      _ = Real.log W ^ 2 / W + (W : ℝ)⁻¹ := by ring

theorem transportD0_pos {b : ℝ} (hb : 0 < b) {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) :
    0 < transportD0 b E := by
  unfold transportD0
  exact div_pos two_pos (mul_pos hb (by nlinarith))

theorem tendsto_transportD0 (b : ℝ) (hb : 0 < b) {Es : ℕ → ℝ} {E : ℝ} (hE0 : -2 < E)
    (hE1 : E < 2) (hEs : Tendsto Es atTop (𝓝 E)) :
    Tendsto (fun W => transportD0 b (Es W)) atTop (𝓝 (transportD0 b E)) := by
  unfold transportD0
  have hden : b * (4 - E ^ 2) ≠ 0 := (mul_pos hb (by nlinarith)).ne'
  exact tendsto_const_nhds.div (tendsto_const_nhds.mul (tendsto_const_nhds.sub (hEs.pow 2))) hden

theorem dStar_nonneg {b : ℝ} (hb : b < 1) : 0 ≤ dStar b := by
  unfold dStar; exact div_nonneg zero_le_one (by linarith)

/-- Second derivatives at `a > 0` only see the function on `(0,∞)`. -/
theorem deriv_deriv_congr_pos {f g : ℝ → ℝ} (h : ∀ x, 0 < x → f x = g x) {a : ℝ} (ha : 0 < a) :
    deriv (deriv f) a = deriv (deriv g) a := by
  have h1 : ∀ x, 0 < x → deriv f x = deriv g x := fun x hx => by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [lt_mem_nhds hx] with y hy using h y hy
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [lt_mem_nhds ha] with y hy using h1 y hy

theorem openClockLaplaceW_eq_lap (W : ℕ) (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (j : ℕ)
    {a : ℝ} (ha : 0 ≤ a) :
    openClockLaplaceW W b E q j a = lap (openProbeLaw W b E q j) a :=
  (lap_openProbeLaw b E hq j ha).symm

end OpenClockLawProof

open OpenClockLawProof

/-- **Core: the Laplace limit along one energy sequence.** For `0 < b < 1/2`, `T > 0`, an
admissible clock weight `q`, energies `E_W → E ∈ (-2, 2)`, if the discrete equation holds along
`E_W` (`heqK`, the conclusion of the deterministic-clock lemma for this sequence) and the entrance
`E γ_{j₀}^q → 0` holds along `E_W` (`hint`, `hlim`), then for `n_W/W → t > 0`, `n_W ≤ TW` and
`a > 0`: `E F_a(Q^q_{n_W}) → openClockLaplace D₀(b,E) d q t a` (the clock Laplace transform). -/
theorem tendsto_openClockLaplaceW_of_seq {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {T : ℝ} (hT : 0 < T) {q : ℝ → ℝ}
    (hq : IsClockWeight q) {Es : ℕ → ℝ} {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2)
    (hEs : Tendsto Es atTop (𝓝 E))
    (heqK : ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
        (∀ W j, openEntranceTime W ≤ j → (j : ℝ) ≤ T * W → ∀ a ∈ Icc K⁻¹ K,
          |detClockRemainder W b (Es W) q j a| ≤ δ W j) ∧
        Tendsto (fun W => ∑ j ∈ Finset.Icc (openEntranceTime W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0))
    (hint : ∀ᶠ W in atTop, Integrable (oneEndedGamma b (Es W) q 0 (openEntranceTime W))
        (oneEndedLaw W b (openEntranceTime W)))
    (hlim : Tendsto (fun W => ∫ ω, oneEndedGamma b (Es W) q 0 (openEntranceTime W) ω
        ∂oneEndedLaw W b (openEntranceTime W)) atTop (𝓝 0))
    {n : ℕ → ℕ} {t : ℝ} (ht : 0 < t)
    (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 t)) (hnT : ∀ W, (n W : ℝ) ≤ T * W)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun W => openClockLaplaceW W b (Es W) q (n W) a) atTop
      (𝓝 (openClockLaplace (transportD0 b E) (dStar b) q t a)) := by
  obtain ⟨hqc, hq0, Qb, hqb⟩ := hq
  set μ : ℕ → ℕ → Measure ℝ := fun W j => openProbeLaw W b (Es W) q j with hμ
  have hμP : ∀ W j, IsProbabilityMeasure (μ W j) := fun W j => by
    simp only [hμ]; infer_instance
  have hμ0 : ∀ W j, ∀ᵐ x ∂μ W j, 0 ≤ x := fun W j => openProbeLaw_nonneg b (Es W) hq0 j
  have hD : 0 ≤ transportD0 b E := (transportD0_pos hb0 hE0 hE1).le
  have hc : 0 ≤ dStar b := dStar_nonneg (by linarith)
  have hDseq := tendsto_transportD0 b hb0 hE0 hE1 hEs
  -- the entrance
  have hentr : ∀ b', 0 < b' → Tendsto (fun W => lap (μ W (openEntranceTime W)) b') atTop
      (𝓝 1) := by
    intro b' hb'
    have hlow : Tendsto (fun W => 1 - b' * ∫ ω, oneEndedGamma b (Es W) q 0 (openEntranceTime W) ω
        ∂oneEndedLaw W b (openEntranceTime W)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hlim.const_mul b')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hint] with W hW
      obtain ⟨hI, heq⟩ := integral_openProbeLaw_id (W := W) b (Es W) hq0 (openEntranceTime W) hW
      have := one_sub_le_lap (μ W (openEntranceTime W)) (hμ0 W _) hI hb'.le
      simp only [hμ] at this ⊢
      rw [heq] at this
      exact this
    · exact Filter.Eventually.of_forall fun W => lap_le_one _ (hμ0 W _) hb'.le
  -- the equation
  have heq : ClockEquation (fun W => transportD0 b (Es W)) (dStar b) q T μ openEntranceTime := by
    intro K hK
    obtain ⟨δ, hδ, hδs⟩ := heqK K hK
    refine ⟨δ, fun W j hj hjT a' ha' => ?_, hδs⟩
    have ha'0 : 0 < a' := lt_of_lt_of_le (inv_pos.mpr (by linarith)) ha'.1
    have h := hδ W j hj hjT a' ha'
    unfold detClockRemainder at h
    unfold clockRemainder
    have e1 := openClockLaplaceW_eq_lap W b (Es W) hq0 (j + 1) ha'0.le
    have e2 := openClockLaplaceW_eq_lap W b (Es W) hq0 j ha'0.le
    have e3 : deriv (deriv (openClockLaplaceW W b (Es W) q j)) a' = lap2 (μ W j) a' := by
      rw [deriv_deriv_congr_pos (g := lap (μ W j)) (fun x hx =>
        openClockLaplaceW_eq_lap W b (Es W) hq0 j hx.le) ha'0]
      exact deriv_deriv_lap (μ W j) (hμ0 W j) ha'0
    rw [e1, e2, e3] at h
    exact h
  have hmain := tendsto_lap_of_clockEquation hD hc hT hqc hq0 hqb hDseq μ hμ0 openEntranceTime
    tendsto_openEntranceTime_div hentr heq ht hn hnT ha
  refine hmain.congr fun W => ?_
  exact (openClockLaplaceW_eq_lap W b (Es W) hq0 (n W) ha.le).symm

/-- **The entrance at a fixed energy from `OpenInputsMoments`** (at `p = 1`, `T = 1`, `X_0 = 0`):
`E γ^q_{j₀} ≤ C (j₀ + 1)/W → 0`, with integrability, for every fixed bulk energy.
This is the
constant-sequence case of `OpenClockEntrance`.
-/
theorem openClockEntrance_const_of_openInputsMoments (h : OpenInputsMoments) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) {q : ℝ → ℝ}
    (hq : IsClockWeight q) :
    (∀ᶠ W in atTop, Integrable (oneEndedGamma b E q 0 (openEntranceTime W))
        (oneEndedLaw W b (openEntranceTime W))) ∧
      Tendsto (fun W => ∫ ω, oneEndedGamma b E q 0 (openEntranceTime W) ω
        ∂oneEndedLaw W b (openEntranceTime W)) atTop (𝓝 0) := by
  obtain ⟨ε, C, W₀, hε, hbound⟩ := h b hb0 hb1 E hE0 hE1 1 q hq 1 le_rfl
  have hj : ∀ᶠ W : ℕ in atTop, (openEntranceTime W : ℝ) ≤ 1 * W := by
    have := tendsto_openEntranceTime_div.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this, eventually_ge_atTop 1] with W hW hW1
    have hWp : (0 : ℝ) < W := by exact_mod_cast hW1
    rw [div_lt_iff₀ hWp] at hW; linarith
  have hnn : ∀ W j ω, 0 ≤ oneEndedGamma b E q 0 j (ω : Fin j → OneEndedLayer W) := by
    intro W j ω
    have := (oneEndedQ_posSemidef b E hq.2.1 0 j ω).trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  have key : ∀ᶠ W : ℕ in atTop, Integrable (oneEndedGamma b E q 0 (openEntranceTime W))
      (oneEndedLaw W b (openEntranceTime W)) ∧
      ∫ ω, oneEndedGamma b E q 0 (openEntranceTime W) ω ∂oneEndedLaw W b (openEntranceTime W)
        ≤ max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W := by
    filter_upwards [hj, eventually_ge_atTop W₀] with W hjW hW
    have hb := (hbound W hW 0 isHermitian_zero (by rw [norm_zero]; exact hε.le)).2 (openEntranceTime W) hjW
    rw [ENNReal.ofReal_one] at hb
    have hm := ClockMixingProb.meas_gamma (W := W) b E q 0 (openEntranceTime W)
    have hfin : eLpNorm (oneEndedGamma b E q 0 (openEntranceTime W)) 1
        (oneEndedLaw W b (openEntranceTime W)) < ⊤ := lt_of_le_of_lt hb ENNReal.ofReal_lt_top
    have hI : Integrable (oneEndedGamma b E q 0 (openEntranceTime W))
        (oneEndedLaw W b (openEntranceTime W)) :=
      memLp_one_iff_integrable.mp hfin
    refine ⟨hI, ?_⟩
    have h1 : ∫ ω, oneEndedGamma b E q 0 (openEntranceTime W) ω ∂oneEndedLaw W b (openEntranceTime W)
        = ∫ ω, ‖oneEndedGamma b E q 0 (openEntranceTime W) ω‖ ∂oneEndedLaw W b (openEntranceTime W) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only; rw [Real.norm_eq_abs, abs_of_nonneg (hnn W _ ω)])
    rw [h1, integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    have hC : 0 ≤ max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W := by positivity
    have hb' : eLpNorm (oneEndedGamma b E q 0 (openEntranceTime W)) 1
        (oneEndedLaw W b (openEntranceTime W)) ≤
        ENNReal.ofReal (max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W) := by
      refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (((openEntranceTime W : ℕ) : ℝ) + 1) / W := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
    · exact (ENNReal.toReal_le_of_le_ofReal hC hb')
    · exact hm.aestronglyMeasurable
  refine ⟨key.mono fun W hW => hW.1, ?_⟩
  have hup : Tendsto (fun W : ℕ => max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun W : ℕ => max C 0 * ((openEntranceTime W : ℝ) / W + (W : ℝ)⁻¹)) atTop
        (𝓝 (max C 0 * (0 + 0))) :=
      (tendsto_openEntranceTime_div.add (tendsto_inv_atTop_zero.comp
        tendsto_natCast_atTop_atTop)).const_mul (max C 0)
    rw [add_zero, mul_zero] at h1
    exact h1.congr fun W => by ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun W => integral_nonneg fun ω => hnn W _ ω)
    (key.mono fun W hW => hW.2)

/-- **The open-clock law theorem, Laplace form, fixed energy**: under `DetClockEvolution` and
`OpenInputsMoments`, for `0 < b < 1/2`, `-2 < E < 2`, `T > 0`, an admissible clock weight `q`,
`n_W/W → t > 0` with `n_W ≤ TW`, and every `a > 0`:
`E F_a(Q^q_{n_W}) → E exp{-a d ∫₀^t q(t-s) e^{√D₀ B_s - D₀ s/2} ds}`, `D₀ = transportD0 b E`,
`d = dStar b`.
-/
theorem tendsto_openClockLaplaceW (hDet : DetClockEvolution) (hOI : OpenInputsMoments)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) {T : ℝ}
    (hT : 0 < T) {q : ℝ → ℝ} (hq : IsClockWeight q) {n : ℕ → ℕ} {t : ℝ} (ht : 0 < t)
    (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 t)) (hnT : ∀ W, (n W : ℝ) ≤ T * W)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun W => openClockLaplaceW W b E q (n W) a) atTop
      (𝓝 (openClockLaplace (transportD0 b E) (dStar b) q t a)) := by
  obtain ⟨hint, hlim⟩ := openClockEntrance_const_of_openInputsMoments hOI hb0 hb1 hE0 hE1 hq
  exact tendsto_openClockLaplaceW_of_seq hb0 hb1 hT hq (Es := fun _ => E) hE0 hE1
    tendsto_const_nhds (fun K hK => hDet b hb0 hb1 E hE0 hE1 T q hq K hK) hint hlim ht hn hnT ha

/-- **Energy-uniform form** (moving energies `E_W → E`, limit at the base energy), under the
hypotheses `DetClockEvolutionUniform` and `OpenClockEntranceUniform`. -/
theorem tendsto_openClockLaplaceW_uniform (hDet : DetClockEvolutionUniform)
    (hEnt : OpenClockEntranceUniform) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {T : ℝ}
    (hT : 0 < T) {q : ℝ → ℝ} (hq : IsClockWeight q) {Es : ℕ → ℝ} {E : ℝ} (hE0 : -2 < E)
    (hE1 : E < 2) (hEs : Tendsto Es atTop (𝓝 E)) {n : ℕ → ℕ} {t : ℝ} (ht : 0 < t)
    (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 t)) (hnT : ∀ W, (n W : ℝ) ≤ T * W)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun W => openClockLaplaceW W b (Es W) q (n W) a) atTop
      (𝓝 (openClockLaplace (transportD0 b E) (dStar b) q t a)) := by
  obtain ⟨hint, hlim⟩ := hEnt b hb0 hb1 q hq Es E hE0 hE1 hEs
  exact tendsto_openClockLaplaceW_of_seq hb0 hb1 hT hq hE0 hE1 hEs
    (fun K hK => hDet b hb0 hb1 T q hq Es E hE0 hE1 hEs K hK) hint hlim ht hn hnT ha

/-- **Continuity of the limit in the diffusion coefficient** (hence in the energy through
`D₀(b, E)`): `D_k → D ≥ 0` implies `openClockLaplace D_k c q t a → openClockLaplace D c q t a`
(dominated convergence; `c, a ≥ 0`, `t ≥ 0`). -/
theorem tendsto_openClockLaplace_of_tendsto {Ds : ℕ → ℝ} {D : ℝ} (hDs : Tendsto Ds atTop (𝓝 D))
    {c : ℝ} (hc : 0 ≤ c) {q : ℝ → ℝ} (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x) {t a : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) :
    Tendsto (fun k => openClockLaplace (Ds k) c q t a) atTop
      (𝓝 (openClockLaplace D c q t a)) := by
  simp only [openClockLaplace_eq]
  have hjoint : ∀ ω : BlockBand.SourceProcess.CanonicalWienerPath,
      Continuous (fun D' : ℝ => openClockIntegral D' q t ω) := by
    intro ω
    unfold openClockIntegral
    have hev : Continuous (fun s : ℝ => ω s.toNNReal) :=
      ω.continuous.comp continuous_real_toNNReal
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (D' : ℝ) (s : ℝ) => q (t - s) * exp (Real.sqrt D' * ω s.toNNReal - D' * s / 2))
      ((hq.comp (continuous_const.sub continuous_snd)).mul (continuous_exp.comp
        (((Real.continuous_sqrt.comp continuous_fst).mul (hev.comp continuous_snd)).sub
          ((continuous_fst.mul continuous_snd).div_const _)))) 0 t
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_)
    (integrable_const 1) (fun k => Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · exact (continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (continuous_openClockIntegral _ hq t))).neg).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
    exact mul_nonneg ha (mul_nonneg hc (openClockIntegral_nonneg _ hq0 ht ω))
  · exact ((continuous_exp.comp (continuous_const.mul (continuous_const.mul
      (hjoint ω))).neg).tendsto D).comp hDs

/-- For the constant weight `q ≡ 1` the limit is the Laplace transform of the open-clock law
`openClockLaw b E τ` (law of `X_τ`), i.e. of the total mass
`Σ_τ([0, τ])` of the open Brownian measure. -/
theorem openClockLaplace_one_eq (b E τ a : ℝ) :
    openClockLaplace (transportD0 b E) (dStar b) (fun _ => 1) τ a =
      ∫ x, exp (-(a * x)) ∂openClockLaw b E τ := by
  rw [openClockLaw, integral_map (measurable_openClockFunctional b E τ).aemeasurable
    (show Continuous (fun x : ℝ => exp (-(a * x))) by fun_prop).aestronglyMeasurable,
    openClockLaplace_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [openClockIntegral, openClockFunctional, one_mul]

end BlockBand.Endpoints.Clock
