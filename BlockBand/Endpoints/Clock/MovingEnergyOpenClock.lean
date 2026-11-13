module

public import BlockBand.Endpoints.Clock.MovingEnergyLabels
public import BlockBand.Endpoints.Clock.OpenClockProfile
public import BlockBand.Endpoints.Clock.RobinEntrance

/-!
# The open-clock law theorem from `X₀ = D`, along moving energies, uniformly in `‖D‖ ≤ ε`

## Main result

`openClockLawUniformInitial_of (hDet : DetClockEvolutionDBulk) (hOI : OpenInputsMomentsBulk) :
RobinEntrance.OpenClockLawUniformInitial` proves the hypothesis `h1` of the Robin entrance lemma
from the two compact-set statements `DetClockEvolutionDBulk` and `OpenInputsMomentsBulk`.

## Proof (along a sequence of energies `E_W` and of initial matrices `D_W`)

* `D`-versions of the probe identities: the probe is nonnegative,
  `lap (openProbeLawFrom W b E D j) a = openClockLaplaceWD W b E 1 D j a` for `a ≥ 0`, and the
  first moment of the probe is `E γ_j^D`.
* `entrance_seq`: the entrance `E γ_{j₀}^{D_W} → 0` along `(E_W, D_W)`. It comes from the
  clock clause of `OpenInputsMomentsBulk` at `p = 1`.
* `tendsto_lap_seq`: the Laplace limit along `(E_W, D_W)`, from
  `OpenClock.tendsto_lap_of_clockEquation`, which accepts arbitrary sequences of laws, with
  coefficient `D₀(b, E_W)`; the discrete equation comes from `DetClockEvolutionDBulk`. This is
  the argument of `tendsto_openClockLaplaceW_of_seq` with `X₀ = D_W`.
* `tendsto_law_of_lap`: from the Laplace limit to weak convergence, by
  `OpenClock.tendsto_integral_of_tendsto_laplace` with `m = 1`; the limit `X_τ` has first moment
  `≤ dτ`.
* `openClockLawUniformInitial_of`: uniformity in `D` by choice. If the conclusion failed
  frequently, choose a bad `D_W` at each bad width (and `0` elsewhere); the sequence result then
  gives a contradiction.

Norms are `ℓ²` operator norms on matrices. The result is used in `negativeClock_of_bulk` and
`clockSmallBall_of_bulk`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess OpenClock OpenClockLawProof OpenClockProfile RobinEntrance
open scoped NNReal ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator BoundedContinuousFunction

namespace MovingEnergy

variable {W : ℕ}

/-!
## 1. The probe started at `X₀ = D`
-/

theorem measurable_probeFrom (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    Measurable (fun p : (Fin j → OneEndedLayer W) × (Fin W → ℂ) =>
      quadForm (oneEndedQ b E (fun _ => 1) D j p.1) p.2) :=
  measurable_quadForm_comp ((ClockMixingProb.meas_Q b E _ D j).comp measurable_fst)
    measurable_snd

theorem quadForm_probeFrom_nonneg (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (p : (Fin j → OneEndedLayer W) × (Fin W → ℂ)) :
    0 ≤ quadForm (oneEndedQ b E (fun _ => 1) D j p.1) p.2 :=
  CommonPortRatios.quadForm_nonneg_of_posSemidef
    (oneEndedQ_posSemidef b E (fun _ => zero_le_one) D j p.1) p.2

theorem openProbeLawFrom_nonneg (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) :
    ∀ᵐ x ∂openProbeLawFrom W b E D j, 0 ≤ x := by
  unfold openProbeLawFrom
  rw [ae_map_iff (measurable_probeFrom b E D j).aemeasurable measurableSet_Ici]
  exact Filter.Eventually.of_forall fun p => quadForm_probeFrom_nonneg b E D j p

/-- `lap (openProbeLawFrom) a = E F_a(Q_j^1)` for the chain started at `X₀ = D`, `a ≥ 0`. -/
theorem lap_openProbeLawFrom (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) {a : ℝ}
    (ha : 0 ≤ a) :
    lap (openProbeLawFrom W b E D j) a = openClockLaplaceWD W b E (fun _ => 1) D j a := by
  unfold lap openProbeLawFrom openClockLaplaceWD
  have hm := measurable_probeFrom (W := W) b E D j
  rw [integral_map hm.aemeasurable
    (show Continuous (fun x : ℝ => exp (-(a * x))) by fun_prop).aestronglyMeasurable]
  have hI : Integrable (fun p : (Fin j → OneEndedLayer W) × (Fin W → ℂ) =>
      exp (-(a * quadForm (oneEndedQ b E (fun _ => 1) D j p.1) p.2)))
      ((oneEndedLaw W b j).prod (circularVectorLaw (Fin W))) := by
    refine Integrable.of_bound
      ((measurable_exp.comp ((measurable_const.mul hm).neg)).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
    exact mul_nonneg ha (quadForm_probeFrom_nonneg b E D j p)
  rw [integral_prod _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact (detLaplace_eq_integral (oneEndedQ_posSemidef b E (fun _ => zero_le_one) D j ω) ha).symm

/-- The probe started at `X₀ = D` is integrable as soon as `γ_j^D` is, with mean `E γ_j^D`. -/
theorem integral_openProbeLawFrom_id (b E : ℝ) (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ)
    (hint : Integrable (oneEndedGamma b E (fun _ => 1) D j) (oneEndedLaw W b j)) :
    Integrable id (openProbeLawFrom W b E D j) ∧
      ∫ x, x ∂openProbeLawFrom W b E D j =
        ∫ ω, oneEndedGamma b E (fun _ => 1) D j ω ∂oneEndedLaw W b j := by
  have hm := measurable_probeFrom (W := W) b E D j
  have hlin : ∀ ω, ∫ h, quadForm (oneEndedQ b E (fun _ => 1) D j ω) h ∂circularVectorLaw (Fin W) =
      oneEndedGamma b E (fun _ => 1) D j ω := fun ω => integral_quadForm_circular _
  have hI : Integrable (fun p : (Fin j → OneEndedLayer W) × (Fin W → ℂ) =>
      quadForm (oneEndedQ b E (fun _ => 1) D j p.1) p.2)
      ((oneEndedLaw W b j).prod (circularVectorLaw (Fin W))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · dsimp only
      exact integrable_quadForm_circular (oneEndedQ b E (fun _ => 1) D j ω)
    dsimp only
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    show oneEndedGamma b E (fun _ => 1) D j ω =
      ∫ h, ‖quadForm (oneEndedQ b E (fun _ => 1) D j ω) h‖ ∂circularVectorLaw (Fin W)
    rw [← hlin ω]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show quadForm (oneEndedQ b E (fun _ => 1) D j ω) h =
      ‖quadForm (oneEndedQ b E (fun _ => 1) D j ω) h‖
    rw [Real.norm_eq_abs, abs_of_nonneg (quadForm_probeFrom_nonneg b E D j (ω, h))]
  unfold openProbeLawFrom
  refine ⟨(integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).mpr hI, ?_⟩
  rw [integral_map hm.aemeasurable
    (show Continuous (fun x : ℝ => x) from continuous_id).aestronglyMeasurable,
    integral_prod _ hI]
  exact integral_congr_ae (Filter.Eventually.of_forall hlin)

theorem isClockWeight_one : IsClockWeight (fun _ : ℝ => (1 : ℝ)) :=
  ⟨continuous_const, fun _ => zero_le_one, 1, fun _ => le_rfl⟩

theorem mem_bulk_facts {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : -2 < E ∧ E < 2 := by
  have h : -2 + κ ≤ E ∧ E ≤ 2 - κ := hE
  constructor <;> linarith

theorem mem_Icc_facts {β b : ℝ} (hβ : 0 < β) (hb : b ∈ Set.Icc β (1 / 2 - β)) :
    0 < b ∧ b < 1 / 2 := by
  have h : β ≤ b ∧ b ≤ 1 / 2 - β := hb
  constructor <;> linarith

/-!
## 2. The entrance along `(E_W, D_W)`
-/

/-- **The entrance along moving energies and initial matrices**: from the clock clause of `OpenInputsMomentsBulk` at `p = 1`, `T = 1`,
`E γ_{j₀}^{D_W} ≤ C (j₀ + 1)/W → 0`, with integrability, for `E_W ∈ bulkInterval κ` and
Hermitian `‖D_W‖ ≤ ε`. -/
theorem entrance_seq (hOI : OpenInputsMomentsBulk) {β κ : ℝ} (hβ : 0 < β) (hβ4 : β < 1 / 4)
    (hκ : 0 < κ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ Es : ℕ → ℝ, (∀ W, Es W ∈ bulkInterval κ) →
      ∀ Ds : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ, (∀ W, (Ds W).IsHermitian ∧ ‖Ds W‖ ≤ ε) →
        (∀ᶠ W in atTop, Integrable (oneEndedGamma b (Es W) (fun _ => 1) (Ds W)
            (openEntranceTime W)) (oneEndedLaw W b (openEntranceTime W))) ∧
          Tendsto (fun W => ∫ ω, oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W) ω
            ∂oneEndedLaw W b (openEntranceTime W)) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hbε⟩ := hOI β κ hβ hβ4 hκ 1 (fun _ => 1) isClockWeight_one 1 le_rfl
  refine ⟨ε, hε, fun b hb Es hEs Ds hDs => ?_⟩
  obtain ⟨C, W₀, hbound⟩ := hbε b hb
  have hj : ∀ᶠ W : ℕ in atTop, (openEntranceTime W : ℝ) ≤ 1 * W := by
    have := tendsto_openEntranceTime_div.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [this, eventually_ge_atTop 1] with W hW hW1
    have hWp : (0 : ℝ) < W := by exact_mod_cast hW1
    rw [div_lt_iff₀ hWp] at hW; linarith
  have hnn : ∀ W j ω, 0 ≤ oneEndedGamma b (Es W) (fun _ => 1) (Ds W) j
      (ω : Fin j → OneEndedLayer W) := by
    intro W j ω
    have := (oneEndedQ_posSemidef b (Es W) (fun _ => zero_le_one) (Ds W) j ω).trace_nonneg
    exact (Complex.nonneg_iff.mp this).1
  have key : ∀ᶠ W : ℕ in atTop, Integrable (oneEndedGamma b (Es W) (fun _ => 1) (Ds W)
      (openEntranceTime W)) (oneEndedLaw W b (openEntranceTime W)) ∧
      ∫ ω, oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W) ω
          ∂oneEndedLaw W b (openEntranceTime W)
        ≤ max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W := by
    filter_upwards [hj, eventually_ge_atTop W₀] with W hjW hW
    have hb' := (hbound W hW (Es W) (hEs W) (Ds W) (hDs W).1 (hDs W).2).2
      (openEntranceTime W) hjW
    rw [ENNReal.ofReal_one] at hb'
    have hm := ClockMixingProb.meas_gamma (W := W) b (Es W) (fun _ => 1) (Ds W)
      (openEntranceTime W)
    have hfin : eLpNorm (oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W)) 1
        (oneEndedLaw W b (openEntranceTime W)) < ⊤ := lt_of_le_of_lt hb' ENNReal.ofReal_lt_top
    have hI : Integrable (oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W))
        (oneEndedLaw W b (openEntranceTime W)) :=
      memLp_one_iff_integrable.mp hfin
    refine ⟨hI, ?_⟩
    have h1 : ∫ ω, oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W) ω
          ∂oneEndedLaw W b (openEntranceTime W)
        = ∫ ω, ‖oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W) ω‖
          ∂oneEndedLaw W b (openEntranceTime W) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        dsimp only; rw [Real.norm_eq_abs, abs_of_nonneg (hnn W _ ω)])
    rw [h1, integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    have hC : 0 ≤ max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W := by positivity
    have hb'' : eLpNorm (oneEndedGamma b (Es W) (fun _ => 1) (Ds W) (openEntranceTime W)) 1
        (oneEndedLaw W b (openEntranceTime W)) ≤
        ENNReal.ofReal (max C 0 * (((openEntranceTime W : ℕ) : ℝ) + 1) / W) := by
      refine hb'.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ (((openEntranceTime W : ℕ) : ℝ) + 1) / W := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
    · exact ENNReal.toReal_le_of_le_ofReal hC hb''
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

/-!
## 3. The Laplace limit along `(E_W, D_W)`
-/

/-- **Laplace limit along moving energies and initial matrices** (the clock Laplace transform with
`q ≡ 1`). `β, κ, T` first; then `ε > 0`; for `b ∈ [β, 1/2-β]`, energies
`E_W → E` in `bulkInterval κ`, Hermitian `‖D_W‖ ≤ ε`, `n_W/W → τ > 0`, `n_W ≤ TW` and `a > 0`:
`E F_a(Q^1_{n_W}) → E exp{-a d ∫₀^τ e^{√D₀ B_s - D₀ s/2} ds}` with `D₀ = D₀(b, E)` at the base
energy. -/
theorem tendsto_lap_seq (hDet : DetClockEvolutionDBulk) (hOI : OpenInputsMomentsBulk)
    {β κ T : ℝ} (hβ : 0 < β) (hβ4 : β < 1 / 4) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ, ∀ Es : ℕ → ℝ,
      Tendsto Es atTop (𝓝 E) → (∀ W, Es W ∈ bulkInterval κ) →
      ∀ Ds : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ, (∀ W, (Ds W).IsHermitian ∧ ‖Ds W‖ ≤ ε) →
      ∀ (n : ℕ → ℕ) (τ : ℝ), 0 < τ → Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 τ) →
        (∀ W, (n W : ℝ) ≤ T * W) → ∀ a : ℝ, 0 < a →
          Tendsto (fun W => lap (openProbeLawFrom W b (Es W) (Ds W) (n W)) a) atTop
            (𝓝 (openClockLaplace (transportD0 b E) (dStar b) (fun _ => 1) τ a)) := by
  obtain ⟨ε₁, hε₁, hdet⟩ := hDet β κ hβ hβ4 hκ T (fun _ => 1) isClockWeight_one
  obtain ⟨ε₂, hε₂, hent⟩ := entrance_seq hOI hβ hβ4 hκ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂,
    fun b hb E hE Es hEs hEsb Ds hDs n τ hτ hn hnT a ha => ?_⟩
  obtain ⟨hb0, hb1⟩ := mem_Icc_facts hβ hb
  obtain ⟨hE0, hE1⟩ := mem_bulk_facts hκ hE
  set μ : ℕ → ℕ → Measure ℝ := fun W j => openProbeLawFrom W b (Es W) (Ds W) j with hμ
  have hμP : ∀ W j, IsProbabilityMeasure (μ W j) := fun W j => by
    simp only [hμ]; infer_instance
  have hμ0 : ∀ W j, ∀ᵐ x ∂μ W j, 0 ≤ x := fun W j => openProbeLawFrom_nonneg _ _ _ _
  have hD : 0 ≤ transportD0 b E := (transportD0_pos hb0 hE0 hE1).le
  have hc : 0 ≤ dStar b := dStar_nonneg (by linarith)
  have hDseq := tendsto_transportD0 b hb0 hE0 hE1 hEs
  obtain ⟨hint, hlim⟩ := hent b hb Es hEsb Ds
    (fun W => ⟨(hDs W).1, (hDs W).2.trans (min_le_right _ _)⟩)
  -- the entrance
  have hentr : ∀ b', 0 < b' → Tendsto (fun W => lap (μ W (openEntranceTime W)) b') atTop
      (𝓝 1) := by
    intro b' hb'
    have hlow : Tendsto (fun W => 1 - b' * ∫ ω, oneEndedGamma b (Es W) (fun _ => 1) (Ds W)
        (openEntranceTime W) ω ∂oneEndedLaw W b (openEntranceTime W)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hlim.const_mul b')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hint] with W hW
      obtain ⟨hI, heq⟩ := integral_openProbeLawFrom_id (W := W) b (Es W) (Ds W)
        (openEntranceTime W) hW
      have := one_sub_le_lap (μ W (openEntranceTime W)) (hμ0 W _) hI hb'.le
      simp only [hμ] at this ⊢
      rw [heq] at this
      exact this
    · exact Filter.Eventually.of_forall fun W => lap_le_one _ (hμ0 W _) hb'.le
  -- the equation
  have heq : ClockEquation (fun W => transportD0 b (Es W)) (dStar b) (fun _ => 1) T μ
      openEntranceTime := by
    intro K hK
    obtain ⟨δ, hδ, hδs⟩ := hdet b hb K hK
    refine ⟨δ, fun W j hj hjT a' ha' => ?_, hδs⟩
    have ha'0 : 0 < a' := lt_of_lt_of_le (inv_pos.mpr (by linarith)) ha'.1
    have h := hδ W j (Es W) (hEsb W) (Ds W) (hDs W).1 ((hDs W).2.trans (min_le_left _ _)) hj
      hjT a' ha'
    unfold detClockRemainderD at h
    unfold clockRemainder
    have e1 := (lap_openProbeLawFrom (W := W) b (Es W) (Ds W) (j + 1) ha'0.le).symm
    have e2 := (lap_openProbeLawFrom (W := W) b (Es W) (Ds W) j ha'0.le).symm
    have e3 : deriv (deriv (openClockLaplaceWD W b (Es W) (fun _ => 1) (Ds W) j)) a' =
        lap2 (μ W j) a' := by
      rw [deriv_deriv_congr_pos (g := lap (μ W j)) (fun x hx =>
        (lap_openProbeLawFrom (W := W) b (Es W) (Ds W) j hx.le).symm) ha'0]
      exact deriv_deriv_lap (μ W j) (hμ0 W j) ha'0
    rw [e1, e2, e3] at h
    exact h
  exact tendsto_lap_of_clockEquation hD hc hT continuous_const (fun _ => zero_le_one)
    (fun _ => le_rfl) hDseq μ hμ0 openEntranceTime tendsto_openEntranceTime_div hentr heq hτ hn
    hnT ha

/-!
## 4. From the Laplace limit to the weak limit
-/

/-- **Weak convergence from the Laplace limit** (test `1`): if the Laplace
transforms of `openProbeLawFrom W b (E_W) (D_W) (n_W)` converge to that of `X_τ` at every
`a > 0`, then `E f(g*Q^1_{n_W}g) → E f(X_τ)` for every bounded continuous `f`. -/
theorem tendsto_law_of_lap {b E τ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E)
    (hE1 : E < 2) (hτ : 0 < τ) (Es : ℕ → ℝ) (Ds : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ)
    (n : ℕ → ℕ)
    (hlap : ∀ a : ℝ, 0 < a →
      Tendsto (fun W => lap (openProbeLawFrom W b (Es W) (Ds W) (n W)) a) atTop
        (𝓝 (openClockLaplace (transportD0 b E) (dStar b) (fun _ => 1) τ a)))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun W => ∫ x, f x ∂openProbeLawFrom W b (Es W) (Ds W) (n W)) atTop
      (𝓝 (∫ x, f x ∂openClockLaw b E τ)) := by
  have hD : 0 ≤ transportD0 b E := (transportD0_pos hb0 hE0 hE1).le
  have hd : 0 ≤ dStar b := dStar_nonneg (by linarith)
  have hmom := integral_openClockIntegral_le hD (φ := fun _ => (1 : ℝ)) continuous_const
    (fun _ => zero_le_one) (fun _ => le_rfl) hτ.le
  set Y : CanonicalWienerPath → Fin 1 → ℝ :=
    fun ω _ => dStar b * openClockIntegral (transportD0 b E) (fun _ => 1) τ ω with hY
  have hYm : Measurable Y := Measurable.of_eval fun _ =>
    (continuous_const.mul (continuous_openClockIntegral _ continuous_const τ)).measurable
  have key := tendsto_integral_of_tendsto_laplace (m := 1)
    (fun W => (Fin (n W) → OneEndedLayer W) × (Fin W → ℂ))
    (fun W => (oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W)))
    (fun W p _ => quadForm (oneEndedQ b (Es W) (fun _ => 1) (Ds W) (n W) p.1) p.2)
    (fun W => Measurable.of_eval fun _ => measurable_probeFrom _ _ _ _)
    (fun W p _ => quadForm_probeFrom_nonneg _ _ _ _ p)
    canonicalWienerLaw Y hYm
    (fun ω _ => mul_nonneg hd (openClockIntegral_nonneg _ (fun _ => zero_le_one) hτ.le ω))
    (fun _ => hmom.1.const_mul _) (K := dStar b * (1 * τ))
    (fun _ => by
      simp only [hY]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hmom.2 hd)
    (fun l hl => ?_) (fun x => f (x 0)) (f.continuous.comp (continuous_apply 0)) (M := ‖f‖)
    (fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
  · have hl : ∀ W, ∫ x, f x ∂openProbeLawFrom W b (Es W) (Ds W) (n W) =
        ∫ p, f (quadForm (oneEndedQ b (Es W) (fun _ => 1) (Ds W) (n W) p.1) p.2)
          ∂(oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W)) := by
      intro W
      unfold openProbeLawFrom
      rw [integral_map (measurable_probeFrom (W := W) b (Es W) (Ds W) (n W)).aemeasurable
        f.continuous.aestronglyMeasurable]
    have hr : ∫ x, f x ∂openClockLaw b E τ = ∫ ω, f (Y ω 0) ∂canonicalWienerLaw := by
      rw [openClockLaw, integral_map (measurable_openClockFunctional b E τ).aemeasurable
        f.continuous.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hY, openClockIntegral, openClockFunctional, one_mul]
    simp_rw [hl, hr]
    exact key
  · simp only [Fin.sum_univ_one]
    rcases (hl 0).eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [zero_mul, neg_zero, Real.exp_zero, integral_const, smul_eq_mul, mul_one,
        probReal_univ]
      exact tendsto_const_nhds
    · have hlhs : ∀ W, ∫ p, exp (-(l 0 * quadForm (oneEndedQ b (Es W) (fun _ => 1) (Ds W) (n W)
            p.1) p.2)) ∂(oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W)) =
          lap (openProbeLawFrom W b (Es W) (Ds W) (n W)) (l 0) := by
        intro W
        unfold lap openProbeLawFrom
        rw [integral_map (measurable_probeFrom (W := W) b (Es W) (Ds W) (n W)).aemeasurable
          (show Continuous (fun x : ℝ => exp (-(l 0 * x))) by fun_prop).aestronglyMeasurable]
      have hrhs : ∫ ω, exp (-(l 0 * Y ω 0)) ∂canonicalWienerLaw =
          openClockLaplace (transportD0 b E) (dStar b) (fun _ => 1) τ (l 0) := by
        rw [openClockLaplace_eq]
      simp_rw [hlhs, hrhs]
      exact hlap (l 0) hpos

/-!
## 5. Uniformity in `D` and the label `h1`
-/

/-- **The open-clock law along `(E_W, D_W)`**: `β, κ, T` first; then `ε > 0`; for
`b ∈ [β, 1/2-β]`, along every sequence of Hermitian `‖D_W‖ ≤ ε`, energies `E_W → E` in
`bulkInterval κ` and lengths `n_W/W → τ > 0` with `n_W ≤ TW`, the probe law converges weakly to
the law of `X_τ` at the base energy. -/
theorem exists_eps_tendsto_law (hDet : DetClockEvolutionDBulk) (hOI : OpenInputsMomentsBulk)
    {β κ T : ℝ} (hβ : 0 < β) (hβ4 : β < 1 / 4) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ E ∈ bulkInterval κ, ∀ Es : ℕ → ℝ,
      Tendsto Es atTop (𝓝 E) → (∀ W, Es W ∈ bulkInterval κ) →
      ∀ Ds : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ, (∀ W, (Ds W).IsHermitian ∧ ‖Ds W‖ ≤ ε) →
      ∀ (n : ℕ → ℕ) (τ : ℝ), 0 < τ → Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 τ) →
        (∀ W, (n W : ℝ) ≤ T * W) → ∀ f : ℝ →ᵇ ℝ,
          Tendsto (fun W => ∫ x, f x ∂openProbeLawFrom W b (Es W) (Ds W) (n W)) atTop
            (𝓝 (∫ x, f x ∂openClockLaw b E τ)) := by
  obtain ⟨ε, hε, h⟩ := tendsto_lap_seq hDet hOI hβ hβ4 hκ hT
  refine ⟨ε, hε, fun b hb E hE Es hEs hEsb Ds hDs n τ hτ hn hnT f => ?_⟩
  obtain ⟨hb0, hb1⟩ := mem_Icc_facts hβ hb
  obtain ⟨hE0, hE1⟩ := mem_bulk_facts hκ hE
  exact tendsto_law_of_lap hb0 hb1 hE0 hE1 hτ Es Ds n
    (h b hb E hE Es hEs hEsb Ds hDs n τ hτ hn hnT) f

/-- **Hypothesis `h1` of the Robin entrance lemma** (`RobinEntrance.OpenClockLawUniformInitial`)
from the two compact-set statements `DetClockEvolutionDBulk` and `OpenInputsMomentsBulk`. The
uniformity in `‖D‖ ≤ ε` comes from the sequence form `exists_eps_tendsto_law` by choosing a bad
`D_W` at each bad width.
-/
theorem openClockLawUniformInitial_of (hDet : DetClockEvolutionDBulk)
    (hOI : OpenInputsMomentsBulk) : OpenClockLawUniformInitial := by
  classical
  intro β κ T hβ hβ4 hκ hT
  obtain ⟨ε, hε, hseq⟩ := exists_eps_tendsto_law hDet hOI hβ hβ4 hκ hT
  refine ⟨ε, hε, fun b hb E hE τ hτ _ n Es hn hnT hEs hEsb f δ hδ => ?_⟩
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  let P : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ → Prop := fun W D =>
    D.IsHermitian ∧ ‖D‖ ≤ ε ∧
      δ < |∫ x, f x ∂openProbeLawFrom W b (Es W) D (n W) - ∫ x, f x ∂openClockLaw b E τ|
  let Ds : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ := fun W =>
    if h : ∃ D, P W D then h.choose else 0
  have hDs : ∀ W, (Ds W).IsHermitian ∧ ‖Ds W‖ ≤ ε := by
    intro W
    by_cases h : ∃ D, P W D
    · rw [show Ds W = h.choose from dite_eq_left h]
      exact ⟨h.choose_spec.1, h.choose_spec.2.1⟩
    · rw [show Ds W = 0 from dite_eq_right h]
      exact ⟨isHermitian_zero, by rw [norm_zero]; exact hε.le⟩
  have hconv := hseq b hb E hE Es hEs hEsb Ds hDs n τ hτ hn hnT f
  have hev := Metric.tendsto_nhds.mp hconv δ hδ
  obtain ⟨W, hW1, hW2⟩ := (hcon.and_eventually hev).exists
  have h : ∃ D, P W D := by
    push Not at hW1
    obtain ⟨D, hD, hDε, hbad⟩ := hW1
    exact ⟨D, hD, hDε, hbad⟩
  have hbad := h.choose_spec.2.2
  have hDW : Ds W = h.choose := dite_eq_left h
  rw [Real.dist_eq, hDW] at hW2
  linarith

end MovingEnergy

end BlockBand.Endpoints.Clock
