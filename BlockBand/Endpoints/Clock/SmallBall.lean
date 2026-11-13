module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Coarea.GUELaw
public import BlockBand.Counting.ComplexGaussianWick
public import BlockBand.Layers.LayerMeasurability
public import BlockBand.Layers.GinibreTails

/-!
# The clock small-ball lemma from the negative-clock theorem

We prove `clockSmallBall_of_negativeClock : NegativeClockContract → ClockSmallBallContract`.

*Measure.* The joint law `probedClockLaw W b` of the near-end-grown Gaussian path
(`growthPathLaw`) and an independent `h ~ CN(0, I_{2W})` (`circularVectorLaw`); laws on `ℝ` of the
clocks `T_W = W⁻²h*Yh` (`scaledClock`), `M_W = h*Yh/(nW)` (`rescaledClock`) and the path functional
`A_W = Tr Y/(nW)` (`traceClock`), `Y = fullClock`. *Uniformity.* `C = max C₀ 0`, `C₀` the constant
of `NegativeClockContract.negative` for the same `β, κ, T₀, p`.

Proof, by section:
* §1: measurability of `fullInverse`, `fullClock`, `scaledClock`, `rescaledClock`, `traceClock`.
* §3: `E_h[Re h*Yh] = Re Tr Y` for every deterministic `Y` (`integral_quadForm_circular`, from
  the Counting Wick identity via `circularVectorLaw_eq_map_counting`); `h*(U*U)h ≥ 0`.
* §4: finite width, every `n, W` and `ε > 0`:
  `(1 - √ε) P(A_W ≤ ε) ≤ P(M_W ≤ √ε)` (`ofReal_mul_growthPathLaw_traceClock_le`, conditional
  Markov in `h` and Tonelli on the product law).
* §5: general weak-limit tools on `ℝ`: Prokhorov extraction for `IsTightSeq`
  (`exists_tendsto_subseq_of_isTightSeq`), deterministic Slutsky scaling
  (`tendsto_integral_comp_mul`), Markov for a positive limit (`measure_Iic_sqrt_le`).
* §6: `T_W = τ_W M_W` (`n > 0`), tightness of `M_W` on `{τ_W ≥ τ/2}` from `h.tight`, and the
  Slutsky identification `T = τM` along every subsequence (`isSubsequentialLimit_scaledClock`).
* §7: the limit clause (`rescaled_limit_of_scaled_limit`), the Portmanteau step
  (`eventually_clockLaw_Iic_sqrt_le`, closed set `(-∞, √ε]`), and the assembly.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix BoundedContinuousFunction

/-!
## 1. Measurability of the clocks
-/

/-- The path read-out `pathAt` is continuous in the growth coordinates. -/
theorem continuous_pathAt (W r : ℕ) : Continuous (fun ω : GrowthPath W => pathAt W r ω) := by
  unfold pathAt
  refine Continuous.prodMk (continuous_pi fun i => ?_) (Continuous.prodMk (continuous_pi fun i => ?_)
    (continuous_pi fun i => ?_))
  · exact (continuous_apply _).comp continuous_fst
  · exact ((continuous_apply _).comp continuous_snd).matrix_conjTranspose
  · fin_cases i <;> simp <;> fun_prop

/-- The path matrix is continuous in the path sample. -/
theorem continuous_pathMatrix (W r : ℕ) :
    Continuous (fun ω : PathSample W r => pathMatrix ω) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold pathMatrix
  split_ifs
  · fun_prop
  · fun_prop
  · exact continuous_star.comp (by fun_prop)
  · fun_prop

/-- The port coupling is continuous in the path sample. -/
theorem continuous_pathPortCoupling (W r : ℕ) :
    Continuous (fun ω : PathSample W r => pathPortCoupling ω) := by
  refine continuous_pi fun x => continuous_pi fun y => ?_
  unfold pathPortCoupling
  split_ifs
  · fun_prop
  · fun_prop

/-- `𝓜(ω)` is continuous in the growth coordinates. -/
theorem continuous_fullPathMatrix (b E : ℝ) (W n : ℕ) :
    Continuous (fun ω : GrowthPath W => fullPathMatrix b E W n ω) := by
  unfold fullPathMatrix
  have h1 := (continuous_pathMatrix W n).comp (continuous_pathAt W n)
  have h2 := (continuous_pathPortCoupling W n).comp (continuous_pathAt W n)
  exact Continuous.matrix_fromBlocks (h1.sub continuous_const) h2 h2.matrix_conjTranspose
    continuous_const

/-- `G = 𝓜⁻¹` is measurable (the inverse is Borel, not continuous). -/
theorem measurable_fullInverse (b E : ℝ) (W n : ℕ) :
    Measurable (fun ω : GrowthPath W => fullInverse b E W n ω) := by
  have : SecondCountableTopology (Matrix (Fin W) (Fin W) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin W → Fin W → ℂ))
  exact BlockBand.Layers.measurable_matrix_inv.comp (continuous_fullPathMatrix b E W n).measurable

/-- `G ↦ G₁₂ᴴ G₁₂` is continuous. -/
theorem continuous_clockOfInverse {W n : ℕ} :
    Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      (G.toBlocks₁₂)ᴴ * G.toBlocks₁₂) := by
  have h : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ => G.toBlocks₁₂) :=
    continuous_pi fun x => continuous_pi fun y => by unfold Matrix.toBlocks₁₂; fun_prop
  exact h.matrix_conjTranspose.matrix_mul h

/-- `Y = 𝒰_n*𝒰_n` is measurable in the path. -/
theorem measurable_fullClock (b E : ℝ) (W n : ℕ) :
    Measurable (fun ω : GrowthPath W => fullClock b E W n ω) :=
  continuous_clockOfInverse.measurable.comp (measurable_fullInverse b E W n)

/-- `(Y, h) ↦ Re(h*Yh)` is jointly continuous. -/
theorem continuous_quadForm {ι : Type*} [Fintype ι] :
    Continuous (fun x : Matrix ι ι ℂ × (ι → ℂ) => quadForm x.1 x.2) := by
  unfold quadForm
  refine Complex.continuous_re.comp ?_
  simp only [dotProduct, mulVec]
  fun_prop

/-- `T_W` is measurable on the product space. -/
theorem measurable_scaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    Measurable (scaledClock b s j) := by
  unfold scaledClock
  exact (continuous_quadForm.measurable.comp
    (((measurable_fullClock b _ _ _).comp measurable_fst).prodMk measurable_snd)).div_const _

/-- `M_W` is measurable on the product space. -/
theorem measurable_rescaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    Measurable (rescaledClock b s j) := by
  unfold rescaledClock
  exact (continuous_quadForm.measurable.comp
    (((measurable_fullClock b _ _ _).comp measurable_fst).prodMk measurable_snd)).div_const _

/-- `A_W` is measurable on the path space. -/
theorem measurable_traceClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ) :
    Measurable (traceClock b s j) := by
  unfold traceClock
  have h : Continuous (fun Y : Matrix (Fin 2 × Fin (s.W j)) (Fin 2 × Fin (s.W j)) ℂ =>
      Y.trace.re) := Complex.continuous_re.comp (continuous_id.matrix_trace)
  exact (h.measurable.comp (measurable_fullClock b _ _ _)).div_const _

/-!
## 2. Laws are probability measures
-/

/-- The growth-path law is a probability measure. -/
instance isProbabilityMeasure_growthPathLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthPathLaw W b) := by
  unfold growthPathLaw; infer_instance

/-- The probed law is a probability measure. -/
instance isProbabilityMeasure_probedClockLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (probedClockLaw W b) := by
  unfold probedClockLaw; infer_instance

/-- Every clock law is a probability measure. -/
instance isProbabilityMeasure_clockLaw (W : ℕ) (b : ℝ)
    (X : GrowthPath W × (Fin 2 × Fin W → ℂ) → ℝ) :
    IsProbabilityMeasure (clockLaw W b X) := by
  unfold clockLaw; infer_instance

/-!
## 3. The conditional mean `E_h[h*Yh] = Re Tr Y`
-/

/-- The contract's `circularVectorLaw` is the image of the Counting product law
`Π_a N(0,1/2)⊗N(0,1/2)` under `z ↦ (z_a.1 + i z_a.2)_a`. -/
theorem circularVectorLaw_eq_map_counting (ι : Type*) [Fintype ι] :
    circularVectorLaw ι =
      (BlockBand.Counting.circularVectorLaw ι).map BlockBand.Counting.circularVector := by
  have hone : BlockBand.Coarea.ProjectiveHaar.circularLawOne =
      BlockBand.Counting.standardCircularGaussian.map
        BlockBand.Counting.circularGaussianCoordinate := by
    unfold BlockBand.Coarea.ProjectiveHaar.circularLawOne BlockBand.Counting.standardCircularGaussian
      BlockBand.Counting.standardCircularReal
    rw [← (measurePreserving_finTwoArrow (gaussianReal 0 (1 / 2 : ℝ≥0))).symm.map_eq,
      Measure.map_map Complex.measurableEquivPi.symm.measurable
        (MeasurableEquiv.measurable _)]
    congr 1
    funext z
    simp [Complex.measurableEquivPi_symm_apply, BlockBand.Counting.circularGaussianCoordinate,
      MeasurableEquiv.finTwoArrow, mul_comm]
  rw [BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_eq_pi, BlockBand.Counting.circularVectorLaw]
  unfold BlockBand.Counting.circularVector
  have hmc : Measurable BlockBand.Counting.circularGaussianCoordinate := by
    unfold BlockBand.Counting.circularGaussianCoordinate; fun_prop
  rw [Measure.pi_map_pi (fun _ => hmc.aemeasurable), hone]

/-- `Re(q*Yq)` is the real part of the Counting quadratic form. -/
theorem quadForm_eq_re_complexQuadraticForm {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℂ)
    (v : ι → ℂ) : quadForm Y v = (BlockBand.Counting.complexQuadraticForm Y v).re := by
  unfold quadForm BlockBand.Counting.complexQuadraticForm
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `Re(h*Yh)` is integrable under `CN(0, I)`. -/
theorem integrable_quadForm_circular {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℂ) :
    Integrable (fun h => quadForm Y h) (circularVectorLaw ι) := by
  classical
  rw [circularVectorLaw_eq_map_counting]
  have hm : Measurable (BlockBand.Counting.circularVector (ι := ι)) := by
    unfold BlockBand.Counting.circularVector BlockBand.Counting.circularGaussianCoordinate
    fun_prop
  have hc : Continuous (fun h : ι → ℂ => quadForm Y h) :=
    continuous_quadForm.comp (continuous_const.prodMk continuous_id)
  rw [integrable_map_measure hc.aestronglyMeasurable hm.aemeasurable]
  have := (BlockBand.Counting.integrable_actualComplexQuadratic Y).re
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp [Function.comp, quadForm_eq_re_complexQuadraticForm]

/-- `E_h[Re(h*Yh)] = Re Tr Y` for `h ~ CN(0, I)` and every deterministic complex `Y`. -/
theorem integral_quadForm_circular {ι : Type*} [Fintype ι] (Y : Matrix ι ι ℂ) :
    ∫ h, quadForm Y h ∂circularVectorLaw ι = Y.trace.re := by
  classical
  rw [circularVectorLaw_eq_map_counting]
  have hm : Measurable (BlockBand.Counting.circularVector (ι := ι)) := by
    unfold BlockBand.Counting.circularVector BlockBand.Counting.circularGaussianCoordinate
    fun_prop
  have hc : Continuous (fun h : ι → ℂ => quadForm Y h) :=
    continuous_quadForm.comp (continuous_const.prodMk continuous_id)
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
  simp_rw [quadForm_eq_re_complexQuadraticForm]
  have := integral_re (BlockBand.Counting.integrable_actualComplexQuadratic Y)
  simp only [RCLike.re_to_complex] at this
  rw [this, BlockBand.Counting.integral_actualComplexQuadratic_eq_trace]

/-- `h*(U*U)h ≥ 0`. -/
theorem quadForm_conjTranspose_mul_self_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix κ ι ℂ) (h : ι → ℂ) : 0 ≤ quadForm (Uᴴ * U) h := by
  classical
  have := (posSemidef_conjTranspose_mul_self U).dotProduct_mulVec_nonneg h
  exact (Complex.nonneg_iff.mp this).1

/-- `h*Yh ≥ 0` for the full clock `Y = 𝒰*𝒰`. -/
theorem fullClock_quadForm_nonneg (b E : ℝ) (W n : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) : 0 ≤ quadForm (fullClock b E W n ω) h :=
  quadForm_conjTranspose_mul_self_nonneg _ h

/-!
## 4. The finite-width conditional Markov inequality
-/

/-- Unfolding `M_W`. -/
theorem rescaledClock_apply (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (ω : GrowthPath (s.W j)) (h : Fin 2 × Fin (s.W j) → ℂ) :
    rescaledClock b s j (ω, h) =
      quadForm (fullClock b (s.energy j) (s.W j) (s.n j) ω) h / ((s.n j : ℝ) * s.W j) := rfl

/-- Unfolding `T_W`. -/
theorem scaledClock_apply (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (x : GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ)) :
    scaledClock b s j x =
      quadForm (fullClock b (s.energy j) (s.W j) (s.n j) x.1) x.2 / (s.W j : ℝ) ^ 2 := rfl

/-- Conditional mean: `E_h M_W = A_W` for every path `ω` (any `n`, any `W`). -/
theorem integral_rescaledClock (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (ω : GrowthPath (s.W j)) :
    ∫ h, rescaledClock b s j (ω, h) ∂circularVectorLaw (Fin 2 × Fin (s.W j)) =
      traceClock b s j ω := by
  simp_rw [rescaledClock_apply]
  rw [integral_div, integral_quadForm_circular]
  rfl

/-- Conditional Markov bound: for every path `ω` with `A_W(ω) ≤ ε` (`0 < ε`),
`P_h(M_W > √ε) ≤ √ε`. -/
theorem circular_rescaledClock_gt_le (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (ω : GrowthPath (s.W j)) {ε : ℝ} (hε : 0 < ε) (hA : traceClock b s j ω ≤ ε) :
    circularVectorLaw (Fin 2 × Fin (s.W j)) {h | Real.sqrt ε < rescaledClock b s j (ω, h)} ≤
      ENNReal.ofReal (Real.sqrt ε) := by
  set c := Real.sqrt ε with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hε
  have hmeas : Measurable (fun h => rescaledClock b s j (ω, h)) :=
    (measurable_rescaledClock b s j).comp measurable_prodMk_left
  have hnn : ∀ h, 0 ≤ rescaledClock b s j (ω, h) := fun h => by
    rw [rescaledClock_apply]
    exact div_nonneg (fullClock_quadForm_nonneg _ _ _ _ _ _) (by positivity)
  have hint : Integrable (fun h => rescaledClock b s j (ω, h))
      (circularVectorLaw (Fin 2 × Fin (s.W j))) := by
    simp_rw [rescaledClock_apply]
    exact (integrable_quadForm_circular (fullClock b (s.energy j) (s.W j) (s.n j) ω)).div_const _
  have hmark := mul_meas_ge_le_lintegral₀ (μ := circularVectorLaw (Fin 2 × Fin (s.W j)))
    (f := fun h => ENNReal.ofReal (rescaledClock b s j (ω, h)))
    (ENNReal.measurable_ofReal.comp hmeas).aemeasurable (ENNReal.ofReal c)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn),
    integral_rescaledClock] at hmark
  have hsub : {h | c < rescaledClock b s j (ω, h)} ⊆
      {h | ENNReal.ofReal c ≤ ENNReal.ofReal (rescaledClock b s j (ω, h))} := fun h hh =>
    ENNReal.ofReal_le_ofReal (le_of_lt hh)
  have h1 : ENNReal.ofReal c * circularVectorLaw (Fin 2 × Fin (s.W j))
      {h | c < rescaledClock b s j (ω, h)} ≤ ENNReal.ofReal c * ENNReal.ofReal c := by
    calc _ ≤ _ := by gcongr
      _ ≤ ENNReal.ofReal (traceClock b s j ω) := hmark
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hA
      _ = ENNReal.ofReal c * ENNReal.ofReal c := by
        rw [← ENNReal.ofReal_mul hc0.le, hc, Real.mul_self_sqrt hε.le]
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hc0) ENNReal.ofReal_ne_top).mp h1

/-- **Finite-width step of the clock small-ball lemma**:
`(1 - √ε) P(A_W ≤ ε) ≤ P(M_W ≤ √ε)`, for every width, length and `0 < ε`. -/
theorem ofReal_mul_growthPathLaw_traceClock_le (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E)
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (1 - Real.sqrt ε) * growthPathLaw (s.W j) b {ω | traceClock b s j ω ≤ ε} ≤
      clockLaw (s.W j) b (rescaledClock b s j) (Set.Iic (Real.sqrt ε)) := by
  set c := Real.sqrt ε with hc
  have hM := measurable_rescaledClock b s j
  have hS : MeasurableSet {x | rescaledClock b s j x ≤ c} := measurableSet_le hM measurable_const
  unfold clockLaw probedClockLaw
  rw [Measure.map_apply hM measurableSet_Iic]
  change _ ≤ ((growthPathLaw (s.W j) b).prod (circularVectorLaw (Fin 2 × Fin (s.W j))))
    {x | rescaledClock b s j x ≤ c}
  rw [Measure.prod_apply hS]
  have hf : Measurable fun ω => circularVectorLaw (Fin 2 × Fin (s.W j))
      (Prod.mk ω ⁻¹' {x | rescaledClock b s j x ≤ c}) := measurable_measure_prodMk_left hS
  refine le_trans ?_ (mul_meas_ge_le_lintegral₀ hf.aemeasurable (ENNReal.ofReal (1 - c)))
  refine mul_le_mul' le_rfl (measure_mono fun ω (hω : traceClock b s j ω ≤ ε) => ?_)
  change ENNReal.ofReal (1 - c) ≤ circularVectorLaw (Fin 2 × Fin (s.W j))
    (Prod.mk ω ⁻¹' {x | rescaledClock b s j x ≤ c})
  have hmeas : Measurable (fun h => rescaledClock b s j (ω, h)) :=
    hM.comp measurable_prodMk_left
  have hset : Prod.mk ω ⁻¹' {x | rescaledClock b s j x ≤ c} =
      {h | c < rescaledClock b s j (ω, h)}ᶜ := by
    ext h; simp [not_lt]
  rw [hset, prob_compl_eq_one_sub (measurableSet_lt measurable_const hmeas),
    ENNReal.ofReal_sub _ (Real.sqrt_nonneg _), ENNReal.ofReal_one]
  exact tsub_le_tsub_left (circular_rescaledClock_gt_le b s j ω hε hω) _

/-!
## 5. Weak-limit tools on `ℝ`: Prokhorov extraction, Portmanteau, Slutsky, Markov
-/

/-- `IsTightSeq` gives Mathlib tightness of the range. -/
theorem isTightMeasureSet_range_of_isTightSeq {ν : ℕ → Measure ℝ} (h : IsTightSeq ν) :
    IsTightMeasureSet (Set.range ν) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => htop ▸ le_top⟩
  obtain ⟨R, hR⟩ := h ε.toReal (ENNReal.toReal_pos hε.ne' htop)
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro _ ⟨j, rfl⟩
  have hset : (Metric.closedBall (0 : ℝ) R)ᶜ = {x | R < |x|} := by
    ext x; simp
  rw [hset]
  exact (hR j).trans (ENNReal.ofReal_toReal htop).le

/-- A sequence of probability measures on `ℝ`, as points of `ProbabilityMeasure ℝ`. -/
def probSeq (ν : ℕ → Measure ℝ) [hν : ∀ j, IsProbabilityMeasure (ν j)] (j : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨ν j, hν j⟩

@[simp] theorem coe_probSeq (ν : ℕ → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)] (j : ℕ) :
    ((probSeq ν j : ProbabilityMeasure ℝ) : Measure ℝ) = ν j := rfl

/-- **Prokhorov extraction.** A tight sequence of probability measures on `ℝ` has a weakly
convergent subsequence (convergence in `ProbabilityMeasure ℝ`). -/
theorem exists_tendsto_subseq_of_isTightSeq (ν : ℕ → Measure ℝ)
    [hν : ∀ j, IsProbabilityMeasure (ν j)] (h : IsTightSeq ν) :
    ∃ μ : ProbabilityMeasure ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => probSeq ν (φ k)) atTop (𝓝 μ) := by
  let P : ℕ → ProbabilityMeasure ℝ := probSeq ν
  have hS : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
    convert isTightMeasureSet_range_of_isTightSeq h using 1
    ext m
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨P j, ⟨j, rfl⟩, rfl⟩
  obtain ⟨μ, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet hS).tendsto_subseq
    (fun n => subset_closure ⟨n, rfl⟩)
  exact ⟨μ, φ, hφ, hlim⟩

/-- **Slutsky (deterministic scaling).** If `ν_j → μ` weakly (bounded continuous tests),
`ν_j` is eventually tight and `c_j → c₀`, then `∫ f(c_j x) dν_j → ∫ f(c₀ x) dμ`. -/
theorem tendsto_integral_comp_mul {ν : ℕ → Measure ℝ} [∀ j, IsProbabilityMeasure (ν j)]
    {μ : Measure ℝ}
    (htight : ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ᶠ j in atTop, ν j {x | R < |x|} ≤ ENNReal.ofReal δ)
    (hlim : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ x, f x ∂ν j) atTop (𝓝 (∫ x, f x ∂μ)))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀)) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun j => ∫ x, f (c j * x) ∂ν j) atTop (𝓝 (∫ x, f (c₀ * x) ∂μ)) := by
  have hint : ∀ (a : ℝ) j, Integrable (fun x => f (a * x)) (ν j) := fun a j =>
    BoundedContinuousFunction.integrable (ν j)
      (f.compContinuous ⟨fun x => a * x, continuous_const.mul continuous_id⟩)
  have hg := hlim (f.compContinuous ⟨fun x => c₀ * x, continuous_const.mul continuous_id⟩)
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] at hg
  suffices hd : Tendsto (fun j => ∫ x, f (c j * x) ∂ν j - ∫ x, f (c₀ * x) ∂ν j) atTop (𝓝 0) by
    have := hd.add hg
    simp only [sub_add_cancel, zero_add] at this
    exact this
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B := ‖f‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  set δ := ε / (4 * (B + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨R₀, hR₀⟩ := htight δ hδ0
  set R := max R₀ 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  set L := (|c₀| + 1) * R with hL
  have huc := (isCompact_Icc (a := -L) (b := L)).uniformContinuousOn_of_continuous
    f.continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη0, hη⟩ := huc (ε / 2) (by positivity)
  have hcj : ∀ᶠ j in atTop, |c j - c₀| < min 1 (η / (R + 1)) := by
    have := (Metric.tendsto_nhds.mp hc) (min 1 (η / (R + 1))) (by positivity)
    simpa [Real.dist_eq] using this
  filter_upwards [hR₀, hcj] with j hj hcj
  have hc1 : |c j - c₀| < 1 := lt_of_lt_of_le hcj (min_le_left _ _)
  have hc2 : |c j - c₀| < η / (R + 1) := lt_of_lt_of_le hcj (min_le_right _ _)
  set S : Set ℝ := {x | R < |x|} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const measurable_abs
  have hSj : ν j S ≤ ENNReal.ofReal δ := by
    refine le_trans (measure_mono fun x (hx : R < |x|) => ?_) hj
    exact lt_of_le_of_lt (le_max_left _ _) hx
  have hpt : ∀ x, ‖f (c j * x) - f (c₀ * x)‖ ≤ ε / 2 + 2 * B * S.indicator 1 x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      have h1 := f.norm_coe_le_norm (c j * x)
      have h2 := f.norm_coe_le_norm (c₀ * x)
      calc ‖f (c j * x) - f (c₀ * x)‖ ≤ ‖f (c j * x)‖ + ‖f (c₀ * x)‖ := norm_sub_le _ _
        _ ≤ ε / 2 + 2 * B * (1 : ℝ → ℝ) x := by simp only [Pi.one_apply]; linarith
    · rw [Set.indicator_of_notMem hx]
      have hxR : |x| ≤ R := not_lt.mp hx
      have hcjx : |c j| ≤ |c₀| + 1 := by
        have := abs_sub_abs_le_abs_sub (c j) c₀
        linarith
      have hmem1 : c j * x ∈ Set.Icc (-L) L := by
        rw [Set.mem_Icc, ← abs_le, abs_mul]
        exact mul_le_mul hcjx hxR (abs_nonneg _) (by positivity)
      have hmem2 : c₀ * x ∈ Set.Icc (-L) L := by
        rw [Set.mem_Icc, ← abs_le, abs_mul]
        exact mul_le_mul (by linarith) hxR (abs_nonneg _) (by positivity)
      have hdist : dist (c j * x) (c₀ * x) < η := by
        rw [Real.dist_eq, ← sub_mul, abs_mul]
        calc |c j - c₀| * |x| ≤ |c j - c₀| * (R + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ < η / (R + 1) * (R + 1) := mul_lt_mul_of_pos_right hc2 (by positivity)
          _ = η := div_mul_cancel₀ _ (by positivity)
      have := hη _ hmem1 _ hmem2 hdist
      rw [dist_eq_norm] at this
      simp only [mul_zero, add_zero]
      exact this.le
  have hi2 : Integrable (fun x => 2 * B * S.indicator 1 x) (ν j) :=
    ((integrable_const (1 : ℝ)).indicator hSm).const_mul _
  have hgi : Integrable (fun x => ε / 2 + 2 * B * S.indicator 1 x) (ν j) :=
    (integrable_const _).add hi2
  have hcomp : ∫ x, (ε / 2 + 2 * B * S.indicator 1 x) ∂ν j = ε / 2 + 2 * B * (ν j).real S := by
    rw [integral_add (integrable_const _) hi2, integral_const_mul, integral_indicator_one hSm,
      integral_const]
    simp
  rw [Real.dist_eq, sub_zero, ← integral_sub (hint _ _) (hint _ _)]
  have hle := norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)
  rw [hcomp] at hle
  have hSr : (ν j).real S ≤ δ := ENNReal.toReal_le_of_le_ofReal hδ0.le hSj
  have : 2 * B * (ν j).real S ≤ 2 * B * δ := mul_le_mul_of_nonneg_left hSr (by positivity)
  have hBδ : 2 * B * δ < ε / 2 := by
    rw [hδ]
    have : 2 * B * (ε / (4 * (B + 1))) = ε / 2 * (B / (B + 1)) := by field_simp; ring
    rw [this]
    have : B / (B + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    nlinarith
  rw [← Real.norm_eq_abs]
  linarith

/-- **Markov for a positive limit.** If `μ(-∞,0] = 0` and `∫ x^{-p} dμ ≤ C`, then
`μ(-∞, √ε] ≤ C ε^{p/2}` for every `ε > 0`. -/
theorem measure_Iic_sqrt_le {μ : Measure ℝ} (hμ0 : μ (Set.Iic 0) = 0) {p C : ℝ} (hp : 0 < p)
    (hC : ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ ≤ ENNReal.ofReal C) {ε : ℝ} (hε : 0 < ε) :
    μ (Set.Iic (Real.sqrt ε)) ≤ ENNReal.ofReal (C * ε ^ (p / 2)) := by
  set a := ε ^ (-(p / 2)) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hε _
  have hsplit : μ (Set.Iic (Real.sqrt ε)) ≤ μ (Set.Ioc 0 (Real.sqrt ε)) := by
    calc μ (Set.Iic (Real.sqrt ε)) ≤ μ (Set.Iic 0 ∪ Set.Ioc 0 (Real.sqrt ε)) :=
          measure_mono fun x hx => by
            by_cases h0 : x ≤ 0
            · exact Or.inl h0
            · exact Or.inr ⟨lt_of_not_ge h0, hx⟩
      _ ≤ μ (Set.Iic 0) + μ (Set.Ioc 0 (Real.sqrt ε)) := measure_union_le _ _
      _ = _ := by rw [hμ0, zero_add]
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (-p))) := by fun_prop
  have hmark := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable (ENNReal.ofReal a) (μ := μ)
  have hsub : Set.Ioc 0 (Real.sqrt ε) ⊆ {x | ENNReal.ofReal a ≤ ENNReal.ofReal (x ^ (-p))} := by
    rintro x ⟨hx0, hxs⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.rpow_le_rpow_of_nonpos hx0 hxs (by linarith : -p ≤ 0)
    have h2 : Real.sqrt ε ^ (-p) = a := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hε.le, ha]
      ring_nf
    exact h2 ▸ h1
  have h3 : ENNReal.ofReal a * μ (Set.Ioc 0 (Real.sqrt ε)) ≤ ENNReal.ofReal C :=
    ((mul_le_mul' le_rfl (measure_mono hsub)).trans hmark).trans hC
  have h4 : μ (Set.Ioc 0 (Real.sqrt ε)) ≤ ENNReal.ofReal C / ENNReal.ofReal a := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ha0)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact h3
  have h5 : C * ε ^ (p / 2) = C / a := by
    rw [ha, Real.rpow_neg hε.le, div_inv_eq_mul]
  refine hsplit.trans (h4.trans ?_)
  rw [h5, ENNReal.ofReal_div_of_pos ha0]

/-!
## 6. The clock sequence: `T_W = τ_W M_W`, tightness of `M_W`, Slutsky
-/

section ClockSequence

variable {τ E : ℝ}

/-- `T_W = τ_W M_W` pointwise, `τ_W = n/W`, whenever `n > 0`. -/
theorem scaledClock_eq_mul (b : ℝ) (s : ClockSequence τ E) (j : ℕ) (hn : 0 < s.n j)
    (x : GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ)) :
    scaledClock b s j x = (s.n j : ℝ) / s.W j * rescaledClock b s j x := by
  rw [scaledClock_apply, rescaledClock_apply]
  have hW : (s.W j : ℝ) ≠ 0 := by exact_mod_cast (s.W_pos j).ne'
  have hn' : (s.n j : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Integrals against the law of `T_W` are integrals of `f(τ_W x)` against the law of `M_W`. -/
theorem integral_clockLaw_scaledClock (b : ℝ) (s : ClockSequence τ E) (j : ℕ) (hn : 0 < s.n j)
    (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂clockLaw (s.W j) b (scaledClock b s j) =
      ∫ x, f ((s.n j : ℝ) / s.W j * x) ∂clockLaw (s.W j) b (rescaledClock b s j) := by
  unfold clockLaw
  rw [integral_map (measurable_scaledClock b s j).aemeasurable f.continuous.aestronglyMeasurable,
    integral_map (f := fun x : ℝ => f ((s.n j : ℝ) / s.W j * x))
      (measurable_rescaledClock b s j).aemeasurable
      (f.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable]
  simp_rw [scaledClock_eq_mul b s j hn]

/-- `τ_W ≥ τ/2 > 0` forces `n > 0`. -/
theorem pos_of_half_le_ratio (s : ClockSequence τ E) (hτ : 0 < τ) {j : ℕ}
    (hj : τ / 2 ≤ (s.n j : ℝ) / s.W j) : 0 < s.n j := by
  rcases Nat.eq_zero_or_pos (s.n j) with h0 | h0
  · rw [h0] at hj; simp at hj; linarith
  · exact h0

/-- Eventually `τ_W ≥ τ/2`. -/
theorem eventually_half_le_ratio (s : ClockSequence τ E) (hτ : 0 < τ) :
    ∀ᶠ j in atTop, τ / 2 ≤ (s.n j : ℝ) / s.W j :=
  s.ratio_tendsto.eventually_const_le (by linarith)

/-- Tightness of `M_W = T_W/τ_W` on the indices with `τ_W ≥ τ/2`, from `h.tight`. -/
theorem rescaledClock_tight (h : NegativeClockContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE0 : -2 < E) (hE1 : E < 2) (hτ : 0 < τ) (s : ClockSequence τ E) :
    ∀ δ : ℝ, 0 < δ → ∃ R : ℝ, ∀ j, τ / 2 ≤ (s.n j : ℝ) / s.W j →
      clockLaw (s.W j) b (rescaledClock b s j) {x | R < |x|} ≤ ENNReal.ofReal δ := by
  intro δ hδ
  obtain ⟨R₀, hR₀⟩ := h.tight b hb0 hb1 E hE0 hE1 τ hτ s δ hδ
  refine ⟨2 * max R₀ 0 / τ, fun j hj => ?_⟩
  have hn := pos_of_half_le_ratio s hτ hj
  have hS : MeasurableSet {x : ℝ | 2 * max R₀ 0 / τ < |x|} :=
    measurableSet_lt measurable_const measurable_abs
  have hS₀ : MeasurableSet {x : ℝ | R₀ < |x|} := measurableSet_lt measurable_const measurable_abs
  refine le_trans ?_ (hR₀ j)
  unfold clockLaw
  rw [Measure.map_apply (measurable_rescaledClock b s j) hS,
    Measure.map_apply (measurable_scaledClock b s j) hS₀]
  refine measure_mono fun x (hx : 2 * max R₀ 0 / τ < |rescaledClock b s j x|) => ?_
  change R₀ < |scaledClock b s j x|
  have hτj : 0 < (s.n j : ℝ) / s.W j := lt_of_lt_of_le (by linarith) hj
  rw [scaledClock_eq_mul b s j hn, abs_mul, abs_of_pos hτj]
  have hR' : 0 ≤ 2 * max R₀ 0 / τ := by positivity
  calc R₀ ≤ max R₀ 0 := le_max_left _ _
    _ = τ / 2 * (2 * max R₀ 0 / τ) := by field_simp
    _ ≤ (s.n j : ℝ) / s.W j * (2 * max R₀ 0 / τ) := mul_le_mul_of_nonneg_right hj hR'
    _ < _ := mul_lt_mul_of_pos_left hx hτj

/-- **Slutsky step of the clock small-ball lemma**: if `μ` is a
subsequential limit of the laws of `M_W`, then `x ↦ τx` pushes it to a subsequential limit of the
laws of `T_W` (along the same subsequence). -/
theorem isSubsequentialLimit_scaledClock (h : NegativeClockContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) (hτ : 0 < τ) (s : ClockSequence τ E)
    {μ : Measure ℝ}
    (hμ : IsSubsequentialLimit (fun j => clockLaw (s.W j) b (rescaledClock b s j)) μ) :
    IsSubsequentialLimit (fun j => clockLaw (s.W j) b (scaledClock b s j))
      (μ.map (fun x => τ * x)) := by
  obtain ⟨hprob, φ, hφ, hconv⟩ := hμ
  have hmeas : Measurable (fun x : ℝ => τ * x) := measurable_const.mul measurable_id
  refine ⟨inferInstance, φ, hφ, fun f => ?_⟩
  rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hgood : ∀ᶠ k in atTop, τ / 2 ≤ (s.n (φ k) : ℝ) / s.W (φ k) :=
    hφt.eventually (eventually_half_le_ratio s hτ)
  have htight := rescaledClock_tight h hb0 hb1 hE0 hE1 hτ s
  have hsl := tendsto_integral_comp_mul
    (ν := fun k => clockLaw (s.W (φ k)) b (rescaledClock b s (φ k))) (μ := μ)
    (fun δ hδ => by
      obtain ⟨R, hR⟩ := htight δ hδ
      exact ⟨R, hgood.mono fun k hk => hR _ hk⟩)
    hconv (c := fun k => (s.n (φ k) : ℝ) / s.W (φ k)) (s.ratio_tendsto.comp hφt) f
  refine hsl.congr' (hgood.mono fun k hk => ?_)
  exact (integral_clockLaw_scaledClock b s (φ k) (pos_of_half_le_ratio s hτ hk) f).symm

end ClockSequence

/-!
## 7. the clock small-ball lemma
-/

section Main

variable {τ E : ℝ}

/-- **Limit clause of the clock small-ball lemma**.
If every subsequential limit `ν` of the laws of `T_W` has `ν(-∞,0] = 0` and
`∫ x^{-p} dν ≤ C₀ τ^{-p}`, then every subsequential limit `μ` of the laws of `M_W` has
`μ(-∞,0] = 0` and `∫ x^{-p} dμ ≤ max C₀ 0`. -/
theorem rescaled_limit_of_scaled_limit (h : NegativeClockContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) (hτ : 0 < τ) (s : ClockSequence τ E)
    {p C₀ : ℝ}
    (hneg : ∀ ν : Measure ℝ,
      IsSubsequentialLimit (fun j => clockLaw (s.W j) b (scaledClock b s j)) ν →
        ν (Set.Iic 0) = 0 ∧ ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂ν ≤ ENNReal.ofReal (C₀ * τ ^ (-p)))
    (μ : Measure ℝ)
    (hμ : IsSubsequentialLimit (fun j => clockLaw (s.W j) b (rescaledClock b s j)) μ) :
    μ (Set.Iic 0) = 0 ∧ ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ ≤ ENNReal.ofReal (max C₀ 0) := by
  have hmeas : Measurable (fun x : ℝ => τ * x) := measurable_const.mul measurable_id
  obtain ⟨h0, hint⟩ := hneg _ (isSubsequentialLimit_scaledClock h hb0 hb1 hE0 hE1 hτ s hμ)
  have hpre : (fun x : ℝ => τ * x) ⁻¹' Set.Iic 0 = Set.Iic 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hx
      by_contra hx'
      have := mul_pos hτ (lt_of_not_ge hx')
      linarith
    · intro hx
      exact mul_nonpos_of_nonneg_of_nonpos hτ.le hx
  rw [Measure.map_apply hmeas measurableSet_Iic, hpre] at h0
  refine ⟨h0, ?_⟩
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (-p))) := by fun_prop
  rw [lintegral_map hg hmeas] at hint
  have hae : ∀ᵐ x ∂μ, ENNReal.ofReal ((τ * x) ^ (-p)) =
      ENNReal.ofReal (τ ^ (-p)) * ENNReal.ofReal (x ^ (-p)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
    have hx0 : 0 < x := lt_of_not_ge hx
    rw [Real.mul_rpow hτ.le hx0.le, ENNReal.ofReal_mul (Real.rpow_nonneg hτ.le _)]
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hg] at hint
  have hτp : 0 < τ ^ (-p) := Real.rpow_pos_of_pos hτ _
  have hle : ENNReal.ofReal (C₀ * τ ^ (-p)) ≤
      ENNReal.ofReal (τ ^ (-p)) * ENNReal.ofReal (max C₀ 0) := by
    rw [← ENNReal.ofReal_mul hτp.le]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [le_max_left C₀ 0])
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hτp) ENNReal.ofReal_ne_top).mp
    (hint.trans hle)

/-- **Portmanteau step of the clock small-ball lemma**. If every
subsequential limit `μ` of the laws of `M_W` has `μ(-∞,0] = 0` and `∫ x^{-p} dμ ≤ C`, then for
every `c' > C ε^{p/2}`, eventually `P(M_W ≤ √ε) ≤ c'`. -/
theorem eventually_clockLaw_Iic_sqrt_le (h : NegativeClockContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) (hτ : 0 < τ) (s : ClockSequence τ E)
    {p C : ℝ} (hp : 0 < p)
    (hlim : ∀ μ : Measure ℝ,
      IsSubsequentialLimit (fun j => clockLaw (s.W j) b (rescaledClock b s j)) μ →
        μ (Set.Iic 0) = 0 ∧ ∫⁻ x, ENNReal.ofReal (x ^ (-p)) ∂μ ≤ ENNReal.ofReal C)
    {ε : ℝ} (hε : 0 < ε) {c' : ℝ≥0∞} (hc' : ENNReal.ofReal (C * ε ^ (p / 2)) < c') :
    ∀ᶠ j in atTop, clockLaw (s.W j) b (rescaledClock b s j) (Set.Iic (Real.sqrt ε)) ≤ c' := by
  by_contra hcon
  rw [not_eventually] at hcon
  have hfreq := (hcon.and_eventually (eventually_half_le_ratio s hτ))
  obtain ⟨ψ, hψ, hP⟩ := extraction_of_frequently_atTop hfreq
  let ν : ℕ → Measure ℝ := fun k => clockLaw (s.W (ψ k)) b (rescaledClock b s (ψ k))
  have htight := rescaledClock_tight h hb0 hb1 hE0 hE1 hτ s
  have hνt : IsTightSeq ν := fun δ hδ => by
    obtain ⟨R, hR⟩ := htight δ hδ
    exact ⟨R, fun k => hR _ (hP k).2⟩
  obtain ⟨μ, φ, hφ, hconv⟩ := exists_tendsto_subseq_of_isTightSeq ν hνt
  have hsub : IsSubsequentialLimit (fun j => clockLaw (s.W j) b (rescaledClock b s j))
      (μ : Measure ℝ) :=
    ⟨inferInstance, ψ ∘ φ, hψ.comp hφ, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      hconv⟩
  obtain ⟨h0, hC⟩ := hlim _ hsub
  have hmark := measure_Iic_sqrt_le h0 hp hC hε
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
    (isClosed_Iic (a := Real.sqrt ε))
  have hlow : c' ≤ atTop.limsup fun k => ((probSeq ν (φ k) : ProbabilityMeasure ℝ) : Measure ℝ)
      (Set.Iic (Real.sqrt ε)) :=
    le_limsup_of_frequently_le (Frequently.of_forall fun k => (not_le.mp (hP (φ k)).1).le)
  exact absurd (hlow.trans (hport.trans hmark)) (not_le.mpr hc')

/-- **The clock small-ball lemma from the negative-clock theorem.** Quantifiers exactly as in
`ClockSmallBallContract`: `β, κ, T₀, p` first, then the single constant `C = max C₀ 0` with `C₀` the constant of
`NegativeClockContract.negative` for the same `β, κ, T₀, p`; uniform in
`b ∈ [β, 1/2 - β]`, `E ∈ bulkInterval κ`, `τ ∈ (0, T₀]`, and every clock sequence whose energies
are eventually in `bulkInterval κ`. Both clauses (`limit`, `smallBall`) are derived from
`NegativeClockContract`; the width limit precedes the small-ball limit; no finite-width negative
moment is used.
-/
theorem clockSmallBall_of_negativeClock (h : NegativeClockContract) : ClockSmallBallContract := by
  intro β κ T₀ p hβ hβ4 hκ hT₀ hp
  obtain ⟨C₀, hC₀⟩ := h.negative β κ T₀ p hβ hβ4 hκ hT₀ hp
  refine ⟨max C₀ 0, fun b hb E hE τ hτ hτT s hev => ?_⟩
  have hb' : β ≤ b ∧ b ≤ 1 / 2 - β := hb
  have hE' : -2 + κ ≤ E ∧ E ≤ 2 - κ := hE
  have hb0 : 0 < b := lt_of_lt_of_le hβ hb'.1
  have hb1 : b < 1 / 2 := lt_of_le_of_lt hb'.2 (by linarith)
  have hE0 : -2 < E := lt_of_lt_of_le (by linarith) hE'.1
  have hE1 : E < 2 := lt_of_le_of_lt hE'.2 (by linarith)
  have hlim := rescaled_limit_of_scaled_limit h hb0 hb1 hE0 hE1 hτ s
    (hC₀ b hb E hE τ hτ hτT s hev)
  refine ⟨hlim, fun ε hε hε1 => ?_⟩
  have hsq1 : Real.sqrt ε < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt hε.le hε1
  set d := ENNReal.ofReal (1 - Real.sqrt ε) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.ofReal_div_of_pos (by linarith)]
  refine le_of_forall_gt_imp_ge_of_dense fun c'' hc'' => ?_
  by_cases htop : c'' = ⊤
  · exact htop ▸ le_top
  have hlt : ENNReal.ofReal (max C₀ 0 * ε ^ (p / 2)) < d * c'' := by
    rw [mul_comm d]
    exact (ENNReal.div_lt_iff (Or.inl hd0) (Or.inl hdtop)).mp hc''
  have hev' := eventually_clockLaw_Iic_sqrt_le h hb0 hb1 hE0 hE1 hτ s hp hlim hε hlt
  refine limsup_le_of_le (by isBoundedDefault) (hev'.mono fun j hj => ?_)
  exact (ENNReal.mul_le_mul_iff_right hd0 hdtop).mp
    ((ofReal_mul_growthPathLaw_traceClock_le b s j hε).trans hj)

end Main

end BlockBand.Endpoints.Clock
