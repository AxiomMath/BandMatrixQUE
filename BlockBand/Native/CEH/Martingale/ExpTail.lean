module

public import BlockBand.Internal.Contracts.Transmission
public import BlockBand.Palm.RelativeLocalizationSemimart
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularAugment
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential (Freedman-type) tail bound for the martingale part of a continuous semimartingale

For a continuous semimartingale `Y` in `ℝ^d` with characteristics `(β, α)` and a coordinate `i`,
write `X_t = smCompensated Y β i t = Y^i_t - Y^i_0 - ∫_{(0,t]} β^i` and
`A_t = ∫_{(0,t]} α^{ii}`. No hypothesis beyond `IsContinuousSemimartingale` is used (in particular
no sign or continuity assumption on `α`).

* `isContinuousSemimartingale_compensated`: `X` is a real continuous semimartingale with drift
  `0` and covariance `α^{ii}` (same localizing sequence).
* `isContinuousSemimartingale_compensated_bracket`: `(X, A)` is a continuous semimartingale in
  `ℝ²` (`sumVec` layout) with drift `(0, α^{ii})` and covariance `α^{ii}` on the first block.
* `integral_le_of_drift_nonpos_ae`: a.s. bounded real semimartingale with nonpositive drift
  integrals has `E Y_t ≤ E Y_0` (a.e.-bound variant of
  `Palm.RelativeLocalization.integral_le_of_drift_nonpos`).
* `measure_exists_le_expMart_le`: maximal inequality for the exponential process
  `Z_t = exp(θ X_t - θ²/2 A_t)`: `Q(∃ t ≤ T, L ≤ Z_t) ≤ 1/L` for every `θ ∈ ℝ`, `L > 0`. Proof:
  Itô's formula (`semimartingaleItoFormula_holds`) for `φ(x, q) = exp(θx - θ²q/2)` gives drift
  `0`; stop at the (raw) hitting time `ρ` of `[L, ∞)` by `Z` (contract (a2),
  `stoppedSemimartingale_holds`), so `0 < Z^ρ ≤ L` a.s.; hence `E Z^ρ_T ≤ E Z_0 = 1`, and on the
  event `Z^ρ_T ≥ L`; Markov.
* `measure_compensated_ge_le_coord`, `measure_compensated_le_neg_le_coord`,
  `measure_abs_compensated_ge_le_coord`: for `a, b > 0`,
  `Q(∃ t ≤ T, a ≤ X_t ∧ A_t ≤ b) ≤ exp(-a²/(2b))`, the same for `X_t ≤ -a`, and
  `Q(∃ t ≤ T, a ≤ |X_t| ∧ A_t ≤ b) ≤ 2 exp(-a²/(2b))` (take `θ = ±a/b`, `L = exp(a²/(2b))`).
* `measure_compensated_ge_le`, `measure_abs_compensated_ge_le`: the `d = 1`, `i = 0` instances.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Martingale

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

/-!
### The exponential test function
-/

/-- The linear functional `(t, x, q) ↦ θ x - c q` on `ℝ × ℝ²`. -/
def expLin (θ c : ℝ) : ℝ × (Fin (1 + 1) → ℝ) →L[ℝ] ℝ :=
  θ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + 1) => ℝ) 0).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin (1 + 1) → ℝ))) -
    c • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (1 + 1) => ℝ) 1).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin (1 + 1) → ℝ)))

theorem expLin_apply (θ c : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) :
    expLin θ c p = θ * p.2 0 - c * p.2 1 := by
  simp [expLin]

/-- The exponential test function `φ(t, x, q) = exp(θ x - c q)`. -/
def expPhi (θ c : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) : ℝ := Real.exp (expLin θ c p)

theorem fderiv_expPhi (θ c : ℝ) :
    fderiv ℝ (expPhi θ c) = fun p => Real.exp (expLin θ c p) • expLin θ c := by
  funext p
  exact ((expLin θ c).hasFDerivAt.exp).fderiv

theorem fderiv_fderiv_expPhi (θ c : ℝ) (p v w : ℝ × (Fin (1 + 1) → ℝ)) :
    fderiv ℝ (fderiv ℝ (expPhi θ c)) p v w =
      Real.exp (expLin θ c p) * expLin θ c v * expLin θ c w := by
  rw [fderiv_expPhi]
  have h := ((expLin θ c).hasFDerivAt (x := p)).exp.smul_const (expLin θ c)
  rw [h.fderiv]
  simp [mul_assoc]

theorem measurable_expPhi (θ c : ℝ) : Measurable (expPhi θ c) :=
  (Real.continuous_exp.comp (expLin θ c).continuous).measurable

theorem contDiffOn_expPhi (θ c : ℝ) (U : Set (ℝ × (Fin (1 + 1) → ℝ))) :
    ContDiffOn ℝ 2 (expPhi θ c) U :=
  (Real.contDiff_exp.comp (expLin θ c).contDiff).contDiffOn

/-- **The Itô drift of `exp(θ x - θ²q/2)` vanishes** when `x` has drift `0` and covariance `a`
and `q` has drift `a` and no martingale part. -/
theorem itoDrift_expPhi (θ : ℝ) (y : Fin (1 + 1) → ℝ) (t : ℝ≥0) (a : ℝ) :
    itoDrift (expPhi θ (θ ^ 2 / 2)) y t
      (BlockBand.Palm.RelativeLocalization.sumVec (fun _ : Fin 1 => (0 : ℝ)) fun _ : Fin 1 => a)
      (BlockBand.Palm.RelativeLocalization.blockCov (e := 1)
        (Matrix.of fun _ _ : Fin 1 => a)) = 0 := by
  have h0 : (finSumFinEquiv.symm (0 : Fin (1 + 1))) = Sum.inl 0 := rfl
  have h1 : (finSumFinEquiv.symm (Fin.succ 0 : Fin (1 + 1))) = Sum.inr 0 := rfl
  simp only [itoDrift, partialTime, partialSpace, partialSpace2, fderiv_fderiv_expPhi]
  simp only [fderiv_expPhi, Fin.sum_univ_succ, Fin.sum_univ_zero, FunLike.coe_smul,
    Pi.smul_apply, expLin_apply, smul_eq_mul, BlockBand.Palm.RelativeLocalization.sumVec,
    BlockBand.Palm.RelativeLocalization.blockCov, Matrix.of_apply, h0, h1, Sum.elim_inl,
    Sum.elim_inr]
  simp
  ring

/-!
### The compensated coordinate and its bracket integral
-/

section Structure

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}

omit [MeasurableSpace Ω] in
theorem smCompensated_zero (Y β : ℝ≥0 → Ω → Fin d → ℝ) (i : Fin d) (ω : Ω) :
    smCompensated Y β i 0 ω = 0 := by
  simp [smCompensated]

omit [MeasurableSpace Ω] in
/-- Compensating the compensated coordinate (drift `0`) changes nothing. -/
theorem smCompensated_compensated (Y β : ℝ≥0 → Ω → Fin d → ℝ) (i : Fin d) (j : Fin 1) :
    smCompensated (fun t ω (_ : Fin 1) => smCompensated Y β i t ω) (fun _ _ _ => 0) j =
      smCompensated Y β i := by
  funext t ω
  simp [smCompensated]

/-- The constant embedding `ℝ → ℝ¹`. -/
theorem continuous_const_fin1 : Continuous fun x : ℝ => (fun _ : Fin 1 => x) :=
  continuous_pi fun _ => continuous_id

theorem isStronglyProgressive_smCompensated {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) : IsStronglyProgressive 𝓖 (smCompensated Y β i) := by
  intro t
  have h1 : StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝓖 t)]
      fun p : Set.Iic t × Ω => Y p.1 p.2 i :=
    (continuous_apply i).comp_stronglyMeasurable (hY.progressive t)
  have h0 : StronglyMeasurable[𝓖 t] fun ω => Y 0 ω i :=
    ((continuous_apply i).comp_stronglyMeasurable (hY.adapted 0)).mono (𝓖.mono (zero_le (a := t)))
  have h2 : StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝓖 t)]
      fun p : Set.Iic t × Ω => Y 0 p.2 i :=
    h0.comp_measurable measurable_snd
  have h3 := BlockBand.SourceProcess.Stochastic.Dyson.Angular.isStronglyProgressive_integral
    (𝓕 := 𝓖) (g := fun s ω => β s ω i)
    (fun u => (continuous_apply i).comp_stronglyMeasurable (hY.drift_progressive u)) t
  exact (h1.sub h2).sub h3

/-- **The compensated coordinate is a continuous semimartingale** with drift `0` and covariance
`α^{ii}`. -/
theorem isContinuousSemimartingale_compensated {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) :
    IsContinuousSemimartingale (d := 1) Q 𝓖 (fun t ω _ => smCompensated Y β i t ω)
      (fun _ _ _ => 0) (fun t ω => Matrix.of fun _ _ => α t ω i i) := by
  have hP := isStronglyProgressive_smCompensated hY i
  have hP1 : IsStronglyProgressive 𝓖 (fun t ω (_ : Fin 1) => smCompensated Y β i t ω) :=
    fun t => continuous_const_fin1.comp_stronglyMeasurable (hP t)
  have hm : Continuous fun M : Matrix (Fin d) (Fin d) ℝ =>
      (Matrix.of fun _ _ : Fin 1 => M i i) :=
    continuous_matrix fun _ _ => by simp only [Matrix.of_apply]; fun_prop
  obtain ⟨τ, hτ, hτlim, hloc⟩ := hY.localizing
  refine ⟨hP1.stronglyAdapted, hP1, ?_, isStronglyProgressive_const _ _,
    fun t => hm.comp_stronglyMeasurable (hY.cov_progressive t), ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun j => ?_, fun j k => ?_⟩⟩⟩
  · filter_upwards [hY.continuous, hY.integrable] with ω h1 h2
    exact continuous_const_fin1.comp (continuous_smCompensated h1 fun t => (h2 t).1 i)
  · filter_upwards [hY.integrable] with ω h t
    exact ⟨fun _ => integrableOn_zero, fun _ _ => by simpa using (h t).2 i i⟩
  · rw [smCompensated_compensated]
    exact (hloc n).1 i
  · rw [smCompensated_compensated, smCompensated_compensated]
    simpa only [Matrix.of_apply] using (hloc n).2 i i

/-- **The pair `(X, A)`**, `X = smCompensated Y β i`, `A = ∫_{(0,·]} α^{ii}`, is a continuous
semimartingale in `ℝ²` with drift `(0, α^{ii})` and covariance `α^{ii}` on the `X` block. -/
theorem isContinuousSemimartingale_compensated_bracket {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) :
    IsContinuousSemimartingale Q 𝓖
      (fun t ω => BlockBand.Palm.RelativeLocalization.sumVec
        (fun _ : Fin 1 => smCompensated Y β i t ω)
        (fun _ : Fin 1 => ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i))
      (fun t ω => BlockBand.Palm.RelativeLocalization.sumVec (fun _ : Fin 1 => (0 : ℝ))
        (fun _ : Fin 1 => α t ω i i))
      (fun t ω => BlockBand.Palm.RelativeLocalization.blockCov (e := 1)
        (Matrix.of fun _ _ : Fin 1 => α t ω i i)) := by
  have hαp : IsStronglyProgressive 𝓖 fun t ω => α t ω i i := fun t =>
    (continuous_id.matrix_elem i i).comp_stronglyMeasurable (hY.cov_progressive t)
  have hZp : IsStronglyProgressive 𝓖
      (fun t ω (_ : Fin 1) => ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i) := fun t =>
    continuous_const_fin1.comp_stronglyMeasurable
      (BlockBand.SourceProcess.Stochastic.Dyson.Angular.isStronglyProgressive_integral hαp t)
  refine BlockBand.Palm.RelativeLocalization.IsContinuousSemimartingale.appendFV
    (isContinuousSemimartingale_compensated hY i) hZp.stronglyAdapted hZp ?_
    (fun t => continuous_const_fin1.comp_stronglyMeasurable (hαp t)) ?_ ?_
  · filter_upwards [hY.integrable] with ω h
    exact continuous_const_fin1.comp
      (continuous_setIntegral_Ioc (g := fun u => α u ω i i) fun t => (h t).2 i i)
  · filter_upwards [hY.integrable] with ω h t _
    exact (h t).2 i i
  · exact ae_of_all _ fun ω t j => by simp [smCompensated]

end Structure

/-!
### Bounded semimartingales with nonpositive drift
-/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Nonpositive drift decreases the mean** of an a.s. bounded real continuous semimartingale
(variant of `Palm.RelativeLocalization.integral_le_of_drift_nonpos` with an a.e. bound). -/
theorem integral_le_of_drift_nonpos_ae {Y : ℝ≥0 → Ω → Fin 1 → ℝ} {β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    {C : ℝ} (hC : ∀ᵐ ω ∂Q, ∀ t, |Y t ω 0| ≤ C)
    (hβ : ∀ᵐ ω ∂Q, ∀ r : ℝ≥0, ∫ s in Set.Ioc (0 : ℝ) r, β s.toNNReal ω 0 ≤ 0) (t : ℝ≥0) :
    ∫ ω, Y t ω 0 ∂Q ≤ ∫ ω, Y 0 ω 0 ∂Q := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := hY.localizing
  have hmeasY : ∀ s, Measurable fun ω => Y s ω 0 := fun s =>
    (continuous_apply 0).measurable.comp ((hY.adapted s).mono (𝓖.le s)).measurable
  set g : ℕ → Ω → ℝ := fun n ω => stoppedProcess Y (τ n) t ω 0 - Y 0 ω 0 with hg
  have hgmeas : ∀ n, AEStronglyMeasurable (g n) Q := by
    intro n
    have h1 := hY.progressive.stronglyMeasurable_stoppedProcess (hτ n) t
    exact (((continuous_apply 0).measurable.comp h1.measurable).sub
      (hmeasY 0)).aestronglyMeasurable
  have hgbd : ∀ n, ∀ᵐ ω ∂Q, ‖g n ω‖ ≤ 2 * C := by
    intro n
    filter_upwards [hC] with ω hω
    have h1 := hω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA)
    have h2 := hω 0
    rw [Real.norm_eq_abs]
    simp only [hg, stoppedProcess]
    calc _ ≤ |Y ((min (t : WithTop ℝ≥0) (τ n ω)).untopA) ω 0| + |Y 0 ω 0| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hstep : ∀ n, ∫ ω, g n ω ∂Q ≤ 0 := by
    intro n
    obtain ⟨M, hM, hMeq⟩ := (hmart n).1 0
    have hint : ∫ ω, M t ω ∂Q = ∫ ω, M 0 ω ∂Q := by
      have := hM.setIntegral_eq (zero_le (a := t)) (MeasurableSet.univ (m := 𝓖 0))
      simpa only [Measure.restrict_univ] using this.symm
    have hM0 : M 0 =ᵐ[Q] fun _ => 0 := by
      filter_upwards [hMeq 0] with ω hω
      rw [hω]
      simp [stoppedProcess, smCompensated]
    have hint0 : ∫ ω, M t ω ∂Q = 0 := by rw [hint, integral_congr_ae hM0, integral_zero]
    have hle : ∀ᵐ ω ∂Q, g n ω ≤ M t ω := by
      filter_upwards [hMeq t, hβ] with ω hω hβω
      rw [hω]
      simp only [hg, stoppedProcess, smCompensated]
      have := hβω ((min (t : WithTop ℝ≥0) (τ n ω)).untopA)
      linarith
    have hgint : Integrable (g n) Q := Integrable.of_bound (hgmeas n) (2 * C) (hgbd n)
    calc ∫ ω, g n ω ∂Q ≤ ∫ ω, M t ω ∂Q := integral_mono_ae hgint (hM.integrable t) hle
      _ = 0 := hint0
  have hlim : ∀ᵐ ω ∂Q, Tendsto (fun n => g n ω) atTop (𝓝 (Y t ω 0 - Y 0 ω 0)) := by
    filter_upwards [hτlim] with ω hω
    have hev : ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < τ n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hg, stoppedProcess, min_eq_left hn.le]; rfl
  have hconv := tendsto_integral_of_dominated_convergence (fun _ => 2 * C) hgmeas
    (integrable_const _) hgbd hlim
  have hle0 : ∫ ω, (Y t ω 0 - Y 0 ω 0) ∂Q ≤ 0 :=
    le_of_tendsto hconv (Eventually.of_forall hstep)
  have hi : ∀ s, Integrable (fun ω => Y s ω 0) Q := fun s =>
    Integrable.of_bound (hmeasY s).aestronglyMeasurable C (by
      filter_upwards [hC] with ω hω
      rw [Real.norm_eq_abs]; exact hω s)
  rw [integral_sub (hi t) (hi 0)] at hle0
  linarith

end Expectation

/-!
### Hitting times on continuous paths
-/

section Hit

variable {Ω : Type*}

/-- On a continuous real path, a hitting time of a closed set that is `≤ T` is attained: the
path stopped at it at time `T` lies in the set. -/
theorem stopTime_hitTime_mem {F : Set ℝ} (hF : IsClosed F) {R : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hR : Continuous fun t => R t ω) {t T : ℝ≥0} (ht : t ≤ T) (hmem : R t ω ∈ F) :
    R (stopTime (hitTime F R ω) T) ω ∈ F := by
  set S := {s : ℝ≥0 | R s ω ∈ F}
  have hc : IsClosed S := hF.preimage hR
  have hS : S.Nonempty := ⟨t, hmem⟩
  have hinf := hc.csInf_mem hS ⟨0, fun _ _ => zero_le⟩
  have heq : hitTime F R ω = (sInf S : ℝ≥0) := le_antisymm (iInf₂_le _ hinf)
    (le_iInf₂ fun s hs => WithTop.coe_le_coe.2 (csInf_le ⟨0, fun _ _ => zero_le⟩ hs))
  have hle : sInf S ≤ T := (csInf_le ⟨0, fun _ _ => zero_le⟩ (show t ∈ S from hmem)).trans ht
  rw [heq, stopTime_coe, min_eq_right hle]
  exact hinf

end Hit

/-!
### The exponential maximal inequality
-/

section Tail

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}

/-- **Maximal inequality for the exponential process** `exp(θ X_t - θ²/2 A_t)`, with
`X = smCompensated Y β i` and `A = ∫_{(0,·]} α^{ii}`: for every `θ ∈ ℝ` and `L > 0`,
`Q(∃ t ≤ T, L ≤ exp(θ X_t - θ²/2 A_t)) ≤ 1/L`. -/
theorem measure_exists_le_expMart_le {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) (θ : ℝ) (T : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    Q {ω | ∃ t ≤ T, L ≤ Real.exp (θ * smCompensated Y β i t ω -
        θ ^ 2 / 2 * ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i)} ≤ ENNReal.ofReal (1 / L) := by
  rcases lt_or_ge L 1 with hL1 | hL1
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hL]; linarith)
  -- the joint state and Itô's formula
  have hW := isContinuousSemimartingale_compensated_bracket hY i
  have hZ0 := BlockBand.SourceProcess.Stochastic.SemimartingaleIto.semimartingaleItoFormula_holds
    (1 + 1) Ω Q 𝓖 _ _ _ hW univ isOpen_univ (ae_of_all _ fun _ _ => mem_univ _)
    (expPhi θ (θ ^ 2 / 2)) (measurable_expPhi _ _) (contDiffOn_expPhi _ _ _)
  have hdrift : (fun t ω (_ : Fin 1) => itoDrift (expPhi θ (θ ^ 2 / 2))
      (BlockBand.Palm.RelativeLocalization.sumVec (fun _ : Fin 1 => smCompensated Y β i t ω)
        (fun _ : Fin 1 => ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i)) t
      (BlockBand.Palm.RelativeLocalization.sumVec (fun _ : Fin 1 => (0 : ℝ))
        (fun _ : Fin 1 => α t ω i i))
      (BlockBand.Palm.RelativeLocalization.blockCov (e := 1)
        (Matrix.of fun _ _ : Fin 1 => α t ω i i))) = fun _ _ _ => 0 := by
    funext t ω _
    exact itoDrift_expPhi θ _ t _
  rw [hdrift] at hZ0
  set Z : ℝ≥0 → Ω → Fin 1 → ℝ := fun t ω _ => expPhi θ (θ ^ 2 / 2) ((t : ℝ),
    BlockBand.Palm.RelativeLocalization.sumVec (fun _ : Fin 1 => smCompensated Y β i t ω)
      (fun _ : Fin 1 => ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i)) with hZdef
  set R : ℝ≥0 → Ω → ℝ := fun t ω => Z t ω 0 with hRdef
  have hReq : ∀ t ω, R t ω = Real.exp (θ * smCompensated Y β i t ω -
      θ ^ 2 / 2 * ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i) := fun t ω => by
    simp only [hRdef, hZdef, expPhi, expLin_apply]; rfl
  have hR0 : ∀ ω, R 0 ω = 1 := fun ω => by
    rw [hReq, smCompensated_zero]; simp
  have hRpos : ∀ t ω, 0 < R t ω := fun t ω => by rw [hReq]; exact Real.exp_pos _
  have hRad : ∀ t, Measurable[𝓖 t] (R t) := fun t =>
    (continuous_apply 0).measurable.comp (hZ0.adapted t).measurable
  have hRc : ∀ᵐ ω ∂Q, Continuous fun t => R t ω := by
    filter_upwards [hZ0.continuous] with ω hω
    exact (continuous_apply 0).comp hω
  -- stopping at the hitting time of `[L, ∞)`
  set ρ : Ω → WithTop ℝ≥0 := rawHit (Ici L) R with hρdef
  have hρ : IsStoppingTime 𝓖 ρ := isStoppingTime_rawHit hRad
  have hS := BlockBand.SourceProcess.Stochastic.Semimartingale.stoppedSemimartingale_holds 1
    Ω Q 𝓖 _ _ _ hZ0 ρ hρ
  have hbd : ∀ᵐ ω ∂Q, ∀ t, |stoppedProcess Z ρ t ω 0| ≤ L := by
    filter_upwards [hRc] with ω hω t
    have hρω : ρ ω = hitTime (Ici L) R ω := rawHit_eq_hitTime isClosed_Ici hω
    have hle : R (stopTime (ρ ω) t) ω ≤ L :=
      BlockBand.SourceProcess.Stochastic.SemimartingaleIto.le_of_le_hitTime_Ici hω
        (by rw [hR0]; exact hL1) (hρω ▸ stopTime_le_self (ρ ω) t)
    rw [stoppedProcess_eq_stopTime, abs_of_pos (hRpos _ _)]
    exact hle
  have hdr : ∀ᵐ ω ∂Q, ∀ r : ℝ≥0,
      ∫ s in Set.Ioc (0 : ℝ) r,
        switchAfter ρ (fun _ _ (_ : Fin 1) => (0 : ℝ)) s.toNNReal ω 0 ≤ 0 := by
    refine ae_of_all _ fun ω r => le_of_eq ?_
    have e : ∀ s : ℝ, switchAfter ρ (fun _ _ (_ : Fin 1) => (0 : ℝ)) s.toNNReal ω 0 = 0 :=
      fun s => by unfold switchAfter; split_ifs <;> rfl
    simp only [e, integral_zero]
  have hE := integral_le_of_drift_nonpos_ae hS hbd hdr T
  set f : Ω → ℝ := fun ω => stoppedProcess Z ρ T ω 0 with hfdef
  have hE1 : ∫ ω, f ω ∂Q ≤ 1 := by
    refine hE.trans (le_of_eq ?_)
    have e : (fun ω => stoppedProcess Z ρ 0 ω 0) = fun _ => (1 : ℝ) := by
      funext ω
      rw [stoppedProcess_eq_stopTime, le_antisymm (stopTime_le _ _) zero_le]
      exact hR0 ω
    rw [e]; simp
  have hfmeas : AEStronglyMeasurable f Q :=
    ((continuous_apply 0).measurable.comp
      ((hS.adapted T).mono (𝓖.le T)).measurable).aestronglyMeasurable
  have hfint : Integrable f Q := Integrable.of_bound hfmeas L (by
    filter_upwards [hbd] with ω hω
    rw [Real.norm_eq_abs]; exact hω T)
  have hfnn : 0 ≤ᵐ[Q] f := ae_of_all _ fun ω => (hRpos _ _).le
  -- the event is contained in `{L ≤ f}` a.s.
  have hsub : {ω | ∃ t ≤ T, L ≤ Real.exp (θ * smCompensated Y β i t ω -
      θ ^ 2 / 2 * ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i)} ≤ᵐ[Q] {ω | L ≤ f ω} := by
    filter_upwards [hRc] with ω hω hmem
    obtain ⟨t, htT, ht⟩ := hmem
    have hρω : ρ ω = hitTime (Ici L) R ω := rawHit_eq_hitTime isClosed_Ici hω
    have := stopTime_hitTime_mem isClosed_Ici hω htT (show R t ω ∈ Ici L by rw [hReq]; exact ht)
    show L ≤ stoppedProcess Z ρ T ω 0
    rw [stoppedProcess_eq_stopTime, hρω]
    exact this
  have hM := mul_meas_ge_le_integral_of_nonneg hfnn hfint L
  have hreal : Q.real {ω | L ≤ f ω} ≤ 1 / L := by
    rw [le_div_iff₀ hL, mul_comm]; linarith
  calc _ ≤ Q {ω | L ≤ f ω} := measure_mono_ae hsub
    _ = ENNReal.ofReal (Q.real {ω | L ≤ f ω}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (1 / L) := ENNReal.ofReal_le_ofReal hreal

/-- The exponent `θ a - θ²/2 b` at `θ = a/b` is `a²/(2b)`. -/
theorem freedman_exponent {a b : ℝ} (hb : 0 < b) :
    a / b * a - (a / b) ^ 2 / 2 * b = a ^ 2 / (2 * b) := by
  field_simp
  ring

theorem one_div_exp_freedman (a b : ℝ) :
    1 / Real.exp (a ^ 2 / (2 * b)) = Real.exp (-(a ^ 2) / (2 * b)) := by
  rw [neg_div, Real.exp_neg, one_div]

/-- **Exponential (Freedman) upper tail**, coordinate form: for `a, b > 0`,
`Q(∃ t ≤ T, a ≤ X_t ∧ A_t ≤ b) ≤ exp(-a²/(2b))`. -/
theorem measure_compensated_ge_le_coord {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) (T : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q {ω | ∃ t ≤ T, a ≤ smCompensated Y β i t ω ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω i i ≤ b} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * b))) := by
  have hθ : 0 ≤ a / b := (div_pos ha hb).le
  refine le_trans (measure_mono fun ω hω => ?_)
    ((measure_exists_le_expMart_le hY i (a / b) T (Real.exp_pos (a ^ 2 / (2 * b)))).trans
      (le_of_eq (by rw [one_div_exp_freedman])))
  obtain ⟨t, htT, h1, h2⟩ := hω
  refine ⟨t, htT, Real.exp_le_exp.2 ?_⟩
  rw [← freedman_exponent hb]
  have := mul_le_mul_of_nonneg_left h1 hθ
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (a / b) ^ 2 / 2)
  linarith

/-- **Exponential (Freedman) lower tail**, coordinate form: for `a, b > 0`,
`Q(∃ t ≤ T, X_t ≤ -a ∧ A_t ≤ b) ≤ exp(-a²/(2b))`. -/
theorem measure_compensated_le_neg_le_coord {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) (T : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q {ω | ∃ t ≤ T, smCompensated Y β i t ω ≤ -a ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω i i ≤ b} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * b))) := by
  have hθ : 0 ≤ a / b := (div_pos ha hb).le
  refine le_trans (measure_mono fun ω hω => ?_)
    ((measure_exists_le_expMart_le hY i (-(a / b)) T (Real.exp_pos (a ^ 2 / (2 * b)))).trans
      (le_of_eq (by rw [one_div_exp_freedman])))
  obtain ⟨t, htT, h1, h2⟩ := hω
  refine ⟨t, htT, Real.exp_le_exp.2 ?_⟩
  rw [← freedman_exponent hb]
  have := mul_le_mul_of_nonneg_left (show a ≤ -smCompensated Y β i t ω by linarith) hθ
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (a / b) ^ 2 / 2)
  have e : (-(a / b)) ^ 2 = (a / b) ^ 2 := neg_sq _
  rw [e]
  linarith

/-- **Two-sided exponential (Freedman) tail**, coordinate form: for `a, b > 0`,
`Q(∃ t ≤ T, a ≤ |X_t| ∧ A_t ≤ b) ≤ 2 exp(-a²/(2b))`. -/
theorem measure_abs_compensated_ge_le_coord {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) (T : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q {ω | ∃ t ≤ T, a ≤ |smCompensated Y β i t ω| ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω i i ≤ b} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) := by
  have hsub : {ω | ∃ t ≤ T, a ≤ |smCompensated Y β i t ω| ∧
      ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω i i ≤ b} ⊆
      {ω | ∃ t ≤ T, a ≤ smCompensated Y β i t ω ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω i i ≤ b} ∪
      {ω | ∃ t ≤ T, smCompensated Y β i t ω ≤ -a ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω i i ≤ b} := by
    rintro ω ⟨t, htT, h1, h2⟩
    rcases le_abs'.1 h1 with h | h
    · exact Or.inr ⟨t, htT, h, h2⟩
    · exact Or.inl ⟨t, htT, h, h2⟩
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * b))) +
        ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * b))) :=
      add_le_add (measure_compensated_ge_le_coord hY i T ha hb)
        (measure_compensated_le_neg_le_coord hY i T ha hb)
    _ = ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring

/-- **Exponential (Freedman) tail for the martingale part of a real continuous
semimartingale**: with `X_t = Y_t - Y_0 - ∫_{(0,t]} β` and `A_t = ∫_{(0,t]} α`, for `a, b > 0`,
`Q(∃ t ≤ T, a ≤ X_t ∧ A_t ≤ b) ≤ exp(-a²/(2b))`. -/
theorem measure_compensated_ge_le {Y : ℝ≥0 → Ω → Fin 1 → ℝ} {β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (T : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q {ω | ∃ t ≤ T, a ≤ smCompensated Y β 0 t ω ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω 0 0 ≤ b} ≤
      ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * b))) :=
  measure_compensated_ge_le_coord hY 0 T ha hb

/-- **Two-sided exponential (Freedman) tail** for a real continuous semimartingale:
`Q(∃ t ≤ T, a ≤ |X_t| ∧ A_t ≤ b) ≤ 2 exp(-a²/(2b))`. -/
theorem measure_abs_compensated_ge_le {Y : ℝ≥0 → Ω → Fin 1 → ℝ} {β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    (T : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Q {ω | ∃ t ≤ T, a ≤ |smCompensated Y β 0 t ω| ∧
        ∫ s in Set.Ioc 0 (t : ℝ), α s.toNNReal ω 0 0 ≤ b} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * b))) :=
  measure_abs_compensated_ge_le_coord hY 0 T ha hb

end Tail

end BlockBand.Native.CEH.Martingale
