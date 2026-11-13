module

public import BlockBand.Native.ErdosRiabov.Stochastic.ExpTail
public import BlockBand.SourceProcess.Stochastic.Levy.BrownianIntegrator
public import BlockBand.SourceProcess.Stochastic.Bridges.Structural
public import BlockBand.SourceProcess.Stochastic.Integral.Family
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.ItoNative.Core
public import BlockBand.Model.Construction.GaussianCompatibility

set_option autoImplicit false

/-!
# The band Ornstein–Uhlenbeck flow of the Gaussian ring

## Construction (no SDE well-posedness is used)

* `driverNoise v = diag(√v) B`, a continuous semimartingale with characteristics
  `(0, diag v)` (Lévy martingale facts `martingale_coord`/`martingale_cross` and
  `IsContinuousSemimartingale.affine`). Coordinates with `v i = 0` are allowed.
* `ouProcess ξ Y`: the **Mehler / variation-of-constants form after integration by parts**,
  pathwise for every sample,
  `X^i_t = e^{-t/2} ξ^i + (Y^i_t - Y^i_0) - ½ e^{-t/2} ∫_0^t e^{s/2} (Y^i_s - Y^i_0) ds`,
  which is `e^{-t/2}(ξ + ∫_0^t e^{s/2} dY_s)` written without a stochastic integral.
  The deterministic identity `ouPath_sub_add_integral` (fundamental theorem of calculus) gives
  `X_t - X_0 + ½ ∫_0^t X_s ds = Y_t - Y_0` on every continuous path, so the martingale parts of
  `X` (with drift `-½X`) and of `Y` (with drift `0`) coincide pathwise.

## The Gaussian ring (main results)

Real coordinates: `p.GaussianCoordinate ≃ Fin (ringDim p)` (`ringEquiv`), variances
`ringVariance` (`gaussianCoordinateVariance`, zero for the redundant labels), coordinates of a
matrix `ringCoords` (`gaussianExtraction`), matrix of coordinates `ringMatrix`
(`gaussianReconstruction`, Hermitian for every argument). With `μ = model.law`:

* `ringOU p t x = ouProcess (ringCoords ∘ fst) (driverNoise ringVariance)` and
  `ringOUMatrix p t x = ringMatrix (ringOU p t x)`, the matrix OU flow, which solves
  `dH = -½ H dt + Σ^{1/2} dB` in the real coordinates `ringCoords` (formally:
  `isContinuousSemimartingale_ringOU`), `H_0 = x.1 ~ model.law` (`ringOUMatrix_zero_ae`),
  independent of `B`. Linearity of `ringMatrix`/`ringCoords`, the inverse identity on the
  subspace where the redundant coordinates vanish, and the matrix-level Mehler form are
  `ringCoords_ringMatrix` and `ringOUMatrix_eq_mehler`.
* **`isContinuousSemimartingale_ringOU`**: `ringOU` is a continuous semimartingale for
  `(driverLaw model.law, driverAugmented model.law)` with drift `-½ ringOU` and constant
  covariance `diag(ringVariance)`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Levy
open scoped NNReal ENNReal Matrix

/-!
### The deterministic Ornstein–Uhlenbeck path functional
-/

/-- **Pathwise Mehler functional** (integrated-by-parts variation of constants):
`ouPath h₀ y t = e^{-t/2} h₀ + y t - ½ e^{-t/2} ∫_0^t e^{s/2} y s ds`. For `y = Y - Y_0` it is
`e^{-t/2}(h₀ + ∫_0^t e^{s/2} dY_s)`. -/
def ouPath (h₀ : ℝ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t / 2) * h₀ + y t -
    1 / 2 * Real.exp (-t / 2) * ∫ s in (0 : ℝ)..t, Real.exp (s / 2) * y s

theorem continuous_ouIntegrand {y : ℝ → ℝ} (hy : Continuous y) :
    Continuous fun s : ℝ => Real.exp (s / 2) * y s :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).mul hy

theorem hasDerivAt_ouPrimitive {y : ℝ → ℝ} (hy : Continuous y) (s : ℝ) :
    HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, Real.exp (r / 2) * y r) (Real.exp (s / 2) * y s) s :=
  ((continuous_ouIntegrand hy).integral_hasStrictDerivAt 0 s).hasDerivAt

theorem continuous_ouPath (h₀ : ℝ) {y : ℝ → ℝ} (hy : Continuous y) : Continuous (ouPath h₀ y) := by
  have hI : Continuous fun u => ∫ r in (0 : ℝ)..u, Real.exp (r / 2) * y r :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_ouPrimitive hy s).continuousAt
  have hE : Continuous fun t : ℝ => Real.exp (-t / 2) :=
    Real.continuous_exp.comp (continuous_neg.div_const 2)
  exact ((hE.mul continuous_const).add hy).sub ((continuous_const.mul hE).mul hI)

/-- **The pathwise Langevin identity.** For a continuous driving path `y` and every `t`,
`ouPath h₀ y t - h₀ + ½ ∫_0^t ouPath h₀ y s ds = y t`; i.e. `x = ouPath h₀ y` solves
`x_t = h₀ - ½ ∫_0^t x_s ds + y_t` (when `y 0 = 0`). Proof: `F(s) = -2h₀ e^{-s/2} +
e^{-s/2} ∫_0^s e^{r/2} y` is a primitive of `ouPath h₀ y`. -/
theorem ouPath_sub_add_integral (h₀ : ℝ) {y : ℝ → ℝ} (hy : Continuous y) (t : ℝ) :
    ouPath h₀ y t - h₀ + 1 / 2 * ∫ s in (0 : ℝ)..t, ouPath h₀ y s = y t := by
  have hE : ∀ s : ℝ, HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
      (Real.exp (-s / 2) * (-1 / 2)) s := fun s => ((hasDerivAt_neg s).div_const 2).exp
  have hF : ∀ s : ℝ, HasDerivAt (fun x : ℝ => -2 * h₀ * Real.exp (-x / 2) +
      Real.exp (-x / 2) * ∫ r in (0 : ℝ)..x, Real.exp (r / 2) * y r) (ouPath h₀ y s) s := by
    intro s
    have h := ((hE s).const_mul (-2 * h₀)).add ((hE s).mul (hasDerivAt_ouPrimitive hy s))
    convert h using 1
    have hexp : Real.exp (-s / 2) * Real.exp (s / 2) = 1 := by
      rw [← Real.exp_add, show -s / 2 + s / 2 = 0 by ring, Real.exp_zero]
    simp only [ouPath]
    linear_combination (-(y s)) * hexp
  have hint : IntervalIntegrable (ouPath h₀ y) volume 0 t :=
    (continuous_ouPath h₀ hy).intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s) hint]
  simp only [ouPath, intervalIntegral.integral_same, neg_zero, zero_div, Real.exp_zero]
  ring

/-!
### The Ornstein–Uhlenbeck process driven by a continuous semimartingale
-/

variable {Ω : Type*} {d : ℕ}

/-- The driving path of coordinate `i` on `ℝ`: `s ↦ Y^i_{s⁺} - Y^i_0`. -/
def ouDrive (Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) (i : Fin d) (s : ℝ) : ℝ :=
  Y s.toNNReal ω i - Y 0 ω i

/-- **The Ornstein–Uhlenbeck process** with initial value `ξ` driven by `Y` (pathwise Mehler
form): `X^i_t = e^{-t/2} ξ^i + (Y^i_t - Y^i_0) - ½ e^{-t/2} ∫_0^t e^{s/2} (Y^i_s - Y^i_0) ds`. -/
def ouProcess (ξ : Ω → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) : Fin d → ℝ :=
  fun i => ouPath (ξ ω i) (ouDrive Y ω i) t

theorem ouProcess_zero (ξ : Ω → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) :
    ouProcess ξ Y 0 ω = ξ ω := by
  funext i
  simp [ouProcess, ouPath, ouDrive]

theorem continuous_ouDrive {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hω : Continuous fun t => Y t ω)
    (i : Fin d) : Continuous (ouDrive Y ω i) :=
  ((continuous_apply i).comp (hω.comp continuous_real_toNNReal)).sub continuous_const

theorem continuous_ouProcess {ξ : Ω → Fin d → ℝ} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hω : Continuous fun t => Y t ω) : Continuous fun t => ouProcess ξ Y t ω :=
  continuous_pi fun i => (continuous_ouPath _ (continuous_ouDrive hω i)).comp NNReal.continuous_coe

/-- The coordinate of `ouProcess` with the Bochner integral over `(0, t]` in the form used by
`isStronglyProgressive_integral`. -/
theorem ouProcess_apply_eq (ξ : Ω → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω)
    (i : Fin d) :
    ouProcess ξ Y t ω i = Real.exp (-(t : ℝ) / 2) * ξ ω i + (Y t ω i - Y 0 ω i) -
      1 / 2 * Real.exp (-(t : ℝ) / 2) * ∫ s in Ioc (0 : ℝ) t,
        Real.exp ((s.toNNReal : ℝ) / 2) * (Y s.toNNReal ω i - Y 0 ω i) := by
  simp only [ouProcess, ouPath, ouDrive, Real.toNNReal_coe]
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  simp only [Real.coe_toNNReal _ hs.1.le]

/-- **Pathwise identification of the martingale parts.** On a continuous path of `Y`, the
compensated coordinates of `ouProcess ξ Y` for the drift `-½ ouProcess` equal those of `Y` for
the drift `0`. -/
theorem smCompensated_ouProcess {ξ : Ω → Fin d → ℝ} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hω : Continuous fun t => Y t ω) (i : Fin d) (t : ℝ≥0) :
    smCompensated (ouProcess ξ Y) (fun t ω => (-(1 / 2 : ℝ)) • ouProcess ξ Y t ω) i t ω =
      smCompensated Y (fun _ _ => 0) i t ω := by
  have key := ouPath_sub_add_integral (ξ ω i) (continuous_ouDrive hω i) t
  have hI : ∫ s in Ioc (0 : ℝ) t, ((-(1 / 2 : ℝ)) • ouProcess ξ Y s.toNNReal ω) i =
      -(1 / 2) * ∫ s in (0 : ℝ)..t, ouPath (ξ ω i) (ouDrive Y ω i) s := by
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ouProcess, Real.coe_toNNReal _ hs.1.le]
  have hyt : ouDrive Y ω i t = Y t ω i - Y 0 ω i := by simp [ouDrive]
  have h0 : ouProcess ξ Y 0 ω i = ξ ω i := congrFun (ouProcess_zero ξ Y ω) i
  have ht : ouProcess ξ Y t ω i = ouPath (ξ ω i) (ouDrive Y ω i) t := rfl
  simp only [smCompensated]
  rw [hI, h0, ht]
  simp only [Pi.zero_apply, integral_zero, sub_zero]
  linarith

/-- The OU process is strongly progressive when `ξ` is `𝓖_0`-measurable and `Y` is strongly
progressive. -/
theorem isStronglyProgressive_ouProcess {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀}
    {ξ : Ω → Fin d → ℝ} {Y : ℝ≥0 → Ω → Fin d → ℝ} (hξ : StronglyMeasurable[𝓖 0] ξ)
    (hY : IsStronglyProgressive 𝓖 Y) : IsStronglyProgressive 𝓖 (ouProcess ξ Y) := by
  refine isStronglyProgressive_pi_fin fun i => ?_
  have hYc : IsStronglyProgressive 𝓖 fun t ω => Y t ω i := fun s =>
    (continuous_apply i).comp_stronglyMeasurable (hY s)
  have hY0 : IsStronglyProgressive 𝓖 fun (_ : ℝ≥0) ω => Y 0 ω i :=
    isStronglyProgressive_initial ((continuous_apply i).comp_stronglyMeasurable
      (hY.stronglyAdapted 0))
  have hYi : IsStronglyProgressive 𝓖 fun t ω => Y t ω i - Y 0 ω i := hYc.sub hY0
  have hf : IsStronglyProgressive 𝓖
      fun (r : ℝ≥0) ω => Real.exp ((r : ℝ) / 2) * (Y r ω i - Y 0 ω i) :=
    ItoNative.isStronglyProgressive_timeComp hYi (Φ := fun q : ℝ × ℝ => Real.exp (q.1 / 2) * q.2)
      (by fun_prop)
  have hint := isStronglyProgressive_integral hf
  have hξi : IsStronglyProgressive 𝓖 fun (_ : ℝ≥0) ω => ξ ω i :=
    isStronglyProgressive_initial ((continuous_apply i).comp_stronglyMeasurable hξ)
  have htriple : IsStronglyProgressive 𝓖 fun (t : ℝ≥0) ω => (ξ ω i, Y t ω i - Y 0 ω i,
      ∫ s in Ioc (0 : ℝ) t, Real.exp ((s.toNNReal : ℝ) / 2) * (Y s.toNNReal ω i - Y 0 ω i)) :=
    fun s => (hξi s).prodMk ((hYi s).prodMk (hint s))
  have hall := ItoNative.isStronglyProgressive_timeComp htriple
    (Φ := fun q : ℝ × (ℝ × ℝ × ℝ) =>
      Real.exp (-q.1 / 2) * q.2.1 + q.2.2.1 - 1 / 2 * Real.exp (-q.1 / 2) * q.2.2.2)
    (by fun_prop)
  have e : (fun t ω => ouProcess ξ Y t ω i) = fun (t : ℝ≥0) ω =>
      Real.exp (-(t : ℝ) / 2) * ξ ω i + (Y t ω i - Y 0 ω i) -
        1 / 2 * Real.exp (-(t : ℝ) / 2) * ∫ s in Ioc (0 : ℝ) t,
          Real.exp ((s.toNNReal : ℝ) / 2) * (Y s.toNNReal ω i - Y 0 ω i) := by
    funext t ω
    exact ouProcess_apply_eq ξ Y t ω i
  rw [e]
  exact hall

variable [MeasurableSpace Ω]

/-- **General form: the OU process driven by a continuous martingale is a continuous
semimartingale.** On any filtered probability space `(Ω, 𝓖, Q)` (raw filtration), if `Y` is a
continuous semimartingale in `ℝ^d` with characteristics `(0, α)` and `ξ` is `𝓖_0`-measurable,
then `X = ouProcess ξ Y` (pathwise Mehler form, `X_0 = ξ`) is a continuous semimartingale with
drift `-½ X` and the same covariance density `α`, with the localizing sequence of `Y`: the
compensated coordinates of `X` and `Y` agree on every continuous path of `Y`
(`smCompensated_ouProcess`). -/
theorem isContinuousSemimartingale_ouProcess {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} {ξ : Ω → Fin d → ℝ}
    (hY : IsContinuousSemimartingale Q 𝓖 Y (fun _ _ => 0) α) (hξ : StronglyMeasurable[𝓖 0] ξ) :
    IsContinuousSemimartingale Q 𝓖 (ouProcess ξ Y)
      (fun t ω => (-(1 / 2 : ℝ)) • ouProcess ξ Y t ω) α := by
  have hprog := isStronglyProgressive_ouProcess hξ hY.progressive
  obtain ⟨τ, hτ, hτlim, hm⟩ := hY.localizing
  have hcomp : ∀ᵐ ω ∂Q, ∀ i t, smCompensated (ouProcess ξ Y)
      (fun t ω => (-(1 / 2 : ℝ)) • ouProcess ξ Y t ω) i t ω =
        smCompensated Y (fun _ _ => 0) i t ω := by
    filter_upwards [hY.continuous] with ω hω i t
    exact smCompensated_ouProcess hω i t
  refine ⟨hprog.stronglyAdapted, hprog, ?_,
    fun s => (continuous_const_smul (-(1 / 2 : ℝ))).comp_stronglyMeasurable (hprog s),
    hY.cov_progressive,
    ?_, ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [hY.continuous] with ω hω
    exact continuous_ouProcess hω
  · filter_upwards [hY.continuous, hY.integrable] with ω hω hi t
    refine ⟨fun i => ?_, (hi t).2⟩
    have hc : Continuous fun s : ℝ => ((-(1 / 2 : ℝ)) • ouProcess ξ Y s.toNNReal ω) i :=
      (continuous_apply i).comp ((continuous_const_smul (-(1 / 2 : ℝ))).comp
        ((continuous_ouProcess (ξ := ξ) hω).comp continuous_real_toNNReal))
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · refine hasMartingaleModification_congr ((hm n).1 i) fun t => ?_
    filter_upwards [hcomp] with ω hω
    simp only [stoppedProcess_eq_stopTime, hω]
  · refine hasMartingaleModification_congr ((hm n).2 i j) fun t => ?_
    filter_upwards [hcomp] with ω hω
    simp only [stoppedProcess_eq_stopTime, hω]

/-- Rewriting the three data of a continuous semimartingale along equalities. -/
theorem isContinuousSemimartingale_congr_data {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Y Y' β β' : ℝ≥0 → Ω → Fin d → ℝ}
    {α α' : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (h : IsContinuousSemimartingale Q 𝓖 Y β α)
    (hY : Y = Y') (hβ : β = β') (hα : α = α') : IsContinuousSemimartingale Q 𝓖 Y' β' α' := by
  subst hY hβ hα
  exact h

/-!
### The Brownian driver on the driver space
-/

section Driver

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- Independence from the raw driver σ-algebra `F_s` transfers to its null augmentation
`F_s ∨ N` (every augmented set is a.e. equal to a raw one, `exists_raw_ae_eq`). -/
theorem indep_driverAugmented_of_raw {κ : Type*} [Fintype κ]
    {m₁ : MeasurableSpace (DriverSample S κ)} {s : ℝ≥0}
    (h : Indep m₁ (commonWienerFiltration S κ s) (driverLaw (κ := κ) μ)) :
    Indep m₁ (driverAugmented (κ := κ) μ s) (driverLaw (κ := κ) μ) := by
  rw [Indep_iff] at h ⊢
  intro A C hA hC
  obtain ⟨C', hC', hCC'⟩ := Integral.exists_raw_ae_eq μ hC
  rw [measure_congr (ae_eq_set_inter (ae_eq_refl A) hCC'), measure_congr hCC']
  exact h A C' hA hC'

/-- The coordinate Brownian motion `B_t(x) = (x.2 i t)_i` of the driver space. -/
def driverBrownian (S : Type*) (d : ℕ) (t : ℝ≥0) (x : DriverSample S (Fin d)) : Fin d → ℝ :=
  fun i => x.2 i t

/-- **The driver is a Brownian motion for the augmented filtration.** Under `driverLaw μ`
(arbitrary initial law `μ`), `B` is adapted to `driverAugmented μ = F_t ∨ N`, starts at `0`
a.s., has everywhere continuous paths, and `B_t - B_s` is independent of `F_s ∨ N` with law
`N(0, (t - s) I_d)`. In particular `B` is independent of the initial state `x.1`, which is
`F_0`-measurable. -/
theorem isFiltrationBrownian_driverBrownian (d : ℕ) :
    IsFiltrationBrownian (driverLaw (κ := Fin d) μ) (driverAugmented (κ := Fin d) μ)
      (driverBrownian S d) := by
  refine ⟨fun t => ?_, ae_of_all _ fun x => continuous_pi fun i => (x.2 i).continuous, ?_,
    fun s t hst => ?_, fun s t hst => ?_⟩
  · exact ((commonRealBrownian_adapted (S := S) (κ := Fin d) t).mono
      (le_augmentedFiltration _ _ t) le_rfl).stronglyMeasurable
  · have h : ∀ i : Fin d, ∀ᵐ x ∂driverLaw (κ := Fin d) μ, x.2 i 0 = 0 := fun i =>
      (commonRealBrownian_isBrownian (κ := Fin d) μ i).toIsPreBrownianReal.eval_zero_ae_eq_zero
    filter_upwards [ae_all_iff.2 h] with x hx
    funext i
    exact hx i
  · apply indep_driverAugmented_of_raw μ
    have hind := (IndepFun_iff_Indep _ _ _).1
      (commonWienerFuture_independent_old_past (κ := Fin d) μ s)
    refine indep_of_indep_of_le_left hind ?_
    have e : (fun x => driverBrownian S d t x - driverBrownian S d s x) =
        (fun z : Fin d → ℝ≥0 → ℝ => fun a => z a (t - s)) ∘
          (fun x : DriverSample S (Fin d) => commonWienerFuture s x.2) := by
      funext x a
      simp [driverBrownian, commonWienerFuture, add_tsub_cancel_of_le hst]
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_eval fun a =>
      (measurable_pi_apply (t - s)).comp (measurable_pi_apply a)).comap_le
  · have h := hasLaw_commonRealBrownian_increment (κ := Fin d) μ s t
    have hn : nndist t s = t - s := by
      rw [NNReal.nndist_eq, tsub_eq_zero_of_le hst, max_eq_left zero_le]
    rw [hn] at h
    exact h

/-- The driver is a continuous semimartingale with characteristics `(0, I)` (from the Lévy
martingale facts of the Brownian integrator).
-/
theorem isContinuousSemimartingale_driverBrownian (d : ℕ) :
    IsContinuousSemimartingale (driverLaw (κ := Fin d) μ) (driverAugmented (κ := Fin d) μ)
      (driverBrownian S d) (fun _ _ => 0) (fun _ _ => 1) := by
  have hB := isFiltrationBrownian_driverBrownian μ d
  exact (IsLevyMartingale.of_forall_continuous hB.adapted
    (fun x => continuous_pi fun i => (x.2 i).continuous) hB.zero
    (fun i => ⟨_, hB.martingale_coord i, fun _ => ae_of_all _ fun _ => rfl⟩)
    (fun i j => ⟨_, hB.martingale_cross i j, fun _ => ae_of_all _ fun _ =>
      rfl⟩)).isContinuousSemimartingale

/-- The band noise `Y = diag(√v) B`: coordinate `i` is `√(v i)` times the `i`-th driver. -/
def driverNoise (v : Fin d → ℝ) (t : ℝ≥0) (x : DriverSample S (Fin d)) : Fin d → ℝ :=
  fun i => Real.sqrt (v i) * x.2 i t

/-- The band noise is a continuous semimartingale with characteristics `(0, diag v)`; zero
variances are allowed. -/
theorem isContinuousSemimartingale_driverNoise {v : Fin d → ℝ} (hv : ∀ i, 0 ≤ v i) :
    IsContinuousSemimartingale (driverLaw (κ := Fin d) μ) (driverAugmented (κ := Fin d) μ)
      (driverNoise (S := S) v) (fun _ _ => 0) (fun _ _ => Matrix.diagonal v) := by
  refine isContinuousSemimartingale_congr_data
    ((isContinuousSemimartingale_driverBrownian μ d).affine
      (Matrix.diagonal fun i => Real.sqrt (v i)) 0) ?_ ?_ ?_
  · funext t x i
    simp [driverNoise, driverBrownian, Matrix.mulVec_diagonal]
  · funext t x
    simp
  · funext t x
    rw [Matrix.mul_one, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hv i)

omit [IsProbabilityMeasure μ] in
/-- A functional `ξ(x.1)` of the initial state is `F_0 ∨ N`-measurable. -/
theorem stronglyMeasurable_oldState {ξ : S → Fin d → ℝ} (hξ : Measurable ξ) :
    StronglyMeasurable[driverAugmented (κ := Fin d) μ 0]
      fun x : DriverSample S (Fin d) => ξ x.1 := by
  have h : Measurable[commonWienerFiltration S (Fin d) 0] fun x : DriverSample S (Fin d) => x.1 :=
    (comap_measurable (fun x : DriverSample S (Fin d) => (x.1, commonWienerPast 0 x.2))).fst
  exact ((hξ.comp h).mono (le_augmentedFiltration _ _ 0) le_rfl).stronglyMeasurable

/-- The OU flow on the driver space: initial value `ξ(x.1)`, noise `diag(√v) B`. -/
def driverOU (ξ : S → Fin d → ℝ) (v : Fin d → ℝ) :
    ℝ≥0 → DriverSample S (Fin d) → Fin d → ℝ :=
  ouProcess (fun x => ξ x.1) (driverNoise v)

/-- **The OU flow on the driver space is a continuous semimartingale** with drift `-½X` and
constant covariance `diag v`, for `(driverLaw μ, driverAugmented μ)`. -/
theorem isContinuousSemimartingale_driverOU {ξ : S → Fin d → ℝ} (hξ : Measurable ξ)
    {v : Fin d → ℝ} (hv : ∀ i, 0 ≤ v i) :
    IsContinuousSemimartingale (driverLaw (κ := Fin d) μ) (driverAugmented (κ := Fin d) μ)
      (driverOU ξ v) (fun t x => (-(1 / 2 : ℝ)) • driverOU ξ v t x)
      (fun _ _ => Matrix.diagonal v) :=
  isContinuousSemimartingale_ouProcess (isContinuousSemimartingale_driverNoise μ hv)
    (stronglyMeasurable_oldState μ hξ)

end Driver

/-!
### The Gaussian ring
-/

section Ring

variable (p : BlockBand.Parameters)

/-- Number of real Gaussian coordinates (including the redundant zero-variance labels). -/
abbrev ringDim : ℕ := Fintype.card p.GaussianCoordinate

/-- A fixed enumeration of the real Gaussian coordinates. -/
def ringEquiv : p.GaussianCoordinate ≃ Fin (ringDim p) := Fintype.equivFin _

/-- Variance of coordinate `i` (`gaussianCoordinateVariance`; `0` for redundant labels). -/
def ringVariance (i : Fin (ringDim p)) : ℝ :=
  (p.gaussianCoordinateVariance ((ringEquiv p).symm i) : ℝ)

theorem ringVariance_nonneg (i : Fin (ringDim p)) : 0 ≤ ringVariance p i := NNReal.coe_nonneg _

/-- Real coordinates of a matrix (`gaussianExtraction`, enumerated). -/
def ringCoords (H : p.SiteMatrix) : Fin (ringDim p) → ℝ :=
  fun i => p.gaussianExtraction H ((ringEquiv p).symm i)

/-- The Hermitian matrix with given real coordinates (`gaussianReconstruction`). -/
def ringMatrix (z : Fin (ringDim p) → ℝ) : p.SiteMatrix :=
  p.gaussianReconstruction fun c => z (ringEquiv p c)

theorem measurable_ringCoords : Measurable (ringCoords p) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).comp p.measurable_gaussianExtraction

theorem measurable_ringMatrix : Measurable (ringMatrix p) :=
  p.measurable_gaussianReconstruction.comp
    (measurable_pi_iff.2 fun c => measurable_pi_apply (ringEquiv p c))

theorem ringMatrix_isHermitian (z : Fin (ringDim p) → ℝ) : (ringMatrix p z).IsHermitian :=
  p.gaussianReconstruction_isHermitian _

theorem ringMatrix_ringCoords {H : p.SiteMatrix} (hH : H.IsHermitian) :
    ringMatrix p (ringCoords p H) = H := by
  have e : (fun c => ringCoords p H (ringEquiv p c)) = p.gaussianExtraction H := by
    funext c
    simp [ringCoords]
  rw [ringMatrix, e, p.gaussianReconstruction_gaussianExtraction H hH]

/-- The sample space of the ring OU flow: initial state `H_0 ∈ SiteMatrix`, one real Brownian
driver per real coordinate. -/
abbrev RingSample : Type := DriverSample p.SiteMatrix (Fin (ringDim p))

/-- **The ring OU flow in real coordinates**:
`X^i_t = e^{-t/2} c^i(H_0) + √v_i (B^i_t - B^i_0)
  - ½ e^{-t/2} ∫_0^t e^{s/2} √v_i (B^i_s - B^i_0) ds`, `H_0 = x.1`, `c = ringCoords`,
`v = ringVariance`. -/
def ringOU : ℝ≥0 → RingSample p → Fin (ringDim p) → ℝ :=
  driverOU (ringCoords p) (ringVariance p)

/-- **The matrix OU flow** `H_t = ringMatrix (X_t)`, Hermitian for every sample. The SDE
`dH = -½ H dt + Σ^{1/2} dB` holds in the real coordinates `ringCoords`
(`isContinuousSemimartingale_ringOU`, with `ringCoords (ringOUMatrix p t x) = ringOU p t x` by
`ringCoords_ringOUMatrix`); at matrix level the pathwise Mehler form is
`ringOUMatrix_eq_mehler`. -/
def ringOUMatrix (t : ℝ≥0) (x : RingSample p) : p.SiteMatrix := ringMatrix p (ringOU p t x)

theorem ringOU_zero (x : RingSample p) : ringOU p 0 x = ringCoords p x.1 := by
  rw [ringOU, driverOU, ouProcess_zero]

theorem ringOUMatrix_isHermitian (t : ℝ≥0) (x : RingSample p) :
    (ringOUMatrix p t x).IsHermitian :=
  ringMatrix_isHermitian p _

/-- The explicit (pathwise Mehler) formula of the ring OU flow. -/
theorem ringOU_apply (t : ℝ≥0) (x : RingSample p) (i : Fin (ringDim p)) :
    ringOU p t x i = Real.exp (-(t : ℝ) / 2) * ringCoords p x.1 i +
      Real.sqrt (ringVariance p i) * (x.2 i t - x.2 i 0) -
      1 / 2 * Real.exp (-(t : ℝ) / 2) * ∫ s in (0 : ℝ)..t, Real.exp (s / 2) *
        (Real.sqrt (ringVariance p i) * (x.2 i s.toNNReal - x.2 i 0)) := by
  simp only [ringOU, driverOU, ouProcess, ouPath, ouDrive, driverNoise, Real.toNNReal_coe,
    mul_sub]

variable {p}

/-- The initial matrix of the flow is the initial state: `H_0 = x.1` almost surely (the physical
law is a.s. Hermitian). -/
theorem ringOUMatrix_zero_ae (model : p.GaussianRingModel) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix),
      ringOUMatrix p 0 x = x.1 := by
  have h : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix),
      x.1.IsHermitian :=
    (measurePreserving_fst (μ := (model.law : Measure p.SiteMatrix))
      (ν := commonWienerLaw (Fin (ringDim p)))).quasiMeasurePreserving.ae model.isPhysical.1
  filter_upwards [h] with x hx
  rw [ringOUMatrix, ringOU_zero, ringMatrix_ringCoords p hx]

/-- The initial coordinates `X_0 = c(x.1)` are `F_0 ∨ N`-measurable. -/
theorem stronglyMeasurable_ringOU_zero (model : p.GaussianRingModel) :
    StronglyMeasurable[driverAugmented (κ := Fin (ringDim p))
      (model.law : Measure p.SiteMatrix) 0] (ringOU p 0) := by
  have e : ringOU p 0 = fun x : RingSample p => ringCoords p x.1 := funext (ringOU_zero p)
  rw [e]
  exact stronglyMeasurable_oldState _ (measurable_ringCoords p)

/-- **The band Ornstein–Uhlenbeck flow of the Gaussian ring is a continuous
semimartingale.** On the driver space with law `driverLaw model.law` (old state
`H_0 = x.1` with the physical law, independent drivers `B`, a Brownian motion for the
filtration by `isFiltrationBrownian_driverBrownian`) and the null-augmented filtration
`driverAugmented model.law`, the real coordinates `X_t = ringOU p t` of `H_t` form a continuous
semimartingale (`IsContinuousSemimartingale`) with drift `-½ X_t` and constant covariance
`diag(ringVariance p)` (the band variances `S_xx`, `S_xy/2`; zero for redundant labels).
-/
theorem isContinuousSemimartingale_ringOU (model : p.GaussianRingModel) :
    IsContinuousSemimartingale
      (driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix))
      (driverAugmented (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)) (ringOU p)
      (fun t x => (-(1 / 2 : ℝ)) • ringOU p t x)
      (fun _ _ => Matrix.diagonal (ringVariance p)) :=
  isContinuousSemimartingale_driverOU _ (measurable_ringCoords p) (ringVariance_nonneg p)

/-- **Itô's formula along the ring OU flow** (`semimartingaleItoFormula_holds`):
for every Borel `φ : ℝ × ℝ^d → ℝ` that is `C²` on `ℝ × U`, `U` open and containing `X_t` for all
`t` a.s., `φ(t, X_t)` is a continuous semimartingale with drift
`itoDrift φ X_t t (-½X_t) (diag v)` and bracket density `itoBracket φ X_t t (diag v)`. -/
theorem ringOU_itoFormula (model : p.GaussianRingModel) {U : Set (Fin (ringDim p) → ℝ)}
    (hU : IsOpen U)
    (hXU : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix),
      ∀ t, ringOU p t x ∈ U)
    {φ : ℝ × (Fin (ringDim p) → ℝ) → ℝ} (hφm : Measurable φ)
    (hφ : ContDiffOn ℝ 2 φ (Set.univ ×ˢ U)) :
    IsContinuousSemimartingale (d := 1)
      (driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix))
      (driverAugmented (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix))
      (fun t x (_ : Fin 1) => φ ((t : ℝ), ringOU p t x))
      (fun t x (_ : Fin 1) => itoDrift φ (ringOU p t x) t ((-(1 / 2 : ℝ)) • ringOU p t x)
        (Matrix.diagonal (ringVariance p)))
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        itoBracket φ (ringOU p t x) t (Matrix.diagonal (ringVariance p))) :=
  SemimartingaleIto.semimartingaleItoFormula_holds (ringDim p) (RingSample p) _ _ _ _ _
    (isContinuousSemimartingale_ringOU model) U hU hXU φ hφm hφ

end Ring

end BlockBand.Native.ErdosRiabov.Stochastic
