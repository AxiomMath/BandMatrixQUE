module

public import BlockBand.SourceProcess.Stochastic.Assembly.ItoUniverse
public import BlockBand.SourceProcess.Stochastic.Bridges.Product
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

/-!
# Exponential maximal tail for continuous local martingales

**Main result** (`measure_exists_abs_compensated_ge_le`): for a `𝓖`-stopping time `τ`, a
deterministic horizon `T`, a deterministic `y > 0` such that a.s.
`∫_0^t α ≤ y` for all `t ≤ T` with `t ≤ τ`, and every `λ ≥ 0`,
`Q(∃ t ≤ T, t ≤ τ, λ ≤ |N_t|) ≤ 2 exp(-λ²/(2y))`.
On a.s. continuous paths the event is `{sup_{t ≤ τ ∧ T} |N_t| ≥ λ}`. The one-sided form is
`measure_exists_compensated_ge_le`; the zero-drift form (`N_t = M_t - M_0`) is
`measure_exists_abs_sub_ge_le`; for `α ≥ 0` the hypothesis follows from the single bound
`∫_0^{τ∧T} α ≤ y` (`bracket_bound_of_nonneg`). Coordinate, real-linear-functional and complex
(Re/Im) corollaries are `measure_exists_abs_compensated_coord_ge_le`,
`measure_exists_abs_linear_compensated_ge_le` and `measure_exists_norm_complex_compensated_ge_le`.

* `compensated_isContinuousSemimartingale`: `N` is a continuous semimartingale with
  characteristics `(0, α)` (progressive measurability of pathwise integrals,
  `isStronglyProgressive_integral`);
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

universe u

/-!
### Measurability helpers
-/

/-- A function into `ℝ^d` is strongly measurable if its coordinates are. -/
theorem stronglyMeasurable_pi_fin {X : Type*} {m : MeasurableSpace X} {d : ℕ}
    {g : X → Fin d → ℝ} (h : ∀ i, StronglyMeasurable fun x => g x i) : StronglyMeasurable g :=
  (measurable_pi_iff.2 fun i => (h i).measurable).stronglyMeasurable

/-- A process in `ℝ^d` is strongly progressive if its coordinates are. -/
theorem isStronglyProgressive_pi_fin {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {𝓖 : Filtration ℝ≥0 m₀} {d : ℕ} {u : ℝ≥0 → Ω → Fin d → ℝ}
    (h : ∀ i, IsStronglyProgressive 𝓖 fun t ω => u t ω i) : IsStronglyProgressive 𝓖 u :=
  fun t => stronglyMeasurable_pi_fin fun i => h i t

/-- A time-constant process with `𝓖_0`-measurable value is strongly progressive. -/
theorem isStronglyProgressive_initial {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {𝓖 : Filtration ℝ≥0 m₀} {E : Type*} [TopologicalSpace E] {g : Ω → E}
    (hg : StronglyMeasurable[𝓖 0] g) : IsStronglyProgressive 𝓖 fun (_ : ℝ≥0) ω => g ω :=
  fun _ => (hg.mono (𝓖.mono zero_le)).comp_measurable measurable_snd

/-- Auxiliary (ambient σ-algebra): `p ↦ ∫_{(0, p.1]} f` is measurable on `Iic i × Ω'`. -/
theorem stronglyMeasurable_integral_Iic {Ω' : Type*} [MeasurableSpace Ω'] {f : ℝ≥0 → Ω' → ℝ}
    (i : ℝ≥0) (hf : StronglyMeasurable fun p : Set.Iic i × Ω' => f p.1 p.2) :
    StronglyMeasurable fun p : Set.Iic i × Ω' =>
      ∫ s in Ioc (0 : ℝ) ((p.1 : ℝ≥0) : ℝ), f s.toNNReal p.2 := by
  set c : ℝ → Set.Iic i := fun s => ⟨min s.toNNReal i, min_le_right _ _⟩
  have hc : Measurable c := (measurable_real_toNNReal.min measurable_const).subtype_mk
  have hg : Measurable fun q : (Set.Iic i × Ω') × ℝ => (c q.2, q.1.2) :=
    (hc.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)
  have hset : MeasurableSet {q : (Set.Iic i × Ω') × ℝ | q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)} :=
    measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)))
  have hF : StronglyMeasurable fun q : (Set.Iic i × Ω') × ℝ =>
      {q : (Set.Iic i × Ω') × ℝ | q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}.indicator
        (fun q => f (c q.2) q.1.2) q :=
    (hf.comp_measurable hg).indicator hset
  have hI := hF.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) i))
  convert hI using 1
  funext p
  have hp : ((p.1 : ℝ≥0) : ℝ) ≤ i := NNReal.coe_le_coe.2 p.1.2
  have e1 : (fun s : ℝ => {q : (Set.Iic i × Ω') × ℝ | q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}.indicator
      (fun q => f (c q.2) q.1.2) (p, s)) =
      (Iic ((p.1 : ℝ≥0) : ℝ)).indicator (fun s => f (c s) p.2) := by
    funext s
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iic]
  rw [e1, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have e2 : Iic ((p.1 : ℝ≥0) : ℝ) ∩ Ioc 0 (i : ℝ) = Ioc 0 ((p.1 : ℝ≥0) : ℝ) := by
    ext s
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hp⟩
  rw [e2]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hs' : s.toNNReal ≤ i := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1.le]; exact hs.2.trans hp
  simp only [c, min_eq_left hs']

/-- **Pathwise integrals of strongly progressive processes are strongly progressive.** -/
theorem isStronglyProgressive_integral {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {𝓖 : Filtration ℝ≥0 m₀} {f : ℝ≥0 → Ω → ℝ} (hf : IsStronglyProgressive 𝓖 f) :
    IsStronglyProgressive 𝓖 fun t ω => ∫ s in Ioc (0 : ℝ) t, f s.toNNReal ω := fun i =>
  @stronglyMeasurable_integral_Iic Ω (𝓖 i) f i (hf i)

/-!
### The martingale part of a continuous semimartingale
-/

variable {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The martingale part `N_t = Y_t - Y_0 - ∫_0^t β` (all coordinates). -/
def mgPart {Ω' : Type*} {d : ℕ} (Y β : ℝ≥0 → Ω' → Fin d → ℝ) : ℝ≥0 → Ω' → Fin d → ℝ :=
  fun t ω i => smCompensated Y β i t ω

theorem smCompensated_zero_time {Ω' : Type*} {d : ℕ} (Y β : ℝ≥0 → Ω' → Fin d → ℝ) (i : Fin d)
    (ω : Ω') : smCompensated Y β i 0 ω = 0 := by
  simp [smCompensated]

theorem smCompensated_mgPart {Ω' : Type*} {d : ℕ} (Y β : ℝ≥0 → Ω' → Fin d → ℝ) (i : Fin d) :
    smCompensated (mgPart Y β) (fun _ _ => 0) i = smCompensated Y β i := by
  funext t ω
  show smCompensated Y β i t ω - smCompensated Y β i 0 ω -
    ∫ s in Ioc (0 : ℝ) t, (0 : Fin d → ℝ) i = smCompensated Y β i t ω
  rw [smCompensated_zero_time]
  simp

/-- **The martingale part is a continuous semimartingale with characteristics `(0, α)`**, with
the localizing sequence of `Y`.
-/
theorem compensated_isContinuousSemimartingale
    {d : ℕ} {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 Y β α) :
    IsContinuousSemimartingale Q 𝓖 (mgPart Y β) (fun _ _ => 0) α := by
  have hprog : IsStronglyProgressive 𝓖 (mgPart Y β) := by
    refine isStronglyProgressive_pi_fin fun i => ?_
    have h1 : IsStronglyProgressive 𝓖 fun t ω => Y t ω i := fun s =>
      (continuous_apply i).comp_stronglyMeasurable (H.progressive s)
    have h0 : IsStronglyProgressive 𝓖 fun (_ : ℝ≥0) ω => Y 0 ω i :=
      isStronglyProgressive_initial ((continuous_apply i).comp_stronglyMeasurable (H.adapted 0))
    have h2 : IsStronglyProgressive 𝓖 fun t ω => ∫ s in Ioc (0 : ℝ) t, β s.toNNReal ω i :=
      isStronglyProgressive_integral (f := fun t ω => β t ω i) fun s =>
        (continuous_apply i).comp_stronglyMeasurable (H.drift_progressive s)
    exact (h1.sub h0).sub h2
  obtain ⟨τ, hτ, hτlim, hm⟩ := H.localizing
  refine ⟨hprog.stronglyAdapted, hprog, ?_, isStronglyProgressive_const _ _, H.cov_progressive,
    ?_, ⟨τ, hτ, hτlim, fun n => ?_⟩⟩
  · filter_upwards [H.continuous, H.integrable] with ω hω hi
    exact continuous_pi fun i => continuous_smCompensated hω fun t => (hi t).1 i
  · filter_upwards [H.integrable] with ω hi t
    exact ⟨fun i => by simp, (hi t).2⟩
  · simp only [smCompensated_mgPart]
    exact hm n

/-!
### The exponential test function
-/

/-- The linear form `(t, z) ↦ c z₀ - q z₁` on `ℝ × ℝ^{1+1}`. -/
def expLin (c q : ℝ) : (ℝ × (Fin (1 + 1) → ℝ)) →L[ℝ] ℝ :=
  c • ((ContinuousLinearMap.proj (Fin.castAdd 1 0)).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin (1 + 1) → ℝ))) -
    q • ((ContinuousLinearMap.proj (Fin.natAdd 1 0)).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin (1 + 1) → ℝ)))

theorem expLin_apply (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) :
    expLin c q p = c * p.2 (Fin.castAdd 1 0) - q * p.2 (Fin.natAdd 1 0) := by
  simp [expLin]

/-- `φ(t, z) = exp(c z₀ - q z₁)`; with `q = c²/2` it has zero Itô drift for `Z = (N, ∫α)`. -/
def expPhi (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) : ℝ := Real.exp (expLin c q p)

theorem contDiff_expPhi (c q : ℝ) : ContDiff ℝ 2 (expPhi c q) :=
  Real.contDiff_exp.comp (expLin c q).contDiff

theorem hasFDerivAt_expPhi (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) :
    HasFDerivAt (expPhi c q) (expPhi c q p • expLin c q) p :=
  (expLin c q).hasFDerivAt.exp

theorem fderiv_expPhi (c q : ℝ) : fderiv ℝ (expPhi c q) = fun p => expPhi c q p • expLin c q :=
  funext fun p => (hasFDerivAt_expPhi c q p).fderiv

theorem hasFDerivAt_fderiv_expPhi (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) :
    HasFDerivAt (fderiv ℝ (expPhi c q))
      ((expPhi c q p • expLin c q).smulRight (expLin c q)) p := by
  rw [fderiv_expPhi]
  exact (hasFDerivAt_expPhi c q p).smul_const (expLin c q)

theorem partialTime_expPhi (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) :
    partialTime (expPhi c q) p = 0 := by
  rw [partialTime, (hasFDerivAt_expPhi c q p).fderiv]
  simp [expLin_apply]

theorem partialSpace_expPhi (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) (i : Fin (1 + 1)) :
    partialSpace (expPhi c q) p i = expPhi c q p * expLin c q ((0 : ℝ), Pi.single i 1) := by
  rw [partialSpace, (hasFDerivAt_expPhi c q p).fderiv]
  simp only [smul_apply, smul_eq_mul]

theorem partialSpace2_expPhi (c q : ℝ) (p : ℝ × (Fin (1 + 1) → ℝ)) (i j : Fin (1 + 1)) :
    partialSpace2 (expPhi c q) p i j = expPhi c q p * expLin c q ((0 : ℝ), Pi.single i 1) *
      expLin c q ((0 : ℝ), Pi.single j 1) := by
  rw [partialSpace2, (hasFDerivAt_fderiv_expPhi c q p).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]

theorem natAdd_ne_castAdd : (Fin.natAdd 1 (0 : Fin 1) : Fin (1 + 1)) ≠ Fin.castAdd 1 0 := by
  decide

theorem expLin_single_castAdd (c q : ℝ) :
    expLin c q ((0 : ℝ), Pi.single (Fin.castAdd 1 0) 1) = c := by
  simp only [expLin_apply, Pi.single_eq_same, Pi.single_eq_of_ne natAdd_ne_castAdd]
  ring

theorem expLin_single_natAdd (c q : ℝ) :
    expLin c q ((0 : ℝ), Pi.single (Fin.natAdd 1 0) 1) = -q := by
  simp only [expLin_apply, Pi.single_eq_same, Pi.single_eq_of_ne natAdd_ne_castAdd.symm]
  ring

theorem concatCov_castAdd_castAdd {d₁ d₂ : ℕ} (a₁ : Matrix (Fin d₁) (Fin d₁) ℝ)
    (γ : Matrix (Fin d₁) (Fin d₂) ℝ) (a₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (i j : Fin d₁) :
    concatCov a₁ γ a₂ (Fin.castAdd d₂ i) (Fin.castAdd d₂ j) = a₁ i j := by
  simp [concatCov]

theorem concatCov_castAdd_natAdd {d₁ d₂ : ℕ} (a₁ : Matrix (Fin d₁) (Fin d₁) ℝ)
    (γ : Matrix (Fin d₁) (Fin d₂) ℝ) (a₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (i : Fin d₁)
    (j : Fin d₂) : concatCov a₁ γ a₂ (Fin.castAdd d₂ i) (Fin.natAdd d₁ j) = γ i j := by
  simp [concatCov]

theorem concatCov_natAdd_castAdd {d₁ d₂ : ℕ} (a₁ : Matrix (Fin d₁) (Fin d₁) ℝ)
    (γ : Matrix (Fin d₁) (Fin d₂) ℝ) (a₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (i : Fin d₂)
    (j : Fin d₁) : concatCov a₁ γ a₂ (Fin.natAdd d₁ i) (Fin.castAdd d₂ j) = γ j i := by
  simp [concatCov]

theorem concatCov_natAdd_natAdd {d₁ d₂ : ℕ} (a₁ : Matrix (Fin d₁) (Fin d₁) ℝ)
    (γ : Matrix (Fin d₁) (Fin d₂) ℝ) (a₂ : Matrix (Fin d₂) (Fin d₂) ℝ) (i j : Fin d₂) :
    concatCov a₁ γ a₂ (Fin.natAdd d₁ i) (Fin.natAdd d₁ j) = a₂ i j := by
  simp [concatCov]

/-- **Zero Itô drift.** For the characteristics of `Z = (N, ∫α)` (drift `(0, α)`, covariance
`[[α, 0], [0, 0]]`), the Itô drift of `exp(c z₀ - c² z₁ / 2)` vanishes. -/
theorem itoDrift_expPhi (c : ℝ) (z : Fin (1 + 1) → ℝ) (t : ℝ≥0)
    (a : Matrix (Fin 1) (Fin 1) ℝ) :
    itoDrift (expPhi c (c ^ 2 / 2)) z t (concatCoord 0 fun _ => a 0 0) (concatCov a 0 0) = 0 := by
  simp only [itoDrift, partialTime_expPhi, partialSpace_expPhi, partialSpace2_expPhi,
    Fin.sum_univ_add, Fin.sum_univ_one, concatCoord_castAdd, concatCoord_natAdd,
    concatCov_castAdd_castAdd, concatCov_castAdd_natAdd, concatCov_natAdd_castAdd,
    concatCov_natAdd_natAdd, expLin_single_castAdd, expLin_single_natAdd, Pi.zero_apply,
    Matrix.zero_apply]
  ring

/-!
### The exponential process
-/

/-- The bracket integral `A_t = ∫_0^t α^{00}`. -/
def bracketInt {Ω' : Type*} (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ≥0) (ω : Ω') : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω 0 0

/-- The joined state `Z = (N, A)`. -/
def expState {Ω' : Type*} (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ≥0) (ω : Ω') : Fin (1 + 1) → ℝ :=
  concatCoord (mgPart Y β t ω) fun _ => bracketInt α t ω

/-- The exponential process `E_t = exp(c N_t - c² A_t / 2)`. -/
def expProc {Ω' : Type*} (c : ℝ) (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ≥0) (ω : Ω') : ℝ :=
  expPhi c (c ^ 2 / 2) ((t : ℝ), expState Y β α t ω)

theorem expPhi_expState {Ω' : Type*} (c q : ℝ) (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ≥0) (ω : Ω') :
    expPhi c q ((t : ℝ), expState Y β α t ω) =
      Real.exp (c * smCompensated Y β 0 t ω - q * bracketInt α t ω) := by
  simp only [expPhi, expLin_apply, expState, concatCoord_castAdd, concatCoord_natAdd, mgPart]

theorem bracketInt_zero {Ω' : Type*} (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (ω : Ω') :
    bracketInt α 0 ω = 0 := by
  simp [bracketInt]

theorem expProc_zero {Ω' : Type*} (c : ℝ) (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (ω : Ω') : expProc c Y β α 0 ω = 1 := by
  rw [expProc, expPhi_expState, smCompensated_zero_time, bracketInt_zero]
  simp

theorem expProc_pos {Ω' : Type*} (c : ℝ) (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ≥0) (ω : Ω') : 0 < expProc c Y β α t ω :=
  Real.exp_pos _

theorem expProc_eq_of_sq {Ω' : Type*} (θ s : ℝ) (hs : s ^ 2 = 1) (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ≥0) (ω : Ω') :
    expProc (θ * s) Y β α t ω =
      Real.exp (θ * (s * smCompensated Y β 0 t ω) - θ ^ 2 / 2 * bracketInt α t ω) := by
  rw [expProc, expPhi_expState, mul_pow, hs, mul_one]
  ring_nf

theorem smCompensated_expProc {Ω' : Type*} (c : ℝ) (Y β : ℝ≥0 → Ω' → Fin 1 → ℝ)
    (α : ℝ≥0 → Ω' → Matrix (Fin 1) (Fin 1) ℝ) :
    smCompensated (fun t ω (_ : Fin 1) => expPhi c (c ^ 2 / 2) ((t : ℝ), expState Y β α t ω))
      (fun t ω (_ : Fin 1) => itoDrift (expPhi c (c ^ 2 / 2)) (expState Y β α t ω) t
        (concatCoord 0 fun _ => α t ω 0 0) (concatCov (α t ω) 0 0)) 0 =
      fun t ω => expProc c Y β α t ω - 1 := by
  funext t ω
  have h0 := expProc_zero c Y β α ω
  rw [expProc] at h0
  simp only [smCompensated, itoDrift_expPhi, integral_zero, sub_zero, h0, expProc]

/-- **The exponential local martingale.** For a continuous semimartingale `Y` in `ℝ¹` with
characteristics `(β, α)` and any `c`, `E_t = exp(c N_t - c² A_t / 2)` has a.s. continuous
paths and, along some localizing sequence `σ_n → ⊤` a.s., each stopped `E - 1` has a
`𝓖`-martingale modification. Proof: `compensated_isContinuousSemimartingale`, `concat_ac`,
Itô's formula and `itoDrift_expPhi`. -/
theorem exists_localized_expProc [IsProbabilityMeasure Q] {Y β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    (c : ℝ) :
    ∃ σn : ℕ → Ω → WithTop ℝ≥0, (∀ᵐ ω ∂Q, Tendsto (fun n => σn n ω) atTop (𝓝 ⊤)) ∧
      (∀ᵐ ω ∂Q, Continuous fun t => expProc c Y β α t ω) ∧
      ∀ n, HasMartingaleModification Q 𝓖
        (stoppedProcess (fun t ω => expProc c Y β α t ω - 1) (σn n)) := by
  have hα00 : IsStronglyProgressive 𝓖 fun t ω => α t ω 0 0 := fun s =>
    (continuous_id.matrix_elem 0 0).comp_stronglyMeasurable (H.cov_progressive s)
  have hv : IsStronglyProgressive 𝓖 fun t ω (_ : Fin 1) => bracketInt α t ω :=
    isStronglyProgressive_pi_fin fun _ => isStronglyProgressive_integral hα00
  have hvd : IsStronglyProgressive 𝓖 fun t ω (_ : Fin 1) => α t ω 0 0 :=
    isStronglyProgressive_pi_fin fun _ => hα00
  have hac : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ i : Fin 1,
      IntegrableOn (fun s : ℝ => (fun t ω (_ : Fin 1) => α t ω 0 0) s.toNNReal ω i) (Ioc 0 t) ∧
      (fun t ω (_ : Fin 1) => bracketInt α t ω) t ω i =
        (fun t ω (_ : Fin 1) => bracketInt α t ω) 0 ω i +
          ∫ s in Ioc (0 : ℝ) t, (fun t ω (_ : Fin 1) => α t ω 0 0) s.toNNReal ω i := by
    filter_upwards [H.integrable] with ω hi t _
    refine ⟨(hi t).2 0 0, ?_⟩
    simp only [bracketInt_zero, zero_add]
    rfl
  have HZ0 := (compensated_isContinuousSemimartingale H).concat_ac hv hvd hac
  have HZ : IsContinuousSemimartingale Q 𝓖 (expState Y β α)
      (fun t ω => concatCoord 0 fun _ => α t ω 0 0) (fun t ω => concatCov (α t ω) 0 0) := HZ0
  have HE := semimartingaleItoFormulaU_holds.{u} (1 + 1) Ω Q 𝓖 _ _ _ HZ univ isOpen_univ
    (ae_of_all _ fun _ _ => mem_univ _) (expPhi c (c ^ 2 / 2))
    (contDiff_expPhi _ _).continuous.measurable (contDiff_expPhi _ _).contDiffOn
  obtain ⟨σn, -, hσlim, hloc⟩ := HE.localizing
  refine ⟨σn, hσlim, ?_, fun n => ?_⟩
  · filter_upwards [HE.continuous] with ω hω
    exact (continuous_apply 0).comp hω
  · have := (hloc n).1 0
    rwa [smCompensated_expProc] at this

/-!
### Hitting times and localization
-/

/-- On a continuous real path the hitting time of a closed set that the path meets before `t`
is a time `h ≤ t` at which the path is in the set. -/
theorem exists_hitTime_eq_of_mem {Ω' : Type*} {X : ℝ≥0 → Ω' → ℝ} {ω : Ω'} {F : Set ℝ}
    (hF : IsClosed F) (hX : Continuous fun t => X t ω) {t : ℝ≥0} (ht : X t ω ∈ F) :
    ∃ h : ℝ≥0, hitTime F X ω = h ∧ h ≤ t ∧ X h ω ∈ F := by
  have hc : IsClosed {r : ℝ≥0 | X r ω ∈ F} := hF.preimage hX
  have hS : ({r : ℝ≥0 | X r ω ∈ F}).Nonempty := ⟨t, ht⟩
  have hbdd : BddBelow {r : ℝ≥0 | X r ω ∈ F} := ⟨0, fun _ _ => zero_le⟩
  have hmem := hc.csInf_mem hS hbdd
  exact ⟨_, le_antisymm (iInf₂_le _ hmem)
    (le_iInf₂ fun r hr => WithTop.coe_le_coe.2 (csInf_le hbdd hr)), csInf_le hbdd ht, hmem⟩

/-- Removing a localization: if every `Sn n` has measure `≤ b` and a.e. point of `S` lies in
`Sn n` for all large `n`, then `Q S ≤ b`. -/
theorem measure_le_of_eventually_mem {S : Set Ω} {Sn : ℕ → Set Ω} {b : ℝ≥0∞}
    (hb : ∀ n, Q (Sn n) ≤ b) (hsub : ∀ᵐ ω ∂Q, ω ∈ S → ∃ N, ∀ n ≥ N, ω ∈ Sn n) : Q S ≤ b := by
  have hmono : Monotone fun N => ⋂ n ≥ N, Sn n := fun N N' h =>
    subset_iInter₂ fun n hn => iInter₂_subset n (h.trans hn)
  calc Q S ≤ Q (⋃ N, ⋂ n ≥ N, Sn n) := by
        refine measure_mono_ae ?_
        filter_upwards [hsub] with ω h hω
        obtain ⟨N, hN⟩ := h hω
        exact mem_iUnion.2 ⟨N, mem_iInter₂.2 hN⟩
    _ = ⨆ N, Q (⋂ n ≥ N, Sn n) := hmono.measure_iUnion
    _ ≤ b := iSup_le fun N => (measure_mono (iInter₂_subset N (le_refl N))).trans (hb N)

/-!
### The exponential tail
-/

variable [IsProbabilityMeasure Q]

/-- **Signed exponential tail, general `θ`.** For `s = ±1` (`s² = 1`) and `θ ≥ 0`,
`Q(∃ t ≤ T, t ≤ τ, λ ≤ s N_t) ≤ exp(-(θλ - θ² y / 2))` whenever a.s. `∫_0^t α ≤ y` for all
`t ≤ T` with `t ≤ τ`. -/
theorem measure_exists_signed_ge_le {Y β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ}
    (hA : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω 0 0 ≤ y)
    {s θ lam : ℝ} (hs : s ^ 2 = 1) (hθ : 0 ≤ θ) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ s * smCompensated Y β 0 t ω} ≤
      ENNReal.ofReal (Real.exp (-(θ * lam - θ ^ 2 / 2 * y))) := by
  obtain ⟨σn, hσlim, hEc, hmod⟩ := exists_localized_expProc H (θ * s)
  have HN := compensated_isContinuousSemimartingale H
  have hXad : ∀ t, Measurable[𝓖 t] fun ω => s * smCompensated Y β 0 t ω := fun t =>
    ((continuous_const.mul (continuous_apply 0)).comp_stronglyMeasurable (HN.adapted t)).measurable
  have hXc : ∀ᵐ ω ∂Q, Continuous fun t => s * smCompensated Y β 0 t ω := by
    filter_upwards [HN.continuous] with ω hω
    exact continuous_const.mul ((continuous_apply 0).comp hω)
  obtain ⟨σ, hσ, -, hσae⟩ := exists_stoppingTime_ae_eq_hitTime (𝓖 := 𝓖) (F := Ici lam)
    (Y := fun t ω => s * smCompensated Y β 0 t ω) hXad hXc isClosed_Ici
  have hρ : IsStoppingTime 𝓖 fun ω => min (min (σ ω) (τ ω)) (T : WithTop ℝ≥0) :=
    (hσ.min hτ).min_const T
  have hEc' : ∀ᵐ ω ∂Q, Continuous fun t => expProc (θ * s) Y β α t ω - 1 := by
    filter_upwards [hEc] with ω hω using hω.sub continuous_const
  set K : ℝ := Real.exp (θ * lam - θ ^ 2 / 2 * y) with hK_def
  have hK : 0 < K := Real.exp_pos _
  refine measure_le_of_eventually_mem
    (Sn := fun n => {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
      (t : WithTop ℝ≥0) ≤ σn n ω ∧ lam ≤ s * smCompensated Y β 0 t ω}) (fun n => ?_) ?_
  · obtain ⟨Mt, hMt, hMtX⟩ := hasMartingaleModification_stopped_min (hmod n) hEc' hρ
      (σ := fun ω => min (min (min (σ ω) (τ ω)) (T : WithTop ℝ≥0)) (σn n ω)) fun _ => rfl
    have hfi : Integrable (fun ω => Mt T ω + 1) Q := (hMt.integrable T).add (integrable_const 1)
    have hint0 : ∫ ω, Mt 0 ω ∂Q = 0 := by
      rw [integral_congr_ae (hMtX 0)]
      simp only [stoppedProcess_eq_stopTime, stopTime_zero', expProc_zero, sub_self,
        integral_zero]
    have hintT : ∫ ω, Mt T ω ∂Q = 0 := by
      calc ∫ ω, Mt T ω ∂Q = ∫ ω, (Q[Mt T | 𝓖 0]) ω ∂Q := (integral_condExp (𝓖.le 0)).symm
        _ = ∫ ω, Mt 0 ω ∂Q := integral_congr_ae (hMt.condExp_ae_eq zero_le)
        _ = 0 := hint0
    have hf_nonneg : 0 ≤ᵐ[Q] fun ω => Mt T ω + 1 := by
      filter_upwards [hMtX T] with ω hω
      show (0 : ℝ) ≤ Mt T ω + 1
      rw [hω, stoppedProcess_eq_stopTime]
      linarith [expProc_pos (θ * s) Y β α
        (stopTime (min (min (min (σ ω) (τ ω)) (T : WithTop ℝ≥0)) (σn n ω)) T) ω]
    have hfint : ∫ ω, (Mt T ω + 1) ∂Q = 1 := by
      rw [integral_add (hMt.integrable T) (integrable_const 1), hintT]
      simp
    have hmark := mul_meas_ge_le_lintegral₀ hfi.aemeasurable.ennreal_ofReal (ENNReal.ofReal K)
    rw [← ofReal_integral_eq_lintegral_ofReal hfi hf_nonneg, hfint, ENNReal.ofReal_one] at hmark
    have hle : Q {ω | ENNReal.ofReal K ≤ ENNReal.ofReal (Mt T ω + 1)} ≤
        ENNReal.ofReal (Real.exp (-(θ * lam - θ ^ 2 / 2 * y))) := by
      rw [Real.exp_neg, ← hK_def, ENNReal.ofReal_inv_of_pos hK, ENNReal.le_inv_iff_mul_le,
        mul_comm]
      exact hmark
    refine le_trans (measure_mono_ae ?_) hle
    filter_upwards [hXc, hσae, hA, hMtX T] with ω hXω hσω hAω hMω
    rintro ⟨t, htT, htτ, htσ, hlt⟩
    obtain ⟨h, hh, hht, hhF⟩ := exists_hitTime_eq_of_mem
      (X := fun t ω => s * smCompensated Y β 0 t ω) (t := t) isClosed_Ici hXω (Set.mem_Ici.2 hlt)
    have hhτ : (h : WithTop ℝ≥0) ≤ τ ω := (WithTop.coe_le_coe.2 hht).trans htτ
    have hhT : (h : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0) := WithTop.coe_le_coe.2 (hht.trans htT)
    have hhσ : (h : WithTop ℝ≥0) ≤ σn n ω := (WithTop.coe_le_coe.2 hht).trans htσ
    have hρω : min (min (min (σ ω) (τ ω)) (T : WithTop ℝ≥0)) (σn n ω) = h := by
      rw [hσω, hh, min_eq_left hhτ, min_eq_left hhT, min_eq_left hhσ]
    have hfω : Mt T ω + 1 = expProc (θ * s) Y β α h ω := by
      rw [hMω, stoppedProcess_eq_stopTime, hρω, stopTime_coe, min_eq_right (hht.trans htT)]
      ring
    show ENNReal.ofReal K ≤ ENNReal.ofReal (Mt T ω + 1)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hfω, expProc_eq_of_sq θ s hs, hK_def]
    refine Real.exp_le_exp.2 ?_
    have h1 : θ * lam ≤ θ * (s * smCompensated Y β 0 h ω) := mul_le_mul_of_nonneg_left hhF hθ
    have h2 : bracketInt α h ω ≤ y := hAω h (hht.trans htT) hhτ
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ θ ^ 2 / 2)
    linarith
  · filter_upwards [hσlim] with ω hω hmem
    obtain ⟨t, htT, htτ, hlt⟩ := hmem
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((WithTop.tendsto_nhds_top_iff _).1 hω T)
    exact ⟨N, fun n hn => ⟨t, htT, htτ, (WithTop.coe_le_coe.2 htT).trans (hN n hn).le, hlt⟩⟩

theorem exponent_opt {lam y : ℝ} (hy : 0 < y) :
    -(lam / y * lam - (lam / y) ^ 2 / 2 * y) = -(lam ^ 2 / (2 * y)) := by
  field_simp
  ring

/-- **One-sided exponential maximal tail.** Let `Y` be a continuous
semimartingale in `ℝ¹` with characteristics `(β, α)` (`IsContinuousSemimartingale`),
`N_t = Y_t - Y_0 - ∫_0^t β` its martingale part, `τ` a `𝓖`-stopping time, `T` a deterministic
horizon and `y > 0` deterministic with a.s.
`∫_0^t α ≤ y` for every `t ≤ T` with `t ≤ τ`.
Then for every
`λ ≥ 0`:
`Q(∃ t ≤ T, t ≤ τ, λ ≤ N_t) ≤ exp(-λ²/(2y))`.
-/
theorem measure_exists_compensated_ge_le {Y β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (hA : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω 0 0 ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ smCompensated Y β 0 t ω} ≤
      ENNReal.ofReal (Real.exp (-(lam ^ 2 / (2 * y)))) := by
  have h := measure_exists_signed_ge_le H hτ T hA (s := 1) (θ := lam / y) (lam := lam)
    (by norm_num) (div_nonneg hlam hy.le)
  rw [exponent_opt hy] at h
  simpa only [one_mul] using h

/-- **Two-sided exponential maximal tail.** Same hypotheses as
`measure_exists_compensated_ge_le`; then for every `λ ≥ 0`:
`Q(∃ t ≤ T, t ≤ τ, λ ≤ |N_t|) ≤ 2 exp(-λ²/(2y))`, i.e.
`Q(sup_{t ≤ τ ∧ T} |Y_t - Y_0 - ∫_0^t β| ≥ λ) ≤ 2 exp(-λ²/(2y))` on a.s. continuous paths. -/
theorem measure_exists_abs_compensated_ge_le {Y β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (hA : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω 0 0 ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ |smCompensated Y β 0 t ω|} ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (2 * y)))) := by
  have hp := measure_exists_signed_ge_le H hτ T hA (s := 1) (θ := lam / y) (lam := lam)
    (by norm_num) (div_nonneg hlam hy.le)
  have hm := measure_exists_signed_ge_le H hτ T hA (s := -1) (θ := lam / y) (lam := lam)
    (by norm_num) (div_nonneg hlam hy.le)
  rw [exponent_opt hy] at hp hm
  calc Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ |smCompensated Y β 0 t ω|}
      ≤ Q ({ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
            lam ≤ 1 * smCompensated Y β 0 t ω} ∪
          {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
            lam ≤ -1 * smCompensated Y β 0 t ω}) := by
        refine measure_mono ?_
        rintro ω ⟨t, htT, htτ, hlt⟩
        rcases le_total 0 (smCompensated Y β 0 t ω) with h0 | h0
        · left
          refine ⟨t, htT, htτ, ?_⟩
          rw [one_mul]; rwa [abs_of_nonneg h0] at hlt
        · right
          refine ⟨t, htT, htτ, ?_⟩
          rw [neg_one_mul]; rwa [abs_of_nonpos h0] at hlt
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := by rw [two_mul]; exact add_le_add hp hm

/-- **Zero-drift form.** For a continuous semimartingale `M` in `ℝ¹` with zero
drift and bracket density `α`, under the bracket bound of `measure_exists_compensated_ge_le`:
`Q(∃ t ≤ T, t ≤ τ, λ ≤ |M_t - M_0|) ≤ 2 exp(-λ²/(2y))` for every `λ ≥ 0`. -/
theorem measure_exists_abs_sub_ge_le {M : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 M (fun _ _ => 0) α)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (hA : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω 0 0 ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ |M t ω 0 - M 0 ω 0|} ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (2 * y)))) := by
  have e : ∀ t ω, smCompensated M (fun _ _ => 0) 0 t ω = M t ω 0 - M 0 ω 0 := fun t ω => by
    simp [smCompensated]
  simpa only [e] using measure_exists_abs_compensated_ge_le H hτ T hy hA hlam

omit [IsProbabilityMeasure Q] in
/-- **The bracket hypothesis from a bound at `τ ∧ T`.** If a.s. `α^{00} ≥ 0`, its paths are
locally integrable and `∫_0^{τ∧T} α^{00} ≤ y`, then a.s. `∫_0^t α^{00} ≤ y` for every `t ≤ T`
with `t ≤ τ` (the hypothesis of `measure_exists_compensated_ge_le`). -/
theorem bracket_bound_of_nonneg {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
    (hi : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => α s.toNNReal ω 0 0) (Ioc 0 t))
    (hα : ∀ᵐ ω ∂Q, ∀ t, 0 ≤ α t ω 0 0) {τ : Ω → WithTop ℝ≥0} {T : ℝ≥0} {y : ℝ}
    (hy : ∀ᵐ ω ∂Q, ∫ s in Ioc (0 : ℝ) (stopTime (τ ω) T), α s.toNNReal ω 0 0 ≤ y) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω 0 0 ≤ y := by
  filter_upwards [hi, hα, hy] with ω hiω hαω hyω t htT htτ
  refine le_trans (setIntegral_mono_set (hiω _) (ae_of_all _ fun s => hαω _) ?_) hyω
  exact (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (le_stopTime htτ htT))).eventuallyLE

end BlockBand.Native.ErdosRiabov.Stochastic
