module
public import BlockBand.SourceProcess.Stochastic.Representation.Basic
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VecMart
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.FixStop
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.FixAlpha
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.HorizonRestrict
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bounded predictable multipliers on `PredL2`

Setting: `(Ω, m₀)`, raw filtration `𝓖`, a measure `μ` on `ℝ × Ω` (finite where stated),
`PredL2 𝓖 μ` the raw-predictable classes in `L²(μ)`.

* `IsBddPred 𝓖 f`: `f : ℝ × Ω → ℝ` is raw predictable and bounded; closed under sums, products,
  constants and predictable indicators.
* `bpL2 μ hf`: its class in `PredL2 𝓖 μ` (`bpL2_coeFn`: representative `f` `μ`-a.e.).
* `predMul 𝓖 hg : PredL2 𝓖 μ →L[ℝ] PredL2 𝓖 μ`: multiplication by a bounded predictable `g`
  (`predMul_coeFn`: representative `g · F̃`).
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓖 : Filtration ℝ≥0 mΩ)

/-- Bounded raw predictable functions on `ℝ × Ω`. -/
structure IsBddPred (f : ℝ × Ω → ℝ) : Prop where
  sm : StronglyMeasurable[predictableSpace (toCF 𝓖)] f
  bdd : ∃ C, 0 ≤ C ∧ ∀ p, |f p| ≤ C

variable {𝓖}

namespace IsBddPred

theorem const (c : ℝ) : IsBddPred 𝓖 fun _ => c :=
  ⟨stronglyMeasurable_const, |c|, abs_nonneg _, fun _ => le_rfl⟩

theorem add {f g : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) (hg : IsBddPred 𝓖 g) :
    IsBddPred 𝓖 fun p => f p + g p := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  obtain ⟨D, hD0, hD⟩ := hg.bdd
  exact ⟨hf.sm.add hg.sm, C + D, add_nonneg hC0 hD0, fun p =>
    (abs_add_le _ _).trans (add_le_add (hC p) (hD p))⟩

theorem mul {f g : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) (hg : IsBddPred 𝓖 g) :
    IsBddPred 𝓖 fun p => f p * g p := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  obtain ⟨D, hD0, hD⟩ := hg.bdd
  exact ⟨hf.sm.mul hg.sm, C * D, mul_nonneg hC0 hD0, fun p => by
    rw [abs_mul]; exact mul_le_mul (hC p) (hD p) (abs_nonneg _) hC0⟩

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ × Ω → ℝ} (hf : ∀ i, IsBddPred 𝓖 (f i)) :
    IsBddPred 𝓖 fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (𝓖 := 𝓖) 0
  | insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (hf x).add ih

theorem indicator {f : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) {R : Set (ℝ × Ω)}
    (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R) : IsBddPred 𝓖 (R.indicator f) := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  refine ⟨hf.sm.indicator hR, C, hC0, fun p => ?_⟩
  by_cases hp : p ∈ R
  · rw [indicator_of_mem hp]; exact hC p
  · rw [indicator_of_notMem hp, abs_zero]; exact hC0

theorem comp {f : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    ∃ C, 0 ≤ C ∧ ∀ p, |φ (f p)| ≤ C := by
  obtain ⟨C, -, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun p => ?_⟩
  have h := hD (f p) (abs_le.1 (hC p))
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

end IsBddPred

variable {μ : Measure (ℝ × Ω)}

/-- The class of a bounded predictable function. -/
def bpL2 (μ : Measure (ℝ × Ω)) [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) :
    PredL2 𝓖 μ :=
  boundedPredL2 hf.sm.aestronglyMeasurable hf.bdd.choose_spec.2

theorem bpL2_coeFn [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) :
    (((bpL2 μ hf : PredL2 𝓖 μ) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ] f :=
  boundedPredL2_coeFn _ _

theorem bpL2_congr [IsFiniteMeasure μ] {f g : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f)
    (hg : IsBddPred 𝓖 g) (hfg : f =ᵐ[μ] g) : bpL2 μ hf = bpL2 μ hg :=
  predL2_ext 𝓖 ((bpL2_coeFn hf).trans (hfg.trans (bpL2_coeFn hg).symm))

section Mul

variable {g : ℝ × Ω → ℝ}

theorem memLp_predMul (hg : IsBddPred 𝓖 g) (f : Lp ℝ 2 μ) : MemLp (fun p => g p * f p) 2 μ := by
  obtain ⟨C, -, hC⟩ := hg.bdd
  refine (Lp.memLp f).of_le_mul (c := C)
    ((hg.sm.mono (predictableSpace_le _)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun p => ?_)
  rw [norm_mul, Real.norm_eq_abs (g p)]
  exact mul_le_mul_of_nonneg_right (hC p) (norm_nonneg _)

theorem predMul_map_add {g : ℝ × Ω → ℝ} (f f' : Lp ℝ 2 μ) :
    (fun p => g p * (f + f') p) =ᵐ[μ] (fun p => g p * f p) + fun p => g p * f' p := by
  filter_upwards [Lp.coeFn_add f f'] with p hp
  simp only [hp, Pi.add_apply, mul_add]

/-- Multiplication by `g` on `L²(μ)` (linear map). -/
def mulLin (hg : IsBddPred 𝓖 g) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_predMul hg f).toLp _
  map_add' f f' :=
    (MemLp.toLp_congr _ ((memLp_predMul hg f).add (memLp_predMul hg f'))
      (predMul_map_add f f')).trans (MemLp.toLp_add _ _)
  map_smul' c f := by
    refine (MemLp.toLp_congr _ ((memLp_predMul hg f).const_smul c) ?_).trans
      (MemLp.toLp_const_smul _ _)
    filter_upwards [Lp.coeFn_smul c f] with p hp
    simp only [hp, Pi.smul_apply, smul_eq_mul]
    ring

theorem mulLin_coeFn (hg : IsBddPred 𝓖 g) (f : Lp ℝ 2 μ) :
    (mulLin hg f : ℝ × Ω → ℝ) =ᵐ[μ] fun p => g p * f p :=
  MemLp.coeFn_toLp (memLp_predMul hg f)

theorem norm_mulLin_le (hg : IsBddPred 𝓖 g) (f : Lp ℝ 2 μ) : ‖mulLin hg f‖ ≤ hg.bdd.choose * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [mulLin_coeFn hg f] with p hp
  rw [hp, norm_mul, Real.norm_eq_abs (g p)]
  exact mul_le_mul_of_nonneg_right (hg.bdd.choose_spec.2 p) (norm_nonneg _)

/-- Multiplication by `g` on `L²(μ)` (continuous linear map). -/
def mulCLM (hg : IsBddPred 𝓖 g) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (mulLin hg).mkContinuous _ (norm_mulLin_le hg)

theorem mulCLM_mem (hg : IsBddPred 𝓖 g) (f : PredL2 𝓖 μ) :
    mulCLM hg (f : Lp ℝ 2 μ) ∈ lpMeas ℝ ℝ (predictableSpace (toCF 𝓖)) 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  obtain ⟨k, hk, hfk⟩ := lpMeas.aestronglyMeasurable f
  refine ⟨fun p => g p * k p, hg.sm.mul hk, ?_⟩
  filter_upwards [mulLin_coeFn hg (f : Lp ℝ 2 μ), hfk] with p h1 h2
  change (mulLin hg (f : Lp ℝ 2 μ) : ℝ × Ω → ℝ) p = _
  rw [h1, h2]

variable (𝓖) in
/-- **Multiplication by a bounded predictable function on `PredL2 𝓖 μ`.** -/
def predMul (hg : IsBddPred 𝓖 g) : PredL2 𝓖 μ →L[ℝ] PredL2 𝓖 μ :=
  ((mulCLM hg).comp (lpMeas ℝ ℝ (predictableSpace (toCF 𝓖)) 2 μ).subtypeL).codRestrict _
    (mulCLM_mem hg)

theorem predMul_coeFn (hg : IsBddPred 𝓖 g) (f : PredL2 𝓖 μ) :
    (((predMul 𝓖 hg f : PredL2 𝓖 μ) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ]
      fun p => g p * ((f : Lp ℝ 2 μ) : ℝ × Ω → ℝ) p :=
  mulLin_coeFn hg _

theorem predMul_bpL2 (hg : IsBddPred 𝓖 g) [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) :
    predMul 𝓖 hg (bpL2 μ hf) = bpL2 μ (hg.mul hf) := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predMul_coeFn hg (bpL2 μ hf), bpL2_coeFn (μ := μ) hf,
    bpL2_coeFn (μ := μ) (hg.mul hf)] with p h1 h2 h3
  rw [h1, h2, h3]

end Mul

end BlockBand.SourceProcess.Stochastic.Representation
