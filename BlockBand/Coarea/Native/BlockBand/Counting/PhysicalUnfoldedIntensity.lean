module

public import BlockBand.Coarea.Native.BlockBand.Counting.ProjectedWegnerCount
public import BlockBand.Coarea.Native.BlockBand.Counting.UnfoldedMarkedConfiguration
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Unfolded first intensities for the physical Gaussian ring

This module transports the physical projected-Wegner first-count estimate through
exact spectral unfolding.  The resulting expected empirical measure has interval
mass at most

`π (C / √c) W n (b-a) / (L ρ)`

at general unfolding scale `L`, and therefore at most
`π (C / √c) (b-a) / ρ` at the physical dimension scale `L = nW`.
The measure is diffuse.  These are first-intensity statements only: no
factorial-moment estimate is asserted.

The finite law below uses the trivial mark `Unit`.  Passing these finite
intensities to a varying-dimension vague weak limit needs a common
point-measure state space and an expectation/uniform-integrability theorem; it
is not inferred merely from weak convergence, and it is not done here.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory
open scoped BigOperators ENNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The sample probability measure of a physical Gaussian-ring law. -/
def sampleProbability {p : Params} (M : Law p) : ProbabilityMeasure M.Ω :=
  ⟨M.P, inferInstance⟩

/-- The paper's unfolded location `L ρ (λ-e)` for the physical spectrum. -/
def unfoldedPhysicalLocation {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) (ω : M.Ω) (i : Fin (Fintype.card (Site p.n p.W))) : ℝ :=
  L * ρ * (orderedEigenvalue (physicalDeformedHermitian M V hV ω) i - e)

/-- The finite unfolded physical spectrum with the trivial mark. -/
def unfoldedPhysicalConfiguration {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) (ω : M.Ω) :
    FiniteMarkedConfiguration (Fintype.card (Site p.n p.W)) Unit :=
  fun i => (unfoldedPhysicalLocation M V hV e L ρ ω i, ())

/-- The unfolded physical finite configuration is measurable. -/
theorem measurable_unfoldedPhysicalConfiguration {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) :
    Measurable (unfoldedPhysicalConfiguration M V hV e L ρ) := by
  rw [measurable_pi_iff]
  intro i
  apply Measurable.prodMk
  · unfold unfoldedPhysicalLocation
    exact (measurable_const.mul measurable_const).mul
      (((measurable_orderedEigenvalue i).comp
        (measurable_physicalDeformedHermitian M V hV)).sub measurable_const)
  · exact measurable_const

/-- The finite pushforward law of the unfolded physical spectrum. -/
def unfoldedPhysicalConfigurationLaw {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) :
    ProbabilityMeasure (FiniteMarkedConfiguration
      (Fintype.card (Site p.n p.W)) Unit) :=
  (sampleProbability M).map (unfoldedPhysicalConfiguration M V hV e L ρ)

/-- Local counts are exactly eigenvalue counts in the inverse unfolded window. -/
theorem finiteMarkedLocalCount_unfoldedPhysicalConfiguration
    {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) (U : Set ℝ) (ω : M.Ω) :
    finiteMarkedLocalCount U (unfoldedPhysicalConfiguration M V hV e L ρ ω) =
      eigenCount (physicalDeformedHermitian M V hV ω)
        {x | L * ρ * (x - e) ∈ U} := by
  rfl

/-- Exact transport of an arbitrary unfolded closed interval under a positive
unfolding slope. -/
theorem finiteMarkedLocalCount_Icc_unfoldedPhysicalConfiguration
    {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ a b : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (ω : M.Ω) :
    finiteMarkedLocalCount (Set.Icc a b)
        (unfoldedPhysicalConfiguration M V hV e L ρ ω) =
      eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e + a / (L * ρ)) (e + b / (L * ρ))) := by
  rw [finiteMarkedLocalCount_unfoldedPhysicalConfiguration]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  have hs : 0 < L * ρ := mul_pos hL hρ
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · have h : a / (L * ρ) ≤ x - e := (div_le_iff₀ hs).2 (by nlinarith)
      linarith
    · have h : x - e ≤ b / (L * ρ) := (le_div_iff₀ hs).2 (by nlinarith)
      linarith
  · rintro ⟨ha, hb⟩
    constructor
    · have h : a / (L * ρ) ≤ x - e := by linarith
      simpa [mul_comm] using (div_le_iff₀ hs).1 h
    · have h : x - e ≤ b / (L * ρ) := by linarith
      simpa [mul_comm] using (le_div_iff₀ hs).1 h

/-- The expected unnormalised unfolded physical empirical spectral measure. -/
def expectedUnfoldedPhysicalMeasure {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) : Measure ℝ :=
  ∑ i : Fin (Fintype.card (Site p.n p.W)),
    M.P.map (unfoldedPhysicalLocation M V hV e L ρ · i)

/-- Integration against the unfolded intensity is expectation of the finite
unfolded eigenvalue sum. -/
theorem lintegral_expectedUnfoldedPhysicalMeasure {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂expectedUnfoldedPhysicalMeasure M V hV e L ρ =
      ∫⁻ ω, ∑ i : Fin (Fintype.card (Site p.n p.W)),
        f (unfoldedPhysicalLocation M V hV e L ρ ω i) ∂M.P := by
  rw [expectedUnfoldedPhysicalMeasure, lintegral_finsetSum_measure]
  have heig (i : Fin (Fintype.card (Site p.n p.W))) :
      Measurable (unfoldedPhysicalLocation M V hV e L ρ · i) := by
    unfold unfoldedPhysicalLocation
    exact (measurable_const.mul measurable_const).mul
      (((measurable_orderedEigenvalue i).comp
        (measurable_physicalDeformedHermitian M V hV)).sub measurable_const)
  simp_rw [lintegral_map hf (heig _)]
  rw [lintegral_finsetSum]
  intro i _hi
  exact hf.comp (heig i)

/-- On a Borel set, unfolded intensity is expected multiplicity count. -/
theorem expectedUnfoldedPhysicalMeasure_apply {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    expectedUnfoldedPhysicalMeasure M V hV e L ρ s =
      ∫⁻ ω, (finiteMarkedLocalCount s
        (unfoldedPhysicalConfiguration M V hV e L ρ ω) : ℝ≥0∞) ∂M.P := by
  rw [← lintegral_indicator_one hs]
  change (∫⁻ x, s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) x ∂
      expectedUnfoldedPhysicalMeasure M V hV e L ρ) = _
  rw [lintegral_expectedUnfoldedPhysicalMeasure M V hV e L ρ
    (s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hs)]
  apply lintegral_congr
  intro ω
  unfold finiteMarkedLocalCount unfoldedPhysicalConfiguration
  simp [Set.indicator, Finset.sum_boole]

/-- General-scale unfolded interval intensity bound obtained by exact transport
of the physical first-count estimate. -/
theorem expectedUnfoldedPhysicalMeasure_Icc_le {p : Params}
    (input : PSSSInput.{0}) (M : Law.{0} p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ a b : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hab : a < b) :
    expectedUnfoldedPhysicalMeasure M V hV e L ρ (Set.Icc a b) ≤
      ENNReal.ofReal (Real.pi * (input.C / Real.sqrt p.c) *
        (p.W : ℝ) * (p.n : ℝ) * ((b - a) / (L * ρ))) := by
  rw [expectedUnfoldedPhysicalMeasure_apply M V hV e L ρ _ measurableSet_Icc]
  let N : M.Ω → ℝ := fun ω =>
    (finiteMarkedLocalCount (Set.Icc a b)
      (unfoldedPhysicalConfiguration M V hV e L ρ ω) : ℝ)
  have hNmeas : Measurable N := by
    exact measurable_from_nat.comp
      ((measurable_finiteMarkedLocalCount (Mark := Unit) _ measurableSet_Icc).comp
        (measurable_unfoldedPhysicalConfiguration M V hV e L ρ))
  have hNint : Integrable N M.P := by
    refine Integrable.of_bound hNmeas.aestronglyMeasurable
      (Fintype.card (Site p.n p.W) : ℝ) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp [N]
    unfold finiteMarkedLocalCount
    norm_cast
    simpa using Finset.card_filter_le (Finset.univ :
      Finset (Fin (Fintype.card (Site p.n p.W))))
      (fun i => (unfoldedPhysicalConfiguration M V hV e L ρ ω i).1 ∈ Set.Icc a b)
  have hconvert : ENNReal.ofReal (∫ ω, N ω ∂M.P) =
      ∫⁻ ω, (finiteMarkedLocalCount (Set.Icc a b)
        (unfoldedPhysicalConfiguration M V hV e L ρ ω) : ℝ≥0∞) ∂M.P := by
    rw [ofReal_integral_eq_lintegral_ofReal hNint
      (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)]
    apply lintegral_congr
    intro ω
    simp [N]
  rw [← hconvert]
  apply ENNReal.ofReal_le_ofReal
  have hs : 0 < L * ρ := mul_pos hL hρ
  have hab' : e + a / (L * ρ) < e + b / (L * ρ) := by
    gcongr
  have h := expected_eigenCount_arbitrary_Icc_physical_le
    input M V hV hab'
  have hcount : (∫ ω, N ω ∂M.P) =
      ∫ ω, (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e + a / (L * ρ)) (e + b / (L * ρ))) : ℝ) ∂M.P := by
    apply integral_congr_ae
    filter_upwards with ω
    unfold N
    exact_mod_cast finiteMarkedLocalCount_Icc_unfoldedPhysicalConfiguration
      M V hV e L ρ a b hL hρ ω
  rw [hcount]
  calc
    _ ≤ Real.pi * (input.C / Real.sqrt p.c) * (p.W : ℝ) * (p.n : ℝ) *
        ((e + b / (L * ρ)) - (e + a / (L * ρ))) := h
    _ = Real.pi * (input.C / Real.sqrt p.c) * (p.W : ℝ) * (p.n : ℝ) *
        ((b - a) / (L * ρ)) := by
      field_simp [ne_of_gt hs]
      ring

/-- The unnormalised unfolded intensity has total mass equal to the physical
matrix dimension `nW`. -/
theorem expectedUnfoldedPhysicalMeasure_univ {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) :
    expectedUnfoldedPhysicalMeasure M V hV e L ρ Set.univ =
      (p.n : ℝ≥0∞) * (p.W : ℝ≥0∞) := by
  simp [expectedUnfoldedPhysicalMeasure]

/-- At the physical dimension scale `L = nW`, the factors `nW` cancel and
one obtains a size-uniform unfolded interval intensity bound. -/
theorem expectedUnfoldedPhysicalMeasure_Icc_le_dimensionScale {p : Params}
    (input : PSSSInput.{0}) (M : Law.{0} p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e ρ a b : ℝ) (hρ : 0 < ρ) (hab : a < b) :
    expectedUnfoldedPhysicalMeasure M V hV e
        ((p.n : ℝ) * (p.W : ℝ)) ρ (Set.Icc a b) ≤
      ENNReal.ofReal (Real.pi * (input.C / Real.sqrt p.c) *
        ((b - a) / ρ)) := by
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast p.n_pos
  have hW : 0 < (p.W : ℝ) := by exact_mod_cast p.W_pos
  have h := expectedUnfoldedPhysicalMeasure_Icc_le input M V hV e
    ((p.n : ℝ) * (p.W : ℝ)) ρ a b (mul_pos hn hW) hρ hab
  have hscale :
      Real.pi * (input.C / Real.sqrt p.c) * (p.W : ℝ) * (p.n : ℝ) *
          ((b - a) / (((p.n : ℝ) * (p.W : ℝ)) * ρ)) =
        Real.pi * (input.C / Real.sqrt p.c) * ((b - a) / ρ) := by
    field_simp [ne_of_gt hn, ne_of_gt hW, ne_of_gt hρ]
  rw [hscale] at h
  exact h

/-- The expected unfolded physical measure is finite (its total mass is the
finite matrix dimension). -/
def unfoldedPhysicalIntensity {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e L ρ : ℝ) : FiniteMeasure ℝ :=
by
  let μ := expectedUnfoldedPhysicalMeasure M V hV e L ρ
  have hfin : μ Set.univ < ⊤ := by
    simp [μ, expectedUnfoldedPhysicalMeasure]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  exact ⟨μ, (isFiniteMeasure_iff μ).2 hfin⟩

/-- The dimension-scale expected unfolded intensity has no atoms.  This is the
finite-volume diffuseness consequence of the uniform Lipschitz interval bound;
it does not assert diffuseness of a weak-limit intensity without an additional
expectation-passage theorem. -/
theorem expectedUnfoldedPhysicalMeasure_singleton_eq_zero {p : Params}
    (input : PSSSInput.{0}) (M : Law.{0} p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    expectedUnfoldedPhysicalMeasure M V hV e
        ((p.n : ℝ) * (p.W : ℝ)) ρ {x} = 0 := by
  let K : ℝ := Real.pi * (input.C / Real.sqrt p.c) / ρ
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg
      (mul_nonneg Real.pi_nonneg
        (div_nonneg input.C_nonneg (Real.sqrt_nonneg _))) hρ.le
  refine ENNReal.eq_zero_of_le_mul_pow
    (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) < 1)
    (ε := Real.toNNReal (2 * K)) ?_
  intro n
  let r : ℝ := (1 / 2 : ℝ) ^ n
  have hr : 0 < r := by positivity
  calc
    expectedUnfoldedPhysicalMeasure M V hV e
        ((p.n : ℝ) * (p.W : ℝ)) ρ {x} ≤
      expectedUnfoldedPhysicalMeasure M V hV e
        ((p.n : ℝ) * (p.W : ℝ)) ρ (Set.Icc (x - r) (x + r)) := by
          apply measure_mono
          intro y hy
          simp only [Set.mem_singleton_iff] at hy
          subst y
          exact ⟨by linarith, by linarith⟩
    _ ≤ ENNReal.ofReal (Real.pi * (input.C / Real.sqrt p.c) *
        (((x + r) - (x - r)) / ρ)) :=
      expectedUnfoldedPhysicalMeasure_Icc_le_dimensionScale
        input M V hV e ρ (x - r) (x + r) hρ (by linarith)
    _ = (Real.toNNReal (2 * K) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 2 : ℝ)) ^ n := by
      rw [ENNReal.ofNNReal_toNNReal,
        ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK)]
      congr 1
      dsimp [K, r]
      field_simp [ne_of_gt hρ]
      ring

/-- The bundled dimension-scale intensity is diffuse. -/
theorem unfoldedPhysicalIntensity_singleton_eq_zero {p : Params}
    (input : PSSSInput.{0}) (M : Law.{0} p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (hV : V.IsHermitian)
    (e ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    (unfoldedPhysicalIntensity M V hV e
      ((p.n : ℝ) * (p.W : ℝ)) ρ : Measure ℝ) {x} = 0 :=
  expectedUnfoldedPhysicalMeasure_singleton_eq_zero
    input M V hV e ρ hρ x

end GaussianRing

/-- Generic weak-limit intensity closure.  Any coordinate intensity for which
the physical unfolded interval estimate has already been passed to the limit is
diffuse.  Thus, in an application to `EndpointIntensityBoundaryInput`, once the
finite coordinate intensity and the expected-evaluation identity are given,
diffuseness follows from this theorem. -/
theorem intensity_singleton_eq_zero_of_Icc_lipschitz
    (ν : Measure ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hIcc : ∀ a b : ℝ, a < b → ν (Set.Icc a b) ≤
      ENNReal.ofReal (K * (b - a))) (x : ℝ) :
    ν {x} = 0 := by
  refine ENNReal.eq_zero_of_le_mul_pow
    (by norm_num : ENNReal.ofReal (1 / 2 : ℝ) < 1)
    (ε := Real.toNNReal (2 * K)) ?_
  intro n
  let r : ℝ := (1 / 2 : ℝ) ^ n
  have hr : 0 < r := by positivity
  calc
    ν {x} ≤ ν (Set.Icc (x - r) (x + r)) := by
      apply measure_mono
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨by linarith, by linarith⟩
    _ ≤ ENNReal.ofReal (K * ((x + r) - (x - r))) :=
      hIcc (x - r) (x + r) (by linarith)
    _ = (Real.toNNReal (2 * K) : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 2 : ℝ)) ^ n := by
      rw [ENNReal.ofNNReal_toNNReal,
        ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK)]
      congr 1
      dsimp [r]
      ring

/-- Coordinatewise version tailored to limit point-process intensities. -/
theorem coordinateIntensities_diffuse_of_Icc_lipschitz
    (ν : ℕ → FiniteMeasure ℝ) (K : ℕ → ℝ)
    (hK : ∀ n, 0 ≤ K n)
    (hIcc : ∀ n a b, a < b →
      (ν n : Measure ℝ) (Set.Icc a b) ≤
        ENNReal.ofReal (K n * (b - a))) :
    ∀ n x, (ν n : Measure ℝ) {x} = 0 := by
  intro n x
  exact intensity_singleton_eq_zero_of_Icc_lipschitz
    (ν n : Measure ℝ) (K n) (hK n) (hIcc n) x

end CoareaNative.BlockBand
