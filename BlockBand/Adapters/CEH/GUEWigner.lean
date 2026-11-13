module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Counting.CircularGaussianMoments

/-!
# The normalized GUE as a CEH Wigner family

The CEH local law and eigenstate thermalization theorems are applied to `F + G` with
`G ~ GUE_N(s/N)`; this module realizes `GUE_N(1/N)` as a `BlockBand.External.CEH.WignerFamily`.

Law: in dimension `N` the law is `gueSourceLaw N`, the image of the Johansson coordinate
product `Johansson.coordinateMeasure N (1/N)` (diagonal real variance `1/N`, strict-upper
real and imaginary parts variance `1/(2N)`) under Hermitian reconstruction. Entry laws:
diagonal `gaussianReal 0 1`, off-diagonal the standard circular complex Gaussian (image of
`gaussianReal 0 (1/2) ⊗ gaussianReal 0 (1/2)` under `(x, y) ↦ x + i y`), so
`E|χ|² = 1`, `E χ² = 0`. For `N = 0` every index set is empty and the law is the Dirac
mass on the empty matrix. No contract or cited input is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.CEH

open MeasureTheory ProbabilityTheory
open BlockBand.External BlockBand.Counting
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-!
### Entry distributions
-/

/-- The off-diagonal entry measure: the standard circular complex Gaussian. -/
def circularMeasure : Measure ℂ := standardCircularGaussian.map circularGaussianCoordinate

/-- The circular coordinate `(x, y) ↦ x + i y` is measurable. -/
theorem measurable_circularGaussianCoordinate : Measurable circularGaussianCoordinate := by
  unfold circularGaussianCoordinate
  fun_prop

/-- The circular entry measure is a probability measure. -/
theorem circularMeasure_isProbability : IsProbabilityMeasure circularMeasure :=
  (Measure.isProbabilityMeasure_map_iff
    measurable_circularGaussianCoordinate.aemeasurable).mpr inferInstance

/-- `N(0,1)` is a probability measure (explicit instance). -/
theorem gaussianReal_one_isProbability : IsProbabilityMeasure (gaussianReal 0 1) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 1

/-- Every finite moment of the circular coordinate under the product law. -/
theorem memLp_circularGaussianCoordinate (p : ℝ≥0) :
    MemLp circularGaussianCoordinate p standardCircularGaussian := by
  have : IsProbabilityMeasure standardCircularReal := by
    unfold standardCircularReal
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have h0 : MemLp (fun x : ℝ => (x : ℂ)) p standardCircularReal :=
    (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) p).ofReal
  have h1 : MemLp (fun z : ℝ × ℝ => (z.1 : ℂ)) p standardCircularGaussian :=
    h0.comp_measurePreserving (measurePreserving_fst (μ := standardCircularReal)
      (ν := standardCircularReal))
  have h2 : MemLp (fun z : ℝ × ℝ => (z.2 : ℂ)) p standardCircularGaussian :=
    h0.comp_measurePreserving (measurePreserving_snd (μ := standardCircularReal)
      (ν := standardCircularReal))
  exact h1.add (h2.const_mul Complex.I)

/-- All absolute moments `E|χ_od|^p` are finite. -/
theorem integrable_norm_pow_circular (p : ℕ) :
    Integrable (fun x : ℂ => ‖x‖ ^ p) circularMeasure := by
  have := circularMeasure_isProbability
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · unfold circularMeasure
    rw [integrable_map_measure (by fun_prop)
      measurable_circularGaussianCoordinate.aemeasurable]
    exact (memLp_circularGaussianCoordinate p).integrable_norm_pow hp.ne'

/-- All absolute moments of `N(0,1)` are finite. -/
theorem integrable_norm_pow_gaussianReal_one (p : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ p) (gaussianReal 0 1) := by
  have := gaussianReal_one_isProbability
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact (memLp_id_gaussianReal (μ := 0) (v := 1) p).integrable_norm_pow hp.ne'

/-- The circular entry is integrable. -/
theorem integrable_id_circular : Integrable (fun x : ℂ => x) circularMeasure := by
  have h := integrable_norm_pow_circular 1
  simp only [pow_one] at h
  exact (integrable_norm_iff (by fun_prop)).mp h

/-- The `N(0,1)` entry is integrable. -/
theorem integrable_id_gaussianReal_one : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := by
  have h := integrable_norm_pow_gaussianReal_one 1
  simp only [pow_one] at h
  exact (integrable_norm_iff (by fun_prop)).mp h

/-- `χ_od²` is integrable. -/
theorem integrable_sq_circular : Integrable (fun x : ℂ => x ^ 2) circularMeasure := by
  have h := integrable_norm_pow_circular 2
  simp only [← norm_pow] at h
  exact (integrable_norm_iff (by fun_prop)).mp h

/-- `|x + i y|² = x² + y²`. -/
theorem norm_sq_circularGaussianCoordinate (z : ℝ × ℝ) :
    ‖circularGaussianCoordinate z‖ ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circularGaussianCoordinate]
  ring

/-- Integrating a function of the real part against the product law. -/
theorem integral_fst_standardCircular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ z : ℝ × ℝ, f z.1 ∂standardCircularGaussian = ∫ x, f x ∂standardCircularReal := by
  have : IsProbabilityMeasure standardCircularReal := by
    unfold standardCircularReal
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  unfold standardCircularGaussian
  rw [integral_fun_fst]
  simp

/-- Integrating a function of the imaginary part against the product law. -/
theorem integral_snd_standardCircular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ z : ℝ × ℝ, f z.2 ∂standardCircularGaussian = ∫ x, f x ∂standardCircularReal := by
  have : IsProbabilityMeasure standardCircularReal := by
    unfold standardCircularReal
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  unfold standardCircularGaussian
  rw [integral_fun_snd]
  simp

/-- The real component law `N(0,1/2)` is centered. -/
theorem integral_ofReal_standardCircularReal :
    ∫ x : ℝ, (x : ℂ) ∂standardCircularReal = 0 := by
  rw [integral_complex_ofReal]
  simp [standardCircularReal, integral_id_gaussianReal]

/-- The real part is integrable under the product law. -/
theorem integrable_fst_ofReal_standardCircular :
    Integrable (fun z : ℝ × ℝ => (z.1 : ℂ)) standardCircularGaussian :=
  memLp_one_iff_integrable.mp
    (((memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) 1).ofReal (K := ℂ)).comp_measurePreserving
      (measurePreserving_fst (μ := standardCircularReal) (ν := standardCircularReal)))

/-- The imaginary part is integrable under the product law. -/
theorem integrable_snd_ofReal_standardCircular :
    Integrable (fun z : ℝ × ℝ => (z.2 : ℂ)) standardCircularGaussian :=
  memLp_one_iff_integrable.mp
    (((memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) 1).ofReal (K := ℂ)).comp_measurePreserving
      (measurePreserving_snd (μ := standardCircularReal) (ν := standardCircularReal)))

/-- `E χ_od = 0`. -/
theorem integral_id_circular : ∫ x : ℂ, x ∂circularMeasure = 0 := by
  unfold circularMeasure
  rw [integral_map measurable_circularGaussianCoordinate.aemeasurable (by fun_prop)]
  unfold circularGaussianCoordinate
  rw [integral_add integrable_fst_ofReal_standardCircular
    (integrable_snd_ofReal_standardCircular.const_mul Complex.I), integral_const_mul]
  have h1 := integral_fst_standardCircular (fun x : ℝ => (x : ℂ))
  have h2 := integral_snd_standardCircular (fun x : ℝ => (x : ℂ))
  rw [h1, h2, integral_ofReal_standardCircularReal]
  simp

/-- `E|χ_od|² = 1`. -/
theorem integral_norm_sq_circular : ∫ x : ℂ, ‖x‖ ^ 2 ∂circularMeasure = 1 := by
  unfold circularMeasure
  rw [integral_map measurable_circularGaussianCoordinate.aemeasurable (by fun_prop)]
  simp_rw [norm_sq_circularGaussianCoordinate]
  exact integral_circular_normSq

/-- `(x + i y)² = (x² - y²) + 2 i x y`. -/
theorem sq_circularGaussianCoordinate (z : ℝ × ℝ) :
    circularGaussianCoordinate z ^ 2 =
      ((z.1 ^ 2 - z.2 ^ 2 : ℝ) : ℂ) + (2 * Complex.I) * ((z.1 * z.2 : ℝ) : ℂ) := by
  unfold circularGaussianCoordinate
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `E χ_od² = 0` (so `σ = 0`). -/
theorem integral_sq_circular : ∫ x : ℂ, x ^ 2 ∂circularMeasure = 0 := by
  have : IsProbabilityMeasure standardCircularReal := by
    unfold standardCircularReal
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) standardCircularReal := integrable_const 1
  have hx : Integrable (fun z : ℝ × ℝ => z.1 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using integrable_sq_standardCircularReal.smul_prod h1
  have hy : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using h1.smul_prod integrable_sq_standardCircularReal
  have hid : Integrable (fun x : ℝ => x) standardCircularReal := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) 1)
    exact memLp_one_iff_integrable.mp h
  have hxy : Integrable (fun z : ℝ × ℝ => z.1 * z.2) standardCircularGaussian := by
    simpa [standardCircularGaussian] using hid.mul_prod hid
  unfold circularMeasure
  rw [integral_map measurable_circularGaussianCoordinate.aemeasurable (by fun_prop)]
  simp_rw [sq_circularGaussianCoordinate]
  have hA : Integrable (fun z : ℝ × ℝ => ((z.1 ^ 2 - z.2 ^ 2 : ℝ) : ℂ))
      standardCircularGaussian := (hx.sub hy).ofReal
  have hB : Integrable (fun z : ℝ × ℝ => (2 * Complex.I) * ((z.1 * z.2 : ℝ) : ℂ))
      standardCircularGaussian := (hxy.ofReal (𝕜 := ℂ)).const_mul _
  rw [integral_add hA hB, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_sub hx hy]
  have e1 := integral_fst_standardCircular (fun x : ℝ => x ^ 2)
  have e2 := integral_snd_standardCircular (fun x : ℝ => x ^ 2)
  have e3 : ∫ z : ℝ × ℝ, z.1 * z.2 ∂standardCircularGaussian = 0 := by
    unfold standardCircularGaussian
    rw [integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y)]
    simp [standardCircularReal, integral_id_gaussianReal]
  rw [e1, e2, e3]
  simp

/-- The CEH entry data of the normalized GUE: diagonal `N(0,1)`, off-diagonal standard
circular complex Gaussian, moment constants `C_p = E|χ_d|^p + E|χ_od|^p`. -/
def gueEntryDistributions : CEH.EntryDistributions where
  diagonal := ⟨gaussianReal 0 1, gaussianReal_one_isProbability⟩
  offDiagonal := ⟨circularMeasure, circularMeasure_isProbability⟩
  momentBound p := (∫ x, ‖x‖ ^ p ∂gaussianReal 0 1) + ∫ x, ‖x‖ ^ p ∂circularMeasure
  momentBound_nonneg p :=
    add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
  diagonal_integrable := integrable_id_gaussianReal_one
  offDiagonal_integrable := integrable_id_circular
  diagonal_centered := integral_id_gaussianReal
  offDiagonal_centered := integral_id_circular
  diagonal_moments_integrable := integrable_norm_pow_gaussianReal_one
  offDiagonal_moments_integrable := integrable_norm_pow_circular
  moments _ := le_rfl
  variance := integral_norm_sq_circular
  square_integrable := integrable_sq_circular
  sigma_lt_one := by
    change ‖∫ x : ℂ, x ^ 2 ∂circularMeasure‖ < 1
    rw [integral_sq_circular]
    simp

/-!
### The GUE coordinate law
-/

/-- Hermitian reconstruction into the CEH sample space. -/
def gueSample {N : ℕ} (z : Johansson.UpperPair N → ℝ × ℝ) : CEH.SourceHermitian N :=
  ⟨(Johansson.gaussianMatrix z).1, (Johansson.gaussianMatrix z).2⟩

/-- Hermitian reconstruction is measurable. -/
theorem measurable_gueSample (N : ℕ) : Measurable (@gueSample N) :=
  (measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix).subtype_mk

/-- Unfolding of `gueSourceLaw` through `gueSample`. -/
theorem gueSourceLaw_eq (N : ℕ) : gueSourceLaw N =
    (Johansson.coordinateMeasure N (1 / (N : ℝ≥0))).map gueSample := rfl

/-- `gueSourceLaw N` is a probability measure (every `N`, including `0`). -/
theorem gueSourceLaw_isProbability (N : ℕ) : IsProbabilityMeasure (gueSourceLaw N) := by
  have := Johansson.coordinateMeasure_probability N (1 / (N : ℝ≥0))
  rw [gueSourceLaw_eq]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_gueSample N).aemeasurable).mpr
    inferInstance

/-- The scaled upper entry carried by one coordinate pair. -/
def scaledUpperValue (N : ℕ) (q : Johansson.UpperPair N) (p : ℝ × ℝ) : ℂ :=
  (Real.sqrt (N : ℝ) : ℂ) * if q.1.1 = q.1.2 then (p.1 : ℂ) else Johansson.complexPair p

/-- The scaled upper value is measurable. -/
theorem measurable_scaledUpperValue (N : ℕ) (q : Johansson.UpperPair N) :
    Measurable (scaledUpperValue N q) := by
  unfold scaledUpperValue Johansson.complexPair
  split_ifs <;> fun_prop

/-- The scaled `(q.1, q.2)` entry of the sample depends only on coordinate `q`. -/
theorem gueSample_upper {N : ℕ} (z : Johansson.UpperPair N → ℝ × ℝ)
    (q : Johansson.UpperPair N) :
    (Real.sqrt (N : ℝ) : ℂ) * (gueSample z).1 q.1.1 q.1.2 = scaledUpperValue N q (z q) := by
  rcases q with ⟨⟨i, j⟩, hij⟩
  by_cases h : i = j
  · subst h
    simp [gueSample, Johansson.gaussianMatrix, Johansson.gaussianMatrixRaw, scaledUpperValue]
  · simp [gueSample, Johansson.gaussianMatrix, Johansson.gaussianMatrixRaw, scaledUpperValue,
      h, hij]

/-- Each scaled matrix entry is measurable on the Hermitian sample space. -/
theorem measurable_scaledEntry (N : ℕ) (a b : Fin N) :
    Measurable (fun W : CEH.SourceHermitian N => (Real.sqrt (N : ℝ) : ℂ) * W.1 a b) := by
  have h : Measurable (fun W : CEH.SourceHermitian N => W.1 a b) :=
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_subtype_coe)
  exact h.const_mul _

/-- Transfer of a law along a measurable reconstruction map. -/
theorem hasLaw_map_of_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {φ : α → β} {f : β → γ} {ν : Measure γ}
    (hφ : Measurable φ) (hf : Measurable f) (h : HasLaw (f ∘ φ) ν μ) :
    HasLaw f ν (μ.map φ) :=
  ⟨hf.aemeasurable, by rw [Measure.map_map hf hφ]; exact h.map_eq⟩

/-- Independence of the `√N`-scaled upper entries under `gueSourceLaw N`. -/
theorem gue_upper_independent (N : ℕ) :
    iIndepFun (fun q : CEH.SourceUpperPair N => fun W : CEH.SourceHermitian N =>
      ((Real.sqrt (N : ℝ) : ℂ) * W.1 q.1.1 q.1.2)) (gueSourceLaw N) := by
  have hP := Johansson.coordinateMeasure_probability N (1 / (N : ℝ≥0))
  have hU := Johansson.upperEntryMeasure_probability (N := N) (1 / (N : ℝ≥0))
  have hG := gueSourceLaw_isProbability N
  have hmeas : ∀ q : CEH.SourceUpperPair N, Measurable (fun W : CEH.SourceHermitian N =>
      ((Real.sqrt (N : ℝ) : ℂ) * W.1 q.1.1 q.1.2)) := fun q => measurable_scaledEntry N _ _
  have h0 : iIndepFun (fun (q : Johansson.UpperPair N) (z : Johansson.UpperPair N → ℝ × ℝ) =>
      scaledUpperValue N q (z q)) (Johansson.coordinateMeasure N (1 / (N : ℝ≥0))) :=
    iIndepFun_pi (fun q => (measurable_scaledUpperValue N q).aemeasurable)
  have h1 : iIndepFun (fun (q : CEH.SourceUpperPair N) (z : Johansson.UpperPair N → ℝ × ℝ) =>
      (Real.sqrt (N : ℝ) : ℂ) * (gueSample z).1 q.1.1 q.1.2)
      (Johansson.coordinateMeasure N (1 / (N : ℝ≥0))) := by
    convert h0 using 1
    funext q z
    exact gueSample_upper z q
  have h2 := (iIndepFun_iff_map_fun_eq_pi_map
    (f := fun (q : CEH.SourceUpperPair N) (z : Johansson.UpperPair N → ℝ × ℝ) =>
      (Real.sqrt (N : ℝ) : ℂ) * (gueSample z).1 q.1.1 q.1.2)
    (fun q => ((hmeas q).comp (measurable_gueSample N)).aemeasurable)).mp h1
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun q => (hmeas q).aemeasurable)]
  rw [gueSourceLaw_eq, Measure.map_map (measurable_pi_iff.mpr hmeas) (measurable_gueSample N)]
  simp_rw [Measure.map_map (hmeas _) (measurable_gueSample N)]
  exact h2

/-- Variance bookkeeping for the diagonal: `(√N)² ⋅ (1/N) = 1` in `ℝ≥0`, for `N > 0`. -/
theorem sqrt_sq_mul_inv {N : ℕ} (hN : 0 < N) :
    NNReal.mk (Real.sqrt (N : ℝ) ^ 2) (sq_nonneg _) * (1 / (N : ℝ≥0)) = 1 := by
  apply NNReal.eq
  have : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  rw [Real.sq_sqrt this.le]
  field_simp

/-- Variance bookkeeping for off-diagonal real components, `N > 0`. -/
theorem sqrt_sq_mul_half_inv {N : ℕ} (hN : 0 < N) :
    NNReal.mk (Real.sqrt (N : ℝ) ^ 2) (sq_nonneg _) * (1 / (N : ℝ≥0) / 2) = 1 / 2 := by
  apply NNReal.eq
  have : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast,
    NNReal.coe_ofNat]
  rw [Real.sq_sqrt this.le]
  field_simp

/-- Diagonal law: `√N ⋅ Re W_aa ~ N(0,1)` under `gueSourceLaw N`. -/
theorem gue_diagonal_law (N : ℕ) (a : Fin N) :
    HasLaw (fun W : CEH.SourceHermitian N => Real.sqrt (N : ℝ) * (W.1 a a).re)
      (gaussianReal 0 1) (gueSourceLaw N) := by
  have hN : 0 < N := Fin.pos a
  have hmeas : Measurable (fun W : CEH.SourceHermitian N => Real.sqrt (N : ℝ) * (W.1 a a).re) :=
    (Complex.measurable_re.comp
      ((measurable_pi_apply a).comp ((measurable_pi_apply a).comp measurable_subtype_coe))).const_mul _
  rw [gueSourceLaw_eq]
  apply hasLaw_map_of_comp (measurable_gueSample N) hmeas
  let q : Johansson.UpperPair N := ⟨(a, a), le_rfl⟩
  have hfun : (fun W : CEH.SourceHermitian N => Real.sqrt (N : ℝ) * (W.1 a a).re) ∘ gueSample =
      (fun x : ℝ => Real.sqrt (N : ℝ) * x) ∘ (fun p : ℝ × ℝ => p.1) ∘
        (fun z : Johansson.UpperPair N → ℝ × ℝ => z q) := by
    funext z
    simp [gueSample, Johansson.gaussianMatrix, Johansson.gaussianMatrixRaw, q]
  rw [hfun]
  have hU := Johansson.upperEntryMeasure_probability (N := N) (1 / (N : ℝ≥0))
  have hq : HasLaw (fun z : Johansson.UpperPair N → ℝ × ℝ => z q)
      (Johansson.upperEntryMeasure (1 / (N : ℝ≥0)) q)
      (Johansson.coordinateMeasure N (1 / (N : ℝ≥0))) :=
    (measurePreserving_eval _ q).hasLaw
  have hfst : HasLaw (fun p : ℝ × ℝ => p.1) (gaussianReal 0 (1 / (N : ℝ≥0)))
      (Johansson.upperEntryMeasure (1 / (N : ℝ≥0)) q) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    simp only [Johansson.upperEntryMeasure, q, ↓reduceIte]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    exact Measure.map_id
  have hscale : HasLaw (fun x : ℝ => Real.sqrt (N : ℝ) * x) (gaussianReal 0 1)
      (gaussianReal 0 (1 / (N : ℝ≥0))) := by
    refine ⟨(measurable_const_mul _).aemeasurable, ?_⟩
    rw [gaussianReal_map_const_mul, mul_zero, sqrt_sq_mul_inv hN]
  exact hscale.comp (hfst.comp hq)

/-- Off-diagonal law: `√N ⋅ W_ab` is standard circular under `gueSourceLaw N` for `a < b`. -/
theorem gue_offDiagonal_law (N : ℕ) (a b : Fin N) (hab : a < b) :
    HasLaw (fun W : CEH.SourceHermitian N => (Real.sqrt (N : ℝ) : ℂ) * W.1 a b)
      circularMeasure (gueSourceLaw N) := by
  have hN : 0 < N := Fin.pos a
  rw [gueSourceLaw_eq]
  apply hasLaw_map_of_comp (measurable_gueSample N) (measurable_scaledEntry N a b)
  let q : Johansson.UpperPair N := ⟨(a, b), hab.le⟩
  have hne : a ≠ b := hab.ne
  have hfun : (fun W : CEH.SourceHermitian N => (Real.sqrt (N : ℝ) : ℂ) * W.1 a b) ∘ gueSample =
      circularGaussianCoordinate ∘
        (Prod.map (fun x : ℝ => Real.sqrt (N : ℝ) * x) (fun x : ℝ => Real.sqrt (N : ℝ) * x)) ∘
        (fun z : Johansson.UpperPair N → ℝ × ℝ => z q) := by
    funext z
    simp [gueSample, Johansson.gaussianMatrix, Johansson.gaussianMatrixRaw, q, hne, hab.le,
      Johansson.complexPair, circularGaussianCoordinate]
    ring
  rw [hfun]
  have hU := Johansson.upperEntryMeasure_probability (N := N) (1 / (N : ℝ≥0))
  have hq : HasLaw (fun z : Johansson.UpperPair N → ℝ × ℝ => z q)
      (Johansson.upperEntryMeasure (1 / (N : ℝ≥0)) q)
      (Johansson.coordinateMeasure N (1 / (N : ℝ≥0))) :=
    (measurePreserving_eval _ q).hasLaw
  have hprod : HasLaw
      (Prod.map (fun x : ℝ => Real.sqrt (N : ℝ) * x) (fun x : ℝ => Real.sqrt (N : ℝ) * x))
      standardCircularGaussian (Johansson.upperEntryMeasure (1 / (N : ℝ≥0)) q) := by
    refine ⟨(measurable_fst.const_mul _).prodMk (measurable_snd.const_mul _) |>.aemeasurable, ?_⟩
    simp only [Johansson.upperEntryMeasure, q, hne, ↓reduceIte]
    rw [← Measure.map_prod_map _ _ (measurable_const_mul _) (measurable_const_mul _),
      gaussianReal_map_const_mul, mul_zero, sqrt_sq_mul_half_inv hN]
    rfl
  have hc : HasLaw circularGaussianCoordinate circularMeasure standardCircularGaussian :=
    ⟨measurable_circularGaussianCoordinate.aemeasurable, rfl⟩
  exact hc.comp (hprod.comp hq)

/-- The normalized GUE as a CEH Wigner family (`σ = 0`). -/
def gueWignerFamily : CEH.WignerFamily where
  entries := gueEntryDistributions
  law N := ⟨gueSourceLaw N, gueSourceLaw_isProbability N⟩
  upper_independent N _ := gue_upper_independent N
  diagonal_law N a := gue_diagonal_law N a
  offDiagonal_law N a b hab := gue_offDiagonal_law N a b hab

/-- The law of `gueWignerFamily` in dimension `N` is `gueSourceLaw N`. -/
theorem gueWignerFamily_law (N : ℕ) :
    (gueWignerFamily.law N : Measure (CEH.SourceHermitian N)) = gueSourceLaw N := rfl

/-- The CEH Wigner family `gueWignerFamily` (diagonal entry law `N(0,1)`, off-diagonal
standard circular complex Gaussian, `E χ_od² = 0`) has law exactly `gueSourceLaw N = GUE_N(1/N)`
in every dimension `N`, including `N = 0`. -/
theorem gueWignerFamilyAdapter_holds : GUEWignerFamilyAdapter :=
  ⟨gueWignerFamily, gueWignerFamily_law⟩

end BlockBand.Adapters.CEH
