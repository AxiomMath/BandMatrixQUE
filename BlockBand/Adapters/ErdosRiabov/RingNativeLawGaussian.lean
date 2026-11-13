module

public import Mathlib
public import BlockBand.External.ErdosRiabov.NativeModel
public import BlockBand.Counting.CircularGaussianMoments

/-!
# Standardized Gaussian coordinates for the ring as an Erdős–Riabov law

The coordinate space carries one standard real pair per upper index of `Fin N`. This file
proves the one-site marginals, moments and moment bounds of the standardized entries
(real Gaussian on the diagonal, circular complex Gaussian off it), and computes their joint
characteristic function.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open MeasureTheory ProbabilityTheory BlockBand.External BlockBand.Counting
open scoped ComplexConjugate NNReal

instance ringUpperPairFintype (N : ℕ) : Fintype (ErdosRiabov.UpperPair N) := by
  unfold ErdosRiabov.UpperPair
  infer_instance

instance ringUpperPairDecidableEq (N : ℕ) : DecidableEq (ErdosRiabov.UpperPair N) := by
  unfold ErdosRiabov.UpperPair
  infer_instance

/-- The coordinate space: one real pair per upper index. -/
abbrev RingOmega (N : ℕ) := ErdosRiabov.UpperPair N → ℝ × ℝ

/-- The product law of independent standard circular pairs. -/
def ringOmegaMeasure (N : ℕ) : Measure (RingOmega N) :=
  Measure.pi (fun _ => standardCircularGaussian)

instance ringOmegaMeasure_isProbability (N : ℕ) : IsProbabilityMeasure (ringOmegaMeasure N) := by
  unfold ringOmegaMeasure
  infer_instance

/-- The standardized real diagonal value `√2 w₁` (variance one). -/
def diagValue (w : ℝ × ℝ) : ℂ := ((Real.sqrt 2 * w.1 : ℝ) : ℂ)

/-- The standardized entry. -/
def stdEntry {N : ℕ} (ω : RingOmega N) (i j : Fin N) : ℂ :=
  if h : i = j then diagValue (ω ⟨(i, j), h.le⟩)
  else if h' : i < j then circularGaussianCoordinate (ω ⟨(i, j), h'.le⟩)
  else conj (circularGaussianCoordinate (ω ⟨(j, i), not_lt.mp h'⟩))

/-- The upper value carried by one coordinate pair. -/
def upperValue {N : ℕ} (q : ErdosRiabov.UpperPair N) (w : ℝ × ℝ) : ℂ :=
  if q.1.1 = q.1.2 then diagValue w else circularGaussianCoordinate w

theorem continuous_diagValue : Continuous diagValue := by
  unfold diagValue
  fun_prop

theorem continuous_circular : Continuous circularGaussianCoordinate := by
  unfold circularGaussianCoordinate
  fun_prop

theorem measurable_upperValue {N : ℕ} (q : ErdosRiabov.UpperPair N) :
    Measurable (upperValue q) := by
  unfold upperValue
  split_ifs
  · exact continuous_diagValue.measurable
  · exact continuous_circular.measurable

theorem stdEntry_upper {N : ℕ} (ω : RingOmega N) (q : ErdosRiabov.UpperPair N) :
    stdEntry ω q.1.1 q.1.2 = upperValue q (ω q) := by
  obtain ⟨⟨i, j⟩, hij⟩ := q
  unfold stdEntry upperValue
  dsimp only
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (lt_of_le_of_ne hij h1) h2

theorem measurable_stdEntry {N : ℕ} (i j : Fin N) :
    Measurable (fun ω : RingOmega N => stdEntry ω i j) := by
  unfold stdEntry
  split_ifs
  · exact continuous_diagValue.measurable.comp (measurable_pi_apply _)
  · exact continuous_circular.measurable.comp (measurable_pi_apply _)
  · exact (Complex.continuous_conj.comp continuous_circular).measurable.comp
      (measurable_pi_apply _)

theorem diagValue_conj (w : ℝ × ℝ) : conj (diagValue w) = diagValue w := by
  unfold diagValue
  exact Complex.conj_ofReal _

/-- Hermitian symmetry of the standardized entries, for every sample. -/
theorem stdEntry_conj {N : ℕ} (ω : RingOmega N) (i j : Fin N) :
    conj (stdEntry ω j i) = stdEntry ω i j := by
  by_cases h : i = j
  · subst h
    simp [stdEntry, diagValue_conj]
  · have h' : j ≠ i := Ne.symm h
    by_cases hlt : i < j
    · have hn : ¬ j < i := not_lt.mpr hlt.le
      simp [stdEntry, h, h', hlt, hn]
    · have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) h'
      simp [stdEntry, h, h', hlt, hji]

/-- Every standardized entry is one of three fixed functions of one coordinate pair. -/
theorem stdEntry_cases {N : ℕ} (i j : Fin N) : ∃ (q : ErdosRiabov.UpperPair N)
    (F : ℝ × ℝ → ℂ), (∀ ω : RingOmega N, stdEntry ω i j = F (ω q)) ∧
      ((i = j ∧ F = diagValue) ∨ (i ≠ j ∧ F = circularGaussianCoordinate) ∨
        (i ≠ j ∧ F = fun w => conj (circularGaussianCoordinate w))) := by
  by_cases h : i = j
  · exact ⟨⟨(i, j), h.le⟩, diagValue, fun ω => by simp [stdEntry, h], Or.inl ⟨h, rfl⟩⟩
  · by_cases hlt : i < j
    · exact ⟨⟨(i, j), hlt.le⟩, circularGaussianCoordinate,
        fun ω => by simp [stdEntry, h, hlt], Or.inr (Or.inl ⟨h, rfl⟩)⟩
    · exact ⟨⟨(j, i), not_lt.mp hlt⟩, fun w => conj (circularGaussianCoordinate w),
        fun ω => by simp [stdEntry, h, hlt], Or.inr (Or.inr ⟨h, rfl⟩)⟩

/-!
### Marginals
-/

theorem measurePreserving_ringOmega_eval {N : ℕ} (q : ErdosRiabov.UpperPair N) :
    MeasurePreserving (fun ω : RingOmega N => ω q) (ringOmegaMeasure N)
      standardCircularGaussian :=
  measurePreserving_eval (fun _ : ErdosRiabov.UpperPair N => standardCircularGaussian) q

theorem integral_ringOmega_eval {N : ℕ} (q : ErdosRiabov.UpperPair N) {g : ℝ × ℝ → ℂ}
    (hg : Continuous g) :
    (∫ ω, g (ω q) ∂ringOmegaMeasure N) = ∫ w, g w ∂standardCircularGaussian := by
  have hmp := measurePreserving_ringOmega_eval (N := N) q
  rw [← hmp.map_eq, integral_map (measurable_pi_apply q).aemeasurable
    hg.aestronglyMeasurable]

theorem integral_ringOmega_eval_real {N : ℕ} (q : ErdosRiabov.UpperPair N) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) :
    (∫ ω, g (ω q) ∂ringOmegaMeasure N) = ∫ w, g w ∂standardCircularGaussian := by
  have hmp := measurePreserving_ringOmega_eval (N := N) q
  rw [← hmp.map_eq, integral_map (measurable_pi_apply q).aemeasurable
    hg.aestronglyMeasurable]

theorem integrable_ringOmega_eval {N : ℕ} (q : ErdosRiabov.UpperPair N) {E : Type*}
    [NormedAddCommGroup E] {g : ℝ × ℝ → E} (hg : Continuous g)
    (hint : Integrable g standardCircularGaussian) :
    Integrable (fun ω : RingOmega N => g (ω q)) (ringOmegaMeasure N) :=
  ((measurePreserving_ringOmega_eval (N := N) q).integrable_comp
    hg.aestronglyMeasurable).mpr hint

/-!
### One-site moments
-/

theorem memLp_fst (r : ℝ≥0) :
    MemLp (fun w : ℝ × ℝ => w.1) r standardCircularGaussian := by
  have : IsProbabilityMeasure (gaussianReal 0 (1 / 2 : ℝ≥0)) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  unfold standardCircularGaussian standardCircularReal
  exact (memLp_id_gaussianReal r).comp_measurePreserving measurePreserving_fst

theorem memLp_snd (r : ℝ≥0) :
    MemLp (fun w : ℝ × ℝ => w.2) r standardCircularGaussian := by
  have : IsProbabilityMeasure (gaussianReal 0 (1 / 2 : ℝ≥0)) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  unfold standardCircularGaussian standardCircularReal
  exact (memLp_id_gaussianReal r).comp_measurePreserving measurePreserving_snd

theorem memLp_diagValue (r : ℝ≥0) : MemLp diagValue r standardCircularGaussian := by
  have h : MemLp (fun w : ℝ × ℝ => ((Real.sqrt 2 * w.1 : ℝ) : ℂ)) r standardCircularGaussian :=
    ((memLp_fst r).const_mul (Real.sqrt 2)).ofReal
  exact h

theorem memLp_circular (r : ℝ≥0) :
    MemLp circularGaussianCoordinate r standardCircularGaussian := by
  have h1 : MemLp (fun w : ℝ × ℝ => ((w.1 : ℝ) : ℂ)) r standardCircularGaussian :=
    (memLp_fst r).ofReal
  have h2 : MemLp (fun w : ℝ × ℝ => Complex.I * ((w.2 : ℝ) : ℂ)) r standardCircularGaussian :=
    (memLp_snd r).ofReal.const_mul Complex.I
  have h3 := h1.add h2
  exact h3

theorem integral_fst_circular : (∫ w : ℝ × ℝ, w.1 ∂standardCircularGaussian) = 0 := by
  unfold standardCircularGaussian standardCircularReal
  rw [integral_fun_fst (fun x : ℝ => x), integral_id_gaussianReal, smul_zero]

theorem integral_snd_circular : (∫ w : ℝ × ℝ, w.2 ∂standardCircularGaussian) = 0 := by
  unfold standardCircularGaussian standardCircularReal
  rw [integral_fun_snd (fun x : ℝ => x), integral_id_gaussianReal, smul_zero]

theorem integral_fst_sq_circular :
    (∫ w : ℝ × ℝ, w.1 ^ 2 ∂standardCircularGaussian) = 1 / 2 := by
  unfold standardCircularGaussian
  rw [integral_fun_fst (fun x : ℝ => x ^ 2), integral_sq_standardCircularReal]
  simp

theorem integral_snd_sq_circular :
    (∫ w : ℝ × ℝ, w.2 ^ 2 ∂standardCircularGaussian) = 1 / 2 := by
  unfold standardCircularGaussian
  rw [integral_fun_snd (fun x : ℝ => x ^ 2), integral_sq_standardCircularReal]
  simp

theorem integrable_fst_sq : Integrable (fun w : ℝ × ℝ => w.1 ^ 2) standardCircularGaussian := by
  have h := (memLp_fst 2).integrable_norm_pow (p := 2) (by norm_num)
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem integrable_snd_sq : Integrable (fun w : ℝ × ℝ => w.2 ^ 2) standardCircularGaussian := by
  have h := (memLp_snd 2).integrable_norm_pow (p := 2) (by norm_num)
  simpa [Real.norm_eq_abs, sq_abs] using h

theorem integral_diagValue : (∫ w, diagValue w ∂standardCircularGaussian) = 0 := by
  unfold diagValue
  rw [integral_complex_ofReal, integral_const_mul, integral_fst_circular, mul_zero,
    Complex.ofReal_zero]

theorem integral_circular : (∫ w, circularGaussianCoordinate w ∂standardCircularGaussian) = 0 := by
  unfold circularGaussianCoordinate
  have h1 : Integrable (fun w : ℝ × ℝ => ((w.1 : ℝ) : ℂ)) standardCircularGaussian :=
    (memLp_one_iff_integrable.mp (memLp_fst 1)).ofReal
  have h2 : Integrable (fun w : ℝ × ℝ => Complex.I * ((w.2 : ℝ) : ℂ)) standardCircularGaussian :=
    (memLp_one_iff_integrable.mp (memLp_snd 1)).ofReal.const_mul Complex.I
  rw [integral_add h1 h2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_fst_circular, integral_snd_circular]
  simp

theorem norm_diagValue_sq (w : ℝ × ℝ) : ‖diagValue w‖ ^ 2 = 2 * w.1 ^ 2 := by
  unfold diagValue
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by norm_num)]

theorem norm_circular_sq (w : ℝ × ℝ) :
    ‖circularGaussianCoordinate w‖ ^ 2 = w.1 ^ 2 + w.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circularGaussianCoordinate]
  ring

theorem integral_norm_sq_diagValue :
    (∫ w, ‖diagValue w‖ ^ 2 ∂standardCircularGaussian) = 1 := by
  simp_rw [norm_diagValue_sq]
  rw [integral_const_mul, integral_fst_sq_circular]
  norm_num

theorem integral_norm_sq_circular :
    (∫ w, ‖circularGaussianCoordinate w‖ ^ 2 ∂standardCircularGaussian) = 1 := by
  simp_rw [norm_circular_sq]
  exact integral_circular_normSq

theorem circular_sq (w : ℝ × ℝ) :
    circularGaussianCoordinate w ^ 2 =
      ((w.1 ^ 2 - w.2 ^ 2 : ℝ) : ℂ) + ((2 * (w.1 * w.2) : ℝ) : ℂ) * Complex.I := by
  unfold circularGaussianCoordinate
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integral_fst_mul_snd :
    (∫ w : ℝ × ℝ, w.1 * w.2 ∂standardCircularGaussian) = 0 := by
  unfold standardCircularGaussian
  rw [integral_prod_mul (fun x : ℝ => x) (fun y : ℝ => y)]
  unfold standardCircularReal
  rw [integral_id_gaussianReal, zero_mul]

theorem integrable_fst_mul_snd :
    Integrable (fun w : ℝ × ℝ => w.1 * w.2) standardCircularGaussian := by
  have h1 : Integrable (fun x : ℝ => x) standardCircularReal := by
    unfold standardCircularReal
    exact memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  unfold standardCircularGaussian
  simpa using h1.smul_prod h1

theorem integral_circular_sq :
    (∫ w, circularGaussianCoordinate w ^ 2 ∂standardCircularGaussian) = 0 := by
  simp_rw [circular_sq]
  have hA : Integrable (fun w : ℝ × ℝ => w.1 ^ 2 - w.2 ^ 2) standardCircularGaussian :=
    integrable_fst_sq.sub integrable_snd_sq
  have hB : Integrable (fun w : ℝ × ℝ => 2 * (w.1 * w.2)) standardCircularGaussian :=
    integrable_fst_mul_snd.const_mul 2
  have hA' : Integrable (fun w : ℝ × ℝ => ((w.1 ^ 2 - w.2 ^ 2 : ℝ) : ℂ))
      standardCircularGaussian := hA.ofReal
  have hB' : Integrable (fun w : ℝ × ℝ => ((2 * (w.1 * w.2) : ℝ) : ℂ) * Complex.I)
      standardCircularGaussian := hB.ofReal.mul_const Complex.I
  rw [integral_add hA' hB', integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, integral_sub integrable_fst_sq integrable_snd_sq,
    integral_const_mul, integral_fst_sq_circular, integral_snd_sq_circular,
    integral_fst_mul_snd]
  simp

theorem integrable_circular_sq :
    Integrable (fun w => circularGaussianCoordinate w ^ 2) standardCircularGaussian := by
  simp_rw [circular_sq]
  have hA' : Integrable (fun w : ℝ × ℝ => ((w.1 ^ 2 - w.2 ^ 2 : ℝ) : ℂ))
      standardCircularGaussian := (integrable_fst_sq.sub integrable_snd_sq).ofReal
  have hB' : Integrable (fun w : ℝ × ℝ => ((2 * (w.1 * w.2) : ℝ) : ℂ) * Complex.I)
      standardCircularGaussian := (integrable_fst_mul_snd.const_mul 2).ofReal.mul_const Complex.I
  exact hA'.add hB'

/-- The `N`-independent moment bound: the larger one-site moment. -/
def ringMomentBound (r : ℕ) : ℝ :=
  max (∫ w, ‖diagValue w‖ ^ r ∂standardCircularGaussian)
    (∫ w, ‖circularGaussianCoordinate w‖ ^ r ∂standardCircularGaussian)

theorem integrable_norm_pow_of_memLp {F : ℝ × ℝ → ℂ}
    (hF : ∀ r : ℝ≥0, MemLp F r standardCircularGaussian) (r : ℕ) :
    Integrable (fun w => ‖F w‖ ^ r) standardCircularGaussian := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h
    simp
  · exact (hF r).integrable_norm_pow h.ne'

/-!
### The joint characteristic function
-/

theorem gaussianReal_charFun_mul (v : ℝ≥0) (a : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)) ∂gaussianReal 0 v) =
      Complex.exp (-((v : ℂ) * (a : ℂ) ^ 2) / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := v) a
  rw [charFun_apply_real] at h
  simpa [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc, neg_div] using h

theorem circular_charFun (a c : ℝ) :
    (∫ w : ℝ × ℝ, Complex.exp (Complex.I * ((a * w.1 + c * w.2 : ℝ) : ℂ))
      ∂standardCircularGaussian) =
      Complex.exp (-((((1 : ℝ) / 2 * (a ^ 2 + c ^ 2) : ℝ)) : ℂ) / 2) := by
  have hsplit : (fun w : ℝ × ℝ => Complex.exp (Complex.I * ((a * w.1 + c * w.2 : ℝ) : ℂ))) =
      fun w => Complex.exp (Complex.I * ((a * w.1 : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((c * w.2 : ℝ) : ℂ)) := by
    funext w
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit]
  unfold standardCircularGaussian
  rw [integral_prod_mul (fun x : ℝ => Complex.exp (Complex.I * ((a * x : ℝ) : ℂ)))
    (fun y : ℝ => Complex.exp (Complex.I * ((c * y : ℝ) : ℂ)))]
  unfold standardCircularReal
  rw [gaussianReal_charFun_mul, gaussianReal_charFun_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Joint characteristic function of `ringOmegaMeasure N` for every real-linear pairing. -/
theorem ringOmega_characteristic {N : ℕ} (α β : ErdosRiabov.UpperPair N → ℝ) :
    (∫ ω, Complex.exp (Complex.I *
        ((∑ q, (α q * (ω q).1 + β q * (ω q).2) : ℝ) : ℂ)) ∂ringOmegaMeasure N) =
      Complex.exp (-((∑ q, (1 : ℝ) / 2 * (α q ^ 2 + β q ^ 2) : ℝ) : ℂ) / 2) := by
  have hpoint (ω : RingOmega N) :
      Complex.exp (Complex.I * ((∑ q, (α q * (ω q).1 + β q * (ω q).2) : ℝ) : ℂ)) =
        ∏ q, Complex.exp (Complex.I * ((α q * (ω q).1 + β q * (ω q).2 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp_rw [hpoint]
  unfold ringOmegaMeasure
  rw [integral_fintype_prod_eq_prod
    (fun q (w : ℝ × ℝ) => Complex.exp (Complex.I * ((α q * w.1 + β q * w.2 : ℝ) : ℂ)))
    (μ := fun _ => standardCircularGaussian)]
  simp_rw [circular_charFun]
  rw [← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  simp only [neg_div]

end BlockBand.Adapters.ErdosRiabov
