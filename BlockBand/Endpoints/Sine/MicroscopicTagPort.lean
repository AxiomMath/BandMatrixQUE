module

public import BlockBand.Endpoints.Sine.MicroscopicTagAlgebra
public import BlockBand.Endpoints.Response.PassDerivative
public import BlockBand.Endpoints.Poisson.PhaseFractionalCollar
public import BlockBand.Counting.CircularGaussianMoments

/-!
# The matched-lead clocks: interior identity, port bound, Gaussian norm, measurability

Used to remove the ports after the four steps of the lead comparison (the microscopic tag
comparison). Law where stated: the standard circular
Gaussian `circularVectorLaw ι` (`CN(0, I)`, real and imaginary parts of variance `1/2`) and the
path law `growthPathLaw W b`.

* `interiorLeadMass_eq_quadForm`: `h*Y^{int}h = Σ_j ‖P_jUh‖² = h*𝒰*𝒰h`, i.e. the interior
  clock of the matched-lead path of length `r` is `fullClock b e W r`
  (`𝒰 = boundaryToInterior`), the clock of the negative-clock theorem.
* `portLeadMass_le` (`Tr Y^{port} ≤ 2W/(Im z_b)²`, in the pointwise form used): for Hermitian path
  blocks and `η = Im z_b > 0`, `h*Y^{port}h = ‖ℝh‖² ≤ ‖h‖²/η²`, from the Ward identity
  `𝓜 - 𝓜* = 2iηVV*` (contraction of `𝕊 = I - 2iηℝ`). It holds for every sample,
  including the singular one (Lean's `𝓜⁻¹ = 0`).
* `integral_vecNormSq_circularVectorLaw`: `E‖h‖² = card ι`.
* Joint measurability in `(e, ω, h)` of the lead masses (`measurable_leadPositionMass`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

variable {W r : ℕ}

theorem leadPositionMass_nonneg (b e : ℝ) (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ)
    (y : Fin r ⊕ Fin 2) : 0 ≤ leadPositionMass b e W r ω h y := by
  rcases y with i | j <;> exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem interiorLeadMass_nonneg (b e : ℝ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ interiorLeadMass b e W r x :=
  Finset.sum_nonneg fun _ _ => leadPositionMass_nonneg _ _ _ _ _

theorem portLeadMass_nonneg (b e : ℝ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ portLeadMass b e W r x :=
  Finset.sum_nonneg fun _ _ => leadPositionMass_nonneg _ _ _ _ _

theorem totalLeadMass_eq (b e : ℝ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    totalLeadMass b e W r x = interiorLeadMass b e W r x + portLeadMass b e W r x := by
  rw [totalLeadMass, Fintype.sum_sum_type]; rfl

/-- The interior clock of the matched-lead path is `fullClock`. -/
theorem interiorLeadMass_eq_quadForm (b e : ℝ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    interiorLeadMass b e W r x = quadForm (fullClock b e W r x.1) x.2 := by
  rw [quadForm, fullClock, star_dotProduct_gram_mulVec, Complex.ofReal_re, vecNormSq,
    Fintype.sum_prod_type]
  rfl

/-- The port masses are `‖ℝh‖²`, `ℝ` the port block of `G_lead`. -/
theorem portLeadMass_eq (b e : ℝ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    portLeadMass b e W r x = vecNormSq (boundaryResolvent b e W r x.1 *ᵥ x.2) := by
  rw [vecNormSq, Fintype.sum_prod_type]
  rfl

/-- **Port bound**: `h*Y^{port}h ≤ ‖h‖²/(Im z_b)²` for Hermitian blocks. -/
theorem portLeadMass_le {b e : ℝ} (hη : 0 < (boundaryZ b e).im)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) (h : Fin 2 × Fin W → ℂ) :
    portLeadMass b e W r (ω, h) ≤ vecNormSq h / (boundaryZ b e).im ^ 2 := by
  have hη' : 0 < etaZ b e := hη
  rw [portLeadMass_eq]
  have hW := fullPathMatrix_ward (b := b) (E := e) (n := r) hH
  have hS : pencilScattering (etaZ b e) (leadInclusion W r) (fullPathMatrix b e W r ω) =
      1 - (((2 * etaZ b e : ℝ) : ℂ) * Complex.I) • boundaryResolvent b e W r ω := by
    rw [pencilScattering, leadInclusion_conjTranspose_mul_mul]; rfl
  have hc := pencilScattering_contraction (η := etaZ b e) (κ := 0)
    (R := (0 : Matrix (FullSite W r) (FullSite W r) ℂ)) hη'.le le_rfl
    (V := leadInclusion W r) (M := fullPathMatrix b e W r ω)
    (by rw [hW, conjTranspose_zero, zero_mul, smul_zero, add_zero]) h
  rw [hS] at hc
  set R := boundaryResolvent b e W r ω
  set c : ℂ := ((2 * etaZ b e : ℝ) : ℂ) * Complex.I
  have hsub : c • (R *ᵥ h) = h - (1 - c • R) *ᵥ h := by
    rw [sub_mulVec, one_mulVec, smul_mulVec]; abel
  set u := (EuclideanSpace.equiv (Fin 2 × Fin W) ℂ).symm h
  set v := (EuclideanSpace.equiv (Fin 2 × Fin W) ℂ).symm ((1 - c • R) *ᵥ h)
  have hc' : ‖v‖ ≤ ‖u‖ := by
    rw [vecNormSq_eq_norm_sq, vecNormSq_eq_norm_sq] at hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hc
  have hnorm : vecNormSq (c • (R *ᵥ h)) ≤ 4 * vecNormSq h := by
    rw [hsub, vecNormSq_eq_norm_sq, vecNormSq_eq_norm_sq, map_sub]
    have ht := norm_sub_le u v
    have h0 := norm_nonneg u
    have h1 := norm_nonneg (u - v)
    nlinarith
  rw [vecNormSq_smul] at hnorm
  have hn2 : ‖c‖ ^ 2 = 4 * etaZ b e ^ 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hn2] at hnorm
  change vecNormSq (R *ᵥ h) ≤ vecNormSq h / etaZ b e ^ 2
  rw [le_div_iff₀ (by positivity)]
  nlinarith [vecNormSq_nonneg (R *ᵥ h)]

/-!
## The standard circular Gaussian vector
-/

theorem measurable_circularVectorMap (ι : Type*) [Fintype ι] :
    Measurable (fun (q : ι × Fin 2 → ℝ) (a : ι) =>
      (q (a, 0) : ℂ) + (q (a, 1) : ℂ) * Complex.I) := by
  refine Measurable.of_eval fun a => ?_
  exact ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
    ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul_const _))

instance isProbabilityMeasure_circularVectorLaw (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (circularVectorLaw ι) := by
  unfold circularVectorLaw
  infer_instance

theorem vecNormSq_circularVectorMap {ι : Type*} [Fintype ι] (q : ι × Fin 2 → ℝ) :
    vecNormSq (fun a : ι => (q (a, 0) : ℂ) + (q (a, 1) : ℂ) * Complex.I) =
      ∑ x : ι × Fin 2, q x ^ 2 := by
  rw [vecNormSq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_two, ← Complex.mk_eq_add_mul_I, Complex.sq_norm, Complex.normSq_mk]
  ring

theorem measurable_vecNormSq {ι : Type*} [Fintype ι] :
    Measurable (fun h : ι → ℂ => vecNormSq h) := by
  unfold vecNormSq
  exact Finset.measurable_sum _ fun i _ => (continuous_norm.measurable.comp
    (measurable_pi_apply i)).pow_const 2

theorem integrable_vecNormSq_circularVectorLaw (ι : Type*) [Fintype ι] :
    Integrable (fun h : ι → ℂ => vecNormSq h) (circularVectorLaw ι) := by
  unfold circularVectorLaw
  rw [integrable_map_measure measurable_vecNormSq.aestronglyMeasurable
    (measurable_circularVectorMap ι).aemeasurable]
  have : (fun h : ι → ℂ => vecNormSq h) ∘
      (fun (q : ι × Fin 2 → ℝ) (a : ι) => (q (a, 0) : ℂ) + (q (a, 1) : ℂ) * Complex.I) =
      fun q => ∑ x : ι × Fin 2, q x ^ 2 := by
    funext q; exact vecNormSq_circularVectorMap q
  rw [this]
  refine integrable_finsetSum _ fun x _ => ?_
  have hsq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 (1 / 2 : ℝ≥0)) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (2 : ℝ≥0)).integrable_norm_pow
      (p := 2) (by norm_num)
    simpa [Real.norm_eq_abs, sq_abs] using h
  exact integrable_comp_eval (μ := fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) (i := x)
    (f := fun y : ℝ => y ^ 2) hsq

/-- `E‖h‖² = card ι` for `h ~ CN(0, I_ι)`. -/
theorem integral_vecNormSq_circularVectorLaw (ι : Type*) [Fintype ι] :
    ∫ h, vecNormSq h ∂circularVectorLaw ι = Fintype.card ι := by
  unfold circularVectorLaw
  rw [integral_map (measurable_circularVectorMap ι).aemeasurable
    measurable_vecNormSq.aestronglyMeasurable]
  simp_rw [vecNormSq_circularVectorMap]
  have hsq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 (1 / 2 : ℝ≥0)) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := (1 / 2 : ℝ≥0)) (2 : ℝ≥0)).integrable_norm_pow
      (p := 2) (by norm_num)
    simpa [Real.norm_eq_abs, sq_abs] using h
  rw [integral_finsetSum _ fun x _ => integrable_comp_eval
    (μ := fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) (i := x) (f := fun y : ℝ => y ^ 2) hsq]
  have : ∀ x : ι × Fin 2, ∫ q : ι × Fin 2 → ℝ, q x ^ 2
      ∂(Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) = 1 / 2 := by
    intro x
    rw [integral_comp_eval (μ := fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) (i := x)
      (f := fun y : ℝ => y ^ 2) hsq.aestronglyMeasurable,
      BlockBand.Counting.integral_sq_gaussianReal]
    norm_num
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast; ring

/-!
## Measurability in the energy, the path and the probe
-/

theorem continuous_matchedA : Continuous matchedA := by
  have : matchedA = fun e : ℝ => ((-e / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - e ^ 2) / 2 : ℝ) : ℂ) *
      Complex.I := by
    funext e; rw [matchedA, Complex.mk_eq_add_mul_I]
  rw [this]; fun_prop

theorem measurable_boundaryZ (b : ℝ) : Measurable (fun e : ℝ => boundaryZ b e) := by
  unfold boundaryZ
  exact (continuous_matchedA.measurable.inv).add
    (measurable_const.mul continuous_matchedA.measurable)

theorem measurable_fullPathMatrix_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {E : α → ℝ} {Ω : α → GrowthPath W} (hE : Measurable E) (hΩ : Measurable Ω) :
    Measurable (fun a => fullPathMatrix b (E a) W r (Ω a)) := by
  have hP : Measurable (fun ω : PathSample W r => pathMatrix ω) := by
    unfold pathMatrix; fun_prop
  have hC : Measurable (fun ω : PathSample W r => pathPortCoupling ω) := by
    unfold pathPortCoupling; fun_prop
  have ha : Measurable (fun a => pathAt W r (Ω a)) := (measurable_pathAt W r).comp hΩ
  have hsub : Measurable (fun a =>
      pathMatrix (pathAt W r (Ω a)) -
        (E a : ℂ) • (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ)) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    have h1 : Measurable (fun a => pathMatrix (pathAt W r (Ω a)) x y) :=
      (measurable_pi_apply y).comp ((measurable_pi_apply x).comp (hP.comp ha))
    have h2 : Measurable (fun a =>
        (E a : ℂ) * (1 : Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ) x y) :=
      (Complex.measurable_ofReal.comp hE).mul_const _
    exact h1.sub h2
  have hz : Measurable (fun a =>
      (boundaryZ b (E a) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ))) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact ((measurable_boundaryZ b).comp hE).mul_const _
  unfold fullPathMatrix
  exact measurable_fromBlocks hsub (hC.comp ha)
    ((continuous_id.matrix_conjTranspose).measurable.comp (hC.comp ha)) hz

theorem measurable_fullInverse_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {E : α → ℝ} {Ω : α → GrowthPath W} (hE : Measurable E) (hΩ : Measurable Ω) :
    Measurable (fun a => fullInverse b (E a) W r (Ω a)) :=
  passDeriv_measurable_inv.comp (measurable_fullPathMatrix_of b W r hE hΩ)

/-- The lead masses are jointly measurable in `(e, ω, h)` (general parametrized form). -/
theorem measurable_leadPositionMass_of (b : ℝ) (W r : ℕ) (y : Fin r ⊕ Fin 2) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)}
    (he : Measurable e) (hx : Measurable x) :
    Measurable (fun a => leadPositionMass b (e a) W r (x a).1 (x a).2 y) := by
  have hF' := measurable_fullInverse_of b W r (α := α) he (measurable_fst.comp hx)
  have hG : ∀ x' z, Measurable (fun a => fullInverse b (e a) W r (x a).1 x' z) := fun x' z =>
    measurable_pi_iff.1 (measurable_pi_iff.1 hF' x') z
  have hh : ∀ z, Measurable (fun a => (x a).2 z) :=
    fun z => (measurable_pi_apply z).comp (measurable_snd.comp hx)
  have hψ : ∀ x', Measurable (fun a => (leadResponse b (e a) W r (x a).1 *ᵥ (x a).2) x') := by
    intro x'
    simp only [mulVec, dotProduct, leadResponse]
    exact Finset.measurable_sum _ fun z _ => (hG x' (Sum.inr z)).mul (hh z)
  rcases y with i | j
  · exact Finset.measurable_sum _ fun a _ =>
      (continuous_norm.measurable.comp (hψ (Sum.inl (i, a)))).pow_const 2
  · exact Finset.measurable_sum _ fun a _ =>
      (continuous_norm.measurable.comp (hψ (Sum.inr (j, a)))).pow_const 2

theorem measurable_leadPositionMass (b : ℝ) (W r : ℕ) (y : Fin r ⊕ Fin 2) :
    Measurable (fun q : ℝ × (GrowthPath W × (Fin 2 × Fin W → ℂ)) =>
      leadPositionMass b q.1 W r q.2.1 q.2.2 y) :=
  measurable_leadPositionMass_of b W r y measurable_fst measurable_snd

end BlockBand.Endpoints
