module

public import BlockBand.Critical.RelativeVectors.Equilibrate

/-!
# Phase-averaged tests of the tested labels

The marks are `z_ℓ = √N e^{iθ_ℓ} V^* u_ℓ` with independent uniform phases. For a mark test
`f : MarkArray k r → ℝ` and tested labels `ι : Fin k → Fin N`:

* `phaseAvg N ι f x = ∫ f((θ_{ι m} x_m)_m) dθ` (`θ ~ phaseVectorLaw N`), and
  `arrayTest ι f z = phaseAvg N ι f (π z)` (`π = testProj ι`).
* `IsC2Bounded.norm_fderiv_fderiv_le`: `‖D(Df)‖ ≤ K` from the `iteratedFDeriv` bound.
* `isC2Bounded_phaseAvg`: phase averaging preserves `IsC2Bounded K` (the phases are unit a.s.;
  derivatives under the integral via `fderiv_fderiv_backward_apply` with diagonal unit matrices).
* `isArrayC2Bounded_arrayTest`: `arrayTest ι f` is `IsArrayC2Bounded K` (Euclidean bounds,
  `‖π v‖_sup ≤ ‖v‖₂`).
* `phaseLaw_map_mul`, `phaseVectorLaw_map_mul`: the phase laws are invariant under
  multiplication by unit scalars.
* `arrayTest_phaseCLM`, `isLabelPhaseInvariant_arrayTest`: `arrayTest ι f` is label-phase
  invariant (for every `f`).
* `gaussianMarkLaw_map_testProj`: the marginal of `γ_r^{⊗N}` on injective labels is `γ_r^{⊗k}`;
  `integral_arrayTest_gaussian`: `∫ arrayTest ι f dγ_r^{⊗N} = ∫ f dγ_r^{⊗k}`.
* `measurable_phaseAvg_uncurry`, `measurable_arrayTest_uncurry`: joint measurability for
  path-dependent tests.
* `integral_relativeMark_eq`: `∫ f((relativeMark V K θ (ι m))_m) dθ = arrayTest ι f
  (frameArray V K)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm

variable {N r k : ℕ}

/-- Phase average of a mark test over the label phases of `phaseVectorLaw N`. -/
def phaseAvg (N : ℕ) (ι : Fin k → Fin N) (f : MarkArray k r → ℝ) (x : MarkArray k r) : ℝ :=
  ∫ θ, f (fun m => θ (ι m) • x m) ∂phaseVectorLaw N

/-- The phase-averaged test as a function of the full array. -/
def arrayTest (ι : Fin k → Fin N) (f : MarkArray k r → ℝ) (z : Fin N → Fin r → ℂ) : ℝ :=
  phaseAvg N ι f (testProj ι z)

/-!
## `iteratedFDeriv` and `fderiv ∘ fderiv`
-/

theorem norm_iteratedFDeriv_two_eq {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (g : X → Y) (x : X) :
    ‖iteratedFDeriv ℝ 2 g x‖ = ‖fderiv ℝ (fderiv ℝ g) x‖ := by
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ g), norm_iteratedFDeriv_fderiv]

theorem IsC2Bounded.norm_fderiv_fderiv_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : ℝ} {f : X → ℝ} (hf : IsC2Bounded K f) (x : X) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K := by
  rw [← norm_iteratedFDeriv_two_eq]
  exact hf.hessian_bound x

/-!
## Diagonal unit matrices
-/

/-- `u` if `‖u‖ = 1`, else `1` (a unit scalar for every input). -/
def unitize (u : ℂ) : ℂ := if ‖u‖ = 1 then u else 1

theorem norm_unitize (u : ℂ) : ‖unitize u‖ = 1 := by
  unfold unitize
  split_ifs with h
  · exact h
  · simp

theorem measurable_unitize : Measurable unitize :=
  Measurable.ite (measurableSet_eq_fun continuous_norm.measurable measurable_const)
    measurable_id measurable_const

/-- The diagonal matrix of the (unitized) tested phases. -/
def phaseMat (ι : Fin k → Fin N) (θ : Fin N → ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal fun m => unitize (θ (ι m))

theorem measurable_phaseMat (ι : Fin k → Fin N) : Measurable (phaseMat ι) := by
  unfold phaseMat
  refine Measurable.of_eval fun a => Measurable.of_eval fun b => ?_
  simp only [Matrix.diagonal_apply]
  split_ifs
  · exact measurable_unitize.comp (measurable_pi_apply _)
  · exact measurable_const

theorem arrayMul_diagonal (d : Fin k → ℂ) (x : Fin k → Fin r → ℂ) :
    arrayMul (Matrix.diagonal d) x = fun m => d m • x m := by
  funext m q
  simp [arrayMul, Matrix.diagonal_apply]

theorem opNorm_arrayMulCLM_diagonal_le {d : Fin k → ℂ} (hd : ∀ m, ‖d m‖ ≤ 1) :
    ‖(arrayMulCLM (Matrix.diagonal d) : (Fin k → Fin r → ℂ) →L[ℝ] _)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [arrayMulCLM_apply, arrayMul_diagonal, one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun m => ?_
    rw [norm_smul]
    calc ‖d m‖ * ‖z m‖ ≤ 1 * ‖z m‖ := mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
      _ ≤ ‖z‖ := by rw [one_mul]; exact norm_le_pi_norm z m

theorem opNorm_arrayMulCLM_phaseMat_le (ι : Fin k → Fin N) (θ : Fin N → ℂ) :
    ‖(arrayMulCLM (phaseMat ι θ) : (Fin k → Fin r → ℂ) →L[ℝ] _)‖ ≤ 1 :=
  opNorm_arrayMulCLM_diagonal_le fun _ => (norm_unitize _).le

/-- The phase average as a backward function `∫ f(Mx + 0) dP`, in the sense of
`fderiv_backward_apply`. -/
theorem phaseAvg_eq_backward (ι : Fin k → Fin N) (f : MarkArray k r → ℝ) :
    phaseAvg N ι f =
      fun x => ∫ θ, f (arrayMul (phaseMat ι θ) x + 0) ∂phaseVectorLaw N := by
  funext x
  unfold phaseAvg
  refine integral_congr_ae (ae_norm_phase_eq_one.mono fun θ hθ => ?_)
  simp only [add_zero, phaseMat, arrayMul_diagonal, unitize, hθ, ↓reduceIte]

/-!
## Phase averaging preserves bounded `C²`
-/

theorem isC2Bounded_phaseAvg (ι : Fin k → Fin N) {K : ℝ} {f : MarkArray k r → ℝ}
    (hf : IsC2Bounded K f) : IsC2Bounded K (phaseAvg N ι f) := by
  have hK : 0 ≤ K := hf.nonneg
  have hM := measurable_phaseMat (N := N) ι
  have hΞ : Measurable fun _ : Fin N → ℂ => (0 : Fin k → Fin r → ℂ) := measurable_const
  have hB := opNorm_arrayMulCLM_phaseMat_le (r := r) ι
  have hf2 := hf.norm_fderiv_fderiv_le
  have hD1 := fun x => hasFDerivAt_backward (P := phaseVectorLaw N) hM hΞ hf.contDiff hB
    hf.bound hf.deriv_bound hK x
  have hD2 := fun x => hasFDerivAt_fderiv_backward (P := phaseVectorLaw N) hM hΞ hf.contDiff hB
    zero_le_one hf.bound hf.deriv_bound hK hf2 hK x
  have hf''c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hcompc : Continuous fun L : (Fin k → Fin r → ℂ) →L[ℝ] (Fin k → Fin r → ℂ) =>
      (ContinuousLinearMap.compL ℝ (Fin k → Fin r → ℂ) (Fin k → Fin r → ℂ) ℝ).flip L :=
    (ContinuousLinearMap.compL ℝ (Fin k → Fin r → ℂ) (Fin k → Fin r → ℂ) ℝ).flip.continuous
  have hF2c : Continuous fun x => ∫ θ, hessInt f (phaseMat ι θ)
      (arrayMul (phaseMat ι θ) x + (fun _ => (0 : Fin k → Fin r → ℂ)) θ) ∂phaseVectorLaw N := by
    refine continuous_of_dominated (bound := fun _ => 1 * K * 1) (fun x => ?_)
      (fun x => Filter.Eventually.of_forall fun θ =>
        norm_hessInt_le _ _ (hf2 _) (hB θ) hK zero_le_one)
      (integrable_const _) (Filter.Eventually.of_forall fun θ => ?_)
    · have hc3 : Continuous fun M : Matrix (Fin k) (Fin k) ℂ =>
          hessInt f M (arrayMul M x + 0) := by
        unfold hessInt
        exact (hcompc.comp continuous_arrayMulCLM).clm_comp
          ((hf''c.comp ((continuous_arrayMul_apply x).add continuous_const)).clm_comp
            continuous_arrayMulCLM)
      exact (hc3.measurable.comp hM).aestronglyMeasurable
    · unfold hessInt
      exact continuous_const.clm_comp ((hf''c.comp
        ((arrayMulCLM (phaseMat ι θ) : (Fin k → Fin r → ℂ) →L[ℝ] _).continuous.congr
          (fun y => arrayMulCLM_apply _ y) |>.add continuous_const)).clm_comp continuous_const)
  rw [phaseAvg_eq_backward]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
    rw [e, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, fun x => (hD1 x).differentiableAt.hasFDerivAt⟩
    rw [Nat.cast_one, contDiff_one_iff_hasFDerivAt]
    exact ⟨_, hF2c, hD2⟩
  · intro x
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := K)
      (Filter.Eventually.of_forall fun θ => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    exact hf.bound _
  · intro x
    rw [(hD1 x).fderiv]
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun θ =>
      norm_comp_arrayMul_le _ _ (hf.deriv_bound _) (hB θ) hK)).trans (by simp)
  · intro x
    rw [norm_iteratedFDeriv_two_eq, (hD2 x).fderiv]
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun θ =>
      norm_hessInt_le _ _ (hf2 _) (hB θ) hK zero_le_one)).trans (by simp)

/-!
## The array test: Euclidean bounds
-/

theorem norm_le_sqrt_arrayNormSq (v : Fin N → Fin r → ℂ) : ‖v‖ ≤ Real.sqrt (arrayNormSq v) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun q => ?_
  refine Real.le_sqrt_of_sq_le ?_
  unfold arrayNormSq
  calc ‖v i q‖ ^ 2 ≤ ∑ q', ‖v i q'‖ ^ 2 :=
        Finset.single_le_sum (f := fun q' => ‖v i q'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ q)
    _ ≤ ∑ i', ∑ q', ‖v i' q'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ q', ‖v i' q'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

theorem norm_testProj_le_sqrt (ι : Fin k → Fin N) (v : Fin N → Fin r → ℂ) :
    ‖testProj ι v‖ ≤ Real.sqrt (arrayNormSq v) :=
  (norm_testProj_le ι v).trans (norm_le_sqrt_arrayNormSq v)

theorem isArrayC2Bounded_arrayTest (ι : Fin k → Fin N) {K : ℝ} {f : MarkArray k r → ℝ}
    (hf : IsC2Bounded K f) : IsArrayC2Bounded K (arrayTest ι f) := by
  have hpa := isC2Bounded_phaseAvg (N := N) ι hf
  have hK : 0 ≤ K := hf.nonneg
  refine ⟨?_, fun z => hpa.bound _, fun z v => ?_, fun z v w => ?_⟩
  · exact hpa.contDiff.comp (testProj ι).contDiff
  · show |fderiv ℝ (fun z => phaseAvg N ι f (testProj ι z)) z v| ≤ _
    rw [fderiv_comp_testProj_apply ι hpa.contDiff, ← Real.norm_eq_abs]
    refine ((fderiv ℝ (phaseAvg N ι f) (testProj ι z)).le_opNorm _).trans ?_
    exact mul_le_mul (hpa.deriv_bound _) (norm_testProj_le_sqrt ι v) (norm_nonneg _) hK
  · show |fderiv ℝ (fderiv ℝ (fun z => phaseAvg N ι f (testProj ι z))) z v w| ≤ _
    rw [fderiv_fderiv_comp_testProj_apply ι hpa.contDiff, ← Real.norm_eq_abs]
    refine ((fderiv ℝ (fderiv ℝ (phaseAvg N ι f)) (testProj ι z) (testProj ι v)).le_opNorm
      _).trans ?_
    refine mul_le_mul ?_ (norm_testProj_le_sqrt ι w) (norm_nonneg _) (by positivity)
    refine ((fderiv ℝ (fderiv ℝ (phaseAvg N ι f)) (testProj ι z)).le_opNorm _).trans ?_
    exact mul_le_mul (hpa.norm_fderiv_fderiv_le _) (norm_testProj_le_sqrt ι v) (norm_nonneg _) hK

/-!
## Phase invariance
-/

theorem phaseMap_add_one (x : ℝ) : phaseMap (x + 1) = phaseMap x := by
  unfold phaseMap
  rw [show 2 * (Real.pi : ℂ) * ((x + 1 : ℝ) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I + 2 * Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- `phaseLaw` is invariant under multiplication by a unit scalar. -/
theorem phaseLaw_map_mul {u : ℂ} (hu : ‖u‖ = 1) : phaseLaw.map (fun θ => u * θ) = phaseLaw := by
  have hmeas : Measurable fun θ : ℂ => u * θ := measurable_const_mul u
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  rw [integral_map hmeas.aemeasurable g.continuous.aestronglyMeasurable]
  set a : ℝ := Complex.arg u / (2 * Real.pi) with ha
  have hu' : Complex.exp (Complex.arg u * Complex.I) = u := by
    have := Complex.norm_mul_exp_arg_mul_I u
    rwa [hu, Complex.ofReal_one, one_mul] at this
  have hua : ∀ x : ℝ, u * phaseMap x = phaseMap (x + a) := by
    intro x
    unfold phaseMap
    rw [← hu', ← Complex.exp_add]
    congr 1
    rw [ha]
    push_cast
    field_simp
    ring
  have hg : Continuous fun θ : ℂ => g θ := g.continuous
  rw [phaseLaw_eq_map, integral_map continuous_phaseMap.measurable.aemeasurable
      (f := fun θ => g (u * θ)) (hg.comp (continuous_const.mul continuous_id)).aestronglyMeasurable,
    integral_map (f := fun θ => g θ) continuous_phaseMap.measurable.aemeasurable
      hg.aestronglyMeasurable]
  simp_rw [hua]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_add_right (fun x => g (phaseMap x))]
  have hper : Function.Periodic (fun x => g (phaseMap x)) 1 := fun x => by
    simp only [phaseMap_add_one]
  have := hper.intervalIntegral_add_eq a 0
  rw [zero_add, add_comm 1 a, this, zero_add]

/-- **`phaseVectorLaw` is invariant under unit label phases.** -/
theorem phaseVectorLaw_map_mul (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    (phaseVectorLaw N).map (fun θ i => u i * θ i) = phaseVectorLaw N := by
  unfold phaseVectorLaw
  rw [Measure.pi_map_pi (f := fun i θ => u i * θ)
    (fun i => (measurable_const_mul (u i)).aemeasurable)]
  congr 1
  funext i
  exact phaseLaw_map_mul (hu i)

theorem integral_phaseVectorLaw_mul (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ = 1)
    (F : (Fin N → ℂ) → ℝ) :
    ∫ θ, F (fun i => u i * θ i) ∂phaseVectorLaw N = ∫ θ, F θ ∂phaseVectorLaw N := by
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by
    have h1 := hu i
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  let e : (Fin N → ℂ) ≃ᵐ (Fin N → ℂ) :=
    MeasurableEquiv.piCongrRight fun i => MeasurableEquiv.mulLeft₀ (u i) (hu0 i)
  have he : (e : (Fin N → ℂ) → (Fin N → ℂ)) = fun θ i => u i * θ i := rfl
  calc ∫ θ, F (fun i => u i * θ i) ∂phaseVectorLaw N = ∫ θ, F (e θ) ∂phaseVectorLaw N := rfl
    _ = ∫ y, F y ∂(phaseVectorLaw N).map e := (integral_map_equiv e F).symm
    _ = ∫ θ, F θ ∂phaseVectorLaw N := by rw [he, phaseVectorLaw_map_mul u hu]

/-- **Label-phase invariance of the array test** (for every `f`). -/
theorem arrayTest_phaseCLM (ι : Fin k → Fin N) {f : MarkArray k r → ℝ} (u : Fin N → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (z : Fin N → Fin r → ℂ) :
    arrayTest ι f (phaseCLM u z) = arrayTest ι f z := by
  unfold arrayTest phaseAvg
  rw [← integral_phaseVectorLaw_mul u hu (fun θ => f (fun m => θ (ι m) • testProj ι z m))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show f _ = f _
  congr 1
  funext m
  simp only [testProj_apply, phaseCLM_apply, smul_smul, mul_comm]

theorem isLabelPhaseInvariant_arrayTest (ι : Fin k → Fin N) {f : MarkArray k r → ℝ} :
    IsLabelPhaseInvariant (arrayTest ι f) := fun α z =>
  arrayTest_phaseCLM ι (fun i => Complex.exp ((α i : ℂ) * Complex.I))
    (fun _ => Complex.norm_exp_ofReal_mul_I _) z

/-!
## The Gaussian average
-/

/-- The marginal of `γ_r^{⊗N}` on injective labels is `γ_r^{⊗k}`. -/
theorem gaussianMarkLaw_map_testProj (ι : Fin k → Fin N) (hι : Function.Injective ι) :
    (gaussianMarkLaw N r).map (testProj ι) = gaussianMarkLaw k r := by
  have hπ : Measurable (testProj ι : (Fin N → Fin r → ℂ) → MarkArray k r) :=
    (testProj ι).continuous.measurable
  unfold gaussianMarkLaw
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hπ (MeasurableSet.univ_pi hs)]
  have hpre : (testProj ι : (Fin N → Fin r → ℂ) → MarkArray k r) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => ⋂ m, ⋂ (_ : ι m = i), s m := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter, testProj_apply]
    constructor
    · rintro h _ m rfl
      exact h m
    · intro h m
      exact h _ m rfl
  rw [hpre, Measure.pi_pi]
  have h1 : ∀ m, (⋂ m', ⋂ (_ : ι m' = ι m), s m') = s m := by
    intro m
    ext x
    simp only [Set.mem_iInter]
    constructor
    · intro h
      exact h m rfl
    · intro h m' hm'
      rw [hι hm']
      exact h
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image ι)) ?_]
  · rw [Finset.prod_image (fun a _ b _ h => hι h)]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [h1 m]
  · intro i _ hi
    have : (⋂ m, ⋂ (_ : ι m = i), s m) = Set.univ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_univ, iff_true]
      intro m hm
      exact absurd (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, hm⟩) hi
    rw [this, measure_univ]

theorem circularVectorLaw_map_unit_smul {c : ℂ} (hc : ‖c‖ = 1) :
    (circularVectorLaw (Fin r)).map (fun v => c • v) = circularVectorLaw (Fin r) := by
  have hdet : ‖LinearMap.det (c • LinearMap.id : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))‖ = 1 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, norm_pow, hc, one_pow]
  have hnormSq : Complex.normSq c = 1 := by rw [Complex.normSq_eq_norm_sq, hc, one_pow]
  exact BlockBand.Coarea.ProjectiveHaar.circularVectorLaw_map_linear (c • LinearMap.id) hdet fun g => by
    simp [Complex.normSq_mul, hnormSq]

theorem gaussianMarkLaw_map_phase (c : Fin k → ℂ) (hc : ∀ m, ‖c m‖ = 1) :
    (gaussianMarkLaw k r).map (fun g m => c m • g m) = gaussianMarkLaw k r := by
  unfold gaussianMarkLaw
  rw [Measure.pi_map_pi (f := fun m (v : Fin r → ℂ) => c m • v)
    (fun m => (continuous_const_smul (c m)).measurable.aemeasurable)]
  congr 1
  funext m
  exact circularVectorLaw_map_unit_smul (hc m)

/-- **The Gaussian average of the array test**: `∫ arrayTest ι f dγ_r^{⊗N} = ∫ f dγ_r^{⊗k}`
for injective labels. -/
theorem integral_arrayTest_gaussian (ι : Fin k → Fin N) (hι : Function.Injective ι)
    {f : MarkArray k r → ℝ} (hf : Continuous f) (hb : ∃ C, ∀ x, |f x| ≤ C) :
    ∫ z, arrayTest ι f z ∂gaussianMarkLaw N r = ∫ g, f g ∂gaussianMarkLaw k r := by
  obtain ⟨C, hC⟩ := hb
  set F : (Fin N → Fin r → ℂ) → (Fin N → ℂ) → ℝ :=
    fun z θ => f (fun m => θ (ι m) • z (ι m)) with hF
  have hFc : Continuous (Function.uncurry F) := by
    refine hf.comp (continuous_pi fun m => ?_)
    exact ((continuous_apply (ι m)).comp continuous_snd).smul
      ((continuous_apply (ι m)).comp continuous_fst)
  have hint : Integrable (Function.uncurry F) ((gaussianMarkLaw N r).prod (phaseVectorLaw N)) :=
    Integrable.of_bound hFc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hC _)
  have hinner : ∀ θ : Fin N → ℂ, (∀ i, ‖θ i‖ = 1) →
      ∫ z, F z θ ∂gaussianMarkLaw N r = ∫ g, f g ∂gaussianMarkLaw k r := by
    intro θ hθ
    have hg : Continuous fun y : MarkArray k r => f (fun m => θ (ι m) • y m) :=
      hf.comp (continuous_pi fun m => (continuous_apply m).const_smul (θ (ι m)))
    have hS : Measurable fun (y : MarkArray k r) (m : Fin k) => θ (ι m) • y m :=
      (continuous_pi fun m => (continuous_apply m).const_smul (θ (ι m))).measurable
    calc ∫ z, F z θ ∂gaussianMarkLaw N r
        = ∫ y, f (fun m => θ (ι m) • y m) ∂(gaussianMarkLaw N r).map (testProj ι) := by
          rw [integral_map (testProj ι).continuous.measurable.aemeasurable
            hg.aestronglyMeasurable]
          rfl
      _ = ∫ y, f (fun m => θ (ι m) • y m) ∂gaussianMarkLaw k r := by
          rw [gaussianMarkLaw_map_testProj ι hι]
      _ = ∫ y, f y ∂(gaussianMarkLaw k r).map (fun g m => θ (ι m) • g m) := by
          rw [integral_map hS.aemeasurable hf.aestronglyMeasurable]
      _ = _ := by rw [gaussianMarkLaw_map_phase _ (fun m => hθ (ι m))]
  calc ∫ z, arrayTest ι f z ∂gaussianMarkLaw N r
      = ∫ z, ∫ θ, F z θ ∂phaseVectorLaw N ∂gaussianMarkLaw N r := rfl
    _ = ∫ θ, ∫ z, F z θ ∂gaussianMarkLaw N r ∂phaseVectorLaw N := integral_integral_swap hint
    _ = ∫ _θ, (∫ g, f g ∂gaussianMarkLaw k r) ∂phaseVectorLaw N :=
        integral_congr_ae (ae_norm_phase_eq_one.mono fun θ hθ => hinner θ hθ)
    _ = _ := by simp

/-!
## Joint measurability
-/

theorem measurable_phaseAvg_uncurry {Ω : Type*} [MeasurableSpace Ω] (ι : Fin k → Fin N)
    {f : Ω → MarkArray k r → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry fun ω => phaseAvg N ι (f ω)) := by
  have hc : Continuous fun q : MarkArray k r × (Fin N → ℂ) =>
      fun m => q.2 (ι m) • q.1 m :=
    continuous_pi fun m => ((continuous_apply (ι m)).comp continuous_snd).smul
      ((continuous_apply m).comp continuous_fst)
  have hmap : Measurable fun p : (Ω × MarkArray k r) × (Fin N → ℂ) =>
      (p.1.1, fun m => p.2 (ι m) • p.1.2 m) :=
    measurable_fst.fst.prodMk (hc.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  exact (StronglyMeasurable.integral_prod_right (ν := phaseVectorLaw N)
    (f := fun (x : Ω × MarkArray k r) (θ : Fin N → ℂ) => f x.1 (fun m => θ (ι m) • x.2 m))
    (hf.comp hmap).stronglyMeasurable).measurable

theorem measurable_arrayTest_uncurry {Ω : Type*} [MeasurableSpace Ω] (ι : Fin k → Fin N)
    {f : Ω → MarkArray k r → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry fun ω => arrayTest ι (f ω)) :=
  (measurable_phaseAvg_uncurry ι hf).comp
    (measurable_fst.prodMk ((testProj ι).continuous.measurable.comp measurable_snd))

/-!
## The relative marks
-/

/-- The phase integral of a test of the relative marks is the array test at the frame array. -/
theorem integral_relativeMark_eq (ι : Fin k → Fin N) (f : MarkArray k r → ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    ∫ θ, f (fun m => relativeMark V K θ (ι m)) ∂phaseVectorLaw N =
      arrayTest ι f (frameArray V K) := by
  unfold arrayTest phaseAvg
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show f _ = f _
  congr 1
  funext m
  simp only [relativeMark, testProj_apply, frameArray]
  exact smul_comm _ _ _

end BlockBand.Critical.RelativeVectors
