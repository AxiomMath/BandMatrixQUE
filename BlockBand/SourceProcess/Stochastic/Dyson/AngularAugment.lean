module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularIdent
public import BlockBand.SourceProcess.Stochastic.Dyson.B2
public import BlockBand.SourceProcess.Stochastic.Bridges.Product
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Main
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract

/-!
# The augmented Dyson state is a continuous semimartingale

With `Y_u = (λ, X)(F + G_{s+u})` (contract (b2), `dysonBM_b2_of_b1`, now unconditional on (a))
and `V_u = ∫_0^u (θ·b(λ), 𝒜 f(λ, X), 1)`, the joint process `Y⁺ = (Y, V)` is a continuous
semimartingale for `u ↦ 𝓖_{s+u}` with characteristics `plusDrift θ f (Y⁺)`, `plusCov (Y⁺)`
(`isContinuousSemimartingale_Yplus`), assuming non-collision (b1) and `f ∈ C²`.

* `isStronglyProgressive_integral`: pathwise integrals of progressive processes are progressive;
* `continuousAt_angGen`: the angular generator is continuous at states with distinct eigenvalues.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

/-!
### Progressive measurability of integral processes
-/

theorem stronglyMeasurable_integral_Iic {Ω' : Type*} [MeasurableSpace Ω'] (T : ℝ≥0)
    {g : ℝ≥0 → Ω' → ℝ} (hg : StronglyMeasurable fun p : Set.Iic T × Ω' => g p.1 p.2) :
    StronglyMeasurable fun p : Set.Iic T × Ω' => ∫ r in Ioc (0 : ℝ) (p.1 : ℝ), g r.toNNReal p.2 := by
  set c : ℝ → Set.Iic T := fun s => ⟨min s.toNNReal T, min_le_right _ _⟩
  have hc : Measurable c := (measurable_real_toNNReal.min measurable_const).subtype_mk
  set S : Set ((Set.Iic T × Ω') × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ ((q.1.1 : ℝ≥0) : ℝ)}
  have hS : MeasurableSet S := by
    refine (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd ?_)
    exact measurable_coe_nnreal_real.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_fst))
  have hG : StronglyMeasurable fun q : (Set.Iic T × Ω') × ℝ => g (c q.2) q.1.2 :=
    hg.comp_measurable ((hc.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hI := StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) T))
    (hG.indicator hS)
  convert hI using 1
  funext p
  have hsub : Ioc (0 : ℝ) (p.1 : ℝ) ⊆ Ioc (0 : ℝ) T := Ioc_subset_Ioc_right (by exact_mod_cast p.1.2)
  have e : (fun r => S.indicator (fun q => g (c q.2) q.1.2) (p, r)) =
      (Ioc (0 : ℝ) (p.1 : ℝ)).indicator fun r => g (c r) p.2 := by
    funext r; simp only [Set.indicator, S, Set.mem_ofPred_eq, mem_Ioc]
  rw [e, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 hsub]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hrT : r.toNNReal ≤ T := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1.le]; exact (hsub hr).2
  simp only [c, min_eq_left hrT]

/-- **Pathwise integrals of strongly progressive processes are strongly progressive.** -/
theorem isStronglyProgressive_integral {Ω' : Type*} {m : MeasurableSpace Ω'}
    {𝓕 : Filtration ℝ≥0 m} {g : ℝ≥0 → Ω' → ℝ} (hg : IsStronglyProgressive 𝓕 g) :
    IsStronglyProgressive 𝓕 (fun t ω => ∫ r in Ioc (0 : ℝ) t, g r.toNNReal ω) := fun T =>
  @stronglyMeasurable_integral_Iic Ω' (𝓕 T) T g (hg T)

theorem isStronglyProgressive_pi {Ω' : Type*} {m : MeasurableSpace Ω'} {𝓕 : Filtration ℝ≥0 m}
    {n : ℕ} {g : ℝ≥0 → Ω' → Fin n → ℝ} (hg : ∀ k, IsStronglyProgressive 𝓕 fun t ω => g t ω k) :
    IsStronglyProgressive 𝓕 g := fun T => by
  let _ : MeasurableSpace (Set.Iic T × Ω') := Subtype.instMeasurableSpace.prod (𝓕 T)
  exact (Measurable.of_eval fun k => (hg k T).measurable).stronglyMeasurable

/-!
### The angular generator as a function of the state
-/

variable {N : ℕ}

/-- The pair term of the angular generator. -/
def angTerm (f : (Fin N → ℝ) → ℝ) (i j : Fin N) (X : Fin N → ℝ) : ℝ :=
  X i * X j * fderiv ℝ (fderiv ℝ f) X (Pi.single i 1 - Pi.single j 1)
    (Pi.single i 1 - Pi.single j 1) + (X j - X i) * fderiv ℝ f X (Pi.single i 1 - Pi.single j 1)

theorem continuous_angTerm {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin N) :
    Continuous (angTerm f i j) := by
  have h1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  unfold angTerm
  refine (((continuous_apply i).mul (continuous_apply j)).mul
    ((h2.clm_apply continuous_const).clm_apply continuous_const)).add
    (((continuous_apply j).sub (continuous_apply i)).mul (h1.clm_apply continuous_const))

theorem angularGenerator_eq_sum (f : (Fin N → ℝ) → ℝ) (lam X : Fin N → ℝ) :
    angularGenerator N lam f X = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      dysonCoupling N lam i j * angTerm f i j X := rfl

theorem measurable_angGen {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    Measurable fun y : Fin (N + N) → ℝ => angularGenerator N (lamOf y) f (xOf y) := by
  simp only [angularGenerator_eq_sum]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  refine Measurable.mul ?_ ((continuous_angTerm hf i j).measurable.comp ?_)
  · simp only [dysonCoupling, lamOf_eq]; fun_prop
  · exact measurable_pi_iff.2 fun a => measurable_pi_apply _

theorem continuousAt_angGen {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {y : Fin (N + N) → ℝ}
    (hy : ∀ i j : Fin N, i ≠ j →
      y (finSumFinEquiv (Sum.inl i)) ≠ y (finSumFinEquiv (Sum.inl j))) :
    ContinuousAt (fun y : Fin (N + N) → ℝ => angularGenerator N (lamOf y) f (xOf y)) y := by
  simp only [angularGenerator_eq_sum]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact absurd i.2 (by omega)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc := continuousAt_coupling (i := i) (j := j) hN' (hy i j hij)
  simp only [finSumFinEquiv_apply_left] at hc
  refine ContinuousAt.mul ?_ ((continuous_angTerm hf i j).continuousAt.comp ?_)
  · simpa only [lamOf_eq] using hc
  · exact (continuous_pi fun a => continuous_apply _).continuousAt

theorem measurable_vdOf (θ : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    Measurable (vdOf θ f) := by
  refine measurable_pi_iff.2 fun k => ?_
  fin_cases k
  · simp only [vdOf, Fin.zero_eta, Matrix.cons_val_zero]
    refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
    simp only [dysonDrift, lamOf_eq]; fun_prop
  · simpa [vdOf] using measurable_angGen hf
  · simp [vdOf]

theorem continuousAt_vdOf (θ : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    {y : Fin (N + N) → ℝ} (hy : ∀ i j : Fin N, i ≠ j →
      y (finSumFinEquiv (Sum.inl i)) ≠ y (finSumFinEquiv (Sum.inl j))) :
    ContinuousAt (vdOf θ f) y := by
  refine continuousAt_pi.2 fun k => ?_
  fin_cases k
  · simp only [vdOf, Fin.zero_eta, Matrix.cons_val_zero]
    refine tendsto_finsetSum _ fun i _ => continuousAt_const.mul ?_
    have e : (fun y : Fin (N + N) → ℝ => dysonDrift N (lamOf y) i) =
        fun x => dysonStateDrift N x (finSumFinEquiv (Sum.inl i)) :=
      funext fun x => by rw [dysonStateDrift_inl]; simp [lamOf_eq]
    rw [e]
    exact (continuous_apply _).continuousAt.comp (continuousAt_dysonStateDrift hy)
  · simpa [vdOf] using continuousAt_angGen hf hy
  · simp only [vdOf]; exact continuousAt_const

/-!
### The augmented process
-/

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- `(λ, X)(F + G_{s+u})`. -/
def Yst (N : ℕ) (q : Fin N → ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) : ℝ≥0 → Ω → Fin (N + N) → ℝ :=
  fun u ω => dysonState N q (F ω + G (s + u) ω)

/-- The auxiliary integrals `V_u = ∫_0^u vdOf θ f (Y_r) dr`. -/
def Vint (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) :
    ℝ≥0 → Ω → Fin 3 → ℝ :=
  fun u ω k => ∫ r in Ioc (0 : ℝ) u, vdOf θ f (Y r.toNNReal ω) k

/-- The augmented state `Y⁺ = (Y, V)`. -/
def Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) :
    ℝ≥0 → Ω → Fin ((N + N) + 3) → ℝ :=
  fun u ω => concatCoord (Y u ω) (Vint θ f Y u ω)

omit [MeasurableSpace Ω] in
theorem prY_Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : prY N (Yplus θ f Y u ω) = Y u ω := prY_concatCoord _ _

omit [IsProbabilityMeasure Q] in
theorem continuous_vd_path (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s)
    {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) (θ : Fin N → ℝ)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous fun r : ℝ => vdOf θ f (Yst N q G F s r.toNNReal ω) := by
  have hp : Continuous fun r : ℝ => F ω + G (s + r.toNNReal) ω :=
    (continuous_hermBM_add hG F ω).comp (continuous_const.add continuous_real_toNNReal)
  have hst : Continuous fun r : ℝ => Yst N q G F s r.toNNReal ω :=
    (continuousOn_dysonState q).comp_continuous hp fun r =>
      hω _ (add_pos_of_pos_of_nonneg hs zero_le)
  refine continuous_iff_continuousAt.2 fun r => (continuousAt_vdOf θ hf ?_).comp hst.continuousAt
  exact dysonState_distinct (hω _ (add_pos_of_pos_of_nonneg hs zero_le)) q

/-- **The augmented state is a continuous semimartingale** (from (b1), (b2)). -/
theorem isContinuousSemimartingale_Yplus (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    (hb1 : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω))
    {s : ℝ≥0} (hs : 0 < s) (q : Fin N → ℂ) (θ : Fin N → ℝ) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) :
    IsContinuousSemimartingale Q (shiftFiltration 𝓖 s) (Yplus θ f (Yst N q G F s))
      (fun u ω => plusDrift θ f (Yplus θ f (Yst N q G F s) u ω))
      (fun u ω => plusCov (Yplus θ f (Yst N q G F s) u ω)) := by
  have hY := dysonBM_b2_of_b1 SemimartingaleIto.semimartingaleItoFormula_holds
    Semimartingale.stoppedSemimartingale_holds hG hF hFh hb1 s hs q
  have hvd : IsStronglyProgressive (shiftFiltration 𝓖 s)
      (fun u ω => vdOf θ f (Yst N q G F s u ω)) :=
    IsStronglyProgressive.comp_measurable' hY.progressive (measurable_vdOf θ hf)
  have hV : IsStronglyProgressive (shiftFiltration 𝓖 s) (Vint θ f (Yst N q G F s)) :=
    isStronglyProgressive_pi fun k => isStronglyProgressive_integral
      (g := fun u ω => vdOf θ f (Yst N q G F s u ω) k)
      (IsStronglyProgressive.comp_measurable' hvd (measurable_pi_apply k))
  have hac : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ k, IntegrableOn
      (fun r : ℝ => vdOf θ f (Yst N q G F s r.toNNReal ω) k) (Ioc 0 t) ∧
      Vint θ f (Yst N q G F s) t ω k = Vint θ f (Yst N q G F s) 0 ω k +
        ∫ r in Ioc (0 : ℝ) t, vdOf θ f (Yst N q G F s r.toNNReal ω) k := by
    filter_upwards [hb1] with ω hω t k
    refine ⟨?_, by simp [Vint]⟩
    have hc : Continuous fun r : ℝ => vdOf θ f (Yst N q G F s r.toNNReal ω) k :=
      (continuous_apply k).comp (continuous_vd_path hG hs hω q θ hf)
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have H := hY.concat_ac hV hvd hac
  have e1 : (fun u ω => plusDrift θ f (Yplus θ f (Yst N q G F s) u ω)) =
      fun u ω => concatCoord (dysonStateDrift N (Yst N q G F s u ω))
        (vdOf θ f (Yst N q G F s u ω)) := by
    funext u ω; simp only [plusDrift, prY_Yplus]
  have e2 : (fun u ω => plusCov (Yplus θ f (Yst N q G F s) u ω)) =
      fun u ω => concatCov (dysonStateCov N (Yst N q G F s u ω)) 0 0 := by
    funext u ω; simp only [plusCov, prY_Yplus]
  rw [e1, e2]
  exact H

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
