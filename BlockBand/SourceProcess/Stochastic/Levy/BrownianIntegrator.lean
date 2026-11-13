module
public import BlockBand.SourceProcess.Stochastic.Levy.Brownian
public import BlockBand.SourceProcess.Stochastic.Levy.Product
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Filtration Brownian motions are vector integrators

For a `𝓖`-Brownian motion `B` in `ℝ^d` (`IsFiltrationBrownian`, arbitrary filtered probability
space, raw filtration):

* `integral_mul_increment`: `∫ g · f(B_t - B_s) = (∫ g) · ∫ f dN(0,(t-s)I)` for `𝓖_s`-measurable
  `g` and Borel `f` (independence of the increment from `𝓖_s`);
* `martingale_coord`: each coordinate `B^i` is a `𝓖`-martingale (raw, no modification);
* `martingale_cross`: `B^i B^j - δ_ij t` is a `𝓖`-martingale;
* **`IsFiltrationBrownian.isL2IntegratorVec`**: `B` is an `IsL2IntegratorVec` with identity
  bracket densities `a_ij = δ_ij`, so it can be used as an integrator in the general vector
  stochastic integral. With `isFiltrationBrownian_extension` this applies to the Wiener
  coordinate `B'` of the product extension.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open scoped NNReal ENNReal

universe u

variable {d : ℕ}

/-!
### Moments of `N(0, v I)`
-/

theorem measurePreserving_coord (v : ℝ≥0) (i : Fin d) :
    MeasurePreserving (fun x : Fin d → ℝ => x i) (gaussPi d v) (gaussianReal 0 v) :=
  measurePreserving_eval _ i

theorem memLp_coord_gaussPi (v : ℝ≥0) (i : Fin d) :
    MemLp (fun x : Fin d → ℝ => x i) 2 (gaussPi d v) :=
  (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving (measurePreserving_coord v i)

theorem integral_comp_coord (v : ℝ≥0) (i : Fin d) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f (x i) ∂gaussPi d v = ∫ y, f y ∂gaussianReal 0 v := by
  rw [← (measurePreserving_coord v i).map_eq, integral_map (measurable_pi_apply i).aemeasurable
    hf.aestronglyMeasurable]

theorem integral_coord_gaussPi (v : ℝ≥0) (i : Fin d) : ∫ x, x i ∂gaussPi d v = 0 := by
  have h := integral_comp_coord v i (f := id) measurable_id
  simp only [id] at h
  rw [h]
  exact integral_id_gaussianReal

theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ y, y ^ 2 ∂gaussianReal 0 v = v := by
  have h := variance_eq_integral (X := id) (μ := gaussianReal 0 v) aemeasurable_id
  rw [variance_id_gaussianReal] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  exact h.symm

theorem integral_coord_mul_gaussPi (v : ℝ≥0) (i j : Fin d) :
    ∫ x, x i * x j ∂gaussPi d v = if i = j then (v : ℝ) else 0 := by
  split_ifs with hij
  · subst hij
    simp_rw [← sq]
    rw [integral_comp_coord v i (f := fun y => y ^ 2) (measurable_id.pow_const 2),
      integral_sq_gaussianReal]
  · have hind := (iIndepFun_pi (μ := fun _ : Fin d => gaussianReal 0 v) (X := fun _ => id)
      (fun _ => aemeasurable_id)).indepFun hij
    simp only [id] at hind
    have h0 := integral_coord_gaussPi (d := d) v i
    rw [gaussPi] at h0 ⊢
    rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable, h0, zero_mul]

/-!
### Increments of a filtration Brownian motion
-/

variable {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {B : ℝ≥0 → Ω → Fin d → ℝ}

namespace IsFiltrationBrownian

omit [IsProbabilityMeasure Q] in
theorem measurable_incr (hB : IsFiltrationBrownian Q 𝓖 B) (s t : ℝ≥0) :
    Measurable fun ω => B t ω - B s ω :=
  ((hB.adapted t).mono (𝓖.le t)).measurable.sub ((hB.adapted s).mono (𝓖.le s)).measurable

omit [IsProbabilityMeasure Q] in
/-- **Independence of the increment, integral form.** -/
theorem integral_mul_increment (hB : IsFiltrationBrownian Q 𝓖 B) {s t : ℝ≥0} (hst : s ≤ t)
    {g : Ω → ℝ} (hg : StronglyMeasurable[𝓖 s] g) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, g ω * f (B t ω - B s ω) ∂Q = (∫ ω, g ω ∂Q) * ∫ x, f x ∂gaussPi d (t - s) := by
  have hΔ := hB.measurable_incr s t
  have hind : IndepFun g (fun ω => f (B t ω - B s ω)) Q := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (hB.indep s t hst).symm
      hg.measurable.comap_le) ?_
    rw [show (fun ω => f (B t ω - B s ω)) = f ∘ fun ω => B t ω - B s ω from rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hf.comap_le
  rw [hind.integral_fun_mul_eq_mul_integral (hg.mono (𝓖.le s)).aestronglyMeasurable
    (hf.comp hΔ).aestronglyMeasurable, ← (hB.hasLaw s t hst).map_eq,
    integral_map hΔ.aemeasurable hf.aestronglyMeasurable]

omit [IsProbabilityMeasure Q] in
theorem memLp_incr (hB : IsFiltrationBrownian Q 𝓖 B) {s t : ℝ≥0} (hst : s ≤ t) (i : Fin d) :
    MemLp (fun ω => B t ω i - B s ω i) 2 Q := by
  have h := memLp_coord_gaussPi (d := d) (t - s) i
  rw [← (hB.hasLaw s t hst).map_eq, memLp_map_measure_iff
    (measurable_pi_apply i).aestronglyMeasurable (hB.measurable_incr s t).aemeasurable] at h
  exact h

omit [IsProbabilityMeasure Q] in
theorem memLp_coord (hB : IsFiltrationBrownian Q 𝓖 B) (t : ℝ≥0) (i : Fin d) :
    MemLp (fun ω => B t ω i) 2 Q :=
  (hB.memLp_incr (s := 0) (t := t) zero_le i).ae_eq (hB.zero.mono fun ω hω => by simp [hω])

omit [IsProbabilityMeasure Q] in
theorem stronglyMeasurable_coord (hB : IsFiltrationBrownian Q 𝓖 B) (t : ℝ≥0) (i : Fin d) :
    StronglyMeasurable[𝓖 t] fun ω => B t ω i :=
  (continuous_apply i).comp_stronglyMeasurable (hB.adapted t)

omit [IsProbabilityMeasure Q] in
/-- `∫_S f(B_t - B_s) = Q(S) ∫ f dN(0,(t-s)I)` for `S ∈ 𝓖_s`. -/
theorem setIntegral_increment (hB : IsFiltrationBrownian Q 𝓖 B) {s t : ℝ≥0} (hst : s ≤ t)
    {S : Set Ω} (hS : MeasurableSet[𝓖 s] S) {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω in S, f (B t ω - B s ω) ∂Q = Q.real S * ∫ x, f x ∂gaussPi d (t - s) := by
  have h := hB.integral_mul_increment hst (stronglyMeasurable_one.indicator hS) hf
    (g := S.indicator 1)
  rw [integral_indicator_one (𝓖.le s S hS)] at h
  rw [← h, ← integral_indicator (𝓖.le s S hS)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  by_cases hω : ω ∈ S <;> simp [hω]

/-- **Coordinates are martingales.** -/
theorem martingale_coord (hB : IsFiltrationBrownian Q 𝓖 B) (i : Fin d) :
    Martingale (fun t ω => B t ω i) 𝓖 Q := by
  refine martingale_of_setIntegral_eq (hB.stronglyMeasurable_coord · i)
    (fun t => (hB.memLp_coord t i).integrable one_le_two) fun s t hst S hS => ?_
  have hS' := 𝓖.le s S hS
  have h := hB.setIntegral_increment hst hS (measurable_pi_apply i)
  rw [integral_coord_gaussPi, mul_zero] at h
  have hi := fun r => ((hB.memLp_coord r i).integrable one_le_two).integrableOn (s := S)
  rw [← sub_eq_zero, ← integral_sub (hi t) (hi s)]
  simpa using h

/-- **`B^i B^j - δ_ij t` is a martingale.** -/
theorem martingale_cross (hB : IsFiltrationBrownian Q 𝓖 B) (i j : Fin d) :
    Martingale (fun t ω => B t ω i * B t ω j - if i = j then (t : ℝ) else 0) 𝓖 Q := by
  have hint : ∀ r, Integrable (fun ω => B r ω i * B r ω j - if i = j then (r : ℝ) else 0) Q :=
    fun r => ((hB.memLp_coord r i).integrable_mul (hB.memLp_coord r j)).sub (integrable_const _)
  refine martingale_of_setIntegral_eq (fun t => ((hB.stronglyMeasurable_coord t i).mul
    (hB.stronglyMeasurable_coord t j)).sub stronglyMeasurable_const) hint fun s t hst S hS => ?_
  have hS' := 𝓖.le s S hS
  -- the three increment terms
  have hII : Integrable (fun ω => (B t ω i - B s ω i) * (B t ω j - B s ω j)) Q :=
    (hB.memLp_incr hst i).integrable_mul (hB.memLp_incr hst j)
  have hSI : ∀ k l, Integrable (fun ω => B s ω k * (B t ω l - B s ω l)) Q := fun k l =>
    (hB.memLp_coord s k).integrable_mul (hB.memLp_incr hst l)
  have e1 : ∫ ω in S, (B t ω i - B s ω i) * (B t ω j - B s ω j) ∂Q =
      Q.real S * if i = j then ((t : ℝ) - s) else 0 := by
    have := hB.setIntegral_increment hst hS (f := fun x : Fin d → ℝ => x i * x j)
      ((measurable_pi_apply i).mul (measurable_pi_apply j))
    beta_reduce at this
    rw [show (∫ ω in S, (B t ω i - B s ω i) * (B t ω j - B s ω j) ∂Q) =
      ∫ ω in S, (B t ω - B s ω) i * (B t ω - B s ω) j ∂Q from rfl, this,
      integral_coord_mul_gaussPi, NNReal.coe_sub hst]
  have e2 : ∀ k l, ∫ ω in S, B s ω k * (B t ω l - B s ω l) ∂Q = 0 := fun k l => by
    have := hB.integral_mul_increment hst ((hB.stronglyMeasurable_coord s k).indicator hS)
      (measurable_pi_apply l)
    rw [integral_coord_gaussPi, mul_zero] at this
    rw [← this, ← integral_indicator hS']
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ S <;> simp [hω]
  have hpt : ∀ ω, (B t ω i * B t ω j - if i = j then (t : ℝ) else 0) -
      (B s ω i * B s ω j - if i = j then (s : ℝ) else 0) =
      (B t ω i - B s ω i) * (B t ω j - B s ω j) + B s ω i * (B t ω j - B s ω j) +
        B s ω j * (B t ω i - B s ω i) - if i = j then ((t : ℝ) - s) else 0 := fun ω => by
    split_ifs <;> ring
  rw [← sub_eq_zero, ← integral_sub (hint t).integrableOn (hint s).integrableOn]
  simp_rw [hpt]
  have h12 : Integrable (fun ω => (B t ω i - B s ω i) * (B t ω j - B s ω j) +
      B s ω i * (B t ω j - B s ω j)) Q := hII.add (hSI i j)
  have h123 : Integrable (fun ω => (B t ω i - B s ω i) * (B t ω j - B s ω j) +
      B s ω i * (B t ω j - B s ω j) + B s ω j * (B t ω i - B s ω i)) Q := h12.add (hSI j i)
  rw [integral_sub h123.integrableOn (integrable_const _).integrableOn,
    integral_add h12.integrableOn (hSI j i).integrableOn,
    integral_add hII.integrableOn (hSI i j).integrableOn, e1, e2, e2,
    setIntegral_const, smul_eq_mul]
  ring

/-- **Converse Lévy: a filtration Brownian motion is a vector integrator with identity
bracket densities.** -/
theorem isL2IntegratorVec (hB : IsFiltrationBrownian Q 𝓖 B) :
    IsL2IntegratorVec Q 𝓖 (fun i t ω => B t ω i) (fun i j _ _ => if i = j then 1 else 0) := by
  have hint : ∀ (c : ℝ) (t : ℝ≥0), ∫ r in Ioc (0 : ℝ) t, c = (t : ℝ) * c := fun c t => by simp
  refine ⟨fun i => ⟨?_, (hB.memLp_coord · i), ⟨_, hB.martingale_coord i, fun _ => ae_of_all _
      fun _ => rfl⟩, fun _ _ => by simp, measurable_const, ae_of_all _ fun _ _ =>
      integrableOn_const (by simp), ⟨_, hB.martingale_cross i i, fun t => ae_of_all _
      fun ω => by simp [hint, sq]⟩⟩, fun t ω v => ?_, fun _ _ => measurable_const,
    fun _ _ => ae_of_all _ fun _ _ => integrableOn_const (by simp),
    fun i j => ⟨_, hB.martingale_cross i j, fun t => ae_of_all _ fun ω => ?_⟩⟩
  · filter_upwards [hB.continuous] with ω hω
    exact (continuous_apply i).comp hω
  · refine Finset.sum_nonneg fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simpa using mul_self_nonneg (v i)
  · simp only [hint]
    split_ifs <;> simp

end IsFiltrationBrownian

end BlockBand.SourceProcess.Stochastic.Levy
