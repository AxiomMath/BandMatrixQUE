module

public import BlockBand.SourceProcess.FullSourceGenerator.LimTools

/-!
# The bracket clause on the limit, abstractly

* `pathwise_identity`: `M² - ∫Γ - N + 2X_sM = -2∫_s^t A_u M(u,t) du`, where
  `N = X_t² - X_s² - ∫_s^t(2XA + Γ)` (from `(∫A)² = 2∫A_u∫_u^tA`, `integral_mul_tail`);
* `lintegral_sq_tail_le`, `memLp_incr`: `E|∫_u^tA|² ≤ (t-u)²C` (Cauchy–Schwarz pathwise, the
  real `fubini_slices`), so `M(u,t) ∈ L²` uniformly;
* **`bracket_abstract`**: if `E[fN] = 0`, `E[fX_sM(s,t)] = 0` and `E[fA_uM(u,t)] = 0` for
  `u ∈ (s,t]` (bounded measurable `f`), then `M(s,t)² - ∫_s^tΓ` is integrable and
  `E[f(M² - ∫Γ)] = 0` (one complex Fubini, `fubini_slices_C`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.GenLim

open MeasureTheory Filter Topology
open BlockBand.Transmission.Generator
open scoped ENNReal

/-!
### Pathwise identities
-/

theorem continuous_tail {A : ℝ → ℂ} (hA : Continuous A) (t : ℝ) :
    Continuous fun u => ∫ v in u..t, A v := by
  have h := (intervalIntegral.continuous_primitive (μ := MeasureTheory.volume)
    (fun a b => hA.intervalIntegrable a b) t).neg
  refine h.congr fun u => ?_
  exact (intervalIntegral.integral_symm t u).symm

/-- `M² - ∫Γ - N + 2X_sM = -2∫_s^t A_u M(u,t) du` for continuous paths, where
`M(u,t) = X_t - X_u - ∫_u^tA` and `N = X_t² - X_s² - ∫_s^t(2XA + Γ)`. -/
theorem pathwise_identity {X A G : ℝ → ℂ} (hX : Continuous X) (hA : Continuous A)
    (hG : Continuous G) (s t : ℝ) :
    (X t - X s - ∫ u in s..t, A u) ^ 2 - (∫ u in s..t, G u) -
        (X t ^ 2 - X s ^ 2 - ∫ u in s..t, (2 * X u * A u + G u)) +
        2 * X s * (X t - X s - ∫ u in s..t, A u) =
      -2 * ∫ u in s..t, A u * (X t - X u - ∫ v in u..t, A v) := by
  have hi : ∀ f : ℝ → ℂ, Continuous f → IntervalIntegrable f MeasureTheory.volume s t :=
    fun f hf => hf.intervalIntegrable s t
  have hJ := continuous_tail hA t
  have e1 : ∫ u in s..t, (2 * X u * A u + G u) = 2 * (∫ u in s..t, X u * A u) + ∫ u in s..t, G u := by
    rw [intervalIntegral.integral_add (hi _ (by fun_prop)) (hi _ hG),
      ← intervalIntegral.integral_const_mul]
    congr 1; exact intervalIntegral.integral_congr fun u _ => by ring
  have e2 : ∫ u in s..t, A u * (X t - X u - ∫ v in u..t, A v) =
      X t * (∫ u in s..t, A u) - (∫ u in s..t, X u * A u) -
        ∫ u in s..t, A u * ∫ v in u..t, A v := by
    have e : (fun u => A u * (X t - X u - ∫ v in u..t, A v)) =
        fun u => X t * A u - X u * A u - A u * ∫ v in u..t, A v := by
      funext u; ring
    rw [e, intervalIntegral.integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop)),
      intervalIntegral.integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop)),
      intervalIntegral.integral_const_mul]
  rw [e1, e2, integral_mul_tail hA]
  ring

/-!
### Second moments of the time integral
-/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `M(u,t) = X_t - X_u - ∫_u^tA`. -/
def incr (X A : ℝ → Ω → ℂ) (u t : ℝ) (ω : Ω) : ℂ := X t ω - X u ω - ∫ v in u..t, A v ω

theorem measurable_slice {X : ℝ → Ω → ℂ} (hX : Measurable (Function.uncurry X)) (u : ℝ) :
    Measurable (X u) :=
  hX.comp measurable_prodMk_left

theorem lintegral_sq_tail_le [IsFiniteMeasure P] {A : ℝ → Ω → ℂ}
    (hAc : ∀ ω, Continuous fun u => A u ω) (hAm : Measurable (Function.uncurry A)) {u t C : ℝ}
    (hut : u ≤ t) (hA2 : ∀ v ∈ Set.Ioc u t, ∫⁻ ω, ‖A v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ‖∫ v in u..t, A v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ((t - u) * ((t - u) * C)) := by
  set J : ℝ → Ω → ℝ := fun v ω => ‖A v ω‖ ^ 2
  have hJm : Measurable (Function.uncurry J) := hAm.norm.pow_const 2
  have hpt : ∀ ω, ‖∫ v in u..t, A v ω‖ₑ ^ 2 ≤
      ENNReal.ofReal (t - u) * ‖(1 : ℝ) * ∫ v in u..t, J v ω‖ₑ := fun ω => by
    have hJ0 : 0 ≤ ∫ v in u..t, J v ω :=
      intervalIntegral.integral_nonneg hut fun v _ => by positivity
    rw [one_mul, Real.enorm_eq_ofReal hJ0, ← ENNReal.ofReal_mul (by linarith), ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := intervalIntegral.norm_integral_le_integral_norm (f := fun v => A v ω)
      (μ := MeasureTheory.volume) hut
    have h2 := sq_intervalIntegral_le (continuous_norm.comp (hAc ω)) hut
    calc ‖∫ v in u..t, A v ω‖ ^ 2 ≤ (∫ v in u..t, ‖A v ω‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hF := (fubini_slices hJm (ψ := fun _ => (1 : ℝ)) measurable_const hut
    (C := C) fun v hv => by
      refine le_of_eq_of_le (lintegral_congr fun ω => ?_) (hA2 v hv)
      rw [one_mul, Real.enorm_eq_ofReal (by positivity), ← ofReal_norm,
        ← ENNReal.ofReal_pow (norm_nonneg _)]).2.1
  calc ∫⁻ ω, ‖∫ v in u..t, A v ω‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (t - u) * ‖(1 : ℝ) * ∫ v in u..t, J v ω‖ₑ ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (t - u) * ∫⁻ ω, ‖(1 : ℝ) * ∫ v in u..t, J v ω‖ₑ ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (t - u) * ENNReal.ofReal ((t - u) * C) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by linarith)).symm

theorem enorm_sub_sub_sq_le (x y z : ℂ) :
    ‖x - y - z‖ₑ ^ 2 ≤ 3 * ‖x‖ₑ ^ 2 + 3 * ‖y‖ₑ ^ 2 + 3 * ‖z‖ₑ ^ 2 := by
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (norm_sub_le (x - y) z).trans (add_le_add_left (norm_sub_le x y) _)
  nlinarith [norm_nonneg (x - y - z), norm_nonneg x, norm_nonneg y, norm_nonneg z,
    sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖)]

/-- `E|M(u,t)|² ≤ 3(2C + (t-u)²C)` and `M(u,t) ∈ L²`. -/
theorem memLp_incr [IsFiniteMeasure P] {X A : ℝ → Ω → ℂ} (hXm : Measurable (Function.uncurry X))
    (hAc : ∀ ω, Continuous fun u => A u ω) (hAm : Measurable (Function.uncurry A))
    {u t C : ℝ} (hut : u ≤ t) (hX2 : ∀ v ∈ Set.Icc u t, ∫⁻ ω, ‖X v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C)
    (hA2 : ∀ v ∈ Set.Icc u t, ∫⁻ ω, ‖A v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ‖incr X A u t ω‖ₑ ^ 2 ∂P ≤
        3 * ENNReal.ofReal C + 3 * ENNReal.ofReal C +
          3 * ENNReal.ofReal ((t - u) * ((t - u) * C)) ∧
      MemLp (incr X A u t) 2 P := by
  have hJ := lintegral_sq_tail_le hAc hAm hut fun v hv => hA2 v ⟨hv.1.le, hv.2⟩
  have hJm := measurable_intervalIntegral_C hAm u t
  have hb : ∫⁻ ω, ‖incr X A u t ω‖ₑ ^ 2 ∂P ≤ 3 * ENNReal.ofReal C + 3 * ENNReal.ofReal C +
      3 * ENNReal.ofReal ((t - u) * ((t - u) * C)) := by
    calc ∫⁻ ω, ‖incr X A u t ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, (3 * ‖X t ω‖ₑ ^ 2 + 3 * ‖X u ω‖ₑ ^ 2 + 3 * ‖∫ v in u..t, A v ω‖ₑ ^ 2) ∂P :=
          lintegral_mono fun ω => enorm_sub_sub_sq_le _ _ _
      _ = 3 * ∫⁻ ω, ‖X t ω‖ₑ ^ 2 ∂P + 3 * ∫⁻ ω, ‖X u ω‖ₑ ^ 2 ∂P +
          3 * ∫⁻ ω, ‖∫ v in u..t, A v ω‖ₑ ^ 2 ∂P := by
          rw [lintegral_add_right _ ((hJm.enorm.pow_const 2).const_mul _),
            lintegral_add_left (((measurable_slice hXm t).enorm.pow_const 2).const_mul _),
            lintegral_const_mul _ ((measurable_slice hXm t).enorm.pow_const 2),
            lintegral_const_mul _ ((measurable_slice hXm u).enorm.pow_const 2),
            lintegral_const_mul _ (hJm.enorm.pow_const 2)]
      _ ≤ _ := by
          gcongr
          · exact hX2 t ⟨hut, le_rfl⟩
          · exact hX2 u ⟨le_rfl, hut⟩
  refine ⟨hb, memLp_two_of_lintegral
    (((measurable_slice hXm t).sub (measurable_slice hXm u)).sub hJm).aestronglyMeasurable
    (ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top]) hb)⟩

/-!
### The bracket clause on the limit, abstractly
-/

theorem integral_sub_sub' {a b c : Ω → ℂ} (ha : Integrable a P) (hb : Integrable b P)
    (hc : Integrable c P) : ∫ ω, (a ω - b ω - c ω) ∂P =
      (∫ ω, a ω ∂P) - (∫ ω, b ω ∂P) - ∫ ω, c ω ∂P := by
  rw [integral_sub (f := fun ω => a ω - b ω) (ha.sub hb) hc, integral_sub ha hb]

/-- **`M² - ∫Γ` has tested mean zero** from the three tested identities: `E[fN] = 0` (`N` the
increment of `X² - ∫(2XA + Γ)`), `E[fX_sM] = 0`, and `E[fA_uM(u,t)] = 0` for `u ∈ (s,t]`. -/
theorem bracket_abstract [IsProbabilityMeasure P] {f : Ω → ℂ} (hfm : Measurable f) {B : ℝ}
    (hB : 0 ≤ B) (hfB : ∀ ω, ‖f ω‖ ≤ B) {X A G : ℝ → Ω → ℂ}
    (hXc : ∀ ω, Continuous fun u => X u ω) (hAc : ∀ ω, Continuous fun u => A u ω)
    (hGc : ∀ ω, Continuous fun u => G u ω) (hXm : Measurable (Function.uncurry X))
    (hAm : Measurable (Function.uncurry A)) (hGm : Measurable (Function.uncurry G))
    {s t C : ℝ} (hst : s ≤ t) (hC : 0 ≤ C)
    (hX2 : ∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖X v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C)
    (hA2 : ∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖A v ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C)
    (hG1 : ∀ v ∈ Set.Icc s t, ∫⁻ ω, ‖G v ω‖ₑ ∂P ≤ ENNReal.ofReal C)
    (hN : ∫ ω, f ω * (X t ω ^ 2 - X s ω ^ 2 - ∫ u in s..t, (2 * X u ω * A u ω + G u ω)) ∂P = 0)
    (hXM : ∫ ω, f ω * X s ω * incr X A s t ω ∂P = 0)
    (hAM : ∀ u ∈ Set.Ioc s t, ∫ ω, f ω * A u ω * incr X A u t ω ∂P = 0) :
    Integrable (fun ω => incr X A s t ω ^ 2 - ∫ u in s..t, G u ω) P ∧
      ∫ ω, f ω * (incr X A s t ω ^ 2 - ∫ u in s..t, G u ω) ∂P = 0 := by
  have hMs := (memLp_incr hXm hAc hAm hst hX2 hA2).2
  have hXs : MemLp (X s) 2 P := memLp_two_of_lintegral (measurable_slice hXm s).aestronglyMeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hX2 s ⟨le_rfl, hst⟩))
  set K : ℝ≥0∞ := 3 * ENNReal.ofReal C + 3 * ENNReal.ofReal C +
    3 * ENNReal.ofReal ((t - s) * ((t - s) * C))
  have hK : K ≠ ⊤ := by simp [K, ENNReal.mul_eq_top]
  have hMu : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖incr X A u t ω‖ₑ ^ 2 ∂P ≤ K := fun u hu => by
    refine (memLp_incr hXm hAc hAm hu.2 (fun v hv => hX2 v ⟨hu.1.le.trans hv.1, hv.2⟩)
      (fun v hv => hA2 v ⟨hu.1.le.trans hv.1, hv.2⟩)).1.trans ?_
    have h1 : t - u ≤ t - s := by linarith [hu.1]
    have h0 : 0 ≤ t - u := by linarith [hu.2]
    have : (t - u) * ((t - u) * C) ≤ (t - s) * ((t - s) * C) := by
      gcongr
    show _ ≤ 3 * ENNReal.ofReal C + 3 * ENNReal.ofReal C +
      3 * ENNReal.ofReal ((t - s) * ((t - s) * C))
    gcongr
  -- the jointly measurable integrand `A_u M(u,t)`
  have hJm : Measurable (Function.uncurry fun u ω => ∫ v in u..t, A v ω) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_tail (hAc ω) t)
      fun u => measurable_intervalIntegral_C hAm u t
  have hXt : Measurable (Function.uncurry fun (_ : ℝ) ω => X t ω) :=
    (measurable_slice hXm t).comp measurable_snd
  have hFm : Measurable (Function.uncurry fun u ω => A u ω * incr X A u t ω) :=
    hAm.mul ((hXt.sub hXm).sub hJm)
  have hslice : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖f ω * (A u ω * incr X A u t ω)‖ₑ ∂P ≤
      ENNReal.ofReal (B * (C + K.toReal)) := fun u hu => by
    have hMm : Measurable (incr X A u t) :=
      ((measurable_slice hXm t).sub (measurable_slice hXm u)).sub
        (measurable_intervalIntegral_C hAm u t)
    calc ∫⁻ ω, ‖f ω * (A u ω * incr X A u t ω)‖ₑ ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal B * (‖A u ω‖ₑ ^ 2 + ‖incr X A u t ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [enorm_mul]
          gcongr
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hfB ω)
          · exact enorm_mul_le_sq_add_sq _ _
      _ = ENNReal.ofReal B * (∫⁻ ω, ‖A u ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖incr X A u t ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left ((measurable_slice hAm u).enorm.pow_const 2)]
      _ ≤ ENNReal.ofReal B * (ENNReal.ofReal C + K) := by
          gcongr
          · exact hA2 u ⟨hu.1.le, hu.2⟩
          · exact hMu u hu
      _ = _ := by
          rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_add hC ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hK]
  have hF := fubini_slices_C hFm hfm hst hslice
  have hF0 : ∫ ω, f ω * (∫ u in s..t, A u ω * incr X A u t ω) ∂P = 0 := by
    rw [hF.2.2.1]
    refine (intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)).trans
      intervalIntegral.integral_zero
    rw [Set.uIoc_of_le hst] at hu
    rw [← hAM u hu]
    exact integral_congr_ae (Eventually.of_forall fun ω => by beta_reduce; ring)
  have hGi := fubini_slices_C hGm (ψ := fun _ => (1 : ℂ)) measurable_const hst
    (C := C) fun u hu => by simpa using hG1 u ⟨hu.1.le, hu.2⟩
  have hGint : Integrable (fun ω => ∫ u in s..t, G u ω) P :=
    hGi.1.congr (Eventually.of_forall fun ω => one_mul _)
  have hM2 : Integrable (fun ω => incr X A s t ω ^ 2) P :=
    (integrable_mul_of_memLp hMs hMs).congr (Eventually.of_forall fun ω => (sq _).symm)
  have htarget := hM2.sub hGint
  refine ⟨htarget, ?_⟩
  have hfb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ B := Eventually.of_forall hfB
  have h1 : Integrable (fun ω => f ω * (incr X A s t ω ^ 2 - ∫ u in s..t, G u ω)) P :=
    htarget.bdd_mul hfm.aestronglyMeasurable hfb
  have h2 : Integrable (fun ω => f ω * X s ω * incr X A s t ω) P :=
    ((integrable_mul_of_memLp hXs hMs).bdd_mul hfm.aestronglyMeasurable hfb).congr
      (Eventually.of_forall fun ω => by beta_reduce; ring)
  -- the pathwise identity
  have hpath : ∀ ω, f ω * (incr X A s t ω ^ 2 - ∫ u in s..t, G u ω) =
      f ω * (X t ω ^ 2 - X s ω ^ 2 - ∫ u in s..t, (2 * X u ω * A u ω + G u ω)) -
        2 * (f ω * X s ω * incr X A s t ω) -
        2 * (f ω * (∫ u in s..t, A u ω * incr X A u t ω)) := fun ω => by
    have h := pathwise_identity (hXc ω) (hAc ω) (hGc ω) s t
    simp only [incr] at h ⊢
    linear_combination f ω * h
  have h3 : Integrable (fun ω => f ω * (X t ω ^ 2 - X s ω ^ 2 -
      ∫ u in s..t, (2 * X u ω * A u ω + G u ω))) P :=
    ((h1.add (h2.const_mul 2)).add (hF.1.const_mul 2)).congr
      (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; rw [hpath ω]; ring)
  rw [integral_congr_ae (Eventually.of_forall hpath),
    integral_sub_sub' h3 (h2.const_mul 2) (hF.1.const_mul 2), integral_const_mul, integral_const_mul,
    hN, hXM, hF0]
  ring

end BlockBand.SourceProcess.FullSourceGenerator.GenLim
