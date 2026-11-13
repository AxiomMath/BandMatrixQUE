module

public import BlockBand.SourceProcess.FullSourceGenerator.GenTools
public import BlockBand.Transmission.Generator.ProdTools

/-!
# Abstract tools for the limit passage of `GeneratorClause` (complex-valued)

* `eval_congr_vars`, `measurable_eval_of`, `continuous_eval_of`: polynomial evaluation only
  sees the variables;
* `tendsto_integral_of_sq_bound_C`: `Transmission.Generator.tendsto_integral_of_sq_bound` for a complex
  continuous functional (applied to `‖G‖`, `Re G`, `Im G`);
* `riemann_tendsto_C`: `riemann_tendsto` for complex cells (real and imaginary parts);
* `fubini_slices_C`: `fubini_slices` over `ℂ`; `measurable_intervalIntegral_C`;
* `sq_intervalIntegral_le` (`(∫_s^t h)² ≤ (t-s)∫_s^t h²`) and `integral_mul_tail`
  (`∫_s^t g(u)∫_u^t g = (∫_s^t g)²/2`, FTC), the two pathwise facts of the bracket clause.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.GenLim

open MeasureTheory Filter Topology MvPolynomial
open BlockBand.Transmission.Generator
open scoped ENNReal

/-!
### Polynomial evaluation
-/

section Poly
variable {σ : Type*}

theorem eval_congr_vars {Ψ : MvPolynomial σ ℂ} {x y : σ → ℂ} (h : ∀ w ∈ Ψ.vars, x w = y w) :
    eval x Ψ = eval y Ψ := by
  show eval₂ (RingHom.id ℂ) x Ψ = eval₂ (RingHom.id ℂ) y Ψ
  exact eval₂_congr _ _ _ fun {i c} hi hc =>
    h i ((mem_vars_iff_mem_support i).mpr ⟨c, mem_support_iff.mpr hc, hi⟩)

theorem measurable_eval_of {Ω : Type*} [MeasurableSpace Ω] {Ψ : MvPolynomial σ ℂ}
    {x : Ω → σ → ℂ} (h : ∀ w ∈ Ψ.vars, Measurable fun ω => x ω w) :
    Measurable fun ω => eval (x ω) Ψ := by
  simp only [eval_eq]
  exact Finset.measurable_sum _ fun d hd => measurable_const.mul
    (Finset.measurable_prod _ fun i hi => (h i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)).pow_const _)

theorem continuous_eval_of {Ψ : MvPolynomial σ ℂ} {x : ℝ → σ → ℂ}
    (h : ∀ w ∈ Ψ.vars, Continuous fun u => x u w) : Continuous fun u => eval (x u) Ψ := by
  simp only [eval_eq]
  exact continuous_finsetSum _ fun d hd => continuous_const.mul
    (continuous_finsetProd _ fun i hi => (h i ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)).pow _)

end Poly

/-!
### Elementary inequalities
-/

theorem ennreal_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := mul_le_mul_right h x
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

theorem ennreal_sq_le_one_add_pow4 (x : ℝ≥0∞) : x ^ 2 ≤ 1 + x ^ 4 := by
  have h := ennreal_le_one_add_sq (x ^ 2)
  rwa [← pow_mul] at h

theorem enorm_mul_le_sq_add_sq (a b : ℂ) : ‖a * b‖ₑ ≤ ‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_mul]; nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

theorem enorm_re_le (z : ℂ) : ‖z.re‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm z)

theorem enorm_im_le (z : ℂ) : ‖z.im‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)

theorem integral_eq_re_im {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ((∫ ω, (f ω).re ∂μ : ℝ) : ℂ) + ((∫ ω, (f ω).im ∂μ : ℝ) : ℂ) * Complex.I := by
  have h1 : ∫ ω, (f ω).re ∂μ = (∫ ω, f ω ∂μ).re := integral_re hf
  have h2 : ∫ ω, (f ω).im ∂μ = (∫ ω, f ω ∂μ).im := integral_im hf
  rw [h1, h2]; exact (Complex.re_add_im _).symm

/-!
### Weak convergence of complex `L²`-bounded functionals
-/

theorem integrable_of_sq_le {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] {G : S → ℂ} (hG : Continuous G) {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {Z : α → S} (hZ : Measurable Z) {C : ℝ}
    (h : ∫⁻ ω, ‖G (Z ω)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal C) : Integrable (fun ω => G (Z ω)) ν :=
  (memLp_two_of_lintegral (hG.measurable.comp hZ).aestronglyMeasurable
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)).integrable one_le_two

/-- **Complex version of `tendsto_integral_of_sq_bound`.** -/
theorem tendsto_integral_of_sq_bound_C {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] {Ω : Type*}
    [MeasurableSpace Ω] {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    {μ : ∀ n, Measure (Ωn n)} [∀ n, IsProbabilityMeasure (μ n)] {X : ∀ n, Ωn n → S}
    (hX : ∀ n, Measurable (X n)) {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → S}
    (hY : Measurable Y)
    (hconv : ∀ Φ : BoundedContinuousFunction S ℝ,
      Tendsto (fun n => ∫ ω, Φ (X n ω) ∂μ n) atTop (𝓝 (∫ ω, Φ (Y ω) ∂P)))
    {G : S → ℂ} (hG : Continuous G) {C : ℝ}
    (hC : ∀ᶠ n in atTop, ∫⁻ ω, ‖G (X n ω)‖ₑ ^ 2 ∂μ n ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ‖G (Y ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C ∧
      Tendsto (fun n => ∫ ω, G (X n ω) ∂μ n) atTop (𝓝 (∫ ω, G (Y ω) ∂P)) := by
  have hN := tendsto_integral_of_sq_bound hX hY hconv (G := fun x => ‖G x‖)
    (continuous_norm.comp hG) (C := C) (hC.mono fun n hn => by simpa only [enorm_norm] using hn)
  have hre := tendsto_integral_of_sq_bound hX hY hconv (G := fun x => (G x).re)
    (Complex.continuous_re.comp hG) (C := C) (hC.mono fun n hn =>
      le_trans (lintegral_mono fun ω => by gcongr; exact enorm_re_le _) hn)
  have him := tendsto_integral_of_sq_bound hX hY hconv (G := fun x => (G x).im)
    (Complex.continuous_im.comp hG) (C := C) (hC.mono fun n hn =>
      le_trans (lintegral_mono fun ω => by gcongr; exact enorm_im_le _) hn)
  have hlim : ∫⁻ ω, ‖G (Y ω)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal C := by
    simpa only [enorm_norm] using hN.1
  refine ⟨hlim, ?_⟩
  rw [integral_eq_re_im (integrable_of_sq_le hG hY hlim)]
  refine (((Complex.continuous_ofReal.tendsto _).comp hre.2).add
    (((Complex.continuous_ofReal.tendsto _).comp him.2).mul_const _)).congr' ?_
  filter_upwards [hC] with n hn
  exact (integral_eq_re_im (integrable_of_sq_le hG (hX n) hn)).symm

/-!
### Riemann sums
-/

/-- **Complex Riemann sums with pointwise convergent bounded cells.** -/
theorem riemann_tendsto_C {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) {c : ℕ → ℕ → ℂ}
    {g : ℝ → ℂ} {s t K : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hg : IntervalIntegrable g volume s t)
    (hbd : ∀ᶠ n in atTop, ∀ u ∈ Set.Icc s t, ‖c n ⌊((σ n : ℕ) : ℝ) * u⌋₊‖ ≤ K)
    (hlim : ∀ u ∈ Set.Icc s t, Tendsto (fun n => c n ⌊((σ n : ℕ) : ℝ) * u⌋₊) atTop (𝓝 (g u))) :
    Tendsto (fun n => ∑ r ∈ Finset.Ico ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊,
      c n r / (σ n : ℂ)) atTop (𝓝 (∫ u in s..t, g u)) := by
  have hre := riemann_tendsto hσ (c := fun n r => (c n r).re) (g := fun u => (g u).re) hs hst
    (hbd.mono fun n hn u hu => (Complex.abs_re_le_norm _).trans (hn u hu))
    fun u hu => (Complex.continuous_re.tendsto _).comp (hlim u hu)
  have him := riemann_tendsto hσ (c := fun n r => (c n r).im) (g := fun u => (g u).im) hs hst
    (hbd.mono fun n hn u hu => (Complex.abs_im_le_norm _).trans (hn u hu))
    fun u hu => (Complex.continuous_im.tendsto _).comp (hlim u hu)
  have hgi : ∫ u in s..t, g u =
      ((∫ u in s..t, (g u).re : ℝ) : ℂ) + ((∫ u in s..t, (g u).im : ℝ) : ℂ) * Complex.I := by
    have h1 := Complex.reCLM.intervalIntegral_comp_comm hg
    have h2 := Complex.imCLM.intervalIntegral_comp_comm hg
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at h1 h2
    rw [h1, h2]; exact (Complex.re_add_im _).symm
  rw [hgi]
  refine (((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const _)).congr fun n => ?_
  apply Complex.ext <;> simp [Complex.div_natCast_re, Complex.div_natCast_im]

/-!
### Interval Fubini for complex slices
-/

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_intervalIntegral_C {F : ℝ → Ω → ℂ}
    (hF : Measurable (Function.uncurry F)) (s t : ℝ) :
    Measurable fun ω => ∫ u in s..t, F u ω := by
  have h1 := (hF.stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Set.Ioc s t))).measurable
  have h2 := (hF.stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Set.Ioc t s))).measurable
  have e : (fun ω => ∫ u in s..t, F u ω) =
      fun ω => (∫ u in Set.Ioc s t, F u ω) - ∫ u in Set.Ioc t s, F u ω :=
    funext fun ω => rfl
  rw [e]; exact h1.sub h2

/-- **Interval Fubini with `L¹`-bounded complex slices** (`fubini_slices` over `ℂ`). -/
theorem fubini_slices_C {P : Measure Ω} [IsFiniteMeasure P] {F : ℝ → Ω → ℂ}
    (hF : Measurable (Function.uncurry F)) {ψ : Ω → ℂ} (hψ : Measurable ψ) {s t C : ℝ}
    (hst : s ≤ t) (hC : ∀ u ∈ Set.Ioc s t, ∫⁻ ω, ‖ψ ω * F u ω‖ₑ ∂P ≤ ENNReal.ofReal C) :
    Integrable (fun ω => ψ ω * ∫ u in s..t, F u ω) P ∧
      ∫⁻ ω, ‖ψ ω * ∫ u in s..t, F u ω‖ₑ ∂P ≤ ENNReal.ofReal ((t - s) * C) ∧
      ∫ ω, ψ ω * (∫ u in s..t, F u ω) ∂P = ∫ u in s..t, ∫ ω, ψ ω * F u ω ∂P ∧
      IntervalIntegrable (fun u => ∫ ω, ψ ω * F u ω ∂P) volume s t := by
  set G : ℝ → Ω → ℂ := fun u ω => ψ ω * F u ω
  have hGm : Measurable (Function.uncurry G) := (hψ.comp measurable_snd).mul hF
  have hlin : ∫⁻ u in Set.uIoc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P ≤ ENNReal.ofReal ((t - s) * C) := by
    rw [Set.uIoc_of_le hst]
    calc ∫⁻ u in Set.Ioc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P ≤ ∫⁻ _ in Set.Ioc s t, ENNReal.ofReal C :=
          setLIntegral_mono' measurableSet_Ioc hC
      _ = ENNReal.ofReal ((t - s) * C) := by
          rw [setLIntegral_const, Real.volume_Ioc, mul_comm, ← ENNReal.ofReal_mul (by linarith)]
  have hint : Integrable (Function.uncurry G) ((volume.restrict (Set.uIoc s t)).prod P) := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral]
    rw [lintegral_prod _ hGm.enorm.aemeasurable]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hfun : ∀ ω, ψ ω * ∫ u in s..t, F u ω = ∫ u, G u ω ∂volume.restrict (Set.uIoc s t) := by
    intro ω
    rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hst,
      Set.uIoc_of_le hst]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hint.integral_prod_right
    simp only [Function.uncurry_apply_pair] at this
    exact this.congr (Eventually.of_forall fun ω => (hfun ω).symm)
  · calc ∫⁻ ω, ‖ψ ω * ∫ u in s..t, F u ω‖ₑ ∂P
        ≤ ∫⁻ ω, (∫⁻ u in Set.uIoc s t, ‖G u ω‖ₑ) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [hfun ω]; exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ u in Set.uIoc s t, ∫⁻ ω, ‖G u ω‖ₑ ∂P :=
          lintegral_lintegral_swap (f := fun ω u => ‖G u ω‖ₑ) (μ := P)
            (ν := volume.restrict (Set.uIoc s t)) ((hGm.enorm.comp measurable_swap).aemeasurable)
      _ ≤ _ := hlin
  · rw [intervalIntegral_integral_swap hint]
    exact integral_congr_ae (Eventually.of_forall fun ω => by
      simp only [G]; rw [intervalIntegral.integral_const_mul])
  · have h2 := hint.integral_prod_left
    simp only [Function.uncurry_apply_pair] at h2
    rw [intervalIntegrable_iff]; exact h2

/-!
### Two deterministic interval-integral facts
-/

/-- Cauchy–Schwarz on an interval: `(∫_s^t h)² ≤ (t - s)∫_s^t h²`. -/
theorem sq_intervalIntegral_le {h : ℝ → ℝ} (hh : Continuous h) {s t : ℝ} (hst : s ≤ t) :
    (∫ u in s..t, h u) ^ 2 ≤ (t - s) * ∫ u in s..t, h u ^ 2 := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  have hpos : 0 < t - s := by linarith
  set I := ∫ u in s..t, h u
  set c := I / (t - s)
  have h0 : 0 ≤ ∫ u in s..t, (h u - c) ^ 2 :=
    intervalIntegral.integral_nonneg hst fun u _ => sq_nonneg _
  have hi : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable f volume s t :=
    fun f hf => hf.intervalIntegrable s t
  have e : ∫ u in s..t, (h u - c) ^ 2 = (∫ u in s..t, h u ^ 2) - 2 * c * I + c ^ 2 * (t - s) := by
    have e1 : (fun u => (h u - c) ^ 2) = fun u => (h u ^ 2 - 2 * c * h u) + c ^ 2 := by
      funext u; ring
    rw [e1, intervalIntegral.integral_add (hi _ (by fun_prop)) intervalIntegrable_const,
      intervalIntegral.integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have hc : c * (t - s) = I := div_mul_cancel₀ I hpos.ne'
  nlinarith

/-- `∫_s^t g(u) ∫_u^t g = (∫_s^t g)²/2` for continuous `g`. -/
theorem integral_mul_tail {g : ℝ → ℂ} (hg : Continuous g) (s t : ℝ) :
    ∫ u in s..t, g u * ∫ v in u..t, g v = (∫ u in s..t, g u) ^ 2 / 2 := by
  set I : ℝ → ℂ := fun u => ∫ v in t..u, g v
  have hI : Continuous I :=
    intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) t
  have hd : ∀ x ∈ Set.uIcc s t, HasDerivAt (fun u => I u * I u) (g x * I x + I x * g x) x := by
    intro x _
    have h1 : HasDerivAt I (g x) x := (hg.integral_hasStrictDerivAt t x).hasDerivAt
    convert h1.mul h1 using 1
  have hcont : Continuous fun x => g x * I x + I x * g x := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable s t)
  have hIt : I t = 0 := intervalIntegral.integral_same
  have hIs : I s = -∫ u in s..t, g u := intervalIntegral.integral_symm _ _
  have htail : ∀ u, ∫ v in u..t, g v = -I u := fun u => intervalIntegral.integral_symm _ _
  have e : (fun u => g u * ∫ v in u..t, g v) =
      fun u => (-(1 / 2 : ℂ)) * (g u * I u + I u * g u) := by
    funext u; rw [htail]; ring
  rw [e, intervalIntegral.integral_const_mul, hftc, hIt, hIs]
  ring

end BlockBand.SourceProcess.FullSourceGenerator.GenLim
