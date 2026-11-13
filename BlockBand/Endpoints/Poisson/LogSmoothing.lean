module

public import BlockBand.Endpoints.Poisson.LogKernel

/-!
# Smoothing error of the logarithmic kernel

Convolution is written out: `(k_δ ⋆ f)(u) = ∫ s, logKernel δ s * f (u - s)`.

- `abs_sum_logKernel_conv_sub_le` (deterministic Tonelli estimate, B): for measurable bounded
  `f` and every finite family `u`,
  `|Σ_α (k_δ ⋆ f)(u_α) - Σ_α f(u_α)| ≤ Σ_α ∫ k_δ(s) |f(u_α - s) - f(u_α)| ds`.
- `integral_abs_sum_logKernel_conv_sub_le` (probabilistic estimate, C): on a finite measure
  space, for a measurable random family `u : Ω → ι → ℝ` with the first factorial-moment
  bound `E #{α | u_α ∈ [a, b]} ≤ K (b - a)`, and `f` differentiable everywhere with
  integrable derivative `f'`, `f = 0` off `[-R, R]`, `|f| ≤ M`, for every `δ > 0`:
  `E |Σ_α (k_δ ⋆ f)(u_α) - Σ_α f(u_α)| ≤ 8 K (‖f'‖₁ + R M) δ (1 + |log δ|)`.
  The random variable is integrable (`integrable_sum_logKernel_conv_sub`).
- `integral_abs_sum_logKernel_conv_sub_le_of_contDiff`: the `C¹`, support in `[-R, R]` case,
  in the form `8 K (‖f'‖₁ + R M + ‖f‖₁) δ (1 + |log δ|)`.

The proof uses only interval counts. Writing `f(x - s) - f(x) = -∫_{x-s}^{x} f'` and
swapping integrals, `E Σ_α |f(u_α - s) - f(u_α)| ≤ 2K|s|‖f'‖₁`; the support bound gives
`≤ 4KRM`. Tonelli over `Ω × ℝ` and `lintegral_logKernel_mul_min_le` finish the proof. The
constant `8` is absolute (independent of `ι, Ω, P, u, K, f, R, M, δ`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Real
open scoped ENNReal Interval

/-- `s ↦ k_δ(s) g(x - s)` is integrable for measurable bounded `g`. -/
theorem integrable_logKernel_mul_comp {δ : ℝ} (hδ : 0 < δ) {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M) (x : ℝ) :
    Integrable fun s => logKernel δ s * g (x - s) :=
  (integrable_logKernel hδ).mul_bdd
    (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hM (x - s))

/-- Deterministic Tonelli estimate (B): for measurable `f` with `|f| ≤ M` and every finite
family `u`, `|Σ_α (k_δ ⋆ f)(u_α) - Σ_α f(u_α)| ≤ Σ_α ∫ k_δ(s) |f(u_α - s) - f(u_α)| ds`. -/
theorem abs_sum_logKernel_conv_sub_le {ι : Type*} [Fintype ι] {δ : ℝ} (hδ : 0 < δ)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (u : ι → ℝ) :
    |∑ α, (∫ s, logKernel δ s * f (u α - s)) - ∑ α, f (u α)| ≤
      ∑ α, ∫ s, logKernel δ s * |f (u α - s) - f (u α)| := by
  have key : ∀ x, (∫ s, logKernel δ s * f (x - s)) - f x =
      ∫ s, logKernel δ s * (f (x - s) - f x) := by
    intro x
    simp_rw [mul_sub]
    rw [integral_sub (integrable_logKernel_mul_comp hδ hf hM x)
      ((integrable_logKernel hδ).mul_const _), integral_mul_const, integral_logKernel hδ,
      one_mul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [key]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  refine abs_integral_le_integral_abs.trans (le_of_eq (integral_congr_ae
    (Filter.Eventually.of_forall fun s => ?_)))
  simp only [abs_mul, abs_of_nonneg (logKernel_nonneg hδ.le s)]

/-- The estimate (B) for continuous compactly supported `f` (in particular `C¹` or `C^∞`
with compact support). -/
theorem abs_sum_logKernel_conv_sub_le_of_continuous {ι : Type*} [Fintype ι] {δ : ℝ}
    (hδ : 0 < δ) {f : ℝ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (u : ι → ℝ) :
    |∑ α, (∫ s, logKernel δ s * f (u α - s)) - ∑ α, f (u α)| ≤
      ∑ α, ∫ s, logKernel δ s * |f (u α - s) - f (u α)| := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  exact abs_sum_logKernel_conv_sub_le hδ hf.measurable (M := M)
    (fun x => by simpa [Real.norm_eq_abs] using hM x) u

/-- Fundamental theorem of calculus in window form:
`|f(x - s) - f(x)| ≤ ∫ |f'(v)| 1{x ∈ [v - |s|, v + |s|]} dv`. -/
theorem ofReal_abs_sub_le_lintegral {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Integrable f') (x s : ℝ) :
    ENNReal.ofReal |f (x - s) - f x| ≤
      ∫⁻ v, ENNReal.ofReal |f' v| *
        (Set.Icc (v - |s|) (v + |s|)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hftc : f x - f (x - s) = ∫ v in (x - s)..x, f' v :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hf v)
      hf'.intervalIntegrable).symm
  have h1 : |f (x - s) - f x| ≤ ∫ v in Ι (x - s) x, |f' v| := by
    rw [abs_sub_comm, hftc]
    simpa [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm_uIoc (f := f') (μ := volume)
        (a := x - s) (b := x)
  have hsub : Ι (x - s) x ⊆ Set.Icc (x - |s|) (x + |s|) := by
    intro v hv
    rw [Set.mem_uIoc] at hv
    have := le_abs_self s
    have := neg_abs_le s
    constructor <;> rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  calc ENNReal.ofReal |f (x - s) - f x|
      ≤ ENNReal.ofReal (∫ v in Ι (x - s) x, |f' v|) := ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ v in Ι (x - s) x, ENNReal.ofReal |f' v| :=
        ofReal_integral_eq_lintegral_ofReal hf'.abs.integrableOn
          (Filter.Eventually.of_forall fun v => abs_nonneg _)
    _ ≤ ∫⁻ v in Set.Icc (x - |s|) (x + |s|), ENNReal.ofReal |f' v| :=
        lintegral_mono_set hsub
    _ = ∫⁻ v, (Set.Icc (x - |s|) (x + |s|)).indicator
          (fun v => ENNReal.ofReal |f' v|) v :=
        (lintegral_indicator measurableSet_Icc _).symm
    _ = _ := by
        refine lintegral_congr fun v => ?_
        have h' : x ∈ Set.Icc (v - |s|) (v + |s|) ↔
            v ∈ Set.Icc (x - |s|) (x + |s|) := by
          simp only [Set.mem_Icc]
          constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
        by_cases h : v ∈ Set.Icc (x - |s|) (x + |s|)
        · simp [h, h'.mpr h]
        · simp [h, mt h'.mp h]

/-- Support bound: `|f(x - s) - f(x)| ≤ M 1{x ∈ [s - R, s + R]} + M 1{x ∈ [-R, R]}`. -/
theorem ofReal_abs_sub_le_indicator {f : ℝ → ℝ} {R M : ℝ}
    (hsupp : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) (hM : ∀ x, |f x| ≤ M) (x s : ℝ) :
    ENNReal.ofReal |f (x - s) - f x| ≤
      ENNReal.ofReal M * (Set.Icc (s - R) (s + R)).indicator (fun _ => (1 : ℝ≥0∞)) x +
        ENNReal.ofReal M * (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  have hy : ∀ y, ENNReal.ofReal |f y| ≤
      ENNReal.ofReal M * (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases h : y ∈ Set.Icc (-R) R
    · simp [h, ENNReal.ofReal_le_ofReal (hM y)]
    · simp [h, hsupp y h]
  have hshift : (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) (x - s) =
      (Set.Icc (s - R) (s + R)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    have h' : x - s ∈ Set.Icc (-R) R ↔ x ∈ Set.Icc (s - R) (s + R) := by
      simp only [Set.mem_Icc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases h : x ∈ Set.Icc (s - R) (s + R)
    · simp [h, h'.mpr h]
    · simp [h, mt h'.mp h]
  calc ENNReal.ofReal |f (x - s) - f x| ≤ ENNReal.ofReal (|f (x - s)| + |f x|) :=
        ENNReal.ofReal_le_ofReal (abs_sub _ _)
    _ = ENNReal.ofReal |f (x - s)| + ENNReal.ofReal |f x| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add (hshift ▸ hy (x - s)) (hy x)

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {ι : Type*} [Fintype ι] {u : Ω → ι → ℝ}

/-- `ofReal` of a real `0/1` indicator. -/
theorem finiteLog_ofReal_indicator_one (S : Set ℝ) (x : ℝ) :
    ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) x) =
      S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases h : x ∈ S <;> simp [h]

/-- The interval count hypothesis in `ℝ≥0∞` form:
`∫⁻ Σ_α 1{u_α ∈ [a, b]} dP ≤ K (b - a)`. -/
theorem lintegral_sum_indicator_Icc_le (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ ω, ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α) ∂P ≤
      ENNReal.ofReal (K * (b - a)) := by
  have hcard : ∀ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) =
      ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) (u ω α) := by
    intro ω
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases h : u ω α ∈ Set.Icc a b <;> simp [h]
  have hmeas : Measurable fun ω =>
      ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) (u ω α) :=
    Finset.measurable_sum _ fun α _ =>
      (measurable_const.indicator measurableSet_Icc).comp ((measurable_pi_apply α).comp hu)
  have hint : Integrable
      (fun ω => ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) (u ω α)) P := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Fintype.card ι)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [← hcard, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Finset.card_filter_le _ _
  have h1 := hcount a b hab
  simp_rw [hcard] at h1
  calc ∫⁻ ω, ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α) ∂P
      = ∫⁻ ω, ENNReal.ofReal
          (∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) (u ω α)) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun α _ =>
          Set.indicator_nonneg (fun _ _ => zero_le_one) _]
        simp_rw [finiteLog_ofReal_indicator_one]
    _ = ENNReal.ofReal
          (∫ ω, ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ)) (u ω α) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω =>
          Finset.sum_nonneg fun α _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)).symm
    _ ≤ ENNReal.ofReal (K * (b - a)) := ENNReal.ofReal_le_ofReal h1

/-- Tonelli with sliding windows: for measurable `φ ≥ 0` and `r ≥ 0`,
`∫⁻ Σ_α ∫⁻ φ(v) 1{u_α ∈ [v - r, v + r]} dv dP ≤ 2Kr ∫⁻ φ`. -/
theorem lintegral_sum_window_count_le (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    {r : ℝ} (hr : 0 ≤ r) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, (∑ α, ∫⁻ v, φ v *
        (Set.Icc (v - r) (v + r)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α)) ∂P
      ≤ ENNReal.ofReal (K * (2 * r)) * ∫⁻ v, φ v := by
  set W : Set (ℝ × ℝ) := {q | q.2 - r ≤ q.1 ∧ q.1 ≤ q.2 + r} with hW
  have hWm : MeasurableSet W :=
    (measurableSet_le (measurable_snd.sub_const r) measurable_fst).inter
      (measurableSet_le measurable_fst (measurable_snd.add_const r))
  have hind : ∀ x v : ℝ, (Set.Icc (v - r) (v + r)).indicator (fun _ => (1 : ℝ≥0∞)) x =
      W.indicator (fun _ => (1 : ℝ≥0∞)) (x, v) := fun _ _ => rfl
  have hF : ∀ α, Measurable (fun p : Ω × ℝ =>
      φ p.2 * (Set.Icc (p.2 - r) (p.2 + r)).indicator (fun _ => (1 : ℝ≥0∞)) (u p.1 α)) := by
    intro α
    simp_rw [hind]
    exact (hφ.comp measurable_snd).mul ((measurable_const.indicator hWm).comp
      ((((measurable_pi_apply α).comp hu).comp measurable_fst).prodMk measurable_snd))
  calc ∫⁻ ω, (∑ α, ∫⁻ v, φ v *
        (Set.Icc (v - r) (v + r)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α)) ∂P
      = ∫⁻ ω, (∫⁻ v, ∑ α, φ v *
          (Set.Icc (v - r) (v + r)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α)) ∂P := by
        refine lintegral_congr fun ω => ?_
        exact (lintegral_finsetSum _ fun α _ => (hF α).comp measurable_prodMk_left).symm
    _ = ∫⁻ v, ∫⁻ ω, ∑ α,
          φ v * (Set.Icc (v - r) (v + r)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α) ∂P :=
        lintegral_lintegral_swap (Finset.measurable_sum _ fun α _ => hF α).aemeasurable
    _ = ∫⁻ v, φ v * ∫⁻ ω, ∑ α,
          (Set.Icc (v - r) (v + r)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α) ∂P := by
        refine lintegral_congr fun v => ?_
        simp_rw [← Finset.mul_sum]
        exact lintegral_const_mul _ (Finset.measurable_sum _ fun α _ =>
          (measurable_const.indicator measurableSet_Icc).comp ((measurable_pi_apply α).comp hu))
    _ ≤ ∫⁻ v, φ v * ENNReal.ofReal (K * (2 * r)) := by
        refine lintegral_mono fun v => ?_
        gcongr
        calc _ ≤ ENNReal.ofReal (K * ((v + r) - (v - r))) :=
              lintegral_sum_indicator_Icc_le hu hcount (by linarith)
          _ = ENNReal.ofReal (K * (2 * r)) := by ring_nf
    _ = ENNReal.ofReal (K * (2 * r)) * ∫⁻ v, φ v := by
        rw [lintegral_mul_const _ hφ, mul_comm]

/-- Measurability of the interval count `ω ↦ Σ_α 1{u_α(ω) ∈ [a, b]}`. -/
theorem measurable_sum_indicator_Icc (hu : Measurable u) (a b : ℝ) :
    Measurable fun ω => ∑ α, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α) :=
  Finset.measurable_sum _ fun α _ =>
    (measurable_const.indicator measurableSet_Icc).comp ((measurable_pi_apply α).comp hu)

/-- Expected translation error at a fixed shift `s`:
`E Σ_α |f(u_α - s) - f(u_α)| ≤ min (2K‖f'‖₁ |s|) (4KRM)`. -/
theorem lintegral_sum_abs_sub_le (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    (hK : 0 ≤ K) {R M : ℝ} (hR : 0 ≤ R) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hsupp : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) (hM : ∀ x, |f x| ≤ M) (s : ℝ) :
    ∫⁻ ω, (∑ α, ENNReal.ofReal |f (u ω α - s) - f (u ω α)|) ∂P ≤
      ENNReal.ofReal (min ((2 * K * ∫ v, |f' v|) * |s|) (4 * K * R * M)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hf'm : Measurable f' := by
    have : f' = deriv f := funext fun x => (hf x).deriv.symm
    rw [this]
    exact measurable_deriv f
  have hA : 0 ≤ ∫ v, |f' v| := integral_nonneg fun v => abs_nonneg _
  rw [ENNReal.ofReal_min]
  refine le_min ?_ ?_
  · calc ∫⁻ ω, (∑ α, ENNReal.ofReal |f (u ω α - s) - f (u ω α)|) ∂P
        ≤ ∫⁻ ω, (∑ α, ∫⁻ v, ENNReal.ofReal |f' v| *
            (Set.Icc (v - |s|) (v + |s|)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α)) ∂P :=
          lintegral_mono fun ω => Finset.sum_le_sum fun α _ =>
            ofReal_abs_sub_le_lintegral hf hf' _ _
      _ ≤ ENNReal.ofReal (K * (2 * |s|)) * ∫⁻ v, ENNReal.ofReal |f' v| :=
          lintegral_sum_window_count_le hu hcount (abs_nonneg s) hf'm.abs.ennreal_ofReal
      _ = ENNReal.ofReal ((2 * K * ∫ v, |f' v|) * |s|) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hf'.abs
            (Filter.Eventually.of_forall fun v => abs_nonneg _),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  · calc ∫⁻ ω, (∑ α, ENNReal.ofReal |f (u ω α - s) - f (u ω α)|) ∂P
        ≤ ∫⁻ ω, (∑ α, (ENNReal.ofReal M *
            (Set.Icc (s - R) (s + R)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α) +
              ENNReal.ofReal M *
                (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α))) ∂P :=
          lintegral_mono fun ω => Finset.sum_le_sum fun α _ =>
            ofReal_abs_sub_le_indicator hsupp hM _ _
      _ = ENNReal.ofReal M * ∫⁻ ω, (∑ α,
            (Set.Icc (s - R) (s + R)).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α)) ∂P +
          ENNReal.ofReal M * ∫⁻ ω, (∑ α,
            (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ≥0∞)) (u ω α)) ∂P := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [lintegral_add_left ((measurable_sum_indicator_Icc hu _ _).const_mul _),
            lintegral_const_mul _ (measurable_sum_indicator_Icc hu _ _),
            lintegral_const_mul _ (measurable_sum_indicator_Icc hu _ _)]
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal (K * ((s + R) - (s - R))) +
          ENNReal.ofReal M * ENNReal.ofReal (K * (R - -R)) := by
          gcongr
          · exact lintegral_sum_indicator_Icc_le hu hcount (by linarith)
          · exact lintegral_sum_indicator_Icc_le hu hcount (by linarith)
      _ = ENNReal.ofReal (4 * K * R * M) := by
          rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul hM0,
            ← ENNReal.ofReal_add (mul_nonneg hM0 (mul_nonneg hK (by linarith)))
              (mul_nonneg hM0 (mul_nonneg hK (by linarith)))]
          congr 1
          ring

/-- The probabilistic estimate (C) in `ℝ≥0∞` form, for every `δ > 0`. -/
theorem lintegral_abs_sum_logKernel_conv_sub_le (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    (hK : 0 ≤ K) {δ R M : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hsupp : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) (hM : ∀ x, |f x| ≤ M) :
    ∫⁻ ω, ENNReal.ofReal
        |∑ α, (∫ s, logKernel δ s * f (u ω α - s)) - ∑ α, f (u ω α)| ∂P ≤
      ENNReal.ofReal (8 * K * ((∫ x, |f' x|) + R * M) * (δ * (1 + |Real.log δ|))) := by
  set A := ∫ x, |f' x| with hAdef
  have hA : 0 ≤ A := integral_nonneg fun v => abs_nonneg _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hfm := hfc.measurable
  have hk := logKernel_nonneg hδ.le
  have hΔ : ∀ α, Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (logKernel δ p.2 * |f (u p.1 α - p.2) - f (u p.1 α)|)) := by
    intro α
    have hua : Measurable fun p : Ω × ℝ => u p.1 α :=
      ((measurable_pi_apply α).comp hu).comp measurable_fst
    exact (((measurable_logKernel δ).comp measurable_snd).mul
      ((hfm.comp (hua.sub measurable_snd)).sub (hfm.comp hua)).abs).ennreal_ofReal
  have hInt : ∀ x, Integrable fun s => logKernel δ s * |f (x - s) - f x| := by
    intro x
    exact integrable_logKernel_mul_comp hδ (g := fun y => |f y - f x|)
      (hfm.sub measurable_const).abs (M := 2 * M) (fun y => by
        rw [abs_abs]
        have := abs_sub (f y) (f x)
        linarith [hM y, hM x]) x
  have hL : 0 ≤ δ * (1 + |Real.log δ|) := by positivity
  calc ∫⁻ ω, ENNReal.ofReal
        |∑ α, (∫ s, logKernel δ s * f (u ω α - s)) - ∑ α, f (u ω α)| ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal
          (∑ α, ∫ s, logKernel δ s * |f (u ω α - s) - f (u ω α)|) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          (abs_sum_logKernel_conv_sub_le hδ hfm hM (u ω))
    _ = ∫⁻ ω, (∑ α, ∫⁻ s,
          ENNReal.ofReal (logKernel δ s * |f (u ω α - s) - f (u ω α)|)) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun α _ => integral_nonneg fun s =>
          mul_nonneg (hk s) (abs_nonneg _)]
        exact Finset.sum_congr rfl fun α _ => ofReal_integral_eq_lintegral_ofReal (hInt _)
          (Filter.Eventually.of_forall fun s => mul_nonneg (hk s) (abs_nonneg _))
    _ = ∫⁻ ω, (∫⁻ s, ∑ α,
          ENNReal.ofReal (logKernel δ s * |f (u ω α - s) - f (u ω α)|)) ∂P := by
        refine lintegral_congr fun ω => ?_
        exact (lintegral_finsetSum _ fun α _ => (hΔ α).comp measurable_prodMk_left).symm
    _ = ∫⁻ s, ∫⁻ ω, (∑ α,
          ENNReal.ofReal (logKernel δ s * |f (u ω α - s) - f (u ω α)|)) ∂P :=
        lintegral_lintegral_swap (Finset.measurable_sum _ fun α _ => hΔ α).aemeasurable
    _ = ∫⁻ s, ENNReal.ofReal (logKernel δ s) *
          ∫⁻ ω, (∑ α, ENNReal.ofReal |f (u ω α - s) - f (u ω α)|) ∂P := by
        refine lintegral_congr fun s => ?_
        simp_rw [ENNReal.ofReal_mul (hk s), ← Finset.mul_sum]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∫⁻ s, ENNReal.ofReal (logKernel δ s) *
          ENNReal.ofReal (min ((2 * K * A) * |s|) (4 * K * R * M)) := by
        refine lintegral_mono fun s => ?_
        gcongr
        exact lintegral_sum_abs_sub_le hu hcount hK hR hf hf' hsupp hM s
    _ = ∫⁻ s, ENNReal.ofReal
          (logKernel δ s * min ((2 * K * A) * |s|) (4 * K * R * M)) :=
        lintegral_congr fun s => (ENNReal.ofReal_mul (hk s)).symm
    _ ≤ ENNReal.ofReal (2 * (2 * K * A + 4 * K * R * M) * (δ * (1 + |Real.log δ|))) :=
        lintegral_logKernel_mul_min_le hδ (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal (8 * K * (A + R * M) * (δ * (1 + |Real.log δ|))) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hL)
        nlinarith [mul_nonneg hK hA]

/-- Measurability of the smoothed test `x ↦ ∫ k_δ(s) f(x - s) ds`. -/
theorem measurable_logKernel_conv {δ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun x => ∫ s, logKernel δ s * f (x - s) := by
  have : StronglyMeasurable fun p : ℝ × ℝ => logKernel δ p.2 * f (p.1 - p.2) :=
    (((measurable_logKernel δ).comp measurable_snd).mul
      (hf.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact (this.integral_prod_right' (ν := volume)).measurable

/-- Measurability of the smoothing error `ω ↦ Σ_α (k_δ ⋆ f)(u_α) - Σ_α f(u_α)`. -/
theorem measurable_sum_logKernel_conv_sub (hu : Measurable u) {δ : ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) :
    Measurable fun ω => ∑ α, (∫ s, logKernel δ s * f (u ω α - s)) - ∑ α, f (u ω α) :=
  (Finset.measurable_sum _ fun α _ =>
      (measurable_logKernel_conv hf).comp ((measurable_pi_apply α).comp hu)).sub
    (Finset.measurable_sum _ fun α _ => hf.comp ((measurable_pi_apply α).comp hu))

/-- The smoothing error is integrable under the hypotheses of (C). -/
theorem integrable_sum_logKernel_conv_sub (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    (hK : 0 ≤ K) {δ R M : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hsupp : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) (hM : ∀ x, |f x| ≤ M) :
    Integrable
      (fun ω => ∑ α, (∫ s, logKernel δ s * f (u ω α - s)) - ∑ α, f (u ω α)) P := by
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable
  refine ⟨(measurable_sum_logKernel_conv_sub hu hfm).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [Real.enorm_eq_ofReal_abs]
  exact (lintegral_abs_sum_logKernel_conv_sub_le hu hcount hK hδ hR hf hf' hsupp
    hM).trans_lt ENNReal.ofReal_lt_top

/-- **Step 1 of the finite-log recovery lemma** (probabilistic estimate C), for every
`δ > 0`: `E |Σ_α (k_δ ⋆ f)(u_α) - Σ_α f(u_α)| ≤ 8 K (‖f'‖₁ + R M) δ (1 + |log δ|)`.
Hypotheses: `P` finite, `u` measurable with the first factorial-moment interval bound,
`f` differentiable with derivative `f'` integrable, `f = 0` off `[-R, R]`, `|f| ≤ M`. -/
theorem integral_abs_sum_logKernel_conv_sub_le (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    (hK : 0 ≤ K) {δ R M : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Integrable f')
    (hsupp : ∀ x, x ∉ Set.Icc (-R) R → f x = 0) (hM : ∀ x, |f x| ≤ M) :
    ∫ ω, |∑ α, (∫ s, logKernel δ s * f (u ω α - s)) - ∑ α, f (u ω α)| ∂P ≤
      8 * K * ((∫ x, |f' x|) + R * M) * (δ * (1 + |Real.log δ|)) := by
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.2 fun x => (hf x).continuousAt).measurable
  have hA : 0 ≤ ∫ x, |f' x| := integral_nonneg fun v => abs_nonneg _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    (measurable_sum_logKernel_conv_sub hu hfm).abs.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (lintegral_abs_sum_logKernel_conv_sub_le hu hcount hK hδ hR hf hf' hsupp hM)

/-- Step 1 for `C¹` tests supported in `[-R, R]`, in the form
`E |Σ_α (k_δ ⋆ f)(u_α) - Σ_α f(u_α)| ≤ 8 K (‖f'‖₁ + R M + ‖f‖₁) δ (1 + |log δ|)`. -/
theorem integral_abs_sum_logKernel_conv_sub_le_of_contDiff (hu : Measurable u) {K : ℝ}
    (hcount : ∀ a b : ℝ, a ≤ b →
      ∫ ω, ((Finset.univ.filter fun α => u ω α ∈ Set.Icc a b).card : ℝ) ∂P ≤
        K * (b - a))
    (hK : 0 ≤ K) {δ R M : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hsupp : Function.support f ⊆ Set.Icc (-R) R)
    (hM : ∀ x, |f x| ≤ M) :
    ∫ ω, |∑ α, (∫ s, logKernel δ s * f (u ω α - s)) - ∑ α, f (u ω α)| ∂P ≤
      8 * K * ((∫ x, |deriv f x|) + R * M + ∫ x, |f x|) * δ * (1 + |Real.log δ|) := by
  have hcs : HasCompactSupport f := HasCompactSupport.intro isCompact_Icc fun x hx =>
    Function.notMem_support.1 fun h => hx (hsupp h)
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf.differentiable one_ne_zero) x).hasDerivAt
  have hint : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv
  have h := integral_abs_sum_logKernel_conv_sub_le hu hcount hK hδ hR hd hint
    (fun x hx => Function.notMem_support.1 fun h => hx (hsupp h)) hM
  have h1 : 0 ≤ ∫ x, |f x| := integral_nonneg fun v => abs_nonneg _
  have hL : 0 ≤ δ * (1 + |Real.log δ|) := by positivity
  calc _ ≤ 8 * K * ((∫ x, |deriv f x|) + R * M) * (δ * (1 + |Real.log δ|)) := h
    _ ≤ 8 * K * ((∫ x, |deriv f x|) + R * M + ∫ x, |f x|) *
          (δ * (1 + |Real.log δ|)) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hL
    _ = _ := by ring

end Random

end BlockBand.Endpoints
