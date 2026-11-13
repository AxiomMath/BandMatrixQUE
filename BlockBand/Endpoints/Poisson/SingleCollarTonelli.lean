module

public import BlockBand.Endpoints.Poisson.SameVolume

/-!
# Single-collar log error: from the pointwise stage error to the `f`-integrated form

* `ScStageLogErrorPointwise`: the single-collar log-error bound as stated in the paper, pointwise
  in the unfolded energy: `E |B^{π,S}_κ(E + x/Λ) - B^{π,S∪{k}}_κ(E + x/Λ)| ≤ C m² e^{-cR} + ε`,
  eventually in `j`, uniformly for `x` in a bounded window `[-X, X]`.
* `ScStageLogDetIntegrable`: local integrability in the energy of
  `e ↦ log |det H_κ^{π,S}(e)|` on compact subintervals of `(-2, 2)`, almost surely.
* `sc_tonelli_core`: the Tonelli step (`|∫ f(F - G)| ≤ ∫ f|F - G|`, exchange of `x` and the
  configuration).
* `svSingleCollarLogError_of_pointwise`:
  `ScStageLogErrorPointwise → ScStageLogDetIntegrable → SvSingleCollarLogError`.

`ScStageLogErrorPointwise` is the paper's bound at fixed energy (see its docstring);
`ScStageLogDetIntegrable` is a hypothesis here and is proved as `scStageLogDetIntegrable_holds`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.Layers (boundaryZ)
open scoped ENNReal ContDiff

/-!
## 1. The two statements
-/

/-- **The single-collar log-error bound, pointwise in the unfolded energy**, in the stage
geometry of the sequential-collars lemma.

Setting: that of `SvSingleCollarLogError`, with the test function `f` replaced by a window
`X ≥ 0` of unfolded energies (fixed before `c`: the remote-higher window constant `K` depends on
it, `RemoteHigherUniformStatement`). Statement: for either pairing, every stage `S` and every
collar `k ∉ S`, every `ε > 0`, eventually in `j`, for every `x ∈ [-X, X]`,
`E |B^{π,S}_κ(e) - B^{π,S∪{k}}_κ(e)| ≤ C m² e^{-cR} + ε` at `e = E + x/Λ`, with
`B_κ(e) = svStageLog` the source-centred log-determinant (the positive log increment) of the
stage matrix with matched leads `z_b(e)` and physical source `κ = δW²/Λ`. This is the paper's
statement, uniform in the bounded unfolded window; `SvSingleCollarLogError` is its integral
against `f` (`svSingleCollarLogError_of_pointwise`). -/
def ScStageLogErrorPointwise : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 → ∀ X : ℝ, 0 ≤ X →
  ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
  ∀ (m : ℕ) (a : Fin m → ℝ) (R τ : ℝ), 2 ≤ R → 1 ≤ τ → ∑ i, a i = 1 →
    (∀ i, 4 * R + 1 ≤ a i * τ) →
  ∀ (s : CriticalSequence τ) (nb : ℕ → Fin m → ℕ), (∀ j i, 4 ≤ nb j i) →
    (∀ i, Tendsto (fun j => (nb j i : ℝ) / (s.W j : ℝ)) atTop (𝓝 (a i * τ))) →
    (∀ᶠ j in atTop, ∑ i, nb j i = s.n j) →
  ∀ (π : Pairing) (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ j in atTop, ∀ x ∈ Icc (-X) X,
    ∫⁻ v, ENNReal.ofReal
        |svStageLog (svLayout (nb j)) π S b E
            (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) δ
            ⌊R * (s.W j : ℝ)⌋₊ x v -
          svStageLog (svLayout (nb j)) π (insert k S) b E
            (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) δ
            ⌊R * (s.W j : ℝ)⌋₊ x v|
      ∂ringCoordLaw (s.parameters b hb hb' j).n (s.parameters b hb hb' j).W b ≤
      ENNReal.ofReal (C * (m : ℝ) ^ 2 * Real.exp (-(c * R)) + ε)

/-- **Local integrability of the stage log-determinant**: for every ring `ℤ/n` with blocks of
width `W`, `0 < b < 1/2`, every collar layout,
pairing, stage, buffer and source `κ ≥ 0`, and every `-2 < e₁`, `e₂ < 2`, almost surely under the
original prior in Gaussian coordinates, `e ↦ log |det H_κ^{π,S}(e)|` (stage matrix with matched
leads `z_b(e)`) is integrable on `[e₁, e₂]`.

This is strictly weaker than `SvSingleCollarLogError`: it is a qualitative integrability statement
(no bound, no limit, no comparison of stages); it does not imply any estimate on the stage
statistics. -/
def ScStageLogDetIntegrable : Prop :=
  ∀ (n W : ℕ) [NeZero n] (b : ℝ), 0 < b → b < 1 / 2 → ∀ {m : ℕ} (L : Fin m → ℕ),
    IsCollarLayout n L → ∀ (π : Pairing) (S : Finset (Fin m)) (buf : ℕ) (κ : ℝ), 0 ≤ κ →
    ∀ e₁ e₂ : ℝ, -2 < e₁ → e₂ < 2 →
      ∀ᵐ v ∂ringCoordLaw n W b, IntegrableOn
        (fun e => Real.log ‖(stageMatrix L 0 π S e (boundaryZ b e) buf κ v).det‖) (Icc e₁ e₂)

/-!
## 2. The Tonelli step
-/

theorem sc_abs_log_div_le (a b : ℝ) : |Real.log (a / b)| ≤ |Real.log a| + |Real.log b| := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [Real.log_div ha hb]
  exact abs_sub _ _

/-- **The Tonelli step.** For a probability space `Ω`, a nonnegative continuous `f` vanishing off
`[-X, X]`, jointly measurable `F, G : ℝ → Ω → ℝ` with `x ↦ f(x) F(x, v)`, `x ↦ f(x) G(x, v)`
integrable for almost every `v`, and `E|F(x) - G(x)| ≤ B` for `x ∈ [-X, X]`:
`E |a ∫ f F - a ∫ f G| ≤ a (∫ f) B` for `a ≥ 0`. -/
theorem sc_tonelli_core {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) {X : ℝ}
    (hfX : ∀ x, x ∉ Icc (-X) X → f x = 0) {F G : ℝ → Ω → ℝ}
    (hF : Measurable (fun q : Ω × ℝ => F q.2 q.1)) (hG : Measurable (fun q : Ω × ℝ => G q.2 q.1))
    (hFi : ∀ᵐ v ∂μ, Integrable (fun x => f x * F x v))
    (hGi : ∀ᵐ v ∂μ, Integrable (fun x => f x * G x v)) {B : ℝ}
    (hbd : ∀ x ∈ Icc (-X) X, ∫⁻ v, ENNReal.ofReal |F x v - G x v| ∂μ ≤ ENNReal.ofReal B)
    {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ v, ENNReal.ofReal |a * (∫ x, f x * F x v) - a * (∫ x, f x * G x v)| ∂μ ≤
      ENNReal.ofReal (a * (∫ x, f x) * B) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfs
  -- pointwise in `v`: `|a ∫ fF - a ∫ fG| ≤ a ∫⁻ f|F - G|`
  have hpt : ∀ᵐ v ∂μ, ENNReal.ofReal |a * (∫ x, f x * F x v) - a * (∫ x, f x * G x v)| ≤
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal |F x v - G x v| := by
    filter_upwards [hFi, hGi] with v hFv hGv
    have hD : Integrable (fun x => f x * F x v - f x * G x v) := hFv.sub hGv
    have heq : a * (∫ x, f x * F x v) - a * (∫ x, f x * G x v) =
        a * ∫ x, (f x * F x v - f x * G x v) := by
      rw [integral_sub hFv hGv]; ring
    rw [heq, abs_mul, abs_of_nonneg ha, ENNReal.ofReal_mul ha]
    gcongr ENNReal.ofReal a * ?_
    calc ENNReal.ofReal |∫ x, (f x * F x v - f x * G x v)|
        ≤ ENNReal.ofReal (∫ x, |f x * F x v - f x * G x v|) :=
          ENNReal.ofReal_le_ofReal (abs_integral_le_integral_abs)
      _ = ∫⁻ x, ENNReal.ofReal |f x * F x v - f x * G x v| :=
          ofReal_integral_eq_lintegral_ofReal hD.abs (Eventually.of_forall fun _ => abs_nonneg _)
      _ = ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal |F x v - G x v| := by
          refine lintegral_congr fun x => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg (hf0 x), ENNReal.ofReal_mul (hf0 x)]
  have hjoint : Measurable (fun q : Ω × ℝ =>
      ENNReal.ofReal (f q.2) * ENNReal.ofReal |F q.2 q.1 - G q.2 q.1|) :=
    (ENNReal.measurable_ofReal.comp (hf.measurable.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp (hF.sub hG).abs)
  calc ∫⁻ v, ENNReal.ofReal |a * (∫ x, f x * F x v) - a * (∫ x, f x * G x v)| ∂μ
      ≤ ∫⁻ v, ENNReal.ofReal a * (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal |F x v - G x v|)
          ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal a * ∫⁻ x, (∫⁻ v, ENNReal.ofReal (f x) * ENNReal.ofReal |F x v - G x v|
          ∂μ) := by
        rw [lintegral_const_mul _ (hjoint.lintegral_prod_right'),
          lintegral_lintegral_swap hjoint.aemeasurable]
    _ ≤ ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal B := by
        gcongr ENNReal.ofReal a * ?_
        refine lintegral_mono fun x => ?_
        have hFx : Measurable fun v => F x v := hF.comp measurable_prodMk_right
        have hGx : Measurable fun v => G x v := hG.comp measurable_prodMk_right
        rw [lintegral_const_mul (f := fun v => ENNReal.ofReal |F x v - G x v|) _
          (ENNReal.measurable_ofReal.comp (hFx.sub hGx).abs)]
        by_cases hx : x ∈ Icc (-X) X
        · gcongr
          exact hbd x hx
        · simp [hfX x hx]
    _ = ENNReal.ofReal (a * (∫ x, f x) * B) := by
        rw [lintegral_mul_const (f := fun x => ENNReal.ofReal (f x)) _
            (ENNReal.measurable_ofReal.comp hf.measurable),
          ← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hf0),
          ← ENNReal.ofReal_mul (integral_nonneg hf0), ← ENNReal.ofReal_mul ha, mul_assoc]

/-!
## 3. Integrability of the stage statistic integrand
-/

/-- Joint measurability of `(v, x) ↦ B^{π,S}_κ(E + x/Λ)`. -/
theorem sc_measurable_stageLog {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (π : Pairing)
    (S : Finset (Fin m)) (b E Λ δ : ℝ) (buf : ℕ) :
    Measurable (fun q : RingCoords n W × ℝ => svStageLog L π S b E Λ δ buf q.2 q.1) := by
  have hg : Measurable fun x : ℝ => E + x / Λ := by fun_prop
  have hz : Measurable fun x : ℝ => boundaryZ b (E + x / Λ) :=
    (sv_measurable_boundaryZ b).comp hg
  have hA := sv_measurable_det_stageMatrix_param (W := W) L π S (0 : ZMod n) buf
    (δ * (W : ℝ) ^ 2 / Λ) hg hz
  have hB := sv_measurable_det_stageMatrix_param (W := W) L π S (0 : ZMod n) buf 0 hg hz
  exact Real.measurable_log.comp (hA.div hB)

theorem sc_measurable_slice {Ω : Type*} [MeasurableSpace Ω] {F : ℝ → Ω → ℝ}
    (h : Measurable (fun q : Ω × ℝ => F q.2 q.1)) (v : Ω) : Measurable fun x : ℝ => F x v :=
  h.comp measurable_prodMk_left

/-- Affine change of variables for integrability on a window: if `g` is integrable on
`[E - X/Λ, E + X/Λ]` then `x ↦ g(E + x/Λ)` is integrable on `[-X, X]` (`Λ > 0`). -/
theorem sc_integrableOn_affine {g : ℝ → ℝ} {E X Λ : ℝ} (hΛ : 0 < Λ)
    (hg : IntegrableOn g (Icc (E - X / Λ) (E + X / Λ))) :
    IntegrableOn (fun x => g (E + x / Λ)) (Icc (-X) X) := by
  have h1 : Integrable ((Icc (E - X / Λ) (E + X / Λ)).indicator g) :=
    (integrable_indicator_iff measurableSet_Icc).2 hg
  have h2 : Integrable (fun x => (Icc (E - X / Λ) (E + X / Λ)).indicator g (E + x / Λ)) :=
    (h1.comp_add_left E).comp_div hΛ.ne'
  have heq : (fun x => (Icc (E - X / Λ) (E + X / Λ)).indicator g (E + x / Λ)) =
      (Icc (-X) X).indicator (fun x => g (E + x / Λ)) := by
    funext x
    have hmem : E + x / Λ ∈ Icc (E - X / Λ) (E + X / Λ) ↔ x ∈ Icc (-X) X := by
      simp only [mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : -X / Λ ≤ x / Λ := by rw [neg_div]; linarith
        have h2' : x / Λ ≤ X / Λ := by linarith
        exact ⟨(div_le_div_iff_of_pos_right hΛ).1 h1', (div_le_div_iff_of_pos_right hΛ).1 h2'⟩
      · rintro ⟨h1, h2⟩
        have h1' : -X / Λ ≤ x / Λ := (div_le_div_iff_of_pos_right hΛ).2 h1
        have h2' : x / Λ ≤ X / Λ := (div_le_div_iff_of_pos_right hΛ).2 h2
        rw [neg_div] at h1'
        constructor <;> linarith
    by_cases hx : x ∈ Icc (-X) X
    · rw [indicator_of_mem (hmem.2 hx), indicator_of_mem hx]
    · rw [indicator_of_notMem (fun h => hx (hmem.1 h)), indicator_of_notMem hx]
  rw [heq] at h2
  exact (integrable_indicator_iff measurableSet_Icc).1 h2

/-- The integrand `x ↦ f(x) B^{π,S}_κ(E + x/Λ)` of the stage statistic is integrable, almost
surely, as soon as the window `[E - X/Λ, E + X/Λ] ⊂ (-2, 2)` (from `ScStageLogDetIntegrable`). -/
theorem sc_integrable_stageLog (hI : ScStageLogDetIntegrable) {m n W : ℕ} [NeZero n] {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {L : Fin m → ℕ} (hL : IsCollarLayout n L) (π : Pairing)
    (S : Finset (Fin m)) {E Λ δ X : ℝ} (hΛ : 0 < Λ) (hδ : 0 ≤ δ) (buf : ℕ)
    (h1 : -2 < E - X / Λ) (h2 : E + X / Λ < 2) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hfX : ∀ x, x ∉ Icc (-X) X → f x = 0) :
    ∀ᵐ v ∂ringCoordLaw n W b, Integrable (fun x => f x * svStageLog L π S b E Λ δ buf x v) := by
  have hκ : 0 ≤ δ * (W : ℝ) ^ 2 / Λ := by positivity
  filter_upwards [hI n W b hb hb' L hL π S buf _ hκ _ _ h1 h2,
    hI n W b hb hb' L hL π S buf 0 le_rfl _ _ h1 h2] with v hA hB
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  have hA' := sc_integrableOn_affine hΛ hA
  have hB' := sc_integrableOn_affine hΛ hB
  have hdom : Integrable ((Icc (-X) X).indicator fun x =>
      M * (|Real.log ‖(stageMatrix L 0 π S (E + x / Λ) (boundaryZ b (E + x / Λ)) buf
          (δ * (W : ℝ) ^ 2 / Λ) v).det‖| +
        |Real.log ‖(stageMatrix L 0 π S (E + x / Λ) (boundaryZ b (E + x / Λ)) buf 0
          v).det‖|)) :=
    (integrable_indicator_iff measurableSet_Icc).2 ((hA'.abs.add hB'.abs).const_mul M)
  have hcomp : Measurable fun x : ℝ => svStageLog L π S b E Λ δ buf x v :=
    sc_measurable_slice (F := fun x v => svStageLog L π S b E Λ δ buf x v)
      (sc_measurable_stageLog (W := W) L π S b E Λ δ buf) v
  have hmeas : Measurable fun x => f x * svStageLog L π S b E Λ δ buf x v :=
    hf.measurable.mul hcomp
  refine hdom.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Icc (-X) X
  · rw [indicator_of_mem hx, norm_mul]
    refine mul_le_mul (hM x) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM x))
    rw [Real.norm_eq_abs, svStageLog]
    exact sc_abs_log_div_le _ _
  · rw [indicator_of_notMem hx, hfX x hx, zero_mul, norm_zero]

/-!
## 4. The reduction
-/

theorem sc_tendsto_lambda {τ : ℝ} (s : CriticalSequence τ) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun j => ((s.parameters b hb hb' j).N : ℝ) * ρ) atTop atTop := by
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have hn : ∀ᶠ j in atTop, (s.W j : ℝ) ≤ ((s.parameters b hb hb' j).N : ℝ) * ρ / ρ := by
    filter_upwards with j
    rw [mul_div_assoc, div_self hρ.ne', mul_one]
    simp only [CriticalSequence.parameters, Parameters.N, Nat.cast_mul]
    have h4 : (1 : ℝ) ≤ (s.n j : ℝ) := by exact_mod_cast (le_trans (by norm_num) (s.n_ge_four j))
    nlinarith [(Nat.cast_nonneg (s.W j) : (0 : ℝ) ≤ s.W j)]
  have := tendsto_atTop_mono' atTop hn hW
  have h2 := this.atTop_mul_const hρ
  refine h2.congr fun j => ?_
  rw [div_mul_cancel₀ _ hρ.ne']

/-- **`SvSingleCollarLogError` from the pointwise stage error** (Tonelli before the spectral
integration). With `X` a window containing `supp f`, the constant is `(πδ)⁻¹ (∫ f) C`, with the
same `c`. -/
theorem svSingleCollarLogError_of_pointwise (hP : ScStageLogErrorPointwise)
    (hI : ScStageLogDetIntegrable) : SvSingleCollarLogError := by
  intro b hb hb' E hE1 hE2 f hf hfs hf0
  have hfc : Continuous f := hf.continuous
  -- a window containing the support of `f`
  obtain ⟨X₀, hX₀⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  set X := max X₀ 0 with hX
  have hX0 : 0 ≤ X := le_max_right _ _
  have hfX : ∀ x, x ∉ Icc (-X) X → f x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ Metric.closedBall (0 : ℝ) X₀ := hX₀ (subset_tsupport f hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
    exact hx (abs_le.1 (hmem.trans (le_max_left _ _)))
  obtain ⟨c, hc, hδ⟩ := hP b hb hb' E hE1 hE2 X hX0
  refine ⟨c, hc, fun δ hδpos => ?_⟩
  obtain ⟨C, hC, hmain⟩ := hδ δ hδpos
  set A : ℝ := (Real.pi * δ)⁻¹ * ∫ x, f x with hA
  have hA0 : 0 ≤ A := mul_nonneg (inv_nonneg.2 (by positivity)) (integral_nonneg hf0)
  refine ⟨A * C, mul_nonneg hA0 hC, ?_⟩
  intro m a R τ hR hτ ha hgap s nb hnb hlim hsum π S k hk ε hε
  set ε' : ℝ := ε / (A + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by linarith)
  have hρ : 0 < Parameters.semicircleDensity E := by
    unfold Parameters.semicircleDensity
    have : 0 < 4 - E ^ 2 := by nlinarith
    exact div_pos (Real.sqrt_pos.2 this) (by positivity)
  have hΛ := sc_tendsto_lambda s hb hb' hρ
  -- the window `[E - X/Λ, E + X/Λ]` is eventually inside `(-2, 2)`
  have hwin : ∀ᶠ j in atTop, -2 < E - X / (((s.parameters b hb hb' j).N : ℝ) *
        Parameters.semicircleDensity E) ∧
      E + X / (((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E) < 2 ∧
      0 < ((s.parameters b hb hb' j).N : ℝ) * Parameters.semicircleDensity E := by
    have ht : Tendsto (fun j => X / (((s.parameters b hb hb' j).N : ℝ) *
        Parameters.semicircleDensity E)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hΛ
    have hm : (0 : ℝ) < min (E + 2) (2 - E) := lt_min (by linarith) (by linarith)
    filter_upwards [ht.eventually (gt_mem_nhds hm), hΛ.eventually_gt_atTop 0] with j hj hj'
    refine ⟨?_, ?_, hj'⟩
    · have := min_le_left (E + 2) (2 - E); linarith
    · have := min_le_right (E + 2) (2 - E); linarith
  filter_upwards [hmain m a R τ hR hτ ha hgap s nb hnb hlim hsum π S k hk ε' hε'pos, hsum, hwin]
    with j hj hsj hw
  obtain ⟨hw1, hw2, hΛj⟩ := hw
  set p := s.parameters b hb hb' j with hp
  have hL : IsCollarLayout p.n (svLayout (nb j)) := sv_isCollarLayout (hnb j) hsj
  have key := sc_tonelli_core (μ := ringCoordLaw p.n p.W b) hfc hfs hf0 hfX
    (sc_measurable_stageLog (W := p.W) (svLayout (nb j)) π S b E _ δ _)
    (sc_measurable_stageLog (W := p.W) (svLayout (nb j)) π (insert k S) b E _ δ _)
    (sc_integrable_stageLog hI hb hb' hL π S hΛj hδpos.le _ hw1 hw2 hfc hfs hfX)
    (sc_integrable_stageLog hI hb hb' hL π (insert k S) hΛj hδpos.le _ hw1 hw2 hfc hfs hfX)
    hj (a := (Real.pi * δ)⁻¹) (inv_nonneg.2 (by positivity))
  refine (le_of_eq_of_le ?_ key).trans (ENNReal.ofReal_le_ofReal ?_)
  · rfl
  · rw [← hA]
    have h1 : A * ε' ≤ ε := by
      rw [hε', mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith

end BlockBand.Endpoints
