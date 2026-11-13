module

public import BlockBand.Transmission.PassiveLayer.OURot

/-!
# Bilinear Ornstein–Uhlenbeck covariance identity: interpolation in time

For a Gaussian product measure, the covariance of two bounded `C¹` functions with bounded
derivatives is `∫₀^∞ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)] dt`, `x_t = e^{-t}x + √(1-e^{-2t}) x'`,
in vector-, scalar- and matrix-valued forms, with the resulting uniform bound.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory BlockBand.Internal.Contracts.Inputs
open scoped NNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-!
## The Ornstein–Uhlenbeck interpolation in time
-/

/-- `(e^{-t})² = e^{-2t}`. -/
theorem ou_exp_sq (t : ℝ) : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
  rw [← Real.exp_nat_mul]; ring_nf

theorem ou_one_sub_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-2 * t) := by
  have : Real.exp (-2 * t) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem ou_sqrt_pos {t : ℝ} (ht : 0 < t) : 0 < Real.sqrt (1 - Real.exp (-2 * t)) :=
  Real.sqrt_pos.mpr (ou_one_sub_pos ht)

/-- Derivative of `t ↦ √(1 - e^{-2t})` for `t > 0`. -/
theorem ou_hasDerivAt_sqrt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => Real.sqrt (1 - Real.exp (-2 * τ)))
      (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) t := by
  have h1 : HasDerivAt (fun τ => 1 - Real.exp (-2 * τ)) (-(Real.exp (-2 * t) * (-2 * 1))) t :=
    (((hasDerivAt_id t).const_mul (-2)).exp).const_sub 1
  refine (h1.sqrt (ou_one_sub_pos ht).ne').congr_deriv ?_
  have := (ou_sqrt_pos ht).ne'
  field_simp

omit [DecidableEq ι] in
/-- Integrability of a bounded continuous function on `μ ⊗ μ`. -/
theorem ou_integrable_bdd (v : ι → ℝ≥0) {F : Type*} [NormedAddCommGroup F]
    {G : (ι → ℝ) × (ι → ℝ) → F} (hG : Continuous G) {C : ℝ} (hC : ∀ p, ‖G p‖ ≤ C) :
    Integrable G ((gaussianProduct v).prod (gaussianProduct v)) :=
  ou_integrable_of_norm_le _ hG.aestronglyMeasurable C 0 (fun p => by simpa using hC p)

/-- **Time derivative of the interpolation** `φ(t) = E[f(x) g(e^{-t}x + √(1-e^{-2t}) x')]`:
for `t > 0`, `φ'(t) = -e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]`. -/
theorem ou_hasDerivAt_interp (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => ∫ p, f p.1 • g (Real.exp (-τ) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) ∂(gaussianProduct v).prod (gaussianProduct v))
      (-Real.exp (-t) • ∫ p, ouDir v f g p.1 (Real.exp (-t) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
          ∂(gaussianProduct v).prod (gaussianProduct v)) t := by
  set μ := gaussianProduct v
  let c : ℝ → ℝ := fun τ => Real.exp (-τ)
  let s : ℝ → ℝ := fun τ => Real.sqrt (1 - Real.exp (-2 * τ))
  let F : ℝ → (ι → ℝ) × (ι → ℝ) → E := fun τ p => f p.1 • g (c τ • p.1 + s τ • p.2)
  let F' : ℝ → (ι → ℝ) × (ι → ℝ) → E := fun τ p =>
    f p.1 • fderiv ℝ g (c τ • p.1 + s τ • p.2) ((-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2)
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfC 0)
  have hCg' : 0 ≤ Cg' := (norm_nonneg _).trans (hg'C 0)
  have hFc : ∀ τ, Continuous (F τ) := fun τ =>
    (hfc.comp continuous_fst).smul (hgc.comp (by fun_prop))
  have hF'c : Continuous (F' t) :=
    (hfc.comp continuous_fst).smul ((hg'c.comp (by fun_prop)).clm_apply (by fun_prop))
  set s0 := Real.sqrt (1 - Real.exp (-t)) with hs0def
  have hs0 : 0 < s0 := by
    have := ou_sqrt_pos (t := t / 2) (by linarith)
    rwa [show -2 * (t / 2) = -t by ring] at this
  have hsτ : ∀ τ ∈ Set.Ioi (t / 2), s0 ≤ s τ := fun τ hτ => by
    refine Real.sqrt_le_sqrt ?_
    have : Real.exp (-2 * τ) ≤ Real.exp (-t) :=
      Real.exp_le_exp.mpr (by simp only [Set.mem_Ioi] at hτ; linarith)
    linarith
  have hbound : ∀ᵐ p ∂μ.prod μ, ∀ τ ∈ Set.Ioi (t / 2),
      ‖F' τ p‖ ≤ Cf * Cg' * ((1 + s0⁻¹) * ‖p‖) := Filter.Eventually.of_forall fun p τ hτ => by
    have hτ0 : 0 < τ := by simp only [Set.mem_Ioi] at hτ; linarith
    have hc1 : c τ ≤ 1 := by
      simp only [c]; rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hc0 : 0 ≤ c τ := (Real.exp_pos _).le
    have hsp : 0 < s τ := ou_sqrt_pos hτ0
    have he1 : Real.exp (-2 * τ) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hq : Real.exp (-2 * τ) / s τ ≤ s0⁻¹ := by
      rw [div_le_iff₀ hsp]
      calc Real.exp (-2 * τ) ≤ 1 := he1
        _ = s0⁻¹ * s0 := (inv_mul_cancel₀ hs0.ne').symm
        _ ≤ s0⁻¹ * s τ := mul_le_mul_of_nonneg_left (hsτ τ hτ) (inv_nonneg.mpr hs0.le)
    have hw : ‖(-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2‖ ≤ (1 + s0⁻¹) * ‖p‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg hc0,
        abs_of_nonneg (div_nonneg (Real.exp_pos _).le hsp.le)]
      have h1 := norm_fst_le p
      have h2 := norm_snd_le p
      have h3 : c τ * ‖p.1‖ ≤ 1 * ‖p‖ := mul_le_mul hc1 h1 (norm_nonneg _) zero_le_one
      have h4 : Real.exp (-2 * τ) / s τ * ‖p.2‖ ≤ s0⁻¹ * ‖p‖ :=
        mul_le_mul hq h2 (norm_nonneg _) (inv_nonneg.mpr hs0.le)
      linarith
    calc ‖F' τ p‖ = ‖f p.1‖ * ‖fderiv ℝ g (c τ • p.1 + s τ • p.2)
          ((-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2)‖ := norm_smul _ _
      _ ≤ Cf * (Cg' * ((1 + s0⁻¹) * ‖p‖)) := by
        refine mul_le_mul (hfC _) ?_ (norm_nonneg _) hCf
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        exact mul_le_mul (hg'C _) hw (norm_nonneg _) hCg'
      _ = Cf * Cg' * ((1 + s0⁻¹) * ‖p‖) := by ring
  have hbint : Integrable (fun p : (ι → ℝ) × (ι → ℝ) => Cf * Cg' * ((1 + s0⁻¹) * ‖p‖))
      (μ.prod μ) :=
    (IsGaussian.integrable_id.norm.const_mul _).const_mul _
  have hdiff : ∀ᵐ p ∂μ.prod μ, ∀ τ ∈ Set.Ioi (t / 2),
      HasDerivAt (fun τ => F τ p) (F' τ p) τ := Filter.Eventually.of_forall fun p τ hτ => by
    have hτ0 : 0 < τ := by simp only [Set.mem_Ioi] at hτ; linarith
    have hcd : HasDerivAt c (-c τ) τ :=
      ((hasDerivAt_neg τ).exp).congr_deriv (by simp [c])
    have hY : HasDerivAt (fun τ => c τ • p.1 + s τ • p.2)
        ((-c τ) • p.1 + (Real.exp (-2 * τ) / s τ) • p.2) τ :=
      (hcd.smul_const p.1).add ((ou_hasDerivAt_sqrt hτ0).smul_const p.2)
    exact (((hg.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt τ hY).const_smul
      (f p.1)
  obtain ⟨-, h_der⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.prod μ)
    (F := F) (F' := F') (x₀ := t) (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Filter.Eventually.of_forall fun τ => (hFc τ).aestronglyMeasurable)
    (ou_integrable_bdd v (hFc t) (C := Cf * Cg) (fun p => by
      rw [norm_smul]; exact mul_le_mul (hfC _) (hgC _) (norm_nonneg _) hCf))
    hF'c.aestronglyMeasurable hbound hbint hdiff
  refine h_der.congr_deriv ?_
  -- evaluate the derivative through the rotated identity
  have hst : 0 < s t := ou_sqrt_pos ht
  have hc01 : c t ≤ 1 := by
    simp only [c]; rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have hθc : Real.cos (Real.arccos (c t)) = c t :=
    Real.cos_arccos (by linarith [(Real.exp_pos (-t)).le]) hc01
  have hθs : Real.sin (Real.arccos (c t)) = s t := by
    rw [Real.sin_arccos]; simp only [c, s]; rw [ou_exp_sq]
  have hK := ou_rotated_derivative v hf hfC hf'C hg hg'C (Real.arccos (c t))
  rw [hθc, hθs] at hK
  have hpt : ∀ p : (ι → ℝ) × (ι → ℝ), F' t p = (c t / s t) •
      (f p.1 • fderiv ℝ g (c t • p.1 + s t • p.2) (-s t • p.1 + c t • p.2)) := fun p => by
    have e1 : -c t = (c t / s t) * (-s t) := by field_simp
    have e2 : Real.exp (-2 * t) / s t = (c t / s t) * c t := by
      rw [← ou_exp_sq]; simp only [c]; ring
    simp only [F']
    rw [e1, e2, ← smul_smul, ← smul_smul, ← smul_add, map_smul, smul_comm]
  simp_rw [hpt]
  rw [integral_smul, hK, smul_smul]
  congr 1
  field_simp
  rfl

/-- The time kernel `t ↦ E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]` is continuous on `ℝ`. -/
theorem ou_continuous_kernel (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    Continuous (fun t : ℝ => ∫ p, ouDir v f g p.1 (Real.exp (-t) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
          ∂(gaussianProduct v).prod (gaussianProduct v)) := by
  have hd := ou_continuous_dir v hf hg
  have h1 : ∀ t : ℝ, Continuous (fun p : (ι → ℝ) × (ι → ℝ) => (p.1, Real.exp (-t) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) := fun t => by fun_prop
  have h2 : ∀ p : (ι → ℝ) × (ι → ℝ), Continuous (fun t : ℝ => (p.1, Real.exp (-t) • p.1 +
      Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) := fun p => by fun_prop
  exact continuous_of_dominated (bound := fun _ => (∑ i, (v i : ℝ)) * Cf' * Cg')
    (fun t => (hd.comp (h1 t)).aestronglyMeasurable)
    (fun t => Filter.Eventually.of_forall fun p => ou_norm_dir_le v hf'C hg'C _ _)
    (integrable_const _) (Filter.Eventually.of_forall fun p => hd.comp (h2 p))

/-- The time kernel is bounded by `(Σᵢ vᵢ) ‖Df‖_∞ ‖Dg‖_∞`. -/
theorem ou_norm_kernel_le (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℝ) → ℂ} {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') (t : ℝ) :
    ‖∫ p, ouDir v f g p.1 (Real.exp (-t) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * t)) • p.2) ∂(gaussianProduct v).prod (gaussianProduct v)‖ ≤
      (∑ i, (v i : ℝ)) * Cf' * Cg' := by
  have h := norm_integral_le_of_norm_le_const (μ := (gaussianProduct v).prod (gaussianProduct v))
    (Filter.Eventually.of_forall fun p => ou_norm_dir_le v hf'C hg'C p.1
      (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2))
  simpa using h

/-- Integrability of `t ↦ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]` on `(0, ∞)`. -/
theorem ou_integrableOn_kernel (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg' : ℝ} (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    IntegrableOn (fun t : ℝ => Real.exp (-t) • ∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v))
      (Set.Ioi 0) := by
  have hc := ou_continuous_kernel v hf hf'C hg hg'C
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul
    ((∑ i, (v i : ℝ)) * Cf' * Cg')) ((Real.continuous_exp.comp continuous_neg).smul
      hc).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_one_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (ou_norm_kernel_le v hf'C hg'C t) (Real.exp_pos _).le

/-- **Bilinear Ornstein–Uhlenbeck covariance identity**, vector-valued form: for
`μ = gaussianProduct v`, `f : (ι → ℝ) → ℂ` and `g : (ι → ℝ) → E`
`C¹`, bounded, with bounded derivative,
`E[f g] - E f • E g = ∫₀^∞ e^{-t} E_{μ⊗μ}[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(e^{-t}x + √(1-e^{-2t}) x')] dt`.
No conjugation; no hypothesis on `v`. -/
theorem ou_covariance_smul (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    (∫ x, f x • g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, g x ∂gaussianProduct v) =
      ∫ t in Set.Ioi 0, Real.exp (-t) • ∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v) := by
  set μ := gaussianProduct v
  let Ψ : ℝ → E := fun τ => ∫ p, f p.1 • g (Real.exp (-τ) • p.1 +
    Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) ∂μ.prod μ
  let G : ℝ → E := fun τ => ∫ p, ouDir v f g p.1 (Real.exp (-τ) • p.1 +
    Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) ∂μ.prod μ
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hfC 0)
  have hfg : ∀ x y, ‖f x • g y‖ ≤ Cf * Cg := fun x y => by
    rw [norm_smul]; exact mul_le_mul (hfC _) (hgC _) (norm_nonneg _) hCf
  have hΨc : Continuous Ψ :=
    continuous_of_dominated (bound := fun _ => Cf * Cg)
      (fun τ => ((hfc.comp continuous_fst).smul (hgc.comp (by fun_prop))).aestronglyMeasurable)
      (fun τ => Filter.Eventually.of_forall fun p => hfg _ _) (integrable_const _)
      (Filter.Eventually.of_forall fun p => (hfc.comp continuous_const).smul
        (hgc.comp (by fun_prop)))
  have hΨ0 : Ψ 0 = ∫ x, f x • g x ∂μ := by
    simp only [Ψ, neg_zero, Real.exp_zero, mul_zero, sub_self, Real.sqrt_zero, one_smul,
      zero_smul, add_zero]
    rw [integral_fun_fst (fun x => f x • g x)]
    simp
  have hlim : Filter.Tendsto Ψ Filter.atTop (nhds ((∫ x, f x ∂μ) • (∫ x, g x ∂μ))) := by
    rw [← integral_prod_smul]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Cf * Cg)
      (Filter.Eventually.of_forall fun τ =>
        ((hfc.comp continuous_fst).smul (hgc.comp (by fun_prop))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun p => hfg _ _)
      (integrable_const _) (Filter.Eventually.of_forall fun p => ?_)
    have hc : Filter.Tendsto (fun τ : ℝ => Real.exp (-τ)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have he : Filter.Tendsto (fun τ : ℝ => Real.exp (-2 * τ)) Filter.atTop (nhds 0) := by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
      refine this.congr fun τ => ?_
      simp [neg_mul]
    have hs : Filter.Tendsto (fun τ : ℝ => Real.sqrt (1 - Real.exp (-2 * τ))) Filter.atTop
        (nhds 1) := by
      have := ((Real.continuous_sqrt.tendsto (1 - 0)).comp (he.const_sub 1))
      simpa [Function.comp_def] using this
    have hY : Filter.Tendsto (fun τ : ℝ => Real.exp (-τ) • p.1 +
        Real.sqrt (1 - Real.exp (-2 * τ)) • p.2) Filter.atTop (nhds p.2) := by
      have := (hc.smul_const p.1).add (hs.smul_const p.2)
      simpa using this
    exact ((hgc.tendsto _).comp hY).const_smul (f p.1)
  have hint : IntegrableOn (fun τ => -Real.exp (-τ) • G τ) (Set.Ioi 0) := by
    simp_rw [neg_smul]
    exact (ou_integrableOn_kernel v hf hf'C hg hg'C).neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hΨc.continuousWithinAt
    (fun τ hτ => ou_hasDerivAt_interp v hf hfC hf'C hg hgC hg'C hτ) hint hlim
  rw [hΨ0] at hmain
  simp_rw [neg_smul] at hmain
  rw [integral_neg] at hmain
  change _ = ∫ t in Set.Ioi 0, Real.exp (-t) • G t
  rw [← neg_sub, ← hmain, neg_neg]

/-- **Bilinear Ornstein–Uhlenbeck covariance identity**, complex scalar form:
`Cov(f, g) = ∫₀^∞ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)] dt` over `μ ⊗ μ`,
`x_t = e^{-t}x + √(1-e^{-2t}) x'`, bilinear (no conjugation). -/
theorem ou_covariance (v : ι → ℝ≥0) {f g : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) {Cf Cf' Cg Cg' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    (hgC : ∀ x, ‖g x‖ ≤ Cg) (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    (∫ x, f x * g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) * (∫ x, g x ∂gaussianProduct v) =
      ∫ t in Set.Ioi 0, (Real.exp (-t) : ℂ) * ∫ p, ∑ i,
        ((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1) *
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v) := by
  have h := ou_covariance_smul v hf hfC hf'C hg hgC hg'C
  simpa only [smul_eq_mul, Complex.real_smul] using h

/-- Norm form of the covariance identity:
`‖E[f g] - E f • E g‖ ≤ ∫₀^∞ e^{-t} ‖E[Σᵢ vᵢ ∂ᵢ f(x) ∂ᵢ g(x_t)]‖ dt`. -/
theorem ou_covariance_norm_le (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    ‖(∫ x, f x • g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, g x ∂gaussianProduct v)‖ ≤
      ∫ t in Set.Ioi 0, Real.exp (-t) * ‖∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v)‖ := by
  rw [ou_covariance_smul v hf hfC hf'C hg hgC hg'C]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Uniform bound: `‖E[f g] - E f • E g‖ ≤ (Σᵢ vᵢ) ‖Df‖_∞ ‖Dg‖_∞`. -/
theorem ou_covariance_norm_le_const (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') {g : (ι → ℝ) → E}
    (hg : ContDiff ℝ 1 g) {Cg Cg' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ Cg)
    (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    ‖(∫ x, f x • g x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, g x ∂gaussianProduct v)‖ ≤
      (∑ i, (v i : ℝ)) * Cf' * Cg' := by
  rw [ou_covariance_smul v hf hfC hf'C hg hgC hg'C]
  refine (norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).const_mul
    ((∑ i, (v i : ℝ)) * Cf' * Cg')) (Filter.Eventually.of_forall fun t => ?_)).trans
    (le_of_eq ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (ou_norm_kernel_le v hf'C hg'C t) (Real.exp_pos _).le
  · rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- Integrability of the complex time integrand of `ou_covariance` on `(0, ∞)`. -/
theorem ou_integrableOn_kernel_complex (v : ι → ℝ≥0) {f g : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {Cf' Cg' : ℝ}
    (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf') (hg'C : ∀ x, ‖fderiv ℝ g x‖ ≤ Cg') :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ) * ∫ p, ∑ i,
        ((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1) *
          fderiv ℝ g (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v))
      (Set.Ioi 0) := by
  have h := ou_integrableOn_kernel v hf hf'C hg hg'C
  simpa only [smul_eq_mul, Complex.real_smul] using h

open scoped Matrix.Norms.L2Operator in
/-- Matrix-valued covariance identity (Euclidean operator norm on `Matrix κ κ' ℂ`, the
convention of `Inputs`): `E[f G] - E f • E G = ∫₀^∞ e^{-t} E[Σᵢ vᵢ ∂ᵢ f(x) • ∂ᵢ G(x_t)] dt`. -/
theorem ou_covariance_matrix (v : ι → ℝ≥0) {κ κ' : Type*} [Fintype κ] [Fintype κ']
    [DecidableEq κ'] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f) {Cf Cf' : ℝ}
    (hfC : ∀ x, ‖f x‖ ≤ Cf) (hf'C : ∀ x, ‖fderiv ℝ f x‖ ≤ Cf')
    {G : (ι → ℝ) → Matrix κ κ' ℂ} (hG : ContDiff ℝ 1 G) {CG CG' : ℝ}
    (hGC : ∀ x, ‖G x‖ ≤ CG) (hG'C : ∀ x, ‖fderiv ℝ G x‖ ≤ CG') :
    (∫ x, f x • G x ∂gaussianProduct v) -
        (∫ x, f x ∂gaussianProduct v) • (∫ x, G x ∂gaussianProduct v) =
      ∫ t in Set.Ioi 0, Real.exp (-t) • ∫ p, ∑ i,
        (((v i : ℝ) : ℂ) * fderiv ℝ f p.1 (Pi.single i 1)) •
          fderiv ℝ G (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
            (Pi.single i 1) ∂(gaussianProduct v).prod (gaussianProduct v) :=
  ou_covariance_smul v hf hfC hf'C hG hGC hG'C

end BlockBand.Transmission.PassiveLayer
