module

public import BlockBand.Layers.CompensatedFluct
public import BlockBand.Layers.CoreMeans

/-!
# The heat interpolation of the compensated layer increment: `CphIncrementLocal`

The conditional increments of the proof of the compensated phase lemma: the isolated input
`CphIncrementLocal` of `BlockBand.Layers.CompensatedIncrement`.

Law: `layerLaw W b σ` (`A_a ~ GUE_W(c/W)`, `c = 1-2b`, bonds `Gin(b/W)`), realized as the image of
`gaussianProduct (tflVar W b σ)` under `tflEmbed`; deterministic Hermitian two-port `X` (the old
Schur matrix), `E ∈ bulkInterval κ`. Norms: `ℓ²` operator norm on matrices.

* §1 `cht_continuousAt_logDet`: the logarithmic determinant `cplLogDet` is continuous at every
  invertible matrix with `Im ⟨v, M v⟩ ≥ 0` (uniform invertibility of the rays, dominated
  convergence). Deterministic.
* §2–3 **The heat derivative along an affine Gaussian path** `M(t, x) = C₀ + t C₁ + √t Λx`
  (`chtPath`, `Λ` Hermitian-valued, `C₀ + t C₁` coercive on `[0, 1)`):
  `φ(t) = E Im L(M(t, x))` (`chtPhi`) is continuous on `[0, 1]` when `M(1, x)` is a.s. invertible
  (`cht_phi_continuousOn`) and `φ'(t) = Im E[Tr(G C₁) - ½ Tr(S(G) G)]` on `(0, 1)`
  (`cht_hasDerivAt_phi`, `G = M(t,x)⁻¹`, `S(G) = Σᵢ vᵢ Λeᵢ G Λeᵢ`), by `d/dσ` in `σ = √t`,
  dominated differentiation and Gaussian integration by parts (`core_ibp`); mean value step
  `cht_mvt`.
* §4–5 **One fresh layer**: `ℋ_t = [[√t A - E - X - (1-t)(1-b)a, √t B],
  [√t Bᴴ, a⁻¹ + tβa]]` (`chtHeat`; `β = b` separate ports, `β = 2b` common port), deterministic
  heights (`cht_layer_coercive`), the integrand in block traces with constant term `W a²` and a
  quadratic remainder bounded by `W Σ|g - a|² + W Σ|u - a|²` (`cht_integrand_sep_le`,
  `cht_integrand_com_le`; the linear terms vanish since `c + 2b = 1`).
* §6 `cht_layer_main` (integration in `t`), endpoints `cht_phi_zero`
  (`φ(0) = π Θ_{z_∂}(X) + π (#ports · W) ℓ`) and `cht_phi_one` (`φ(1) = π E[N_- + Θ_z(X₊)]`, via
  the phase identity `cpl_tendsto_phase` and the continuity of §1).
* §7 The input `ChtMeanSquare` (trace errors `O_{L²}(d + W⁻¹)`
  uniformly in `t`) and **`cphIncrementLocal_of_meanSquare (hcount) (hms) : CphIncrementLocal`**.

Inputs: `Inputs.ConditionalBlockGUECount` (through `gaussianAbsorption_holds`: a.s.
invertibility of the layer matrix) and the hypothesis `ChtMeanSquare`, proved in
`chtMeanSquare_holds`.
Helper prefix `cht`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct)
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. Continuity of the logarithmic determinant at dissipative invertible matrices
-/

section Dissipative

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cht_norm_sq_add_I (p q : ℂ) (η : ℝ) :
    ‖p + (η : ℂ) * Complex.I * q‖ ^ 2 = ‖p‖ ^ 2 + η ^ 2 * ‖q‖ ^ 2 + 2 * η * (star q * p).im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- `‖(A + iη) v‖² = ‖A v‖² + η² ‖v‖² + 2η Im⟨v, A v⟩`. -/
theorem cht_sq_add_I (A : Matrix n n ℂ) (η : ℝ) (v : n → ℂ) :
    cplSq ((A + ((η : ℂ) * Complex.I) • (1 : Matrix n n ℂ)) *ᵥ v) =
      cplSq (A *ᵥ v) + η ^ 2 * cplSq v + 2 * η * cplForm A v := by
  unfold cplSq cplForm
  rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct, Complex.im_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [cht_norm_sq_add_I]

omit [DecidableEq n] in
theorem cht_sq_smul (r : ℝ) (w : n → ℂ) : cplSq (r • w) = r ^ 2 * cplSq w := by
  unfold cplSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

omit [Fintype n] in
theorem cht_ray_eq (M : Matrix n n ℂ) (t : ℝ) :
    cplRay M t = t • M + (((1 - t : ℝ) : ℂ) * Complex.I) • (1 : Matrix n n ℂ) := by
  unfold cplRay
  rw [add_comm]
  congr 1
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]
  ring

/-- Along the ray of a dissipative `M` with `m ‖v‖² ≤ ‖M v‖²`:
`(m / (1 + m)) ‖v‖² ≤ ‖γ(t) v‖²` for `0 ≤ t ≤ 1`. -/
theorem cht_ray_lower {M : Matrix n n ℂ} (hM : ∀ v, 0 ≤ cplForm M v) {m : ℝ} (hm : 0 < m)
    (hMv : ∀ v, m * cplSq v ≤ cplSq (M *ᵥ v)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : n → ℂ) : m / (1 + m) * cplSq v ≤ cplSq (cplRay M t *ᵥ v) := by
  rw [cht_ray_eq, cht_sq_add_I, smul_mulVec, cht_sq_smul, cpl_form_smul]
  have h1 := hMv v
  have h2 := hM v
  have h3 := cpl_sq_nonneg v
  have h4 : 0 ≤ 2 * (1 - t) * (t * cplForm M v) := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  have h5 : m / (1 + m) * cplSq v ≤ (t ^ 2 * m + (1 - t) ^ 2) * cplSq v := by
    refine mul_le_mul_of_nonneg_right ?_ h3
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg ((1 + m) * t - 1)]
  have h6 : t ^ 2 * m * cplSq v ≤ t ^ 2 * cplSq (M *ᵥ v) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (sq_nonneg t)
  nlinarith

omit [DecidableEq n] in
theorem cht_sq_eq_norm (v : n → ℂ) : cplSq v = ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 :=
  (cpl_norm_toLp_sq v).symm

/-- An invertible matrix satisfies `(‖M⁻¹‖ + 1)⁻² ‖v‖² ≤ ‖M v‖²`. -/
theorem cht_unit_lower {M : Matrix n n ℂ} (hM : IsUnit M) (v : n → ℂ) :
    ((‖M⁻¹‖ + 1) ^ 2)⁻¹ * cplSq v ≤ cplSq (M *ᵥ v) := by
  have hK : 0 < ‖M⁻¹‖ + 1 := by positivity
  have hv : v = M⁻¹ *ᵥ (M *ᵥ v) := by
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det M).mp hM),
      one_mulVec]
  have h1 : ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ≤ (‖M⁻¹‖ + 1) *
      ‖(toLp 2 (M *ᵥ v) : EuclideanSpace ℂ n)‖ := by
    calc ‖(toLp 2 v : EuclideanSpace ℂ n)‖ = ‖(toLp 2 (M⁻¹ *ᵥ (M *ᵥ v)) : EuclideanSpace ℂ n)‖ := by
          rw [← hv]
      _ ≤ ‖M⁻¹‖ * ‖(toLp 2 (M *ᵥ v) : EuclideanSpace ℂ n)‖ := norm_toLp_mulVec_le _ _
      _ ≤ (‖M⁻¹‖ + 1) * ‖(toLp 2 (M *ᵥ v) : EuclideanSpace ℂ n)‖ := by
          gcongr; linarith
  rw [cht_sq_eq_norm, cht_sq_eq_norm, inv_mul_le_iff₀ (by positivity)]
  calc ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 ≤
      ((‖M⁻¹‖ + 1) * ‖(toLp 2 (M *ᵥ v) : EuclideanSpace ℂ n)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := by ring

/-- **Uniform invertibility of the rays near a dissipative invertible matrix.** -/
theorem cht_ray_uniform {M : Matrix n n ℂ} (hM : ∀ v, 0 ≤ cplForm M v) (hMu : IsUnit M) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ M' : Matrix n n ℂ, ‖M' - M‖ < ε → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit (cplRay M' t).det ∧ ‖(cplRay M' t)⁻¹‖ ≤ c⁻¹ := by
  set m := ((‖M⁻¹‖ + 1) ^ 2)⁻¹ with hm
  have hm0 : 0 < m := by positivity
  set ρ := Real.sqrt (m / (1 + m)) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨ρ / 2, ρ / 2, by positivity, by positivity, fun M' hM' t ht => ?_⟩
  refine isUnit_det_and_norm_inv_le_of_lower (by positivity) fun ξ => ?_
  set v : n → ℂ := ofLp ξ with hv
  have hξ : ξ = toLp 2 v := rfl
  have hlow := cht_ray_lower hM hm0 (cht_unit_lower hMu) ht.1 ht.2 v
  rw [cht_sq_eq_norm, cht_sq_eq_norm, ← hξ] at hlow
  have hl1 : ρ * ‖ξ‖ ≤ ‖(toLp 2 (cplRay M t *ᵥ v) : EuclideanSpace ℂ n)‖ := by
    rw [hρ, ← Real.sqrt_sq (norm_nonneg ξ), ← Real.sqrt_mul (by positivity),
      ← Real.sqrt_sq (norm_nonneg (toLp 2 (cplRay M t *ᵥ v) : EuclideanSpace ℂ n))]
    exact Real.sqrt_le_sqrt hlow
  have hdiff : cplRay M' t = cplRay M t + t • (M' - M) := by
    unfold cplRay; rw [smul_sub]; abel
  have h1 : toEuclideanLin (cplRay M' t) ξ =
      toLp 2 (cplRay M t *ᵥ v) + toLp 2 ((t • (M' - M)) *ᵥ v) := by
    rw [hξ, toLpLin_apply, hdiff, add_mulVec]
    rfl
  have h2 : ‖(toLp 2 ((t • (M' - M)) *ᵥ v) : EuclideanSpace ℂ n)‖ ≤ ρ / 2 * ‖ξ‖ := by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [← hξ, norm_smul, Real.norm_of_nonneg ht.1]
    gcongr
    calc t * ‖M' - M‖ ≤ 1 * ‖M' - M‖ := by gcongr; exact ht.2
      _ ≤ ρ / 2 := by rw [one_mul]; exact hM'.le
  rw [h1]
  have h3 := norm_sub_norm_le (toLp 2 (cplRay M t *ᵥ v) : EuclideanSpace ℂ n)
    (-(toLp 2 ((t • (M' - M)) *ᵥ v) : EuclideanSpace ℂ n))
  rw [sub_neg_eq_add, norm_neg] at h3
  linarith

/-- **Continuity of `L` at a dissipative invertible matrix** (`Im ⟨v, M v⟩ ≥ 0` for all `v`,
`M` invertible): the rays `γ(t) = (1-t)i + tM'` stay uniformly invertible for `M'` near `M`,
and dominated convergence applies to `∫₀¹ Tr(γ(t)⁻¹ (M' - i)) dt`. -/
theorem cht_continuousAt_logDet {M : Matrix n n ℂ} (hM : ∀ v, 0 ≤ cplForm M v) (hMu : IsUnit M) :
    ContinuousAt cplLogDet M := by
  obtain ⟨ε, c, hε, hc, hunif⟩ := cht_ray_uniform hM hMu
  unfold cplLogDet
  refine continuousAt_const.add ?_
  set Bd : ℝ := Fintype.card n * (c⁻¹ * (‖M‖ + ε + ‖Complex.I • (1 : Matrix n n ℂ)‖))
  have hball : ∀ᶠ M' in 𝓝 M, ‖M' - M‖ < ε := by
    have := Metric.ball_mem_nhds M hε
    filter_upwards [this] with M' hM'
    rwa [Metric.mem_ball, dist_eq_norm] at hM'
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => Bd)
    (Eventually.of_forall fun M' => (cpl_measurable_integ M').aestronglyMeasurable) ?_
    intervalIntegrable_const ?_
  · filter_upwards [hball] with M' hM'
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨-, hinv⟩ := hunif M' hM' t ⟨ht.1.le, ht.2⟩
    unfold cplInteg
    refine (tfl_trace_le _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    refine (norm_mul_le _ _).trans (mul_le_mul hinv ?_ (norm_nonneg _) (by positivity))
    refine (norm_sub_le _ _).trans ?_
    have : ‖M'‖ ≤ ‖M‖ + ε := by
      have := norm_le_norm_add_norm_sub' M' M
      linarith [norm_sub_rev M' M]
    linarith
  · refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨hu, -⟩ := hunif M (by rw [sub_self, norm_zero]; exact hε) t ⟨ht.1.le, ht.2⟩
    have hU : IsUnit (cplRay M t) := (Matrix.isUnit_iff_isUnit_det _).mpr hu
    have h := NormedRing.inverse_continuousAt hU.unit
    rw [IsUnit.unit_spec] at h
    have hr : Continuous (fun M' : Matrix n n ℂ => cplRay M' t) := by unfold cplRay; fun_prop
    have h1 : ContinuousAt (fun M' : Matrix n n ℂ => Ring.inverse (cplRay M' t)) M :=
      ContinuousAt.comp (g := Ring.inverse) h hr.continuousAt
    have h2 : ContinuousAt (fun M' : Matrix n n ℂ => M' - Complex.I • (1 : Matrix n n ℂ)) M :=
      (continuous_id.sub continuous_const).continuousAt
    have h3 : ContinuousAt (fun M' : Matrix n n ℂ =>
        Ring.inverse (cplRay M' t) * (M' - Complex.I • (1 : Matrix n n ℂ))) M :=
      h1.mul h2
    have h4 : Continuous (fun A : Matrix n n ℂ => A.trace) := continuous_id.matrix_trace
    exact h4.continuousAt.comp h3

end Dissipative

/-!
## 2. Coercivity along an affine path
-/

section Coercive

variable {n : Type} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem cht_form_affine (C₀ C₁ : Matrix n n ℂ) (t : ℝ) (v : n → ℂ) :
    cplForm (C₀ + t • C₁) v = cplForm C₀ v + t * cplForm C₁ v := by
  rw [cpl_form_add, cpl_form_smul]

omit [DecidableEq n] in
theorem cht_coercive_add_herm {δ : ℝ} {M H : Matrix n n ℂ} (hM : cplCoercive δ M)
    (hH : H.IsHermitian) (s : ℝ) : cplCoercive δ (M + s • H) := fun v => by
  rw [cpl_form_add, cpl_form_smul, cpl_form_herm hH, mul_zero, add_zero]
  exact hM v

omit [DecidableEq n] in
/-- Coercivity at two times gives coercivity in between (the form is affine in `t`). -/
theorem cht_coercive_between {C₀ C₁ : Matrix n n ℂ} {δ₁ δ₂ t₁ t₂ t : ℝ}
    (h1 : cplCoercive δ₁ (C₀ + t₁ • C₁)) (h2 : cplCoercive δ₂ (C₀ + t₂ • C₁)) (ht1 : t₁ ≤ t)
    (ht2 : t ≤ t₂) : cplCoercive (min δ₁ δ₂) (C₀ + t • C₁) := fun v => by
  have e1 := h1 v
  have e2 := h2 v
  rw [cht_form_affine] at e1 e2 ⊢
  have hq := cpl_sq_nonneg v
  have hm1 : min δ₁ δ₂ * cplSq v ≤ δ₁ * cplSq v :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hq
  have hm2 : min δ₁ δ₂ * cplSq v ≤ δ₂ * cplSq v :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hq
  rcases le_total 0 (cplForm C₁ v) with h | h
  · nlinarith
  · nlinarith

omit [DecidableEq n] in
/-- Nonnegativity of the form at `t = 1` from coercivity on `[0, 1)`. -/
theorem cht_form_one_nonneg {C₀ C₁ : Matrix n n ℂ}
    (hcoer : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C₀ + t • C₁))
    (v : n → ℂ) : 0 ≤ cplForm (C₀ + C₁) v := by
  have key : ∀ t ∈ Set.Ico (0 : ℝ) 1, 0 ≤ cplForm C₀ v + t * cplForm C₁ v := by
    intro t ht
    obtain ⟨δ, hδ, h⟩ := hcoer t ht
    have := h v
    rw [cht_form_affine] at this
    have := mul_nonneg hδ.le (cpl_sq_nonneg v)
    linarith
  have hc : Tendsto (fun t : ℝ => cplForm C₀ v + t * cplForm C₁ v) (𝓝[<] 1)
      (𝓝 (cplForm C₀ v + 1 * cplForm C₁ v)) :=
    ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 1).mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ cplForm C₀ v + t * cplForm C₁ v := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact key t ⟨ht.1.le, ht.2⟩
  have := ge_of_tendsto hc hev
  rw [one_mul] at this
  rw [cpl_form_add]
  exact this

end Coercive

/-!
## 3. The heat derivative of the expected phase along an affine Gaussian path

`M(t, x) = C₀ + t C₁ + √t Λx` with `Λ` real-linear, Hermitian-valued, `x ~ gaussianProduct v`.
`φ(t) = E Im L(M(t, x))` has derivative `Im E[Tr(G C₁) - ½ Tr(S(G) G)]`, `G = M(t, x)⁻¹`,
`S(G) = Σᵢ vᵢ Λeᵢ G Λeᵢ` (`coreS`): the deterministic part directly, the Gaussian part by
`d/dσ` in `σ = √t` and Gaussian integration by parts (`core_ibp`).
-/

section Heat

variable {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
  {n : Type} [Fintype n] [DecidableEq n]
  (C₀ C₁ : Matrix n n ℂ) (Lin : (ι → ℝ) →L[ℝ] Matrix n n ℂ)

/-- The heat path `M(t, x) = C₀ + t C₁ + √t Λx`. -/
def chtPath (t : ℝ) (x : ι → ℝ) : Matrix n n ℂ := C₀ + t • C₁ + Real.sqrt t • Lin x

/-- The same path in the variable `σ = √t`. -/
def chtPathS (σ : ℝ) (x : ι → ℝ) : Matrix n n ℂ := C₀ + (σ ^ 2) • C₁ + σ • Lin x

/-- `φ(t) = E Im L(M(t, x))`. -/
def chtPhi (t : ℝ) : ℝ := ∫ x, (cplLogDet (chtPath C₀ C₁ Lin t x)).im ∂gaussianProduct v

/-- The (complex) heat derivative `E[Tr(G C₁) - ½ Tr(S(G) G)]`, `G = M(t, x)⁻¹`. -/
def chtDeriv (t : ℝ) : ℂ :=
  ∫ x, ((Ring.inverse (chtPath C₀ C₁ Lin t x) * C₁).trace -
    (coreS v Lin (Ring.inverse (chtPath C₀ C₁ Lin t x)) *
      Ring.inverse (chtPath C₀ C₁ Lin t x)).trace / 2) ∂gaussianProduct v

theorem cht_path_eq_S {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    chtPath C₀ C₁ Lin t x = chtPathS C₀ C₁ Lin (Real.sqrt t) x := by
  rw [chtPath, chtPathS, Real.sq_sqrt ht]

variable {C₀ C₁ Lin}

omit [DecidableEq ι] in
theorem cht_pathS_coercive (hL : ∀ x, (Lin x).IsHermitian) {δ σ : ℝ}
    (h : cplCoercive δ (C₀ + (σ ^ 2) • C₁)) (x : ι → ℝ) :
    cplCoercive δ (chtPathS C₀ C₁ Lin σ x) :=
  cht_coercive_add_herm h (hL x) σ

theorem cht_hasDerivAt_pathS (σ : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => chtPathS C₀ C₁ Lin s x) ((2 * σ) • C₁ + Lin x) σ := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * σ) σ := by
    simpa using hasDerivAt_pow 2 σ
  have h2 := (h1.smul_const C₁).const_add C₀
  have h3 := (hasDerivAt_id σ).smul_const (Lin x)
  simp only [id, one_smul] at h3
  exact h2.add h3

theorem cht_continuous_logDet_im {δ : ℝ} (hδ : 0 < δ) {P : (ι → ℝ) → Matrix n n ℂ}
    (hP : Continuous P) (hc : ∀ x, cplCoercive δ (P x)) :
    Continuous (fun x => (cplLogDet (P x)).im) := by
  refine Complex.continuous_im.comp (continuous_iff_continuousAt.2 fun x => ?_)
  exact (cpl_continuousAt_logDet ⟨δ, hδ, hc x⟩).comp hP.continuousAt

theorem cht_continuous_inv {δ : ℝ} (hδ : 0 < δ) {P : (ι → ℝ) → Matrix n n ℂ}
    (hP : Continuous P) (hc : ∀ x, cplCoercive δ (P x)) :
    Continuous (fun x => Ring.inverse (P x)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hu := cpl_coercive_isUnit hδ (hc x)
  have h := NormedRing.inverse_continuousAt hu.unit
  rw [IsUnit.unit_spec] at h
  exact h.comp hP.continuousAt

theorem cht_norm_inv_le {δ : ℝ} (hδ : 0 < δ) {M : Matrix n n ℂ} (hM : cplCoercive δ M) :
    ‖Ring.inverse M‖ ≤ δ⁻¹ := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]; exact (cpl_coercive_inv hδ hM).2

theorem cht_abs_logDet_im_le {M : Matrix n n ℂ} (hM : M ∈ cplDom n) :
    ‖(cplLogDet M).im‖ ≤ Fintype.card n * Real.pi := by
  have h := cpl_im_logDet_bounds hM
  rw [Real.norm_of_nonneg h.1]; exact h.2

omit [DecidableEq ι] in
theorem cht_continuous_pathS (σ : ℝ) : Continuous (fun x => chtPathS C₀ C₁ Lin σ x) := by
  unfold chtPathS; fun_prop

/-- **The `σ`-derivative** of `ψ(σ) = E Im L(C₀ + σ² C₁ + σ Λx)` at `σ₀`, given coercivity
`δ` of `C₀ + s² C₁` for `|s - σ₀| < r`, `0 < r`, `|s| ≤ 1` there. -/
theorem cht_hasDerivAt_psi (hL : ∀ x, (Lin x).IsHermitian) {σ₀ r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hball : ∀ s ∈ Metric.ball σ₀ r, |s| ≤ 1 ∧ cplCoercive δ (C₀ + (s ^ 2) • C₁)) :
    HasDerivAt (fun σ => ∫ x, (cplLogDet (chtPathS C₀ C₁ Lin σ x)).im ∂gaussianProduct v)
      (∫ x, ((Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) *
        ((2 * σ₀) • C₁ + Lin x)).trace).im ∂gaussianProduct v) σ₀ := by
  set μ := gaussianProduct v
  have hσ₀ := hball σ₀ (Metric.mem_ball_self hr)
  set Bd : (ι → ℝ) → ℝ := fun x =>
    Fintype.card n * (δ⁻¹ * (2 * ‖C₁‖ + ‖Lin‖ * ‖x‖)) with hBd
  have hmeas : ∀ s ∈ Metric.ball σ₀ r,
      Continuous (fun x => (cplLogDet (chtPathS C₀ C₁ Lin s x)).im) := fun s hs =>
    cht_continuous_logDet_im hδ (cht_continuous_pathS s)
      (cht_pathS_coercive hL (hball s hs).2)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := σ₀)
    (F := fun σ x => (cplLogDet (chtPathS C₀ C₁ Lin σ x)).im)
    (F' := fun σ x => ((Ring.inverse (chtPathS C₀ C₁ Lin σ x) *
        ((2 * σ) • C₁ + Lin x)).trace).im) (bound := Bd)
    (Metric.ball_mem_nhds σ₀ hr)
    (by
      filter_upwards [Metric.ball_mem_nhds σ₀ hr] with s hs
      exact (hmeas s hs).aestronglyMeasurable)
    (by
      refine Integrable.of_bound (hmeas σ₀ (Metric.mem_ball_self hr)).aestronglyMeasurable
        (Fintype.card n * Real.pi) (ae_of_all _ fun x => ?_)
      exact cht_abs_logDet_im_le ⟨δ, hδ, cht_pathS_coercive hL hσ₀.2 x⟩)
    (by
      have hc := cht_continuous_inv hδ (cht_continuous_pathS σ₀)
        (cht_pathS_coercive (C₀ := C₀) (C₁ := C₁) hL hσ₀.2)
      exact (Complex.continuous_im.comp ((hc.mul (continuous_const.add
        Lin.continuous)).matrix_trace)).aestronglyMeasurable)
    (ae_of_all _ fun x s hs => by
      have hs' := hball s hs
      refine (Complex.abs_im_le_norm _).trans ((tfl_trace_le _).trans ?_)
      simp only [hBd]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine (norm_mul_le _ _).trans (mul_le_mul (cht_norm_inv_le hδ
        (cht_pathS_coercive hL hs'.2 x)) ?_ (norm_nonneg _) (by positivity))
      refine (norm_add_le _ _).trans (add_le_add ?_ (Lin.le_opNorm x))
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
      have := hs'.1
      have h0 := norm_nonneg C₁
      nlinarith)
    (by
      refine ou_integrable_of_norm_le μ (by
        simp only [hBd]; fun_prop) (Fintype.card n * (δ⁻¹ * (2 * ‖C₁‖)))
        (Fintype.card n * (δ⁻¹ * ‖Lin‖)) fun x => ?_
      simp only [hBd]
      rw [Real.norm_of_nonneg (by positivity)]
      ring_nf; rfl)
    (ae_of_all _ fun x s hs => by
      have hdom : chtPathS C₀ C₁ Lin s x ∈ cplDom n :=
        ⟨δ, hδ, cht_pathS_coercive hL (hball s hs).2 x⟩
      have h1 := (cpl_hasFDerivAt_logDet hdom).comp_hasDerivAt s
        (cht_hasDerivAt_pathS (C₀ := C₀) (C₁ := C₁) (Lin := Lin) s x)
      have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h1
      refine (show HasDerivAt (fun s => (cplLogDet (chtPathS C₀ C₁ Lin s x)).im) _ s from
        h2).congr_deriv ?_
      simp [cplTrMul_apply])
  exact key.2

theorem cht_coreS_smul (σ : ℝ) (G : Matrix n n ℂ) :
    coreS v (σ • Lin) G = (σ ^ 2) • coreS v Lin G := by
  unfold coreS
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [_root_.smul_apply, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

theorem cht_integrable_trace_mul_lin {δ : ℝ} (hδ : 0 < δ) {P : (ι → ℝ) → Matrix n n ℂ}
    (hP : Continuous P) (hc : ∀ x, cplCoercive δ (P x)) :
    Integrable (fun x => (Ring.inverse (P x) * Lin x).trace) (gaussianProduct v) := by
  refine ou_integrable_of_norm_le _ (((cht_continuous_inv hδ hP hc).mul
    Lin.continuous).matrix_trace).aestronglyMeasurable 0 (Fintype.card n * (δ⁻¹ * ‖Lin‖))
    fun x => ?_
  refine (tfl_trace_le _).trans ?_
  rw [zero_add, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_mul_le _ _).trans ?_
  calc ‖Ring.inverse (P x)‖ * ‖Lin x‖ ≤ δ⁻¹ * (‖Lin‖ * ‖x‖) :=
        mul_le_mul (cht_norm_inv_le hδ (hc x)) (Lin.le_opNorm x) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem cht_integrable_trace_mul_const {δ : ℝ} (hδ : 0 < δ) {P : (ι → ℝ) → Matrix n n ℂ}
    (hP : Continuous P) (hc : ∀ x, cplCoercive δ (P x)) (C : Matrix n n ℂ) :
    Integrable (fun x => (Ring.inverse (P x) * C).trace) (gaussianProduct v) := by
  refine Integrable.of_bound (((cht_continuous_inv hδ hP hc).mul
    continuous_const).matrix_trace).aestronglyMeasurable (Fintype.card n * (δ⁻¹ * ‖C‖))
    (ae_of_all _ fun x => ?_)
  refine (tfl_trace_le _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (cht_norm_inv_le hδ (hc x))
    (norm_nonneg _))

theorem cht_integrable_trace_S {δ : ℝ} (hδ : 0 < δ) {P : (ι → ℝ) → Matrix n n ℂ}
    (hP : Continuous P) (hc : ∀ x, cplCoercive δ (P x)) :
    Integrable (fun x => (coreS v Lin (Ring.inverse (P x)) * Ring.inverse (P x)).trace)
      (gaussianProduct v) := by
  refine Integrable.of_bound (((core_continuous_S_mul v Lin).comp
    (cht_continuous_inv hδ hP hc)).matrix_trace).aestronglyMeasurable
    (Fintype.card n * (coreCS v Lin * δ⁻¹ * δ⁻¹)) (ae_of_all _ fun x => ?_)
  refine (tfl_trace_le _).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have hG := cht_norm_inv_le hδ (hc x)
  have hS := core_norm_S_le v Lin (Ring.inverse (P x))
  have h0 := coreCS_nonneg v Lin
  calc ‖coreS v Lin (Ring.inverse (P x)) * Ring.inverse (P x)‖
      ≤ ‖coreS v Lin (Ring.inverse (P x))‖ * ‖Ring.inverse (P x)‖ := norm_mul_le _ _
    _ ≤ (coreCS v Lin * δ⁻¹) * δ⁻¹ := by
        gcongr
        exact hS.trans (mul_le_mul_of_nonneg_left hG h0)

/-- **Gaussian integration by parts** along the path:
`E Tr(G Λx) = -σ E Tr(S(G) G)`, `G = (C₀ + σ² C₁ + σ Λx)⁻¹`. -/
theorem cht_ibp (hL : ∀ x, (Lin x).IsHermitian) {σ δ : ℝ} (hσ : σ ≠ 0) (hδ : 0 < δ)
    (hc : cplCoercive δ (C₀ + (σ ^ 2) • C₁)) :
    ∫ x, (Ring.inverse (chtPathS C₀ C₁ Lin σ x) * Lin x).trace ∂gaussianProduct v =
      -(σ : ℂ) * ∫ x, (coreS v Lin (Ring.inverse (chtPathS C₀ C₁ Lin σ x)) *
        Ring.inverse (chtPathS C₀ C₁ Lin σ x)).trace ∂gaussianProduct v := by
  set μ := gaussianProduct v
  set C0' : Matrix n n ℂ := C₀ + (σ ^ 2) • C₁ - ((δ : ℂ) * Complex.I) • 1 with hC0'
  set L' : (ι → ℝ) →L[ℝ] Matrix n n ℂ := σ • Lin with hL'
  have hpsi : ∀ κ x, corePsi C0' L' κ x =
      chtPathS C₀ C₁ Lin σ x + (((κ - δ : ℝ) : ℂ) * Complex.I) • (1 : Matrix n n ℂ) := by
    intro κ x
    rw [corePsi, hC0', hL', chtPathS, _root_.smul_apply]
    push_cast
    rw [sub_mul, sub_smul]
    abel
  have hreg : CoreReg C0' L' := by
    intro κ hκ x
    have hcx : cplCoercive κ (corePsi C0' L' κ x) := by
      intro w
      rw [hpsi, cpl_form_add]
      have h1 := cht_pathS_coercive hL hc x w
      have h2 := (cpl_coercive_scalar (w := ((κ - δ : ℝ) : ℂ) * Complex.I)
        (p := n)) w
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one] at h2
      nlinarith
    exact ⟨cpl_coercive_isUnit hκ hcx, cht_norm_inv_le hκ hcx⟩
  have hG : ∀ x, coreG C0' L' δ x = Ring.inverse (chtPathS C₀ C₁ Lin σ x) := by
    intro x
    rw [coreG, hpsi, sub_self]
    simp
  have hcP : ∀ x, cplCoercive δ (chtPathS C₀ C₁ Lin σ x) := cht_pathS_coercive hL hc
  have hP : Continuous (fun x => chtPathS C₀ C₁ Lin σ x) := cht_continuous_pathS σ
  have hibp := core_ibp v hreg hδ
  simp only [hG] at hibp
  have hi1 : Integrable (fun x => L' x * Ring.inverse (chtPathS C₀ C₁ Lin σ x)) μ := by
    refine ou_integrable_of_norm_le μ ((L'.continuous.mul
      (cht_continuous_inv hδ hP hcP)).aestronglyMeasurable) 0 (‖L'‖ * δ⁻¹) fun x => ?_
    rw [zero_add]
    calc ‖L' x * Ring.inverse (chtPathS C₀ C₁ Lin σ x)‖
        ≤ ‖L' x‖ * ‖Ring.inverse (chtPathS C₀ C₁ Lin σ x)‖ := norm_mul_le _ _
      _ ≤ (‖L'‖ * ‖x‖) * δ⁻¹ :=
          mul_le_mul (L'.le_opNorm x) (cht_norm_inv_le hδ (hcP x)) (norm_nonneg _)
            (by positivity)
      _ = ‖L'‖ * δ⁻¹ * ‖x‖ := by ring
  have hi2 : Integrable (fun x => coreS v L' (Ring.inverse (chtPathS C₀ C₁ Lin σ x)) *
      Ring.inverse (chtPathS C₀ C₁ Lin σ x)) μ := by
    refine Integrable.of_bound (((core_continuous_S_mul v L').comp
      (cht_continuous_inv hδ hP hcP))).aestronglyMeasurable (coreCS v L' * δ⁻¹ * δ⁻¹)
      (ae_of_all _ fun x => ?_)
    have hGx := cht_norm_inv_le hδ (hcP x)
    have hS := core_norm_S_le v L' (Ring.inverse (chtPathS C₀ C₁ Lin σ x))
    have h0 := coreCS_nonneg v L'
    calc ‖coreS v L' (Ring.inverse (chtPathS C₀ C₁ Lin σ x)) *
          Ring.inverse (chtPathS C₀ C₁ Lin σ x)‖
        ≤ ‖coreS v L' (Ring.inverse (chtPathS C₀ C₁ Lin σ x))‖ *
          ‖Ring.inverse (chtPathS C₀ C₁ Lin σ x)‖ := norm_mul_le _ _
      _ ≤ (coreCS v L' * δ⁻¹) * δ⁻¹ := by
          gcongr
          exact hS.trans (mul_le_mul_of_nonneg_left hGx h0)
  have h1 := congrArg cplTr hibp
  rw [map_neg, ← cplTr.integral_comp_comm hi1, ← cplTr.integral_comp_comm hi2] at h1
  simp only [cplTr_apply, hL', _root_.smul_apply, cht_coreS_smul, Matrix.smul_mul,
    trace_smul] at h1
  have h2 : ∀ x, (Lin x * Ring.inverse (chtPathS C₀ C₁ Lin σ x)).trace =
      (Ring.inverse (chtPathS C₀ C₁ Lin σ x) * Lin x).trace := fun x => trace_mul_comm _ _
  simp only [h2] at h1
  rw [integral_smul, integral_smul] at h1
  have hσ' : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  apply mul_left_cancel₀ hσ'
  rw [Complex.real_smul] at h1
  rw [h1]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- Local uniform coercivity in `σ = √t` around `σ₀ ∈ (0, 1)`. -/
theorem cht_local_coercive
    (hcoer : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C₀ + t • C₁))
    {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ∀ s ∈ Metric.ball σ₀ r,
      0 < s ∧ |s| ≤ 1 ∧ cplCoercive δ (C₀ + (s ^ 2) • C₁) := by
  set r := min σ₀ (1 - σ₀) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; exact half_pos (lt_min h0 (by linarith))
  have hr1 : r ≤ σ₀ / 2 := by rw [hr]; linarith [min_le_left σ₀ (1 - σ₀)]
  have hr2 : r ≤ (1 - σ₀) / 2 := by rw [hr]; linarith [min_le_right σ₀ (1 - σ₀)]
  obtain ⟨δ₁, hδ₁, hc₁⟩ := hcoer ((σ₀ - r) ^ 2) ⟨sq_nonneg _, by nlinarith⟩
  obtain ⟨δ₂, hδ₂, hc₂⟩ := hcoer ((σ₀ + r) ^ 2) ⟨sq_nonneg _, by nlinarith⟩
  refine ⟨r, min δ₁ δ₂, hr0, lt_min hδ₁ hδ₂, fun s hs => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have hs0 : 0 < s := by linarith
  refine ⟨hs0, by rw [abs_of_pos hs0]; linarith, ?_⟩
  exact cht_coercive_between hc₁ hc₂ (by nlinarith) (by nlinarith)

/-- **The heat derivative**: for `t ∈ (0, 1)`,
`φ'(t) = Im E[Tr(G C₁) - ½ Tr(S(G) G)]`. -/
theorem cht_hasDerivAt_phi (hL : ∀ x, (Lin x).IsHermitian)
    (hcoer : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C₀ + t • C₁))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (chtPhi v C₀ C₁ Lin) (chtDeriv v C₀ C₁ Lin t₀).im t₀ := by
  set μ := gaussianProduct v
  set σ₀ := Real.sqrt t₀ with hσ₀
  have hσ0 : 0 < σ₀ := Real.sqrt_pos.mpr ht₀.1
  have hσ1 : σ₀ < 1 := by
    rw [hσ₀, Real.sqrt_lt' one_pos, one_pow]; exact ht₀.2
  obtain ⟨r, δ, hr, hδ, hball⟩ := cht_local_coercive hcoer hσ0 hσ1
  have hψ := cht_hasDerivAt_psi v hL hr hδ fun s hs => ⟨(hball s hs).2.1, (hball s hs).2.2⟩
  have hsq := Real.hasDerivAt_sqrt ht₀.1.ne'
  have hcomp := hψ.comp t₀ hsq
  have hev : chtPhi v C₀ C₁ Lin =ᶠ[𝓝 t₀] (fun σ => ∫ x, (cplLogDet (chtPathS C₀ C₁ Lin σ x)).im
      ∂gaussianProduct v) ∘ Real.sqrt := by
    filter_upwards [Ioi_mem_nhds ht₀.1] with t ht
    simp only [Function.comp_apply, chtPhi]
    exact integral_congr_ae (ae_of_all _ fun x =>
      congrArg (fun M => (cplLogDet M).im) (cht_path_eq_S C₀ C₁ Lin (le_of_lt ht) x))
  refine (hcomp.congr_of_eventuallyEq hev).congr_deriv ?_
  -- identify the derivative
  have hc0 := (hball σ₀ (Metric.mem_ball_self hr)).2.2
  have hcP : ∀ x, cplCoercive δ (chtPathS C₀ C₁ Lin σ₀ x) := cht_pathS_coercive hL hc0
  have hP : Continuous (fun x => chtPathS C₀ C₁ Lin σ₀ x) := cht_continuous_pathS σ₀
  have hiC := cht_integrable_trace_mul_const v hδ hP hcP C₁
  have hiL := cht_integrable_trace_mul_lin v (Lin := Lin) hδ hP hcP
  have hiS := cht_integrable_trace_S v (Lin := Lin) hδ hP hcP
  have hibp := cht_ibp v hL hσ0.ne' hδ hc0
  have hsplit : ∀ x, (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) * ((2 * σ₀) • C₁ + Lin x)).trace =
      ((2 * σ₀ : ℝ) : ℂ) * (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) * C₁).trace +
        (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) * Lin x).trace := by
    intro x
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, Complex.real_smul]
  have hint : ∫ x, ((Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) *
      ((2 * σ₀) • C₁ + Lin x)).trace).im ∂μ =
      (((2 * σ₀ : ℝ) : ℂ) * ∫ x, (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) * C₁).trace ∂μ +
        -(σ₀ : ℂ) * ∫ x, (coreS v Lin (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x)) *
          Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x)).trace ∂μ).im := by
    have hfull : Integrable (fun x => (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) *
        ((2 * σ₀) • C₁ + Lin x)).trace) μ :=
      ((hiC.const_mul ((2 * σ₀ : ℝ) : ℂ)).add hiL).congr (ae_of_all _ fun x => (hsplit x).symm)
    have e1 := Complex.imCLM.integral_comp_comm hfull
    simp only [Complex.imCLM_apply] at e1
    rw [e1, integral_congr_ae (ae_of_all _ hsplit), integral_add (hiC.const_mul _) hiL,
      integral_const_mul, hibp]
  have hD : chtDeriv v C₀ C₁ Lin t₀ = ∫ x, (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) * C₁).trace ∂μ -
      (∫ x, (coreS v Lin (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x)) *
          Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x)).trace ∂μ) / 2 := by
    unfold chtDeriv
    simp only [cht_path_eq_S C₀ C₁ Lin ht₀.1.le]
    rw [integral_sub hiC (hiS.div_const _), integral_div]
  rw [hint, hD]
  set A := ∫ x, (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x) * C₁).trace ∂μ
  set B := ∫ x, (coreS v Lin (Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x)) *
          Ring.inverse (chtPathS C₀ C₁ Lin σ₀ x)).trace ∂μ
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.neg_re, Complex.neg_im, neg_zero, Complex.sub_im, Complex.div_ofNat_im]
  rw [← hσ₀]
  field_simp
  ring

omit [DecidableEq ι] in
theorem cht_continuous_path (x : ι → ℝ) : Continuous (fun t => chtPath C₀ C₁ Lin t x) := by
  unfold chtPath; fun_prop

theorem cht_path_one (x : ι → ℝ) : chtPath C₀ C₁ Lin 1 x = C₀ + C₁ + Lin x := by
  simp [chtPath]

theorem cht_path_coercive (hL : ∀ x, (Lin x).IsHermitian) {δ t : ℝ}
    (h : cplCoercive δ (C₀ + t • C₁)) (x : ι → ℝ) : cplCoercive δ (chtPath C₀ C₁ Lin t x) :=
  cht_coercive_add_herm h (hL x) _

/-- Pointwise continuity of `t ↦ Im L(M(t, x))` on `[0, 1]` where `M(1, x)` is invertible. -/
theorem cht_continuousAt_path_logDet (hL : ∀ x, (Lin x).IsHermitian)
    (hcoer : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C₀ + t • C₁))
    {x : ι → ℝ} (hx : IsUnit (C₀ + C₁ + Lin x)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun s => (cplLogDet (chtPath C₀ C₁ Lin s x)).im) t := by
  refine Complex.continuous_im.continuousAt.comp ?_
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    have hdis : ∀ w, 0 ≤ cplForm (chtPath C₀ C₁ Lin 1 x) w := by
      intro w
      rw [cht_path_one, cpl_form_add, cpl_form_herm (hL x), add_zero]
      exact cht_form_one_nonneg hcoer w
    have hu : IsUnit (chtPath C₀ C₁ Lin 1 x) := by rw [cht_path_one]; exact hx
    exact (cht_continuousAt_logDet hdis hu).comp (f := fun s => chtPath C₀ C₁ Lin s x)
      (cht_continuous_path (C₀ := C₀) (C₁ := C₁) (Lin := Lin) x).continuousAt
  · obtain ⟨δ, hδ, hc⟩ := hcoer t ⟨ht.1, h1⟩
    exact (cpl_continuousAt_logDet ⟨δ, hδ, cht_path_coercive hL hc x⟩).comp
      (f := fun s => chtPath C₀ C₁ Lin s x)
      (cht_continuous_path (C₀ := C₀) (C₁ := C₁) (Lin := Lin) x).continuousAt

/-- **Continuity of `φ` on `[0, 1]`** when `M(1, x)` is almost surely invertible (dominated
convergence, `0 ≤ Im L ≤ dim · π`). -/
theorem cht_phi_continuousOn (hL : ∀ x, (Lin x).IsHermitian)
    (hcoer : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C₀ + t • C₁))
    (hunit : ∀ᵐ x ∂gaussianProduct v, IsUnit (C₀ + C₁ + Lin x)) :
    ContinuousOn (chtPhi v C₀ C₁ Lin) (Set.Icc 0 1) := by
  set μ := gaussianProduct v
  set F : ℝ → (ι → ℝ) → ℝ := fun t x => (cplLogDet (chtPath C₀ C₁ Lin t x)).im with hF
  have hlow : ∀ t ∈ Set.Ico (0 : ℝ) 1, Continuous (F t) ∧ ∀ x, ‖F t x‖ ≤ Fintype.card n * Real.pi := by
    intro t ht
    obtain ⟨δ, hδ, hc⟩ := hcoer t ht
    refine ⟨cht_continuous_logDet_im hδ (by unfold chtPath; fun_prop)
      (cht_path_coercive hL hc), fun x => ?_⟩
    exact cht_abs_logDet_im_le ⟨δ, hδ, cht_path_coercive hL hc x⟩
  have hcont : ∀ᵐ x ∂μ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ContinuousAt (fun s => F s x) t := by
    filter_upwards [hunit] with x hx t ht
    exact cht_continuousAt_path_logDet hL hcoer hx ht
  have hbd1 : ∀ᵐ x ∂μ, ‖F 1 x‖ ≤ Fintype.card n * Real.pi := by
    filter_upwards [hcont] with x hx
    have h1 := (hx 1 ⟨zero_le_one, le_rfl⟩).norm.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
    refine le_of_tendsto h1 ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with s hs
    exact (hlow s ⟨hs.1.le, hs.2⟩).2 x
  have hmeas1 : AEStronglyMeasurable (F 1) μ := by
    set u : ℕ → ℝ := fun j => 1 - cplKappa (j + 1) with hu
    have hu1 : ∀ j, u j ∈ Set.Ico (0 : ℝ) 1 := by
      intro j
      have h2 := cpl_kappa_pos (j + 1)
      have h3 : cplKappa (j + 1) ≤ 1 := by
        unfold cplKappa
        rw [div_le_one (by positivity)]
        push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      exact ⟨by rw [hu]; linarith, by rw [hu]; linarith⟩
    have hut : Tendsto u atTop (𝓝 1) := by
      have h := cpl_tendsto_kappa.comp (tendsto_add_atTop_nat 1)
      simpa [hu] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun j => F (u j))
      (fun j => (hlow (u j) (hu1 j)).1.aestronglyMeasurable) ?_
    filter_upwards [hcont] with x hx
    exact ((hx 1 ⟨zero_le_one, le_rfl⟩).tendsto).comp hut
  refine continuousOn_of_dominated (bound := fun _ => Fintype.card n * Real.pi) ?_ ?_
    (integrable_const _) ?_
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1]; exact hmeas1
    · exact (hlow t ⟨ht.1, h1⟩).1.aestronglyMeasurable
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1]; exact hbd1
    · exact ae_of_all _ (hlow t ⟨ht.1, h1⟩).2
  · filter_upwards [hcont] with x hx
    exact fun t ht => (hx t ht).continuousWithinAt

end Heat

/-- **Mean value step**: `|φ(1) - φ(0) - X| ≤ K` if `|φ'(t) - X| ≤ K` on `(0, 1)`. -/
theorem cht_mvt {φ D : ℝ → ℝ} {X K : ℝ} (hc : ContinuousOn φ (Set.Icc 0 1))
    (hd : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (D t) t)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) 1, |D t - X| ≤ K) : |φ 1 - φ 0 - X| ≤ K := by
  obtain ⟨c, hc', hD⟩ := exists_hasDerivAt_eq_slope φ D zero_lt_one hc hd
  rw [sub_zero, div_one] at hD
  rw [← hD]
  exact hb c hc'

/-!
## 4. The heat path of one fresh layer
-/

section LayerPath

variable {W : ℕ} (σ : LayerShape) (b E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
  (β : ℝ)

/-- `C₀ = [[-E - X - (1-b)a, 0], [0, a⁻¹]]` (at `t = 0`). -/
def chtC0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (-((E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) - X -
    (((1 - b : ℝ) : ℂ) * matchedA E) • 1) 0 0 ((matchedA E)⁻¹ • 1)

/-- `C₁ = [[(1-b)a, 0], [0, βa]]` (`β = b` separate ports, `β = 2b` common port). -/
def chtC1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks ((((1 - b : ℝ) : ℂ) * matchedA E) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ))
    0 0 (((β : ℂ) * matchedA E) • 1)

/-- The Gaussian part `[[A, B], [Bᴴ, 0]]` of a layer sample. -/
def chtLinS (ω : LayerSample W σ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  fromBlocks (Internal.Contracts.Layers.blockDiag ω.1) (bondMatrix σ ω.2) (bondMatrix σ ω.2)ᴴ 0

/-- **The heat interpolation**:
`ℋ_t = [[√t A - E - X - (1-t)(1-b)a, √t B], [√t Bᴴ, a⁻¹ + tβa]] = C₀ + t C₁ + √t [[A, B], [Bᴴ, 0]]`. -/
def chtHeat (t : ℝ) (ω : LayerSample W σ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  chtC0 σ b E X + t • chtC1 σ b E β + Real.sqrt t • chtLinS σ ω

/-- The block-trace error `Σ_k |g_k - a|² + Σ_j |u_j - a|²` of a resolvent. -/
def chtErr (E : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) : ℝ :=
  ∑ k, ‖physBlockTrace G k - matchedA E‖ ^ 2 + ∑ j, ‖portBlockTrace G j - matchedA E‖ ^ 2

theorem cht_linS_eq (ω : LayerSample W σ) : chtLinS σ ω = layerMatrix σ 0 0 0 ω := by
  rw [chtLinS, layerMatrix]
  simp

theorem cht_measurable_linS : Measurable (chtLinS (W := W) σ) := by
  have : chtLinS (W := W) σ = layerMatrix σ 0 0 0 := funext (cht_linS_eq σ)
  rw [this]; exact measurable_layerMatrix σ 0 0 0

theorem cht_measurable_heat (t : ℝ) : Measurable (chtHeat σ b E X β t) := by
  unfold chtHeat
  exact measurable_const.add ((continuous_const_smul (Real.sqrt t)).measurable.comp
    (cht_measurable_linS σ))

theorem cht_linS_embed (x : TflCoord W σ → ℝ) :
    chtLinS σ (tflEmbed W b σ x) = meqLc W b σ x := rfl

theorem cht_heat_embed (t : ℝ) (x : TflCoord W σ → ℝ) :
    chtHeat σ b E X β t (tflEmbed W b σ x) =
      chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) t x := by
  rw [chtHeat, chtPath, cht_linS_embed]

theorem cht_lin_isHermitian (x : TflCoord W σ → ℝ) : (meqLc W b σ x).IsHermitian := by
  rw [meqLc_apply, tflLin]
  exact IsHermitian.fromBlocks (tflEmbed_blockDiag_isHermitian W b σ x) rfl isHermitian_zero

theorem cht_C0_add_C1 :
    chtC0 σ b E X + chtC1 σ b E β = tflConst σ E ((matchedA E)⁻¹ + (β : ℂ) * matchedA E) X := by
  rw [chtC0, chtC1, tflConst, fromBlocks_add, add_zero, add_zero, add_smul]
  congr 1
  abel

/-- At `t = 1` the heat matrix is the layer matrix with port parameter `a⁻¹ + βa`. -/
theorem cht_path_one_layer (x : TflCoord W σ → ℝ) :
    chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 1 x =
      layerMatrix σ E ((matchedA E)⁻¹ + (β : ℂ) * matchedA E) X (tflEmbed W b σ x) := by
  rw [cht_path_one, cht_C0_add_C1, tfl_layerMatrix_embed, meqLc_apply]

variable {σ b E X β}

/-- `C₀ = [[z_∂ - X, 0], [0, a⁻¹]]` for `|E| ≤ 2`. -/
theorem cht_C0_eq (hE : |E| ≤ 2) :
    chtC0 σ b E X = fromBlocks (boundaryZ b E • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X)
      0 0 ((matchedA E)⁻¹ • 1) := by
  rw [chtC0]
  congr 1
  have h := matchedA_add_inv hE
  have e : boundaryZ b E = -(E : ℂ) - ((1 - b : ℝ) : ℂ) * matchedA E := by
    rw [boundaryZ, ← h]; push_cast; ring
  rw [e, sub_smul, neg_smul]
  abel

theorem cht_coercive_fromBlocks {m p : Type} [Fintype m] [DecidableEq m] [Fintype p]
    [DecidableEq p] {δ : ℝ} (hδ : 0 < δ) {A : Matrix m m ℂ} {D : Matrix p p ℂ}
    (hA : cplCoercive δ A) (hD : cplCoercive δ D) :
    cplCoercive δ (fromBlocks A 0 0 D) := by
  have h := cpl_coercive_schurPath hδ hA hD 0 zero_le_one le_rfl
  simpa using h

theorem cht_coercive_herm_scalar {m : Type} [Fintype m] [DecidableEq m] {H : Matrix m m ℂ}
    (hH : H.IsHermitian) (w : ℂ) : cplCoercive w.im (H + w • (1 : Matrix m m ℂ)) := fun v => by
  rw [cpl_form_add, cpl_form_herm hH, zero_add]
  exact cpl_coercive_scalar v

/-- **Deterministic heights**: for `t ∈ [0, 1)`, `C₀ + t C₁` is coercive
(top height `(1-t)(1-b)(-Im a) > 0`, port height `(1-tβ)(-Im a) > 0`). -/
theorem cht_layer_coercive (hb1 : b < 1 / 2) (hβ0 : 0 ≤ β) (hβ : β ≤ 2 * b) (hE : |E| < 2)
    (hX : X.IsHermitian) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (chtC0 σ b E X + t • chtC1 σ b E β) := by
  intro t ht
  have ha := matchedA_im_neg hE
  set γ := -(matchedA E).im with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hinv : ((matchedA E)⁻¹).im = γ := by
    rw [inv_matchedA hE.le, Complex.conj_im]
  have h1 : 0 < (1 - t) * (1 - b) * γ := by
    have : 0 < 1 - t := by linarith [ht.2]
    have : 0 < 1 - b := by linarith
    positivity
  have h2 : 0 < (1 - t * β) * γ := by
    have : t * β ≤ 1 * (2 * b) := mul_le_mul ht.2.le hβ hβ0 zero_le_one
    have : 0 < 1 - t * β := by linarith
    positivity
  refine ⟨min ((1 - t) * (1 - b) * γ) ((1 - t * β) * γ), lt_min h1 h2, ?_⟩
  have heq : chtC0 σ b E X + t • chtC1 σ b E β =
      fromBlocks ((-((E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) - X) +
          (-((1 - t : ℝ) : ℂ) * (((1 - b : ℝ) : ℂ) * matchedA E)) • 1) 0 0
        (((matchedA E)⁻¹ + (t : ℂ) * ((β : ℂ) * matchedA E)) • 1) := by
    rw [chtC0, chtC1, fromBlocks_smul, fromBlocks_add]
    simp only [smul_zero, add_zero]
    congr 1
    · ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Complex.real_smul]
      split_ifs <;> push_cast <;> ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        Complex.real_smul]
      split_ifs <;> ring
  rw [heq]
  have hH : (-((E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)) - X).IsHermitian := by
    refine (IsHermitian.neg ?_).sub hX
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  refine cht_coercive_fromBlocks (lt_min h1 h2) ?_ ?_
  · refine cpl_coercive_mono (min_le_left _ _) ?_
    have := cht_coercive_herm_scalar hH (-((1 - t : ℝ) : ℂ) * (((1 - b : ℝ) : ℂ) * matchedA E))
    refine cpl_coercive_mono (le_of_eq ?_) this
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.neg_re, hγ]
    ring
  · refine cpl_coercive_mono (min_le_right _ _) ?_
    refine cpl_coercive_mono (le_of_eq ?_) cpl_coercive_scalar
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, hinv, Complex.mul_re, sub_zero, hγ]
    ring

end LayerPath

/-!
## 5. The heat derivative of a layer in block traces
-/

section LayerDeriv

variable {W : ℕ} {σ : LayerShape}

theorem cht_trace_diagonal_mul (d : LayerSite W σ → ℂ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (diagonal d * G).trace = ∑ x, d x * G x x := by
  simp [Matrix.trace, diagonal_mul]

theorem cht_trace_mul_diagonal (d : LayerSite W σ → ℂ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (G * diagonal d).trace = ∑ x, G x x * d x := by
  simp [Matrix.trace, mul_diagonal]

theorem cht_sum_phys (hW : 0 < W) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (k : Fin σ.blocks) :
    ∑ α : Fin W, G (Sum.inl (k, α)) (Sum.inl (k, α)) = (W : ℂ) * physBlockTrace G k := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  rw [physBlockTrace, ← mul_assoc, mul_inv_cancel₀ hW', one_mul]

theorem cht_sum_port (hW : 0 < W) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (j : Fin σ.ports) :
    ∑ α : Fin W, G (Sum.inr (j, α)) (Sum.inr (j, α)) = (W : ℂ) * portBlockTrace G j := by
  have hW' : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hW.ne'
  rw [portBlockTrace, ← mul_assoc, mul_inv_cancel₀ hW', one_mul]

theorem cht_C1_diagonal (b E β : ℝ) :
    chtC1 (W := W) σ b E β = diagonal (Sum.elim (fun _ => ((1 - b : ℝ) : ℂ) * matchedA E)
      (fun _ => (β : ℂ) * matchedA E)) := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [chtC1, diagonal_apply, Matrix.one_apply]

/-- `Tr(G C₁) = W [(1-b) a Σ_k g_k + β a Σ_j u_j]`. -/
theorem cht_trace_C1 (hW : 0 < W) (b E β : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (G * chtC1 σ b E β).trace = (W : ℂ) * ((((1 - b : ℝ) : ℂ) * matchedA E) *
      ∑ k, physBlockTrace G k + ((β : ℂ) * matchedA E) * ∑ j, portBlockTrace G j) := by
  rw [cht_C1_diagonal, cht_trace_mul_diagonal, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.sum_mul, cht_sum_phys hW, cht_sum_port hW,
    Finset.mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

/-- `Tr(S(G) G) = W [Σ_k (c g_k + b Σ_j inc u_j) g_k + Σ_j b (Σ_k inc g_k) u_j]`. -/
theorem cht_trace_S (hW : 0 < W) {b : ℝ} (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (meqS W b σ G * G).trace = (W : ℂ) * (
      ∑ k, ((W : ℂ) * ((tflTA W b : ℝ) : ℂ) * physBlockTrace G k +
        (W : ℂ) * ((tflTB W b : ℝ) : ℂ) * ∑ j, meqInc σ k j * portBlockTrace G j) *
          physBlockTrace G k +
      ∑ j, ((W : ℂ) * ((tflTB W b : ℝ) : ℂ) * ∑ k, meqInc σ k j * physBlockTrace G k) *
          portBlockTrace G j) := by
  rw [meqS_eq hW, meqShift, cht_trace_diagonal_mul, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum, cht_sum_phys hW, cht_sum_port hW]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · ring
  · exact Finset.sum_congr rfl fun k _ => by ring

theorem cht_norm_mul_le_sq (x y : ℂ) : ‖x * y‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [norm_mul]; nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- **Separate ports**: the integrand is
`W [(1-b)a(g₁+g₂) + ba(u₁+u₂) - (c/2)(g₁²+g₂²) - b(g₁u₁+g₂u₂)]`; its constant term is `W a²`
and, since `c + 2b = 1`, it equals `W a² - W[(c/2) Σ(g_k-a)² + b Σ(g_k-a)(u_k-a)]`. -/
theorem cht_integrand_sep_le (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (E : ℝ)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    ‖(G * chtC1 .separate b E b).trace - (meqS W b .separate G * G).trace / 2 -
        (W : ℂ) * matchedA E ^ 2‖ ≤ W * chtErr .separate E G := by
  have hC := cht_trace_C1 hW b E b G
  have hS := cht_trace_S hW G (b := b)
  rw [meq_coefA hW hb1, meq_coefB hW hb0] at hS
  simp only [Fin.sum_univ_two, meqInc, LayerShape.incident, Fin.val_zero, Fin.val_one,
    Fin.isValue, decide_true, ite_true, one_mul, zero_ne_one, one_ne_zero, decide_false,
    Bool.false_eq_true, ite_false, zero_mul, add_zero, zero_add] at hC hS
  unfold chtErr
  simp only [Fin.sum_univ_two]
  set a := matchedA E
  set g0 := physBlockTrace G 0
  set g1 := physBlockTrace G 1
  set u0 := portBlockTrace G 0
  set u1 := portBlockTrace G 1
  have key : (G * chtC1 .separate b E b).trace - (meqS W b .separate G * G).trace / 2 -
      (W : ℂ) * a ^ 2 =
      (W : ℂ) * (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)) -
        (b : ℂ) * ((g0 - a) * (u0 - a) + (g1 - a) * (u1 - a))) := by
    rw [hC, hS]; push_cast; ring
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (1 - 2 * b) / 2 := by linarith
  rw [key]
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ hW0
  have h1 : ‖(((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)‖ ≤
      (1 - 2 * b) / 2 * (‖g0 - a‖ ^ 2 + ‖g1 - a‖ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hc
    rw [norm_pow, norm_pow]
  have h2 : ‖(b : ℂ) * ((g0 - a) * (u0 - a) + (g1 - a) * (u1 - a))‖ ≤
      b * ((‖g0 - a‖ ^ 2 + ‖u0 - a‖ ^ 2) / 2 + (‖g1 - a‖ ^ 2 + ‖u1 - a‖ ^ 2) / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (cht_norm_mul_le_sq _ _) (cht_norm_mul_le_sq _ _))) hb0
  have h3 := norm_sub_le (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)))
    ((b : ℂ) * ((g0 - a) * (u0 - a) + (g1 - a) * (u1 - a)))
  rw [norm_neg] at h3
  have hA := sq_nonneg ‖g0 - a‖
  have hB := sq_nonneg ‖g1 - a‖
  have hC' := sq_nonneg ‖u0 - a‖
  have hD := sq_nonneg ‖u1 - a‖
  nlinarith [mul_nonneg hb0 hA, mul_nonneg hb0 hB, mul_nonneg hb0 hC', mul_nonneg hb0 hD]

/-- **Common port**: the integrand is
`W [(1-b)a(g₁+g₂) + 2bau - (c/2)(g₁²+g₂²) - b(g₁+g₂)u]`, equal to
`W a² - W[(c/2) Σ(g_k-a)² + b (g₁+g₂-2a)(u-a)]`. -/
theorem cht_integrand_com_le (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (E : ℝ)
    (G : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) :
    ‖(G * chtC1 .common b E (2 * b)).trace - (meqS W b .common G * G).trace / 2 -
        (W : ℂ) * matchedA E ^ 2‖ ≤ W * chtErr .common E G := by
  have hC := cht_trace_C1 hW b E (2 * b) G
  have hS := cht_trace_S hW G (b := b)
  rw [meq_coefA hW hb1, meq_coefB hW hb0] at hS
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, meqInc, LayerShape.incident, ite_true,
    one_mul] at hC hS
  unfold chtErr
  simp only [Fin.sum_univ_two, Fin.sum_univ_one]
  set a := matchedA E
  set g0 := physBlockTrace G 0
  set g1 := physBlockTrace G 1
  set u := portBlockTrace G 0
  have key : (G * chtC1 .common b E (2 * b)).trace - (meqS W b .common G * G).trace / 2 -
      (W : ℂ) * a ^ 2 =
      (W : ℂ) * (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)) -
        (b : ℂ) * ((g0 - a) * (u - a) + (g1 - a) * (u - a))) := by
    rw [hC, hS]; push_cast; ring
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (1 - 2 * b) / 2 := by linarith
  rw [key]
  rw [norm_mul, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ hW0
  have h1 : ‖(((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)‖ ≤
      (1 - 2 * b) / 2 * (‖g0 - a‖ ^ 2 + ‖g1 - a‖ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) hc
    rw [norm_pow, norm_pow]
  have h2 : ‖(b : ℂ) * ((g0 - a) * (u - a) + (g1 - a) * (u - a))‖ ≤
      b * ((‖g0 - a‖ ^ 2 + ‖u - a‖ ^ 2) / 2 + (‖g1 - a‖ ^ 2 + ‖u - a‖ ^ 2) / 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
      (add_le_add (cht_norm_mul_le_sq _ _) (cht_norm_mul_le_sq _ _))) hb0
  have h3 := norm_sub_le (-((((1 - 2 * b) / 2 : ℝ) : ℂ) * ((g0 - a) ^ 2 + (g1 - a) ^ 2)))
    ((b : ℂ) * ((g0 - a) * (u - a) + (g1 - a) * (u - a)))
  rw [norm_neg] at h3
  have hA := sq_nonneg ‖g0 - a‖
  have hB := sq_nonneg ‖g1 - a‖
  have hC' := sq_nonneg ‖u - a‖
  nlinarith [mul_nonneg hb0 hA, mul_nonneg hb0 hB, mul_nonneg hb0 hC']

theorem cht_continuous_err (E : ℝ) :
    Continuous (fun G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ => chtErr σ E G) := by
  unfold chtErr
  refine (continuous_finsetSum _ fun k _ => ?_).add (continuous_finsetSum _ fun j _ => ?_)
  · exact (((meq_continuous_physBlockTrace k).sub continuous_const).norm).pow 2
  · exact (((meq_continuous_portBlockTrace j).sub continuous_const).norm).pow 2

theorem cht_err_nonneg (E : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    0 ≤ chtErr σ E G := by
  unfold chtErr; positivity

theorem cht_err_le (E : ℝ) {G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} {R : ℝ}
    (hG : ‖G‖ ≤ R) (hE : ‖matchedA E‖ ≤ 1) :
    chtErr σ E G ≤ (σ.blocks + σ.ports) * (R + 1) ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hG
  have h1 : ∀ k, ‖physBlockTrace G k - matchedA E‖ ^ 2 ≤ (R + 1) ^ 2 := fun k =>
    pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (add_le_add ((meq_norm_physBlockTrace_le G k).trans hG) hE)) 2
  have h2 : ∀ j, ‖portBlockTrace G j - matchedA E‖ ^ 2 ≤ (R + 1) ^ 2 := fun j =>
    pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
      (add_le_add ((meq_norm_portBlockTrace_le G j).trans hG) hE)) 2
  unfold chtErr
  calc _ ≤ ∑ _k : Fin σ.blocks, (R + 1) ^ 2 + ∑ _j : Fin σ.ports, (R + 1) ^ 2 :=
        add_le_add (Finset.sum_le_sum fun k _ => h1 k) (Finset.sum_le_sum fun j _ => h2 j)
    _ = _ := by simp; ring

end LayerDeriv

/-!
## 6. Integration of the heat derivative over `t ∈ [0, 1]`
-/

section LayerMain

variable {W : ℕ} {σ : LayerShape}

/-- **The heat step for one layer**: if the mean-square trace error along the interpolation is
at most `K` for all `t ∈ (0, 1)`, then `|φ(1) - φ(0) - W Im a²| ≤ W K`. -/
theorem cht_layer_main {b : ℝ} (hb1 : b < 1 / 2) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ 2 * b) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) {E : ℝ}
    (hE : |E| < 2)
    (hunit : ∀ᵐ ω ∂layerLaw W b σ,
      IsUnit (layerMatrix σ E ((matchedA E)⁻¹ + (β : ℂ) * matchedA E) X ω).det)
    (hint : ∀ G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ‖(G * chtC1 σ b E β).trace - (meqS W b σ G * G).trace / 2 - (W : ℂ) * matchedA E ^ 2‖ ≤
        W * chtErr σ E G)
    {K : ℝ} (hms : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, chtErr σ E (chtHeat σ b E X β t ω)⁻¹ ∂layerLaw W b σ ≤ K) :
    |chtPhi (tflVar W b σ) (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 1 -
        chtPhi (tflVar W b σ) (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 0 -
        W * (matchedA E ^ 2).im| ≤ W * K := by
  set v := tflVar W b σ
  set μ := gaussianProduct v
  set C₀ := chtC0 σ b E X
  set C₁ := chtC1 σ b E β
  set Lin := meqLc W b σ
  have hL : ∀ x, (Lin x).IsHermitian := cht_lin_isHermitian σ b
  have hcoer := cht_layer_coercive (σ := σ) hb1 hβ0 hβ hE hX
  have hlaw : layerLaw W b σ = μ.map (tflEmbed W b σ) := tfl_layerLaw_eq_map W b σ
  have hΦ := tfl_measurable_embed W b σ
  have hunitγ : ∀ᵐ x ∂μ, IsUnit (C₀ + C₁ + Lin x) := by
    rw [hlaw] at hunit
    filter_upwards [ae_of_ae_map hΦ.aemeasurable hunit] with x hx
    rw [← cht_path_one, cht_path_one_layer, Matrix.isUnit_iff_isUnit_det]
    exact hx
  have hcont := cht_phi_continuousOn v hL hcoer hunitγ
  have hder : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (chtPhi v C₀ C₁ Lin)
      (chtDeriv v C₀ C₁ Lin t).im t := fun t ht => cht_hasDerivAt_phi v hL hcoer ht
  have hEn : ‖matchedA E‖ ≤ 1 := (norm_matchedA hE.le).le
  refine cht_mvt hcont hder fun t ht => ?_
  obtain ⟨δ, hδ, hc⟩ := hcoer t ⟨ht.1.le, ht.2⟩
  have hcP : ∀ x, cplCoercive δ (chtPath C₀ C₁ Lin t x) := cht_path_coercive hL hc
  have hP : Continuous (fun x => chtPath C₀ C₁ Lin t x) := by unfold chtPath; fun_prop
  have hGc := cht_continuous_inv hδ hP hcP
  set G : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => Ring.inverse (chtPath C₀ C₁ Lin t x) with hG
  have hiC := cht_integrable_trace_mul_const v hδ hP hcP C₁
  have hiS := cht_integrable_trace_S v (Lin := Lin) hδ hP hcP
  have hErrI : Integrable (fun x => chtErr σ E (G x)) μ :=
    Integrable.of_bound ((cht_continuous_err E).comp hGc).aestronglyMeasurable
      ((σ.blocks + σ.ports) * (δ⁻¹ + 1) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (cht_err_nonneg E _)]
        exact cht_err_le E (cht_norm_inv_le hδ (hcP x)) hEn)
  have hS : ∀ x, coreS v Lin (G x) = meqS W b σ (G x) := fun x => rfl
  have hD : chtDeriv v C₀ C₁ Lin t - (W : ℂ) * matchedA E ^ 2 =
      ∫ x, ((G x * C₁).trace - (meqS W b σ (G x) * G x).trace / 2 -
        (W : ℂ) * matchedA E ^ 2) ∂μ := by
    have hi1 : Integrable (fun x => (G x * C₁).trace - (meqS W b σ (G x) * G x).trace / 2) μ :=
      hiC.sub (hiS.div_const 2)
    rw [integral_sub hi1 (integrable_const _), integral_const, probReal_univ, one_smul]
    rfl
  have hbd : ‖chtDeriv v C₀ C₁ Lin t - (W : ℂ) * matchedA E ^ 2‖ ≤ W * K := by
    rw [hD]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h1 : ∫ x, ‖(G x * C₁).trace - (meqS W b σ (G x) * G x).trace / 2 -
        (W : ℂ) * matchedA E ^ 2‖ ∂μ ≤ ∫ x, (W : ℝ) * chtErr σ E (G x) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hErrI.const_mul _)
        (ae_of_all _ fun x => hint (G x))
    refine h1.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have htr : ∫ x, chtErr σ E (G x) ∂μ =
        ∫ ω, chtErr σ E (chtHeat σ b E X β t ω)⁻¹ ∂layerLaw W b σ := by
      have hm : Measurable (fun ω => chtErr σ E (chtHeat σ b E X β t ω)⁻¹) :=
        (cht_continuous_err E).measurable.comp
          (measurable_matrix_inv.comp (cht_measurable_heat σ b E X β t))
      rw [hlaw, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hG]
      rw [cht_heat_embed, Matrix.nonsing_inv_eq_ringInverse]
    rw [htr]
    exact hms t ht
  have him : (chtDeriv v C₀ C₁ Lin t).im - W * (matchedA E ^ 2).im =
      (chtDeriv v C₀ C₁ Lin t - (W : ℂ) * matchedA E ^ 2).im := by
    simp [Complex.sub_im, Complex.mul_im]
  rw [him]
  exact (Complex.abs_im_le_norm _).trans hbd

/-!
### The endpoints
-/

theorem cht_logDet_sub_herm {m : Type} [Fintype m] [DecidableEq m] {X : Matrix m m ℂ}
    (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    (cplLogDet (z • (1 : Matrix m m ℂ) - X)).im = Real.pi * phaseCount z X := by
  have e : z • (1 : Matrix m m ℂ) - X = (-1 : ℝ) • X + z • 1 := by
    rw [neg_one_smul, neg_add_eq_sub]
  rw [e, cpl_logDet_herm hX (-1) hz, Complex.im_sum]
  unfold phaseCount
  rw [cph_spectralSum_eq_eigenvalues hX, mul_div_cancel₀ _ Real.pi_ne_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.log_im]
  congr 1
  push_cast
  ring

theorem cht_logDet_scalar {m : Type} [Fintype m] [DecidableEq m] {w : ℂ} (hw : 0 < w.im) :
    (cplLogDet (w • (1 : Matrix m m ℂ))).im = Fintype.card m * (Complex.log w).im := by
  rw [smul_one_eq_diagonal, cpl_logDet_diagonal fun _ => hw, Complex.im_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- **The initial phase**: `φ(0) = π Θ_{z_∂}(X) + π (#ports · W) ℓ`. -/
theorem cht_phi_zero {b β : ℝ} (hb1 : b < 1 / 2) {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ}
    (hX : X.IsHermitian) {E : ℝ} (hE : |E| < 2) :
    chtPhi (tflVar W b σ) (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 0 =
      Real.pi * phaseCount (boundaryZ b E) X + Real.pi * ((σ.ports * W : ℕ) * phaseEll E) := by
  have hc : ∀ x, chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 0 x = chtC0 σ b E X := by
    intro x; simp [chtPath]
  unfold chtPhi
  simp only [hc, integral_const, probReal_univ, one_smul]
  have ha := matchedA_im_neg hE
  have hinv : 0 < ((matchedA E)⁻¹).im := by
    rw [inv_matchedA hE.le, Complex.conj_im]; linarith
  have hz : 0 < (boundaryZ b E).im :=
    lt_of_lt_of_le (boundaryZ_im_pos_of_mem_bulkInterval (κ := 2 - |E|) (b := b) (by linarith)
      (by linarith) ⟨by linarith [neg_abs_le E], le_abs_self E |>.trans (by linarith)⟩).1
      (boundaryZ_im_pos_of_mem_bulkInterval (κ := 2 - |E|) (b := b) (by linarith)
      (by linarith) ⟨by linarith [neg_abs_le E], le_abs_self E |>.trans (by linarith)⟩).2
  have hH : (-X).IsHermitian := hX.neg
  have hA : boundaryZ b E • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) - X ∈
      cplDom (PhysSite W σ) := by
    refine ⟨(boundaryZ b E).im, hz, ?_⟩
    have := cht_coercive_herm_scalar hH (boundaryZ b E)
    rwa [neg_add_eq_sub] at this
  have hD : (matchedA E)⁻¹ • (1 : Matrix (PortSite W σ) (PortSite W σ) ℂ) ∈
      cplDom (PortSite W σ) := ⟨_, hinv, cpl_coercive_scalar⟩
  rw [cht_C0_eq hE.le, cpl_logDet_fromBlocks_zero hA hD, Complex.add_im,
    cht_logDet_sub_herm hX hz, cht_logDet_scalar hinv]
  unfold phaseEll
  simp only [Fintype.card_prod, Fintype.card_fin]
  field_simp

theorem cht_tendsto_reg {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) :
    Tendsto (fun j => tflReg (cplKappa j) M) atTop (𝓝 M) := by
  have hc : Continuous (fun κ : ℝ => M + ((κ : ℂ) * Complex.I) • (1 : Matrix m m ℂ)) := by
    fun_prop
  have := (hc.tendsto 0).comp cpl_tendsto_kappa
  simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero] at this
  exact this

/-- **The final phase**: `φ(1) = π E[N_-(A - E - X) + Θ_z(X₊)]`, through the
continuity of `L` at the (a.s. invertible, dissipative) layer matrix and the phase identity
`cpl_tendsto_phase`. `Gb` is any Borel version of the increment. -/
theorem cht_phi_one {b β : ℝ} (hb1 : b < 1 / 2) (hβ0 : 0 ≤ β) (hβ : β ≤ 2 * b)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) {E : ℝ} (hE : |E| < 2)
    (hz : 0 < ((matchedA E)⁻¹ + (β : ℂ) * matchedA E).im)
    (hunit : ∀ᵐ ω ∂layerLaw W b σ,
      IsUnit (layerMatrix σ E ((matchedA E)⁻¹ + (β : ℂ) * matchedA E) X ω).det)
    {Gb : LayerSample W σ → ℝ} (hGb : Measurable Gb)
    (hGeq : ∀ ω : LayerSample W σ, (∀ j, (ω.1 j).IsHermitian) →
      Gb ω = (negativeCount (cplTop E X ω) : ℝ) +
        phaseCount ((matchedA E)⁻¹ + (β : ℂ) * matchedA E) (layerSchur σ E X ω)) :
    chtPhi (tflVar W b σ) (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 1 =
      Real.pi * ∫ ω, Gb ω ∂layerLaw W b σ := by
  set z := (matchedA E)⁻¹ + (β : ℂ) * matchedA E
  set μ := gaussianProduct (tflVar W b σ)
  have hlaw : layerLaw W b σ = μ.map (tflEmbed W b σ) := tfl_layerLaw_eq_map W b σ
  have hΦ := tfl_measurable_embed W b σ
  have hcoer := cht_layer_coercive (σ := σ) hb1 hβ0 hβ hE hX
  have hL := cht_lin_isHermitian (W := W) σ b
  have hunitγ : ∀ᵐ x ∂μ, IsUnit (layerMatrix σ E z X (tflEmbed W b σ x)).det := by
    rw [hlaw] at hunit
    exact ae_of_ae_map hΦ.aemeasurable hunit
  have hDγ : ∀ᵐ x ∂μ, IsUnit (cplTop E X (tflEmbed W b σ x)).det := by
    have h := srec_ae_isUnit_top hb1 σ E X
    rw [hlaw] at h
    exact ae_of_ae_map hΦ.aemeasurable h
  have hpt : ∀ᵐ x ∂μ, (cplLogDet (chtPath (chtC0 σ b E X) (chtC1 σ b E β) (meqLc W b σ) 1 x)).im =
      Real.pi * Gb (tflEmbed W b σ x) := by
    filter_upwards [hunitγ, hDγ] with x hx hDx
    rw [cht_path_one_layer]
    set M := layerMatrix σ E z X (tflEmbed W b σ x)
    have hM : M = chtC0 σ b E X + chtC1 σ b E β + meqLc W b σ x := by
      simp only [M, z]; rw [← cht_path_one_layer, cht_path_one]
    have hdis : ∀ w, 0 ≤ cplForm M w := by
      intro w
      rw [hM, cpl_form_add, cpl_form_herm (hL x), add_zero]
      exact cht_form_one_nonneg hcoer w
    have hMu : IsUnit M := (Matrix.isUnit_iff_isUnit_det _).mpr hx
    have hcontL := cht_continuousAt_logDet hdis hMu
    have h1 : Tendsto (fun j => cplF W b σ E z X (cplKappa j) x) atTop
        (𝓝 (cplOut (cplLogDet M))) := by
      have h2 := (cplOut.continuous.tendsto _).comp (hcontL.tendsto.comp (cht_tendsto_reg M))
      refine h2.congr fun j => ?_
      simp only [Function.comp_apply, cplF, tflPsi_eq]
      rfl
    have h3 := cplF_tendsto W b σ E z hX hz x hDx
    have h4 := tendsto_nhds_unique h1 h3
    rw [cplOut_apply, Complex.ofReal_inj] at h4
    rw [hGeq _ fun j => gueOfCoords_isHermitian _ _ _, ← h4]
    field_simp
  unfold chtPhi
  rw [integral_congr_ae hpt, integral_const_mul, hlaw, integral_map hΦ.aemeasurable
    hGb.aestronglyMeasurable]

end LayerMain

/-!
## 7. The mean-square trace input and `CphIncrementLocal`
-/

section Local

/-- **The trace errors along the interpolation** (proved as `chtMeanSquare_holds`; "The
mean equations along this interpolation have the constant comparison value `a` ... trace errors
`O_{L²}(d + W⁻¹)` uniformly in `t`"). For `b ∈ (0, 1/2)` and the bulk `I = bulkInterval κ` there
are `d_* > 0`, `C` and `W₀`; for `W ≥ W₀`, every Hermitian two-port `X` with `d(X) ≤ d_*`,
`E ∈ I` and every `t ∈ (0, 1)`, the normalized block traces `g_k`, `u_j` of `ℋ_t⁻¹`
(`chtHeat`, port coefficient `β = b` for separate ports, `β = 2b` for the common port) satisfy
`E[Σ_k |g_k - a|² + Σ_j |u_j - a|²] ≤ C (d(X)² + W⁻²)` under `layerLaw W b σ`. -/
structure ChtMeanSquare : Prop where
  separate : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, chtErr .separate E (chtHeat .separate b E X b t ω)⁻¹ ∂layerLaw W b .separate ≤
        C * (matchedDistance b E X ^ 2 + ((W : ℝ) ^ 2)⁻¹)
  common : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ∫ ω, chtErr .common E (chtHeat .common b E X (2 * b) t ω)⁻¹ ∂layerLaw W b .common ≤
        C * (matchedDistance b E X ^ 2 + ((W : ℝ) ^ 2)⁻¹)

theorem cht_small_W {W W₀ : ℕ} (hW : 0 < W) (hW₀ : W < W₀) {L d K : ℝ} (hK : 8 * (W₀ : ℝ) ^ 2 ≤ K)
    (hL : |L| ≤ 8 * W) : |L| ≤ K * (W * d ^ 2 + (W : ℝ)⁻¹) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hlt : (W : ℝ) < W₀ := by exact_mod_cast hW₀
  have h1 : 8 * (W : ℝ) ≤ 8 * (W₀ : ℝ) ^ 2 * (W : ℝ)⁻¹ := by
    rw [mul_assoc, ← div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [le_div_iff₀ hWr]; nlinarith
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  calc |L| ≤ 8 * (W₀ : ℝ) ^ 2 * (W : ℝ)⁻¹ := hL.trans h1
    _ ≤ K * (W : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hK (by positivity)
    _ ≤ K * (W * d ^ 2 + (W : ℝ)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        have : 0 ≤ (W : ℝ) * d ^ 2 := by positivity
        linarith

/-- The final rescaling: `|(φ₁ - φ₀ - W Im a²)/π| ≤ C (W d² + W⁻¹)/π`. -/
theorem cht_final_bound {W : ℕ} (hW : 0 < W) {φ₁ φ₀ s d C K : ℝ}
    (hK : max C 0 / Real.pi ≤ K)
    (h : |φ₁ - φ₀ - s| ≤ W * (C * (d ^ 2 + ((W : ℝ) ^ 2)⁻¹))) :
    |(φ₁ - φ₀ - s) / Real.pi| ≤ K * (W * d ^ 2 + (W : ℝ)⁻¹) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hpi := Real.pi_pos
  have hR : 0 ≤ (W : ℝ) * d ^ 2 + (W : ℝ)⁻¹ := by positivity
  have e : (W : ℝ) * (C * (d ^ 2 + ((W : ℝ) ^ 2)⁻¹)) = C * ((W : ℝ) * d ^ 2 + (W : ℝ)⁻¹) := by
    field_simp
  rw [e] at h
  rw [abs_div, abs_of_pos hpi, div_le_iff₀ hpi]
  calc |φ₁ - φ₀ - s| ≤ C * ((W : ℝ) * d ^ 2 + (W : ℝ)⁻¹) := h
    _ ≤ max C 0 * ((W : ℝ) * d ^ 2 + (W : ℝ)⁻¹) := mul_le_mul_of_nonneg_right (le_max_left _ _) hR
    _ = max C 0 / Real.pi * ((W : ℝ) * d ^ 2 + (W : ℝ)⁻¹) * Real.pi := by field_simp
    _ ≤ K * ((W : ℝ) * d ^ 2 + (W : ℝ)⁻¹) * Real.pi := by gcongr

theorem cht_bulk_facts {b κ E : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    |E| < 2 ∧ (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (boundaryZ b E).im ∧
      ‖boundaryZ b E‖ ≤ 3 ∧ (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 ≤ (commonZ b E).im ∧
      ‖commonZ b E‖ ≤ 3 := by
  have hE2 := abs_lt_two_of_mem_bulkInterval hκ hE
  refine ⟨hE2, ?_, norm_boundaryZ_le hb0.le (by linarith) hE2.le,
    (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE).2, norm_commonZ_le hb0.le (by linarith) hE2.le⟩
  refine le_trans ?_ (boundaryZ_im_ge_of_mem_bulkInterval (by linarith) hκ hE)
  have hs := Real.sqrt_nonneg (4 - (2 - κ) ^ 2)
  nlinarith

/-- **`CphIncrementLocal`** from `ConditionalBlockGUECount` (through `gaussianAbsorption_holds`:
a.s. invertibility of the layer matrix) and the isolated mean-square input `ChtMeanSquare`. Heat
interpolation `ℋ_t` (`chtHeat`), heat derivative `cht_hasDerivAt_phi`, constant term `W a²` and
quadratic remainder (`cht_integrand_sep_le`, `cht_integrand_com_le`), endpoints `cht_phi_zero`,
`cht_phi_one`, mean value step `cht_mvt`; `F_sc = ℓ + h/2`. Small `W < W₀` by the trivial bound
`|Δ| ≤ 8W`. -/
theorem cphIncrementLocal_of_meanSquare (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hms : ChtMeanSquare) : CphIncrementLocal := by
  have habs := gaussianAbsorption_holds hcount
  refine ⟨fun b hb0 hb1 κ hκ => ?_, fun b hb0 hb1 κ hκ => ?_⟩
  · obtain ⟨dstar, C, W₀, hds, hC⟩ := hms.separate b hb0 hb1 κ hκ
    rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
    · exact ⟨1, 0, one_pos, fun W _ X _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
    set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
    have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
    obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
    refine ⟨dstar, max (max C 0 / Real.pi) (8 * (W₀ : ℝ) ^ 2), hds,
      fun W hW X hX E hE hd => ?_⟩
    obtain ⟨hE2, hzη, hz3, -, -⟩ := cht_bulk_facts hb0 hb1 hκ hE
    by_cases hW₀ : W₀ ≤ W
    · have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη hzη
      have hunit := (habs' W hW .separate X hX E (boundaryZ b E) hzη hz3).1
      have hmain := cht_layer_main (σ := .separate) hb1 (β := b) hb0.le (by linarith) hX hE2
        hunit (cht_integrand_sep_le hW hb0.le hb1.le E) (fun t ht => hC W hW hW₀ X hX E hE hd t ht)
      have hGeq : ∀ ω : LayerSample W .separate, (∀ j, (ω.1 j).IsHermitian) →
          cplSepG b E X ω = (negativeCount (cplTop E X ω) : ℝ) +
            phaseCount (boundaryZ b E) (layerSchur .separate E X ω) := by
        intro ω hA
        unfold cplSepG
        rw [cph_negativeCount_eq_rawSum, cph_phaseCount_eq (srec_layerSchur_isHermitian E hX ω hA)]
      rw [cht_phi_one hb1 hb0.le (by linarith) hX hE2 hz hunit (cpl_measurable_sepG b E X) hGeq,
        cht_phi_zero hb1 hX hE2] at hmain
      have hint : ∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
          phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) ∂layerLaw W b .separate =
          ∫ ω, cplSepG b E X ω ∂layerLaw W b .separate := by
        refine integral_congr_ae ?_
        filter_upwards [lct_ae_blocks_isHermitian W b .separate] with ω hω
        exact (hGeq ω hω).symm
      rw [hint, BlockBand.RankLocation.semicircleCDF_eq_phase_of_real E]
      have hfin := cht_final_bound hW (le_max_left _ (8 * (W₀ : ℝ) ^ 2)) hmain
      convert hfin using 2
      unfold phaseH
      push_cast
      field_simp
      ring
    · exact cht_small_W hW (lt_of_not_ge hW₀) (le_max_right _ _) (cph_sep_lhs_le hb1 hκ hE X)
  · obtain ⟨dstar, C, W₀, hds, hC⟩ := hms.common b hb0 hb1 κ hκ
    rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
    · exact ⟨1, 0, one_pos, fun W _ X _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
    set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
    have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
    obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
    refine ⟨dstar, max (max C 0 / Real.pi) (8 * (W₀ : ℝ) ^ 2), hds,
      fun W hW X hX E hE hd => ?_⟩
    obtain ⟨hE2, -, -, hzη, hz3⟩ := cht_bulk_facts hb0 hb1 hκ hE
    by_cases hW₀ : W₀ ≤ W
    · have hzc : (matchedA E)⁻¹ + ((2 * b : ℝ) : ℂ) * matchedA E = commonZ b E := by
        rw [commonZ]; push_cast; ring
      have hz : 0 < ((matchedA E)⁻¹ + ((2 * b : ℝ) : ℂ) * matchedA E).im := by
        rw [hzc]; exact lt_of_lt_of_le hη hzη
      have hunit := (habs' W hW .common X hX E (commonZ b E) hzη hz3).1
      rw [← hzc] at hunit
      have hmain := cht_layer_main (σ := .common) hb1 (β := 2 * b) (by linarith) le_rfl hX hE2
        hunit (cht_integrand_com_le hW hb0.le hb1.le E) (fun t ht => hC W hW hW₀ X hX E hE hd t ht)
      have hGeq : ∀ ω : LayerSample W .common, (∀ j, (ω.1 j).IsHermitian) →
          cplComG b E X ω = (negativeCount (cplTop E X ω) : ℝ) +
            phaseCount ((matchedA E)⁻¹ + ((2 * b : ℝ) : ℂ) * matchedA E)
              (layerSchur .common E X ω) := by
        intro ω hA
        unfold cplComG
        rw [hzc, cph_negativeCount_eq_rawSum,
          cph_phaseCount_eq (rng_layerSchur_common_isHermitian E hX ω hA)]
      rw [cht_phi_one hb1 (by linarith) le_rfl hX hE2 hz hunit (cpl_measurable_comG b E X) hGeq,
        cht_phi_zero hb1 hX hE2] at hmain
      have hint : ∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
          phaseCount (commonZ b E) (layerSchur .common E X ω)) ∂layerLaw W b .common =
          ∫ ω, cplComG b E X ω ∂layerLaw W b .common := by
        refine integral_congr_ae ?_
        filter_upwards [lct_ae_blocks_isHermitian W b .common] with ω hω
        rw [hGeq ω hω, hzc]
      rw [hint]
      have hfin := cht_final_bound hW (le_max_left _ (8 * (W₀ : ℝ) ^ 2)) hmain
      convert hfin using 2
      unfold phaseH
      push_cast
      field_simp
      ring
    · exact cht_small_W hW (lt_of_not_ge hW₀) (le_max_right _ _) (cph_com_lhs_le hb1 hκ hE X)

end Local

end BlockBand.Layers
