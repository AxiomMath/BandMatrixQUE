module

public import BlockBand.Prelude

/-!
# Gaussian integration by parts (Stein's identity), proved from `gaussianReal`

The fresh layer laws `ginibreMeasure`/`gueMeasure` are maps of `Measure.pi` of `gaussianReal`
(`Bridge.gueMeasure_eq_map`). No external hypothesis is used: this is proved from Mathlib's
`gaussianReal` density and integration by parts on `ℝ`
(`integral_mul_deriv_eq_deriv_mul_of_integrable`).

* `stein_gaussianReal`: `E[X f(X)] = v E[f'(X)]` for `X ~ N(0,v)`, `f : ℝ → ℂ` differentiable
  everywhere, with `f`, `f'` and `X f` integrable.
* `pi_map_update_pi`: resampling one coordinate of an independent product keeps the law.
* `stein_pi`: coordinate `i` of `Measure.pi (gaussianReal 0 ∘ v)`:
  `E[x_i f(x)] = v_i E[∂_i f(x)]` (Fubini plus `stein_gaussianReal`).
* `stein_pi_fderiv`: Cameron–Martin form for Fréchet-differentiable `G`:
  `E[(Σ_j h_j x_j) G(x)] = E[G'(x)(v·h)]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

theorem integrable_gaussianReal_iff {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℂ} :
    Integrable g (gaussianReal 0 v) ↔ Integrable (fun x => gaussianPDFReal 0 v x • g x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]

theorem hasDerivAt_gaussianPDFReal {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / v) * gaussianPDFReal 0 v x) x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have h : HasDerivAt (fun y : ℝ => -(y - 0) ^ 2 / (2 * v)) (-(2 * (x - 0)) / (2 * v)) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    simpa using (this.neg).div_const (2 * (v : ℝ))
  have h2 := (h.exp).const_mul (√(2 * π * v))⁻¹
  rw [gaussianPDFReal_def]
  convert h2 using 1
  field_simp
  ring

/-- **Gaussian integration by parts** (Stein): `E[X f(X)] = v E[f'(X)]`, `X ~ N(0,v)`. -/
theorem stein_gaussianReal {v : ℝ≥0} (f f' : ℝ → ℂ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi1 : Integrable f (gaussianReal 0 v)) (hi2 : Integrable f' (gaussianReal 0 v))
    (hi3 : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 v)) :
    ∫ x : ℝ, (x : ℂ) * f x ∂gaussianReal 0 v = (v : ℂ) * ∫ x, f' x ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · subst hv; simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  set φ : ℝ → ℂ := fun x => (gaussianPDFReal 0 v x : ℂ)
  set φ' : ℝ → ℂ := fun x => (-(x / v) * gaussianPDFReal 0 v x : ℝ)
  have hφ : ∀ x, HasDerivAt φ (φ' x) x := fun x =>
    (hasDerivAt_gaussianPDFReal hv x).ofReal_comp
  rw [integrable_gaussianReal_iff hv] at hi1 hi2 hi3
  have e1 : (f * φ') = fun x => -(v : ℂ)⁻¹ * (gaussianPDFReal 0 v x • ((x : ℂ) * f x)) := by
    funext x; simp only [Pi.mul_apply, φ', Complex.real_smul]; push_cast; ring
  have e2 : (f' * φ) = fun x => gaussianPDFReal 0 v x • f' x := by
    funext x; simp only [Pi.mul_apply, φ, Complex.real_smul]; ring
  have e3 : (f * φ) = fun x => gaussianPDFReal 0 v x • f x := by
    funext x; simp only [Pi.mul_apply, φ, Complex.real_smul]; ring
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (v := φ) (u' := f')
    (v' := φ') (fun x _ => hf x) (fun x _ => hφ x)
    (by rw [e1]; exact hi3.const_mul _) (by rw [e2]; exact hi2) (by rw [e3]; exact hi1)
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have l1 : ∫ x, f x * φ' x = -(v : ℂ)⁻¹ * ∫ x, gaussianPDFReal 0 v x • ((x : ℂ) * f x) := by
    rw [← integral_const_mul]; exact congrArg (fun g => ∫ x, g x) e1
  have l2 : ∫ x, f' x * φ x = ∫ x, gaussianPDFReal 0 v x • f' x :=
    congrArg (fun g => ∫ x, g x) e2
  rw [l1, l2] at ibp
  have hvc : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  field_simp at ibp
  linear_combination -ibp

theorem measurable_update_coord_pi {ι : Type*} [DecidableEq ι] (i0 : ι) :
    Measurable fun p : (ι → ℝ) × ℝ => Function.update p.1 i0 p.2 := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i = i0
  · subst h; simpa using measurable_snd
  · simp only [Function.update_of_ne h]; exact (measurable_pi_apply i).comp measurable_fst

theorem pi_map_update_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (i0 : ι) :
    ((Measure.pi μ).prod (μ i0)).map (fun p => Function.update p.1 i0 p.2) = Measure.pi μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_update_coord_pi i0) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i0 p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i0 Set.univ)) ×ˢ s i0 := by
    ext ⟨r, t⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h i0⟩
      by_cases hi : i = i0
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = i0
      · subst hi; simpa using h2
      · simpa [Function.update_of_ne hi] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl i0,
    Fintype.prod_eq_mul_prod_compl i0 (fun i => μ i (s i))]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by simpa using hi)]

/-- **Multivariate Gaussian integration by parts** in coordinate `i`. -/
theorem stein_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) (i : ι)
    (f g : (ι → ℝ) → ℂ)
    (hf : ∀ x, HasDerivAt (fun s => f (Function.update x i s)) (g x) (x i))
    (hi1 : Integrable f (Measure.pi fun j => gaussianReal 0 (v j)))
    (hi2 : Integrable g (Measure.pi fun j => gaussianReal 0 (v j)))
    (hi3 : Integrable (fun x => (x i : ℂ) * f x) (Measure.pi fun j => gaussianReal 0 (v j))) :
    ∫ x, (x i : ℂ) * f x ∂(Measure.pi fun j => gaussianReal 0 (v j)) =
      (v i : ℂ) * ∫ x, g x ∂(Measure.pi fun j => gaussianReal 0 (v j)) := by
  set μ := Measure.pi fun j => gaussianReal 0 (v j)
  set P := μ.prod (gaussianReal 0 (v i))
  set T : (ι → ℝ) × ℝ → (ι → ℝ) := fun p => Function.update p.1 i p.2
  have hT : Measurable T := measurable_update_coord_pi i
  have hmap : P.map T = μ := pi_map_update_pi (fun j => gaussianReal 0 (v j)) i
  have tr : ∀ F : (ι → ℝ) → ℂ, Integrable F μ →
      ∫ x, F x ∂μ = ∫ y, ∫ s, F (T (y, s)) ∂gaussianReal 0 (v i) ∂μ ∧
        Integrable (F ∘ T) P := by
    intro F hF
    rw [← hmap] at hF
    have hFT : Integrable (F ∘ T) P := hF.comp_measurable hT
    refine ⟨?_, hFT⟩
    have h := integral_map hT.aemeasurable hF.aestronglyMeasurable
    rw [hmap] at h
    rw [h]
    exact integral_prod _ hFT
  obtain ⟨e1, i1⟩ := tr _ hi3
  obtain ⟨e2, i2⟩ := tr _ hi2
  obtain ⟨-, i0⟩ := tr _ hi1
  rw [e1, e2, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [i0.prod_right_ae, i2.prod_right_ae, i1.prod_right_ae] with y h0 h2 h1
  have hT1 : ∀ s, T (y, s) i = s := fun s => by simp [T]
  simp only [Function.comp_apply, hT1] at h1 ⊢
  refine stein_gaussianReal (fun s => f (T (y, s))) (fun s => g (T (y, s))) (fun s => ?_) h0 h2 h1
  have := hf (T (y, s))
  simpa [T] using this

/-- **Cameron–Martin form**: for `G` Fréchet differentiable everywhere,
`E[(Σ_j h_j x_j) G(x)] = E[G'(x)(fun j => v_j h_j)]` under `Measure.pi (gaussianReal 0 ∘ v)`. -/
theorem stein_pi_fderiv {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) (h : ι → ℝ)
    (G : (ι → ℝ) → ℂ) (G' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℂ) (hG : ∀ x, HasFDerivAt G (G' x) x)
    (hi1 : Integrable G (Measure.pi fun j => gaussianReal 0 (v j)))
    (hi2 : ∀ j, Integrable (fun x => G' x (Pi.single j 1)) (Measure.pi fun j => gaussianReal 0 (v j)))
    (hi3 : ∀ j, Integrable (fun x => (x j : ℂ) * G x) (Measure.pi fun j => gaussianReal 0 (v j))) :
    ∫ x, ((∑ j, h j * x j : ℝ) : ℂ) * G x ∂(Measure.pi fun j => gaussianReal 0 (v j)) =
      ∫ x, G' x (fun j => (v j : ℝ) * h j) ∂(Measure.pi fun j => gaussianReal 0 (v j)) := by
  set μ := Measure.pi fun j => gaussianReal 0 (v j)
  have hcoord : ∀ j, ∫ x, (x j : ℂ) * G x ∂μ = (v j : ℂ) * ∫ x, G' x (Pi.single j 1) ∂μ := by
    intro j
    refine stein_pi v j G (fun x => G' x (Pi.single j 1)) (fun x => ?_) hi1 (hi2 j) (hi3 j)
    have := (hG (Function.update x j (x j))).comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
    rw [Function.update_eq_self] at this
    exact this
  have hsplit : (fun x => G' x (fun j => (v j : ℝ) * h j)) =
      fun x => ∑ j, ((v j : ℝ) * h j : ℝ) • G' x (Pi.single j 1) := by
    funext x
    conv_lhs => rw [show (fun j => (v j : ℝ) * h j) = ∑ j, ((v j : ℝ) * h j) • Pi.single j (1 : ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    simp only [map_smul]
  have hl : (fun x : ι → ℝ => ((∑ j, h j * x j : ℝ) : ℂ) * G x) =
      fun x => ∑ j, (h j : ℂ) * ((x j : ℂ) * G x) := by
    funext x; push_cast; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have hint2 : ∀ j ∈ Finset.univ, Integrable
      (fun x => ((v j : ℝ) * h j) • G' x (Pi.single j 1)) μ := fun j _ =>
    (hi2 j).smul ((v j : ℝ) * h j)
  have hint3 : ∀ j ∈ Finset.univ, Integrable
      (fun x : ι → ℝ => (h j : ℂ) * ((x j : ℂ) * G x)) μ := fun j _ => (hi3 j).const_mul _
  rw [hl, hsplit, integral_finsetSum _ hint3, integral_finsetSum _ hint2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hcoord, integral_smul, Complex.real_smul]
  push_cast; ring

end BlockBand.Transmission.PassiveCovariance
