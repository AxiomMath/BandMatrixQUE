module

public import BlockBand.Critical.Collar.Density.CondSchurCauchy
public import BlockBand.Critical.Collar.Density.CondSchurConvolution
public import BlockBand.Layers.LayerMeasurability

/-!
# Conditional Schur identity: Measurable

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

Cauchy law versus Lebesgue kernel, measurability in the energy of `S(x)`, `y(x)` and of the
functional calculus, spectral sums for the Schur complement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv cauchyKernel_nonneg
  continuous_cauchyKernel measurable_cauchyKernel)
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {D : Matrix m m ℂ} {B : Matrix m n ℂ} {G : Matrix n n ℂ}

/-!
## Cauchy law and Lebesgue kernel
-/

theorem lintegral_stdCauchy_eq {f : ℝ → ℝ≥0∞} (hf : Measurable f) (t : ℝ) {η : ℝ}
    (hη : 0 < η) :
    ∫⁻ s, f (t + η * s) ∂stdCauchy = ∫⁻ θ, ENNReal.ofReal (cauchyKernel η (θ - t)) * f θ := by
  have hfm : Measurable fun s : ℝ => f (t + η * s) :=
    hf.comp (measurable_const.add (measurable_const.mul measurable_id))
  rw [stdCauchy, cauchyMeasure_of_scale_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_cauchyPDF 0 1) hfm]
  set h : ℝ → ℝ≥0∞ := fun θ => cauchyPDF 0 1 ((θ - t) / η) * f θ
  have hh : Measurable h := ((measurable_cauchyPDF 0 1).comp
    ((measurable_id.sub measurable_const).div_const η)).mul hf
  have hmap := Real.map_volume_mul_left (a := η) hη.ne'
  have h1 : ∫⁻ s, h (t + η * s) = ENNReal.ofReal |η⁻¹| * ∫⁻ θ, h θ := by
    have := lintegral_map (μ := volume) (g := fun s : ℝ => η * s)
      (f := fun y => h (t + y)) (hh.comp (measurable_const.add measurable_id))
      (measurable_const.mul measurable_id)
    rw [hmap, lintegral_smul_measure] at this
    rw [← this, lintegral_add_left_eq_self h t]
    rfl
  have heq : (fun s => (cauchyPDF 0 1 * fun s => f (t + η * s)) s) = fun s => h (t + η * s) := by
    funext s
    simp only [Pi.mul_apply, h]
    congr 2
    field_simp
    ring
  rw [heq, h1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun θ => ?_
  simp only [h]
  rw [← mul_assoc]
  congr 1
  rw [cauchyPDF, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.2 hη)]
  congr 1
  rw [cauchyPDFReal_def]
  unfold cauchyKernel
  have hp := Real.pi_pos
  have : 0 < (θ - t) ^ 2 + η ^ 2 := by positivity
  push_cast
  field_simp
  ring

/-!
## Measurability in the energy
-/

theorem measurable_matrix_inv_cs {ι : Type} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℂ => A⁻¹) :=
  BlockBand.Layers.measurable_matrix_inv

theorem measurable_shift_inv (D : Matrix m m ℂ) :
    Measurable fun x : ℝ => (D - (x : ℂ) • (1 : Matrix m m ℂ))⁻¹ := by
  have hc : Continuous fun x : ℝ => D - (x : ℂ) • (1 : Matrix m m ℂ) :=
    continuous_const.sub (Complex.continuous_ofReal.smul continuous_const)
  exact measurable_matrix_inv_cs.comp hc.measurable

theorem measurable_csS (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) :
    Measurable (csS D B G) := by
  have hc : Continuous fun p : Matrix m m ℂ × ℝ =>
      G - (p.2 : ℂ) • (1 : Matrix n n ℂ) - Bᴴ * p.1 * B :=
    (continuous_const.sub ((Complex.continuous_ofReal.comp continuous_snd).smul
      continuous_const)).sub ((continuous_const.matrix_mul continuous_fst).matrix_mul
        continuous_const)
  have h2 := hc.measurable.comp ((measurable_shift_inv D).prodMk measurable_id)
  exact h2

theorem measurable_csY (D : Matrix m m ℂ) (B : Matrix m n ℂ) (u : m → ℂ) :
    Measurable (csY D B u) := by
  have hc : Continuous fun M : Matrix m m ℂ => (Bᴴ * M) *ᵥ u :=
    (continuous_const.matrix_mul continuous_id).matrix_mulVec continuous_const
  have h2 := hc.measurable.comp (measurable_shift_inv D)
  exact h2

theorem continuous_quadForm_pair {ι : Type} [Fintype ι] :
    Continuous fun p : Matrix ι ι ℂ × (ι → ℂ) => quadForm p.1 p.2 := by
  unfold quadForm
  refine Complex.continuous_re.comp ?_
  refine Continuous.dotProduct ?_ ?_
  · exact continuous_star.comp continuous_snd
  · exact continuous_fst.matrix_mulVec continuous_snd

/-- Joint measurability of `(t, x) ↦ y_x* f_t(S(x)) y_x`. -/
theorem measurable_quadForm_cfc_csS (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ)
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) :
    Measurable fun p : ℝ × ℝ => quadForm (cfc (g p.1) (csS D B G p.2)) (csY D B u p.2) := by
  have heq : (fun p : ℝ × ℝ => quadForm (cfc (g p.1) (csS D B G p.2)) (csY D B u p.2)) =
      fun p => quadForm (rawCfc (g p.1) (csS D B G p.2)) (csY D B u p.2) := by
    funext p
    rw [rawCfc_eq_cfc (csS_isHermitian hD hG p.2)]
  rw [heq]
  have hR : Measurable fun p : ℝ × ℝ => rawCfc (g p.1) (csS D B G p.2) :=
    measurable_matrix_of_entries fun i j => measurable_rawCfc (measurable_csS D B G) hg i j
  have hY : Measurable fun p : ℝ × ℝ => csY D B u p.2 := (measurable_csY D B u).comp measurable_snd
  have h2 := (continuous_quadForm_pair (ι := n)).measurable.comp (hR.prodMk hY)
  exact h2

theorem measurable_quadForm_cfc_csS' (hD : D.IsHermitian) (hG : G.IsHermitian) (u : m → ℂ)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun x : ℝ => quadForm (cfc f (csS D B G x)) (csY D B u x) := by
  have h := measurable_quadForm_cfc_csS (B := B) hD hG u (g := fun _ => f)
    (hf.comp measurable_snd)
  have hp : Measurable fun x : ℝ => ((0 : ℝ), x) := measurable_const.prodMk measurable_id
  have h2 := h.comp hp
  exact h2

/-!
## Spectral sums for the Schur complement
-/

theorem quadForm_cfc_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) (f : ℝ → ℝ) (y : ι → ℂ) :
    quadForm (cfc f K) y = ∑ r, f (increasingEigenvalue hK r) *
      ‖star (increasingEigenvector hK r) ⬝ᵥ y‖ ^ 2 := by
  unfold quadForm
  rw [cfc_eq_specSum hK, dotProduct_specSum_mulVec, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.re_ofReal_mul]
  norm_cast

theorem quadForm_cfc_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (y : ι → ℂ) :
    0 ≤ quadForm (cfc f K) y := by
  rw [quadForm_cfc_eq_sum hK]
  exact Finset.sum_nonneg fun r _ => mul_nonneg (hf _) (sq_nonneg _)

theorem ofReal_quadForm_cfc_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ}
    (hK : K.IsHermitian) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (y : ι → ℂ) :
    ENNReal.ofReal (quadForm (cfc f K) y) = ∑ r, ENNReal.ofReal
      (‖star (increasingEigenvector hK r) ⬝ᵥ y‖ ^ 2) * ENNReal.ofReal (f (increasingEigenvalue hK r)) := by
  rw [quadForm_cfc_eq_sum hK, ENNReal.ofReal_sum_of_nonneg fun r _ =>
    mul_nonneg (hf _) (sq_nonneg _)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ENNReal.ofReal_mul (hf _), mul_comm]

end BlockBand.Critical.Collar.Density
