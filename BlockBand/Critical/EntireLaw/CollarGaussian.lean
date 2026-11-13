module

public import BlockBand.Critical.EntireLaw.CollarCount
public import BlockBand.Critical.EntireLaw.PhasePassage
public import BlockBand.Critical.GlobalSource.ReplacementGaussian

/-!
# The entire law: splitting `ζ = ζ_o + ζ_c` and conditional Gaussian integration

* `ringSource_sub_omitted_eq`: `(ζ^*Rζ - ζ_o^*Rζ_o)_{ac} = ζ_{c,a}^*Rζ_c + ζ_{o,a}^*Rζ_{c,c}`.
* `integral_scaled_quadratic`: `E_h (Dh)^*A(Dh) = Σ_x |d_x|² A_xx` (circular Gaussian law,
  `GlobalSource.integral_quadratic`).
* `lintegral_probeForm_le`: under `fullRingProbeLaw`, if `|d_x|² ≤ κ 1_S(x)` then
  `E[(D g_a)^*|R|(D g_a)] ≤ κ E[Σ_{x ∈ S} Re|R|_xx]` (Tonelli, conditional Gaussian integration).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal ComplexConjugate

/-!
## 1. Deterministic splitting `ζ = ζ_o + ζ_c`
-/

section Split

variable {p : Parameters}

/-- The collar part `ζ_c` of a vector on the ring sites. -/
def collarPart (p : Parameters) (v : p.Site → ℂ) : p.Site → ℂ :=
  fun x => if IsCollarBlock p x.1 then v x else 0

theorem omitCollar_add_collarPart (v : p.Site → ℂ) : omitCollar p v + collarPart p v = v := by
  funext x
  simp only [Pi.add_apply, omitCollar, collarPart]
  split_ifs <;> simp

/-- **The collar contribution**: with `ζ = ζ_o + ζ_c`,
`ζ_a^* R ζ_c - ζ_{o,a}^* R ζ_{o,c} = ζ_{c,a}^* R ζ_c + ζ_{o,a}^* R ζ_{c,c}`. -/
theorem ringSource_sub_omitted_eq (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (H : p.SiteMatrix)
    (g : Fin J → p.Site → ℂ) (a c : Fin J) :
    ringSourceMatrix p E Q H g a c - omittedRingSourceMatrix p E Q H g a c =
      star (collarPart p (ringProbeVector p (Q a) (g a))) ⬝ᵥ
          ((H - (E : ℂ) • 1)⁻¹ *ᵥ ringProbeVector p (Q c) (g c)) +
        star (omitCollar p (ringProbeVector p (Q a) (g a))) ⬝ᵥ
          ((H - (E : ℂ) • 1)⁻¹ *ᵥ collarPart p (ringProbeVector p (Q c) (g c))) := by
  set R := (H - (E : ℂ) • (1 : p.SiteMatrix))⁻¹
  set u := ringProbeVector p (Q a) (g a)
  set v := ringProbeVector p (Q c) (g c)
  have hu := omitCollar_add_collarPart (p := p) u
  have hv := omitCollar_add_collarPart (p := p) v
  change star u ⬝ᵥ (R *ᵥ v) - star (omitCollar p u) ⬝ᵥ (R *ᵥ omitCollar p v) = _
  have e1 : star u ⬝ᵥ (R *ᵥ v) = star (omitCollar p u) ⬝ᵥ (R *ᵥ v) +
      star (collarPart p u) ⬝ᵥ (R *ᵥ v) := by
    rw [← add_dotProduct, ← star_add, hu]
  have e2 : star (omitCollar p u) ⬝ᵥ (R *ᵥ omitCollar p v) +
      star (omitCollar p u) ⬝ᵥ (R *ᵥ collarPart p v) = star (omitCollar p u) ⬝ᵥ (R *ᵥ v) := by
    rw [← dotProduct_add, ← mulVec_add, hv]
  rw [e1, ← e2]
  ring

end Split

/-!
## 2. Gaussian integration of `|R|`-quadratic forms
-/

section Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `E (Dh)^* A (Dh) = Σ_x |d_x|² A_xx` for one standard circular vector `h`. -/
theorem integral_scaled_quadratic (A : Matrix ι ι ℂ) (d : ι → ℂ) :
    ∫ h, star (fun x => d x * h x) ⬝ᵥ (A *ᵥ fun x => d x * h x) ∂circularVectorLaw ι =
      ∑ x, ((‖d x‖ ^ 2 : ℝ) : ℂ) * A x x := by
  have hD : ∀ h : ι → ℂ, (fun x => d x * h x) = diagonal d *ᵥ h := fun h => by
    funext x; rw [mulVec_diagonal]
  have heq : ∀ h : ι → ℂ, star (fun x => d x * h x) ⬝ᵥ (A *ᵥ fun x => d x * h x) =
      star h ⬝ᵥ ((diagonal (star d) * A * diagonal d) *ᵥ h) := fun h => by
    rw [hD, star_mulVec, ← dotProduct_mulVec, diagonal_conjTranspose, ← mulVec_mulVec,
      ← mulVec_mulVec]
  simp_rw [heq]
  rw [BlockBand.Critical.GlobalSource.integral_quadratic, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [diag_apply, mul_diagonal, diagonal_mul]
  push_cast
  rw [← Complex.mul_conj']
  simp only [Pi.star_apply, Complex.star_def]
  ring

theorem integrable_scaled_quadratic (A : Matrix ι ι ℂ) (d : ι → ℂ) :
    Integrable (fun h => star (fun x => d x * h x) ⬝ᵥ (A *ᵥ fun x => d x * h x))
      (circularVectorLaw ι) := by
  have hD : ∀ h : ι → ℂ, (fun x => d x * h x) = diagonal d *ᵥ h := fun h => by
    funext x; rw [mulVec_diagonal]
  have heq : (fun h : ι → ℂ => star (fun x => d x * h x) ⬝ᵥ (A *ᵥ fun x => d x * h x)) =
      fun h => star h ⬝ᵥ ((diagonal (star d) * A * diagonal d) *ᵥ h) := by
    funext h
    rw [hD, star_mulVec, ← dotProduct_mulVec, diagonal_conjTranspose, ← mulVec_mulVec,
      ← mulVec_mulVec]
  rw [heq]
  exact BlockBand.Critical.GlobalSource.integrable_quadratic _

end Gaussian

/-!
## 3. Expected `|R|`-forms of the probes
-/

section Forms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `v^* |R| v` (real part). -/
def absForm (E δ : ℝ) (H : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ (absResolvent E δ H *ᵥ v)).re

theorem absForm_nonneg (E δ : ℝ) (H : Matrix ι ι ℂ) (v : ι → ℂ) : 0 ≤ absForm E δ H v :=
  re_dotProduct_cfc_mulVec_self_nonneg (collarWeight_nonneg E δ) H v

theorem measurable_absForm_scaled (E δ : ℝ) {α : Type*} [MeasurableSpace α]
    {M : α → Matrix ι ι ℂ} (hM : Measurable M) {h : α → ι → ℂ} (hh : Measurable h)
    (d : ι → ℂ) :
    Measurable fun a => absForm E δ (M a) (fun y => d y * h a y) := by
  have hc : Continuous fun q : Matrix ι ι ℂ × (ι → ℂ) => (star q.2 ⬝ᵥ (q.1 *ᵥ q.2)).re := by
    unfold dotProduct mulVec dotProduct
    fun_prop
  have hv : Measurable fun a => (fun y => d y * h a y) :=
    Measurable.of_eval fun y => measurable_const.mul ((measurable_pi_apply y).comp hh)
  exact hc.measurable.comp (((measurable_absResolvent E δ).comp hM).prodMk hv)

/-- **Conditional Gaussian integration**: for fixed `H`,
`E_h (Dh)^* |R| (Dh) = Σ_x |d_x|² |R|_xx`. -/
theorem lintegral_absForm_scaled (E δ : ℝ) (H : Matrix ι ι ℂ) (d : ι → ℂ) :
    ∫⁻ h, ENNReal.ofReal (absForm E δ H (fun y => d y * h y)) ∂circularVectorLaw ι =
      ENNReal.ofReal (∑ x, ‖d x‖ ^ 2 * (absResolvent E δ H x x).re) := by
  have hint := integrable_scaled_quadratic (absResolvent E δ H) d
  have hre : Integrable (fun h : ι → ℂ => absForm E δ H (fun y => d y * h y))
      (circularVectorLaw ι) := hint.re
  have e : ∫ h, absForm E δ H (fun y => d y * h y) ∂circularVectorLaw ι =
      ∑ x, ‖d x‖ ^ 2 * (absResolvent E δ H x x).re := by
    change ∫ h, RCLike.re (star (fun x => d x * h x) ⬝ᵥ
      (absResolvent E δ H *ᵥ fun x => d x * h x)) ∂circularVectorLaw ι = _
    rw [integral_re hint, integral_scaled_quadratic]
    simp only [RCLike.re_to_complex, Complex.re_sum, Complex.re_ofReal_mul]
  rw [← e]
  exact (ofReal_integral_eq_lintegral_ofReal hre
    (Filter.Eventually.of_forall fun h => absForm_nonneg E δ H _)).symm

end Forms

section Probe

variable {p : Parameters}

/-- **Expected `|R|`-form of one masked probe**: if `|d_x|² ≤ κ 1_S(x)`, then
`E[(D g_a)^* |R| (D g_a)] ≤ κ E[Σ_{x ∈ S} |R|_xx]` under the physical law and `J` independent
circular Gaussian vectors. -/
theorem lintegral_probeForm_le (model : p.GaussianRingModel) (E δ : ℝ) {J : ℕ} (a : Fin J)
    (d : p.Site → ℂ) (S : p.Site → Prop) [DecidablePred S] {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ x, ‖d x‖ ^ 2 ≤ if S x then κ else 0) :
    ∫⁻ x, ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 a y)) ∂fullRingProbeLaw model J ≤
      ENNReal.ofReal κ * ∫⁻ H, ENNReal.ofReal
        (∑ y, if S y then (absResolvent E δ H y y).re else 0) ∂(model.law : Measure p.SiteMatrix) := by
  set f : p.SiteMatrix × (Fin J → p.Site → ℂ) → p.SiteMatrix × (p.Site → ℂ) :=
    Prod.map id (Function.eval a)
  have hf : Measurable f := measurable_id.prodMap (measurable_pi_apply a)
  have hmap : (fullRingProbeLaw model J).map f =
      (model.law : Measure p.SiteMatrix).prod (circularVectorLaw p.Site) := by
    unfold fullRingProbeLaw
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply a), Measure.map_id,
      Measure.pi_map_eval]
    simp
  have hG : Measurable fun x : p.SiteMatrix × (p.Site → ℂ) =>
      ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 y)) :=
    ENNReal.measurable_ofReal.comp (measurable_absForm_scaled E δ measurable_fst measurable_snd d)
  have h1 : ∫⁻ x, ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 a y))
      ∂fullRingProbeLaw model J =
      ∫⁻ x, ENNReal.ofReal (absForm E δ x.1 (fun y => d y * x.2 y))
        ∂(model.law : Measure p.SiteMatrix).prod (circularVectorLaw p.Site) := by
    rw [← hmap, lintegral_map hG hf]
    rfl
  rw [h1, lintegral_prod _ hG.aemeasurable]
  simp_rw [lintegral_absForm_scaled]
  have hmS : Measurable fun H : p.SiteMatrix => ENNReal.ofReal
      (∑ y, if S y then (absResolvent E δ H y y).re else 0) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun y _ => ?_)
    by_cases hS : S y
    · simp only [hS, ite_true]
      exact Complex.measurable_re.comp (measurable_absResolvent_apply E δ y y)
    · simp only [hS, ite_false]
      exact measurable_const
  rw [← lintegral_const_mul _ hmS]
  refine lintegral_mono fun H => ?_
  rw [← ENNReal.ofReal_mul hκ]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := re_absResolvent_diag_nonneg E δ H y
  have hy := hd y
  split_ifs at hy ⊢
  · exact mul_le_mul_of_nonneg_right hy h0
  · have : ‖d y‖ ^ 2 = 0 := le_antisymm hy (sq_nonneg _)
    rw [this, zero_mul, mul_zero]

end Probe

end BlockBand.Critical.EntireLaw
