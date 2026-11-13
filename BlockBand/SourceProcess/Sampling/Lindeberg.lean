module

public import BlockBand.SourceProcess.Sampling.DetLin
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure

/-!
# Lindeberg replacement of independent positive rank-one samples by their means

`IsMatSample μ ξ ξm`: `ξ` is a measurable PSD-matrix valued sample under the probability `μ`, every
linear functional `Re Tr(K ·)` is integrable with mean `Re Tr(K ξm)`, `ξm ⪰ 0` and
`(Re Tr ξ)²` is integrable.

* `lindeberg_step`: `|E Π_j F(Z_j + c_j ξ) - Π_j F(Z_j + c_j ξm)| ≤ 2(Σ_j c_j)² E(Re Tr ξ)²`.
  The linear term of `abs_prod_invDet_sub_le` has the same mean at `ξ` and at `ξm`; the two
  quadratic remainders are bounded by `E(Tr ξ)²` and `(Tr ξm)² ≤ E(Tr ξ)²` (`sq_integral_le`).
* proved from it in a sibling module: `lindeberg_fin` (induction on the number of samples, splitting off coordinate `0` with
  `measurePreserving_piFinSuccAbove`) and `lindeberg` (any finite index set): for independent
  samples `ξ_x` under `Measure.pi μ`,
  `|E Π_j F(Z_j + Σ_x c_{jx} ξ_x) - Π_j F(Z_j + Σ_x c_{jx} ξm_x)| ≤ Σ_x 2(Σ_j c_{jx})² E(Re Tr ξ_x)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A measurable positive matrix sample with mean `ξm` (tested on all linear functionals) and
square-integrable trace. -/
structure IsMatSample {α : Type*} [MeasurableSpace α] (μ : Measure α) (ξ : α → Matrix n n ℂ)
    (ξm : Matrix n n ℂ) : Prop where
  psd : ∀ z, (ξ z).PosSemidef
  meas : Measurable ξ
  lin_int : ∀ K : Matrix n n ℂ, Integrable (fun z => (K * ξ z).trace.re) μ
  lin_eq : ∀ K : Matrix n n ℂ, ∫ z, (K * ξ z).trace.re ∂μ = (K * ξm).trace.re
  mean_psd : ξm.PosSemidef
  sq_int : Integrable (fun z => (ξ z).trace.re ^ 2) μ

omit [Fintype n] [DecidableEq n] in
theorem meas_add' {β : Type*} [MeasurableSpace β] {f g : β → Matrix n n ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun z => f z + g z :=
  Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix.add hg.eval_matrix

omit [Fintype n] [DecidableEq n] in
theorem meas_smul' {β : Type*} [MeasurableSpace β] {f : β → Matrix n n ℂ} (c : ℂ)
    (hf : Measurable f) : Measurable fun z => c • f z :=
  Measurable.of_eval_matrix _ fun _ _ => measurable_const.mul hf.eval_matrix

omit [Fintype n] [DecidableEq n] in
theorem meas_sum' {β κ : Type*} [MeasurableSpace β] (s : Finset κ) {f : κ → β → Matrix n n ℂ}
    (hf : ∀ x, Measurable (f x)) : Measurable fun z => ∑ x ∈ s, f x z := by
  refine Measurable.of_eval_matrix _ fun a b => ?_
  simp only [Matrix.sum_apply]
  exact Finset.measurable_sum _ fun x _ => (hf x).eval_matrix

theorem measurable_prodInvDet {β ι : Type*} [MeasurableSpace β] [Fintype ι]
    {F : ι → β → Matrix n n ℂ} (hF : ∀ j, Measurable (F j)) :
    Measurable fun z => ∏ j, invDet (F j z) := by
  refine Finset.measurable_prod _ fun j _ => Complex.measurable_re.comp (Measurable.inv ?_)
  exact (continuous_id.matrix_det).measurable.comp (meas_add' measurable_const (hF j))

theorem prodInvDet_mem {ι : Type*} [Fintype ι] {X : ι → Matrix n n ℂ}
    (hX : ∀ j, (X j).PosSemidef) : 0 ≤ ∏ j, invDet (X j) ∧ ∏ j, invDet (X j) ≤ 1 :=
  ⟨Finset.prod_nonneg fun j _ => (invDet_mem (hX j)).1.le,
    Finset.prod_le_one₀ (fun j _ => (invDet_mem (hX j)).1.le) fun j _ => (invDet_mem (hX j)).2⟩

theorem integrable_prodInvDet {β ι : Type*} [MeasurableSpace β] {μ : Measure β}
    [IsFiniteMeasure μ] [Fintype ι] {F : ι → β → Matrix n n ℂ} (hF : ∀ j, Measurable (F j))
    (hP : ∀ j z, (F j z).PosSemidef) : Integrable (fun z => ∏ j, invDet (F j z)) μ := by
  refine Integrable.of_bound (measurable_prodInvDet hF).aestronglyMeasurable 1
    (ae_of_all _ fun z => ?_)
  have h := prodInvDet_mem fun j => hP j z
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2

/-- Jensen: `(E f)² ≤ E f²` under a probability measure. -/
theorem sq_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun z => f z ^ 2) μ) :
    (∫ z, f z ∂μ) ^ 2 ≤ ∫ z, f z ^ 2 ∂μ := by
  set c := ∫ z, f z ∂μ
  have h : 0 ≤ ∫ z, (f z ^ 2 - 2 * c * f z + c ^ 2) ∂μ :=
    integral_nonneg fun z => by simp only [Pi.zero_apply]; nlinarith [sq_nonneg (f z - c)]
  have i1 : Integrable (fun z => f z ^ 2 - 2 * c * f z) μ := hf2.sub (hf.const_mul _)
  rw [integral_add i1 (integrable_const _), integral_sub hf2 (hf.const_mul _),
    integral_const_mul] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

/-- **One replacement step.** -/
theorem lindeberg_step {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {ξ : α → Matrix n n ℂ} {ξm : Matrix n n ℂ} (h : IsMatSample μ ξ ξm)
    {Z : ι → Matrix n n ℂ} (hZ : ∀ j, (Z j).PosSemidef) {c : ι → ℝ} (hc : ∀ j, 0 ≤ c j) :
    |∫ z, ∏ j, invDet (Z j + (c j : ℂ) • ξ z) ∂μ - ∏ j, invDet (Z j + (c j : ℂ) • ξm)| ≤
      2 * (∑ j, c j) ^ 2 * ∫ z, (ξ z).trace.re ^ 2 ∂μ := by
  set P0 := ∏ j, invDet (Z j)
  set L : Matrix n n ℂ → ℝ := fun B => ∑ j, c j * (linKer (hZ j).1 * B).trace.re
  set G : Matrix n n ℂ → ℝ := fun B => ∏ j, invDet (Z j + (c j : ℂ) • B)
  set s := ∑ j, c j
  have hs : 0 ≤ s := Finset.sum_nonneg fun j _ => hc j
  have hPSD : ∀ B : Matrix n n ℂ, B.PosSemidef → ∀ j, (Z j + (c j : ℂ) • B).PosSemidef :=
    fun B hB j => (hZ j).add (hB.smul (by exact_mod_cast hc j))
  have hGi : Integrable (fun z => G (ξ z)) μ :=
    integrable_prodInvDet (fun j => meas_add' measurable_const (meas_smul' _ h.meas))
      fun j z => hPSD _ (h.psd z) j
  have hLi : Integrable (fun z => L (ξ z)) μ :=
    integrable_finsetSum _ fun j _ => (h.lin_int _).const_mul _
  have hLe : ∫ z, L (ξ z) ∂μ = L ξm := by
    simp only [L]
    rw [integral_finsetSum _ fun j _ => (h.lin_int _).const_mul _]
    exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, h.lin_eq]
  have hA : ∀ B : Matrix n n ℂ, B.PosSemidef → |G B - P0 * (1 - L B)| ≤ s ^ 2 * B.trace.re ^ 2 :=
    fun B hB => by
      have h1 := abs_prod_invDet_sub_le hZ hB hc
      have h2 := sum_linTr_le hZ hB hc
      have h3 : (L B) ^ 2 ≤ (s * B.trace.re) ^ 2 := pow_le_pow_left₀ h2.1 h2.2 2
      exact h1.trans (by rw [mul_pow] at h3; exact h3)
  have hJ : ξm.trace.re ^ 2 ≤ ∫ z, (ξ z).trace.re ^ 2 ∂μ := by
    have e := h.lin_eq 1
    have hi := h.lin_int 1
    simp only [one_mul] at e hi
    rw [← e]; exact sq_integral_le hi h.sq_int
  have hR : Integrable (fun z => P0 * (1 - L (ξ z))) μ := ((integrable_const _).sub hLi).const_mul _
  have hRe : ∫ z, P0 * (1 - L (ξ z)) ∂μ = P0 * (1 - L ξm) := by
    rw [integral_const_mul, integral_sub (integrable_const _) hLi, hLe]
    simp
  have hD : |∫ z, (G (ξ z) - P0 * (1 - L (ξ z))) ∂μ| ≤ s ^ 2 * ∫ z, (ξ z).trace.re ^ 2 ∂μ := by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    exact integral_mono (hGi.sub hR).abs (h.sq_int.const_mul _) fun z => hA _ (h.psd z)
  have hsplit : ∫ z, G (ξ z) ∂μ - G ξm =
      ∫ z, (G (ξ z) - P0 * (1 - L (ξ z))) ∂μ + (P0 * (1 - L ξm) - G ξm) := by
    rw [integral_sub hGi hR, hRe]; ring
  change |∫ z, G (ξ z) ∂μ - G ξm| ≤ _
  rw [hsplit]
  have hB := hA ξm h.mean_psd
  rw [abs_sub_comm] at hB
  calc _ ≤ |∫ z, (G (ξ z) - P0 * (1 - L (ξ z))) ∂μ| + |P0 * (1 - L ξm) - G ξm| := abs_add_le _ _
    _ ≤ s ^ 2 * ∫ z, (ξ z).trace.re ^ 2 ∂μ + s ^ 2 * ∫ z, (ξ z).trace.re ^ 2 ∂μ :=
        add_le_add hD (hB.trans (mul_le_mul_of_nonneg_left hJ (sq_nonneg s)))
    _ = _ := by ring

end BlockBand.SourceProcess.Sampling
