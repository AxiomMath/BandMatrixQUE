module

public import BlockBand.Internal.Contracts.TransmissionStatements
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fresh sizes: mean and centred `L²` size of a function of one fresh layer

`FreshSize ρ X α σ`: on a probability space `(F, ρ)`, `X : F → ℂ` is integrable, `|E X| ≤ α`
and `‖X - E X‖_{L²} ≤ σ`. Closed under `+`, `-`, scalars and `conj` (`FreshSize.add`, …).
An `L²` bound `‖X‖₂ ≤ L` gives `FreshSize X L (2L)` (`FreshSize.of_L2`). A sum
`Σ_y conj(A_y) B_y` with `‖A_y‖₄ ≤ a_y`, `‖B_y‖₄ ≤ b_y` has `‖·‖₂ ≤ Σ a_y b_y`
(`eLpNorm_sum_star_mul_le`, Hölder `4,4 → 2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont.OneLayer

open MeasureTheory
open scoped ENNReal ComplexConjugate

variable {F : Type*} [MeasurableSpace F] {ρ : Measure F}

/-- Mean `≤ α`, centred `L²` norm `≤ σ`. -/
structure FreshSize (ρ : Measure F) (X : F → ℂ) (α σ : ℝ) : Prop where
  meas : AEStronglyMeasurable X ρ
  int : Integrable X ρ
  α_nonneg : 0 ≤ α
  σ_nonneg : 0 ≤ σ
  mean : ‖∫ y, X y ∂ρ‖ ≤ α
  dev : eLpNorm (fun y => X y - ∫ y', X y' ∂ρ) 2 ρ ≤ ENNReal.ofReal σ

namespace FreshSize

variable [IsProbabilityMeasure ρ] {X Y : F → ℂ} {α σ α' σ' : ℝ}

omit [IsProbabilityMeasure ρ] in
theorem mono (h : FreshSize ρ X α σ) (hα : α ≤ α') (hσ : σ ≤ σ') : FreshSize ρ X α' σ' :=
  ⟨h.meas, h.int, h.α_nonneg.trans hα, h.σ_nonneg.trans hσ, h.mean.trans hα,
    h.dev.trans (ENNReal.ofReal_le_ofReal hσ)⟩

omit [IsProbabilityMeasure ρ] in
theorem add (h : FreshSize ρ X α σ) (h' : FreshSize ρ Y α' σ') :
    FreshSize ρ (fun y => X y + Y y) (α + α') (σ + σ') := by
  refine ⟨h.meas.add h'.meas, h.int.add h'.int, add_nonneg h.α_nonneg h'.α_nonneg,
    add_nonneg h.σ_nonneg h'.σ_nonneg, ?_, ?_⟩
  · rw [integral_add h.int h'.int]
    exact (norm_add_le _ _).trans (add_le_add h.mean h'.mean)
  · rw [integral_add h.int h'.int]
    have e : (fun y => X y + Y y - (∫ y', X y' ∂ρ + ∫ y', Y y' ∂ρ)) =
        (fun y => X y - ∫ y', X y' ∂ρ) + (fun y => Y y - ∫ y', Y y' ∂ρ) := by
      funext y; simp only [Pi.add_apply]; ring
    rw [e, ENNReal.ofReal_add h.σ_nonneg h'.σ_nonneg]
    exact (eLpNorm_add_le one_le_two).trans (add_le_add h.dev h'.dev)

omit [IsProbabilityMeasure ρ] in
theorem const_mul (h : FreshSize ρ X α σ) (c : ℂ) :
    FreshSize ρ (fun y => c * X y) (‖c‖ * α) (‖c‖ * σ) := by
  refine ⟨aestronglyMeasurable_const.mul h.meas, h.int.const_mul c,
    mul_nonneg (norm_nonneg _) h.α_nonneg, mul_nonneg (norm_nonneg _) h.σ_nonneg, ?_, ?_⟩
  · rw [integral_const_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left h.mean (norm_nonneg _)
  · rw [integral_const_mul]
    have e : (fun y => c * X y - c * ∫ y', X y' ∂ρ) = c • fun y => X y - ∫ y', X y' ∂ρ := by
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, eLpNorm_const_smul, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    exact mul_le_mul_right h.dev _

omit [IsProbabilityMeasure ρ] in
theorem starC (h : FreshSize ρ X α σ) : FreshSize ρ (fun y => star (X y)) α σ := by
  have hint : ∫ y, star (X y) ∂ρ = star (∫ y, X y ∂ρ) := integral_conj
  refine ⟨h.meas.star, h.int.mono h.meas.star (ae_of_all _ fun y => by simp), h.α_nonneg,
    h.σ_nonneg, ?_, ?_⟩
  · rw [hint, norm_star]; exact h.mean
  · rw [hint]
    have e : (fun y => star (X y) - star (∫ y', X y' ∂ρ)) =
        star fun y => X y - ∫ y', X y' ∂ρ := by
      funext y; simp
    rw [e, eLpNorm_star]; exact h.dev

omit [IsProbabilityMeasure ρ] in
theorem neg (h : FreshSize ρ X α σ) : FreshSize ρ (fun y => -X y) α σ := by
  have := h.const_mul (-1)
  simp only [norm_neg, norm_one, one_mul, neg_one_mul] at this
  exact this

omit [IsProbabilityMeasure ρ] in
theorem sub (h : FreshSize ρ X α σ) (h' : FreshSize ρ Y α' σ') :
    FreshSize ρ (fun y => X y - Y y) (α + α') (σ + σ') := by
  have := h.add h'.neg
  simp only [← sub_eq_add_neg] at this
  exact this

/-- An `L²` bound gives mean `≤ L` and centred size `≤ 2L`. -/
theorem of_L2 {L : ℝ} (hL : 0 ≤ L) (hm : AEStronglyMeasurable X ρ)
    (h2 : eLpNorm X 2 ρ ≤ ENNReal.ofReal L) : FreshSize ρ X L (2 * L) := by
  have hmem : MemLp X 2 ρ := lt_of_le_of_lt h2 ENNReal.ofReal_lt_top
  have hint : Integrable X ρ := hmem.integrable one_le_two
  have h1 : eLpNorm X 1 ρ ≤ ENNReal.ofReal L :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans h2
  have hmean : ‖∫ y, X y ∂ρ‖ ≤ L := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [integral_norm_eq_lintegral_enorm hm, ← eLpNorm_one_eq_lintegral_enorm hm]
    exact ENNReal.toReal_le_of_le_ofReal hL h1
  refine ⟨hm, hint, hL, by positivity, hmean, ?_⟩
  have hc : eLpNorm (fun _ : F => ∫ y', X y' ∂ρ) 2 ρ ≤ ENNReal.ofReal L := by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero ρ), measure_univ,
      ENNReal.one_rpow, mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hmean
  calc eLpNorm (fun y => X y - ∫ y', X y' ∂ρ) 2 ρ
      ≤ eLpNorm X 2 ρ + eLpNorm (fun _ : F => ∫ y', X y' ∂ρ) 2 ρ :=
        eLpNorm_sub_le (f := X) (g := fun _ : F => ∫ y', X y' ∂ρ) one_le_two
    _ ≤ ENNReal.ofReal L + ENNReal.ofReal L := add_le_add h2 hc
    _ = ENNReal.ofReal (2 * L) := by rw [← ENNReal.ofReal_add hL hL]; ring_nf

end FreshSize

instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩

/-- Hölder `4,4 → 2` for a sum of products. -/
theorem eLpNorm_sum_star_mul_le {ι : Type*} [Fintype ι] (A B : ι → F → ℂ)
    (hA : ∀ y, AEStronglyMeasurable (A y) ρ) (hB : ∀ y, AEStronglyMeasurable (B y) ρ)
    (a b : ι → ℝ) (ha : ∀ y, 0 ≤ a y) (hb : ∀ y, 0 ≤ b y)
    (hA4 : ∀ y, eLpNorm (A y) 4 ρ ≤ ENNReal.ofReal (a y))
    (hB4 : ∀ y, eLpNorm (B y) 4 ρ ≤ ENNReal.ofReal (b y)) :
    eLpNorm (fun ω => ∑ y, star (A y ω) * B y ω) 2 ρ ≤ ENNReal.ofReal (∑ y, a y * b y) := by
  have hterm : ∀ y, eLpNorm (fun ω => star (A y ω) * B y ω) 2 ρ ≤
      ENNReal.ofReal (a y * b y) := by
    intro y
    have e : (fun ω => star (A y ω) * B y ω) = (star (A y)) • B y := by
      funext ω; simp [smul_eq_mul]
    rw [e]
    refine (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (hA y).star (hB y)).trans ?_
    rw [eLpNorm_star, ENNReal.ofReal_mul (ha y)]
    exact mul_le_mul' (hA4 y) (hB4 y)
  have e2 : (fun ω => ∑ y, star (A y ω) * B y ω) =
      ∑ y, fun ω => star (A y ω) * B y ω := by
    funext ω; simp
  rw [e2]
  refine (eLpNorm_sum_le one_le_two).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun y _ => mul_nonneg (ha y) (hb y)]
  exact Finset.sum_le_sum fun y _ => hterm y

end BlockBand.SourceProcess.LengthCont.OneLayer
