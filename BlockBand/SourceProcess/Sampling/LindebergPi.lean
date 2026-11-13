module

public import BlockBand.SourceProcess.Sampling.Lindeberg

/-!
# Lindeberg replacement for finitely many independent samples

* `lindeberg_fin`: induction on the number `N` of samples; coordinate `0` is split off with
  `measurePreserving_piFinSuccAbove`, the remaining samples are replaced first (induction
  hypothesis, at the shifted base `Z_j + c_{j0} ξ_0`), then `ξ_0` (`lindeberg_step`, at the base
  `Z_j + Σ_{i>0} c_{ji} ξ̄_i`).
* `lindeberg`: the same for any finite index type (`measurePreserving_piCongrLeft`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Sampling

open MeasureTheory Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The hybrid value `Π_j F(Z_j + Σ_x c_{jx} B_x)`. -/
def hyb {κ ι : Type*} [Fintype κ] [Fintype ι] (Z : ι → Matrix n n ℂ) (c : ι → κ → ℝ)
    (B : κ → Matrix n n ℂ) : ℝ :=
  ∏ j, invDet (Z j + ∑ x, (c j x : ℂ) • B x)

omit [Fintype n] [DecidableEq n] in
theorem comb_psd {κ : Type*} [Fintype κ] {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) {c : κ → ℝ}
    (hc : ∀ x, 0 ≤ c x) {B : κ → Matrix n n ℂ} (hB : ∀ x, (B x).PosSemidef) :
    (Z + ∑ x, (c x : ℂ) • B x).PosSemidef :=
  hZ.add (posSemidef_sum _ fun x _ => (hB x).smul (by exact_mod_cast hc x))

omit [Fintype n] [DecidableEq n] in
theorem measurable_comb {κ β : Type*} [Fintype κ] [MeasurableSpace β] (Z : Matrix n n ℂ)
    (c : κ → ℝ) {B : κ → β → Matrix n n ℂ} (hB : ∀ x, Measurable (B x)) :
    Measurable fun z => Z + ∑ x, (c x : ℂ) • B x z :=
  meas_add' measurable_const (meas_sum' _ fun x => meas_smul' _ (hB x))

/-- **Lindeberg replacement, `N` samples.** -/
theorem lindeberg_fin {ι α : Type*} [Fintype ι] [MeasurableSpace α] (N : ℕ) :
    ∀ (μ : Fin N → Measure α) (_ : ∀ x, IsProbabilityMeasure (μ x))
      (ξ : Fin N → α → Matrix n n ℂ) (ξm : Fin N → Matrix n n ℂ),
      (∀ x, IsMatSample (μ x) (ξ x) (ξm x)) →
    ∀ (Z : ι → Matrix n n ℂ), (∀ j, (Z j).PosSemidef) → ∀ (c : ι → Fin N → ℝ),
      (∀ j x, 0 ≤ c j x) →
      |∫ z, hyb Z c (fun x => ξ x (z x)) ∂Measure.pi μ - hyb Z c ξm| ≤
        ∑ x, 2 * (∑ j, c j x) ^ 2 * ∫ z, (ξ x z).trace.re ^ 2 ∂μ x := by
  induction N with
  | zero =>
    intro μ hμ ξ ξm h Z hZ c hc
    simp [hyb]
  | succ N ih =>
    intro μ hμ ξ ξm h Z hZ c hc
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) 0
    have hmp : MeasurePreserving e (Measure.pi μ)
        ((μ 0).prod (Measure.pi fun i => μ (Fin.succAbove 0 i))) :=
      measurePreserving_piFinSuccAbove μ 0
    set ν := Measure.pi fun i => μ (Fin.succAbove 0 i)
    set c' : ι → Fin N → ℝ := fun j i => c j (Fin.succAbove 0 i)
    set ξ' : Fin N → α → Matrix n n ℂ := fun i => ξ (Fin.succAbove 0 i)
    set ξm' : Fin N → Matrix n n ℂ := fun i => ξm (Fin.succAbove 0 i)
    set Zr : α → ι → Matrix n n ℂ := fun z0 j => Z j + (c j 0 : ℂ) • ξ 0 z0
    set Z1 : ι → Matrix n n ℂ := fun j => Z j + ∑ i, (c' j i : ℂ) • ξm' i
    have hZr : ∀ z0 j, (Zr z0 j).PosSemidef := fun z0 j =>
      (hZ j).add (((h 0).psd z0).smul (by exact_mod_cast hc j 0))
    have hZ1 : ∀ j, (Z1 j).PosSemidef := fun j =>
      comb_psd (hZ j) (fun i => hc j _) fun i => (h _).mean_psd
    set F : (Fin (N + 1) → α) → ℝ := fun z => hyb Z c (fun x => ξ x (z x))
    have heval : ∀ y : α × (Fin N → α),
        F (e.symm y) = hyb (Zr y.1) c' (fun i => ξ' i (y.2 i)) := by
      intro y
      simp only [F, hyb, Zr, c', ξ', e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv_apply, Fin.sum_univ_succAbove _ 0, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove, add_assoc]
    have hmeasF : ∀ j, Measurable fun z : Fin (N + 1) → α =>
        Z j + ∑ x, (c j x : ℂ) • ξ x (z x) :=
      fun j => measurable_comb _ _ fun x => (h x).meas.comp (measurable_pi_apply x)
    have hint : Integrable (fun y => F (e.symm y)) ((μ 0).prod ν) :=
      integrable_prodInvDet (fun j => (hmeasF j).comp e.symm.measurable) fun j y =>
        comb_psd (hZ j) (hc j) fun x => (h x).psd _
    have hF : ∫ z, F z ∂Measure.pi μ = ∫ y, F (e.symm y) ∂((μ 0).prod ν) :=
      (hmp.symm.integral_comp' F).symm
    have hinner := hint.integral_prod_left
    set inner : α → ℝ := fun z0 => ∫ zr, F (e.symm (z0, zr)) ∂ν
    set G' : α → ℝ := fun z0 => ∏ j, invDet (Z1 j + (c j 0 : ℂ) • ξ 0 z0)
    have hIH : ∀ z0, |inner z0 - G' z0| ≤
        ∑ i, 2 * (∑ j, c' j i) ^ 2 * ∫ z, (ξ' i z).trace.re ^ 2 ∂μ (Fin.succAbove 0 i) := by
      intro z0
      have := ih (fun i => μ (Fin.succAbove 0 i)) (fun i => hμ _) ξ' ξm' (fun i => h _) (Zr z0)
        (hZr z0) c' (fun j i => hc j _)
      have e1 : inner z0 = ∫ zr, hyb (Zr z0) c' (fun i => ξ' i (zr i)) ∂ν :=
        integral_congr_ae (ae_of_all _ fun zr => heval (z0, zr))
      have e2 : G' z0 = hyb (Zr z0) c' ξm' := by
        simp only [G', hyb, Zr, Z1]
        exact Finset.prod_congr rfl fun j _ => by rw [add_right_comm]
      rw [e1, e2]; exact this
    have hG'i : Integrable G' (μ 0) :=
      integrable_prodInvDet (fun j => meas_add' measurable_const (meas_smul' _ (h 0).meas))
        fun j z => (hZ1 j).add (((h 0).psd z).smul (by exact_mod_cast hc j 0))
    have hstep := lindeberg_step (h 0) hZ1 (fun j => hc j 0)
    have htarget : hyb Z c ξm = ∏ j, invDet (Z1 j + (c j 0 : ℂ) • ξm 0) := by
      simp only [hyb, Z1, c', ξm', Fin.sum_univ_succAbove _ 0]
      exact Finset.prod_congr rfl fun j _ => by rw [add_comm ((c j 0 : ℂ) • ξm 0), add_assoc]
    have hsum := Fin.sum_univ_succAbove
      (fun x => 2 * (∑ j, c j x) ^ 2 * ∫ z, (ξ x z).trace.re ^ 2 ∂μ x) 0
    change |∫ z, F z ∂Measure.pi μ - hyb Z c ξm| ≤ _
    rw [hF, integral_prod _ hint, htarget, hsum]
    have hsplit : ∫ z0, inner z0 ∂μ 0 - ∏ j, invDet (Z1 j + (c j 0 : ℂ) • ξm 0) =
        ∫ z0, (inner z0 - G' z0) ∂μ 0 +
          (∫ z0, G' z0 ∂μ 0 - ∏ j, invDet (Z1 j + (c j 0 : ℂ) • ξm 0)) := by
      rw [integral_sub hinner hG'i]; ring
    rw [hsplit]
    have hb : |∫ z0, (inner z0 - G' z0) ∂μ 0| ≤
        ∑ i, 2 * (∑ j, c' j i) ^ 2 * ∫ z, (ξ' i z).trace.re ^ 2 ∂μ (Fin.succAbove 0 i) := by
      have := norm_integral_le_of_norm_le_const (μ := μ 0)
        (f := fun z0 => inner z0 - G' z0)
        (ae_of_all _ fun z0 => by rw [Real.norm_eq_abs]; exact hIH z0)
      simpa using this
    calc _ ≤ |∫ z0, (inner z0 - G' z0) ∂μ 0| +
          |∫ z0, G' z0 ∂μ 0 - ∏ j, invDet (Z1 j + (c j 0 : ℂ) • ξm 0)| := abs_add_le _ _
      _ ≤ _ := by rw [add_comm]; exact add_le_add hstep hb

theorem hyb_reindex {κ κ' ι : Type*} [Fintype κ] [Fintype κ'] [Fintype ι] (f : κ' ≃ κ)
    (Z : ι → Matrix n n ℂ) (c : ι → κ → ℝ) (B : κ → Matrix n n ℂ) :
    hyb Z c B = hyb Z (fun j i => c j (f i)) (fun i => B (f i)) := by
  simp only [hyb]
  exact Finset.prod_congr rfl fun j _ => by
    rw [← Equiv.sum_comp f (fun x => (c j x : ℂ) • B x)]

/-- **Lindeberg replacement, any finite index type.** -/
theorem lindeberg {κ ι α : Type*} [Fintype κ] [Fintype ι] [MeasurableSpace α]
    (μ : κ → Measure α) [∀ x, IsProbabilityMeasure (μ x)] (ξ : κ → α → Matrix n n ℂ)
    (ξm : κ → Matrix n n ℂ) (h : ∀ x, IsMatSample (μ x) (ξ x) (ξm x))
    (Z : ι → Matrix n n ℂ) (hZ : ∀ j, (Z j).PosSemidef) (c : ι → κ → ℝ)
    (hc : ∀ j x, 0 ≤ c j x) :
    |∫ z, hyb Z c (fun x => ξ x (z x)) ∂Measure.pi μ - hyb Z c ξm| ≤
      ∑ x, 2 * (∑ j, c j x) ^ 2 * ∫ z, (ξ x z).trace.re ^ 2 ∂μ x := by
  set f : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hmp := measurePreserving_piCongrLeft (α := fun _ : κ => α) μ f
  have hF := hmp.integral_comp' (fun z => hyb Z c (fun x => ξ x (z x)))
  have key := lindeberg_fin (Fintype.card κ) (fun i => μ (f i)) (fun i => inferInstance)
    (fun i => ξ (f i)) (fun i => ξm (f i)) (fun i => h _) Z hZ (fun j i => c j (f i))
    (fun j i => hc j _)
  rw [← hF, ← Equiv.sum_comp f, hyb_reindex f Z c ξm]
  convert key using 4
  funext w
  rw [hyb_reindex f Z c]
  simp only [MeasurableEquiv.piCongrLeft_apply_apply]

end BlockBand.SourceProcess.Sampling
