module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMomDefs

/-!
# The abstract conditional replacement `CondExpReplace`

Measure: an arbitrary probability measure `μ` on `(Ω, mΩ)`; sub-σ-algebra `m ≤ mΩ`. The proof
(modelled on `B3.StopTail.enorm_integral_indicator_le`):
* `g · 1_A X =ᵐ (1_{A'} g) · 1_A X`, and `1_{A'} g` is `m`-strongly measurable, so the
  pull-out property (`condExp_bilin_of_stronglyMeasurable_left` for the real-bilinear complex
  product) and `integral_condExp` give `∫ g 1_A X = ∫ g 1_A Y`, `Y = μ[1_A X | m]`;
* if `g 1_A β` is integrable, subtract and bound `‖g‖ ≤ C` on `A` pointwise;
* otherwise `1_A β` is not integrable (`‖g 1_A β‖ ≤ C ‖1_A β‖`), hence neither is
  `1_A (Y - β)` (`1_A Y` is integrable), so the right side is `ofReal C · ⊤ = ⊤`
  (`C > 0`, since `C = 0` forces `g 1_A β = 0`).
* `A = ∅` (in particular whenever `C < 0`): both sides are `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.GramMom

open MeasureTheory
open scoped ENNReal

/-- **The conditional replacement bound**.
The sub-σ-algebra `m` is declared before
the ambient instance `mΩ`, so that instance synthesis picks `mΩ`.
The hypothesis on `β` is the
one of `CondExpReplace` as elaborated:
`AEStronglyMeasurable[m] β μ`.
-/
theorem condExpReplace_aux {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {A A' : Set Ω}
    (hA' : MeasurableSet[m] A') (hAA : A =ᵐ[μ] A') {g : Ω → ℂ} (hg : StronglyMeasurable[m] g)
    {C : ℝ} (hgC : ∀ ω ∈ A, ‖g ω‖ ≤ C) {X β : Ω → ℂ} (hX : Integrable (A.indicator X) μ)
    (hβm : AEStronglyMeasurable[m] β μ) :
    ‖(∫ ω, A.indicator (fun ω => g ω * X ω) ω ∂μ) -
        ∫ ω, A.indicator (fun ω => g ω * β ω) ω ∂μ‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator X | m] ω - β ω) ω‖ₑ ∂μ := by
  have hβ : AEStronglyMeasurable β μ := hβm.mono hm
  rcases A.eq_empty_or_nonempty with rfl | ⟨ω0, hω0⟩
  · simp
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hgC ω0 hω0)
  set Y : Ω → ℂ := μ[A.indicator X | m] with hYdef
  have hind : ∀ f : Ω → ℂ, A.indicator f =ᵐ[μ] A'.indicator f :=
    fun f => indicator_ae_eq_of_ae_eq_set hAA
  have hAm : MeasurableSet A' := hm _ hA'
  have hgm : StronglyMeasurable g := hg.mono hm
  -- the bound `‖g · 1_A f‖ ≤ C ‖1_A f‖`
  have hbd : ∀ (f : Ω → ℂ) (ω : Ω), ‖g ω * A.indicator f ω‖ ≤ C * ‖A.indicator f ω‖ := by
    intro f ω
    by_cases hω : ω ∈ A
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hgC ω hω) (norm_nonneg _)
    · simp [Set.indicator_of_notMem hω]
  have hint : ∀ f : Ω → ℂ, Integrable (A.indicator f) μ →
      Integrable (fun ω => g ω * A.indicator f ω) μ := fun f hf =>
    Integrable.mono' (hf.norm.const_mul C) (hgm.aestronglyMeasurable.mul hf.1)
      (ae_of_all _ (hbd f))
  have hY : Integrable Y μ := integrable_condExp
  have hAY : Integrable (A.indicator Y) μ :=
    (integrable_congr (hind Y)).2 (hY.indicator hAm)
  have hAβm : AEStronglyMeasurable (A.indicator β) μ :=
    (hβ.indicator hAm).congr (hind β).symm
  have hgX : Integrable (fun ω => g ω * A.indicator X ω) μ := hint X hX
  have hgY : Integrable (fun ω => g ω * A.indicator Y ω) μ := hint Y hAY
  -- the replacement `∫ g 1_A X = ∫ g 1_A Y`
  have hrep : ∫ ω, g ω * A.indicator X ω ∂μ = ∫ ω, g ω * A.indicator Y ω ∂μ := by
    let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
    have hB : ∀ a b : ℂ, B a b = a * b := fun a b => rfl
    have hh : StronglyMeasurable[m] (A'.indicator g) := hg.indicator hA'
    have e1 : (fun ω => g ω * A.indicator X ω) =ᵐ[μ]
        fun ω => B (A'.indicator g ω) (A.indicator X ω) := by
      filter_upwards [hind g] with ω hω
      rw [hB, ← hω]
      by_cases h : ω ∈ A <;> simp [h]
    have e2 : (fun ω => B (A'.indicator g ω) (Y ω)) =ᵐ[μ]
        fun ω => g ω * A.indicator Y ω := by
      filter_upwards [hind g] with ω hω
      rw [hB, ← hω]
      by_cases h : ω ∈ A <;> simp [h]
    have hhX : Integrable (fun ω => B (A'.indicator g ω) (A.indicator X ω)) μ :=
      (integrable_congr e1).1 hgX
    have hpull := condExp_bilin_of_stronglyMeasurable_left (m := m) (μ := μ) B hh hhX hX
    rw [integral_congr_ae e1, ← integral_condExp hm, integral_congr_ae hpull,
      integral_congr_ae e2]
  have hL : ∀ f : Ω → ℂ, (fun ω => A.indicator (fun ω => g ω * f ω) ω) =
      fun ω => g ω * A.indicator f ω := fun f => funext fun ω => Set.indicator_mul_right _ _ _
  rw [hL X, hL β, hrep]
  by_cases hgβ : Integrable (fun ω => g ω * A.indicator β ω) μ
  · rw [← integral_sub hgY hgβ]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω, ← mul_sub,
        enorm_mul]
      refine mul_le_mul_left ?_ _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hgC ω hω)
    · simp [Set.indicator_of_notMem hω]
  · -- the right side is `⊤`
    have hβA : ¬ Integrable (A.indicator β) μ := fun h => hgβ (hint β h)
    have hD : ¬ Integrable (A.indicator (fun ω => Y ω - β ω)) μ := by
      intro h
      refine hβA ((integrable_congr (ae_of_all _ fun ω => ?_)).1 (hAY.sub h))
      by_cases hω : ω ∈ A
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    have hDm : AEStronglyMeasurable (A.indicator (fun ω => Y ω - β ω)) μ :=
      (hAY.1.sub hAβm).congr (ae_of_all _ fun ω => by
        by_cases hω : ω ∈ A
        · simp [Set.indicator_of_mem hω]
        · simp [Set.indicator_of_notMem hω])
    have htop : ∫⁻ ω, ‖A.indicator (fun ω => Y ω - β ω) ω‖ₑ ∂μ = ⊤ := by
      by_contra hne
      exact hD ⟨hDm, lt_top_iff_ne_top.2 hne⟩
    rcases hC0.lt_or_eq with hpos | hzero
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
      exact le_top
    · exfalso
      refine hgβ ((integrable_congr (ae_of_all _ fun ω => ?_)).1 (integrable_zero Ω ℂ μ))
      by_cases hω : ω ∈ A
      · have : ‖g ω‖ ≤ 0 := hzero ▸ hgC ω hω
        simp [norm_le_zero_iff.1 this]
      · simp [Set.indicator_of_notMem hω]

/-- **`CondExpReplace` holds**. -/
theorem condExpReplace_holds :
    BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local.CondExpReplace :=
  fun {Ω} {mΩ} μ _ m hm _ _ hA' hAA _ hg _ hgC _ _ hX hβ =>
    @condExpReplace_aux Ω m mΩ μ _ hm _ _ hA' hAA _ hg _ hgC _ _ hX hβ

end BlockBand.SourceProcess.PhysApprox.GramMom
