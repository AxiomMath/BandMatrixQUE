module

public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Product test functions determine finite measures on `ℝ × ℝ`

`measure_eq_of_lintegral_prod`: if `μ` is a finite measure on `ℝ × ℝ` (product σ-algebra) and
`∫⁻ g(x) k(y) dμ = ∫⁻ g(x) k(y) dν` for all bounded continuous `g, k : ℝ → ℝ≥0`, then `μ = ν`.
No finiteness of `ν` is assumed.

Proof: for fixed `k`, the finite measures `A ↦ ∫⁻_{A × ℝ} k(y) dμ` and the same for `ν` agree on
bounded continuous `g` (Mathlib's `ext_of_forall_lintegral_eq_of_IsFiniteMeasure`), so they agree
on all Borel `A`; for fixed `A`, the finite measures `B ↦ μ(A × B)`, `B ↦ ν(A × B)` then agree on
bounded continuous `k`, hence on all `B`; rectangles form a generating π-system.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

theorem lintegral_boundedNNReal_lt_top {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ≥0} {C : ℝ≥0} (hC : ∀ a, f a ≤ C) :
    ∫⁻ a, (f a : ℝ≥0∞) ∂μ < ∞ := by
  calc ∫⁻ a, (f a : ℝ≥0∞) ∂μ ≤ ∫⁻ _, (C : ℝ≥0∞) ∂μ :=
        lintegral_mono fun a => ENNReal.coe_le_coe.2 (hC a)
    _ = C * μ univ := lintegral_const _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ univ)

/-- **Product test functions determine a finite measure on `ℝ × ℝ`.** -/
theorem measure_eq_of_lintegral_prod {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h : ∀ g k : ℝ →ᵇ ℝ≥0,
      ∫⁻ p, (g p.1 : ℝ≥0∞) * k p.2 ∂μ = ∫⁻ p, (g p.1 : ℝ≥0∞) * k p.2 ∂ν) :
    μ = ν := by
  -- step 1: for fixed `k`, the `x`-marginals of `k(y) dμ` and `k(y) dν` agree
  have step1 : ∀ k : ℝ →ᵇ ℝ≥0, ∀ A : Set ℝ, MeasurableSet A →
      ∫⁻ p in A ×ˢ univ, (k p.2 : ℝ≥0∞) ∂μ = ∫⁻ p in A ×ˢ univ, (k p.2 : ℝ≥0∞) ∂ν := by
    intro k A hA
    have hkm : Measurable fun p : ℝ × ℝ => (k p.2 : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp (k.continuous.comp continuous_snd)).measurable
    set μk := (μ.withDensity fun p => (k p.2 : ℝ≥0∞)).map Prod.fst with hμk
    set νk := (ν.withDensity fun p => (k p.2 : ℝ≥0∞)).map Prod.fst with hνk
    obtain ⟨C, hC⟩ := k.bounded
    have hfin : IsFiniteMeasure (μ.withDensity fun p => (k p.2 : ℝ≥0∞)) :=
      isFiniteMeasure_withDensity
        (lintegral_boundedNNReal_lt_top μ (f := fun p => k p.2) (C := k 0 + C.toNNReal)
          fun p => by
            have h1 := hC p.2 0
            rw [NNReal.dist_eq] at h1
            rw [← NNReal.coe_le_coe, NNReal.coe_add]
            have h2 := (abs_le.1 h1).2
            have h3 := Real.le_coe_toNNReal C
            linarith).ne
    have hμkf : IsFiniteMeasure μk := by rw [hμk]; infer_instance
    have hint : ∀ (ρ : Measure (ℝ × ℝ)) (g : ℝ →ᵇ ℝ≥0),
        ∫⁻ x, (g x : ℝ≥0∞) ∂((ρ.withDensity fun p => (k p.2 : ℝ≥0∞)).map Prod.fst) =
          ∫⁻ p, (g p.1 : ℝ≥0∞) * k p.2 ∂ρ := by
      intro ρ g
      have hgm : Measurable fun x : ℝ => (g x : ℝ≥0∞) :=
        (ENNReal.continuous_coe.comp g.continuous).measurable
      have e := lintegral_withDensity_eq_lintegral_mul ρ hkm (hgm.comp measurable_fst)
      simp only [Function.comp_def] at e
      rw [lintegral_map hgm measurable_fst, e]
      refine lintegral_congr fun p => ?_
      simp only [Pi.mul_apply]
      ring
    have heq : μk = νk := ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun g => by
      rw [hμk, hνk, hint, hint, h]
    have hA' := congrArg (fun ρ => ρ A) heq
    simp only [hμk, hνk] at hA'
    rw [Measure.map_apply measurable_fst hA, Measure.map_apply measurable_fst hA,
      withDensity_apply _ (measurable_fst hA), withDensity_apply _ (measurable_fst hA)] at hA'
    simpa [Set.prod_univ] using hA'
  -- step 2: for fixed `A`, the measures `B ↦ μ(A × B)`, `ν(A × B)` agree
  have step2 : ∀ A : Set ℝ, MeasurableSet A → ∀ B : Set ℝ, MeasurableSet B →
      μ (A ×ˢ B) = ν (A ×ˢ B) := by
    intro A hA
    set μA := (μ.restrict (A ×ˢ univ)).map Prod.snd with hμA
    set νA := (ν.restrict (A ×ˢ univ)).map Prod.snd with hνA
    have heq : μA = νA := ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun k => by
      have hkm : Measurable fun y : ℝ => (k y : ℝ≥0∞) :=
        (ENNReal.continuous_coe.comp k.continuous).measurable
      rw [hμA, hνA, lintegral_map hkm measurable_snd, lintegral_map hkm measurable_snd]
      exact step1 k A hA
    intro B hB
    have hB' := congrArg (fun ρ => ρ B) heq
    simp only [hμA, hνA] at hB'
    rw [Measure.map_apply measurable_snd hB, Measure.map_apply measurable_snd hB,
      Measure.restrict_apply (measurable_snd hB), Measure.restrict_apply (measurable_snd hB)]
      at hB'
    have e : Prod.snd ⁻¹' B ∩ A ×ˢ (univ : Set ℝ) = A ×ˢ B := by
      ext p; simp [and_comm]
    rwa [e] at hB'
  -- step 3: rectangles generate
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact step2 A hA B hB
  · rw [← Set.univ_prod_univ]
    exact step2 univ MeasurableSet.univ univ MeasurableSet.univ

end BlockBand.Diffusion
