module

public import BlockBand.Critical.GlobalSource.ReplacementHybrid

/-!
# Global Gaussian source, source replacement: one Lindeberg swap of the hybrid

On the product of the slot laws `slotMeasures`, replacing the Gaussian weight of one slot by the
tag weight changes the phase to `θ₀ + tα + t²β` with real-linear part `swapAlpha`, quadratic part
`swapBeta` and third-order remainder `swapRemainder`; by the matched slot moments, the
characteristic value changes by at most the two expected remainders
(`enorm_integral_hybridF_swap_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

section Swap
variable {W L J M : ℕ}

/-- The slot laws of the hybrid: slot `s` uses the profile of its group. -/
def slotMeasures (W L : ℕ) {J M : ℕ} (r : Fin J → Fin L → ℝ) :
    Fin (J * M) → Measure (SlotSample W L) :=
  fun s => slotLaw W L (r (tagGroup s))

/-- The real-linear part `α` of one swap. -/
def swapAlpha (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (x : Fin (J * M) → SlotSample W L)
    (y' : SlotSample W L) : ℝ :=
  (star (linVec (coefU u) G (slotSum (zeroAt j Λ₀) x) (tagGroup j)) ⬝ᵥ
    weightVec (lam y'.1) y'.2).re

/-- The quadratic part `β` of one swap. -/
def swapBeta (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (j : Fin (J * M))
    (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (y' : SlotSample W L) : ℝ :=
  (coefU u (tagGroup j) (tagGroup j) *
    (star (weightVec (lam y'.1) y'.2) ⬝ᵥ (G *ᵥ weightVec (lam y'.1) y'.2))).re

/-- The third-order remainder of one swap. -/
def swapRemainder (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2))
    (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ) (x : Fin (J * M) → SlotSample W L)
    (y' : SlotSample W L) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 *
    (4 * |swapAlpha G Λ₀ u j lam x y'| ^ 3 +
      |swapAlpha G Λ₀ u j lam x y'| * |swapBeta G u j lam y'| + 5 * swapBeta G u j lam y' ^ 2))

theorem integrable_of_norm_le_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℂ} (hm : Measurable f) (h : ∀ z, ‖f z‖ ≤ 1) : Integrable f μ :=
  (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ h)

/-- **One Lindeberg swap of the hybrid**: replacing the Gaussian weight of slot
`j` by the tag weight changes the characteristic value by at most the two expected remainders. -/
theorem enorm_integral_hybridF_swap_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ}
    (hG : Measurable G) {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) (hM : 0 < M)
    (Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ) (j : Fin (J * M))
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    ‖∫ z, hybridF G (Function.update Λ₀ j
          (tagWeight W L (profileMass W L (r (tagGroup j))))) u z
          ∂ν.prod (Measure.pi (slotMeasures W L r)) -
        ∫ z, hybridF G (Function.update Λ₀ j (fun _ => gaussWeight W L (r (tagGroup j)))) u z
          ∂ν.prod (Measure.pi (slotMeasures W L r))‖ₑ ≤
      ∫⁻ ω, ∫⁻ x, (∫⁻ y', swapRemainder (G ω) Λ₀ u j
            (tagWeight W L (profileMass W L (r (tagGroup j)))) x y' ∂slotLaw W L (r (tagGroup j)) +
          ∫⁻ y', swapRemainder (G ω) Λ₀ u j (fun _ => gaussWeight W L (r (tagGroup j))) x y'
            ∂slotLaw W L (r (tagGroup j)))
        ∂Measure.pi (slotMeasures W L r) ∂ν := by
  classical
  set μ := slotMeasures W L r (M := M)
  have hμ : ∀ s, IsProbabilityMeasure (μ s) := fun s => isProbabilityMeasure_slotLaw (hr _)
  set lt := tagWeight W L (profileMass W L (r (tagGroup j)))
  set lg : Fin (L + 1) → Fin L × Fin W → ℝ := fun _ => gaussWeight W L (r (tagGroup j))
  have hF : ∀ Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ, Measurable (hybridF G Λ u) := fun Λ => measurable_hybridF hG Λ u
  have hint : ∀ Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ, Integrable (hybridF G Λ u) (ν.prod (Measure.pi μ)) := fun Λ =>
    integrable_of_norm_le_one (hF Λ) fun z => (norm_hybridF G Λ u z).le
  rw [← integral_sub (hint _) (hint _)]
  rw [integral_prod (fun z => hybridF G (Function.update Λ₀ j lt) u z -
    hybridF G (Function.update Λ₀ j lg) u z) ((hint _).sub (hint _))]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun ω => ?_)
  have hsec : ∀ Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ, Measurable fun y : Fin (J * M) → SlotSample W L => hybridF G Λ u (ω, y) :=
    fun Λ => (hF Λ).comp measurable_prodMk_left
  have hI : Integrable (fun y => hybridF G (Function.update Λ₀ j lt) u (ω, y) -
      hybridF G (Function.update Λ₀ j lg) u (ω, y)) (Measure.pi μ) :=
    (integrable_of_norm_le_one (hsec _) fun y => (norm_hybridF G _ u _).le).sub
      (integrable_of_norm_le_one (hsec _) fun y => (norm_hybridF G _ u _).le)
  rw [integral_pi_eq_integral_update μ j hI]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
  have hsec' : ∀ Λ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ, Measurable fun y' : SlotSample W L =>
      hybridF G Λ u (ω, Function.update x j y') :=
    fun Λ => (hsec Λ).comp (measurable_update x)
  have hμj : IsProbabilityMeasure (μ j) := hμ j
  rw [integral_sub (integrable_of_norm_le_one (hsec' _) fun y => (norm_hybridF G _ u _).le)
    (integrable_of_norm_le_one (hsec' _) fun y => (norm_hybridF G _ u _).le)]
  simp only [hybridF, inner_hybrid_update, zeroAt_update, Function.update_self]
  have hmt := slot_moments (W := W) (hr (tagGroup j)) lt
    (linVec (coefU u) (G ω) (slotSum (zeroAt j Λ₀) x) (tagGroup j)) (G ω)
    (coefU u (tagGroup j) (tagGroup j))
  have hmg := slot_moments (W := W) (hr (tagGroup j)) lg
    (linVec (coefU u) (G ω) (slotSum (zeroAt j Λ₀) x) (tagGroup j)) (G ω)
    (coefU u (tagGroup j) (tagGroup j))
  have hmatch := slot_moments_match (W := W) (hr (tagGroup j))
    (linVec (coefU u) (G ω) (slotSum (zeroAt j Λ₀) x) (tagGroup j)) (G ω)
    (coefU u (tagGroup j) (tagGroup j))
  have ht0 : 0 ≤ (Real.sqrt M)⁻¹ := by positivity
  have ht1 : (Real.sqrt M)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (Real.sqrt_pos.2 (by exact_mod_cast hM))]
    exact Real.one_le_sqrt.2 (by exact_mod_cast hM)
  exact enorm_integral_exp_sub_le (μ j) _ _ ht0 ht1 _ _ _ _ hmt.1 hmt.2.1 hmt.2.2.1
    hmg.1 hmg.2.1 hmg.2.2.1 (hmt.2.2.2.1.trans hmg.2.2.2.1.symm)
    ((hmt.2.2.2.2.1.trans hmatch.1).trans hmg.2.2.2.2.1.symm)
    ((hmt.2.2.2.2.2.trans hmatch.2).trans hmg.2.2.2.2.2.symm)

end Swap

end BlockBand.Critical.GlobalSource
