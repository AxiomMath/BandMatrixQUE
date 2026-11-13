module

public import BlockBand.SourceProcess.PhysApprox.IdentK.Statements
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramIBP

/-!
# Helpers for `KGBridge`

Integrability and path lemmas `intervalIntegrable_of_bddK`, `primitive_mul_eqK`, `path_smK`,
`path_bddK`, `path_rcK` (for any continuous path), the additivity `isTestedMartOff_addK` of
tested martingales off the births, and:

* `isTestedMartOff_of_testedK`: full tested increments give those off any set of times.
* `stronglyMeasurable_jointK`, `stronglyMeasurable_integral_gramJK`: joint measurability of
  `(r, ω) ↦ Λ(J_r, Z_r(ω))` and measurability of `ω ↦ ∫_0^t Λ(J_r, Z_r(ω))` for any measurable
  space on `Ω` (used with `pastSigma`), for a path `Z` continuous in time and the deterministic,
  piecewise-constant birth jumps `J = gramJ`.
* `ibp_algebraK`: the integration-by-parts algebra behind `genKG = genKY + D`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ENNReal

/-! ## Abstract tools -/

/-- Tested increments off a set of times `B` are additive: if `X` and `Y` have them, so does
`X + Y`. -/
theorem isTestedMartOff_addK {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {Q : Measure Ω}
    {obs : I → ℝ≥0 → Ω → ℂ} (hobs : ∀ i u, Measurable (obs i u)) {B : Set ℝ≥0}
    {X Y : ℝ≥0 → Ω → ℂ} (h1 : IsTestedMartOff B Q obs X) (h2 : IsTestedMartOff B Q obs Y) :
    IsTestedMartOff B Q obs (fun t ω => X t ω + Y t ω) := by
  refine ⟨fun t => (h1.1 t).add (h2.1 t), fun s t hst hs ht m i u hu huB φ => ?_⟩
  have hY : Measurable fun ω (l : Fin m) => obs (i l) (u l) ω :=
    Measurable.of_eval fun l => hobs _ _
  have hψ : AEStronglyMeasurable (fun ω => φ (fun l => obs (i l) (u l) ω)) Q :=
    (φ.continuous.measurable.comp hY).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂Q, ‖φ (fun l => obs (i l) (u l) ω)‖ ≤ ‖φ‖ :=
    Eventually.of_forall fun ω => φ.norm_coe_le_norm _
  have e : (fun ω => φ (fun l => obs (i l) (u l) ω) • (X t ω + Y t ω - (X s ω + Y s ω))) =
      fun ω => φ (fun l => obs (i l) (u l) ω) • (X t ω - X s ω) +
        φ (fun l => obs (i l) (u l) ω) • (Y t ω - Y s ω) := funext fun ω => by
    rw [← smul_add]; congr 1; ring
  have i1 : Integrable (fun ω => φ (fun l => obs (i l) (u l) ω) • (X t ω - X s ω)) Q :=
    ((h1.1 t).sub (h1.1 s)).bdd_smul _ hψ hb
  have i2 : Integrable (fun ω => φ (fun l => obs (i l) (u l) ω) • (Y t ω - Y s ω)) Q :=
    ((h2.1 t).sub (h2.1 s)).bdd_smul _ hψ hb
  rw [e, integral_add i1 i2, h1.2 s t hst hs ht m i u hu huB φ,
    h2.2 s t hst hs ht m i u hu huB φ, add_zero]

/-- Tested increments at all times give them off any set of times. -/
theorem isTestedMartOff_of_testedK {Ω : Type*} [MeasurableSpace Ω] {I : Type*}
    {Q : Measure Ω} {obs : I → ℝ≥0 → Ω → ℂ} {X : ℝ≥0 → Ω → ℂ} (B : Set ℝ≥0)
    (h : IsTestedMart Q obs X) : IsTestedMartOff B Q obs X :=
  ⟨h.1, fun s t hst _ _ m i u hu _ φ => h.2 s t hst m i u hu φ⟩

/-- A measurable function bounded on every half-line `(-∞, T]` is interval
integrable. -/
theorem intervalIntegrable_of_bddK {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ T : ℝ, ∃ C : ℝ, ∀ r, r ≤ T → ‖f r‖ ≤ C) (a c : ℝ) :
    IntervalIntegrable f volume a c := by
  obtain ⟨C, hC⟩ := hb (max a c)
  refine (intervalIntegrable_iff).2 (Measure.integrableOn_of_bounded (M := C)
    (lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top).ne hf ?_)
  exact (ae_restrict_mem measurableSet_uIoc).mono fun r hr => hC r hr.2

/-- The product rule for primitives of bounded right-continuous integrands. -/
theorem primitive_mul_eqK {f g : ℝ → ℂ} (hfm : StronglyMeasurable f)
    (hgm : StronglyMeasurable g)
    (hfb : ∀ T : ℝ, ∃ C : ℝ, ∀ r, r ≤ T → ‖f r‖ ≤ C)
    (hgb : ∀ T : ℝ, ∃ C : ℝ, ∀ r, r ≤ T → ‖g r‖ ≤ C)
    (hfr : ∀ x, 0 < x → ContinuousWithinAt f (Ici x) x)
    (hgr : ∀ x, 0 < x → ContinuousWithinAt g (Ici x) x) {v : ℝ} (hv : 0 ≤ v) :
    (∫ r in (0 : ℝ)..v, f r) * (∫ r in (0 : ℝ)..v, g r) =
      ∫ x in (0 : ℝ)..v, (f x * (∫ r in (0 : ℝ)..x, g r) + (∫ r in (0 : ℝ)..x, f r) * g x) := by
  have hfi := intervalIntegrable_of_bddK hfm.aestronglyMeasurable hfb
  have hgi := intervalIntegrable_of_bddK hgm.aestronglyMeasurable hgb
  have hd : ∀ {h : ℝ → ℂ}, StronglyMeasurable h → (∀ a c, IntervalIntegrable h volume a c) →
      (∀ x, 0 < x → ContinuousWithinAt h (Ici x) x) → ∀ x ∈ Ioo (min 0 v) (max 0 v),
        HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, h r) (h x) (Ioi x) x := by
    intro h hm hi hr x hx
    have hx0 : 0 < x := by rw [min_eq_left hv] at hx; exact hx.1
    exact (intervalIntegral.integral_hasDerivWithinAt_right (hi 0 x) (s := Ici x) (t := Ioi x)
      hm.aestronglyMeasurable.stronglyMeasurableAtFilter
      ((hr x hx0).mono Ioi_subset_Ici_self)).mono Ioi_subset_Ici_self
  have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (intervalIntegral.continuous_primitive hfi 0).continuousOn
    (intervalIntegral.continuous_primitive hgi 0).continuousOn (hd hfm hfi hfr) (hd hgm hgi hgr)
    (hfi 0 v) (hgi 0 v)
  rw [h]
  simp

/-- **The integration-by-parts algebra.** With `A = ∫β`, `L = ∫ℓ` (on `r > 0`), `A_t = ∫_0^t β`,
`L_t = ∫_0^t ℓ`: `(F_Y − A_t F_1) − ∫_0^t (λ_Y − Aℓ − βf) =
(F_Y − ∫_0^t λ_Y) + (∫_0^t β (f − L) − A_t (F_1 − L_t))`. -/
theorem ibp_algebraK {β ℓ lY f A L : ℝ → ℂ} (hβm : StronglyMeasurable β)
    (hℓm : StronglyMeasurable ℓ) (hlm : StronglyMeasurable lY) (hfc : Continuous f)
    (hβb : ∀ T : ℝ, ∃ C : ℝ, ∀ r, r ≤ T → ‖β r‖ ≤ C)
    (hℓb : ∀ T : ℝ, ∃ C : ℝ, ∀ r, r ≤ T → ‖ℓ r‖ ≤ C)
    (hlb : ∀ T : ℝ, ∃ C : ℝ, ∀ r, r ≤ T → ‖lY r‖ ≤ C)
    (hβr : ∀ x, 0 < x → ContinuousWithinAt β (Ici x) x)
    (hℓr : ∀ x, 0 < x → ContinuousWithinAt ℓ (Ici x) x)
    (hA : ∀ x, 0 < x → A x = ∫ r in (0 : ℝ)..x, β r)
    (hL : ∀ x, 0 < x → L x = ∫ r in (0 : ℝ)..x, ℓ r) {t : ℝ} (ht : 0 ≤ t) {At Lt : ℂ}
    (hAt : At = ∫ r in (0 : ℝ)..t, β r) (hLt : Lt = ∫ r in (0 : ℝ)..t, ℓ r) (FY F1 : ℂ) :
    (FY - At * F1) - ∫ r in Ioc (0 : ℝ) t, (lY r - A r * ℓ r - β r * f r) =
      (FY - ∫ r in Ioc (0 : ℝ) t, lY r) +
        ((∫ r in Ioc (0 : ℝ) t, β r * (f r - L r)) - At * (F1 - Lt)) := by
  have hβi := intervalIntegrable_of_bddK hβm.aestronglyMeasurable hβb
  have hℓi := intervalIntegrable_of_bddK hℓm.aestronglyMeasurable hℓb
  have hli := intervalIntegrable_of_bddK hlm.aestronglyMeasurable hlb
  have hPβ : Continuous fun x => ∫ r in (0 : ℝ)..x, β r :=
    intervalIntegral.continuous_primitive hβi 0
  have hPℓ : Continuous fun x => ∫ r in (0 : ℝ)..x, ℓ r :=
    intervalIntegral.continuous_primitive hℓi 0
  have e1 : ∫ r in Ioc (0 : ℝ) t, (lY r - A r * ℓ r - β r * f r) =
      ∫ r in (0 : ℝ)..t, (lY r - (∫ u in (0 : ℝ)..r, β u) * ℓ r - β r * f r) := by
    rw [intervalIntegral.integral_of_le ht]
    exact setIntegral_congr_fun measurableSet_Ioc fun r hr => by
      simp only [hA r hr.1]
  have e2 : ∫ r in Ioc (0 : ℝ) t, β r * (f r - L r) =
      ∫ r in (0 : ℝ)..t, β r * (f r - ∫ u in (0 : ℝ)..r, ℓ u) := by
    rw [intervalIntegral.integral_of_le ht]
    exact setIntegral_congr_fun measurableSet_Ioc fun r hr => by
      simp only [hL r hr.1]
  have e3 : ∫ r in Ioc (0 : ℝ) t, lY r = ∫ r in (0 : ℝ)..t, lY r :=
    (intervalIntegral.integral_of_le ht).symm
  have i1 : IntervalIntegrable (fun r => (∫ u in (0 : ℝ)..r, β u) * ℓ r) volume 0 t :=
    (hℓi 0 t).continuousOn_mul hPβ.continuousOn
  have i2 : IntervalIntegrable (fun r => β r * f r) volume 0 t :=
    (hβi 0 t).mul_continuousOn hfc.continuousOn
  have i3 : IntervalIntegrable (fun r => β r * ∫ u in (0 : ℝ)..r, ℓ u) volume 0 t :=
    (hβi 0 t).mul_continuousOn hPℓ.continuousOn
  have e4 : ∫ r in (0 : ℝ)..t, β r * (f r - ∫ u in (0 : ℝ)..r, ℓ u) =
      (∫ r in (0 : ℝ)..t, β r * f r) - ∫ r in (0 : ℝ)..t, β r * ∫ u in (0 : ℝ)..r, ℓ u := by
    simp only [mul_sub]
    exact intervalIntegral.integral_sub i2 i3
  have hpm := primitive_mul_eqK hβm hℓm hβb hℓb hβr hℓr ht
  rw [intervalIntegral.integral_add i3 i1] at hpm
  rw [e1, e2, e3, e4, intervalIntegral.integral_sub ((hli 0 t).sub i1) i2,
    intervalIntegral.integral_sub (hli 0 t) i1, hAt, hLt]
  linear_combination (-1 : ℂ) * hpm

/-! ## Paths along the births -/

variable {K np : ℕ}

section PathK

variable {b s : ℝ} {τ m : Fin np → ℝ} {𝒵 : Type*} [TopologicalSpace 𝒵] {Zp : ℝ≥0 → 𝒵}
  (hZ : Continuous Zp) {Λ : GSt K np × 𝒵 → ℂ} (hΛ : Continuous Λ)
include hZ hΛ

/-- `r ↦ Λ(J_r, Z_r)` is strongly measurable for any continuous path `Z`. -/
theorem path_smK [TopologicalSpace.PseudoMetrizableSpace 𝒵] :
    StronglyMeasurable fun r : ℝ => Λ (gramJ b s τ m r.toNNReal, Zp r.toNNReal) :=
  hΛ.comp_stronglyMeasurable ((stronglyMeasurable_gramJ_comp b s τ m).prodMk
    (hZ.comp continuous_real_toNNReal).stronglyMeasurable)

/-- `r ↦ Λ(J_r, Z_r)` is bounded on every half-line `(-∞, T]`. -/
theorem path_bddK (T : ℝ) : ∃ C : ℝ, ∀ r : ℝ, r ≤ T →
    ‖Λ (gramJ b s τ m r.toNNReal, Zp r.toNNReal)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_finite_compact hΛ (finite_range_gramJ (K := K) b s τ m)
    ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T.toNNReal)).image hZ)
  exact ⟨C, fun r hr => hC _ ⟨_, rfl⟩ _ ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hr⟩,
    rfl⟩⟩

/-- `r ↦ Λ(J_r, Z_r)` is right-continuous. -/
theorem path_rcK (x : ℝ) : ContinuousWithinAt
    (fun r : ℝ => Λ (gramJ b s τ m r.toNNReal, Zp r.toNNReal)) (Ici x) x := by
  have hT : Tendsto Real.toNNReal (𝓝[≥] x) (𝓝[≥] x.toNNReal) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_real_toNNReal.tendsto x).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun r hr => Real.toNNReal_le_toNNReal hr⟩
  have hJ : ∀ᶠ r in 𝓝[≥] x, gramJ (K := K) b s τ m r.toNNReal = gramJ b s τ m x.toNNReal :=
    hT.eventually (eventually_gramJ_eq x.toNNReal)
  have hc : ContinuousWithinAt
      (fun r : ℝ => Λ (gramJ b s τ m x.toNNReal, Zp r.toNNReal)) (Ici x) x :=
    (hΛ.comp (continuous_const.prodMk (hZ.comp continuous_real_toNNReal))).continuousWithinAt
  exact hc.congr_of_eventuallyEq (hJ.mono fun r hr => by simp only [hr]) rfl

end PathK

/-! ## Measurability of integrals along the births -/

section MeasK

variable {b s : ℝ} {τ m : Fin np → ℝ} {Ω : Type*} {𝒵 : Type*} [TopologicalSpace 𝒵]
  [TopologicalSpace.PseudoMetrizableSpace 𝒵] {Λ : GSt K np × 𝒵 → ℂ} {Z : ℝ≥0 → Ω → 𝒵}

/-- **Joint measurability** of `(r, ω) ↦ Λ(J_r, Z_r(ω))`, for `Z` continuous in time and
measurable for a measurable space `mΩ` (any one, e.g. a past σ-algebra). -/
theorem stronglyMeasurable_jointK [mΩ : MeasurableSpace Ω] (hΛ : Continuous Λ)
    (hZc : ∀ ω, Continuous fun u => Z u ω) (hZm : ∀ u, StronglyMeasurable (Z u)) :
    StronglyMeasurable fun p : ℝ × Ω => Λ (gramJ b s τ m p.1.toNNReal, Z p.1.toNNReal p.2) := by
  have h : StronglyMeasurable (Function.uncurry fun (r : ℝ) ω => Z r.toNNReal ω) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun ω => (hZc ω).comp continuous_real_toNNReal) fun r => hZm _
  exact hΛ.comp_stronglyMeasurable
    (((stronglyMeasurable_gramJ_comp b s τ m).comp_measurable measurable_fst).prodMk h)

/-- **Measurability of a time integral along the births**: `ω ↦ ∫_0^t Λ(J_r, Z_r(ω))` is
`mΩ`-measurable when `Z_u` is `mΩ`-measurable for `u ≤ t`. -/
theorem stronglyMeasurable_integral_gramJK [mΩ : MeasurableSpace Ω] (hΛ : Continuous Λ)
    (hZc : ∀ ω, Continuous fun u => Z u ω) (t : ℝ≥0)
    (hZm : ∀ u, u ≤ t → StronglyMeasurable (Z u)) :
    StronglyMeasurable fun ω =>
      ∫ r in Ioc (0 : ℝ) t, Λ (gramJ b s τ m r.toNNReal, Z r.toNNReal ω) := by
  set Z' : ℝ≥0 → Ω → 𝒵 := fun u ω => Z (min u t) ω with hZ'
  have hj := stronglyMeasurable_jointK (b := b) (s := s) (τ := τ) (m := m) hΛ (Z := Z')
    (fun ω => (hZc ω).comp (continuous_id.min continuous_const))
    (fun u => hZm _ (min_le_right _ _))
  have hint := (hj.comp_measurable measurable_swap).integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) t))
  have e : (fun ω => ∫ r in Ioc (0 : ℝ) t, Λ (gramJ b s τ m r.toNNReal, Z r.toNNReal ω)) =
      fun ω => ∫ r in Ioc (0 : ℝ) t, Λ (gramJ b s τ m r.toNNReal, Z' r.toNNReal ω) :=
    funext fun ω => setIntegral_congr_fun measurableSet_Ioc fun r hr => by
      have h : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
      simp only [hZ', min_eq_left h]
  rw [e]
  exact hint

end MeasK

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK
