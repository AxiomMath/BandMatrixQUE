module

public import BlockBand.Transmission.LawDuality.FddTilt
public import BlockBand.Transmission.LawDuality.DualityPrinciple

/-!
# Conditional duality between two positive times

Setting of `RatioDualityPrinciple`: a random finite measure process `μ` on `[0,1]`
under a probability `P`, measurable marginals, a.s. continuous paths on `(0,∞)`, ratio
martingale problem (`IsRatioMartingale D₀ E κ`), local mass bound, `κ` an absorption profile.
For a nonnegative bounded continuous `ψ` on `Fin m → FM[0,1]`, times `0 < u_l ≤ a₀ < t`, the past
test `Φ = ψ(μ_{u_1}, …, μ_{u_m})`, and every normalized realization of the dual deletion process
started at an interior `(x, y)` (**`integral_pastTest_mul_ratio`**):
`E[Φ F_{x,y}(μ_t)] = E'[E[Φ F_{Z_L}(μ_{a₀})] e^{−∫_0^L h(t−v)R_v dv}]`, `L = t − a₀`,
`F_{Z_L}` the full-level ratio (`ratioStop … ⊤`, `= 1` at level `0`).

Proof: if `E Φ = 0` both sides vanish. Otherwise tilt `P` to `(Φ/EΦ)·P` (`FddTilt`): it is a
probability measure, the forward increments after `a₀` keep the ratio drift
(`ratioIncFrom_tilt`), and the mass bound survives; then `ratio_eq_stripV_top_from` (the
strip argument under `RatioIncFrom`) at `a₀`, and multiply back by `EΦ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal BoundedContinuousFunction

variable {D0 E : ℝ} {κ : ℝ → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {m : ℕ} (ψ : (Fin m → FiniteMeasure unitInterval) →ᵇ ℝ)
  {u : Fin m → ℝ} {a0 t : ℝ}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}

/-- **Conditional duality, continuous paths.** -/
theorem integral_pastTest_mul_ratio_of_continuous (hκ : IsAbsorptionProfile κ)
    {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
    (hM : IsRatioMartingale D0 E κ P μ) (hmass : HasLocalMassBound P μ) (hψ : ∀ v, 0 ≤ ψ v)
    (ha0 : 0 < a0) (hu : ∀ l, 0 < u l ∧ u l ≤ a0) (hat : a0 < t)
    (hD : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hst : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i)
    (hxy : IsRatioParameter x y) :
    ∫ ω, pastTest ψ μ u ω * transmissionRatio x y (μ t ω) ∂P =
      ∫ ω', (∫ ω, pastTest ψ μ u ω * ratioStop (μ a0 ω) N X Y (fun _ => ⊤) (t - a0) ω' ∂P) *
        killFac (fun v => absorptionRate E κ (t - v)) N X Y (fun _ => ⊤) (t - a0) ω' ∂P' := by
  have := hD.prob
  set k : ℝ → ℝ := fun v => absorptionRate E κ (t - v) with hkdef
  obtain ⟨Kκ, hKκ⟩ := hκ.2.2
  have hκc : Continuous κ := hκ.1
  have hhc := DualBoundary.continuous_absorptionRate hκc E
  have hk : Continuous k := hhc.comp (continuous_const.sub continuous_id)
  have hh0 : ∀ u, 0 ≤ absorptionRate E κ u := fun u => DualBoundary.absorptionRate_nonneg hκ E u
  have hhC : ∀ u, |absorptionRate E κ u| ≤ DualBoundary.rateBound E Kκ := fun u => by
    rw [abs_of_nonneg (hh0 u)]; exact DualBoundary.absorptionRate_le hKκ E u
  have hk0 : ∀ v, 0 ≤ k v := fun v => hh0 _
  have hkC : ∀ v, k v ≤ DualBoundary.rateBound E Kκ := fun v => (le_abs_self _).trans (hhC _)
  have hΦm := measurable_pastTest ψ hmeas fun l => (hu l).1
  have hΦ0 : ∀ ω, 0 ≤ pastTest ψ μ u ω := fun ω => hψ _
  have hΦi : Integrable (pastTest ψ μ u) P :=
    Integrable.of_bound hΦm.aestronglyMeasurable ‖ψ‖ (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 ω)]; exact pastTest_le ψ μ u ω)
  obtain ⟨c, hcdef⟩ : ∃ c, ∫ ω, pastTest ψ μ u ω ∂P = c := ⟨_, rfl⟩
  rcases (hcdef ▸ integral_nonneg hΦ0 : 0 ≤ c).eq_or_lt with hc0 | hc
  · have hae : pastTest ψ μ u =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => hΦ0 ω) hΦi).1 (hcdef.trans hc0.symm)
    have hL : ∫ ω, pastTest ψ μ u ω * transmissionRatio x y (μ t ω) ∂P = 0 :=
      integral_eq_zero_of_ae (hae.mono fun ω h => by simp only [h, Pi.zero_apply, zero_mul])
    have hR : ∀ ω', ∫ ω, pastTest ψ μ u ω * ratioStop (μ a0 ω) N X Y (fun _ => ⊤) (t - a0) ω' ∂P
        = 0 := fun ω' =>
      integral_eq_zero_of_ae (hae.mono fun ω h => by simp only [h, Pi.zero_apply, zero_mul])
    simp only [hL, hR, zero_mul, integral_zero]
  · have := isProbabilityMeasure_tilt hΦm hΦ0 (pastTest_le ψ μ u) hc hcdef
    have key := ratio_eq_stripV_top_from (P := tiltMeasure P (pastTest ψ μ u) c) hD hpath hk hk0
      hmeas hcont ha0 hkC hκc hhC (fun v => rfl)
      (ratioIncFrom_tilt hmeas hM ψ hψ ha0 hu hc hcdef)
      (hasLocalMassBound_of_le_smul hmass (div_nonneg (norm_nonneg ψ) hc.le)
        (tiltMeasure_le hc (pastTest_le ψ μ u))) hxy hst hat
    unfold stripV at key
    rw [clampT_of_mem ⟨le_rfl, hat.le⟩, integral_tiltMeasure hΦm hΦ0 hc] at key
    simp_rw [integral_tiltMeasure hΦm hΦ0 hc, mul_assoc] at key
    rw [integral_const_mul] at key
    exact mul_left_cancel₀ (inv_ne_zero hc.ne') key

/-- **Conditional duality between two positive times** (a.s. continuous paths). -/
theorem integral_pastTest_mul_ratio (hκ : IsAbsorptionProfile κ)
    {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Ioi 0))
    (hM : IsRatioMartingale D0 E κ P μ) (hmass : HasLocalMassBound P μ) (hψ : ∀ v, 0 ≤ ψ v)
    (ha0 : 0 < a0) (hu : ∀ l, 0 < u l ∧ u l ≤ a0) (hat : a0 < t)
    (hD : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hst : ∀ ω, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i)
    (hxy : IsRatioParameter x y) :
    ∫ ω, pastTest ψ μ u ω * transmissionRatio x y (μ t ω) ∂P =
      ∫ ω', (∫ ω, pastTest ψ μ u ω * ratioStop (μ a0 ω) N X Y (fun _ => ⊤) (t - a0) ω' ∂P) *
        killFac (fun v => absorptionRate E κ (t - v)) N X Y (fun _ => ⊤) (t - a0) ω' ∂P' := by
  obtain ⟨μ', hmeas', hcont', hae⟩ := exists_continuous_version hmeas hcont
  have h := integral_pastTest_mul_ratio_of_continuous ψ hκ hmeas' hcont'
    (isRatioMartingale_congr hae hM) (hasLocalMassBound_congr hae hmass) hψ ha0 hu hat hD hpath
    hst hxy
  have e1 : ∫ ω, pastTest ψ μ u ω * transmissionRatio x y (μ t ω) ∂P =
      ∫ ω, pastTest ψ μ' u ω * transmissionRatio x y (μ' t ω) ∂P :=
    integral_congr_ae (hae.mono fun ω hω => by simp only [pastTest, hω])
  have e2 : ∀ ω', ∫ ω, pastTest ψ μ u ω * ratioStop (μ a0 ω) N X Y (fun _ => ⊤) (t - a0) ω' ∂P =
      ∫ ω, pastTest ψ μ' u ω * ratioStop (μ' a0 ω) N X Y (fun _ => ⊤) (t - a0) ω' ∂P := fun ω' =>
    integral_congr_ae (hae.mono fun ω hω => by simp only [pastTest, hω])
  rw [e1, h]
  refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
  simp only [e2]

end BlockBand.Transmission.LawDuality
