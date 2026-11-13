module

public import BlockBand.Transmission.Generator.MeanLimit

/-!
# `meanConductance` along a moving energy

`meanConductance_along hLU hD`: every `IsPowerTraceLimitAlong` limit has
`∫⁻ |P_1(t)| ≤ 2/(D₀(E) t)`, `t > 0`. Proof: `ode_compare` on `[s, t]` gives
`E P_1(t) ≤ 2/(D₀(t-s))`; let `s = t/(N+2) ↓ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology ProbabilityTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

theorem meanConductance_along (hLU : TransmissionLengthUniformContract) (hD : PowerDriftSummable)
    {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ}
    {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Pk : ℕ → ℝ → Ω → ℝ} (h : IsPowerTraceLimitAlong b e P Pk) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ‖Pk 1 t ω‖ₑ ∂P ≤ ENNReal.ofReal (2 / (transportD0 b E * t)) := by
  have := h.prob
  obtain ⟨σ, hσm, hσ⟩ := h.fdd
  have hS : LimitSetup b e P Pk σ := ⟨h.prob, h.measurable, hσm.tendsto_atTop, hσ⟩
  have hDpos := transportD0_pos hb0 hE1 hE2
  set y : ℝ → ℝ := fun u => ∫ ω, Pk 1 u ω ∂P
  set q : ℝ → ℝ := fun u => ∫ ω, Pk 1 u ω ^ 2 ∂P
  have hbound : ∀ s, 0 < s → s < t → y t ≤ 2 / (transportD0 b E * (t - s)) := by
    intro s hs hst
    obtain ⟨C, hC0, hC⟩ := limit_sq_bound_unif hLU hb0 hb hE1 hE2 he hS le_rfl hs (t := t)
    have hmem : ∀ u ∈ Set.Icc s t, Integrable (fun ω => Pk 1 u ω ^ 2) P ∧
        Integrable (Pk 1 u) P ∧ ∫ ω, Pk 1 u ω ^ 2 ∂P ≤ max C 0 := fun u hu =>
      sq_integrable_of (h.measurable 1 le_rfl u (lt_of_lt_of_le hs hu.1)).aestronglyMeasurable
        (hC u hu)
    refine ode_compare (q := q) (C := max C 0) hDpos hst ?_ ?_ ?_ ?_ ?_
    · intro u hu
      exact integral_nonneg_of_ae (limit_nonneg hb hE1 hE2 he hS le_rfl (lt_of_lt_of_le hs hu.1))
    · intro a c ha hac _
      exact (mean_identity hLU hD hb0 hb hE1 hE2 he h hS (lt_of_lt_of_le hs ha) hac).1
    · intro a c ha hac _
      exact (mean_identity hLU hD hb0 hb hE1 hE2 he h hS (lt_of_lt_of_le hs ha) hac).2
    · intro u hu
      obtain ⟨h2, h1, -⟩ := hmem u hu
      have hL : MemLp (Pk 1 u) 2 P :=
        (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).mpr h2
      have hv := variance_nonneg (Pk 1 u) P
      rw [variance_eq_sub hL] at hv
      simp only [y, q]
      have : P[Pk 1 u ^ 2] = ∫ ω, Pk 1 u ω ^ 2 ∂P := rfl
      linarith
    · intro u hu; exact (hmem u hu).2.2
  -- `s = t/(N+2) ↓ 0`
  have hlim : Tendsto (fun N : ℕ => 2 / (transportD0 b E * (t - t / ((N : ℝ) + 2)))) atTop
      (𝓝 (2 / (transportD0 b E * t))) := by
    have h0 : Tendsto (fun N : ℕ => t / ((N : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun N : ℕ => transportD0 b E * (t - t / ((N : ℝ) + 2))) atTop
        (𝓝 (transportD0 b E * t)) := by
      simpa using (tendsto_const_nhds.sub h0).const_mul (transportD0 b E)
    exact (tendsto_const_nhds (x := (2 : ℝ))).div h1 (by positivity)
  have hyt : y t ≤ 2 / (transportD0 b E * t) := by
    refine ge_of_tendsto' hlim fun N => hbound _ (by positivity) ?_
    have : (1 : ℝ) < (N : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  -- convert to the `lintegral`
  obtain ⟨Ct, -, hCt⟩ := limit_sq_bound hLU hb0 hb hE1 hE2 he hS le_rfl ht
  have hint := (sq_integrable_of (h.measurable 1 le_rfl t ht).aestronglyMeasurable hCt).2.1
  have hnn := limit_nonneg hb hE1 hE2 he hS le_rfl ht
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)] at hyt
  refine le_trans (le_of_eq ?_) hyt
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine lintegral_congr_ae (hnn.mono fun ω hω => ?_)
  show ‖Pk 1 t ω‖ₑ = ENNReal.ofReal (Pk 1 t ω)
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]

end BlockBand.Transmission.Generator
