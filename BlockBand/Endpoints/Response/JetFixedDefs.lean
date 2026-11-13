module

public import BlockBand.Endpoints.Response.ClockEntranceLayerDefs

/-!
# The one-port jet contraction in fixed-moment form

This file states `OnePortJetContractionFixed`, the one-port jet contraction (c) in which the
fluctuation moment bound is required only for each fixed order `r`, with constants depending on
`r`.

* `onePortJetContractionFixed_of_onePortJetContraction`: the fixed form is weaker than
  `OnePortJetContraction`.
* `jfx_two`: the `r = 2` case with one constant for the contraction and the `L²` bound, the
  form used by `cel_weighted_det` and `rhc_weighted_det`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers

/-- The one-port jet contraction (c) in fixed-moment form. Quantifiers: `b ∈ (0, 1/2)`, a bulk
energy `E ∈ (-2, 2)` and a stationary jet `s` at `E`; then
`0 ≤ ρ < 1`, `C ≥ 0`, a jet radius `d > 0`, a width threshold `W₀`, and moment data
`Cr : ℝ → ℝ`, `Wr : ℝ → ℕ` (the constant and threshold of the order-`r` moment), all chosen
before `W` and `X`. For every `W ≥ W₀` and every deterministic passive old input `X` in the jet
domain `cel_InJetDomain b E s d X` there is one fluctuation `ξ₊` (a function of the fresh
one-port layer `ν ~ freshLaw W b`, chosen before the moment order) with
* `δ_{0,+} ≤ ρδ₀ + C/W² + |ξ₊|` for `freshLaw`-a.e. `ν`, where
  `δ_{0,+} = cec_freshJet0 b E X ν = ‖W⁻¹ Tr 𝒢_{port,port}(X, ν) - a‖`;
* for every fixed `r ≥ 1` and `W ≥ Wr r`: `‖ξ₊‖_{L^r(ν)} ≤ Cr r / W`. -/
def OnePortJetContractionFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℂ, IsStationaryJet b E s →
    ∃ (ρ C d : ℝ) (W₀ : ℕ) (Cr : ℝ → ℝ) (Wr : ℝ → ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧ 0 < d ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
        ∃ ξ : LayerSample W .oneBlockOnePort → ℝ, AEStronglyMeasurable ξ (freshLaw W b) ∧
          (∀ᵐ ν ∂freshLaw W b,
            cec_freshJet0 b E X ν ≤ ρ * jetDistance0 b E X + C / (W : ℝ) ^ 2 + |ξ ν|) ∧
          ∀ r : ℝ, 1 ≤ r → Wr r ≤ W →
            eLpNorm ξ (ENNReal.ofReal r) (freshLaw W b) ≤ ENNReal.ofReal (Cr r / W)

/-- The fixed-moment form is weaker than `OnePortJetContraction`: take `Cr r = C√r` and
`Wr r = max W₀ ⌈r/a⌉₊`, so that `W ≥ Wr r` gives `r ≤ aW`. -/
theorem onePortJetContractionFixed_of_onePortJetContraction (hc : OnePortJetContraction) :
    OnePortJetContractionFixed := by
  intro b hb0 hb' E hE hE' s hs
  obtain ⟨ρ, C, a, d, W₀, hρ0, hρ1, hC, ha, hd, hW⟩ := hc b hb0 hb' E hE hE' s hs
  refine ⟨ρ, C, d, W₀, fun r => C * Real.sqrt r, fun r => max W₀ ⌈r / a⌉₊, hρ0, hρ1, hC, hd,
    fun W hW0 X hX => ?_⟩
  obtain ⟨ξ, hξm, hξ, hξr⟩ := hW W hW0 X hX
  refine ⟨ξ, hξm, hξ, fun r hr hWr => hξr r hr ?_⟩
  have h1 : (⌈r / a⌉₊ : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hWr
  have h2 : r / a ≤ W := (Nat.le_ceil _).trans h1
  rwa [div_le_iff₀ ha, mul_comm] at h2

/-- The `r = 2` case with one constant (the form used by `cel_weighted_det` and
`rhc_weighted_det`): from `OnePortJetContractionFixed`, at `b, E, s`, there are `0 ≤ ρ < 1`,
`Cc ≥ 0`, `d > 0`, `W₀ ≥ 1` such that for `W ≥ W₀` and `X` in the jet domain, a fluctuation `ξ`
satisfies the a.s. contraction with `Cc` and `‖ξ‖_{L²(ν)} ≤ Cc√2/W`. The constant is
`Cc = max C (max (Cr 2) 0 / √2)` and the threshold `max (max W₀ (Wr 2)) 1`. -/
theorem jfx_two (hc : OnePortJetContractionFixed) {b : ℝ} (hb0 : 0 < b) (hb' : b < 1 / 2)
    {E : ℝ} (hE : -2 < E) (hE' : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) :
    ∃ (ρ Cc d : ℝ) (W₀ : ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ Cc ∧ 0 < d ∧ 1 ≤ W₀ ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, cel_InJetDomain b E s d X →
        ∃ ξ : LayerSample W .oneBlockOnePort → ℝ, AEStronglyMeasurable ξ (freshLaw W b) ∧
          (∀ᵐ ν ∂freshLaw W b,
            cec_freshJet0 b E X ν ≤ ρ * jetDistance0 b E X + Cc / (W : ℝ) ^ 2 + |ξ ν|) ∧
          eLpNorm ξ 2 (freshLaw W b) ≤ ENNReal.ofReal (Cc * Real.sqrt 2 / W) := by
  obtain ⟨ρ, C, d, W₀, Cr, Wr, hρ0, hρ1, hC, hd, hW⟩ := hc b hb0 hb' E hE hE' s hs
  set Cc := max C (max (Cr 2) 0 / Real.sqrt 2) with hCcdef
  have hCc : 0 ≤ Cc := le_trans hC (le_max_left _ _)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  refine ⟨ρ, Cc, d, max (max W₀ (Wr 2)) 1, hρ0, hρ1, hCc, hd, le_max_right _ _,
    fun W hW0 X hX => ?_⟩
  obtain ⟨ξ, hξm, hξ, hξr⟩ := hW W (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW0)
    X hX
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  refine ⟨ξ, hξm, ?_, ?_⟩
  · filter_upwards [hξ] with ν hν
    have : C / (W : ℝ) ^ 2 ≤ Cc / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) hW2
    linarith
  · have h2 := hξr 2 (by norm_num)
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW0)
    rw [ENNReal.ofReal_ofNat] at h2
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg W)
    have e : max (Cr 2) 0 = max (Cr 2) 0 / Real.sqrt 2 * Real.sqrt 2 := by
      field_simp
    calc Cr 2 ≤ max (Cr 2) 0 := le_max_left _ _
      _ = max (Cr 2) 0 / Real.sqrt 2 * Real.sqrt 2 := e
      _ ≤ Cc * Real.sqrt 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) hs2.le

end BlockBand.Endpoints
