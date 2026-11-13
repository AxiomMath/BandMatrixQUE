module

public import BlockBand.Transmission.DualEntrance.FaceNoReturn

/-!
# Generic 1D entrance lemma, conclusion: positivity on `(0, τ]`

Setting of `IsEntranceFace Q 𝓖 z β α τ c K M B` on a filtered probability space `(Ω, Q, 𝓖)`, raw
filtration. Combining the good times (`exists_good_time`: good times `s_j ∈ (0, 1/(j+1))` with
`z_{s_j} > 0` a.s. on `{s_j ≤ τ}`) and the absence of return (`ae_noReturn` at each `s_j`) over
the countably many `j`:

* **`ae_pos`**: almost surely, `z_t > 0` for every `t ∈ (0, τ]` (instantaneous entrance and
  no return, simultaneously for all such `t`).

Also a deterministic tool on hitting times: **`le_of_le_hitLe`** — for a continuous path,
`V_u ≥ c` at every `u ∈ (0, hitLe V c]` (left limit).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- Before and at a positive hitting time of `{V ≤ c}`, a continuous path satisfies `V ≥ c`. -/
theorem le_of_le_hitLe {Ω' : Type*} {V : ℝ≥0 → Ω' → ℝ} {c : ℝ} {ω : Ω'}
    (hV : Continuous fun u => V u ω) {u : ℝ≥0} (hu0 : 0 < u)
    (hu : (u : WithTop ℝ≥0) ≤ hitLe V c ω) : c ≤ V u ω := by
  by_contra h
  have hev : ∀ᶠ v in 𝓝[<] u, V v ω < c ∧ v < u :=
    (((hV.tendsto u).eventually (gt_mem_nhds (not_le.1 h))).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin
  have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu0⟩
  obtain ⟨v, hv, hvu⟩ := hev.exists
  have := lt_hitLe ((WithTop.coe_lt_coe.2 hvu).trans_le hu)
  linarith

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

namespace IsEntranceFace

variable {z β : ℝ≥0 → Ω → Fin 1 → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
  {τ : Ω → WithTop ℝ≥0} {c K M B : ℝ} (hF : IsEntranceFace Q 𝓖 z β α τ c K M B)
include hF

/-- **Instantaneous entrance and no return**: almost surely `z_t > 0` for every
`t ∈ (0, τ]`. -/
theorem ae_pos [IsProbabilityMeasure Q] :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → (t : WithTop ℝ≥0) ≤ τ ω → 0 < z t ω 0 := by
  have h := fun j : ℕ => hF.exists_good_time (ε := 1 / ((j : ℝ) + 1)) (by positivity)
  choose s _ hsε hsae using h
  have hall : ∀ᵐ ω ∂Q, ∀ j, ((s j : WithTop ℝ≥0) ≤ τ ω → 0 < z (s j) ω 0) ∧
      (0 < z (s j) ω 0 → ∀ t : ℝ≥0, s j ≤ t → 0 < z t ω 0) := by
    rw [ae_all_iff]
    exact fun j => (hsae j).and (hF.ae_noReturn (s j))
  filter_upwards [hall] with ω hω t ht htτ
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
  have hst : s j ≤ t := by
    rw [← NNReal.coe_le_coe]; exact ((hsε j).trans hj).le
  exact (hω j).2 ((hω j).1 ((WithTop.coe_le_coe.2 hst).trans htτ)) t hst

end IsEntranceFace

end BlockBand.Transmission.DualEntrance
