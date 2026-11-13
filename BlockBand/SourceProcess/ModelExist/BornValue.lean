module

public import BlockBand.SourceProcess.ModelExist.TransRep

/-!
# `BornRepresents` from the values at the birth times

`bVal e = Σ c_e 𝒢_{e}(θ_e)` is the value of the coordinate `e` of `G` when it is born.
`entry_sub_rep`: `G_e(t) − Σ c_e (𝒢_t − 𝒢_{t∧θ_e}) = 1{θ_e ≤ t} bVal e` (pure algebra).
`bornRepresents_of`: if for every `e` the function `1{θ_e ≤ t} bVal e − J_e(t)` is constant in
`t`, then `BornRepresents` holds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable {Ω : Type*} {c c' F : Type*} [Fintype c] [Fintype c'] [Fintype F]
  {𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ} {θ : c → Ω → ℝ≥0} {lam : c → Ω → c' → ℂ}
  {j : F → Matrix c c ℂ × Matrix c c ℂ} {β : F → Ω → ℝ}

/-- The value of the coordinate `e` at its birth time. -/
def bVal (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ) (θ : c → Ω → ℝ≥0)
    (lam : c → Ω → c' → ℂ) (e : Fin 2 × c × c) (ω : Ω) : ℂ :=
  ∑ x, ∑ x', bCoef lam e ω x x' * gramEntry (e.1, x, x') (𝒢 (max (θ e.2.1 ω) (θ e.2.2 ω)) ω)

omit [Fintype F] in
theorem entry_sub_rep (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) :
    gramEntry e (bornG 𝒢 θ lam t ω) - ∑ x, ∑ x', bCoef lam e ω x x' *
        (gramEntry (e.1, x, x') (𝒢 t ω) - gramEntry (e.1, x, x') (𝒢 (stopTime (bTime θ e ω) t) ω)) =
      if bTime θ e ω ≤ t then bVal 𝒢 θ lam e ω else 0 := by
  rw [gramEntry_bornG, ← Finset.sum_sub_distrib]
  by_cases h : bTime θ e ω ≤ t
  · have hs : stopTime (bTime θ e ω) t = max (θ e.2.1 ω) (θ e.2.2 ω) := by
      simp only [bTime, stopTime_coe]
      exact min_eq_right (WithTop.coe_le_coe.1 h)
    simp only [h, ↓reduceIte, bVal, hs, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    ring
  · have hs : stopTime (bTime θ e ω) t = t := stopTime_eq_self (not_le.1 h).le
    simp only [h, ↓reduceIte, hs, sub_self, mul_zero, zero_mul, Finset.sum_const_zero]

omit [Fintype c] in
theorem gramEntry_sub' (e : Fin 2 × c × c) (A B : Matrix c c ℂ × Matrix c c ℂ) :
    gramEntry e (A - B) = gramEntry e A - gramEntry e B := by
  simp only [gramEntry, Prod.fst_sub, Prod.snd_sub, Matrix.sub_apply]
  split_ifs <;> rfl

/-- **`BornRepresents` from the birth values.** -/
theorem bornRepresents_of {ω : Ω}
    (h : ∀ (e : Fin 2 × c × c) (t : ℝ≥0),
      (if bTime θ e ω ≤ t then bVal 𝒢 θ lam e ω else 0) - gramEntry e (bJ j β t ω) =
        (if bTime θ e ω ≤ 0 then bVal 𝒢 θ lam e ω else 0) - gramEntry e (bJ j β 0 ω)) :
    BornRepresents 𝒢 θ lam j β ω := by
  intro t e
  have h1 := entry_sub_rep (𝒢 := 𝒢) (θ := θ) (lam := lam) e t ω
  have h0 := entry_sub_rep (𝒢 := 𝒢) (θ := θ) (lam := lam) e 0 ω
  have hz : ∀ r : WithTop ℝ≥0, stopTime r 0 = 0 := fun r => le_antisymm (stopTime_le _ 0) zero_le
  simp only [hz, sub_self, mul_zero, Finset.sum_const_zero, sub_zero] at h0
  rw [gramEntry_sub', gramEntry_sub']
  linear_combination h1 - h0 + h e t

end BlockBand.SourceProcess.ModelExist
