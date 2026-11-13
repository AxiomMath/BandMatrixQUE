module

public import BlockBand.SourceProcess.BornStopped.Pin
public import BlockBand.SourceProcess.BornUnique.Concat

/-!
# Agreement of a born solution with its birth-free part before the next birth

For a born Gram solution `G` with birth sum `J`, the process `tildeG = (G - J) + J(0)` agrees
with `G` up to a time `r` before which no birth occurs. Consequently the trace stopping times,
the stopped processes and the compensated processes of `G` and `tildeG` agree up to `r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornStopped

open MeasureTheory ProbabilityTheory
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornUnique
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

variable {Ω c F : Type*} [Fintype c] [DecidableEq c] [Fintype F]

/-- The birth-free part `G̃ = (G - J) + J(0)` of `G`, with `J = birthSum j β`. -/
def tildeG (j : F → GramState c) (β : Ω → F → ℝ) (G : ℝ≥0 → Ω → GramState c) (t : ℝ≥0)
    (ω : Ω) : GramState c :=
  G t ω - birthSum j (β ω) (t : ℝ) + birthSum j (β ω) ((0 : ℝ≥0) : ℝ)

omit [Fintype c] [DecidableEq c] in
theorem birthSum_eq_zero_of_le {j : F → GramState c} {x : F → ℝ} {r : ℝ≥0}
    (h : ∀ f, x f ≤ 0 ∨ (r : ℝ) < x f) {s : ℝ≥0} (hs : s ≤ r) :
    birthSum j x (s : ℝ) = birthSum j x ((0 : ℝ≥0) : ℝ) := by
  unfold birthSum
  refine Finset.sum_congr rfl fun f _ => ?_
  have hs' : (s : ℝ) ≤ r := by exact_mod_cast hs
  rcases h f with h1 | h1
  · have a : x f ≤ (s : ℝ) := h1.trans s.2
    have b : x f ≤ ((0 : ℝ≥0) : ℝ) := by simpa using h1
    simp only [a, b, ite_true]
  · have a : ¬ x f ≤ (s : ℝ) := by linarith
    have b : ¬ x f ≤ ((0 : ℝ≥0) : ℝ) := by simp only [NNReal.coe_zero]; linarith [r.2]
    simp only [a, b, ite_false]

omit [Fintype c] [DecidableEq c] in
theorem tildeG_eq {j : F → GramState c} {β : Ω → F → ℝ} {G : ℝ≥0 → Ω → GramState c} {ω : Ω}
    {r : ℝ≥0} (hω : ∀ f, β ω f ≤ 0 ∨ (r : ℝ) < β ω f) {s : ℝ≥0} (hs : s ≤ r) :
    tildeG j β G s ω = G s ω := by
  rw [tildeG, birthSum_eq_zero_of_le hω hs, sub_add_cancel]

omit [Fintype c] [DecidableEq c] in
theorem gramEntry_add (e : Fin 2 × c × c) (A B : GramState c) :
    gramEntry e (A + B) = gramEntry e A + gramEntry e B := by
  unfold gramEntry
  split_ifs <;> simp [Matrix.add_apply]

omit [Fintype c] [DecidableEq c] in
theorem setIntegral_tildeG_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : F → GramState c} {β : Ω → F → ℝ} {G : ℝ≥0 → Ω → GramState c} {ω : Ω}
    {r : ℝ≥0} (hω : ∀ f, β ω f ≤ 0 ∨ (r : ℝ) < β ω f) (φ : GramState c → E) {u : ℝ≥0}
    (hu : u ≤ r) :
    ∫ s in Set.Ioc (0 : ℝ) u, φ (G s.toNNReal ω) =
      ∫ s in Set.Ioc (0 : ℝ) u, φ (tildeG j β G s.toNNReal ω) := by
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have h1 : s.toNNReal ≤ r := by
    rw [Real.toNNReal_le_iff_le_coe]
    exact hs.2.trans (by exact_mod_cast hu)
  simp only [tildeG_eq hω h1]

theorem bornCompensated_eq {D0 : ℝ} {D : Matrix c c ℂ} {j : F → GramState c}
    {β : Ω → F → ℝ} {G : ℝ≥0 → Ω → GramState c} {ω : Ω} {r : ℝ≥0}
    (hω : ∀ f, β ω f ≤ 0 ∨ (r : ℝ) < β ω f) (e : Fin 2 × c × c) {u : ℝ≥0} (hu : u ≤ r) :
    bornCompensated D0 D G (fun t ω => birthSum j (β ω) (t : ℝ)) e u ω =
      gramCompensated D0 D (tildeG j β G) e u ω := by
  unfold bornCompensated gramCompensated
  rw [setIntegral_tildeG_eq hω (gramDriftEntry D0 D e) hu]
  simp only [tildeG, gramEntry_add]
  ring

/-- Two infima of times agree after `min` with `r` when the predicates agree up to `r`. -/
theorem min_iInf_eq {p q : ℝ≥0 → Prop} {r : ℝ≥0} (h : ∀ t ≤ r, p t ↔ q t) :
    min (⨅ (t : ℝ≥0) (_ : p t), (t : WithTop ℝ≥0)) (r : WithTop ℝ≥0) =
      min (⨅ (t : ℝ≥0) (_ : q t), (t : WithTop ℝ≥0)) (r : WithTop ℝ≥0) := by
  have key : ∀ {p q : ℝ≥0 → Prop}, (∀ t ≤ r, p t → q t) →
      min (⨅ (t : ℝ≥0) (_ : q t), (t : WithTop ℝ≥0)) (r : WithTop ℝ≥0) ≤
        min (⨅ (t : ℝ≥0) (_ : p t), (t : WithTop ℝ≥0)) (r : WithTop ℝ≥0) := by
    intro p q hpq
    refine le_min (le_iInf₂ fun t ht => ?_) (min_le_right _ _)
    by_cases htr : t ≤ r
    · exact (min_le_left _ _).trans (iInf₂_le t (hpq t htr ht))
    · exact (min_le_right _ _).trans (WithTop.coe_le_coe.2 (le_of_not_ge htr))
  exact le_antisymm (key fun t ht => (h t ht).2) (key fun t ht => (h t ht).1)

omit [DecidableEq c] in
theorem min_gramTraceStop_eq {j : F → GramState c} {β : Ω → F → ℝ}
    {G : ℝ≥0 → Ω → GramState c} {ω : Ω} {r : ℝ≥0} (hω : ∀ f, β ω f ≤ 0 ∨ (r : ℝ) < β ω f)
    (K : ℝ) :
    min (gramTraceStop G K ω) (r : WithTop ℝ≥0) =
      min (gramTraceStop (tildeG j β G) K ω) (r : WithTop ℝ≥0) :=
  min_iInf_eq fun t ht => by rw [tildeG_eq hω ht]

/-- `(min t τ).untopA ≤ r` when `τ ≤ r`. -/
theorem untopA_min_le {τ : WithTop ℝ≥0} {r : ℝ≥0} (h : τ ≤ r) (t : ℝ≥0) :
    (min (t : WithTop ℝ≥0) τ).untopA ≤ r := by
  induction τ with
  | top => exact absurd h (not_le.2 (WithTop.coe_lt_top r))
  | coe s =>
    rw [← WithTop.coe_min]
    show WithTop.untopD _ ((min t s : ℝ≥0) : WithTop ℝ≥0) ≤ r
    rw [WithTop.untopD_coe]
    exact (min_le_right _ _).trans (WithTop.coe_le_coe.1 h)

/-- Processes that agree up to `r`, stopped at times that agree after `min` with `r`. -/
theorem stopped_min_eq {E : Type*} {F₁ F₂ : ℝ≥0 → Ω → E} {τ₁ τ₂ : Ω → WithTop ℝ≥0}
    {r : ℝ≥0} {ω : Ω} (hF : ∀ u ≤ r, F₁ u ω = F₂ u ω)
    (hτ : min (τ₁ ω) (r : WithTop ℝ≥0) = min (τ₂ ω) (r : WithTop ℝ≥0)) (t : ℝ≥0) :
    stoppedProcess F₁ τ₁ (min t r) ω =
      stoppedProcess F₂ (fun ω => min (τ₂ ω) (r : WithTop ℝ≥0)) t ω := by
  have e : min ((min t r : ℝ≥0) : WithTop ℝ≥0) (τ₁ ω) =
      min (t : WithTop ℝ≥0) (min (τ₂ ω) (r : WithTop ℝ≥0)) := by
    rw [WithTop.coe_min, min_assoc, min_comm (r : WithTop ℝ≥0), hτ]
  simp only [stoppedProcess]
  rw [e]
  exact hF _ (untopA_min_le (min_le_right _ _) t)

end BlockBand.SourceProcess.BornStopped
