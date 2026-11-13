module

public import BlockBand.SourceProcess.FullSourceGenerator.LimitFdd
public import BlockBand.SourceProcess.FullSourceGenerator.Interface
public import BlockBand.SourceProcess.FullSourceGenerator.LoadBound

/-!
# `WordLimitExists` from `TightClause`

**`wordLimitExists_of hT`**: `WordLimitExists` (Prokhorov over the countably many ordinary
words: joint critical limits `IsWordLimit` exist along subsequences) from `TightClause`.

The words are enumerated (`TraceWord nT nI` is countable); `X n a t = Tr w_a(⌊nt⌋)` for ordinary
`w_a`, `0` otherwise, under `growthPathLaw n b`. `TightClause` gives `OneTimeTight` (its first
clause at `t₁ = t`) and `Modulus` (its second clause at `t₁ = t₀`); `WordLim.exists_limit` gives
`ms`, `P` on `ℕ → ℂ` and the continuous versions `extPath`; `Z w = extPath (index of w)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {nT nI : ℕ}

/-- `TraceLetter → Option (Fin nT ⊕ Fin nI)`. -/
def letterCode : TraceLetter nT nI → Option (Fin nT ⊕ Fin nI)
  | .current => none
  | .tag a => some (.inl a)
  | .interval a => some (.inr a)

theorem letterCode_injective : Function.Injective (letterCode (nT := nT) (nI := nI)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [letterCode]

/-- `Separator → Fin 6`. -/
def sepCode : Separator → Fin 6
  | .id => 0
  | .proj => 1
  | .projS => 2
  | .sStarProj => 3
  | .projSProj => 4
  | .projSStarProj => 5

theorem sepCode_injective : Function.Injective sepCode := by
  intro x y h
  cases x <;> cases y <;> simp_all [sepCode]

theorem countable_traceWord : Countable (TraceWord nT nI) := by
  have : Countable (TraceLetter nT nI) := letterCode_injective.countable
  have : Countable Separator := sepCode_injective.countable
  infer_instance

open scoped Classical in
/-- The enumerated word processes (`0` for non-ordinary words). -/
def wordProc (b E : ℝ) (k : ℕ → Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (enum : ℕ → TraceWord nT nI) (n a : ℕ) (t : ℝ) (ω : GrowthPath n) : ℂ :=
  if IsOrdinaryWord (enum a) then wordValue b E (k n) q n ⌊(n : ℝ) * t⌋₊ ω (enum a) else 0

theorem wordProc_of_ord {b E : ℝ} {k : ℕ → Fin nT → ℕ} {q : Fin nI → ℝ → ℝ}
    {enum : ℕ → TraceWord nT nI} {n a : ℕ} (h : IsOrdinaryWord (enum a)) (t : ℝ)
    (ω : GrowthPath n) :
    wordProc b E k q enum n a t ω = wordValue b E (k n) q n ⌊(n : ℝ) * t⌋₊ ω (enum a) := by
  simp [wordProc, h]

theorem wordProc_of_not {b E : ℝ} {k : ℕ → Fin nT → ℕ} {q : Fin nI → ℝ → ℝ}
    {enum : ℕ → TraceWord nT nI} {n a : ℕ} (h : ¬ IsOrdinaryWord (enum a)) (t : ℝ)
    (ω : GrowthPath n) : wordProc b E k q enum n a t ω = 0 := by
  simp [wordProc, h]

/-- **`WordLimitExists` from `TightClause`.** -/
theorem wordLimitExists_of (hT : TightClause) : WordLimitExists := by
  intro b hb0 hb E hE1 hE2 t₀ ht₀ nT nI q hq k hk
  have := countable_traceWord (nT := nT) (nI := nI)
  obtain ⟨enum, henum⟩ := exists_surjective_nat (TraceWord nT nI)
  set X := wordProc b E k q enum
  have hX : WordLim.AEMeas t₀ (fun n => growthPathLaw n b) X := fun n a t _ => by
    by_cases h : IsOrdinaryWord (enum a)
    · rw [show X n a t = fun ω => wordValue b E (k n) q n ⌊(n : ℝ) * t⌋₊ ω (enum a) from
        funext (wordProc_of_ord h t)]
      exact (measurable_wordValue b E (k n) q _ (enum a)).aemeasurable
    · rw [show X n a t = fun _ => 0 from funext (wordProc_of_not h t)]
      exact aemeasurable_const
  have hOT : WordLim.OneTimeTight t₀ (fun n => growthPathLaw n b) X := by
    intro a t ht θ hθ
    by_cases h : IsOrdinaryWord (enum a)
    · obtain ⟨M, W₀, hM⟩ := (hT b hb0 hb E hE1 hE2 t₀ ht₀ nT nI q hq k hk (enum a) h t (t + 1)
        ht (by linarith)).1 θ hθ
      refine ⟨M, W₀, fun n hn => ?_⟩
      simp only [X, wordProc_of_ord h]
      exact hM n hn
    · refine ⟨0, 0, fun n _ => ?_⟩
      simp [X, wordProc_of_not h]
  have hMod : WordLim.Modulus t₀ (fun n => growthPathLaw n b) X := by
    intro a T η θ hη hθ
    by_cases h : IsOrdinaryWord (enum a) ∧ t₀ < T
    · obtain ⟨δ, hδ, W₀, hW⟩ := (hT b hb0 hb E hE1 hE2 t₀ ht₀ nT nI q hq k hk (enum a) h.1 t₀ T
        le_rfl h.2).2 η θ hη hθ
      refine ⟨δ, hδ, W₀, fun n hn => ?_⟩
      simp only [X, wordProc_of_ord h.1]
      exact hW n hn
    · refine ⟨1, one_pos, 0, fun n _ => ?_⟩
      have he : {ω : GrowthPath n | ∃ t ∈ Icc t₀ T, ∃ t' ∈ Icc t₀ T, |t - t'| ≤ 1 ∧
          η < ‖X n a t ω - X n a t' ω‖} = ∅ := by
        refine eq_empty_of_forall_notMem fun ω ⟨t, ht, t', ht', _, hlt⟩ => ?_
        by_cases ho : IsOrdinaryWord (enum a)
        · have hTt : T ≤ t₀ := not_lt.mp fun h' => h ⟨ho, h'⟩
          have e1 : t = t₀ := le_antisymm (ht.2.trans hTt) ht.1
          have e2 : t' = t₀ := le_antisymm (ht'.2.trans hTt) ht'.1
          rw [e1, e2, sub_self, norm_zero] at hlt
          exact absurd hlt (not_lt.mpr hη.le)
        · simp only [X, wordProc_of_not ho, sub_self, norm_zero] at hlt
          exact absurd hlt (not_lt.mpr hη.le)
      rw [he, measure_empty]; exact zero_le
  obtain ⟨ms, hms, P, hP, hmeas, hcont, hfdd⟩ := WordLim.exists_limit hX hOT hMod
  choose idx hidx using henum
  refine ⟨ℕ → ℂ, inferInstance, P, fun w t ω => WordLim.extPath t₀ (idx w) ω t,
    ⟨hP, fun w _ t ht => hmeas (idx w) t ht, fun w _ => hcont (idx w), ms, hms,
      fun m ws ts hws Ψ => ?_⟩⟩
  have h := hfdd m (fun l => idx (ws l)) ts (fun l => (hws l).2) Ψ
  have e : ∀ n, ∫ ω, Ψ (fun l => X (ms n) (idx (ws l)) (ts l) ω) ∂growthPathLaw (ms n) b =
      ∫ ω, Ψ (fun l => wordValue b E (k (ms n)) q (ms n) ⌊(ms n : ℝ) * ts l⌋₊ ω (ws l))
        ∂growthPathLaw (ms n) b := fun n => by
    congr 1; funext ω; congr 1; funext l
    have ho : IsOrdinaryWord (enum (idx (ws l))) := by rw [hidx]; exact (hws l).1
    simp only [X, wordProc_of_ord ho, hidx]
  simpa only [e] using h

end BlockBand.SourceProcess.FullSourceGenerator
