module

public import BlockBand.SourceProcess.FullSourceGenerator.LimTools
public import BlockBand.SourceProcess.FullSourceGenerator.WordLimit
public import BlockBand.SourceProcess.FullSourceGenerator.GenCyl

/-!
# The limit side: versions, slots, re-indexed fdd

* `contSet`: a measurable full-measure set on which *all* ordinary paths are continuous
  (countably many words, `countable_traceWord`); `ver P Z t₀ Ψ`: the version of `u ↦ Ψ(Z_u)`,
  clamped to `[t₀,∞)` and zero off `contSet`; continuous in `u` for every `ω`, jointly
  measurable (`measurable_uncurry_ver`), `= Ψ(Z_u)` on `contSet` for `u ≥ t₀` and ordinary `Ψ`
  (`ver_eq`) — `limit_version` with words in place of powers;
* `slotW`, `slotT`, `slotG`: the finite vector (test words at their times, variables of `Ψ` at
  `u`) and the continuous functional `x ↦ φ(x_test)Ψ(x_vars)` (`slotG_apply`);
* `fdd_fintype`: the fdd clause of `IsWordLimit` for a finite index type.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.GenLim

open MeasureTheory Filter Topology MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal

variable {nT nI : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-!
### A jointly measurable, everywhere continuous version on `[t₀, ∞)`
-/

open Classical in
/-- The ordinary coordinates of `Z` at time `u` (non-ordinary words set to `0`). -/
def ordCut (Z : TraceWord nT nI → ℝ → Ω → ℂ) (u : ℝ) (ω : Ω) : TraceWord nT nI → ℂ :=
  fun w => if IsOrdinaryWord w then Z w u ω else 0

/-- A measurable full-measure set on which every ordinary path is continuous on `[t₀,∞)`. -/
def contSet (P : Measure Ω) (Z : TraceWord nT nI → ℝ → Ω → ℂ) (t₀ : ℝ) : Set Ω :=
  (toMeasurable P {ω | ¬ ∀ w : TraceWord nT nI, IsOrdinaryWord w →
    ContinuousOn (fun t => Z w t ω) (Set.Ici t₀)})ᶜ

variable {P : Measure Ω} {Z : TraceWord nT nI → ℝ → Ω → ℂ} {t₀ : ℝ}

theorem measurableSet_contSet : MeasurableSet (contSet P Z t₀) :=
  (measurableSet_toMeasurable _ _).compl

theorem ae_contSet
    (hc : ∀ w, IsOrdinaryWord w → ∀ᵐ ω ∂P, ContinuousOn (fun t => Z w t ω) (Set.Ici t₀)) :
    ∀ᵐ ω ∂P, ω ∈ contSet P Z t₀ := by
  have := countable_traceWord (nT := nT) (nI := nI)
  have hall : ∀ᵐ ω ∂P, ∀ w : TraceWord nT nI, IsOrdinaryWord w →
      ContinuousOn (fun t => Z w t ω) (Set.Ici t₀) := by
    refine ae_all_iff.mpr fun w => ?_
    by_cases hw : IsOrdinaryWord w
    · exact (hc w hw).mono fun ω h _ => h
    · exact Eventually.of_forall fun ω h => absurd h hw
  rw [ae_iff]
  simp only [contSet, Set.mem_compl_iff, not_not, Set.ofPred_mem_eq]
  rw [measure_toMeasurable]; exact ae_iff.mp hall

theorem continuousOn_of_mem_contSet {ω : Ω} (hω : ω ∈ contSet P Z t₀) {w : TraceWord nT nI}
    (hw : IsOrdinaryWord w) : ContinuousOn (fun t => Z w t ω) (Set.Ici t₀) := by
  by_contra hc
  exact hω (subset_toMeasurable _ _ fun h => hc (h w hw))

/-- The version of `u ↦ Ψ(Z_u)`: clamped to `[t₀,∞)`, zero off `contSet`. -/
def ver (P : Measure Ω) (Z : TraceWord nT nI → ℝ → Ω → ℂ) (t₀ : ℝ) (Ψ : TracePoly nT nI)
    (u : ℝ) (ω : Ω) : ℂ :=
  (contSet P Z t₀).indicator (fun ω => eval (ordCut Z (max t₀ u) ω) Ψ) ω

theorem continuous_ver (Ψ : TracePoly nT nI) (ω : Ω) : Continuous fun u => ver P Z t₀ Ψ u ω := by
  by_cases hω : ω ∈ contSet P Z t₀
  · simp only [ver, Set.indicator_of_mem hω]
    refine continuous_eval_of fun w _ => ?_
    simp only [ordCut]
    split_ifs with hw
    · exact (continuousOn_of_mem_contSet hω hw).comp_continuous
        (continuous_const.max continuous_id) fun u => Set.mem_Ici.mpr (le_max_left _ _)
    · exact continuous_const
  · simp only [ver, Set.indicator_of_notMem hω]; exact continuous_const

theorem measurable_ver (hm : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t))
    (Ψ : TracePoly nT nI) (u : ℝ) : Measurable (ver P Z t₀ Ψ u) := by
  refine Measurable.indicator (measurable_eval_of fun w _ => ?_) measurableSet_contSet
  simp only [ordCut]
  split_ifs with hw
  · exact hm w hw _ (le_max_left _ _)
  · exact measurable_const

theorem measurable_uncurry_ver (hm : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t))
    (Ψ : TracePoly nT nI) : Measurable (Function.uncurry (ver P Z t₀ Ψ)) :=
  measurable_uncurry_of_continuous_of_measurable (continuous_ver Ψ) (measurable_ver hm Ψ)

theorem ver_eq {Ψ : TracePoly nT nI} (hΨ : IsOrdinaryPoly Ψ) {u : ℝ} (hu : t₀ ≤ u) {ω : Ω}
    (hω : ω ∈ contSet P Z t₀) : ver P Z t₀ Ψ u ω = eval (fun w => Z w u ω) Ψ := by
  simp only [ver, Set.indicator_of_mem hω, max_eq_right hu]
  exact eval_congr_vars fun w hw => by simp [ordCut, hΨ w hw]

theorem measurable_evalZ (hm : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t))
    {Ψ : TracePoly nT nI} (hΨ : IsOrdinaryPoly Ψ) {u : ℝ} (hu : t₀ ≤ u) :
    Measurable fun ω => eval (fun w => Z w u ω) Ψ :=
  measurable_eval_of fun w hw => hm w (hΨ w hw) u hu

/-!
### Slots: a cylinder test times a polynomial at one time
-/

/-- The slot words: those of the test, then the variables of `Ψ`. -/
def slotW {m : ℕ} (ws : Fin m → TraceWord nT nI) (Ψ : TracePoly nT nI) :
    Fin m ⊕ Ψ.vars → TraceWord nT nI :=
  Sum.elim ws Subtype.val

/-- The slot times: those of the test, then `u`. -/
def slotT {m : ℕ} (us : Fin m → ℝ) (Ψ : TracePoly nT nI) (u : ℝ) : Fin m ⊕ Ψ.vars → ℝ :=
  Sum.elim us fun _ => u

open Classical in
/-- `x ↦ φ(x_test) Ψ(x_vars)`. -/
def slotG {m : ℕ} (φ : BoundedContinuousFunction (Fin m → ℂ) ℝ) (Ψ : TracePoly nT nI)
    (x : Fin m ⊕ Ψ.vars → ℂ) : ℂ :=
  (φ (fun l => x (Sum.inl l)) : ℂ) *
    eval (fun w => if h : w ∈ Ψ.vars then x (Sum.inr ⟨w, h⟩) else 0) Ψ

theorem continuous_slotG {m : ℕ} (φ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    (Ψ : TracePoly nT nI) : Continuous (slotG φ Ψ) := by
  classical
  unfold slotG
  refine (Complex.continuous_ofReal.comp (φ.continuous.comp
    (continuous_pi fun l => continuous_apply _))).mul
    ((continuous_eval Ψ).comp (continuous_pi fun w => ?_))
  by_cases h : w ∈ Ψ.vars
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

theorem slotG_apply {m : ℕ} (φ : BoundedContinuousFunction (Fin m → ℂ) ℝ)
    (Ψ : TracePoly nT nI) (ws : Fin m → TraceWord nT nI) (us : Fin m → ℝ) (u : ℝ)
    (V : TraceWord nT nI → ℝ → ℂ) :
    slotG φ Ψ (fun i => V (slotW ws Ψ i) (slotT us Ψ u i)) =
      (φ (fun l => V (ws l) (us l)) : ℂ) * eval (fun w => V w u) Ψ := by
  unfold slotG
  congr 1
  exact eval_congr_vars fun w hw => by simp [hw, slotW, slotT]

theorem slot_ord {m : ℕ} {ws : Fin m → TraceWord nT nI} {us : Fin m → ℝ}
    (hws : ∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ us l) {Ψ : TracePoly nT nI}
    (hΨ : IsOrdinaryPoly Ψ) {u : ℝ} (hu : t₀ ≤ u) :
    ∀ i, IsOrdinaryWord (slotW ws Ψ i) ∧ t₀ ≤ slotT us Ψ u i := by
  rintro (l | ⟨w, hw⟩)
  · exact hws l
  · exact ⟨hΨ w hw, hu⟩

/-!
### Re-indexing the fdd by a finite type
-/

theorem fdd_fintype {b E : ℝ} {k : ℕ → Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {σ : ℕ → ℕ}
    (hfdd : ∀ (m : ℕ) (ws : Fin m → TraceWord nT nI) (ts : Fin m → ℝ),
      (∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ ts l) → ∀ Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
        Tendsto (fun n => ∫ ω, Ψ (fun l =>
          wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * ts l⌋₊ ω (ws l)) ∂growthPathLaw (σ n) b)
        atTop (𝓝 (∫ ω, Ψ (fun l => Z (ws l) (ts l) ω) ∂P)))
    {ι : Type*} [Fintype ι] (ws : ι → TraceWord nT nI) (ts : ι → ℝ)
    (h : ∀ i, IsOrdinaryWord (ws i) ∧ t₀ ≤ ts i) (Φ : BoundedContinuousFunction (ι → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, Φ (fun i =>
      wordValue b E (k (σ n)) q (σ n) ⌊(σ n : ℝ) * ts i⌋₊ ω (ws i)) ∂growthPathLaw (σ n) b)
      atTop (𝓝 (∫ ω, Φ (fun i => Z (ws i) (ts i) ω) ∂P)) := by
  set e := Fintype.equivFin ι
  set L : C(Fin (Fintype.card ι) → ℂ, ι → ℂ) := ⟨fun y i => y (e i), by fun_prop⟩
  have := hfdd _ (fun j => ws (e.symm j)) (fun j => ts (e.symm j)) (fun j => h _)
    (Φ.compContinuous L)
  simpa [L, BoundedContinuousFunction.compContinuous_apply] using this

end BlockBand.SourceProcess.FullSourceGenerator.GenLim
