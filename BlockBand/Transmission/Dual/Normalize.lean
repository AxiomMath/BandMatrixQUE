module

public import BlockBand.Transmission.Dual.Statement
public import BlockBand.SourceProcess.Stochastic.Basic

/-!
# Normalization of a dual deletion process

For a realization `(N, X, Y)` of `IsDualDeletionProcess P 𝓖 D₀ x y` with an ordered interior
start, `exists_normalized` produces a version `(N', X', Y')` that
* is a realization for the null-augmented filtration `augmentedFiltration 𝓖 P`, and
* is a deletion path starting at `(p; x, y)` at **every** `ω`, and
* is indistinguishable from `(N, X, Y)`: a.s. the three paths agree at all times; hence the
  law of `dualState` is unchanged.

The modification sets the path to the constant path at the start on a measurable null set
`B ⊇ {bad ω}`; `B` is in the augmented `𝓖_0`. Generic tools (any `Ω`, `𝓖`, `P`):
`exists_ae_eq_of_measurableSet_aug` (augmented events are raw events up to null sets),
`martingale_aug` (raw martingale ⇒ augmented martingale), `martingale_of_ae_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

/-!
## Null augmentation, generic
-/

section Aug

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem ae_good_of_generateMeasurable (𝓖 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) {C : Set (Set Ω)}
    (hC : ∀ s ∈ C, ∃ B, MeasurableSet[𝓖 t] B ∧ s =ᵐ[P] B)
    {s : Set Ω} (hs : MeasurableSpace.GenerateMeasurable C s) :
    ∃ B, MeasurableSet[𝓖 t] B ∧ s =ᵐ[P] B := by
  induction hs with
  | basic s h => exact hC s h
  | empty => exact ⟨∅, @MeasurableSet.empty _ (𝓖 t), EventuallyEq.rfl⟩
  | compl s _ ih =>
    obtain ⟨B, hB, h⟩ := ih
    exact ⟨Bᶜ, hB.compl, EventuallyEqSet.compl h⟩
  | iUnion f _ ih =>
    choose B hB h using ih
    exact ⟨⋃ i, B i, MeasurableSet.iUnion hB, EventuallyEqSet.countable_iUnion h⟩

/-- Events of `m ⊔ N_P` are events of `m` up to `P`-null sets. -/
theorem exists_ae_eq_of_measurableSet_aug (𝓖 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[augmentedFiltration 𝓖 P t] A) :
    ∃ B, MeasurableSet[𝓖 t] B ∧ A =ᵐ[P] B := by
  have hA' := (MeasurableSpace.measurableSet_sup (m₁ := 𝓖 t) (m₂ := nullSigma P)).1 hA
  refine ae_good_of_generateMeasurable 𝓖 t ?_ hA'
  rintro s (hs | hs)
  · exact ⟨s, hs, EventuallyEq.rfl⟩
  · refine ae_good_of_generateMeasurable 𝓖 t ?_ hs
    rintro N ⟨_, hN⟩
    exact ⟨∅, @MeasurableSet.empty _ (𝓖 t), ae_eq_empty.2 hN⟩

theorem measurableSet_aug_of_null (𝓖 : Filtration ℝ≥0 mΩ) {B : Set Ω} (hB : MeasurableSet B)
    (h0 : P B = 0) (t : ℝ≥0) : MeasurableSet[augmentedFiltration 𝓖 P t] B :=
  (le_sup_right : nullSigma P ≤ 𝓖 t ⊔ nullSigma P) _
    (MeasurableSpace.measurableSet_generateFrom ⟨hB, h0⟩)

/-- A raw martingale is a martingale for the null-augmented filtration. -/
theorem martingale_aug {𝓖 : Filtration ℝ≥0 mΩ} [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓖 P) : Martingale M (augmentedFiltration 𝓖 P) P := by
  have hm (t : ℝ≥0) : StronglyMeasurable[augmentedFiltration 𝓖 P t] (M t) :=
    (hM.stronglyMeasurable t).mono (le_augmentedFiltration _ _ t)
  refine ⟨hm, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((augmentedFiltration 𝓖 P).le s)
    (hM.integrable t) (fun _ _ _ => (hM.integrable s).integrableOn) (fun A hA _ => ?_)
    (hm s).aestronglyMeasurable).symm
  obtain ⟨B, hB, hAB⟩ := exists_ae_eq_of_measurableSet_aug 𝓖 s hA
  rw [setIntegral_congr_set hAB, setIntegral_congr_set hAB]
  exact hM.setIntegral_eq hst hB

/-- An adapted process that is a modification of a martingale is a martingale. -/
theorem martingale_of_ae_eq {𝓕 : Filtration ℝ≥0 mΩ} {M M' : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓕 P) (hm : ∀ t, StronglyMeasurable[𝓕 t] (M' t))
    (he : ∀ t, M' t =ᵐ[P] M t) : Martingale M' 𝓕 P := by
  refine ⟨hm, fun s t hst => ?_⟩
  exact (condExp_congr_ae (he t)).trans ((hM.2 s t hst).trans (he s).symm)

end Aug

/-!
## The constant start path and locality of `dualMartingale`
-/

/-- The finite start vector extended by `0`. -/
def extendFin {p : ℕ} (x : Fin p → ℝ) : ℕ → ℝ := fun i => if h : i < p then x ⟨i, h⟩ else 0

theorem dualCoordOf_extendFin {p : ℕ} (x y : Fin p → ℝ) :
    dualCoordOf p (extendFin x) (extendFin y) = (x, y) := by
  ext i <;> simp [dualCoordOf, extendFin]

/-- The constant path at an ordered interior start is a deletion path. -/
theorem isDeletionPath_const {p : ℕ} {x y : Fin p → ℝ} (hxy : IsRatioParameter x y) :
    IsDeletionPath (fun _ => p) (fun _ => extendFin x) (fun _ => extendFin y) where
  antitone := fun _ _ _ => le_rfl
  chamber := fun _ => by
    show dualCoordOf p (extendFin x) (extendFin y) ∈ dualChamber p
    rw [dualCoordOf_extendFin]; exact hxy
  rightCont := fun _ => Eventually.of_forall fun _ => rfl
  cont := fun _ _ _ _ _ _ => ⟨continuousOn_const, continuousOn_const⟩
  deletion := fun τ hτ q hq hne => by
    have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
    obtain ⟨u, hu⟩ := hq.exists
    exact absurd hu hne

/-- `dualMartingale` at `(t, ω)` depends only on the three paths of `ω`. -/
theorem dualMartingale_congr {Ω Ω' : Type*} (D0 : ℝ) (q : ℕ) (f : DualCoord q → ℝ)
    {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {N' : ℝ≥0 → Ω' → ℕ}
    {X' Y' : ℝ≥0 → Ω' → ℕ → ℝ} {ω : Ω} {ω' : Ω'} (hN : ∀ s, N s ω = N' s ω')
    (hX : ∀ s, X s ω = X' s ω') (hY : ∀ s, Y s ω = Y' s ω') (t : ℝ≥0) :
    dualMartingale D0 q f N X Y t ω = dualMartingale D0 q f N' X' Y' t ω' := by
  by_cases hc : ∃ u ≤ t, N' u ω' ≤ q
  · simp only [dualMartingale, dualEntranceValue, dualEntrance, hN, hX, hY, hc, ↓reduceIte]
  · simp only [dualMartingale, dualEntranceValue, hN, hX, hY, hc, ↓reduceIte]

/-!
## The normalized version
-/

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

open scoped Classical in
/-- The modification on the set `B`: the constant start path there, the original elsewhere. -/
def modN (B : Set Ω) (p : ℕ) (N : ℝ≥0 → Ω → ℕ) : ℝ≥0 → Ω → ℕ :=
  fun t ω => if ω ∈ B then p else N t ω

open scoped Classical in
/-- Coordinate modification on `B`. -/
def modX (B : Set Ω) {p : ℕ} (x : Fin p → ℝ) (X : ℝ≥0 → Ω → ℕ → ℝ) : ℝ≥0 → Ω → ℕ → ℝ :=
  fun t ω => if ω ∈ B then extendFin x else X t ω

open scoped Classical in
/-- **Normalization.** Every realization has an indistinguishable version which is a
realization for the augmented filtration and a deletion path from the start at every `ω`. -/
theorem exists_normalized (hxy : IsRatioParameter x y)
    (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y) :
    ∃ (N' : ℝ≥0 → Ω → ℕ) (X' Y' : ℝ≥0 → Ω → ℕ → ℝ),
      IsDualDeletionProcess P (augmentedFiltration 𝓖 P) D0 x y N' X' Y' ∧
      (∀ ω, IsDeletionPath (fun t => N' t ω) (fun t => X' t ω) (fun t => Y' t ω)) ∧
      (∀ ω, N' 0 ω = p ∧ ∀ i : Fin p, X' 0 ω i = x i ∧ Y' 0 ω i = y i) ∧
      (∀ᵐ ω ∂P, ∀ t, N' t ω = N t ω ∧ X' t ω = X t ω ∧ Y' t ω = Y t ω) := by
  have := h.prob
  set Good : Set Ω := {ω | (N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i) ∧
    IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)} with hGood
  have hae : ∀ᵐ ω ∂P, ω ∈ Good := h.start.and h.paths
  set B := toMeasurable P Goodᶜ with hBdef
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : P B = 0 := by rw [hBdef, measure_toMeasurable]; exact ae_iff.1 hae
  have hgood : ∀ ω, ω ∉ B → ω ∈ Good := fun ω hω => by
    by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hBaug : ∀ t, MeasurableSet[augmentedFiltration 𝓖 P t] B :=
    measurableSet_aug_of_null 𝓖 hBm hB0
  have hnotB : ∀ᵐ ω ∂P, ω ∉ B := measure_eq_zero_iff_ae_notMem.1 hB0
  refine ⟨modN B p N, modX B x X, modX B y Y, ?_, ?_, ?_, ?_⟩
  · refine
      { prob := h.prob
        adapted := fun t => ?_
        start := ?_
        paths := ?_
        martingale := fun q hq hqp f hf hfc hfs => ?_ }
    · have hle := le_augmentedFiltration 𝓖 P t
      obtain ⟨hN, hX, hY⟩ := h.adapted t
      exact ⟨Measurable.ite (hBaug t) measurable_const (hN.mono hle le_rfl),
        Measurable.ite (hBaug t) (measurable_const (a := extendFin x)) (hX.mono hle le_rfl),
        Measurable.ite (hBaug t) (measurable_const (a := extendFin y)) (hY.mono hle le_rfl)⟩
    · refine Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ B
      · simp [modN, modX, hω, extendFin]
      · simpa [modN, modX, hω] using (hgood ω hω).1
    · refine Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ B
      · simpa [modN, modX, hω] using isDeletionPath_const hxy
      · simpa [modN, modX, hω] using (hgood ω hω).2
    · have hM := martingale_aug (h.martingale q hq hqp f hf hfc hfs)
      set c : ℝ≥0 → ℝ := fun t => dualMartingale D0 q f (fun _ (_ : Unit) => p)
        (fun _ _ => extendFin x) (fun _ _ => extendFin y) t ()
      have hrep : ∀ t, dualMartingale D0 q f (modN B p N) (modX B x X) (modX B y Y) t =
          fun ω => if ω ∈ B then c t else dualMartingale D0 q f N X Y t ω := fun t => by
        funext ω
        by_cases hω : ω ∈ B
        · simp only [hω, ↓reduceIte]
          exact dualMartingale_congr D0 q f (fun s => by simp [modN, hω])
            (fun s => by simp [modX, hω]) (fun s => by simp [modX, hω]) t
        · simp only [hω, ↓reduceIte]
          exact dualMartingale_congr D0 q f (fun s => by simp [modN, hω])
            (fun s => by simp [modX, hω]) (fun s => by simp [modX, hω]) t
      refine martingale_of_ae_eq hM (fun t => ?_) (fun t => ?_)
      · rw [hrep t]
        exact StronglyMeasurable.ite (hBaug t) stronglyMeasurable_const (hM.1 t)
      · rw [hrep t]
        filter_upwards [hnotB] with ω hω
        simp [hω]
  · intro ω
    by_cases hω : ω ∈ B
    · simpa [modN, modX, hω] using isDeletionPath_const hxy
    · simpa [modN, modX, hω] using (hgood ω hω).2
  · intro ω
    by_cases hω : ω ∈ B
    · simp [modN, modX, hω, extendFin]
    · simpa [modN, modX, hω] using (hgood ω hω).1
  · filter_upwards [hnotB] with ω hω t
    simp [modN, modX, hω]

/-- The normalized version has the same law of the truncated state. -/
theorem map_dualState_congr {N' : ℝ≥0 → Ω → ℕ} {X' Y' : ℝ≥0 → Ω → ℕ → ℝ}
    (he : ∀ᵐ ω ∂P, ∀ t, N' t ω = N t ω ∧ X' t ω = X t ω ∧ Y' t ω = Y t ω) :
    P.map (dualState N' X' Y') = P.map (dualState N X Y) := by
  refine Measure.map_congr ?_
  filter_upwards [he] with ω hω
  funext t
  obtain ⟨h1, h2, h3⟩ := hω t
  simp [dualState, h1, h2, h3]

end BlockBand.Transmission.Dual
