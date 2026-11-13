module

public import BlockBand.Transmission.DualBoundary.MarkovPath
public import BlockBand.Transmission.DualBoundary.Transfer
public import BlockBand.Transmission.Dual.Normalize

/-!
# Markov property at a deterministic time

Setting: any one-pair boundary realization `h : IsBoundaryDualProcess P 𝓖 D₀ ![x] ![y] N X Y`
(any filtered probability space, raw filtration `𝓖`) and a deterministic time `s > 0`.
* `badSet`: a measurable `P`-null set off which the path starts at level one and is a boundary
  deletion path; `postSet = {ω ∉ badSet, N_s = 1}`.
* `postN`, `postC`: the path after `s`, truncated, on `postSet`; the empty path elsewhere.
* `shiftAug 𝓖 P s`: the null-augmented filtration shifted by `s`, `u ↦ 𝓖_{s+u} ∨ 𝒩_P`.
* **`markov_at`**: for `A ⊆ postSet`, `A` in the augmented `𝓖_s`, `P A ≠ 0`, the post path is
  an `IsDualFrom` realization at level `1` under `P[|A]` for `shiftAug 𝓖 P s` (random start in
  `𝒞₁`, deletion path at every `ω`).
* `ae_dualState_post`: a.s. the truncated post state at `u` is `truncDualState` at `s + u`.
* `martingale_shiftConst_indicator` (generic): `1_E (M_{s+u} − M_s)` is a martingale for the
  shifted filtration when `M` is a martingale and `E ∈ 𝓕_s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness (martingale_cond ae_cond_of_ae)
open scoped NNReal ENNReal

/-- A filtration shifted by a deterministic time. -/
def shiftConst {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (s : ℝ≥0) :
    Filtration ℝ≥0 m where
  seq u := 𝓕 (s + u)
  mono' _ _ h := 𝓕.mono (add_le_add_right h s)
  le' u := 𝓕.le (s + u)

/-- The null-augmented filtration shifted by `s`. -/
def shiftAug {Ω : Type*} {m : MeasurableSpace Ω} (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (s : ℝ≥0) : Filtration ℝ≥0 m :=
  shiftConst (augmentedFiltration 𝓖 P) s

/-- **`1_E (M_{s+u} − M_s)` is a martingale for `𝓕_{s+·}`.** -/
theorem martingale_shiftConst_indicator {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    (s : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[𝓕 s] E) :
    Martingale (fun u => E.indicator fun ω => M (s + u) ω - M s ω) (shiftConst 𝓕 s) P := by
  have hEu : ∀ u : ℝ≥0, MeasurableSet[𝓕 (s + u)] E := fun u => 𝓕.mono le_self_add _ hE
  have hm : ∀ u : ℝ≥0, StronglyMeasurable[𝓕 (s + u)] (E.indicator fun ω => M (s + u) ω - M s ω) :=
    fun u => ((hM.stronglyMeasurable (s + u)).sub
      ((hM.stronglyMeasurable s).mono (𝓕.mono le_self_add))).indicator (hEu u)
  have hEm : MeasurableSet E := 𝓕.le s _ hE
  have hint : ∀ u : ℝ≥0, Integrable (E.indicator fun ω => M (s + u) ω - M s ω) P := fun u =>
    ((hM.integrable (s + u)).sub (hM.integrable s)).indicator hEm
  refine ⟨hm, fun u v huv => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((shiftConst 𝓕 s).le u) (hint v)
    (fun _ _ _ => (hint u).integrableOn) (fun B hB _ => ?_) (hm u).aestronglyMeasurable).symm
  have hB' : MeasurableSet B := (shiftConst 𝓕 s).le u _ hB
  have hBE : MeasurableSet[𝓕 (s + u)] (B ∩ E) := hB.inter (hEu u)
  rw [setIntegral_indicator hEm, setIntegral_indicator hEm,
    integral_sub ((hM.integrable _).integrableOn) ((hM.integrable _).integrableOn),
    integral_sub ((hM.integrable _).integrableOn) ((hM.integrable _).integrableOn),
    hM.setIntegral_eq ((add_le_add_iff_left s).2 huv) hBE]

section Real

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- A measurable null set off which the path is a one-pair boundary deletion path. -/
def badSet (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : Set Ω :=
  toMeasurable P {ω | ¬(N 0 ω = 1 ∧
    IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))}

/-- `{ω ∉ badSet, N_s = 1}`. -/
def postSet (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ≥0) : Set Ω :=
  {ω | ω ∉ badSet P N X Y ∧ N s ω = 1}

open scoped Classical in
/-- The post-`s` level (empty path off `postSet`). -/
def postN (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ≥0) :
    ℝ≥0 → Ω → ℕ := fun u ω => if ω ∈ postSet P N X Y s then N (s + u) ω else 0

open scoped Classical in
/-- The post-`s` coordinates, truncated (`C = X` or `C = Y`). -/
def postC (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ≥0)
    (C : ℝ≥0 → Ω → ℕ → ℝ) : ℝ≥0 → Ω → ℕ → ℝ := fun u ω =>
  if ω ∈ postSet P N X Y s then truncCoord (N (s + u) ω) (C (s + u) ω) else 0

theorem measurableSet_badSet : MeasurableSet (badSet P N X Y) := measurableSet_toMeasurable _ _

theorem measure_badSet (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    P (badSet P N X Y) = 0 := by
  rw [badSet, measure_toMeasurable]
  exact ae_iff.1 (ae_path h)

theorem good_of_notMem_badSet {ω : Ω} (hω : ω ∉ badSet P N X Y) :
    N 0 ω = 1 ∧ IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω) := by
  by_contra hc; exact hω (subset_toMeasurable _ _ hc)

theorem measurableSet_postSet_aug (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (s : ℝ≥0) : MeasurableSet[augmentedFiltration 𝓖 P s] (postSet P N X Y s) := by
  have hB := measurableSet_aug_of_null 𝓖 measurableSet_badSet (measure_badSet h) s
  have hN : MeasurableSet[augmentedFiltration 𝓖 P s] {ω | N s ω = 1} :=
    le_augmentedFiltration 𝓖 P s _ ((h.adapted s).1 (measurableSet_singleton 1))
  exact hB.compl.inter hN

/-- **Markov property at `s`: the post-`s` path is an `IsDualFrom` realization at level
one.** -/
theorem markov_at (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) {s : ℝ≥0} (hs : 0 < s)
    {A : Set Ω} (hA : MeasurableSet[augmentedFiltration 𝓖 P s] A)
    (hAE : A ⊆ postSet P N X Y s) (hA0 : P A ≠ 0) :
    IsDualFrom (P[|A]) (shiftAug 𝓖 P s) D0 1 (postN P N X Y s) (postC P N X Y s X)
      (postC P N X Y s Y) := by
  have := h.prob
  set E := postSet P N X Y s with hEdef
  have hE := measurableSet_postSet_aug h s
  have hEu : ∀ u, MeasurableSet[shiftAug 𝓖 P s u] E := fun u =>
    (augmentedFiltration 𝓖 P).mono le_self_add _ hE
  have hAm : MeasurableSet A := (augmentedFiltration 𝓖 P).le s _ hA
  have hpN : ∀ ω ∈ E, ∀ u, postN P N X Y s u ω = N (s + u) ω := fun ω hω u => by
    simp only [postN, ← hEdef, hω, ite_true]
  have hpC : ∀ (C : ℝ≥0 → Ω → ℕ → ℝ), ∀ ω ∈ E, ∀ u, postC P N X Y s C u ω =
      truncCoord (N (s + u) ω) (C (s + u) ω) := fun C ω hω u => by
    simp only [postC, ← hEdef, hω, ite_true]
  have hnN : ∀ ω ∉ E, ∀ u, postN P N X Y s u ω = 0 := fun ω hω u => by
    simp only [postN, ← hEdef, hω, ite_false]
  refine
    { prob := cond_isProbabilityMeasure hA0
      adapted := fun u => ?_
      start := ?_
      bound := fun ω => ?_
      paths := fun ω => ?_
      martingale := fun q hq hq1 f hf hfc hfs => ?_ }
  · have hle : 𝓖 (s + u) ≤ shiftAug 𝓖 P s u := le_augmentedFiltration 𝓖 P (s + u)
    obtain ⟨hN, hX, hY⟩ := h.adapted (s + u)
    have hN' := hN.mono hle le_rfl
    have tc : ∀ (k : Ω → ℕ) (a : Ω → ℕ → ℝ), Measurable[shiftAug 𝓖 P s u] k →
        Measurable[shiftAug 𝓖 P s u] a →
        Measurable[shiftAug 𝓖 P s u] fun ω => truncCoord (k ω) (a ω) := fun _ _ hk ha =>
      @measurable_truncCoord_comp Ω (shiftAug 𝓖 P s u) _ _ hk ha
    exact ⟨Measurable.ite (hEu u) hN' measurable_const,
      Measurable.ite (hEu u) (tc _ _ hN' (hX.mono hle le_rfl)) measurable_const,
      Measurable.ite (hEu u) (tc _ _ hN' (hY.mono hle le_rfl)) measurable_const⟩
  · filter_upwards [ae_cond_mem hAm] with ω hω
    rw [hpN ω (hAE hω), add_zero]; exact (hAE hω).2
  · by_cases hω : ω ∈ E
    · rw [hpN ω hω, add_zero, hω.2]
    · rw [hnN ω hω]; exact Nat.zero_le _
  · by_cases hω : ω ∈ E
    · have e1 : (fun u => postN P N X Y s u ω) = fun u => N (s + u) ω := funext (hpN ω hω)
      have e2 : (fun u => postC P N X Y s X u ω) = fun u => truncCoord (N (s + u) ω)
          (X (s + u) ω) := funext (hpC X ω hω)
      have e3 : (fun u => postC P N X Y s Y u ω) = fun u => truncCoord (N (s + u) ω)
          (Y (s + u) ω) := funext (hpC Y ω hω)
      rw [e1, e2, e3]
      exact isDeletionPath_shift_boundary (good_of_notMem_badSet hω.1).2 hs
    · have e1 : (fun u => postN P N X Y s u ω) = fun _ => 0 := funext (hnN ω hω)
      rw [e1]; exact isDeletionPath_empty _ _
  · obtain rfl : q = 1 := le_antisymm hq1 hq
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
    have hM := martingale_aug (h.martingale 1 le_rfl le_rfl f hf hfc hfs)
    have e : dualMartingale D0 1 f (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) =
        fun u => E.indicator fun ω => dualMartingale D0 1 f N X Y (s + u) ω -
          dualMartingale D0 1 f N X Y s ω := by
      funext u ω
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        obtain ⟨h0, hP⟩ := good_of_notMem_badSet hω.1
        exact dualMartingale_shift_one hP h0 hf2 hfc hfs hω.2 (hpN ω hω) (hpC X ω hω)
          (hpC Y ω hω) u
      · rw [indicator_of_notMem hω]
        exact dualMartingale_empty le_rfl (hnN ω hω) u
    rw [e]
    have hA' : MeasurableSet[shiftAug 𝓖 P s 0] A := by
      show MeasurableSet[augmentedFiltration 𝓖 P (s + 0)] A
      rw [add_zero]; exact hA
    exact martingale_cond (martingale_shiftConst_indicator hM s hE) hA' hA0

/-- A.s. the post state at `u` is the original truncated state at `s + u`. -/
theorem ae_dualState_post (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ u, dualState (postN P N X Y s) (postC P N X Y s X) (postC P N X Y s Y) ω u =
      truncDualState N X Y ω (s + u) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_badSet h)] with ω hω u
  obtain ⟨h0, hP⟩ := good_of_notMem_badSet hω
  have tt : ∀ (k : ℕ) (c : ℕ → ℝ), truncCoord k (truncCoord k c) = truncCoord k c := fun k c => by
    funext i; unfold truncCoord; split_ifs <;> rfl
  by_cases hs1 : N s ω = 1
  · have hE : ω ∈ postSet P N X Y s := ⟨hω, hs1⟩
    simp only [dualState, postN, postC, hE, ite_true, tt, truncDualState]
    rfl
  · have hs0 : N s ω = 0 := (level_eq_one_or_zero hP h0 s).resolve_left hs1
    have hE : ω ∉ postSet P N X Y s := fun h => hs1 h.2
    have hsu : N (s + u) ω = 0 := Nat.le_zero.1 (hs0 ▸ hP.antitone le_self_add)
    simp only [dualState, postN, postC, hE, ite_false, truncDualState, hsu]
    ext i <;> simp [truncCoord, truncDualCoord]

end Real

end BlockBand.Transmission.DualBoundary
