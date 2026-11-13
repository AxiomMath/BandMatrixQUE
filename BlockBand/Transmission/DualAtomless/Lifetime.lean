module

public import BlockBand.Transmission.DualAtomless.Glue
public import BlockBand.Transmission.Dual.ExistsAtomless

/-!
# The `p`-pair dual lifetime is atomless, for every realization

* **`DualLifetimeAtomless D₀ p`** (statement): for every ordered interior start with `p` pairs
  and every realization of `IsDualDeletionProcess` (any `Ω : Type`, filtration, probability),
  `P(ζ = u) = 0` for every `u ∈ [0, ∞)`, `ζ = dualExtinction N`. The left side is an outer
  measure: no measurability of `{ζ = u}` is assumed. Same shape as `DualLifetimeAtomlessOne`
  (the case `p = 1`).
* **`dualLifetimeAtomless_holds`**: `0 < D₀ → 1 ≤ p → DualLifetimeAtomless D₀ p`.
  (For `p = 0`, `ζ = 0` and the statement fails at `u = 0`.)
* **`dualLifetimeAtomlessOne_holds`**: `DualLifetimeAtomlessOne`.

Proof. `DelFromA` with `S = Unit` gives one realization whose lifetime has no atom at `u`. On
deletion paths (antitone, right-continuous level) `ζ = u` iff `N_u = 0` and `N_r ≠ 0` for the
dense times `r = qtime i < u` (`extOf_eq_iff`); the right side is a measurable set `atomSet u`
of state paths (product σ-algebra). Its probability is a function of the law of the truncated
state path, which is the same for every realization (`dualBoundaryLaw_holds.unique`); and a.s.
the path is a deletion path.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualAtomless

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.G
open scoped NNReal ENNReal

/-- **Statement: the `p`-pair lifetime is atomless** (every realization, every `u ≥ 0`). -/
def DualLifetimeAtomless (D0 : ℝ) (p : ℕ) : Prop :=
  ∀ (x y : Fin p → ℝ), IsRatioParameter x y →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsDualDeletionProcess P 𝓖 D0 x y N X Y →
      ∀ u : ℝ≥0, P {ω | dualExtinction N ω = (u : ℝ≥0∞)} = 0

/-!
## Deterministic: the atom event on deletion paths
-/

/-- The extinction time of one level path. -/
def extOf (n : ℝ≥0 → ℕ) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : n t = 0), (t : ℝ≥0∞)

theorem extOf_eq_iff {n : ℝ≥0 → ℕ} (hanti : Antitone n) (hrc : ∀ t, ∀ᶠ u in 𝓝[>] t, n u = n t)
    (u : ℝ≥0) : extOf n = u ↔ n u = 0 ∧ ∀ i, qtime i < u → n (qtime i) ≠ 0 := by
  constructor
  · intro h
    refine ⟨?_, fun i hi h0 => ?_⟩
    · obtain ⟨s, hs, hsu⟩ := ((hrc u).and self_mem_nhdsWithin).exists
      have hlt : extOf n < s := by rw [h]; exact ENNReal.coe_lt_coe.2 hsu
      obtain ⟨t, ht⟩ := iInf_lt_iff.1 hlt
      obtain ⟨ht0, hts⟩ := iInf_lt_iff.1 ht
      have := hanti (ENNReal.coe_le_coe.1 hts.le)
      rw [ht0] at this
      omega
    · have : extOf n ≤ qtime i := iInf₂_le (qtime i) h0
      rw [h] at this
      exact absurd (ENNReal.coe_le_coe.1 this) (not_le.2 hi)
  · rintro ⟨h0, hq⟩
    refine le_antisymm (iInf₂_le u h0) (le_iInf₂ fun t ht => ENNReal.coe_le_coe.2 ?_)
    by_contra hlt
    obtain ⟨i, hti, hiu⟩ := exists_qtime_mem_Ioo (not_le.1 hlt)
    have := hanti hti.le
    rw [ht] at this
    exact hq i hiu (Nat.le_zero.1 this)

/-- The atom event as a set of state paths. -/
def atomSet (u : ℝ≥0) : Set (ℝ≥0 → DualState) :=
  {w | (w u).1 = 0 ∧ ∀ i, qtime i < u → (w (qtime i)).1 ≠ 0}

theorem measurableSet_atomSet (u : ℝ≥0) : MeasurableSet (atomSet u) := by
  have hm : ∀ t : ℝ≥0, Measurable fun w : ℝ≥0 → DualState => (w t).1 := fun t =>
    measurable_fst.comp (measurable_pi_apply t)
  have e : atomSet u = {w : ℝ≥0 → DualState | (w u).1 = 0} ∩
      ⋂ i, ({_w : ℝ≥0 → DualState | ¬ qtime i < u} ∪ {w | (w (qtime i)).1 = 0}ᶜ) := by
    ext w
    simp only [atomSet, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    tauto
  rw [e]
  exact (measurableSet_eq_fun (hm u) measurable_const).inter (MeasurableSet.iInter fun i =>
    (MeasurableSet.const _).union (measurableSet_eq_fun (hm _) measurable_const).compl)

theorem dualExtinction_eq_iff {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω}
    (h : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) (u : ℝ≥0) :
    dualExtinction N ω = u ↔ dualState N X Y ω ∈ atomSet u :=
  extOf_eq_iff (n := fun t => N t ω) h.antitone h.rightCont u

/-!
## The atom clause for every realization
-/

/-- **The `p`-pair lifetime is atomless** (`p ≥ 1`, every realization). -/
theorem dualLifetimeAtomless_holds {D0 : ℝ} (hD0 : 0 < D0) {p : ℕ} (hp : 1 ≤ p) :
    DualLifetimeAtomless D0 p := by
  intro x y hxy Ω m 𝓖 P N X Y hD u
  obtain ⟨Ω₀, m₀, 𝓖₀, P₀, π₀, N₀, X₀, Y₀, hF, -, -, h0, hA⟩ :=
    delFromA_all hD0 p Unit inferInstance (Measure.dirac ()) inferInstance
      (fun _ => Fin.append x y) measurable_const (fun _ => append_mem_flatChamber hxy)
  have hD₀ : IsDualDeletionProcess P₀ 𝓖₀ D0 x y N₀ X₀ Y₀ := by
    refine ⟨hF.prob, hF.adapted, Eventually.of_forall fun ω => ?_,
      Eventually.of_forall hF.paths, hF.martingale⟩
    obtain ⟨hN, hc⟩ := h0 ω
    rw [ofFlat_append] at hc
    exact ⟨hN, fun i => ⟨congrFun (congrArg Prod.fst hc) i, congrFun (congrArg Prod.snd hc) i⟩⟩
  have hB := measurableSet_atomSet u
  have h₀ : P₀ (dualState N₀ X₀ Y₀ ⁻¹' atomSet u) = 0 := by
    have := ae_iff.1 (hA hp (fun _ => u) measurable_const)
    refine measure_mono_null (fun ω hω => ?_) this
    simp only [mem_ofPred_eq, not_not]
    exact (dualExtinction_eq_iff (hF.paths ω) u).2 hω
  have hlaw := dualBoundaryLaw_holds.unique D0 hD0 p x y hxy Ω m 𝓖 P N X Y Ω₀ m₀ 𝓖₀ P₀ N₀ X₀ Y₀
    hD hD₀
  have h1 : P (dualState N X Y ⁻¹' atomSet u) = 0 := by
    rw [← Measure.map_apply (measurable_dualState_of_isDual hD) hB, hlaw,
      Measure.map_apply (measurable_dualState_of_isDual hD₀) hB, h₀]
  have h2 := ae_iff.1 hD.paths
  refine measure_mono_null (fun ω hω => ?_) (measure_union_null h1 h2)
  by_cases hω' : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
  · exact Or.inl ((dualExtinction_eq_iff hω' u).1 hω)
  · exact Or.inr hω'

/-- **Lemma A3 for the `p = 1` object** (`Dual.Exists.DualLifetimeAtomlessOne`). -/
theorem dualLifetimeAtomlessOne_holds : Exists.DualLifetimeAtomlessOne :=
  fun _ hD0 x y hxy => dualLifetimeAtomless_holds hD0 le_rfl x y hxy

end BlockBand.Transmission.DualAtomless
