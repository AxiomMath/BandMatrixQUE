module

public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra
public import Mathlib.MeasureTheory.Measure.Trim

/-!
# Domination extends from an increasing union of σ-algebras

The class `{A : μ(A) ≤ ν(A)}` is not closed under complements, so Dynkin's π–λ theorem does not
apply. We use approximation instead: for finite measures, every set of `σ(⋃ₙ 𝒜ₙ)` is
approximated in `(μ + ν)`-measure by sets of the ring `⋃ₙ 𝒜ₙ`
(Mathlib `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`).
* `le_of_le_on_iSup`: if `μ ≤ ν` on every `𝒜ₙ` (increasing, `𝒜ₙ ≤ m`), then on `⨆ₙ 𝒜ₙ`.
* `measure_le_of_forall_fin`: on a sequence space `ℕ → X`, if `μ ≤ ν` on the σ-algebra of the
  first `n + 1` coordinates for every `n`, then `μ ≤ ν` (as measures).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Set Filter
open scoped ENNReal NNReal

variable {α : Type*}

/-- The union of an increasing sequence of σ-algebras is a ring of sets. -/
theorem isSetRing_iUnion_measurableSet {𝒜 : ℕ → MeasurableSpace α} (h𝒜 : Monotone 𝒜) :
    IsSetRing {s : Set α | ∃ n, MeasurableSet[𝒜 n] s} where
  empty_mem := ⟨0, @MeasurableSet.empty α (𝒜 0)⟩
  union_mem := by
    rintro s t ⟨m, hs⟩ ⟨n, ht⟩
    exact ⟨max m n, (h𝒜 (le_max_left m n) _ hs).union (h𝒜 (le_max_right m n) _ ht)⟩
  sdiff_mem := by
    rintro s t ⟨m, hs⟩ ⟨n, ht⟩
    exact ⟨max m n, (h𝒜 (le_max_left m n) _ hs).diff (h𝒜 (le_max_right m n) _ ht)⟩

/-- Two-sided estimate through a symmetric difference. -/
theorem measure_le_add_symmDiff {m : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}
    (ht : μ t ≤ ν t) : μ s ≤ ν s + (μ + ν) (symmDiff t s) := by
  have h1 : μ s ≤ μ t + μ (symmDiff t s) :=
    (measure_mono (show s ⊆ t ∪ symmDiff t s from fun x hx => by
      by_cases hxt : x ∈ t
      · exact Or.inl hxt
      · exact Or.inr (Or.inr ⟨hx, hxt⟩))).trans (measure_union_le _ _)
  have h2 : ν t ≤ ν s + ν (symmDiff t s) :=
    (measure_mono (show t ⊆ s ∪ symmDiff t s from fun x hx => by
      by_cases hxs : x ∈ s
      · exact Or.inl hxs
      · exact Or.inr (Or.inl ⟨hx, hxs⟩))).trans (measure_union_le _ _)
  calc μ s ≤ μ t + μ (symmDiff t s) := h1
    _ ≤ ν s + ν (symmDiff t s) + μ (symmDiff t s) := add_le_add_left (ht.trans h2) _
    _ = ν s + (μ + ν) (symmDiff t s) := by rw [Measure.add_apply]; ring

/-- **Domination extends to `⨆ₙ 𝒜ₙ`.** -/
theorem le_of_le_on_iSup {m : MeasurableSpace α} {𝒜 : ℕ → MeasurableSpace α} (h𝒜 : Monotone 𝒜)
    (hle : ∀ n, 𝒜 n ≤ m) {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n s, MeasurableSet[𝒜 n] s → μ s ≤ ν s) {s : Set α}
    (hs : MeasurableSet[⨆ n, 𝒜 n] s) : μ s ≤ ν s := by
  have hle' : (⨆ n, 𝒜 n) ≤ m := iSup_le hle
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hC : ∃ D : Set (Set α), D.Countable ∧ D ⊆ {s : Set α | ∃ n, MeasurableSet[𝒜 n] s} ∧
      (μ + ν).trim hle' (⋃₀ D)ᶜ = 0 :=
    ⟨{univ}, countable_singleton _, by
      rw [singleton_subset_iff]; exact ⟨0, MeasurableSet.univ⟩, by simp⟩
  obtain ⟨t, ⟨n, ht⟩, hts⟩ := @exists_measure_symmDiff_lt_of_generateFrom_isSetRing α
    (⨆ n, 𝒜 n) ((μ + ν).trim hle') _ _ (isSetRing_iUnion_measurableSet h𝒜) hC
    (MeasurableSpace.measurableSpace_iSup_eq 𝒜) s hs (ε : ℝ≥0∞) (by exact_mod_cast hε)
  have htm : MeasurableSet[⨆ n, 𝒜 n] t :=
    MeasurableSpace.measurableSet_iSup.2 (MeasurableSpace.GenerateMeasurable.basic _ ⟨n, ht⟩)
  rw [trim_measurableSet_eq hle' (htm.symmDiff hs)] at hts
  exact (measure_le_add_symmDiff (h n t ht)).trans (add_le_add_right hts.le _)

/-! ## Sequence spaces -/

variable {X : Type*} [MeasurableSpace X]

/-- The first `n + 1` coordinates. -/
def finRestr (n : ℕ) (w : ℕ → X) : Fin (n + 1) → X := fun k => w k

theorem measurable_finRestr (n : ℕ) : Measurable (finRestr (X := X) n) :=
  measurable_pi_iff.2 fun k => measurable_pi_apply (k : ℕ)

/-- The σ-algebra of the first `n + 1` coordinates. -/
abbrev finAlg (X : Type*) [MeasurableSpace X] (n : ℕ) : MeasurableSpace (ℕ → X) :=
  MeasurableSpace.comap (finRestr n) inferInstance

theorem finAlg_le (n : ℕ) : finAlg X n ≤ MeasurableSpace.pi := (measurable_finRestr n).comap_le

theorem monotone_finAlg : Monotone (finAlg X) := by
  intro m n hmn
  have hg : Measurable fun (v : Fin (n + 1) → X) (k : Fin (m + 1)) =>
      v (Fin.castLE (by omega) k) := measurable_pi_iff.2 fun k => measurable_pi_apply _
  have e : finRestr (X := X) m =
      (fun (v : Fin (n + 1) → X) (k : Fin (m + 1)) => v (Fin.castLE (by omega) k)) ∘
        finRestr n := by
    funext w k; simp [finRestr]
  refine Measurable.comap_le ?_
  rw [e]
  exact hg.comp (comap_measurable _)

theorem iSup_finAlg : (⨆ n, finAlg X n) = MeasurableSpace.pi := by
  refine le_antisymm (iSup_le finAlg_le) (iSup_le fun k => le_iSup_of_le k ?_)
  refine Measurable.comap_le ?_
  have e : (fun w : ℕ → X => w k) = (fun v : Fin (k + 1) → X => v (Fin.last k)) ∘ finRestr k := by
    funext w; simp [finRestr]
  rw [e]
  exact (measurable_pi_apply _).comp (comap_measurable _)

/-- **Domination on a sequence space from the finite-coordinate σ-algebras.** -/
theorem measure_le_of_forall_fin {μ ν : Measure (ℕ → X)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (n : ℕ) (B : Set (Fin (n + 1) → X)), MeasurableSet B →
      μ (finRestr n ⁻¹' B) ≤ ν (finRestr n ⁻¹' B)) : μ ≤ ν := by
  refine Measure.le_iff.2 fun s hs => ?_
  refine le_of_le_on_iSup monotone_finAlg finAlg_le (fun n s hs => ?_) (by rwa [iSup_finAlg])
  obtain ⟨B, hB, rfl⟩ := hs
  exact h n B hB

end BlockBand.Transmission.Dual.G
