module

public import BlockBand.Critical.GlobalSource.Statement

/-!
# Global Gaussian source: the complex source limit along every length sequence

`IsComplexSourceLimit b E T τ m ν` is convergence along all widths `W` at the single length
`⌊W T⌋₊`. The global Gaussian source statement applies the complex source law to the ring path of
length `n - 3` along an arbitrary critical sequence, which needs the same limit along every length
sequence `r_W` with `r_W / W → T`.

* `ComplexSourceLimitAlongSequences`: that statement, as a `Prop`, used as an explicit hypothesis
  (it follows from `ComplexSourceLimitSequenceContract`, see
  `complexSourceLimitAlongSequences_of_contract`).
* `tendsto_of_forall_length_seq`: an abstract subsequence lemma. Convergence along every length
  function `r : ℕ → ℕ` with `r W / W → T` gives convergence along every pair sequence
  `(W_j, r_j)` with `W_j → ∞`, `r_j / W_j → T` (widths may repeat).
* `ComplexSourceLimitAlongSequences.tendsto_seq`: the source data converge along every such
  pair sequence, in particular along `(W_j, n_j - 3)` for a critical sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws

/-- **The complex source limit along every length sequence**: if `ν` is the complex source limit
at the lengths `⌊W T⌋₊` (`IsComplexSourceLimit b E T τ m ν`), then the source data at width `W` and
length `r W` converge in law to `ν` for every `r` with `r W / W → T`. -/
def ComplexSourceLimitAlongSequences : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ T : ℝ, (∀ j, τ j < T) →
    ∀ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν →
    ∀ r : ℕ → ℕ, Tendsto (fun W : ℕ => (r W : ℝ) / W) atTop (𝓝 T) →
    ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
      Tendsto (fun W : ℕ => ∫ x, Φ (complexSourceData b E W (r W) τ m x) ∂probedPathLaw W np b)
        atTop (𝓝 (∫ y, Φ y ∂ν))

/-- **From length functions to pair sequences** (abstract). Let `f w r` be a value at width `w`
and length `r`, `T ∈ ℝ`, and suppose `f w (r' w) → L` for every `r' : ℕ → ℕ` with
`r' w / w → T`. Then `f (W_j) (r_j) → L` for every sequence with `W_j → ∞` and
`r_j / W_j → T` (repetitions in `W_j` allowed). Proof: every subsequence has a further
subsequence with strictly increasing widths; along it the lengths define a length function
(completed by `⌊T w⌋₊`). -/
theorem tendsto_of_forall_length_seq {α : Type*} [TopologicalSpace α] {f : ℕ → ℕ → α}
    {L : α} {T : ℝ}
    (H : ∀ r' : ℕ → ℕ, Tendsto (fun w : ℕ => (r' w : ℝ) / w) atTop (𝓝 T) →
      Tendsto (fun w => f w (r' w)) atTop (𝓝 L))
    {W r : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hr : Tendsto (fun j => (r j : ℝ) / W j) atTop (𝓝 T)) :
    Tendsto (fun j => f (W j) (r j)) atTop (𝓝 L) := by
  have hT : 0 ≤ T := ge_of_tendsto' hr fun j => by positivity
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨φ, hφ, hV⟩ := strictMono_subseq_of_tendsto_atTop (hW.comp hns)
  set V : ℕ → ℕ := (W ∘ ns) ∘ φ with hVdef
  set jk : ℕ → ℕ := ns ∘ φ with hjk
  have hjk_tend : Tendsto jk atTop atTop := hns.comp hφ.tendsto_atTop
  classical
  let r' : ℕ → ℕ := fun w => if h : ∃ k, V k = w then r (jk (Classical.choose h)) else
    ⌊T * w⌋₊
  have hr'V : ∀ k, r' (V k) = r (jk k) := by
    intro k
    have h : ∃ k', V k' = V k := ⟨k, rfl⟩
    simp only [r', h, ↓reduceDIte]
    rw [hV.injective (Classical.choose_spec h)]
  have hfl : Tendsto (fun w : ℕ => (⌊T * w⌋₊ : ℝ) / w) atTop (𝓝 T) :=
    (tendsto_nat_floor_mul_div_atTop hT).comp tendsto_natCast_atTop_atTop
  have hr' : Tendsto (fun w : ℕ => (r' w : ℝ) / w) atTop (𝓝 T) := by
    rw [Metric.tendsto_atTop] at hr hfl ⊢
    intro ε hε
    obtain ⟨J0, hJ0⟩ := hr ε hε
    obtain ⟨N1, hN1⟩ := hfl ε hε
    obtain ⟨K0, hK0⟩ := (tendsto_atTop.mp hjk_tend) J0 |>.exists_forall_of_atTop
    refine ⟨max N1 (V K0), fun w hw => ?_⟩
    by_cases h : ∃ k, V k = w
    · simp only [r', h, ↓reduceDIte]
      set k := Classical.choose h
      have hk : V k = w := Classical.choose_spec h
      have hKk : K0 ≤ k := by
        rw [← hV.le_iff_le, hk]
        exact le_of_max_le_right hw
      have := hJ0 (jk k) (hK0 k hKk)
      have hWk : W (jk k) = w := hk
      rwa [hWk] at this
    · simp only [r', h, ↓reduceDIte]
      exact hN1 w (le_of_max_le_left hw)
  refine ⟨φ, ?_⟩
  have := (H r' hr').comp hV.tendsto_atTop
  refine this.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [hr'V k]
  rfl

/-- **The source data along every pair sequence**: under `ComplexSourceLimitAlongSequences`, for
every sequence of widths `W_j → ∞` and path lengths `r_j` with `r_j / W_j → T`,
`E Φ(data at (W_j, r_j)) → ∫Φ dν` for every bounded continuous `Φ`. Same law and data as
`IsComplexSourceLimit`. -/
theorem ComplexSourceLimitAlongSequences.tendsto_seq (hA : ComplexSourceLimitAlongSequences)
    {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE : -2 < E) (hE' : E < 2) {np : ℕ}
    {τ m : Fin np → ℝ} (hτ : Function.Injective τ) (hτpos : ∀ j, 0 < τ j) (hm : ∀ j, 0 ≤ m j)
    {T : ℝ} (hT : ∀ j, τ j < T) {ν : Measure (SourceData np)}
    (hν : IsComplexSourceLimit b E T τ m ν) {W r : ℕ → ℕ} (hW : Tendsto W atTop atTop)
    (hr : Tendsto (fun j => (r j : ℝ) / W j) atTop (𝓝 T))
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    Tendsto (fun j => ∫ x, Φ (complexSourceData b E (W j) (r j) τ m x)
      ∂probedPathLaw (W j) np b) atTop (𝓝 (∫ y, Φ y ∂ν)) :=
  tendsto_of_forall_length_seq (f := fun w l => ∫ x, Φ (complexSourceData b E w l τ m x)
      ∂probedPathLaw w np b)
    (fun r' hr' => hA b hb hb' E hE hE' np τ m hτ hτpos hm T hT ν hν r' hr' Φ) hW hr

end BlockBand.Critical.GlobalSource
