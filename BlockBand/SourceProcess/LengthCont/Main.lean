module

public import BlockBand.SourceProcess.LengthCont.Holds

/-!
# Main theorems: `LengthContinuity` and `ComplexSourceLimitSequenceContract`

The one-layer increment bounds `LayerIncrementBounds` give length continuity of the complex source
data, and hence the complex source limit sequence statement.

```
theorem lengthContinuity_of_layerIncrements (hL : LayerIncrementBounds) : LengthContinuity
theorem complexSourceLimitSequence_holds (hL : LayerIncrementBounds) :
    ComplexSourceLimitSequenceContract
```
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionSequences
open BlockBand.SourceProcess.ComplexSourceLaw

/-- `R_j / W_j → T` for `R_j = ⌊W_j T⌋`, `T ≥ 0`. -/
theorem tendsto_floor_div (Wseq : ℕ → ℕ) (hW : Tendsto Wseq atTop atTop) {T : ℝ}
    (hT : 0 ≤ T) :
    Tendsto (fun j => (⌊(Wseq j : ℝ) * T⌋₊ : ℝ) / Wseq j) atTop (𝓝 T) := by
  have := (tendsto_nat_floor_mul_div_atTop hT).comp (tendsto_natCast_atTop_atTop.comp hW)
  refine this.congr fun j => ?_
  simp [Function.comp, mul_comm]

/-- The window conditions of `LayerIncrementBounds`, from `p/W, q/W ∈ (T - δ/2, T + δ/2)`. -/
theorem window_of_mem {T δ : ℝ} {W p q n : ℕ} (hW : (0 : ℝ) < W)
    (hp : (p : ℝ) / W ∈ Ioo (T - δ / 2) (T + δ / 2))
    (hq : (q : ℝ) / W ∈ Ioo (T - δ / 2) (T + δ / 2)) (hδ : 0 < δ)
    (h1 : min p q ≤ n) (h2 : n < max p q) :
    (T - δ) * W ≤ n ∧ (n : ℝ) ≤ (T + δ) * W := by
  have hp1 : (T - δ / 2) * W < p := (lt_div_iff₀ hW).1 hp.1
  have hp2 : (p : ℝ) < (T + δ / 2) * W := (div_lt_iff₀ hW).1 hp.2
  have hq1 : (T - δ / 2) * W < q := (lt_div_iff₀ hW).1 hq.1
  have hq2 : (q : ℝ) < (T + δ / 2) * W := (div_lt_iff₀ hW).1 hq.2
  have hWδ : 0 ≤ δ / 2 * W := by positivity
  constructor
  · rcases min_le_iff.1 h1 with h | h
    · have : (p : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
    · have : (q : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  · rcases lt_max_iff.1 h2 with h | h
    · have : (n : ℝ) ≤ p := by exact_mod_cast h.le
      nlinarith
    · have : (n : ℝ) ≤ q := by exact_mod_cast h.le
      nlinarith

/-- **Length continuity** (`ComplexSourceLaw.LengthContinuity`) from the one-layer
bounds `LayerIncrementBounds`. -/
theorem lengthContinuity_of_layerIncrements (hL : LayerIncrementBounds) : LengthContinuity := by
  intro b E np τ m T hdom Wseq rseq hW hr r i k ε hε
  obtain ⟨δ, hδ, C, W₀, hB⟩ := hL b E np τ m T hdom
  obtain ⟨-, -, -, -, -, hτpos, -, hτT⟩ := hdom
  have hT : 0 < T := (hτpos i).trans (hτT i)
  set K := 2 * (16 / ε ^ 2 + 4 / ε) * C
  have hR := tendsto_floor_div Wseq hW hT.le
  have hdiff : Tendsto (fun j => |(rseq j : ℝ) / Wseq j -
      (⌊(Wseq j : ℝ) * T⌋₊ : ℝ) / Wseq j|) atTop (𝓝 0) := by
    simpa using (hr.sub hR).abs
  have hlim : Tendsto (fun j => ENNReal.ofReal (K * |(rseq j : ℝ) / Wseq j -
      (⌊(Wseq j : ℝ) * T⌋₊ : ℝ) / Wseq j|)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := K)).mul hdiff)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  have hI : Ioo (T - δ / 2) (T + δ / 2) ∈ 𝓝 T := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hr hI, hR hI, hW.eventually_ge_atTop (max W₀ 1)] with j hrj hRj hWj
  have hW1 : 1 ≤ Wseq j := le_of_max_le_right hWj
  have hW0 : (0 : ℝ) < Wseq j := by exact_mod_cast hW1
  have hb : ∀ n, min (rseq j) ⌊(Wseq j : ℝ) * T⌋₊ ≤ n →
      n < max (rseq j) ⌊(Wseq j : ℝ) * T⌋₊ → ∀ s : Bool, _ := fun n h1 h2 s =>
    hB (Wseq j) (le_of_max_le_left hWj) n (window_of_mem hW0 hrj hRj hδ h1 h2).1
      (window_of_mem hW0 hrj hRj hδ h1 h2).2 r i k s
  refine (measure_entry_sub_ge_le' b E τ m (Wseq j) r i k hε (rseq j)
    ⌊(Wseq j : ℝ) * T⌋₊ hb).trans (le_of_eq ?_)
  congr 1
  rw [← sub_div, abs_div, abs_of_pos hW0]
  simp only [K]
  field_simp

/-- **`ComplexSourceLimitSequenceContract`** from `LayerIncrementBounds`, through
`complexSourceLimitSequence_of`. -/
theorem complexSourceLimitSequence_holds (hL : LayerIncrementBounds) :
    ComplexSourceLimitSequenceContract :=
  complexSourceLimitSequence_of (lengthContinuity_of_layerIncrements hL)

end BlockBand.SourceProcess.LengthCont
