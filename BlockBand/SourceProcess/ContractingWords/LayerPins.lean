module

public import BlockBand.SourceProcess.ContractingWords.LayerFresh
public import BlockBand.SourceProcess.ContractingWords.SummedPins
public import BlockBand.SourceProcess.ContractingWords.PathStep

/-!
# The one-layer drift and covariance of ordinary words

This file defines the contracting products, the one-layer error scales, and the one-layer drift
and covariance bounds `LayerDrift`, `LayerCov` of ordinary words.

Data, as in `LayerFreshBound`: Hermitian old letters `A_ℓ` with `Tr|A_ℓ| ≤ K`, the current
letter equal to the current of `𝕏` (`A_J = currentOf 𝕏 = 𝕊*P𝕊 - P`, as along the path), interval
tests `|q_a| ≤ c₀` with the injection weights `injCoef q W j` (`q_a((j+1)/W)/W²`), the fresh
transport `N`, new block row `D` and new separators; `old v = Tr v(𝕏)` (`coreProd A (sepOf 𝕏) [v]`)
and `new v` (`newWord`). The error scale is `e = δ₀ + δ₁ + g/W + W⁻¹` at `X = nearSchur z 𝕏`.

* `LayerDrift`: `|E new w - old w - W⁻¹(drift_w + inj_w(t))(old)| ≤
  C e Σ_{Z ∈ contrDrift w}|old Z| + C(W^{-3/2} + e² + e^{2d+4})`, `t = (j+1)/W`.
* `LayerCov`: `|E(new w - old w)(new v - old v) - W⁻¹cov_{w,v}(old)| ≤
  C e Σ_{Z ∈ contrCov w v}|old Z| + C(W^{-3/2} + e² + e^{2d+4})`.

The contracting products: `contrOne w` replaces one separator by a contracting
letter (the Ward mean `-(2iη)⁻¹ΩP𝕊 + h.c.` paired with the old letters, coefficient `Ω = O(δ₀ + W⁻²)`);
`contrTwo w` are the two cycles `Tr(M σ)Tr(N σ')` of a within-word pair contracted against the
same-sign tensors `σ₋P𝕊 ⊗ P𝕊/(4η²W)` (coefficient `O(W⁻¹)`); `contrCov w v` is the one cycle
`Tr(MσNσ')` of a cross pair. Every such product is admitted, has a contracting letter and degree
`|w|` (resp. `|w| + |v|`): `contrDrift_facts`, `contrCov_facts`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge
open scoped ENNReal Matrix

variable {nT nI : ℕ}

/-- The four contracting separators `P𝕊, 𝕊*P, P𝕊P, P𝕊*P`. -/
def contrSeps : List Separator := [.projS, .sStarProj, .projSProj, .projSStarProj]

theorem contrSeps_count {σ : Separator} (h : σ ∈ contrSeps) : 1 ≤ σ.unconj + σ.conj := by
  simp only [contrSeps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp [Separator.unconj, Separator.conj]

/-- Replace the separator after letter `p`. -/
def setSepAt (w : TraceWord nT nI) (p : ℕ) (σ : Separator) : TraceWord nT nI :=
  w.modify p fun x => (x.1, σ)

/-- The two segments of a pair `i < j` of separators (as in `pairTerm`). -/
def pairS₁ (w : TraceWord nT nI) (i j : ℕ) : TraceWord nT nI :=
  (w.rotate (j + 1)).take (w.length - (j - i))

/-- The second segment. -/
def pairS₂ (w : TraceWord nT nI) (i j : ℕ) : TraceWord nT nI :=
  (w.rotate (i + 1)).take (j - i)

/-- One separator made contracting. -/
def contrOne (w : TraceWord nT nI) : List (List (TraceWord nT nI)) :=
  (List.range w.length).flatMap fun p => contrSeps.map fun σ => [setSepAt w p σ]

/-- Two cycles of a within-word pair, each closed by a contracting letter. -/
def contrTwo (w : TraceWord nT nI) : List (List (TraceWord nT nI)) :=
  (List.range w.length).flatMap fun j => (List.range j).flatMap fun i =>
    contrSeps.flatMap fun σ => contrSeps.map fun σ' =>
      [setLastSep (pairS₁ w i j) σ, setLastSep (pairS₂ w i j) σ']

/-- The contracting products of the first conditional increment. -/
def contrDrift (w : TraceWord nT nI) : List (List (TraceWord nT nI)) := contrOne w ++ contrTwo w

/-- The contracting products of the second conditional increment of a pair of words. -/
def contrCov (w v : TraceWord nT nI) : List (List (TraceWord nT nI)) :=
  (List.range w.length).flatMap fun i => (List.range v.length).flatMap fun j =>
    contrSeps.flatMap fun σ => contrSeps.map fun σ' =>
      [setLastSep (w.rotate (i + 1)) σ ++ setLastSep (v.rotate (j + 1)) σ']

/-- The current `J = 𝕊*P𝕊 - P` of an old two-port (`P' = P + J`, `g = ½ Tr J²`). -/
def currentOf (b E : ℝ) {W : ℕ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX - nearProjection W

/-- The one-layer error scale `e = δ₀ + δ₁ + g/W + W⁻¹`. -/
def layerErr (b E : ℝ) (s : ℂ) {W : ℕ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  jetDistance0 b E (nearSchur (boundaryZ b E) XX) +
    jetDistance1 b E s (nearSchur (boundaryZ b E) XX) +
    conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) / W + (W : ℝ)⁻¹

/-- The one-layer remainder scale `W^{-3/2} + e² + e^{2d+4}`. -/
def layerRem (W d : ℕ) (e : ℝ) : ℝ := (W : ℝ)⁻¹ / Real.sqrt W + e ^ 2 + e ^ (2 * d + 4)

/-- The new value of one word at one fresh layer. -/
abbrev layerNew (b E : ℝ) {W : ℕ} (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : TraceLetter nT nI → ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (w : TraceWord nT nI) (y : LayerSample W .oneBlockOnePort) : ℂ :=
  newWord A c (freshTransport b E XX y) (freshD b E XX y) (sepOf b E (freshTwoPortSchur E XX y)) w

/-- **The one-layer drift of an ordinary word.** -/
def LayerDrift : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (d : ℕ) (K c₀ : ℝ), 0 ≤ K → 0 ≤ c₀ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (q : Fin nI → ℝ → ℝ) (j : ℕ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        A .current = currentOf b E XX → (∀ a x, |q a x| ≤ c₀) →
      ∀ w : TraceWord nT nI, IsOrdinaryWord w → w.length ≤ d →
        ‖∫ y, layerNew b E A (injCoef q W j) XX w y ∂freshLaw W b -
            coreProd A (sepOf b E XX) [w] - (W : ℂ)⁻¹ *
              MvPolynomial.eval (fun v => coreProd A (sepOf b E XX) [v])
                (wordDrift (transportD0 b E) w +
                  MvPolynomial.C (wordInjection b q (stepTime W j) w))‖ ≤
          C * layerErr b E s XX *
              ((contrDrift w).map fun Zs => ‖coreProd A (sepOf b E XX) Zs‖).sum +
            C * layerRem W d (layerErr b E s XX)

/-- **The one-layer covariance of two ordinary words.** -/
def LayerCov : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ (d : ℕ) (K c₀ : ℝ), 0 ≤ K → 0 ≤ c₀ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ (nT nI : ℕ) (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (q : Fin nI → ℝ → ℝ) (j : ℕ), (∀ ℓ, (A ℓ).IsHermitian) → (∀ ℓ, nuclearNorm (A ℓ) ≤ K) →
        A .current = currentOf b E XX → (∀ a x, |q a x| ≤ c₀) →
      ∀ w v : TraceWord nT nI, IsOrdinaryWord w → IsOrdinaryWord v → w.length ≤ d →
        v.length ≤ d →
        ‖∫ y, (layerNew b E A (injCoef q W j) XX w y - coreProd A (sepOf b E XX) [w]) *
              (layerNew b E A (injCoef q W j) XX v y - coreProd A (sepOf b E XX) [v])
              ∂freshLaw W b - (W : ℂ)⁻¹ *
              MvPolynomial.eval (fun u => coreProd A (sepOf b E XX) [u])
                (wordCov (transportD0 b E) w v)‖ ≤
          C * layerErr b E s XX *
              ((contrCov w v).map fun Zs => ‖coreProd A (sepOf b E XX) Zs‖).sum +
            C * layerRem W d (layerErr b E s XX)

/-!
### Combinatorics of the contracting products
-/

theorem length_setLastSep (w : TraceWord nT nI) (σ : Separator) :
    (setLastSep w σ).length = w.length := by
  rcases List.eq_nil_or_concat w with h | ⟨L, x, rfl⟩
  · subst h; rfl
  · simp [setLastSep]

theorem count_setLastSep {w : TraceWord nT nI} (hw : w ≠ []) {σ : Separator}
    (hσ : σ ∈ contrSeps) :
    1 ≤ ((setLastSep w σ).map fun x => x.2.unconj).sum +
      ((setLastSep w σ).map fun x => x.2.conj).sum := by
  obtain ⟨L, x, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
  have := contrSeps_count hσ
  rw [List.concat_eq_append]
  simp [setLastSep]
  omega

theorem count_setSepAt {w : TraceWord nT nI} {p : ℕ} (hp : p < w.length) {σ : Separator}
    (hσ : σ ∈ contrSeps) :
    1 ≤ ((setSepAt w p σ).map fun x => x.2.unconj).sum +
      ((setSepAt w p σ).map fun x => x.2.conj).sum := by
  have hmem : (w[p].1, σ) ∈ setSepAt w p σ := by
    rw [setSepAt, List.mem_iff_getElem]
    exact ⟨p, by simpa using hp, by simp⟩
  have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => x.2.unconj) hmem)
  have h2 := List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => x.2.conj) hmem)
  have := contrSeps_count hσ
  simp only at h1 h2
  omega

end BlockBand.SourceProcess.ContractingWords
