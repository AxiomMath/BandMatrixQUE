module

public import BlockBand.Transmission.Dual.GMonoClass
public import BlockBand.Transmission.Dual.GCPath

/-!
# Domination of the laws of stopped-path sequences on `𝒜`

Fix open sets `W n ⊆ ℝ^d` and `t₀`. A random sequence of continuous paths
`Φ : Ω → ℕ → CPath d` is a *stop sequence* (`IsStopSeq`) if a.s. `Φ k = pstop (W k) t₀ (Φ n)`
for `k ≤ n` (each path is the `n`-th one stopped earlier). Then the first `n + 1` paths are a
measurable function `stopTuple n` of the `n`-th one, so `law(Φ)` on the first `n + 1`
coordinates is determined by the law of the `n`-th path (`exists_map_finRestr_eq`). Hence
(`map_le_of_stopSeq`):

  if `P(Φ_n ∈ B) ≤ Σ_j c_j Q(Ψ^{(j)}_n ∈ B)` for every `n` and measurable path set `B`,
  then `law_P(Φ) ≤ Σ_j c_j law_Q(Ψ^{(j)})` as measures on `ℕ → CPath d`.

This is the domination inequality on the whole σ-algebra `𝒜 = σ(⋃ₙ 𝒜ₙ)`, with `𝒜ₙ` the
σ-algebra of the first `n + 1` stopped paths (`measure_le_of_forall_fin`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Set
open scoped NNReal ENNReal

variable {d : ℕ} {W : ℕ → Set (Fin d → ℝ)} {t₀ : ℝ≥0}

/-- `Φ` is a.s. a sequence of nested stopped paths. -/
def IsStopSeq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℕ → Set (Fin d → ℝ))
    (t₀ : ℝ≥0) (Φ : Ω → ℕ → CPath d) : Prop :=
  ∀ k n, k ≤ n → ∀ᵐ x ∂P, Φ x k = pstop (W k) t₀ (Φ x n)

/-- The first `n + 1` stopped paths of a path. -/
def stopTuple (W : ℕ → Set (Fin d → ℝ)) (t₀ : ℝ≥0) (n : ℕ) (w : CPath d) :
    Fin (n + 1) → CPath d := fun k => pstop (W k) t₀ w

theorem measurable_stopTuple (hW : ∀ n, IsOpen (W n)) (n : ℕ) :
    Measurable (stopTuple W t₀ n) :=
  measurable_pi_iff.2 fun k => measurable_pstop (hW k) t₀

theorem IsStopSeq.ae_finRestr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : Ω → ℕ → CPath d} (h : IsStopSeq P W t₀ Φ) (n : ℕ) :
    ∀ᵐ x ∂P, finRestr n (Φ x) = stopTuple W t₀ n (Φ x n) := by
  have hk : ∀ k : Fin (n + 1), ∀ᵐ x ∂P, Φ x k = pstop (W k) t₀ (Φ x n) := fun k =>
    h k n (Nat.lt_succ_iff.1 k.2)
  filter_upwards [ae_all_iff.2 hk] with x hx
  funext k; exact hx k

/-- A measurable set of continuous paths is the trace of a measurable set of paths. -/
theorem exists_trace {S : Set (CPath d)} (hS : MeasurableSet S) :
    ∃ B : Set (ℝ≥0 → Fin d → ℝ), MeasurableSet B ∧ Subtype.val ⁻¹' B = S := hS

/-- **The law of a stop sequence on the first `n + 1` paths** is read off its `n`-th path:
for every measurable `B` there is a measurable path set `B'` (depending only on `W, t₀, n, B`)
with `law(Φ)(finRestr n ∈ B) = P(Φ_n ∈ B')` for every stop sequence. -/
theorem exists_map_finRestr_eq (hW : ∀ n, IsOpen (W n)) (n : ℕ)
    {B : Set (Fin (n + 1) → CPath d)} (hB : MeasurableSet B) :
    ∃ B' : Set (ℝ≥0 → Fin d → ℝ), MeasurableSet B' ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Φ : Ω → ℕ → CPath d},
        Measurable Φ → IsStopSeq P W t₀ Φ →
        P.map Φ (finRestr n ⁻¹' B) = P {x | (Φ x n).1 ∈ B'} := by
  obtain ⟨B', hB', he⟩ := exists_trace (measurable_stopTuple (t₀ := t₀) hW n hB)
  refine ⟨B', hB', fun {Ω} _ {P} {Φ} hΦ hs => ?_⟩
  rw [Measure.map_apply hΦ (measurable_finRestr n hB)]
  refine measure_congr ?_
  filter_upwards [hs.ae_finRestr n] with x hx
  change (finRestr n (Φ x) ∈ B) = ((Φ x n).1 ∈ B')
  rw [hx]
  change (Φ x n ∈ stopTuple W t₀ n ⁻¹' B) = (Φ x n ∈ Subtype.val ⁻¹' B')
  rw [he]

theorem isFiniteMeasure_sum_smul {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    {c : ι → ℝ≥0∞} (hc : ∀ j, c j ≠ ⊤) (ν : ι → Measure X) [∀ j, IsFiniteMeasure (ν j)] :
    IsFiniteMeasure (∑ j, c j • ν j) := by
  refine ⟨?_⟩
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (hc j).lt_top (measure_lt_top _ _)

/-- **Domination on the whole σ-algebra**: domination of the `n`-th stopped paths for every
`n` gives domination of the laws of the stop sequences on `ℕ → CPath d`. -/
theorem map_le_of_stopSeq {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ι : Type*}
    [Fintype ι] {P : Measure Ω} [IsFiniteMeasure P] {Q : Measure Ω'} [IsFiniteMeasure Q]
    (hW : ∀ n, IsOpen (W n)) {Φ : Ω → ℕ → CPath d} {Ψ : ι → Ω' → ℕ → CPath d}
    (hΦ : Measurable Φ) (hΨ : ∀ j, Measurable (Ψ j)) (sΦ : IsStopSeq P W t₀ Φ)
    (sΨ : ∀ j, IsStopSeq Q W t₀ (Ψ j)) {c : ι → ℝ≥0∞} (hc : ∀ j, c j ≠ ⊤)
    (h : ∀ (n : ℕ) (B : Set (ℝ≥0 → Fin d → ℝ)), MeasurableSet B →
      P {x | (Φ x n).1 ∈ B} ≤ ∑ j, c j * Q {x | (Ψ j x n).1 ∈ B}) :
    P.map Φ ≤ ∑ j, c j • Q.map (Ψ j) := by
  have := isFiniteMeasure_sum_smul hc fun j => Q.map (Ψ j)
  refine measure_le_of_forall_fin fun n B hB => ?_
  obtain ⟨B', hB', hE⟩ := exists_map_finRestr_eq (t₀ := t₀) hW n hB
  rw [hE hΦ sΦ, Measure.coe_finsetSum, Finset.sum_apply]
  refine (h n B' hB').trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [Measure.smul_apply, smul_eq_mul, hE (hΨ j) (sΨ j)]

end BlockBand.Transmission.Dual.G
