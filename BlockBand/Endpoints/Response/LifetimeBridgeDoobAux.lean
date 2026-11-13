module

public import BlockBand.Endpoints.Response.LifetimeBridgeSplit

/-!
# Auxiliary lemmas for the H-transform law

These lemmas are used to prove `LbkHTransformLaw` from the corner heat identity and the Doob killed
law; they need no further hypothesis.

* `lbk_extinction_pos_ae_of_dualProcess`: `σ₀ > 0` almost surely for a boundary dual process.
* `lbk_strictMono_snoc`, `lbk_lastTime_snoc`, `lbk_fddProd_snoc`: appending one later time
  `r > t_k` to the time string, and the factorisation
  `Π_{k+1}(t, r)(zs, w) = Π_k(t)(zs) · p_{r - t_k}(z_k, w)`;
* `lbk_measure_ext_Iic_rect`: two measures on `α × ℝ`, the first finite, that agree on all
  rectangles `A ×ˢ Iic r` (`A` measurable) are equal (`Measure.ext_prod` and, for each `A`,
  `Measure.ext_of_Iic` on the second marginal of the restriction to `A ×ˢ univ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### `σ₀ > 0` from the start and right-continuity of the paths
-/

/-- **`σ₀ > 0` a.s. from the fields `start` and `rightCont` alone**: for every boundary dual
realization with `p ≥ 1` pairs, `N₀ = p ≠ 0` (`start`) and the level path is right
continuous at `0` (`IsBoundaryDeletionPath.rightCont`), so `N = p` on some `[0, ε)` and the
lifetime `dualExtinction N ≥ ε > 0`.
-/
theorem lbk_extinction_pos_ae_of_dualProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {p : ℕ} (hp : 0 < p)
    {x y : Fin p → ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    (hP : IsBoundaryDualProcess P 𝓖 D0 x y N X Y) :
    ∀ᵐ ω ∂P, 0 < dualExtinction N ω := by
  filter_upwards [hP.start, hP.paths] with ω h0 hω
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hω.rightCont 0)
  refine lt_of_lt_of_le (ENNReal.coe_pos.2 hε) (le_iInf₂ fun t ht => ?_)
  by_contra hlt
  have hlt' : t < ε := ENNReal.coe_lt_coe.1 (not_le.1 hlt)
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h | h
  · subst h
    rw [h0.1] at ht
    exact hp.ne' ht
  · have hN : N t ω = N 0 ω := hsub ⟨h, hlt'⟩
    rw [ht, h0.1] at hN
    exact hp.ne' hN.symm

/-!
### Appending a later time
-/

theorem lbk_lastTime_snoc {k : ℕ} (ts : Fin k → ℝ) (r : ℝ) :
    lbkLastTime (Fin.snoc ts r : Fin (k + 1) → ℝ) = r := by
  simp only [lbkLastTime, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

theorem lbk_strictMono_snoc {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) {r : ℝ}
    (hr : 0 < r) (hTr : lbkLastTime ts < r) : StrictMono (Fin.snoc ts r : Fin (k + 1) → ℝ) := by
  have hlt : ∀ i, ts i < r := (lbk_forall_lt_iff hts hr).2 hTr
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast i => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hlt i
  | cast j =>
    induction a using Fin.lastCases with
    | last => exact absurd ((Fin.castSucc_lt_last j).trans hab) (lt_irrefl _)
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact hts (Fin.castSucc_lt_castSucc_iff.1 hab)

theorem lbk_snoc_pos {k : ℕ} {ts : Fin k → ℝ} (htp : ∀ i, 0 < ts i) {r : ℝ} (hr : 0 < r) :
    ∀ i, 0 < (Fin.snoc ts r : Fin (k + 1) → ℝ) i := by
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hr
  | cast i => simpa only [Fin.snoc_castSucc] using htp i

theorem lbk_lastPoint_snoc {α : Type*} (z : α) {k : ℕ} (zs : Fin k → α) (w : α) :
    lbkLastPoint z (Fin.snoc zs w : Fin (k + 1) → α) = w := by
  simp only [lbkLastPoint, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

/-- The string of transition densities with one appended time `r` and point `w` factorises:
`Π_{k+1}(t, r)(zs, w) = Π_k(t)(zs) · p_{r - t_k}(z_k, w)`. -/
theorem lbk_fddProd_snoc {α : Type*} (p : ℝ → α → α → ℝ) (z : α) {k : ℕ} (ts : Fin k → ℝ)
    (r : ℝ) (zs : Fin k → α) (w : α) :
    lbkFddProd p z (Fin.snoc ts r : Fin (k + 1) → ℝ) (Fin.snoc zs w : Fin (k + 1) → α) =
      lbkFddProd p z ts zs * ENNReal.ofReal (p (r - lbkLastTime ts) (lbkLastPoint z zs) w) := by
  unfold lbkFddProd lbkLastTime lbkLastPoint
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last]

/-!
### Uniqueness of measures on `α × ℝ` from rectangles `A × Iic r`
-/

/-- Two measures on `α × ℝ`, the first finite, that agree on every rectangle `A ×ˢ Iic r` with
`A` measurable are equal. -/
theorem lbk_measure_ext_Iic_rect {α : Type*} [MeasurableSpace α] {μ ν : Measure (α × ℝ)}
    [IsFiniteMeasure μ]
    (h : ∀ A : Set α, MeasurableSet A → ∀ r : ℝ, μ (A ×ˢ Iic r) = ν (A ×ˢ Iic r)) : μ = ν := by
  have hrect : ∀ (A : Set α) (B : Set ℝ), MeasurableSet A → MeasurableSet B →
      ∀ ρ : Measure (α × ℝ), ((ρ.restrict (A ×ˢ univ)).map Prod.snd) B = ρ (A ×ˢ B) := by
    intro A B hA hB ρ
    rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 1
    ext q
    simp [and_comm]
  refine Measure.ext_prod fun {A B} hA hB => ?_
  have hμν : (μ.restrict (A ×ˢ univ)).map Prod.snd = (ν.restrict (A ×ˢ univ)).map Prod.snd := by
    refine Measure.ext_of_Iic _ _ fun r => ?_
    rw [hrect A _ hA measurableSet_Iic, hrect A _ hA measurableSet_Iic, h A hA r]
  rw [← hrect A B hA hB μ, ← hrect A B hA hB ν, hμν]

end BlockBand.Endpoints
