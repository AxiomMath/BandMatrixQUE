module

public import BlockBand.SourceProcess.ComplexUnique.Rank

/-!
# Rank facts on a birth-free segment

`RankProp k g T`: no creation and no loss of the `k`-th principal minor sums of `B` and `M - B`
along the path `g`, from time `0` to the times in `T`.
**`rank_segment`**: for a born Gram solution with deterministic births and no birth in
`(a, a + h)`, a.s. `RankProp k (u ↦ G(a + u)) {u < h}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornStopped
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.BornRestart
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable {c : Type} [Fintype c] [DecidableEq c]

/-- No rank creation and no rank loss along `g` from `0` to the times in `T`. -/
def RankProp (k : ℕ) (g : ℝ≥0 → GramState c) (T : Set ℝ≥0) : Prop :=
  (principalMinorSum k (g 0).2 = 0 → ∀ t ∈ T, principalMinorSum k (g t).2 = 0) ∧
  (0 < principalMinorSum k (g 0).2 → ∀ t ∈ T, 0 < principalMinorSum k (g t).2) ∧
  (principalMinorSum k ((g 0).1 - (g 0).2) = 0 →
    ∀ t ∈ T, principalMinorSum k ((g t).1 - (g t).2) = 0) ∧
  (0 < principalMinorSum k ((g 0).1 - (g 0).2) →
    ∀ t ∈ T, 0 < principalMinorSum k ((g t).1 - (g t).2))

theorem RankProp.congr {k : ℕ} {g g' : ℝ≥0 → GramState c} {T T' : Set ℝ≥0}
    (h : RankProp k g T) (hT : T' ⊆ T) (h0 : g' 0 = g 0) (hg : ∀ t ∈ T', g' t = g t) :
    RankProp k g' T' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun h0' t ht => ?_, fun h0' t ht => ?_, fun h0' t ht => ?_, fun h0' t ht => ?_⟩ <;>
    rw [h0] at h0' <;> rw [hg t ht]
  · exact h1 h0' t (hT ht)
  · exact h2 h0' t (hT ht)
  · exact h3 h0' t (hT ht)
  · exact h4 h0' t (hT ht)

theorem RankProp.iUnion {k : ℕ} {g : ℝ≥0 → GramState c} {T : ℕ → Set ℝ≥0}
    (h : ∀ n, RankProp k g (T n)) : RankProp k g (⋃ n, T n) := by
  refine ⟨fun h0 t ht => ?_, fun h0 t ht => ?_, fun h0 t ht => ?_, fun h0 t ht => ?_⟩ <;>
    obtain ⟨n, hn⟩ := mem_iUnion.1 ht
  · exact (h n).1 h0 t hn
  · exact (h n).2.1 h0 t hn
  · exact (h n).2.2.1 h0 t hn
  · exact (h n).2.2.2 h0 t hn

variable {F : Type} [Fintype F] {D0 : ℝ} {D : Matrix c c ℂ} {j : F → GramState c} {β0 : F → ℝ}
  {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {G : ℝ≥0 → Ω → GramState c}

/-- The rank facts up to a fixed `r < h`. -/
theorem rank_segment_le (hD0 : 0 < D0) (hD : IsSignature D)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t _ => birthSum j β0 (t : ℝ)) G) {a r : ℝ≥0}
    (hnb : ∀ f, β0 f - a ≤ 0 ∨ (r : ℝ) < β0 f - a) (k : ℕ) :
    ∀ᵐ ω ∂Q, RankProp k (fun u => G (a + u) ω) (Iic r) := by
  obtain ⟨𝓗, H, -, hH, hHG⟩ := bornRestart_holds c F D0 D j (fun _ => a) measurable_const Ω _ 𝓖 Q
    (fun _ => β0) G inferInstance measurable_const hG
  have hHor := isGramHorizonSolution_tilde (β := fun _ f => β0 f - a) hH MeasurableSet.univ
    (by simp) (fun _ _ f => hnb f)
  rw [cond_univ] at hHor
  obtain ⟨W, _, ν, _, 𝓕, Ĝ, hĜ, hĜeq⟩ := exists_global_extension hD0 hD hHor
  have hR := rank_global hD0 hD hĜ k
  have hR' : ∀ᵐ x ∂(Q.prod ν), RankProp k (fun t => tildeG j (fun _ f => β0 f - a) H t x.1)
      (Iic r) := by
    filter_upwards [hR] with x h
    have h' : RankProp k (fun t => Ĝ t x) univ := ⟨fun h0 t _ => h.1 h0 t,
      fun h0 t _ => h.2.1 h0 t, fun h0 t _ => h.2.2.1 h0 t, fun h0 t _ => h.2.2.2 h0 t⟩
    exact RankProp.congr (g := fun t => Ĝ t x) h' (subset_univ _) (hĜeq 0 zero_le x).symm
      fun t ht => (hĜeq t ht x).symm
  filter_upwards [ae_of_ae_prod_fst (P := fun ω => RankProp k
    (fun t => tildeG j (fun _ f => β0 f - a) H t ω) (Iic r)) hR', hHG] with ω h hω
  refine RankProp.congr h subset_rfl ?_ fun t ht => ?_
  · rw [tildeG_eq (fun f => hnb f) zero_le, hω, add_zero]
  · rw [tildeG_eq (fun f => hnb f) ht, hω]

/-- **No rank creation and no rank loss on a birth-free segment.** -/
theorem rank_segment (hD0 : 0 < D0) (hD : IsSignature D)
    (hG : IsBornGramSolution Q 𝓖 D0 D (fun t _ => birthSum j β0 (t : ℝ)) G) {a h : ℝ≥0}
    (hnb : ∀ f, β0 f ≤ a ∨ ((a + h : ℝ≥0) : ℝ) ≤ β0 f) (k : ℕ) :
    ∀ᵐ ω ∂Q, RankProp k (fun u => G (a + u) ω) (Iio h) := by
  rcases eq_or_ne h 0 with rfl | h0
  · refine Eventually.of_forall fun ω => ?_
    refine ⟨fun _ t ht => absurd (mem_Iio.1 ht) (not_lt_of_ge zero_le), fun _ t ht => absurd (mem_Iio.1 ht) (not_lt_of_ge zero_le),
      fun _ t ht => absurd (mem_Iio.1 ht) (not_lt_of_ge zero_le), fun _ t ht => absurd (mem_Iio.1 ht) (not_lt_of_ge zero_le)⟩
  set r : ℕ → ℝ≥0 := fun n => h * n / (n + 1)
  have hr : ∀ n, r n < h := fun n => by
    have hn : (0 : ℝ≥0) < n + 1 := by positivity
    show h * n / (n + 1) < h
    rw [div_lt_iff₀ hn]
    exact mul_lt_mul_of_pos_left (lt_add_one _) (pos_iff_ne_zero.2 h0)
  have hcover : Iio h ⊆ ⋃ n, Iic (r n) := fun u hu => by
    have hu' : (u : ℝ) < h := hu
    obtain ⟨n, hn⟩ := exists_nat_ge ((u : ℝ) / ((h : ℝ) - u))
    refine mem_iUnion.2 ⟨n, ?_⟩
    show u ≤ h * n / (n + 1)
    rw [le_div_iff₀ (by positivity)]
    have hpos : (0 : ℝ) < (h : ℝ) - u := by linarith
    rw [div_le_iff₀ hpos] at hn
    rw [← NNReal.coe_le_coe]; push_cast; nlinarith
  have hall := ae_all_iff.2 fun n => rank_segment_le hD0 hD hG (a := a) (r := r n) (fun f => by
    rcases hnb f with h1 | h1
    · left; linarith
    · right
      have : (r n : ℝ) < h := hr n
      push_cast at h1; linarith) k
  filter_upwards [hall] with ω h
  exact (RankProp.iUnion h).congr hcover rfl fun _ _ => rfl

end BlockBand.SourceProcess.ComplexUnique
