module

public import BlockBand.DeterminantScore.EigenDensityGT
public import BlockBand.DeterminantScore.WeylIntegrationInterlace

/-!
# Gelfand–Tsetlin patterns: peeling off the top row

The free coordinates of a pattern below a top row of length `n + 1` (`GTIndex (n + 1)`) split as
the row of length `n` directly below the top (`Fin n`) and the pattern below that row
(`GTIndex n`): `gtSplit n : Fin n ⊕ GTIndex n → GTIndex (n + 1)` is a bijection, and the induced
coordinate map `gtJoin n : (Fin n → ℝ) × (GTIndex n → ℝ) → (GTIndex (n + 1) → ℝ)` preserves
Lebesgue measure (`measurePreserving_gtJoin`). Under this splitting the entries, the interlacing
set and the row-sum increments of `(λ, gtJoin (μ, y))` are those of `(μ, y)` together with the
closed interlacing `λ_i ≤ μ_i ≤ λ_{i+1}` and the top increment `Σλ - Σμ`. Consequently the
marginal `gtMarginal k λ = ∫ 1_{GT}(λ, y) e^{Σ_r k_r d_r} dy` satisfies the recursion
(`gtMarginal_succ`)

`gtMarginal k λ = ∫_{λ_i ≤ μ_i ≤ λ_{i+1}} e^{k_n (Σλ - Σμ)} gtMarginal (k ∘ castSucc) μ dμ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.GelfandTsetlin

open MeasureTheory Matrix
open BlockBand.DeterminantScore.EigenDensity
open scoped ENNReal

variable {n : ℕ}

/-- The splitting of the pattern coordinates below a top row of length `n + 1`: `inl i` is entry
`i` of the row of length `n` (zero-based row `n - 1`), `inr q` is the coordinate `q` of the pattern
below it. -/
def gtSplit (n : ℕ) : Fin n ⊕ GTIndex n → GTIndex (n + 1)
  | .inl i => ⟨(⟨n - 1, by omega⟩, i.castSucc), by
      have := i.isLt
      refine ⟨?_, ?_⟩
      · rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega
      · simp only; omega⟩
  | .inr q => ⟨(q.1.1.castSucc, q.1.2.castSucc), by
      have h1 := q.2.1
      have h2 := q.2.2
      rw [Fin.le_def] at h1
      refine ⟨?_, ?_⟩
      · rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega
      · simp only [Fin.val_castSucc]; omega⟩

theorem gtSplit_inl_val (i : Fin n) :
    ((gtSplit n (.inl i)).1.1.val, (gtSplit n (.inl i)).1.2.val) = (n - 1, i.val) := rfl

theorem gtSplit_inr_val (q : GTIndex n) :
    ((gtSplit n (.inr q)).1.1.val, (gtSplit n (.inr q)).1.2.val) = (q.1.1.val, q.1.2.val) := rfl

theorem gtSplit_bijective : Function.Bijective (gtSplit n) := by
  constructor
  · rintro (i | q) (j | q')
    · intro h
      have := congrArg (fun z : GTIndex (n + 1) => z.1.2.val) h
      simp only [gtSplit, Fin.val_castSucc] at this
      rw [Fin.ext this]
    · intro h
      have := congrArg (fun z : GTIndex (n + 1) => z.1.1.val) h
      have h2 := q'.2.2
      simp only [gtSplit, Fin.val_castSucc] at this
      omega
    · intro h
      have := congrArg (fun z : GTIndex (n + 1) => z.1.1.val) h
      have h2 := q.2.2
      simp only [gtSplit, Fin.val_castSucc] at this
      omega
    · intro h
      have h1 := congrArg (fun z : GTIndex (n + 1) => z.1.1.val) h
      have h2 := congrArg (fun z : GTIndex (n + 1) => z.1.2.val) h
      simp only [gtSplit, Fin.val_castSucc] at h1 h2
      congr 1
      exact Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
  · rintro ⟨⟨r, i⟩, hri, hr⟩
    dsimp only at hri hr
    rw [Fin.le_def] at hri
    by_cases h : r.val + 1 < n
    · refine ⟨.inr ⟨(⟨r.val, by omega⟩, ⟨i.val, by omega⟩), by rw [Fin.le_def]; exact hri, h⟩, ?_⟩
      exact Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))
    · refine ⟨.inl ⟨i.val, by omega⟩, ?_⟩
      refine Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext rfl))
      simp only [gtSplit]
      omega

/-- The bijection `Fin n ⊕ GTIndex n ≃ GTIndex (n + 1)`. -/
def gtSplitEquiv (n : ℕ) : Fin n ⊕ GTIndex n ≃ GTIndex (n + 1) :=
  Equiv.ofBijective _ gtSplit_bijective

/-- The coordinate map `(μ, y) ↦` the pattern below a top row of length `n + 1` whose row of
length `n` is `μ` and whose lower part is `y`. -/
def gtJoin (n : ℕ) : (Fin n → ℝ) × (GTIndex n → ℝ) ≃ᵐ (GTIndex (n + 1) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ GTIndex n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : GTIndex (n + 1) => ℝ) (gtSplitEquiv n))

theorem measurePreserving_gtJoin : MeasurePreserving (gtJoin n) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : GTIndex (n + 1) => ℝ) (gtSplitEquiv n)).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ GTIndex n => ℝ))

theorem gtJoin_apply_split (p : (Fin n → ℝ) × (GTIndex n → ℝ)) (s : Fin n ⊕ GTIndex n) :
    gtJoin n p (gtSplit n s) = Sum.rec p.1 p.2 s := by
  have h : gtSplit n s = gtSplitEquiv n s := rfl
  rw [h]
  simp only [gtJoin, MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  rfl

theorem gtJoin_inl (p : (Fin n → ℝ) × (GTIndex n → ℝ)) (i : Fin n) :
    gtJoin n p (gtSplit n (.inl i)) = p.1 i :=
  gtJoin_apply_split p (.inl i)

theorem gtJoin_inr (p : (Fin n → ℝ) × (GTIndex n → ℝ)) (q : GTIndex n) :
    gtJoin n p (gtSplit n (.inr q)) = p.2 q :=
  gtJoin_apply_split p (.inr q)

/-!
## Entries
-/

/-- On the row of length `n` (zero-based row `n - 1`) the entries are those of `μ`. -/
theorem gtEntry_lastRow (p : (Fin n → ℝ) × (GTIndex n → ℝ)) (i : ℕ) (hi : i < n) :
    gtEntry p (n - 1) i = p.1 ⟨i, hi⟩ := by
  unfold gtEntry
  rw [dite_eq_right (by omega), dite_eq_left ⟨by omega, hi⟩]

/-- Rows strictly below the top row are those of `(μ, y)`. -/
theorem gtEntry_gtJoin_of_lt (lam : Fin (n + 1) → ℝ) (p : (Fin n → ℝ) × (GTIndex n → ℝ))
    {r : ℕ} (hr : r < n) (i : ℕ) :
    gtEntry (lam, gtJoin n p) r i = gtEntry p r i := by
  by_cases hi : i ≤ r
  · have hA : i ≤ r ∧ r + 1 < n + 1 := ⟨hi, by omega⟩
    unfold gtEntry
    rw [dite_eq_left hA]
    by_cases hr1 : r + 1 < n
    · rw [dite_eq_left ⟨hi, hr1⟩]
      have hq : (⟨(⟨r, by omega⟩, ⟨i, by omega⟩), Fin.mk_le_mk.2 hA.1, hA.2⟩ : GTIndex (n + 1)) =
          gtSplit n (.inr ⟨(⟨r, by omega⟩, ⟨i, by omega⟩), Fin.mk_le_mk.2 hi, hr1⟩) :=
        Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))
      rw [hq]; exact gtJoin_inr p _
    · rw [dite_eq_right (by omega), dite_eq_left ⟨by omega, by omega⟩]
      have hq : (⟨(⟨r, by omega⟩, ⟨i, by omega⟩), Fin.mk_le_mk.2 hA.1, hA.2⟩ : GTIndex (n + 1)) =
          gtSplit n (.inl ⟨i, by omega⟩) :=
        Subtype.ext (Prod.ext (Fin.ext (by simp only [gtSplit]; omega)) (Fin.ext rfl))
      rw [hq]; exact gtJoin_inl p _
  · unfold gtEntry
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega)]

/-- The top row is `λ`. -/
theorem gtEntry_top (lam : Fin (n + 1) → ℝ) (Y : GTIndex (n + 1) → ℝ) (i : ℕ) (hi : i < n + 1) :
    gtEntry (lam, Y) n i = lam ⟨i, hi⟩ := by
  unfold gtEntry
  rw [dite_eq_right (by omega), dite_eq_left ⟨rfl, hi⟩]

/-- The row of length `n` of `(λ, gtJoin (μ, y))` is `μ`. -/
theorem gtEntry_gtJoin_lastRow (lam : Fin (n + 1) → ℝ) (p : (Fin n → ℝ) × (GTIndex n → ℝ))
    (i : ℕ) (hi : i < n) : gtEntry (lam, gtJoin n p) (n - 1) i = p.1 ⟨i, hi⟩ := by
  rw [gtEntry_gtJoin_of_lt lam p (by omega), gtEntry_lastRow p i hi]

/-!
## The interlacing set and the increments
-/

/-- The closed interlacing box `∏_i [λ_i, λ_{i+1}]`. -/
def closedBox (lam : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun i => Set.Icc (lam i.castSucc) (lam i.succ)

theorem isClosed_closedBox (lam : Fin (n + 1) → ℝ) : IsClosed (closedBox lam) :=
  isClosed_set_pi fun _ _ => isClosed_Icc

theorem mem_GTSet_gtJoin (lam : Fin (n + 1) → ℝ) (p : (Fin n → ℝ) × (GTIndex n → ℝ)) :
    (lam, gtJoin n p) ∈ GTSet (n + 1) ↔ p ∈ GTSet n ∧ p.1 ∈ closedBox lam := by
  constructor
  · intro h
    refine ⟨fun r i hr hi => ?_, fun i _ => ?_⟩
    · have := h r i (by omega) hi
      simpa only [gtEntry_gtJoin_of_lt lam p hr, gtEntry_gtJoin_of_lt lam p (show r < n by omega)]
        using this
    · have hi := i.isLt
      have := h (n - 1) i (by omega) (by omega)
      rw [show n - 1 + 1 = n by omega, gtEntry_top lam _ i (by omega),
        gtEntry_top lam _ (i + 1) (by omega), gtEntry_gtJoin_lastRow lam p i hi] at this
      exact this
  · rintro ⟨h1, h2⟩ r i hr hi
    by_cases hr1 : r + 1 < n
    · simpa only [gtEntry_gtJoin_of_lt lam p hr1, gtEntry_gtJoin_of_lt lam p (show r < n by omega)]
        using h1 r i hr1 hi
    · have hrn : r = n - 1 := by omega
      subst hrn
      rw [show n - 1 + 1 = n by omega, gtEntry_top lam _ i (by omega),
        gtEntry_top lam _ (i + 1) (by omega), gtEntry_gtJoin_lastRow lam p i (by omega)]
      exact h2 ⟨i, by omega⟩ (Set.mem_univ _)

theorem gtDiag_gtJoin_castSucc (lam : Fin (n + 1) → ℝ) (p : (Fin n → ℝ) × (GTIndex n → ℝ))
    (r : Fin n) : gtDiag (lam, gtJoin n p) r.castSucc = gtDiag p r := by
  unfold gtDiag
  simp only [Fin.val_castSucc]
  have hr := r.isLt
  rw [Finset.sum_congr rfl fun i _ => gtEntry_gtJoin_of_lt lam p hr i,
    Finset.sum_congr rfl fun i _ => gtEntry_gtJoin_of_lt lam p (show r.val - 1 < n by omega) i]

theorem gtDiag_gtJoin_last (lam : Fin (n + 1) → ℝ) (p : (Fin n → ℝ) × (GTIndex n → ℝ)) :
    gtDiag (lam, gtJoin n p) (Fin.last n) = ∑ i, lam i - ∑ i, p.1 i := by
  unfold gtDiag
  simp only [Fin.val_last]
  rw [← Fin.sum_univ_eq_sum_range (fun i => gtEntry (lam, gtJoin n p) n i),
    ← Fin.sum_univ_eq_sum_range (fun i => gtEntry (lam, gtJoin n p) (n - 1) i)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => gtEntry_top lam _ i i.isLt
  · exact Finset.sum_congr rfl fun i _ => gtEntry_gtJoin_lastRow lam p i i.isLt

/-- The phase splits as the phase of `(μ, y)` plus `k_n (Σλ - Σμ)`. -/
theorem sum_gtDiag_gtJoin (k : Fin (n + 1) → ℝ) (lam : Fin (n + 1) → ℝ)
    (p : (Fin n → ℝ) × (GTIndex n → ℝ)) :
    ∑ r, k r * gtDiag (lam, gtJoin n p) r =
      ∑ r : Fin n, k r.castSucc * gtDiag p r + k (Fin.last n) * (∑ i, lam i - ∑ i, p.1 i) := by
  rw [Fin.sum_univ_castSucc]
  simp only [gtDiag_gtJoin_castSucc, gtDiag_gtJoin_last]

/-- The top factor `e^{k_n (Σλ - Σμ)}`. -/
def topWeight (c : ℝ) (lam : Fin (n + 1) → ℝ) (μ : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (c * (∑ i, lam i - ∑ i, μ i)))

theorem gtIntegrand_gtJoin (k : Fin (n + 1) → ℝ) (lam : Fin (n + 1) → ℝ)
    (p : (Fin n → ℝ) × (GTIndex n → ℝ)) :
    gtIntegrand k (lam, gtJoin n p) =
      (closedBox lam).indicator (topWeight (k (Fin.last n)) lam) p.1 *
        gtIntegrand (fun r => k r.castSucc) p := by
  classical
  unfold gtIntegrand
  by_cases hp : p ∈ GTSet n
  · by_cases hb : p.1 ∈ closedBox lam
    · have hm : (lam, gtJoin n p) ∈ GTSet (n + 1) := (mem_GTSet_gtJoin lam p).2 ⟨hp, hb⟩
      rw [ite_eq_left hm, ite_eq_left hp, Set.indicator_of_mem hb, topWeight, sum_gtDiag_gtJoin,
        Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
    · have hm : (lam, gtJoin n p) ∉ GTSet (n + 1) := fun h =>
        hb ((mem_GTSet_gtJoin lam p).1 h).2
      rw [ite_eq_right hm, Set.indicator_of_notMem hb, zero_mul]
  · have hm : (lam, gtJoin n p) ∉ GTSet (n + 1) := fun h => hp ((mem_GTSet_gtJoin lam p).1 h).1
    rw [ite_eq_right hm, ite_eq_right hp, mul_zero]

/-!
## The marginal and its recursion
-/

/-- The Gelfand–Tsetlin marginal `∫ 1_{GT}(λ, y) e^{Σ_r k_r d_r(λ, y)} dy`. -/
def gtMarginal {m : ℕ} (k : Fin m → ℝ) (lam : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ y : GTIndex m → ℝ, gtIntegrand k (lam, y)

theorem measurable_gtIntegrand_joint {m : ℕ} (k : Fin m → ℝ) :
    Measurable fun z : (Fin m → ℝ) × (GTIndex m → ℝ) => gtIntegrand k z := by
  classical
  unfold gtIntegrand
  refine Measurable.ite isClosed_GTSet.measurableSet ?_ measurable_const
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  refine Finset.measurable_sum _ fun r _ => measurable_const.mul ?_
  unfold gtDiag
  exact Continuous.measurable ((continuous_finsetSum _ fun i _ => continuous_gtEntry _ _).sub
    (continuous_finsetSum _ fun i _ => continuous_gtEntry _ _))

theorem measurable_gtMarginal {m : ℕ} (k : Fin m → ℝ) : Measurable (gtMarginal k) :=
  (measurable_gtIntegrand_joint k).lintegral_prod_right'

theorem measurable_topWeight (c : ℝ) :
    Measurable fun q : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => topWeight c q.1 q.2 := by
  unfold topWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Continuous.measurable ?_))
  fun_prop

theorem measurable_topWeight_right (c : ℝ) (lam : Fin (n + 1) → ℝ) :
    Measurable (topWeight c lam) := by
  unfold topWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Continuous.measurable ?_))
  fun_prop

/-- **Recursion of the Gelfand–Tsetlin marginal** over the row below the top. -/
theorem gtMarginal_succ (k : Fin (n + 1) → ℝ) (lam : Fin (n + 1) → ℝ) :
    gtMarginal k lam = ∫⁻ μ, (closedBox lam).indicator (topWeight (k (Fin.last n)) lam) μ *
      gtMarginal (fun r => k r.castSucc) μ := by
  unfold gtMarginal
  have hJ := (measurePreserving_gtJoin (n := n)).lintegral_comp_emb (gtJoin n).measurableEmbedding
    (fun Y => gtIntegrand k (lam, Y))
  rw [← hJ]
  simp_rw [gtIntegrand_gtJoin]
  have hm : Measurable fun p : (Fin n → ℝ) × (GTIndex n → ℝ) =>
      (closedBox lam).indicator (topWeight (k (Fin.last n)) lam) p.1 *
        gtIntegrand (fun r => k r.castSucc) p := by
    refine Measurable.mul ?_ (measurable_gtIntegrand_joint _)
    refine (Measurable.indicator ?_ (isClosed_closedBox lam).measurableSet).comp measurable_fst
    exact measurable_topWeight_right _ _
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun μ => ?_
  dsimp only
  rw [lintegral_const_mul _ (measurable_gtIntegrand _ μ)]

/-!
## Closed versus open interlacing boxes
-/

/-- Off finitely many coordinate hyperplanes `μ_i = λ_i`, `μ_i = λ_{i+1}` (a Lebesgue-null set). -/
theorem ae_ne_boxBoundary (lam : Fin (n + 1) → ℝ) :
    ∀ᵐ μ : Fin n → ℝ, ∀ i, μ i ≠ lam i.castSucc ∧ μ i ≠ lam i.succ := by
  have h1 : ∀ (i : Fin n) (c : ℝ), ∀ᵐ μ : Fin n → ℝ, μ i ≠ c := by
    intro i c
    rw [ae_iff]
    have hset : {a : Fin n → ℝ | ¬a i ≠ c} = Function.eval i ⁻¹' ({c} : Set ℝ) := by
      ext a; simp
    rw [hset, volume_pi]
    exact Measure.pi_eval_preimage_null _ Real.volume_singleton
  rw [ae_all_iff]
  intro i
  exact (h1 i _).and (h1 i _)

theorem mem_closedBox_iff_of_ne {lam : Fin (n + 1) → ℝ} {μ : Fin n → ℝ}
    (hμ : ∀ i, μ i ≠ lam i.castSucc ∧ μ i ≠ lam i.succ) :
    μ ∈ closedBox lam ↔ μ ∈ WeylIntegration.interlaceBox lam := by
  simp only [closedBox, WeylIntegration.interlaceBox, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc, Set.mem_Ioo]
  refine forall_congr' fun i => ?_
  obtain ⟨h1, h2⟩ := hμ i
  constructor
  · rintro ⟨a, b⟩; exact ⟨lt_of_le_of_ne a (Ne.symm h1), lt_of_le_of_ne b h2⟩
  · rintro ⟨a, b⟩; exact ⟨a.le, b.le⟩

/-- The integral over the closed box equals the integral over the open box. -/
theorem lintegral_closedBox_eq (lam : Fin (n + 1) → ℝ) (w φ : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ μ, (closedBox lam).indicator w μ * φ μ =
      ∫⁻ μ in WeylIntegration.interlaceBox lam, w μ * φ μ := by
  rw [← lintegral_indicator (WeylIntegration.measurableSet_interlaceBox lam)]
  refine lintegral_congr_ae ((ae_ne_boxBoundary lam).mono fun μ hμ => ?_)
  dsimp only
  by_cases h : μ ∈ closedBox lam
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((mem_closedBox_iff_of_ne hμ).1 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((mem_closedBox_iff_of_ne hμ).2 h')),
      zero_mul]

end BlockBand.DeterminantScore.GelfandTsetlin
