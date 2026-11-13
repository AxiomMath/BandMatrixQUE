module

public import BlockBand.Native.ErdosRiabov.Psi.Tau

/-!
# Closed a-priori form and hitting property of `τ`

The stopping time `τ` is a real time in `[0,1]`, the excess process is negative before it, and at
`τ < 1` some control quantity reaches its threshold. The setting is the VS band process
`H_t = VS.vsBandFin p t` on `RingSample p`; all statements hold for every sample (no law is used).
Hypotheses: `N, W ≥ 1`, `Im z > 0`, `S` stochastic symmetric.

* `tau_le_one`, `tau_ne_top`, `exists_coe_eq_tau`: `τ ≤ 1`, so `τ = (t : WithTop ℝ≥0)` for a
  real time `t ∈ [0,1]`.
* `excessProc_neg_of_lt_tau`: `excessProc s x < 0` for every `s < τ` (no `s ≤ 1` needed).
* `bigPsi_le_of_le_tau` (closed form): for `0 < t ≤ τ`, `Ψ^iso_{k,t}(H_t) ≤ ψ^iso_k` and
  `Ψ^av_{k,t}(H_t) ≤ ψ^av_k` for all `k ∈ [1,K]`, by the limit from the left;
  `ratio_le_of_le_tau`: the same for every pattern and all sites. `bigPsi_le_of_le_tau_of_zero`
  covers all `t ≤ τ` under the hypothesis `Split.ZeroStatement` and positive thresholds.
* **`exists_ge_at_tau`** (hitting property): if `τ < 1`, then `τ = t` for a real
  `t < 1` and some `k ∈ [1,K]` has `ψ^iso_k ≤ Ψ^iso_{k,t}(H_t)` or `ψ^av_k ≤ Ψ^av_{k,t}(H_t)`
  (the infimum of the closed hit set is attained, `IsClosed.csInf_mem`);
  `exists_ratio_ge_at_tau`: for positive thresholds, a pattern and sites realize it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Psi

open MeasureTheory Filter Topology Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {N : ℕ}

/-- `excess ≤ 0` iff all control quantities are at most their thresholds. -/
theorem PsiData.excess_nonpos_iff (P : PsiData N) (psiI psiA : ℕ → ℝ) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    P.excess psiI psiA t H ≤ 0 ↔
      ∀ k ∈ kRange, P.bigPsiIso k t H ≤ psiI k ∧ P.bigPsiAv k t H ≤ psiA k := by
  unfold PsiData.excess
  rw [Finset.sup'_le_iff]
  simp only [max_le_iff, sub_nonpos]

variable {p : BlockBand.Parameters}

theorem tau_le_one (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    tau p P psiI psiA x ≤ ((1 : ℝ≥0) : WithTop ℝ≥0) :=
  min_le_right _ _

theorem tau_ne_top (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    tau p P psiI psiA x ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (tau_le_one P psiI psiA x)

/-- `τ` is a real time in `[0,1]`. -/
theorem exists_coe_eq_tau (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    ∃ t : ℝ≥0, (t : WithTop ℝ≥0) = tau p P psiI psiA x ∧ t ≤ 1 := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (tau_ne_top P psiI psiA x)
  refine ⟨t, ht, ?_⟩
  have h := tau_le_one P psiI psiA x
  rw [← ht] at h
  exact WithTop.coe_le_coe.mp h

/-- Before `τ` the excess process is negative (every `s`, also `s > 1`). -/
theorem excessProc_neg_of_lt_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W)
    (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ)
    (x : RingSample p) {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < tau p P psiI psiA x) :
    excessProc p P psiI psiA s x < 0 := by
  by_contra hc
  rw [not_lt] at hc
  have hle : hitTime (Ici (0 : ℝ)) (excessProc p P psiI psiA) x ≤ s := iInf₂_le s hc
  rw [tau_eq_hitTime hN hW hz hS psiI psiA x] at hs
  exact absurd (lt_of_lt_of_le hs ((min_le_left _ _).trans hle)) (lt_irrefl _)

/-- **Closed a-priori form**: for `0 < t ≤ τ` (hence `t ≤ 1`), every control quantity
is at most its threshold:
`Ψ^iso_{k,t}(H_t) ≤ ψ^iso_k`, `Ψ^av_{k,t}(H_t) ≤ ψ^av_k`,
`1 ≤ k ≤ K`.
Pathwise, every sample.
-/
theorem bigPsi_le_of_le_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (x : RingSample p)
    {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    ∀ k ∈ kRange, P.bigPsiIso k t (vsBandFin p t x) ≤ psiI k ∧
      P.bigPsiAv k t (vsBandFin p t x) ≤ psiA k := by
  have ht1 : t ≤ 1 := WithTop.coe_le_coe.mp (ht.trans (tau_le_one P psiI psiA x))
  have hc := continuous_excessProc hN hW hz hS psiI psiA x
  have hclosed : IsClosed {s : ℝ≥0 | excessProc p P psiI psiA s x ≤ 0} :=
    isClosed_le hc continuous_const
  have hsub : Iio t ⊆ {s : ℝ≥0 | excessProc p P psiI psiA s x ≤ 0} := fun s hs =>
    (excessProc_neg_of_lt_tau hN hW hz hS psiI psiA x
      (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hs) ht)).le
  have hcl : closure (Iio t) = Iic t := closure_Iio' ⟨0, ht0⟩
  have hmem : t ∈ {s : ℝ≥0 | excessProc p P psiI psiA s x ≤ 0} :=
    hclosed.closure_subset_iff.mpr hsub (by rw [hcl]; exact Set.mem_Iic.mpr le_rfl)
  have h' : P.excess psiI psiA (t : ℝ) (vsBandFin p t x) ≤ 0 := by
    have h2 : excessProc p P psiI psiA t x ≤ 0 := hmem
    unfold excessProc at h2
    rwa [min_eq_left ht1] at h2
  exact (P.excess_nonpos_iff psiI psiA _ _).mp h'

/-- **Closed a-priori form**, all `t ≤ τ` including `t = 0`, under the hypothesis
`Split.ZeroStatement` (proved as `MTerms.zero_holds`) and positive thresholds. -/
theorem bigPsi_le_of_le_tau_of_zero (hZ : Split.ZeroStatement) {P : PsiData (p.n * p.W)}
    (hN : 0 < p.n * p.W) (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S)
    {psiI psiA : ℕ → ℝ} (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k)
    (x : RingSample p) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x) :
    ∀ k ∈ kRange, P.bigPsiIso k t (vsBandFin p t x) ≤ psiI k ∧
      P.bigPsiAv k t (vsBandFin p t x) ≤ psiA k := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
  · subst h0
    have h := excessProc_zero hZ (P := P) hI hA x
    simp only [excessProc, min_eq_left (zero_le_one' ℝ≥0)] at h
    exact (P.excess_nonpos_iff psiI psiA _ _).mp h.le
  · exact bigPsi_le_of_le_tau hN hW hz hS psiI psiA x h0 ht

/-- **Closed a-priori form**, per pattern and sites: for `0 < t ≤ τ` and `1 ≤ k ≤ K`, every
isotropic and averaged ratio is at most its threshold.
-/
theorem ratio_le_of_le_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (x : RingSample p)
    {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : WithTop ℝ≥0) ≤ tau p P psiI psiA x) {k : ℕ}
    (hk : k ∈ kRange) :
    (∀ i : IsoIdx (p.n * p.W) k, P.isoRatio i t (vsBandFin p t x) ≤ psiI k) ∧
      ∀ i : AvIdx (p.n * p.W) k, P.avRatio i t (vsBandFin p t x) ≤ psiA k := by
  obtain ⟨h1, h2⟩ := bigPsi_le_of_le_tau hN hW hz hS psiI psiA x ht0 ht k hk
  exact ⟨fun i => (P.isoRatio_le_bigPsiIso i _ _).trans h1,
    fun i => (P.avRatio_le_bigPsiAv i _ _).trans h2⟩

/-- **Hitting property**: if `τ < 1`, then `τ = t` for a real time `t < 1` at which
some control quantity reaches its threshold:
`∃ k ∈ [1,K]`, `ψ^iso_k ≤ Ψ^iso_{k,t}(H_t)` or
`ψ^av_k ≤ Ψ^av_{k,t}(H_t)`.
Pathwise, every sample.
-/
theorem exists_ge_at_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (x : RingSample p)
    (hlt : tau p P psiI psiA x < ((1 : ℝ≥0) : WithTop ℝ≥0)) :
    ∃ t : ℝ≥0, (t : WithTop ℝ≥0) = tau p P psiI psiA x ∧ t < 1 ∧
      ∃ k ∈ kRange, psiI k ≤ P.bigPsiIso k t (vsBandFin p t x) ∨
        psiA k ≤ P.bigPsiAv k t (vsBandFin p t x) := by
  have hc := continuous_excessProc hN hW hz hS psiI psiA x
  have htau := tau_eq_hitTime hN hW hz hS psiI psiA x
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℝ≥0,
      T = (fun t => excessProc p P psiI psiA t x) ⁻¹' Ici (0 : ℝ) := ⟨_, rfl⟩
  have hT : ∀ t, t ∈ T ↔ 0 ≤ excessProc p P psiI psiA t x := fun t => by
    rw [hTdef, Set.mem_preimage, Set.mem_Ici]
  have hne : T.Nonempty := by
    by_contra hT0
    rw [not_nonempty_iff_eq_empty] at hT0
    have htop : hitTime (Ici (0 : ℝ)) (excessProc p P psiI psiA) x = ⊤ := by
      refine iInf₂_eq_top.mpr fun t ht => ?_
      have : t ∈ T := (hT t).mpr (Set.mem_Ici.mp ht)
      rw [hT0] at this
      exact absurd this (notMem_empty t)
    rw [htau, htop, min_eq_right le_top] at hlt
    exact lt_irrefl _ hlt
  have hTc : IsClosed T := by rw [hTdef]; exact isClosed_Ici.preimage hc
  have hbdd : BddBelow T := ⟨0, fun _ _ => zero_le⟩
  have hmem : sInf T ∈ T := hTc.csInf_mem hne hbdd
  have hmem' : 0 ≤ excessProc p P psiI psiA (sInf T) x := by
    exact (hT _).mp hmem
  have hhit : hitTime (Ici (0 : ℝ)) (excessProc p P psiI psiA) x =
      ((sInf T : ℝ≥0) : WithTop ℝ≥0) :=
    le_antisymm (iInf₂_le (sInf T)
      (show excessProc p P psiI psiA (sInf T) x ∈ Ici (0 : ℝ) from Set.mem_Ici.mpr hmem'))
      (le_iInf₂ fun t ht => WithTop.coe_le_coe.mpr
        (csInf_le hbdd ((hT t).mpr (Set.mem_Ici.mp ht))))
  rw [htau, hhit] at hlt ⊢
  have hlt1 : sInf T < 1 := by
    rcases le_total (sInf T) 1 with h | h
    · rw [min_eq_left (WithTop.coe_le_coe.mpr h)] at hlt
      exact WithTop.coe_lt_coe.mp hlt
    · rw [min_eq_right (WithTop.coe_le_coe.mpr h)] at hlt
      exact absurd hlt (lt_irrefl _)
  refine ⟨sInf T, (min_eq_left (WithTop.coe_le_coe.mpr hlt1.le)).symm, hlt1, ?_⟩
  have h0 : 0 ≤ P.excess psiI psiA ((sInf T : ℝ≥0) : ℝ) (vsBandFin p (sInf T) x) := by
    have h := hmem'
    unfold excessProc at h
    rwa [min_eq_left hlt1.le] at h
  exact (P.excess_nonneg_iff psiI psiA _ _).mp h0

/-- **Hitting property**, per pattern and sites: if `τ < 1` and the thresholds are positive, then at
`t = τ` some isotropic or averaged ratio (a pattern and sites) reaches its threshold.
-/
theorem exists_ratio_ge_at_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) {psiI psiA : ℕ → ℝ}
    (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k) (x : RingSample p)
    (hlt : tau p P psiI psiA x < ((1 : ℝ≥0) : WithTop ℝ≥0)) :
    ∃ t : ℝ≥0, (t : WithTop ℝ≥0) = tau p P psiI psiA x ∧ t < 1 ∧ ∃ k ∈ kRange,
      (∃ i : IsoIdx (p.n * p.W) k, psiI k ≤ P.isoRatio i t (vsBandFin p t x)) ∨
        ∃ i : AvIdx (p.n * p.W) k, psiA k ≤ P.avRatio i t (vsBandFin p t x) := by
  obtain ⟨t, ht, ht1, k, hk, h⟩ := exists_ge_at_tau hN hW hz hS psiI psiA x hlt
  refine ⟨t, ht, ht1, k, hk, ?_⟩
  rcases h with h | h
  · exact Or.inl ((P.le_bigPsiIso_iff _ _ (hI k hk)).mp h)
  · exact Or.inr ((P.le_bigPsiAv_iff _ _ (hA k hk)).mp h)

end BlockBand.Native.ErdosRiabov.Psi
