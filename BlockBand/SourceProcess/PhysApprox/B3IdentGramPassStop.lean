module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassDefs

/-!
# Removal of the auxiliary stop

Measure: `closedLaw b W np`; the cap event `physCapEventC` enters as an indicator.

* `sum_Ico_telescope`, **`tail_sum`** (abstract): over an upward-closed set of indices, a sum of
  increments `f(j+1) − f j` is `f n − f k` for one `k`.
* `cellT_first`, `cellT_last`, `cellT_le`: the grid starts at `a`, ends at `t`, stays in `[a, t]`.
* `measurable_b3ObsAll`, `sm_pG`, `sm_pM`, `measurable_pTest`: measurability of the prelimit
  objects for a measurable frame.
* **`norm_pUnst_sub_le`** (fixed `W`): the stopped and unstopped tested increments differ only on
  the exit event `{∃ i ∈ [n_s, ⌊W T_H⌋], R ≤ Re Tr M_i}` (cap event), by at most `2 C ‖φ‖`, where
  `C` bounds the generator process along every feasible path on `[0, t]`
  (`exists_uniform_bound`; **independent of `R`**).
* **`tendsto_pUnst`**: `GramPassLocal` and the hypotheses give `pUnst → 0` as `W → ∞`
  (`W → ∞` at fixed `R`, then `R` from the stop tail `complexClosedStopTail_of` at the horizon
  `max T (s + t + 1)`; feasibility `complexClosedFeasible_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-!
## Abstract sums
-/

theorem sum_Ico_telescope (f : ℕ → ℂ) {p q : ℕ} (hpq : p ≤ q) :
    ∑ j ∈ Finset.Ico p q, (f (j + 1) - f j) = f q - f p := by
  induction q, hpq using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn, ih]; ring

theorem up_of_le {P : ℕ → Prop} (hP : ∀ j, P j → P (j + 1)) {j n : ℕ} (hjn : j ≤ n)
    (hj : P j) : P n := by
  induction n, hjn using Nat.le_induction with
  | base => exact hj
  | succ q _ ih => exact hP q ih

/-- **Increments over an upward-closed set of indices telescope.** -/
theorem tail_sum (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ j, P j → P (j + 1))
    (p : ℕ) : ∀ n, ∃ k, (∑ j ∈ Finset.Ico p n, if P j then f (j + 1) - f j else 0) =
      f n - f k := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    by_cases hpn : p ≤ n
    · rw [Finset.sum_Ico_succ_top hpn]
      by_cases hn : P n
      · obtain ⟨k, hk⟩ := ih
        exact ⟨k, by simp only [hk, hn, ↓reduceIte]; ring⟩
      · have hz : ∀ j ≤ n, ¬ P j := fun j hj hPj => hn (up_of_le hP hj hPj)
        refine ⟨n + 1, ?_⟩
        rw [Finset.sum_eq_zero fun j hj => by
          simp only [hz j (Finset.mem_Ico.1 hj).2.le, ↓reduceIte]]
        simp only [hn, ↓reduceIte]
        ring
    · exact ⟨n + 1, by rw [Finset.Ico_eq_empty (by omega)]; simp⟩

theorem sum_tail_eq_zero (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] {p n : ℕ}
    (h : ∀ j < n, ¬ P j) :
    (∑ j ∈ Finset.Ico p n, if P j then f (j + 1) - f j else 0) = 0 :=
  Finset.sum_eq_zero fun j hj => by simp only [h j (Finset.mem_Ico.1 hj).2, ↓reduceIte]

/-!
## The grid
-/

theorem cellT_le (s : ℝ) (W : ℕ) {a t : ℝ≥0} (hat : a ≤ t) (j : ℕ) : cellT s W a t j ≤ t :=
  max_le hat (min_le_left _ _)

theorem cellT_first {s : ℝ} (hs : 0 ≤ s) {W : ℕ} (hW : 1 ≤ W) (a t : ℝ≥0) :
    cellT s W a t (limLenAll s W a) = a := by
  refine max_eq_left ((min_le_right _ _).trans ?_)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  refine Real.toNNReal_le_iff_le_coe.2 ?_
  have h1 : (limLenAll s W a : ℝ) ≤ W * (s + a) :=
    Nat.floor_le (mul_nonneg hW0.le (by positivity))
  rw [sub_le_iff_le_add, div_le_iff₀ hW0]
  linarith

theorem cellT_last {s : ℝ} {W : ℕ} (hW : 1 ≤ W) {a t : ℝ≥0} (hat : a ≤ t) :
    cellT s W a t (limLenAll s W t + 1) = t := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : (W : ℝ) * (s + t) < (limLenAll s W t + 1 : ℕ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have h2 : t ≤ ((((limLenAll s W t + 1 : ℕ) : ℝ)) / W - s).toNNReal :=
    (Real.lt_toNNReal_iff_coe_lt.2 (by rw [lt_sub_iff_add_lt, lt_div_iff₀ hW0]; linarith)).le
  unfold cellT
  rw [min_eq_left h2, max_eq_right hat]

/-!
## Measurability of the prelimit objects
-/

theorem gramOfEntries_entries (H : GSt K np) : gramOfEntries (fun e => gramEntry e H) = H := by
  refine Prod.ext (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_) <;>
    simp [gramOfEntries, gramEntry]

section Meas

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable V)
include hV

theorem measurable_b3ObsAll (l : LIdx K np) (u : ℝ≥0) :
    Measurable (b3ObsAll b E s h τ m W V l u) := by
  rcases l with e | k | ij
  · simp only [b3ObsAll]
    exact (ClosedSumProof.measurable_gramEntry e).comp
      (measurable_b3ClosedGramAt b E s h τ m W _ hV)
  · simp only [b3ObsAll]
    exact Complex.measurable_ofReal.comp
      ((CapLaw.measurable_physTseq b E s W k).comp (measurable_fst.comp measurable_fst))
  · simp only [b3ObsAll]
    exact (measurable_b3ClosedKAt b E s h τ m W _).eval_matrix

theorem measurable_pTest {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) :
    Measurable (pTest b E s h τ m W V i u φ) := by
  have h : Measurable fun y : ProbedPath W np × ℝ =>
      fun l => b3ObsAll b E s h τ m W V (i l) (u l) y := by
    refine measurable_pi_iff.2 fun l => ?_
    have h1 := measurable_b3ObsAll (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m) hV (i l)
      (u l)
    exact h1
  exact φ.continuous.measurable.comp h

theorem sm_pG : StronglyMeasurable (Function.uncurry (pG b E s h τ m W V)) := by
  have hL : Measurable fun u : ℝ≥0 => limLenAll s W u :=
    (measurable_const.mul (measurable_const.add measurable_coe_nnreal_real)).nat_floor
  have hg : Measurable fun p : ℝ≥0 × (ProbedPath W np × ℝ) => (limLenAll s W p.1, p.2) :=
    (hL.comp measurable_fst).prodMk measurable_snd
  have hm : Measurable fun p : ℝ≥0 × (ProbedPath W np × ℝ) =>
      fun e : GIdx K np =>
        gramEntry e (b3ClosedGramAt b E s h τ m W (limLenAll s W p.1) V p.2) := by
    refine measurable_pi_iff.2 fun e => ?_
    have h1 : Measurable fun q : ℕ × (ProbedPath W np × ℝ) =>
        gramEntry e (b3ClosedGramAt b E s h τ m W q.1 V q.2) :=
      measurable_from_prod_countable_right fun j =>
        (ClosedSumProof.measurable_gramEntry e).comp (measurable_b3ClosedGramAt b E s h τ m W j hV)
    have h2 := h1.comp hg
    exact h2
  have h2 : StronglyMeasurable fun p : ℝ≥0 × (ProbedPath W np × ℝ) =>
      gramOfEntries fun e : GIdx K np =>
        gramEntry e (b3ClosedGramAt b E s h τ m W (limLenAll s W p.1) V p.2) :=
    continuous_gramOfEntries.comp_stronglyMeasurable hm.stronglyMeasurable
  have e : Function.uncurry (pG b E s h τ m W V) = fun p : ℝ≥0 × (ProbedPath W np × ℝ) =>
      gramOfEntries fun e : GIdx K np =>
        gramEntry e (b3ClosedGramAt b E s h τ m W (limLenAll s W p.1) V p.2) := by
    funext p; rw [gramOfEntries_entries]; rfl
  rw [e]; exact h2

theorem sm_pM {χ : ℝ → ℝ} (hχ : Continuous χ) {F : ZSt K np → ℂ}
    {Λ : GSt K np × ZSt K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ) (v : ℝ≥0) :
    StronglyMeasurable (pM χ b E s h τ m W V F Λ v) := by
  have h1 := (sm_genProc (b := b) (E := E) (s := s) (τ := τ) (m := m)
    (sm_pG (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m) hV) hχ hF
    hΛ).comp_measurable (measurable_const.prodMk measurable_id :
      Measurable fun y : ProbedPath W np × ℝ => (v, y))
  exact h1

end Meas

/-!
## The stop at fixed `W`
-/

theorem b3Alive_succ_subset {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (j : ℕ) :
    b3Alive b E s h τ m R W (j + 1) V ⊆ b3Alive b E s h τ m R W j V :=
  fun _ hy => ⟨hy.1, fun i hi hij => hy.2 i hi (hij.trans (Nat.le_succ j))⟩

theorem b3Alive_subset_cap {b E s h : ℝ} {τ m : Fin np → ℝ} {R : ℝ} {W : ℕ}
    {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (j : ℕ) :
    b3Alive b E s h τ m R W j V ⊆ capS b E s h K W np :=
  fun _ hy => hy.1

/-- **Stopped and unstopped tested increments at fixed `W`.** -/
theorem norm_pUnst_sub_le {b E s h : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (hs : 0 ≤ s)
    {τ m : Fin np → ℝ} {W : ℕ} (hW : 1 ≤ W)
    {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable V)
    {χ : ℝ → ℝ} (hχ : Continuous χ) {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ}
    (hF : Continuous F) (hΛ : Continuous Λ) {C : ℝ} (hC0 : 0 ≤ C) {a t : ℝ≥0} (hat : a ≤ t)
    (hC : ∀ y, (∀ u, GramFeasible (srcSignature K (Fin np)) (pG b E s h τ m W V u y)) →
      ∀ v ≤ t, ‖pM χ b E s h τ m W V F Λ v y‖ ≤ C)
    (hfe : ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W → ∀ j, closeLen s W ≤ j →
      GramFeasible (srcSignature K (Fin np)) (b3ClosedGramAt b E s h τ m W j V y))
    (R TH : ℝ) (hTH : s + t ≤ TH) {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) :
    ‖pUnst χ b E s h τ m W V F Λ i u φ a t - pStopSum χ b E s h τ m W V F Λ R i u φ a t‖ ≤
      2 * C * ‖φ‖ * (closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i,
        closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * TH⌋₊ ∧
          R ≤ ((b3ClosedGramAt b E s h τ m W i V y).1.trace).re}).toReal := by
  classical
  set μ := closedLaw b W np
  set Ex := {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i,
    closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * TH⌋₊ ∧
      R ≤ ((b3ClosedGramAt b E s h τ m W i V y).1.trace).re}
  set M := pM χ b E s h τ m W V F Λ
  set ψ := pTest b E s h τ m W V i u φ
  set p := limLenAll s W a
  set n := limLenAll s W t + 1
  set D : ℕ → ProbedPath W np × ℝ → ℂ := fun j y => M (cellT s W a t (j + 1)) y -
    M (cellT s W a t j) y
  set A : ℕ → Set (ProbedPath W np × ℝ) := fun j => b3Alive b E s h τ m R W j V
  set f : ℕ → ProbedPath W np × ℝ → ℂ := fun j => (A j).indicator fun y => ψ y • D j y
  set g := (capS b E s h K W np).indicator fun y => ψ y • (M t y - M a y)
  have hpn : p ≤ n := Nat.le_succ_of_le (Nat.floor_mono (by
    have : (a : ℝ) ≤ t := hat
    nlinarith [(Nat.cast_nonneg W : (0 : ℝ) ≤ W)]))
  have hψ : ∀ y, ‖ψ y‖ ≤ ‖φ‖ := fun y => φ.norm_coe_le_norm _
  -- feasibility on the cap event, at every model time
  have hfe' : ∀ᵐ y ∂μ, y ∈ capS b E s h K W np → ∀ v ≤ t, ‖M v y‖ ≤ C := by
    filter_upwards [hfe] with y hy hcap v hv
    refine hC y (fun w => hy hcap _ ?_) v hv
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (by
      have : (0 : ℝ) ≤ w := w.2
      linarith) (Nat.cast_nonneg W))
  -- measurability
  have hMm : ∀ v, StronglyMeasurable (M v) :=
    sm_pM (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m) hV hχ hF hΛ
  have hψm : StronglyMeasurable fun y => ((ψ y : ℝ) : ℂ) :=
    (Complex.measurable_ofReal.comp (measurable_pTest (b := b) (E := E) (s := s) (h := h)
      (τ := τ) (m := m) hV i u φ)).stronglyMeasurable
  have hDm : ∀ j, StronglyMeasurable fun y => ψ y • D j y := fun j => by
    simp only [Complex.real_smul]
    exact hψm.mul ((hMm _).sub (hMm _))
  have hf : ∀ j, Integrable (f j) μ := fun j => by
    have hae : f j =ᵐ[μ] (b3AliveM b E s h τ m R W j V).indicator fun y => ψ y • D j y :=
      indicator_ae_eq_of_ae_eq_set (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j V)
    refine Integrable.of_bound (C := ‖φ‖ * (C + C))
      (((hDm j).indicator (measurableSet_b3AliveM b E s h τ m R W j hV)).aestronglyMeasurable.congr
        hae.symm) ?_
    filter_upwards [hfe'] with y hy
    by_cases hA : y ∈ A j
    · simp only [f, Set.indicator_of_mem hA, D, norm_smul]
      refine mul_le_mul (hψ y) ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _)
        (norm_nonneg _)
      · exact hy (b3Alive_subset_cap j hA) _ (cellT_le s W hat _)
      · exact hy (b3Alive_subset_cap j hA) _ (cellT_le s W hat _)
    · simp only [f, Set.indicator_of_notMem hA, norm_zero]
      positivity
  have hg : Integrable g μ := by
    have hae : g =ᵐ[μ] (Fdd.capM b E s h K W np).indicator fun y => ψ y • (M t y - M a y) :=
      indicator_ae_eq_of_ae_eq_set (Fdd.capC_ae_eq hb hE1 hE2 s h)
    have hm : StronglyMeasurable fun y => ψ y • (M t y - M a y) := by
      simp only [Complex.real_smul]
      exact hψm.mul ((hMm _).sub (hMm _))
    refine Integrable.of_bound (C := ‖φ‖ * (C + C))
      ((hm.indicator (Fdd.measurableSet_capM b E s h K W np)).aestronglyMeasurable.congr
        hae.symm) ?_
    filter_upwards [hfe'] with y hy
    by_cases hA : y ∈ capS b E s h K W np
    · simp only [g, Set.indicator_of_mem hA, norm_smul]
      exact mul_le_mul (hψ y) ((norm_sub_le _ _).trans (add_le_add (hy hA _ le_rfl)
        (hy hA _ hat))) (norm_nonneg _) (norm_nonneg _)
    · simp only [g, Set.indicator_of_notMem hA, norm_zero]
      positivity
  -- the difference as one integral
  have e1 : pUnst χ b E s h τ m W V F Λ i u φ a t - pStopSum χ b E s h τ m W V F Λ R i u φ a t =
      ∫ y, (g y - ∑ j ∈ Finset.Ico p n, f j y) ∂μ := by
    rw [integral_sub hg (integrable_finsetSum _ fun j _ => hf j),
      integral_finsetSum _ fun j _ => hf j]
    rfl
  -- the pointwise bound
  have hpt : ∀ᵐ y ∂μ, ‖g y - ∑ j ∈ Finset.Ico p n, f j y‖ₑ ≤
      Ex.indicator (fun _ => ENNReal.ofReal (2 * C * ‖φ‖)) y := by
    filter_upwards [hfe'] with y hy
    by_cases hcap : y ∈ capS b E s h K W np
    · have hsum : g y - ∑ j ∈ Finset.Ico p n, f j y = ψ y • ∑ j ∈ Finset.Ico p n,
          (if y ∉ A j then M (cellT s W a t (j + 1)) y - M (cellT s W a t j) y else 0) := by
        have ht1 := sum_Ico_telescope (fun j => M (cellT s W a t j) y) hpn
        rw [cellT_first hs hW, cellT_last hW hat] at ht1
        simp only [g, Set.indicator_of_mem hcap, f]
        rw [← ht1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hA : y ∈ A j
        · simp [hA, D]
        · simp [hA, D]
      rw [hsum]
      by_cases hEx : y ∈ Ex
      · rw [Set.indicator_of_mem hEx, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨k, hk⟩ := tail_sum (fun j => M (cellT s W a t j) y) (fun j => y ∉ A j)
          (fun j hj hj' => hj (b3Alive_succ_subset j hj')) p n
        rw [hk, norm_smul]
        have hk1 := hy hcap _ (cellT_le s W hat n)
        have hk2 := hy hcap _ (cellT_le s W hat k)
        calc ‖ψ y‖ * ‖M (cellT s W a t n) y - M (cellT s W a t k) y‖ ≤ ‖φ‖ * (C + C) :=
              mul_le_mul (hψ y) ((norm_sub_le _ _).trans (add_le_add hk1 hk2)) (norm_nonneg _)
                (norm_nonneg _)
          _ = 2 * C * ‖φ‖ := by ring
      · have hal : y ∈ A (limLenAll s W t) := by
          refine ⟨hcap, fun i hi hit => ?_⟩
          by_contra hlt
          refine hEx ⟨hcap, i, hi, hit.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hTH
            (Nat.cast_nonneg W))), not_lt.1 hlt⟩
        have hz := sum_tail_eq_zero (fun j => M (cellT s W a t j) y) (fun j => y ∉ A j)
          (p := p) (n := n) fun j hj hj' => up_of_le (P := fun j => y ∉ A j)
            (fun q hq hq' => hq (b3Alive_succ_subset q hq')) (Nat.lt_succ_iff.1 hj) hj' hal
        rw [hz, smul_zero, enorm_zero]
        exact zero_le
    · have hz : g y - ∑ j ∈ Finset.Ico p n, f j y = 0 := by
        simp only [g, Set.indicator_of_notMem hcap, f]
        rw [Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem
          (fun h => hcap (b3Alive_subset_cap j h)) _]
        simp
      rw [hz, enorm_zero]
      exact zero_le
  have hint := (enorm_integral_le_lintegral_enorm _).trans ((lintegral_mono_ae hpt).trans
    (lintegral_indicator_const_le Ex (ENNReal.ofReal (2 * C * ‖φ‖))))
  rw [e1, ← toReal_enorm]
  calc (‖∫ y, (g y - ∑ j ∈ Finset.Ico p n, f j y) ∂μ‖ₑ).toReal ≤
        (ENNReal.ofReal (2 * C * ‖φ‖) * μ Ex).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hint
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-!
## Removal of the stop
-/

/-- **The unstopped tested increments tend to `0`** (`W → ∞` at fixed `R`, then the
stop tail; `C_H` does not depend on `R`). -/
theorem tendsto_pUnst (hloc : GramPassLocal) (hTL : TransmissionLawContract)
    (hS : ComplexClosedSummed) (hT : ComplexClosedTight) (hK : ComplexKStoppedMomentMax)
    (hL : ComplexClosedLindeberg) {b E : ℝ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) {χ : ℝ → ℝ} (h3 : ContDiff ℝ 3 χ)
    (hcs : HasCompactSupport χ) {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ}
    (hp : IsGenPair χ b E F Λ) {a t : ℝ≥0} (hat : a ≤ t) (ha : a ∉ birthTimes s τ)
    (ht : t ∉ birthTimes s τ) {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0)
    (hu : ∀ l, u l ≤ a) (hub : ∀ l, u l ∉ birthTimes s τ)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) :
    Tendsto (fun W => pUnst χ b E s h τ m W (Vs W) F Λ i u φ a t) atTop (𝓝 0) := by
  obtain ⟨hχc, hFc, hΛc, Rχ, hR, hFv, hΛv⟩ := hp.data h3 hcs
  obtain ⟨C, hC0, hC⟩ := exists_uniform_bound (b := b) (E := E) (s := s) (τ := τ) (m := m)
    hχc hR hFc hΛc hFv hΛv t
  obtain ⟨⟨_, hb, hE1, hE2, -⟩, hs, -, -, -, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  set TH := max T (s + t + 1)
  have hD' := Fdd.frameDomain_mono hD (le_max_left T (s + t + 1))
  have hTH : s + t ≤ TH := (by linarith : s + t ≤ s + t + 1).trans (le_max_right _ _)
  have hfe := complexClosedFeasible_holds b E np τ m T s h K Vs hD
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B := 2 * C * ‖φ‖ + 1
  have hB : 0 < B := by positivity
  obtain ⟨R, hRt⟩ := StopTail.complexClosedStopTail_of hS hL b E np τ m TH s h K Vs hD'
    (ε / (2 * B))
    (by positivity)
  have hst := hloc hTL hS hT hK hL b E np τ m T s h K Vs hD χ h3 hcs F Λ hp R a t hat ha ht r
    i u hu hub φ
  filter_upwards [hRt, hfe, hVs, Metric.tendsto_nhds.1 hst (ε / 2) (half_pos hε),
    eventually_ge_atTop 1] with W hW1 hW2 hW3 hW4 hW5
  have hV : Measurable (Vs W) :=
    hW3.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have key := norm_pUnst_sub_le hb1 hE1 hE2 hs.le hW5 hV hχc hFc hΛc hC0 hat
    (fun y hy v hv => hC _ _ y hy v hv) hW2 R TH hTH i u φ
  have hmeas := ENNReal.toReal_le_of_le_ofReal (by positivity) hW1
  rw [dist_zero_right] at hW4 ⊢
  have h2 : 2 * C * ‖φ‖ * (ε / (2 * B)) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg φ]
  calc ‖pUnst χ b E s h τ m W (Vs W) F Λ i u φ a t‖ ≤
        ‖pStopSum χ b E s h τ m W (Vs W) F Λ R i u φ a t‖ +
          ‖pUnst χ b E s h τ m W (Vs W) F Λ i u φ a t -
            pStopSum χ b E s h τ m W (Vs W) F Λ R i u φ a t‖ := norm_le_insert' _ _
    _ < ε / 2 + 2 * C * ‖φ‖ * (ε / (2 * B)) := by
        refine add_lt_add_of_lt_of_le hW4 (key.trans ?_)
        exact mul_le_mul_of_nonneg_left hmeas (by positivity)
    _ ≤ ε := by linarith

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
