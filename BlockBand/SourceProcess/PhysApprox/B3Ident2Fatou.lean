module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Closed

/-!
# A Fatou bound along the uncapped fdd limit, and non-birth grids

Measure: the candidate's `Q`; at finite `W` the conditioned closed law. No RBM estimate here.

* `integral_le_toReal_lintegral`: `∫ f ≤ (∫⁻ F).toReal` for `0 ≤ f`, `ofReal ∘ f ≤ F`,
  `∫⁻ F < ∞` (no measurability of `f`: a non-measurable `f` has integral `0`).
* `condObsTestAll_le`: the conditioned test of a nonnegative `ψ` is at most
  `(∫⁻ F).toReal / P_W(cap)` when `ofReal ψ(obs) ≤ F` on the cap event.
* **`integral_le_of_fddAll`** (Fatou along the fdd limit): if bounded continuous `ψ_k`
  increase pointwise to a function `f ≤ N` and every `ψ_k` has eventually conditioned value
  `≤ B`, then `∫ f(obs) dQ ≤ B`; `f(obs)` is integrable.
* `cl01`: the clamp to `[0, 1]`; `cl01_le_ind`, `tendsto_cl01_ind`: `cl01(k(L − y))` increases
  to `1{y < L}`.
* `exists_nonbirth_btwn`, **`exists_grid`**: rational non-birth points in every interval, and
  finite non-birth grids that are `δ`-dense from the left in `[δ, t]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-!
## Integrals without measurability
-/

theorem integral_le_toReal_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h0 : ∀ x, 0 ≤ f x) {F : α → ℝ≥0∞} (hF : ∀ x, ENNReal.ofReal (f x) ≤ F x)
    (hfin : ∫⁻ x, F x ∂μ ≠ ⊤) : ∫ x, f x ∂μ ≤ (∫⁻ x, F x ∂μ).toReal := by
  by_cases hm : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hm]
    exact ENNReal.toReal_mono hfin (lintegral_mono hF)
  · rw [integral_non_aestronglyMeasurable hm]
    exact ENNReal.toReal_nonneg

variable {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ}

/-- **The conditioned test is bounded by a lintegral on the cap event.** -/
theorem condObsTestAll_le {W : ℕ} {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hW : growthPathLaw W b (physCapEventC b E s h K W) ≠ 0) {ι : Type} [Fintype ι]
    (i : ι → LIdx K np) (u : ι → ℝ≥0) (ψ : BoundedContinuousFunction (ι → ℂ) ℝ)
    (hψ0 : ∀ x, 0 ≤ ψ x) {F : ProbedPath W np × ℝ → ℝ≥0∞}
    (hF : ∀ y, y.1.1 ∈ physCapEventC b E s h K W →
      ENNReal.ofReal (ψ (fun l => b3ObsAll b E s h τ m W V (i l) (u l) y)) ≤ F y)
    (hfin : ∫⁻ y, F y ∂closedLaw b W np ≠ ⊤) :
    condObsTestAll b E s h τ m W V i u ψ ≤
      (∫⁻ y, F y ∂closedLaw b W np).toReal /
        (growthPathLaw W b (physCapEventC b E s h K W)).toReal := by
  have hpos : 0 < (growthPathLaw W b (physCapEventC b E s h K W)).toReal :=
    ENNReal.toReal_pos hW (measure_ne_top _ _)
  unfold condObsTestAll
  refine div_le_div_of_nonneg_right ?_ hpos.le
  refine integral_le_toReal_lintegral (fun y => mul_nonneg (Set.indicator_nonneg
    (fun _ _ => zero_le_one) _) (hψ0 _)) (fun y => ?_) hfin
  by_cases hc : y.1.1 ∈ physCapEventC b E s h K W
  · rw [Set.indicator_of_mem hc, one_mul]; exact hF y hc
  · rw [Set.indicator_of_notMem hc, zero_mul, ENNReal.ofReal_zero]; exact bot_le

variable {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}
  {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
  {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}

/-- **Fatou along the uncapped fdd limit.** -/
theorem integral_le_of_fddAll [IsProbabilityMeasure Q]
    (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    {ι : Type} [Fintype ι] (i : ι → LIdx K np) (u : ι → ℝ≥0) (hu : ∀ l j, s + (u l : ℝ) ≠ τ j)
    (f : (ι → ℂ) → ℝ) (ψ : ℕ → BoundedContinuousFunction (ι → ℂ) ℝ) {N B : ℝ}
    (hψ0 : ∀ k x, 0 ≤ ψ k x) (hψf : ∀ k x, ψ k x ≤ f x) (hfN : ∀ x, f x ≤ N)
    (hlim : ∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (f x)))
    (hB : ∀ k, ∀ᶠ n in atTop, condObsTestAll b E s h τ m (φ n) (Vs (φ n)) i u (ψ k) ≤ B) :
    Integrable (fun ω => f (fun l => complexObs tseq G Kc (i l) (u l) ω)) Q ∧
      ∫ ω, f (fun l => complexObs tseq G Kc (i l) (u l) ω) ∂Q ≤ B := by
  set X : Ω' → ι → ℂ := fun ω l => complexObs tseq G Kc (i l) (u l) ω
  have hX : Measurable X := Measurable.of_eval fun l => hobs (i l) (u l)
  have hψm : ∀ k, AEStronglyMeasurable (fun ω => ψ k (X ω)) Q := fun k =>
    ((ψ k).continuous.measurable.comp hX).aestronglyMeasurable
  have hfm : AEStronglyMeasurable (fun ω => f (X ω)) Q :=
    aestronglyMeasurable_of_tendsto_ae atTop hψm (ae_of_all _ fun ω => hlim (X ω))
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖ψ k (X ω)‖ ≤ N := fun k => ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 k _)]; exact (hψf k _).trans (hfN _)
  have hf0 : ∀ x, 0 ≤ f x := fun x => ge_of_tendsto' (hlim x) fun k => hψ0 k x
  have hint : Integrable (fun ω => f (X ω)) Q :=
    (integrable_const N).mono' hfm (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]; exact hfN _)
  refine ⟨hint, ?_⟩
  have hconv := tendsto_integral_of_dominated_convergence (μ := Q) (fun _ => N) hψm
    (integrable_const N) hbd (ae_of_all _ fun ω => hlim (X ω))
  refine le_of_tendsto' hconv fun k => ?_
  exact le_of_tendsto (hF ι i u hu (ψ k)) (hB k)

/-!
## The clamp
-/

/-- The clamp to `[0, 1]`. -/
def cl01 (y : ℝ) : ℝ := max 0 (min 1 y)

theorem cl01_nonneg (y : ℝ) : 0 ≤ cl01 y := le_max_left _ _

theorem cl01_le_one (y : ℝ) : cl01 y ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem continuous_cl01 : Continuous cl01 :=
  continuous_const.max (continuous_const.min continuous_id)

theorem cl01_le_ind {k : ℝ} (hk : 0 ≤ k) (L y : ℝ) :
    cl01 (k * (L - y)) ≤ if y < L then 1 else 0 := by
  split_ifs with hy
  · exact cl01_le_one _
  · have : k * (L - y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk (by linarith [not_lt.1 hy])
    exact max_le le_rfl ((min_le_right _ _).trans this)

theorem tendsto_cl01_ind (L y : ℝ) :
    Tendsto (fun k : ℕ => cl01 ((k : ℝ) * (L - y))) atTop (𝓝 (if y < L then 1 else 0)) := by
  split_ifs with hy
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / (L - y))
    filter_upwards [eventually_ge_atTop n] with k hk
    have hLy : 0 < L - y := sub_pos.2 hy
    have h1 : 1 ≤ (k : ℝ) * (L - y) := by
      have : 1 / (L - y) ≤ k := hn.trans (by exact_mod_cast hk)
      rwa [div_le_iff₀ hLy] at this
    simp [cl01, min_eq_left h1]
  · refine tendsto_const_nhds.congr fun k => ?_
    have := cl01_le_ind (Nat.cast_nonneg k) L y
    simp only [hy, ↓reduceIte] at this
    exact (le_antisymm this (cl01_nonneg _)).symm

/-!
## Non-birth grids
-/

theorem exists_nonbirth_btwn (s : ℝ) (τ : Fin np → ℝ) {a c : ℝ} (hac : a < c) :
    ∃ q : ℚ, a < q ∧ (q : ℝ) < c ∧ ∀ j, s + (q : ℝ) ≠ τ j := by
  obtain ⟨a', ha1, ha2⟩ := exists_rat_btwn hac
  obtain ⟨c', hc1, hc2⟩ := exists_rat_btwn ha2
  have hI : (Set.Ioo a' c').Infinite := Set.Ioo_infinite (by exact_mod_cast hc1)
  have hB : (⋃ j : Fin np, {q : ℚ | s + (q : ℝ) = τ j}).Finite :=
    Set.finite_iUnion fun j => Set.Subsingleton.finite fun q1 h1 q2 h2 => by
      have h1' : s + (q1 : ℝ) = τ j := h1
      have h2' : s + (q2 : ℝ) = τ j := h2
      exact_mod_cast (show (q1 : ℝ) = q2 by linarith)
  obtain ⟨q, ⟨hq1, hq2⟩, hq3⟩ := (hI.sdiff hB).nonempty
  refine ⟨q, ha1.trans (by exact_mod_cast hq1), (show (q : ℝ) < c' by exact_mod_cast hq2).trans
    hc2, fun j hj => hq3 (Set.mem_iUnion.2 ⟨j, hj⟩)⟩

/-- **Finite non-birth grids, `δ`-dense from the left on `[δ, t]`.** -/
theorem exists_grid (s : ℝ) (τ : Fin np → ℝ) {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    ∃ (M : ℕ) (d : Fin M → ℚ), (∀ a, 0 < (d a : ℝ) ∧ (d a : ℝ) ≤ t ∧ ∀ j, s + (d a : ℝ) ≠ τ j) ∧
      ∀ x : ℝ, δ ≤ x → x ≤ t → ∃ a, (d a : ℝ) ≤ x ∧ x - δ ≤ d a := by
  set M := ⌊2 * t / δ⌋₊
  have hq : ∀ a : Fin M, ∃ q : ℚ, (a : ℝ) * δ / 2 < q ∧ (q : ℝ) < ((a : ℝ) + 1) * δ / 2 ∧
      ∀ j, s + (q : ℝ) ≠ τ j := fun a =>
    exists_nonbirth_btwn s τ (by nlinarith)
  choose d hd1 hd2 hd3 using hq
  refine ⟨M, d, fun a => ⟨?_, ?_, hd3 a⟩, fun x hx1 hx2 => ?_⟩
  · exact lt_of_le_of_lt (by positivity) (hd1 a)
  · refine (hd2 a).le.trans ?_
    have ha : (a : ℝ) + 1 ≤ M := by exact_mod_cast a.isLt
    have hM : (M : ℝ) ≤ 2 * t / δ := Nat.floor_le (by positivity)
    have : ((a : ℝ) + 1) * δ ≤ 2 * t := by
      have := mul_le_mul_of_nonneg_right (ha.trans hM) hδ.le
      rwa [div_mul_cancel₀ _ hδ.ne'] at this
    linarith
  · set k := ⌊2 * x / δ⌋₊
    have hk2 : 2 ≤ k := Nat.le_floor (by
      rw [le_div_iff₀ hδ]; push_cast; linarith)
    have hkM : k ≤ M := Nat.floor_le_floor (by
      exact div_le_div_of_nonneg_right (by linarith) hδ.le)
    refine ⟨⟨k - 1, by omega⟩, ?_, ?_⟩
    · refine (hd2 _).le.trans ?_
      have hk : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hk]
      have := Nat.floor_le (show 0 ≤ 2 * x / δ from div_nonneg (by linarith) hδ.le)
      have : (k : ℝ) * δ ≤ 2 * x := by
        have := mul_le_mul_of_nonneg_right this hδ.le
        rwa [div_mul_cancel₀ _ hδ.ne'] at this
      linarith
    · refine le_trans ?_ (hd1 _).le
      have hlt := Nat.lt_floor_add_one (2 * x / δ)
      have : 2 * x < ((k : ℝ) + 1) * δ := by
        have := mul_lt_mul_of_pos_right hlt hδ
        rwa [div_mul_cancel₀ _ hδ.ne'] at this
      rw [Nat.cast_sub (by omega)]
      push_cast
      nlinarith

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
