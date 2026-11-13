module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionEstimate
public import BlockBand.SourceProcess.Stochastic.Dyson.Assembly

/-!
# Non-collision of Dyson Brownian motion, from the Itô and stopping contracts

The non-collision clause (b1) of `DysonBrownianMotion`, in the exact form `DysonNonCollision N`.
Conditional on the Itô formula (a1) `SemimartingaleItoFormula` and the stopping contract (a2)
`StoppedSemimartingale`.

* `badSet_null`: letting `n → ∞` in `mcKean_bound`, `P(badSet G F s T k m) = 0`;
* `collision_null`: for `s > 0`, a.s. `F + G_{s+u}` has simple spectrum for all `u ≤ T` (the
  collision event is covered by the null sets `badSet` over `k, m` and the fixed-time null set
  at `s`, `simple_fixedTime`);
* `dysonNonCollision_of_ito`: **clause (b1)**, from (a1) and (a2) (union over `s = 1/(j+1)`,
  `T ∈ ℕ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

theorem badSet_null (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian) {s : ℝ≥0} (hs : 0 < s) (T : ℝ≥0)
    {k m : ℕ} (hk : 1 ≤ k) (hm : 0 < m) : Q (badSet G F s T k m) = 0 := by
  have hb : ∀ n : ℕ, max k 2 ≤ n → Q.real (badSet G F s T k m) ≤ mcKeanC N k m / Real.log n := by
    intro n hn
    have h1n : (1 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right k 2).trans hn))
    rw [le_div_iff₀ (Real.log_pos h1n), mul_comm]
    exact mcKean_bound hIto hStop hG hF hFh hs hk ((le_max_left k 2).trans hn) hm T
  have hlim : Tendsto (fun n : ℕ => mcKeanC N k m / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hle : Q.real (badSet G F s T k m) ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨max k 2, hb⟩)
  exact (measureReal_eq_zero_iff).mp (le_antisymm hle measureReal_nonneg)

/-- **No collision on `[s, s + T]`** for `s > 0`. -/
theorem collision_null (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (hG : IsHermitianBrownian Q 𝓖 N G)
    (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian) {s : ℝ≥0} (hs : 0 < s) (T : ℝ≥0) :
    Q {ω | ∃ u ≤ T, ¬ HasSimpleSpectrum N (F ω + G (s + u) ω)} = 0 := by
  have hcover : {ω | ∃ u ≤ T, ¬ HasSimpleSpectrum N (F ω + G (s + u) ω)} ⊆
      {ω | ¬ HasSimpleSpectrum N (F ω + G s ω)} ∪
        ⋃ k : ℕ, ⋃ m : ℕ, badSet G F s T (k + 1) (m + 1) := by
    rintro ω ⟨u, huT, hu⟩
    by_cases h0 : HasSimpleSpectrum N (F ω + G s ω)
    · right
      have h1 : ∀ᶠ k : ℕ in atTop, ∀ i j : Fin N, i ≠ j → 1 / ((k + 1 : ℕ) : ℝ) <
          |dysonEigenvalue N (F ω + G s ω) i - dysonEigenvalue N (F ω + G s ω) j| := by
        refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
        by_cases hij : i = j
        · exact Eventually.of_forall fun _ h => absurd hij h
        · have hpos : 0 < |dysonEigenvalue N (F ω + G s ω) i - dysonEigenvalue N (F ω + G s ω) j| :=
            abs_pos.mpr (sub_ne_zero.mpr (HasSimpleSpectrum.ne h0 hij))
          have ht : Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
            (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
          exact ((tendsto_order.1 ht).2 _ hpos).mono fun k hk _ => hk
      have h2 : ∀ᶠ k : ℕ in atTop, ∀ i,
          |dysonEigenvalue N (F ω + G s ω) i| ≤ ((k + 1 : ℕ) : ℝ) := by
        refine eventually_all.2 fun i => ?_
        obtain ⟨k₀, hk₀⟩ := exists_nat_ge |dysonEigenvalue N (F ω + G s ω) i|
        filter_upwards [eventually_ge_atTop k₀] with k hk
        have : (k₀ : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k₀ ≤ k + 1)
        linarith
      obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
      obtain ⟨m, hm⟩ := ((tendsto_order.1 (tendsto_normStop hG s ω)).1 T
        (WithTop.coe_lt_top T)).exists
      exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨m, ⟨hk1, hk2⟩, hm, u, huT, hu⟩⟩
    · left; exact h0
  refine measure_mono_null hcover (measure_union_null ?_ (measure_iUnion_null fun k =>
    measure_iUnion_null fun m => badSet_null hIto hStop hG hF hFh hs T (by omega) (by omega)))
  have := simple_fixedTime hG hF hFh hs
  rwa [ae_iff] at this

/-- **Clause (b1) of `DysonBrownianMotion`** (non-collision), from (a1) and (a2). -/
theorem dysonNonCollision_of_ito (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) (N : ℕ) : DysonNonCollision N := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh
  have hcover : {ω | ¬ ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)} ⊆
      ⋃ j : ℕ, ⋃ T : ℕ, {ω | ∃ u ≤ (T : ℝ≥0),
        ¬ HasSimpleSpectrum N (F ω + G (1 / ((j : ℝ≥0) + 1) + u) ω)} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall] at hω
    obtain ⟨t, ht, hnt⟩ := hω
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt ht
    refine mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨⌈t - 1 / ((j : ℝ≥0) + 1)⌉₊,
      t - 1 / ((j : ℝ≥0) + 1), Nat.le_ceil _, ?_⟩⟩
    rwa [add_tsub_cancel_of_le hj.le]
  rw [ae_iff]
  exact measure_mono_null hcover (measure_iUnion_null fun j => measure_iUnion_null fun T =>
    collision_null hIto hStop hG hF hFh (by positivity) _)

end BlockBand.SourceProcess.Stochastic.Dyson
