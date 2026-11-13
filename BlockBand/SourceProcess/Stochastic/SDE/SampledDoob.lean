module

public import BlockBand.SourceProcess.Stochastic.SDE.DiscreteDoob

/-!
# Doob's `L²` inequality along monotone time samplings

Setting: an arbitrary measurable space `(Ω, m0)` with a finite measure `P`, a real-time
filtration `𝓕 : Filtration ℝ≥0 m0`, and a martingale `X : ℝ≥0 → Ω → E` with values in a
real Banach space `E`. No integrability of `X` is assumed beyond the martingale property;
the right-hand sides may be `⊤`.

* `sampledFiltration 𝓕 q hq`: the discrete filtration `k ↦ 𝓕 (q k)` along a monotone
  sampling `q : ℕ → ℝ≥0`; `martingale_sampled`: `k ↦ X (q k)` is a martingale for it.
* `lintegral_iSup_sampled_sq_le`: if `q` is monotone and constant from index `n` on, then
  `∫⁻ ⨆ₖ ‖X (q k)‖ₑ² ≤ 4 ∫⁻ ‖X (q n)‖ₑ²` (discrete Doob `L²`, from
  `DoobLp.martingale_eLpNorm_runMax_norm_le` with `p = 2`).
* `measure_sampled_maximal_le` (real case): `λ² P(λ ≤ maxₖ |X (q k)|) ≤ ∫⁻ ‖X (q n)‖ₑ²`
  (weak-type form, via `MeasureTheory.maximal_ineq` for the submartingale `X²`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.SDE
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {P : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E]

/-- The discrete filtration `k ↦ 𝓕 (q k)` along a monotone sampling `q`. -/
def sampledFiltration (𝓕 : Filtration ℝ≥0 m0) (q : ℕ → ℝ≥0) (hq : Monotone q) :
    Filtration ℕ m0 where
  seq k := 𝓕 (q k)
  mono' _ _ hij := 𝓕.mono (hq hij)
  le' k := 𝓕.le (q k)

theorem martingale_sampled [NormedSpace ℝ E] [CompleteSpace E] {𝓕 : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → E}
    (hX : Martingale X 𝓕 P) (q : ℕ → ℝ≥0) (hq : Monotone q) :
    Martingale (fun k => X (q k)) (sampledFiltration 𝓕 q hq) P :=
  ⟨fun k => hX.stronglyAdapted (q k), fun _ _ hij => hX.condExp_ae_eq (hq hij)⟩

/-- `∫⁻ ‖f‖ₑ² = ‖f‖_{L²}²`. -/
theorem lintegral_enorm_sq_eq_eLpNorm_sq {f : Ω → E} (hf : AEStronglyMeasurable f P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = eLpNorm f 2 P ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := P) (p := 2) two_ne_zero hf
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [← h]
  rfl

omit m0 in
/-- The finite running maximum of the norms equals the supremum over all indices when the
sampling is constant after `n`. -/
theorem iSup_sampled_enorm_sq_eq {X : ℕ → Ω → E} (n : ℕ) (hX : ∀ k ≥ n, X k = X n) (ω : Ω) :
    ⨆ k, ‖X k ω‖ₑ ^ 2 =
      ‖(Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => ‖X k ω‖)‖ₑ ^ 2 := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun k => ‖X k ω‖)
  rw [hjeq, enorm_norm]
  refine le_antisymm (iSup_le fun k => ?_) (le_iSup (fun k => ‖X k ω‖ₑ ^ 2) j)
  have hk : ‖X (min k n) ω‖ ≤ ‖X j ω‖ := by
    rw [← hjeq]
    exact Finset.le_sup' (fun k => ‖X k ω‖) (Finset.mem_range.2 (by omega))
  have hkk : X k ω = X (min k n) ω := by
    rcases le_total k n with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, hX k h]
  rw [hkk]
  gcongr
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hk

/-- **Discrete Doob `L²` inequality along a sampling.** For a Banach-valued martingale `X` on
`(Ω, 𝓕, P)` (`P` finite) and a monotone sampling `q` that is constant from index `n` on,
`∫⁻ supₖ ‖X (q k)‖ₑ² dP ≤ 4 ∫⁻ ‖X (q n)‖ₑ² dP`. -/
theorem lintegral_iSup_sampled_sq_le [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → E} (hX : Martingale X 𝓕 P) (q : ℕ → ℝ≥0) (hq : Monotone q) (n : ℕ)
    (hqn : ∀ k ≥ n, q k = q n) :
    ∫⁻ ω, ⨆ k, ‖X (q k) ω‖ₑ ^ 2 ∂P ≤ 4 * ∫⁻ ω, ‖X (q n) ω‖ₑ ^ 2 ∂P := by
  have hY := martingale_sampled hX q hq
  have hD := DoobLp.martingale_eLpNorm_runMax_norm_le hY (p := 2) one_lt_two n
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  norm_num only [h2] at hD
  set g : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    (fun k => ‖X (q k) ω‖)
  have hgm : AEStronglyMeasurable g P := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact Finset.measurable_range_sup'' fun k _ =>
      ((hY.stronglyMeasurable k).mono (𝓕.le (q k))).norm.measurable
  have hXn : AEStronglyMeasurable (X (q n)) P :=
    ((hX.stronglyMeasurable (q n)).mono (𝓕.le (q n))).aestronglyMeasurable
  calc ∫⁻ ω, ⨆ k, ‖X (q k) ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖g ω‖ₑ ^ 2 ∂P := by
        refine lintegral_congr fun ω => ?_
        exact iSup_sampled_enorm_sq_eq (X := fun k => X (q k)) n
          (fun k hk => by simp only [hqn k hk]) ω
    _ = eLpNorm g 2 P ^ 2 := lintegral_enorm_sq_eq_eLpNorm_sq hgm
    _ ≤ (2 * eLpNorm (X (q n)) 2 P) ^ 2 := by gcongr
    _ = 4 * ∫⁻ ω, ‖X (q n) ω‖ₑ ^ 2 ∂P := by
        rw [lintegral_enorm_sq_eq_eLpNorm_sq hXn, mul_pow]
        norm_num

/-- `∫⁻ ‖f‖ₑ² = ∫ f²` for a real square-integrable `f`. -/
theorem lintegral_enorm_sq_eq_ofReal_integral {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall fun ω => sq_nonneg (f ω))]
  refine lintegral_congr fun ω => ?_
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

/-- Square integrability propagates backwards along a martingale. -/
theorem martingale_memLp_two_of_le [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : MemLp (X t) 2 P) : MemLp (X s) 2 P :=
  (ht.condExp (m := 𝓕 s) one_le_two).ae_eq (hX.condExp_ae_eq hst)

/-- **Weak-type discrete Doob `L²` bound along a sampling** (real martingale, `P` finite,
`q` monotone and constant from index `n` on):
`λ² P(∃ k, λ ≤ |X (q k)|) ≤ ∫⁻ ‖X (q n)‖ₑ²`. -/
theorem measure_sampled_maximal_le [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 m0}
    {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P) (q : ℕ → ℝ≥0) (hq : Monotone q) (n : ℕ)
    (hqn : ∀ k ≥ n, q k = q n) (l : ℝ≥0) :
    (l : ℝ≥0∞) ^ 2 * P {ω | ∃ k, (l : ℝ) ≤ |X (q k) ω|} ≤ ∫⁻ ω, ‖X (q n) ω‖ₑ ^ 2 ∂P := by
  have hXn : AEStronglyMeasurable (X (q n)) P :=
    ((hX.stronglyMeasurable (q n)).mono (𝓕.le (q n))).aestronglyMeasurable
  by_cases hfin : ∫⁻ ω, ‖X (q n) ω‖ₑ ^ 2 ∂P = ⊤
  · rw [hfin]; exact le_top
  have hL2n : MemLp (X (q n)) 2 P := by
    rw [lintegral_enorm_sq_eq_eLpNorm_sq hXn] at hfin
    exact lt_top_iff_ne_top.2 fun h => hfin (by rw [h]; simp)
  have hL2 : ∀ k, MemLp (X (q k)) 2 P := fun k => by
    rcases le_total k n with h | h
    · exact martingale_memLp_two_of_le hX (hq h) hL2n
    · rw [hqn k h]; exact hL2n
  let f : ℕ → Ω → ℝ := fun k ω => X (q k) ω ^ 2
  have hcv : ConvexOn ℝ Set.univ (fun z : ℝ => z ^ 2) := (by norm_num : Even 2).convexOn_pow
  have hs : Submartingale f (sampledFiltration 𝓕 q hq) P := by
    refine ⟨fun k => StronglyMeasurable.pow (hX.stronglyAdapted (q k)) 2, fun i j hij => ?_,
      fun k => (hL2 k).integrable_sq⟩
    have hj := ConvexOn.map_condExp_le_univ (m := 𝓕 (q i)) (𝓕.le (q i)) hcv
      (continuous_id.pow 2).lowerSemicontinuous ((hL2 j).integrable one_le_two)
      (hL2 j).integrable_sq
    filter_upwards [hj, hX.condExp_ae_eq (hq hij)] with ω hω hy
    change (P[X (q j) | 𝓕 (q i)] ω) ^ 2 ≤ _ at hω
    rw [hy] at hω
    exact hω
  have hm := maximal_ineq hs (fun k ω => sq_nonneg (X (q k) ω)) (ε := l ^ 2) n
  have hsub : {ω | ∃ k, (l : ℝ) ≤ |X (q k) ω|} ⊆ {ω | ((l ^ 2 : ℝ≥0) : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω} := by
    rintro ω ⟨k, hk⟩
    have hk' : X (q k) ω = X (q (min k n)) ω := by
      rcases le_total k n with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, hqn k h]
    refine le_trans ?_ (Finset.le_sup' (fun k => f k ω)
      (Finset.mem_range.2 (Nat.lt_succ_of_le (min_le_right k n))))
    simp only [f, NNReal.coe_pow, ← hk']
    rw [← sq_abs (X (q k) ω)]
    exact pow_le_pow_left₀ l.coe_nonneg hk 2
  calc (l : ℝ≥0∞) ^ 2 * P {ω | ∃ k, (l : ℝ) ≤ |X (q k) ω|}
      ≤ ((l ^ 2 : ℝ≥0) : ℝ≥0∞) * P {ω | ((l ^ 2 : ℝ≥0) : ℝ) ≤
          (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω} := by
        rw [ENNReal.coe_pow]; gcongr
    _ ≤ _ := hm
    _ ≤ ENNReal.ofReal (∫ ω, f n ω ∂P) := by
        refine ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hL2 n).integrable_sq
          (Eventually.of_forall fun ω => sq_nonneg _))
    _ = ∫⁻ ω, ‖X (q n) ω‖ₑ ^ 2 ∂P := (lintegral_enorm_sq_eq_ofReal_integral hL2n).symm

end BlockBand.SourceProcess.Stochastic.SDE
