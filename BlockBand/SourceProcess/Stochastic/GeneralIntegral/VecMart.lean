module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VecBracket
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Cross-bracket and vector-bracket martingales; summary

Setting: `(Ω, m₀, Q)` with `Q` finite, an arbitrary raw filtration `𝓖` (no usual conditions),
finite `ι`, `h : IsL2IntegratorVec Q 𝓖 N a` (`N^i` a.s. continuous `L²` integrators with
martingale modifications, `⟨N^i, N^j⟩ = ∫ a^{ij}`, `a` PSD everywhere, jointly measurable,
a.s. locally integrable) with **symmetric** `a` (`hs`; WLOG by `IsL2IntegratorVec.symmetrize`),
horizon `T`, integrands in `PredL2 𝓖 ν̄`, `ν̄ = barMeasure Q a T = (∑_i a^{ii}) ds ⊗ Q`
(`= ∑_i ν^{ii}`), with canonical representatives `H̃`.
`Z^i_t(H) = (h.coord i).contIntegral T (h.restr T i H) = ∫_0^t H dN^i`.

* **`cross_martingale`**: `Z^i_t(H) Z^j_t(K) - ∫_{(0, t∧T]} H̃ K̃ a^{ij} dr` has a
  `𝓖`-martingale modification.
* **`vecBracket_martingale`**: `(∑_i Z^i_t(H_i))² - ∫_{(0, t∧T]} Hᵀ a H dr` has a
  `𝓖`-martingale modification.
* `boundedPredL2`: bounded a.e.-predictable functions as integrands (`boundedPredL2_coeFn`).
* **`vecStochasticIntegral_exists`**: the process `t ↦ ∑_i ∫_0^t H_i dN^i` is a.s. continuous,
  `L²`, has a martingale modification, terminal value `vecIntegral` with
  `E(·)² = E ∫_0^T Hᵀ a H`, is constant after `T`, and has the vector bracket martingale.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] {N : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure Q] in
theorem memLp_of_bounded_pred {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ}
    (hf : AEStronglyMeasurable[predictableSpace (toCF 𝓖)] f μ) {C : ℝ} (hC : ∀ p, |f p| ≤ C) :
    MemLp f 2 μ :=
  MemLp.of_bound (hf.mono (predictableSpace_le _)) C (Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]; exact hC p)

/-- The class in `PredL2 𝓖 μ` (`μ` finite) of a bounded, `μ`-a.e. raw predictable function
(e.g. any bounded predictable vector integrand coordinate, or `stoppedComposite`). -/
def boundedPredL2 {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ}
    (hf : AEStronglyMeasurable[predictableSpace (toCF 𝓖)] f μ) {C : ℝ} (hC : ∀ p, |f p| ≤ C) :
    PredL2 𝓖 μ :=
  ⟨(memLp_of_bounded_pred hf hC).toLp f,
    mem_lpMeas_iff_aestronglyMeasurable.2 (hf.congr (memLp_of_bounded_pred hf hC).coeFn_toLp.symm)⟩

omit [IsFiniteMeasure Q] in
theorem boundedPredL2_coeFn {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ}
    (hf : AEStronglyMeasurable[predictableSpace (toCF 𝓖)] f μ) {C : ℝ} (hC : ∀ p, |f p| ≤ C) :
    (((boundedPredL2 hf hC : PredL2 𝓖 μ) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ] f :=
  (memLp_of_bounded_pred hf hC).coeFn_toLp

namespace IsL2IntegratorVec

variable (h : IsL2IntegratorVec Q 𝓖 N a) (T : ℝ≥0) (hs : ∀ i j t ω, a i j t ω = a j i t ω)
include h hs

/-- **Cross-bracket martingale** `∫H dN^i · ∫K dN^j - ∫_0^{·∧T} H K a^{ij}`. -/
theorem cross_martingale (i j : ι) (H K : PredL2 𝓖 (barMeasure Q a T)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] fun ω =>
      (h.coord i).contIntegral T (h.restr T i H) t ω *
        (h.coord j).contIntegral T (h.restr T j K) t ω -
      crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
        ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) (min t T) ω := by
  set Zi := (h.coord i).contIntegral T (h.restr T i H)
  set Zj := (h.coord j).contIntegral T (h.restr T j K)
  set C := crossTerm a i j ((H : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
    ((K : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
  have hZi (t : ℝ≥0) : Zi t = Zi (min t T) := by
    rcases le_total t T with ht | ht
    · rw [min_eq_left ht]
    · rw [min_eq_right ht]; exact (h.coord i).contIntegral_of_le T _ ht
  have hZj (t : ℝ≥0) : Zj t = Zj (min t T) := by
    rcases le_total t T with ht | ht
    · rw [min_eq_left ht]
    · rw [min_eq_right ht]; exact (h.coord j).contIntegral_of_le T _ ht
  refine exists_martingale_modification' (fun t => ?_) (fun t => ?_) ?_
  · exact (((h.coord i).memLp_contIntegral T _ t).integrable_mul
      ((h.coord j).memLp_contIntegral T _ t)).sub
      (h.integrable_crossTerm T hs i j H K (min_le_right t T))
  · exact (((h.coord i).aestronglyMeasurable_contIntegral T _ t).mul
      ((h.coord j).aestronglyMeasurable_contIntegral T _ t)).sub
      (h.aesm_crossTerm hs T i j H K t)
  · intro u v huv A hA
    by_cases huT : u ≤ T
    · have key := h.setIntegral_cross_eq T hs i j H K (le_min huv huT) (min_le_right v T) hA
      rw [hZi v, hZj v]
      simp only [min_eq_left huT]
      exact key
    · have hTu : T ≤ u := (lt_of_not_ge huT).le
      have hv : min v T = T := min_eq_right (hTu.trans huv)
      have hu : min u T = T := min_eq_right hTu
      rw [hZi v, hZj v, hZi u, hZj u, hv, hu]

/-- **Vector bracket martingale** `(∑_i ∫_0^t H_i dN^i)² - ∫_0^{t∧T} Hᵀ a H`. -/
theorem vecBracket_martingale (H : ι → PredL2 𝓖 (barMeasure Q a T)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] fun ω =>
      h.vecCont T H t ω ^ 2 - ∫ r in Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ), quadDensity T a H (r, ω) := by
  choose Y hY hYe using fun p : ι × ι => h.cross_martingale T hs p.1 p.2 (H p.1) (H p.2)
  refine ⟨fun t ω => ∑ i, ∑ j, Y (i, j) t ω, martingale_finset_sum _ fun i =>
    martingale_finset_sum _ fun j => hY (i, j), fun t => ?_⟩
  have hint (p : ι × ι) := (h.integrable_crossDens T hs p.1 p.2 (H p.1) (H p.2)).prod_left_ae
  filter_upwards [ae_all_iff.2 fun p : ι × ι => hYe p t, ae_all_iff.2 hint] with ω hω hi
  have hsub : Ioc (0 : ℝ) (min t T : ℝ≥0) ⊆ Ioc 0 T :=
    Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (min_le_right t T))
  have hq : ∫ r in Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ), quadDensity T a H (r, ω) =
      ∑ i, ∑ j, crossTerm a i j ((H i : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ)
        ((H j : Lp ℝ 2 (barMeasure Q a T)) : ℝ × Ω → ℝ) (min t T) ω := by
    have hI (i j : ι) : IntegrableOn (fun r => crossDens T i j (H i) (H j) (r, ω))
        (Ioc (0 : ℝ) (min t T : ℝ≥0)) := IntegrableOn.mono_set (hi (i, j)) hsub
    have e : (fun r => quadDensity T a H (r, ω)) =
        fun r => ∑ i, ∑ j, crossDens T i j (H i) (H j) (r, ω) := rfl
    rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hI i j]
    rfl
  simp only [hω, hq, vecCont, sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]

/-- **Summary: the continuous vector stochastic integral and its bracket.** -/
theorem vecStochasticIntegral_exists (H : ι → PredL2 𝓖 (barMeasure Q a T)) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂Q, Continuous fun t => Z t ω) ∧
      (∀ t, MemLp (Z t) 2 Q) ∧
      (∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] Z t) ∧
      Z T =ᵐ[Q] h.vecIntegral T H ∧
      ∫ ω, Z T ω ^ 2 ∂Q = ∫ ω, (∫ r in Ioc (0 : ℝ) T, quadDensity T a H (r, ω)) ∂Q ∧
      (∀ t, T ≤ t → Z t = Z T) ∧
      (∃ Y : ℝ≥0 → Ω → ℝ, Martingale Y 𝓖 Q ∧ ∀ t, Y t =ᵐ[Q] fun ω =>
        Z t ω ^ 2 - ∫ r in Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ), quadDensity T a H (r, ω)) := by
  obtain ⟨hc, hL, hM, hT, hconst⟩ := h.vecCont_spec T H
  refine ⟨h.vecCont T H, hc, hL, hM, hT, ?_, hconst, h.vecBracket_martingale T hs H⟩
  rw [← h.integral_sq_vecIntegral_fubini T hs H]
  exact integral_congr_ae (hT.mono fun ω hω => by simp only [hω])

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
