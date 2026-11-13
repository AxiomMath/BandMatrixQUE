module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Decomp
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: martingale identities and moment bounds

Under `SchemeHyp` on a probability space with a raw filtration, for the grid of `[s, t]`
with mesh `Δ = (t - s)/(n + 1)`:

* `integral_mul_incN`: `E[g ΔN^i_k] = 0`, `g` bounded and `𝓖_{t_k}`-a.e. measurable;
* `integral_mul_incN_incN`: `E[g ΔN^i_k ΔN^j_k] = E[g Δ∫α^{ij}_k]`;
* `integral_sqSum_le`: `E[S_n] ≤ d Cα (t - s)` for `S_n = Σ_k Σ_i (ΔN^i_k)²`;
* `integral_sqSum_sq_le`: `E[S_n²] ≤ (d Cα (t-s))² + d² (2M)² Cα (t - s)`, `M = 2R + Cβ t`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 m₀} {K : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα R : ℝ}
  {s t : ℝ≥0}

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.stronglyMeasurable_incN (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hst : s ≤ t)
    (n k : ℕ) (i : Fin d) : StronglyMeasurable[𝓖 (grid s t n (k + 1))] (incN N s t n i k) :=
  ((H.mart i).1 _).sub (((H.mart i).1 _).mono (𝓖.mono (grid_mono hst n (Nat.le_succ k))))

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.integrable_incN (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (n k : ℕ) (i : Fin d) :
    Integrable (incN N s t n i k) Q :=
  ((H.mart i).integrable _).sub ((H.mart i).integrable _)

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.ae_abs_incN_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k < n + 1) (i : Fin d) :
    ∀ᵐ ω ∂Q, |incN N s t n i k ω| ≤ 2 * (2 * R + Cβ * t) := by
  filter_upwards [H.ae_good s t] with ω hω
  exact abs_incN_le hω H.driftBound hR hst n hk i

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.ae_abs_incJ_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hst : s ≤ t)
    (n : ℕ) (i j : Fin d) (k : ℕ) :
    ∀ᵐ ω ∂Q, |incJ α s t n i j k ω| ≤ Cα * ((t - s : ℝ) / (n + 1)) := by
  filter_upwards [H.ae_good s t] with ω hω
  exact abs_incJ_le hω H.diffBound hst n i j k

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.aestronglyMeasurable_incJ (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hst : s ≤ t) (n k : ℕ) (i j : Fin d) :
    AEStronglyMeasurable[𝓖 (grid s t n (k + 1))] (incJ α s t n i j k) Q := by
  have hle := 𝓖.mono (grid_mono hst n (Nat.le_succ k))
  have bm : ∀ u, StronglyMeasurable[𝓖 u] fun ω => N i u ω * N j u ω - B i j u ω := fun u =>
    (((H.mart i).1 u).mul ((H.mart j).1 u)).sub ((H.bracket i j).1 u)
  have hm : StronglyMeasurable[𝓖 (grid s t n (k + 1))] fun ω =>
      (N i (grid s t n (k + 1)) ω * N j (grid s t n (k + 1)) ω - B i j (grid s t n (k + 1)) ω) -
      (N i (grid s t n k) ω * N j (grid s t n k) ω - B i j (grid s t n k) ω) :=
    (bm _).sub ((bm _).mono hle)
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [H.ae_good s t] with ω hω
  exact (incJ_eq_bracket hω n i j k).symm

/-- `E[g ΔN^i_k] = 0`. -/
theorem SchemeHyp.integral_mul_incN (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hst : s ≤ t)
    (n k : ℕ) (i : Fin d) {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q)
    {C : ℝ} (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * incN N s t n i k ω ∂Q = 0 :=
  martingale_integral_mul_sub_eq_zero (H.mart i) (grid_mono hst n (Nat.le_succ k)) hg hgC

/-- `E[g ΔN^i_k ΔN^j_k] = E[g Δ∫α^{ij}_k]`. -/
theorem SchemeHyp.integral_mul_incN_incN (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k < n + 1) (i j : Fin d)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q) {C : ℝ}
    (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) :
    ∫ ω, g ω * (incN N s t n i k ω * incN N s t n j k ω) ∂Q =
      ∫ ω, g ω * incJ α s t n i j k ω ∂Q := by
  have bd : ∀ (l : ℕ), l ≤ n + 1 → ∀ i, ∀ᵐ ω ∂Q, ‖N i (grid s t n l) ω‖ ≤ 2 * R + Cβ * t :=
    fun l hl i => by
      filter_upwards [H.ae_good s t] with ω hω
      rw [Real.norm_eq_abs]; exact abs_N_grid_le hω H.driftBound hR hst n hl i
  have := martingale_integral_mul_incr_incr (H.mart i) (H.mart j) (H.bracket i j)
    (grid_mono hst n (Nat.le_succ k)) (bd k hk.le i) (bd (k + 1) (Nat.succ_le_of_lt hk) i)
    (bd k hk.le j) (bd (k + 1) (Nat.succ_le_of_lt hk) j) hg hgC
  simp only [incN]
  rw [this]
  refine integral_congr_ae ?_
  filter_upwards [H.ae_good s t] with ω hω
  rw [incJ_eq_bracket hω n i j k]

/-- Sum of squared increments in a single cell. -/
def cellSq (N : Fin d → ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n k : ℕ) (ω : Ω) : ℝ :=
  ∑ i, incN N s t n i k ω ^ 2

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.stronglyMeasurable_cellSq (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hst : s ≤ t) (n k : ℕ) : StronglyMeasurable[𝓖 (grid s t n (k + 1))] (cellSq N s t n k) := by
  unfold cellSq
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ => (H.stronglyMeasurable_incN hst n k i).pow 2

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.ae_cellSq_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hR : ∀ z ∈ K, ‖z‖ ≤ R)
    (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k < n + 1) :
    ∀ᵐ ω ∂Q, 0 ≤ cellSq N s t n k ω ∧ cellSq N s t n k ω ≤ d * (2 * (2 * R + Cβ * t)) ^ 2 := by
  filter_upwards [H.ae_good s t] with ω hω
  refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
  unfold cellSq
  calc ∑ i, incN N s t n i k ω ^ 2 ≤ ∑ _i : Fin d, (2 * (2 * R + Cβ * t)) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_incN_le hω H.driftBound hR hst n hk i) 2
    _ = d * (2 * (2 * R + Cβ * t)) ^ 2 := by simp

/-- `E[g · cellSq_k] ≤ d Cα Δ · E|g|`-type bound, for nonnegative bounded `g`. -/
theorem SchemeHyp.integral_mul_cellSq_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k < n + 1)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q) {C : ℝ}
    (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) (hg0 : ∀ᵐ ω ∂Q, 0 ≤ g ω) :
    ∫ ω, g ω * cellSq N s t n k ω ∂Q ≤
      d * (Cα * ((t - s : ℝ) / (n + 1))) * ∫ ω, g ω ∂Q := by
  have hg' : AEStronglyMeasurable g Q := hg.mono (𝓖.le _)
  have hgi : Integrable g Q := Integrable.of_bound hg' C hgC
  have hJi : ∀ i, Integrable (fun ω => g ω * incJ α s t n i i k ω) Q := fun i =>
    (Integrable.of_bound ((H.aestronglyMeasurable_incJ hst n k i i).mono (𝓖.le _)) _
      ((H.ae_abs_incJ_le hst n i i k).mono fun ω h => by rwa [Real.norm_eq_abs])).bdd_mul
      hg' hgC
  have hNi : ∀ i, Integrable (fun ω => g ω * (incN N s t n i k ω * incN N s t n i k ω)) Q :=
    fun i => (Integrable.of_bound (((H.stronglyMeasurable_incN hst n k i).mul
      (H.stronglyMeasurable_incN hst n k i)).mono (𝓖.le _)).aestronglyMeasurable
      ((2 * (2 * R + Cβ * t)) * (2 * (2 * R + Cβ * t)))
      ((H.ae_abs_incN_le hR hst n hk i).mono fun ω h => by
        rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul h h (abs_nonneg _) ((abs_nonneg _).trans h))).bdd_mul hg' hgC
  have e : ∫ ω, g ω * cellSq N s t n k ω ∂Q = ∑ i, ∫ ω, g ω * incJ α s t n i i k ω ∂Q := by
    unfold cellSq
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => by simpa [sq] using hNi i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← H.integral_mul_incN_incN hR hst n hk i i hg hgC]
    simp [sq]
  rw [e]
  have : ∀ i, ∫ ω, g ω * incJ α s t n i i k ω ∂Q ≤
      ∫ ω, (Cα * ((t - s : ℝ) / (n + 1))) * g ω ∂Q := fun i => by
    refine integral_mono_ae (hJi i) (hgi.const_mul _) ?_
    filter_upwards [H.ae_abs_incJ_le hst n i i k, hg0] with ω h1 h2
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans h1) h2
  refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, integral_const_mul, nsmul_eq_mul]
  ring

/-- `E[cellSq_k] ≤ d Cα Δ`. -/
theorem SchemeHyp.integral_cellSq_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k < n + 1) :
    ∫ ω, cellSq N s t n k ω ∂Q ≤ d * (Cα * ((t - s : ℝ) / (n + 1))) := by
  have := H.integral_mul_cellSq_le hR hst n hk (g := fun _ => (1 : ℝ))
    aestronglyMeasurable_const (C := 1) (ae_of_all _ fun _ => by simp)
    (ae_of_all _ fun _ => zero_le_one)
  simpa using this

/-- **First moment of `S_n`.** -/
theorem SchemeHyp.integral_sqSum_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) :
    ∫ ω, sqSum N s t n ω ∂Q ≤ d * Cα * (t - s : ℝ) := by
  have hi : ∀ k ∈ Finset.range (n + 1), Integrable (cellSq N s t n k) Q := fun k hk =>
    Integrable.of_bound ((H.stronglyMeasurable_cellSq hst n k).mono (𝓖.le _)).aestronglyMeasurable
      _ ((H.ae_cellSq_le hR hst n (Finset.mem_range.1 hk)).mono fun ω h => by
        rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2)
  have e : sqSum N s t n = fun ω => ∑ k ∈ Finset.range (n + 1), cellSq N s t n k ω := rfl
  rw [e, integral_finsetSum _ hi]
  refine (Finset.sum_le_sum fun k hk =>
    H.integral_cellSq_le hR hst n (Finset.mem_range.1 hk)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  push_cast
  ring

/-- **Second moment of `S_n`.** -/
theorem SchemeHyp.integral_sqSum_sq_le (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hCα : 0 ≤ Cα) (hst : s ≤ t) (n : ℕ) :
    ∫ ω, sqSum N s t n ω ^ 2 ∂Q ≤
      (d * Cα * (t - s : ℝ)) ^ 2 + d * (2 * (2 * R + Cβ * t)) ^ 2 * (d * Cα * (t - s : ℝ)) := by
  set Δ : ℝ := (t - s : ℝ) / (n + 1) with hΔ
  set D : ℝ := d * (2 * (2 * R + Cβ * t)) ^ 2 with hD
  have hts : (0 : ℝ) ≤ t - s := by
    have : (s : ℝ) ≤ t := by exact_mod_cast hst
    linarith
  have hΔ0 : 0 ≤ Δ := div_nonneg hts (by positivity)
  have hX : 0 ≤ d * (Cα * Δ) := by positivity
  have hmeas : ∀ k, AEStronglyMeasurable (cellSq N s t n k) Q := fun k =>
    ((H.stronglyMeasurable_cellSq hst n k).mono (𝓖.le _)).aestronglyMeasurable
  have hbd : ∀ k ∈ Finset.range (n + 1), ∀ᵐ ω ∂Q, ‖cellSq N s t n k ω‖ ≤ D := fun k hk =>
    (H.ae_cellSq_le hR hst n (Finset.mem_range.1 hk)).mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  have hint : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (n + 1),
      Integrable (fun ω => cellSq N s t n k ω * cellSq N s t n l ω) Q := fun k hk l hl =>
    (Integrable.of_bound (hmeas l) D (hbd l hl)).bdd_mul (hmeas k) (hbd k hk)
  have off : ∀ k l, k < l → l < n + 1 →
      ∫ ω, cellSq N s t n k ω * cellSq N s t n l ω ∂Q ≤ (d * (Cα * Δ)) ^ 2 := by
    intro k l hkl hl
    have hk : k < n + 1 := hkl.trans hl
    have hg : AEStronglyMeasurable[𝓖 (grid s t n l)] (cellSq N s t n k) Q :=
      ((H.stronglyMeasurable_cellSq hst n k).mono
        (𝓖.mono (grid_mono hst n (Nat.succ_le_of_lt hkl)))).aestronglyMeasurable
    refine (H.integral_mul_cellSq_le hR hst n hl hg (hbd k (Finset.mem_range.2 hk))
      ((H.ae_cellSq_le hR hst n hk).mono fun ω h => h.1)).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (H.integral_cellSq_le hR hst n hk) hX
  have key : ∀ k ∈ Finset.range (n + 1), ∀ l ∈ Finset.range (n + 1),
      ∫ ω, cellSq N s t n k ω * cellSq N s t n l ω ∂Q ≤
        (d * (Cα * Δ)) ^ 2 + (if k = l then D * (d * (Cα * Δ)) else 0) := by
    intro k hk l hl
    have hk' := Finset.mem_range.1 hk
    have hl' := Finset.mem_range.1 hl
    rcases lt_trichotomy k l with h | rfl | h
    · simp only [h.ne, ↓reduceIte, add_zero]; exact off k l h hl'
    · simp only [↓reduceIte]
      have h1 : ∫ ω, cellSq N s t n k ω * cellSq N s t n k ω ∂Q ≤
          ∫ ω, D * cellSq N s t n k ω ∂Q := by
        refine integral_mono_ae (hint k hk k hk)
          ((Integrable.of_bound (hmeas k) D (hbd k hk)).const_mul D) ?_
        filter_upwards [H.ae_cellSq_le hR hst n hk'] with ω h
        exact mul_le_mul_of_nonneg_right h.2 h.1
      rw [integral_const_mul] at h1
      have hD0 : 0 ≤ D := by positivity
      have := mul_le_mul_of_nonneg_left (H.integral_cellSq_le hR hst n hk') hD0
      nlinarith [sq_nonneg (d * (Cα * Δ))]
    · simp only [h.ne', ↓reduceIte, add_zero]
      have := off l k h hk'
      simp_rw [mul_comm (cellSq N s t n k _)]
      simpa using this
  have e : (fun ω => sqSum N s t n ω ^ 2) = fun ω => ∑ k ∈ Finset.range (n + 1),
      ∑ l ∈ Finset.range (n + 1), cellSq N s t n k ω * cellSq N s t n l ω := by
    funext ω
    rw [sq, show sqSum N s t n ω = ∑ k ∈ Finset.range (n + 1), cellSq N s t n k ω from rfl,
      Finset.sum_mul_sum]
  rw [e, integral_finsetSum _ fun k hk => integrable_finsetSum _ fun l hl => hint k hk l hl]
  have hsum : ∑ k ∈ Finset.range (n + 1), ∫ ω, ∑ l ∈ Finset.range (n + 1),
      cellSq N s t n k ω * cellSq N s t n l ω ∂Q ≤
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        ((d * (Cα * Δ)) ^ 2 + (if k = l then D * (d * (Cα * Δ)) else 0)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    rw [integral_finsetSum _ fun l hl => hint k hk l hl]
    exact Finset.sum_le_sum fun l hl => key k hk l hl
  refine hsum.trans (le_of_eq ?_)
  have hdiag : ∀ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      (if k = l then D * (d * (Cα * Δ)) else 0) = D * (d * (Cα * Δ)) := fun k hk => by
    simp [Finset.sum_ite_eq, Finset.mem_range.1 hk]
  simp only [Finset.sum_add_distrib, Finset.sum_congr rfl hdiag, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [hΔ, hD]
  field_simp
  push_cast
  ring

end BlockBand.SourceProcess.Stochastic.Semimartingale
