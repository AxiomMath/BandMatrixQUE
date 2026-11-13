module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Moments
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Taylor scheme with integral bounds: the second moment of `S_n`)

Under `IHyp Q 𝓖 K Z β α N B C` with `K ⊆ closedBall 0 R`, for the grid of `[s, t]`:
`E[S_n²] ≤ (D + 2 d C) · d C`, `D = d (2(2R + C))²`, uniformly in `n`
(`IHyp.integral_sqSum_sq_le'`). Proof: `S_n² = Σ_{k,l} c_k c_l`; diagonal terms are bounded by
`D c_k`; for `k < l`, `E[c_k c_l] = E[c_k J_l]` with `J_l = Σ_i Δ∫α^{ii}_l`, and
`Σ_{l > k} J_l ≤ d C` pathwise.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 m₀} {K : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C R : ℝ}
  {s t : ℝ≥0}

/-- `J_l = Σ_i Δ∫α^{ii}_l`. -/
def diagJ (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (s t : ℝ≥0) (n l : ℕ) (ω : Ω) : ℝ :=
  ∑ i, incJ α s t n i i l ω

theorem IHyp.integrable_diagJ (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t) (n l : ℕ) :
    Integrable (diagJ α s t n l) Q :=
  integrable_finsetSum _ fun i _ => Integrable.of_bound
    ((H.aesm_incJ hst n l i i).mono (𝓖.le _)) _
    ((H.ae_abs_incJ_le hst n i i l).mono fun ω h => by rwa [Real.norm_eq_abs])

omit [IsProbabilityMeasure Q] in
theorem IHyp.ae_abs_diagJ_le (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t) (n l : ℕ) :
    ∀ᵐ ω ∂Q, ‖diagJ α s t n l ω‖ ≤ d * C := by
  filter_upwards [ae_all_iff.2 fun i => H.ae_abs_incJ_le hst n i i l] with ω h
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)
  simp

/-- **Second moment of `S_n`.** -/
theorem IHyp.integral_sqSum_sq_le' (H : IHyp Q 𝓖 K Z β α N B C)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) :
    ∫ ω, sqSum N s t n ω ^ 2 ∂Q ≤
      (d * (2 * (2 * R + C)) ^ 2 + 2 * (d * C)) * (d * C) := by
  set D : ℝ := d * (2 * (2 * R + C)) ^ 2 with hD
  set c := fun k => cellSq N s t n k
  set J := fun l => diagJ α s t n l
  set r := Finset.range (n + 1)
  have hC0 : 0 ≤ C := by
    obtain ⟨ω, hω⟩ := (H.ae_igood s t).exists
    exact hω.C_nonneg
  have hD0 : 0 ≤ D := by positivity
  have hmeas : ∀ k, AEStronglyMeasurable (c k) Q := fun k =>
    ((H.stronglyMeasurable_cellSq hst n k).mono (𝓖.le _)).aestronglyMeasurable
  have hbd : ∀ k, ∀ᵐ ω ∂Q, ‖c k ω‖ ≤ D := fun k =>
    (H.ae_cellSq_le hR n k).mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2
  have hci : ∀ k, Integrable (c k) Q := fun k => H.integrable_cellSq hR hst n k
  have hint : ∀ k l, Integrable (fun ω => c k ω * c l ω) Q := fun k l =>
    (hci l).bdd_mul (hmeas k) (hbd k)
  have hcJ : ∀ k l, Integrable (fun ω => c k ω * J l ω) Q := fun k l =>
    (H.integrable_diagJ hst n l).bdd_mul (hmeas k) (hbd k)
  have hS1 : ∑ k ∈ r, ∫ ω, c k ω ∂Q ≤ d * C := by
    rw [← integral_finsetSum _ fun k _ => hci k]
    exact H.integral_sqSum_le' hR hst n
  -- off-diagonal identity
  have off : ∀ k l, k < l → ∫ ω, c k ω * c l ω ∂Q = ∫ ω, c k ω * J l ω ∂Q := by
    intro k l hkl
    have hg : AEStronglyMeasurable[𝓖 (grid s t n l)] (c k) Q :=
      ((H.stronglyMeasurable_cellSq hst n k).mono
        (𝓖.mono (grid_mono hst n (Nat.succ_le_of_lt hkl)))).aestronglyMeasurable
    exact H.integral_mul_cellSq hR hst n l hg (hbd k)
  -- the termwise majorant
  set g : ℕ → ℕ → ℝ := fun k l => (if k = l then D * ∫ ω, c k ω ∂Q else 0) +
    (if k < l then ∫ ω, c k ω * J l ω ∂Q else 0) + (if l < k then ∫ ω, c l ω * J k ω ∂Q else 0)
  have hfg : ∀ k l, ∫ ω, c k ω * c l ω ∂Q ≤ g k l := by
    intro k l
    rcases lt_trichotomy k l with h | rfl | h
    · simp only [g, h.ne, h, ↓reduceIte, not_lt.2 h.le, zero_add, add_zero]
      exact (off k l h).le
    · simp only [g, ↓reduceIte, lt_irrefl, add_zero]
      have h1 : ∫ ω, c k ω * c k ω ∂Q ≤ ∫ ω, D * c k ω ∂Q := by
        refine integral_mono_ae (hint k k) ((hci k).const_mul D) ?_
        filter_upwards [H.ae_cellSq_le hR n k] with ω h
        exact mul_le_mul_of_nonneg_right h.2 h.1
      rwa [integral_const_mul] at h1
    · simp only [g, h.ne', not_lt.2 h.le, h, ↓reduceIte, zero_add]
      rw [show (fun ω => c k ω * c l ω) = fun ω => c l ω * c k ω from funext fun ω => mul_comm _ _]
      exact (off l k h).le
  -- the tail bound
  have tail : ∀ k, ∑ l ∈ r, (if k < l then ∫ ω, c k ω * J l ω ∂Q else 0) ≤
      d * C * ∫ ω, c k ω ∂Q := by
    intro k
    have e : ∑ l ∈ r, (if k < l then ∫ ω, c k ω * J l ω ∂Q else 0) =
        ∫ ω, c k ω * ∑ l ∈ r.filter (fun l => k < l), J l ω ∂Q := by
      rw [← Finset.sum_filter]
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ fun l _ => hcJ k l]
    rw [e, ← integral_const_mul]
    refine integral_mono_ae ((integrable_finsetSum _ fun l _ =>
      H.integrable_diagJ hst n l).bdd_mul (hmeas k) (hbd k)) ((hci k).const_mul _) ?_
    filter_upwards [H.ae_igood s t, H.ae_cellSq_le hR n k] with ω hω hc
    rw [mul_comm (d * C)]
    exact mul_le_mul_of_nonneg_left (hω.sum_incJ_diag_le hst n _ (Finset.filter_subset _ _)) hc.1
  have e : (fun ω => sqSum N s t n ω ^ 2) = fun ω => ∑ k ∈ r, ∑ l ∈ r, c k ω * c l ω := by
    funext ω
    rw [sq, show sqSum N s t n ω = ∑ k ∈ r, c k ω from rfl, Finset.sum_mul_sum]
  rw [e, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l]
  refine (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hfg k l).trans ?_
  simp only [g, Finset.sum_add_distrib]
  have hdiag : ∑ k ∈ r, ∑ l ∈ r, (if k = l then D * ∫ ω, c k ω ∂Q else 0) =
      D * ∑ k ∈ r, ∫ ω, c k ω ∂Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => by simp [Finset.sum_ite_eq, hk]
  have hswap : ∑ k ∈ r, ∑ l ∈ r, (if l < k then ∫ ω, c l ω * J k ω ∂Q else 0) =
      ∑ k ∈ r, ∑ l ∈ r, (if k < l then ∫ ω, c k ω * J l ω ∂Q else 0) := Finset.sum_comm
  rw [hdiag, hswap]
  have h2 : ∑ k ∈ r, ∑ l ∈ r, (if k < l then ∫ ω, c k ω * J l ω ∂Q else 0) ≤ d * C * (d * C) := by
    refine (Finset.sum_le_sum fun k _ => tail k).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hS1 (by positivity)
  have h1 : D * ∑ k ∈ r, ∫ ω, c k ω ∂Q ≤ D * (d * C) := mul_le_mul_of_nonneg_left hS1 hD0
  nlinarith

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
