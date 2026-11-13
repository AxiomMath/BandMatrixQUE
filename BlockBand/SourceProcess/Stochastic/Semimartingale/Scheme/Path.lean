module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Defs
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: pathwise facts on a full-measure set

Fix `s ≤ t`. `GoodPt` collects the countably many almost-sure properties used pathwise
(values in `K`, continuity, Lebesgue measurability of the characteristics, and the
identities defining `N` and `B` at all grid points of `[s, t]`); `SchemeHyp.ae_good` shows
they hold `Q`-a.s. On `GoodPt` we prove: the increment split `ΔZ = ΔN + Δ∫β`, bounds on all
increments, and the exact decomposition
`X_t - X_s = T¹_n + ½ T²_n + (Riemann_n - ∫_s^t 𝓛φ) + ½ Cross_n + Rem_n`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα : ℝ}

/-- The almost-sure properties used pathwise on the grids of `[s, t]`. -/
def GoodPt (K : Set (Fin d → ℝ)) (Z β : ℝ≥0 → Ω → Fin d → ℝ)
    (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ) (N : Fin d → ℝ≥0 → Ω → ℝ)
    (B : Fin d → Fin d → ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (ω : Ω) : Prop :=
  (∀ u, Z u ω ∈ K) ∧ Continuous (fun u => Z u ω) ∧
  (∀ i, AEStronglyMeasurable (fun u : ℝ => β u.toNNReal ω i) volume) ∧
  (∀ i j, AEStronglyMeasurable (fun u : ℝ => α u.toNNReal ω i j) volume) ∧
  (∀ n k i, N i (grid s t n k) ω = Z (grid s t n k) ω i - Z 0 ω i - drI β i (grid s t n k) ω) ∧
  (∀ n k i j, B i j (grid s t n k) ω =
    N i (grid s t n k) ω * N j (grid s t n k) ω - difJ α i j (grid s t n k) ω)

theorem SchemeHyp.ae_good (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (s t : ℝ≥0) :
    ∀ᵐ ω ∂Q, GoodPt K Z β α N B s t ω := by
  have h1 : ∀ᵐ ω ∂Q, ∀ n k i, N i (grid s t n k) ω =
      Z (grid s t n k) ω i - Z 0 ω i - drI β i (grid s t n k) ω := by
    simp only [ae_all_iff]; exact fun n k i => H.mart_eq i _
  have h2 : ∀ᵐ ω ∂Q, ∀ n k i j, B i j (grid s t n k) ω =
      N i (grid s t n k) ω * N j (grid s t n k) ω - difJ α i j (grid s t n k) ω := by
    simp only [ae_all_iff]; exact fun n k i j => H.bracket_eq i j _
  filter_upwards [H.mem, H.cont, H.driftMeas, H.diffMeas, h1, h2] with ω a b c e f g
  exact ⟨a, b, c, e, f, g⟩

section Pathwise

variable {s t : ℝ≥0} {ω : Ω}

theorem GoodPt.intervalIntegrable_β (hω : GoodPt K Z β α N B s t ω)
    (hβ : ∀ t ω i, |β t ω i| ≤ Cβ) (i : Fin d) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => β u.toNNReal ω i) volume a b :=
  intervalIntegrable_of_bound (hω.2.2.1 i) (fun _ => hβ _ _ i) a b

theorem GoodPt.intervalIntegrable_α (hω : GoodPt K Z β α N B s t ω)
    (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) (i j : Fin d) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => α u.toNNReal ω i j) volume a b :=
  intervalIntegrable_of_bound (hω.2.2.2.1 i j) (fun _ => hα _ _ i j) a b

theorem incI_eq (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    (hst : s ≤ t) (n : ℕ) (i : Fin d) (k : ℕ) :
    incI β s t n i k ω = ∫ u in rgrid s t n k..rgrid s t n (k + 1), β u.toNNReal ω i := by
  unfold incI drI
  rw [coe_grid hst, coe_grid hst]
  exact setIntegral_Ioc_sub (hω.intervalIntegrable_β hβ i)
    (by rw [← coe_grid hst]; exact NNReal.coe_nonneg _)
    (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))

theorem incJ_eq (hω : GoodPt K Z β α N B s t ω) (hα : ∀ t ω i j, |α t ω i j| ≤ Cα)
    (hst : s ≤ t) (n : ℕ) (i j : Fin d) (k : ℕ) :
    incJ α s t n i j k ω = ∫ u in rgrid s t n k..rgrid s t n (k + 1), α u.toNNReal ω i j := by
  unfold incJ difJ
  rw [coe_grid hst, coe_grid hst]
  exact setIntegral_Ioc_sub (hω.intervalIntegrable_α hα i j)
    (by rw [← coe_grid hst]; exact NNReal.coe_nonneg _)
    (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))

theorem abs_incI_le (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    (hst : s ≤ t) (n : ℕ) (i : Fin d) (k : ℕ) :
    |incI β s t n i k ω| ≤ Cβ * ((t - s : ℝ) / (n + 1)) := by
  rw [incI_eq hω hβ hst]
  refine (abs_intervalIntegral_le (fun u => hβ _ _ i)
    (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))).trans (le_of_eq ?_)
  rw [rgrid_succ]; ring

theorem abs_incJ_le (hω : GoodPt K Z β α N B s t ω) (hα : ∀ t ω i j, |α t ω i j| ≤ Cα)
    (hst : s ≤ t) (n : ℕ) (i j : Fin d) (k : ℕ) :
    |incJ α s t n i j k ω| ≤ Cα * ((t - s : ℝ) / (n + 1)) := by
  rw [incJ_eq hω hα hst]
  refine (abs_intervalIntegral_le (fun u => hα _ _ i j)
    (rgrid_mono (by exact_mod_cast hst) n (Nat.le_succ k))).trans (le_of_eq ?_)
  rw [rgrid_succ]; ring

/-- `ΔZ = ΔN + Δ∫β` on each grid cell. -/
theorem incZ_eq (hω : GoodPt K Z β α N B s t ω) (n k : ℕ) :
    Z (grid s t n (k + 1)) ω - Z (grid s t n k) ω =
      (fun i => incN N s t n i k ω) + (fun i => incI β s t n i k ω) := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, incN, incI, hω.2.2.2.2.1]
  ring

/-- `Δ∫α = Δ(N^i N^j - B^{ij})` on each grid cell. -/
theorem incJ_eq_bracket (hω : GoodPt K Z β α N B s t ω) (n : ℕ) (i j : Fin d) (k : ℕ) :
    incJ α s t n i j k ω =
      (N i (grid s t n (k + 1)) ω * N j (grid s t n (k + 1)) ω - B i j (grid s t n (k + 1)) ω) -
      (N i (grid s t n k) ω * N j (grid s t n k) ω - B i j (grid s t n k) ω) := by
  simp only [incJ, hω.2.2.2.2.2]
  ring

/-- Bound on `N` at grid points of `[s, t]`. -/
theorem abs_N_grid_le (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    {R : ℝ} (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k ≤ n + 1)
    (i : Fin d) : |N i (grid s t n k) ω| ≤ 2 * R + Cβ * t := by
  rw [hω.2.2.2.2.1]
  have hz : ∀ u, |Z u ω i| ≤ R := fun u =>
    (le_of_eq (Real.norm_eq_abs _).symm).trans ((norm_le_pi_norm _ i).trans (hR _ (hω.1 u)))
  have hg : (grid s t n k : ℝ) ≤ t := by
    have := grid_mono hst n hk; rw [grid_last hst] at this; exact_mod_cast this
  have hI : |drI β i (grid s t n k) ω| ≤ Cβ * t := by
    unfold drI
    have hC : 0 ≤ Cβ := (abs_nonneg _).trans (hβ 0 ω i)
    exact (abs_setIntegral_Ioc_le (fun u => hβ _ _ i) (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hg hC)
  have := hz (grid s t n k); have := hz 0
  calc |Z (grid s t n k) ω i - Z 0 ω i - drI β i (grid s t n k) ω|
      ≤ |Z (grid s t n k) ω i| + |Z 0 ω i| + |drI β i (grid s t n k) ω| := by
        have := abs_sub (Z (grid s t n k) ω i - Z 0 ω i) (drI β i (grid s t n k) ω)
        have := abs_sub (Z (grid s t n k) ω i) (Z 0 ω i)
        linarith
    _ ≤ 2 * R + Cβ * t := by linarith

theorem abs_incN_le (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    {R : ℝ} (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) {k : ℕ} (hk : k < n + 1)
    (i : Fin d) : |incN N s t n i k ω| ≤ 2 * (2 * R + Cβ * t) := by
  unfold incN
  have := abs_N_grid_le hω hβ hR hst n (Nat.succ_le_of_lt hk) i
  have := abs_N_grid_le hω hβ hR hst n hk.le i
  have := abs_sub (N i (grid s t n (k + 1)) ω) (N i (grid s t n k) ω)
  linarith

end Pathwise

end BlockBand.SourceProcess.Stochastic.Semimartingale
