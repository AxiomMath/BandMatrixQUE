module

public import BlockBand.SourceProcess.Stochastic.Dyson.Bounds
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Riemann

/-!
# Lipschitz bounds for the eigenvalue drift away from collisions

* `bv_lip`: on states whose gaps are all `≥ δ > 0`, the drift `b_i(y) = N^{-1}∑_{j≠i}(y_i-y_j)^{-1}`
  is `2/δ²`-Lipschitz in the sup norm;
* `gap_of_near`: points within `δ/4` of a state with gaps `≥ δ` have gaps `≥ δ/2`;
* `exists_gap_lower`: a continuous path of states with distinct coordinates on `[0, u]` has a
  uniform gap `δ > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open Filter Topology Set
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- The eigenvalue drift as a vector field. -/
def bv (N : ℕ) (y : Fin N → ℝ) : Fin N → ℝ := fun i => dysonDrift N y i

theorem measurable_bv : Measurable (bv N) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [bv, dysonDrift]; fun_prop

/-- Gaps at least `δ`. -/
def Gaps (δ : ℝ) (y : Fin N → ℝ) : Prop := ∀ i j, i ≠ j → δ ≤ |y i - y j|

theorem inv_sub_inv_le {a a' δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ |a|) (ha' : δ ≤ |a'|) :
    |1 / a - 1 / a'| ≤ |a - a'| / δ ^ 2 := by
  have h0 : 0 < |a| := hδ.trans_le ha
  have h0' : 0 < |a'| := hδ.trans_le ha'
  have hne : a ≠ 0 := abs_pos.1 h0
  have hne' : a' ≠ 0 := abs_pos.1 h0'
  rw [div_sub_div _ _ hne hne', abs_div, abs_mul, one_mul, mul_one, abs_sub_comm a' a]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  calc δ ^ 2 = δ * δ := sq δ
    _ ≤ |a| * |a'| := mul_le_mul ha ha' hδ.le h0.le

/-- **Lipschitz bound of the drift on states with gaps `≥ δ`.** -/
theorem bv_lip {δ : ℝ} (hδ : 0 < δ) {y y' : Fin N → ℝ} (hy : Gaps δ y) (hy' : Gaps δ y') :
    ‖bv N y - bv N y'‖ ≤ 2 / δ ^ 2 * ‖y - y'‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have hN : (0 : ℝ) < N := by exact_mod_cast (Fin.pos i)
  have hterm : ∀ j ∈ Finset.univ.erase i, |1 / (y i - y j) - 1 / (y' i - y' j)| ≤
      2 * ‖y - y'‖ / δ ^ 2 := fun j hj => by
    have hij : j ≠ i := Finset.ne_of_mem_erase hj
    refine (inv_sub_inv_le hδ (hy i j hij.symm) (hy' i j hij.symm)).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : |y i - y' i| ≤ ‖y - y'‖ := by
      have := norm_le_pi_norm (y - y') i; rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    have h2 : |y j - y' j| ≤ ‖y - y'‖ := by
      have := norm_le_pi_norm (y - y') j; rwa [Pi.sub_apply, Real.norm_eq_abs] at this
    calc |y i - y j - (y' i - y' j)| = |(y i - y' i) - (y j - y' j)| := by ring_nf
      _ ≤ |y i - y' i| + |y j - y' j| := abs_sub _ _
      _ ≤ 2 * ‖y - y'‖ := by linarith
  simp only [bv, dysonDrift]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  calc 1 / (N : ℝ) * |∑ j ∈ Finset.univ.erase i, (1 / (y i - y j) - 1 / (y' i - y' j))|
      ≤ 1 / N * ∑ j ∈ Finset.univ.erase i, 2 * ‖y - y'‖ / δ ^ 2 :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum hterm)) (by positivity)
    _ = 1 / N * ((Finset.univ.erase i).card * (2 * ‖y - y'‖ / δ ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 / N * (N * (2 * ‖y - y'‖ / δ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (card_erase_le i)
          (by positivity)) (by positivity)
    _ = 2 / δ ^ 2 * ‖y - y'‖ := by field_simp

theorem gap_of_near {δ : ℝ} {y z : Fin N → ℝ} (hz : Gaps δ z) (hyz : ‖y - z‖ ≤ δ / 4) :
    Gaps (δ / 2) y := by
  intro i j hij
  have h1 : |y i - z i| ≤ δ / 4 := by
    have := norm_le_pi_norm (y - z) i; rw [Pi.sub_apply, Real.norm_eq_abs] at this; linarith
  have h2 : |y j - z j| ≤ δ / 4 := by
    have := norm_le_pi_norm (y - z) j; rw [Pi.sub_apply, Real.norm_eq_abs] at this; linarith
  have h3 := hz i j hij
  have : |z i - z j| ≤ |y i - y j| + |y i - z i| + |y j - z j| := by
    calc |z i - z j| = |(y i - y j) - (y i - z i) + (y j - z j)| := by ring_nf
      _ ≤ |(y i - y j) - (y i - z i)| + |y j - z j| := abs_add_le _ _
      _ ≤ |y i - y j| + |y i - z i| + |y j - z j| := by linarith [abs_sub (y i - y j) (y i - z i)]
  linarith

theorem Gaps.mono {δ δ' : ℝ} {y : Fin N → ℝ} (h : Gaps δ y) (hδ : δ' ≤ δ) : Gaps δ' y :=
  fun i j hij => hδ.trans (h i j hij)

/-- **A uniform gap along a continuous path of distinct states.** -/
theorem exists_gap_lower {lam : ℝ → Fin N → ℝ} {u : ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn lam (Icc 0 u)) (hd : ∀ r ∈ Icc 0 u, ∀ i j, i ≠ j → lam r i ≠ lam r j) :
    ∃ δ > 0, ∀ r ∈ Icc 0 u, Gaps δ (lam r) := by
  classical
  have hpair : ∀ p : Fin N × Fin N, ∃ d > 0, p.1 ≠ p.2 → ∀ r ∈ Icc 0 u,
      d ≤ |lam r p.1 - lam r p.2| := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun h => absurd hij h⟩
    have hg : ContinuousOn (fun r => |lam r i - lam r j|) (Icc 0 u) :=
      (((continuous_apply i).comp_continuousOn hc).sub
        ((continuous_apply j).comp_continuousOn hc)).abs
    obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hu) hg
    refine ⟨|lam r₀ i - lam r₀ j|, abs_pos.2 (sub_ne_zero.2 (hd r₀ hr₀ i j hij)),
      fun _ r hr => hmin hr⟩
  choose d hd0 hdle using hpair
  set S : Finset ℝ := Finset.univ.image d ∪ {1}
  have hS : S.Nonempty := ⟨1, Finset.mem_union_right _ (Finset.mem_singleton_self 1)⟩
  refine ⟨S.min' hS, ?_, fun r hr i j hij => ?_⟩
  · have hx := S.min'_mem hS
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨p, -, hp⟩ := Finset.mem_image.1 h; rw [← hp]; exact hd0 p
    · rw [Finset.mem_singleton.1 h]; exact one_pos
  · exact (S.min'_le _ (Finset.mem_union_left _ (Finset.mem_image_of_mem d
      (Finset.mem_univ (i, j))))).trans (hdle (i, j) hij r hr)

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
