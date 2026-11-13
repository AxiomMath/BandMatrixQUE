module

public import BlockBand.Palm.RelativeLocalizationExist
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# Relative localization: Picard iterates converge (deterministic part)

For continuous coefficients `L`, the Picard iterates `v₀ + ∫_0^t L(r) v_n(r) dr` of the forward
mass equation converge pointwise to any solution, with the error bound `B (Kt)^n / n!`
(`picardIter_err_le`, `tendsto_picardIter`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set Filter Topology MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open scoped Nat

variable {N : ℕ}

/-- Matrix action `(L x)_k = Σ_l L_kl x_l`. -/
def matAct (L : Fin N → Fin N → ℝ) (x : Fin N → ℝ) : Fin N → ℝ := fun k => ∑ l, L k l * x l

/-- Picard iterates of the linear mass equation from time `0`. -/
def picardIter (L : ℝ → Fin N → Fin N → ℝ) (v₀ : Fin N → ℝ) : ℕ → ℝ → Fin N → ℝ
  | 0 => fun _ => v₀
  | n + 1 => fun t => v₀ + ∫ r in (0 : ℝ)..t, matAct (L r) (picardIter L v₀ n r)

theorem continuous_matAct {L : ℝ → Fin N → Fin N → ℝ} (hL : Continuous L)
    {x : ℝ → Fin N → ℝ} (hx : Continuous x) : Continuous fun r => matAct (L r) (x r) := by
  refine continuous_pi fun k => ?_
  exact continuous_finsetSum _ fun l _ =>
    (((continuous_apply l).comp ((continuous_apply k).comp hL))).mul ((continuous_apply l).comp hx)

theorem continuousOn_matAct {L : ℝ → Fin N → Fin N → ℝ} {S : Set ℝ} (hL : ContinuousOn L S)
    {x : ℝ → Fin N → ℝ} (hx : ContinuousOn x S) :
    ContinuousOn (fun r => matAct (L r) (x r)) S := by
  refine continuousOn_pi.mpr fun k => ?_
  exact continuousOn_finsetSum _ fun l _ =>
    (continuousOn_pi.mp (continuousOn_pi.mp hL k) l).mul (continuousOn_pi.mp hx l)

theorem picardIter_continuous {L : ℝ → Fin N → Fin N → ℝ} (hL : Continuous L)
    (v₀ : Fin N → ℝ) (n : ℕ) : Continuous (picardIter L v₀ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => (continuous_matAct hL ih).intervalIntegrable a b) 0)

theorem norm_matAct_le {L : Fin N → Fin N → ℝ} {K : ℝ} (hK : ∀ k, ∑ l, |L k l| ≤ K)
    (hK0 : 0 ≤ K) (x : Fin N → ℝ) : ‖matAct L x‖ ≤ K * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  rw [Real.norm_eq_abs]
  exact (abs_sum_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hK k) (norm_nonneg _))

theorem matAct_sub (L : Fin N → Fin N → ℝ) (x y : Fin N → ℝ) :
    matAct L x - matAct L y = matAct L (x - y) := by
  funext k; simp [matAct, mul_sub, Finset.sum_sub_distrib]

/-- Integral form of a solution: `v(t) = v₀ + ∫₀ᵗ L v`. -/
theorem forwardMass_integral {L : ℝ → Fin N → Fin N → ℝ} {T : ℝ} (hL : ContinuousOn L (Icc 0 T))
    {v₀ : Fin N → ℝ} {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L 0 T v₀ v) {t : ℝ}
    (ht : t ∈ Icc 0 T) : v t = v₀ + ∫ r in (0 : ℝ)..t, matAct (L r) (v r) := by
  obtain ⟨h0, hc, hd⟩ := hv
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hc.mono hsub)
    (fun x hx => hd x ⟨hx.1, hx.2.trans_le ht.2⟩)
    ((continuousOn_matAct (hL.mono hsub) (hc.mono hsub)).intervalIntegrable_of_Icc ht.1)
  have heq : (∫ r in (0 : ℝ)..t, matAct (L r) (v r)) =
      ∫ r in (0 : ℝ)..t, fun k => ∑ l, L r k l * v r l := rfl
  rw [heq, this, h0]; abel

/-- **Picard error bound.** -/
theorem picardIter_err_le {L : ℝ → Fin N → Fin N → ℝ} (hL : Continuous L) {T K B : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ r ∈ Icc 0 T, ∀ k, ∑ l, |L r k l| ≤ K) {v₀ : Fin N → ℝ}
    {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L 0 T v₀ v)
    (hB : ∀ t ∈ Icc 0 T, ‖v₀ - v t‖ ≤ B) (n : ℕ) :
    ∀ t ∈ Icc 0 T, ‖picardIter L v₀ n t - v t‖ ≤ B * (K * t) ^ n / n ! := by
  induction n with
  | zero => intro t ht; simpa [picardIter] using hB t ht
  | succ n ih =>
    intro t ht
    have hvc : ContinuousOn v (Icc 0 T) := hv.2.1
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hrepr := forwardMass_integral hL.continuousOn hv ht
    have hc1 : ContinuousOn (fun r => matAct (L r) (picardIter L v₀ n r)) (Icc 0 t) :=
      (continuous_matAct hL (picardIter_continuous hL v₀ n)).continuousOn
    have hc2 : ContinuousOn (fun r => matAct (L r) (v r)) (Icc 0 t) :=
      continuousOn_matAct hL.continuousOn (hvc.mono hsub)
    have hdiff : picardIter L v₀ (n + 1) t - v t =
        ∫ r in (0 : ℝ)..t, matAct (L r) (picardIter L v₀ n r - v r) := by
      rw [hrepr]
      simp only [picardIter]
      rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (hc1.intervalIntegrable_of_Icc ht.1) (hc2.intervalIntegrable_of_Icc ht.1)]
      exact intervalIntegral.integral_congr fun r _ => matAct_sub _ _ _
    rw [hdiff]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, ht.1.trans ht.2⟩)
    calc ‖∫ r in (0 : ℝ)..t, matAct (L r) (picardIter L v₀ n r - v r)‖
        ≤ ∫ r in (0 : ℝ)..t, K * (B * (K * r) ^ n / n !) := by
          refine intervalIntegral.norm_integral_le_of_norm_le ht.1
            (Eventually.of_forall fun r hr => ?_) (Continuous.intervalIntegrable (by fun_prop) _ _)
          have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.trans ht.2⟩
          exact (norm_matAct_le (hK r hr') hK0 _).trans
            (mul_le_mul_of_nonneg_left (ih r hr') hK0)
      _ = B * (K * t) ^ (n + 1) / (n + 1)! := by
          have : (fun r : ℝ => K * (B * (K * r) ^ n / n !)) =
              fun r => (B * K ^ (n + 1) / n !) * r ^ n := by
            funext r; rw [mul_pow]; ring
          rw [this, intervalIntegral.integral_const_mul, integral_pow]
          rw [Nat.factorial_succ]; push_cast
          field_simp
          ring

/-- **Picard convergence.** -/
theorem tendsto_picardIter {L : ℝ → Fin N → Fin N → ℝ} (hL : Continuous L) {T : ℝ}
    {v₀ : Fin N → ℝ} {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L 0 T v₀ v) {t : ℝ}
    (ht : t ∈ Icc 0 T) : Tendsto (fun n => picardIter L v₀ n t) atTop (𝓝 (v t)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hL.continuousOn
  set M := max C 0
  have hM0 : 0 ≤ M := le_max_right _ _
  set K : ℝ := N * M
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ r ∈ Icc 0 T, ∀ k, ∑ l, |L r k l| ≤ K := fun r hr k => by
    calc ∑ l, |L r k l| ≤ ∑ _l : Fin N, M := Finset.sum_le_sum fun l _ =>
          ((norm_le_pi_norm (L r k) l).trans (norm_le_pi_norm (L r) k)).trans
            ((hC r hr).trans (le_max_left _ _))
      _ = K := by simp [K]
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuousOn_const.sub hv.2.1 : ContinuousOn (fun t => v₀ - v t) (Icc 0 T))
  have herr := picardIter_err_le hL hK0 hK hv hB
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => B * (K * t) ^ n / n !) atTop (𝓝 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (K * t)).const_mul B
    simpa [mul_div_assoc] using this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => herr n t ht) hlim

end BlockBand.Palm.RelativeLocalization
