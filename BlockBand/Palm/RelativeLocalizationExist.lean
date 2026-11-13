module

public import BlockBand.Internal.Contracts.CoareaPalm
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.UnitInterval

/-!
# Relative localization: existence for the linear mass equation

Proof: Picard–Lindelöf (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) for the
globally Lipschitz and bounded field `x ↦ L(t) · clamp_ρ x` (coordinatewise projection on
`[-ρ, ρ]`), then Gronwall (`norm_le_gronwallBound_of_norm_deriv_right_le`) shows that the
solution stays in the region `‖x‖ < ρ = ‖v₀‖ e^{K(u-s)} + 1` where the clamp is the identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set Filter Topology BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {N : ℕ}

/-- Coordinatewise clamp to `[-ρ, ρ]`. -/
def clampVec (ρ : ℝ) (hρ : -ρ ≤ ρ) (x : Fin N → ℝ) : Fin N → ℝ :=
  fun l => (projIcc (-ρ) ρ hρ (x l) : ℝ)

theorem abs_clampVec_sub {ρ : ℝ} (hρ : -ρ ≤ ρ) (x y : Fin N → ℝ) (l : Fin N) :
    |clampVec ρ hρ x l - clampVec ρ hρ y l| ≤ |x l - y l| :=
  abs_projIcc_sub_projIcc hρ

theorem abs_clampVec_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : -ρ ≤ ρ) (x : Fin N → ℝ) (l : Fin N) :
    |clampVec ρ hρ x l| ≤ |x l| := by
  have h := abs_projIcc_sub_projIcc hρ (c := x l) (d := 0)
  have h0 : (projIcc (-ρ) ρ hρ 0 : ℝ) = 0 := by
    rw [projIcc_of_mem hρ ⟨by linarith, hρ0⟩]
  rw [h0, sub_zero, sub_zero] at h
  exact h

theorem abs_clampVec_le_rho {ρ : ℝ} (hρ : -ρ ≤ ρ) (x : Fin N → ℝ) (l : Fin N) :
    |clampVec ρ hρ x l| ≤ ρ :=
  abs_le.mpr (projIcc (-ρ) ρ hρ (x l)).2

theorem clampVec_eq_self {ρ : ℝ} (hρ : -ρ ≤ ρ) {x : Fin N → ℝ} (hx : ‖x‖ ≤ ρ) :
    clampVec ρ hρ x = x := by
  funext l
  have : |x l| ≤ ρ := (norm_le_pi_norm x l).trans hx
  exact congrArg Subtype.val (projIcc_of_mem hρ (abs_le.mp this))

/-- `|Σ_l A_l y_l| ≤ (Σ_l |A_l|) ‖y‖`. -/
theorem abs_sum_mul_le (A y : Fin N → ℝ) :
    |∑ l, A l * y l| ≤ (∑ l, |A l|) * ‖y‖ := by
  calc |∑ l, A l * y l| ≤ ∑ l, |A l * y l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |A l| * ‖y‖ := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y l) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- Existence for the forward mass equation with continuous coefficients. -/
theorem forwardMass_exists {L : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} (hsu : s ≤ u)
    (hL : ContinuousOn L (Icc s u)) (v₀ : Fin N → ℝ) :
    ∃ v, ForwardMassSolution L s u v₀ v := by
  classical
  -- a bound on the coefficients
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := s) (b := u)).exists_bound_of_continuousOn hL
  set M : ℝ := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hentry : ∀ t ∈ Icc s u, ∀ k l, |L t k l| ≤ M := fun t ht k l =>
    ((norm_le_pi_norm (L t k) l).trans (norm_le_pi_norm (L t) k)).trans
      ((hC t ht).trans (le_max_left _ _))
  set K : ℝ := N * M with hK
  have hK0 : 0 ≤ K := by positivity
  have hrow : ∀ t ∈ Icc s u, ∀ k, ∑ l, |L t k l| ≤ K := fun t ht k => by
    calc ∑ l, |L t k l| ≤ ∑ _l : Fin N, M := Finset.sum_le_sum fun l _ => hentry t ht k l
      _ = K := by simp [hK]
  set ρ : ℝ := ‖v₀‖ * Real.exp (K * (u - s)) + 1 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ : -ρ ≤ ρ := by linarith
  set f : ℝ → (Fin N → ℝ) → (Fin N → ℝ) := fun t x k => ∑ l, L t k l * clampVec ρ hρ x l
    with hf
  -- the clamped field is Lipschitz and bounded
  have hlip : ∀ t ∈ Icc s u, ∀ x y : Fin N → ℝ, ‖f t x - f t y‖ ≤ K * ‖x - y‖ := by
    intro t ht x y
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    have : f t x k - f t y k = ∑ l, L t k l * (clampVec ρ hρ x - clampVec ρ hρ y) l := by
      simp only [hf, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [show (f t x - f t y) k = f t x k - f t y k from rfl, this]
    refine (abs_sum_mul_le _ _).trans ?_
    refine mul_le_mul (hrow t ht k) ?_ (norm_nonneg _) hK0
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun l => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    exact (abs_clampVec_sub hρ x y l).trans ((norm_le_pi_norm (x - y) l).trans_eq' rfl)
  have hbound : ∀ t ∈ Icc s u, ∀ x : Fin N → ℝ, ‖f t x‖ ≤ K * ρ := by
    intro t ht x
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    refine (abs_sum_mul_le _ _).trans (mul_le_mul (hrow t ht k) ?_ (norm_nonneg _) hK0)
    exact (pi_norm_le_iff_of_nonneg hρ0.le).mpr fun l => abs_clampVec_le_rho hρ x l
  have hlin : ∀ t ∈ Icc s u, ∀ x : Fin N → ℝ, ‖f t x‖ ≤ K * ‖x‖ := by
    intro t ht x
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    refine (abs_sum_mul_le _ _).trans (mul_le_mul (hrow t ht k) ?_ (norm_nonneg _) hK0)
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun l =>
      (abs_clampVec_le hρ0.le hρ x l).trans (norm_le_pi_norm x l)
  have hcont : ∀ x : Fin N → ℝ, ContinuousOn (fun t => f t x) (Icc s u) := by
    intro x
    refine continuousOn_pi.mpr fun k => ?_
    refine continuousOn_finsetSum _ fun l _ => ?_
    exact (continuousOn_pi.mp (continuousOn_pi.mp hL k) l).mul continuousOn_const
  -- Picard–Lindelöf
  set t₀ : Icc s u := ⟨s, le_rfl, hsu⟩
  have hPL : IsPicardLindelof f t₀ v₀ (Real.toNNReal (K * ρ * (u - s))) 0
      (Real.toNNReal (K * ρ)) (Real.toNNReal K) := by
    refine ⟨fun t ht => ?_, fun x _ => hcont x, fun t ht x _ => ?_, ?_⟩
    · refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_)
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK0]
      exact hlip t ht x y
    · rw [Real.coe_toNNReal _ (by positivity)]; exact hbound t ht x
    · simp only [NNReal.coe_zero, sub_zero]
      rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by
        have : 0 ≤ u - s := by linarith
        positivity)]
      have h1 : max (u - (t₀ : ℝ)) ((t₀ : ℝ) - s) = u - s := by
        simp only [t₀]; rw [sub_self]; exact max_eq_left (by linarith)
      rw [h1]
  obtain ⟨α, hα0, hαd⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hPL
  have hα0' : α s = v₀ := hα0
  have hαc : ContinuousOn α (Icc s u) := fun t ht => (hαd t ht).continuousWithinAt
  -- Gronwall: the solution stays where the clamp is the identity
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := α) (f' := fun t => f t (α t))
    (δ := ‖v₀‖) (K := K) (ε := 0) hαc
    (fun t ht => (hαd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)) (by rw [hα0'])
    (fun t ht => by rw [add_zero]; exact hlin t ⟨ht.1, ht.2.le⟩ (α t))
  have hsmall : ∀ t ∈ Icc s u, ‖α t‖ ≤ ρ := by
    intro t ht
    have := hgr t ht
    rw [gronwallBound_ε0] at this
    have hexp : Real.exp (K * (t - s)) ≤ Real.exp (K * (u - s)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hK0)
    have := mul_le_mul_of_nonneg_left hexp (norm_nonneg v₀)
    rw [hρdef]; linarith
  have hfα : ∀ t ∈ Icc s u, f t (α t) = fun k => ∑ l, L t k l * α t l := by
    intro t ht
    funext k
    simp only [hf, clampVec_eq_self hρ (hsmall t ht)]
  refine ⟨α, hα0', hαc, fun x hx => ?_⟩
  have := (hαd x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  rwa [hfα x ⟨hx.1.le, hx.2.le⟩] at this

end BlockBand.Palm.RelativeLocalization
