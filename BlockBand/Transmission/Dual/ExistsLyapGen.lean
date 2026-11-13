module

public import BlockBand.Transmission.Dual.ExistsLyap

/-!
# `exists_` at `p = 1`: the generator of `g` and the bounds on `g`

For the Lyapunov function `g = S φ` on the flat chamber: `L₁_lyapG` (`𝒟₁ g = D₀ S`),
`one_le_lyapPhi` (`φ ≥ 1`) and `lyapG_toFlat_ge` (`g ≥ ε n` on the boundary of the `n`-th ball
where `S ≥ ε`), with the one-dimensional derivative computations they use.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.Exists

open MeasureTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic

theorem lineX_first {A c d : ℝ} (hc : 0 < c) :
    deriv (fun r : ℝ => (A + r) * (Real.log (1 + c + r) - Real.log (c + r) + d)) 0 =
      (Real.log (1 + c) - Real.log c + d) + A * (1 / (1 + c) - 1 / c) := by
  have h1 : (0 : ℝ) < 1 + c + 0 := by linarith
  have hl1 := hasDerivAt_log_shift (c := 1 + c) (r := 0) h1
  have hl2 := hasDerivAt_log_shift (c := c) (r := 0) (by simpa using hc)
  have := ((hasDerivAt_id (0 : ℝ)).const_add A).mul ((hl1.sub hl2).add_const d)
  have h' : HasDerivAt (fun r : ℝ => (A + r) * (Real.log (1 + c + r) - Real.log (c + r) + d))
      ((Real.log (1 + c) - Real.log c + d) + A * (1 / (1 + c) - 1 / c)) 0 := by
    convert this using 1
    · funext x; simp
    · simp
  exact h'.deriv

theorem lineY_first {A c d : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    deriv (fun r : ℝ => (A + r) * (d - Real.log (c + r) - Real.log (1 - (c + r)))) 0 =
      (d - Real.log c - Real.log (1 - c)) + A * (-(1 / c) + 1 / (1 - c)) := by
  have h0 : (0 : ℝ) < c + 0 := by simpa using hc
  have h1 : (0 : ℝ) < 1 - (c + 0) := by linarith
  have hl1 := hasDerivAt_log_shift (c := c) (r := 0) h0
  have hl2 := hasDerivAt_log_one_sub (c := c) (r := 0) h1
  have := ((hasDerivAt_id (0 : ℝ)).const_add A).mul (((hasDerivAt_const (0 : ℝ) d).sub hl1).sub hl2)
  have h' : HasDerivAt (fun r : ℝ => (A + r) * (d - Real.log (c + r) - Real.log (1 - (c + r))))
      ((d - Real.log c - Real.log (1 - c)) + A * (-(1 / c) + 1 / (1 - c))) 0 := by
    convert this using 1
    · funext x; simp
    · simp only [add_zero, id_eq, Pi.sub_apply, one_mul]; ring
  exact h'.deriv

theorem contDiffAt_lyapG {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) : ContDiffAt ℝ 2 lyapG y := by
  obtain ⟨h0, h1, h2⟩ := mem_flatChamber_one hy
  have c0 : ContDiffAt ℝ 2 (fun y : Fin 2 → ℝ => y 0) y := (contDiff_apply ℝ ℝ 0).contDiffAt
  have c1 : ContDiffAt ℝ 2 (fun y : Fin 2 → ℝ => y 1) y := (contDiff_apply ℝ ℝ 1).contDiffAt
  refine (contDiff_tot.of_le (by simp)).contDiffAt.mul ?_
  refine (((((contDiffAt_const.add c0).log (by positivity)).sub (c0.log h0.ne')).sub
    (c1.log h1.ne')).sub ((contDiffAt_const.sub c1).log (by linarith)))

theorem contDiffOn_lyapG : ContDiffOn ℝ 2 lyapG (flatChamber 1) := fun _ hy =>
  (contDiffAt_lyapG hy).contDiffWithinAt

theorem measurable_lyapG : Measurable lyapG := by
  have c0 : Measurable fun y : Fin 2 → ℝ => y 0 := measurable_pi_apply 0
  have c1 : Measurable fun y : Fin 2 → ℝ => y 1 := measurable_pi_apply 1
  exact measurable_tot.mul ((((measurable_const.add c0).log.sub c0.log).sub c1.log).sub
    (measurable_const.sub c1).log)

/-- **`𝒟₁ g = D₀ S`** on the chamber. -/
theorem L₁_lyapG (D0 : ℝ) {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) :
    L₁ D0 lyapG y = D0 * tot y := by
  obtain ⟨h0, h1, h2⟩ := mem_flatChamber_one hy
  have hc := contDiffAt_lyapG hy
  have hd := hc.differentiableAt (by norm_num)
  have ex : (fun r : ℝ => lyapG (y + r • Pi.single 0 1)) = fun r => (y 0 + y 1 + r) *
      (Real.log (1 + y 0 + r) - Real.log (y 0 + r) + (-Real.log (y 1) - Real.log (1 - y 1))) := by
    funext r
    simp only [lyapG, tot, lyapPhi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero,
      add_zero]
    ring_nf
  have ey : (fun r : ℝ => lyapG (y + r • Pi.single 1 1)) = fun r => (y 0 + y 1 + r) *
      ((Real.log (1 + y 0) - Real.log (y 0)) - Real.log (y 1 + r) - Real.log (1 - (y 1 + r))) := by
    funext r
    simp only [lyapG, tot, lyapPhi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), mul_one, mul_zero,
      add_zero]
    ring_nf
  rw [L₁_eq, fderiv_eq_deriv_line _ hd, fderiv_eq_deriv_line _ hd,
    fderiv_fderiv_eq_deriv_line _ hc, fderiv_fderiv_eq_deriv_line _ hc, ex, ey,
    lineX_first h0, lineX_second h0, lineY_first h1 h2, lineY_second h1 h2,
    flatDrift_one_zero, flatDrift_one_one]
  have h3 : 0 < 1 - y 1 := by linarith
  have h4 : 0 < y 0 + y 1 := by linarith
  have h5 : 0 < 1 + y 0 := by linarith
  unfold tot
  field_simp
  ring

theorem log_le_log_one_add_exp (u : ℝ) : u ≤ Real.log (1 + exp u) :=
  calc u = Real.log (exp u) := (Real.log_exp u).symm
    _ ≤ _ := Real.log_le_log (exp_pos u) (by linarith [exp_pos u])

theorem log_one_add_exp_nonneg (u : ℝ) : 0 ≤ Real.log (1 + exp u) :=
  Real.log_nonneg (by linarith [exp_pos u])

theorem one_lt_neg_log_mul {y : ℝ} (h1 : 0 < y) (h2 : y < 1) :
    1 < -Real.log y - Real.log (1 - y) := by
  have h3 : 0 < 1 - y := by linarith
  have hq : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
  have he : exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hl : Real.log (y * (1 - y)) < -1 := by
    rw [Real.log_lt_iff_lt_exp (mul_pos h1 h3), exp_neg]
    refine lt_of_le_of_lt hq ?_
    rw [lt_inv_comm₀ (by norm_num) (exp_pos 1)]
    linarith
  rw [Real.log_mul h1.ne' h3.ne'] at hl
  linarith

theorem one_le_lyapPhi {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) : 1 ≤ lyapPhi y := by
  obtain ⟨h0, h1, h2⟩ := mem_flatChamber_one hy
  have hx : Real.log (y 0) ≤ Real.log (1 + y 0) := Real.log_le_log h0 (by linarith)
  have := one_lt_neg_log_mul h1 h2
  unfold lyapPhi
  linarith

theorem tot_pos {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) : 0 < tot y := by
  obtain ⟨h0, h1, -⟩ := mem_flatChamber_one hy
  unfold tot; linarith

theorem tot_le_lyapG {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) : tot y ≤ lyapG y := by
  have := one_le_lyapPhi hy
  have := tot_pos hy
  unfold lyapG; nlinarith

theorem lyapG_nonneg {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) : 0 ≤ lyapG y :=
  (tot_pos hy).le.trans (tot_le_lyapG hy)

theorem L₁_lyapG_le {D0 : ℝ} (hD0 : 0 ≤ D0) {y : Fin 2 → ℝ} (hy : y ∈ flatChamber 1) :
    L₁ D0 lyapG y ≤ D0 * lyapG y := by
  rw [L₁_lyapG D0 hy]
  exact mul_le_mul_of_nonneg_left (tot_le_lyapG hy) hD0

theorem continuousOn_L₁_lyapG (D0 : ℝ) : ContinuousOn (L₁ D0 lyapG) (flatChamber 1) :=
  (continuous_const.mul contDiff_tot.continuous).continuousOn.congr fun _ hy => L₁_lyapG D0 hy

theorem continuousOn_L₁_tot (D0 : ℝ) : ContinuousOn (L₁ D0 tot) (flatChamber 1) :=
  continuousOn_const.congr fun _ hy => L₁_tot D0 hy

theorem tot_toFlat (w : Fin 2 → ℝ) : tot (toFlat w) = exp (w 0) + lgt (w 1) := rfl

theorem lyapPhi_toFlat (w : Fin 2 → ℝ) : lyapPhi (toFlat w) =
    (Real.log (1 + exp (w 0)) - w 0) + Real.log (1 + exp (-w 1)) + Real.log (1 + exp (w 1)) := by
  rw [lyapPhi, toFlat_zero, toFlat_one, Real.log_exp, one_sub_lgt, lgt, Real.log_inv,
    Real.log_inv]
  ring

/-- **`g` is large on the boundary of the `n`-th ball where `S ≥ ε`.** -/
theorem lyapG_toFlat_ge {w : Fin 2 → ℝ} {n ε : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ ‖w‖) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hε : ε ≤ tot (toFlat w)) : ε * n ≤ lyapG (toFlat w) := by
  have hS := tot_pos (toFlat_mem w)
  have hΦ := one_le_lyapPhi (toFlat_mem w)
  have a1 := log_le_log_one_add_exp (w 0)
  have a2 := log_le_log_one_add_exp (-w 1)
  have a3 := log_le_log_one_add_exp (w 1)
  have b1 := log_one_add_exp_nonneg (w 0)
  have b2 := log_one_add_exp_nonneg (-w 1)
  have b3 := log_one_add_exp_nonneg (w 1)
  have hcase : n ≤ w 0 ∨ n ≤ -w 0 ∨ n ≤ |w 1| := by
    by_contra hc
    simp only [not_or, not_le] at hc
    have hlt : ‖w‖ < n := by
      have hpos : 0 < n := lt_of_le_of_lt (abs_nonneg _) hc.2.2
      refine (pi_norm_lt_iff hpos).2 fun i => ?_
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
      · simpa [Real.norm_eq_abs] using hc.2.2
    linarith
  unfold lyapG
  rw [lyapPhi_toFlat] at hΦ ⊢
  rcases hcase with h | h | h
  · have he : n ≤ exp (w 0) := by linarith [Real.add_one_le_exp (w 0)]
    have hS' : n ≤ tot (toFlat w) := by
      rw [tot_toFlat]; linarith [lgt_pos (w 1)]
    nlinarith
  · have : n ≤ (Real.log (1 + exp (w 0)) - w 0) + Real.log (1 + exp (-w 1)) +
        Real.log (1 + exp (w 1)) := by linarith
    nlinarith
  · have : n ≤ (Real.log (1 + exp (w 0)) - w 0) + Real.log (1 + exp (-w 1)) +
        Real.log (1 + exp (w 1)) := by
      rcases abs_cases (w 1) with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] at h <;> linarith
    nlinarith

end BlockBand.Transmission.Dual.Exists
