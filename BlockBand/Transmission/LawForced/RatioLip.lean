module

public import BlockBand.Transmission.LawForced.RatioBrQ

/-!
# The weighted source term of the linear mean

The atoms of `wmErr` at `G = gW hT Λ`.
* `lamLip z = Σx_i² + Σy_i²/(1−y_i)`; `abs_dualLam_sub_le`: `|Λ_z(t) − Λ_z(0)| ≤ lamLip·t`
  on `[0,1]`; `abs_dualLam_zero_le`: `|Λ_z(0)| ≤ Λ̂`;
* **`norm_trace_gW_f_le`**: `‖Tr(Gf)‖ ≤ (Λ̂ + lamLip)(‖Tr(Tf)‖ + √g·hs(T,f))`;
* `re_trace_gW_le`: `0 ≤ Re Tr G ≤ Λ̂g`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing
open scoped ComplexOrder

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}

/-- The Lipschitz constant of `Λ_z` on `[0,1]`. -/
def lamLip (z : DualCoord p) : ℝ := ∑ i, z.1 i ^ 2 + ∑ i, z.2 i ^ 2 / (1 - z.2 i)

theorem lamLip_nonneg {z : DualCoord p} (hz : IsRatioRange z.1 z.2) : 0 ≤ lamLip z :=
  add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.sum_nonneg fun i _ =>
    div_nonneg (sq_nonneg _) (by linarith [(hz.2 i).2]))

theorem abs_dualLam_sub_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |dualLam z t - dualLam z 0| ≤ lamLip z * t := by
  have e : dualLam z t - dualLam z 0 = ∑ i, (z.1 i / (1 + z.1 i * t) - z.1 i) +
      ∑ i, (z.2 i / (1 - z.2 i * t) - z.2 i) := by
    unfold dualLam
    simp only [mul_zero, add_zero, sub_zero, div_one, Finset.sum_sub_distrib]
    ring
  rw [e, lamLip, add_mul, Finset.sum_mul, Finset.sum_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  · have hx := hz.1 i
    have hb := (rx_bounds hx ht0).2
    have e1 : z.1 i / (1 + z.1 i * t) - z.1 i = z.1 i * ((1 + z.1 i * t)⁻¹ - 1) := by
      rw [div_eq_mul_inv]; ring
    rw [e1, abs_mul, abs_of_nonneg hx]
    calc z.1 i * |_| ≤ z.1 i * (z.1 i * t) := mul_le_mul_of_nonneg_left hb hx
      _ = _ := by ring
  · have hy0 := (hz.2 i).1
    have hb := (ry_bounds hy0 (hz.2 i).2 ht0 ht1).2
    have e1 : z.2 i / (1 - z.2 i * t) - z.2 i = z.2 i * ((1 + -z.2 i * t)⁻¹ - 1) := by
      rw [div_eq_mul_inv, neg_mul, ← sub_eq_add_neg]; ring
    rw [e1, abs_mul, abs_of_nonneg hy0]
    calc z.2 i * |_| ≤ z.2 i * (z.2 i / (1 - z.2 i) * t) := mul_le_mul_of_nonneg_left hb hy0
      _ = _ := by ring

theorem abs_dualLam_zero_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) :
    |dualLam z 0| ≤ lamHat z :=
  abs_dualLam_le hz le_rfl zero_le_one

theorem norm_trace_gW_f_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) (f : Matrix (Fin W) (Fin W) ℂ) :
    ‖((gW hT fun k => dualLam z (ts_lam hT k)) * f).trace‖ ≤
      (lamHat z + lamLip z) * (‖(T * f).trace‖ + Real.sqrt T.trace.re * hsSandwich T f) := by
  rw [trace_gW_mul]
  have ht0 := ts_lam_nonneg hT
  have h := norm_sum_weight_fd_le hT ht1 f (φ := fun k => dualLam z (ts_lam hT k))
    (φ₀ := dualLam z 0) (lamLip_nonneg hz) fun i => abs_dualLam_sub_le hz (ht0 i) (ht1 i)
  refine h.trans ?_
  have h0 := abs_dualLam_zero_le hz
  have hl := lamLip_nonneg hz
  have hL := lamHat_nonneg hz
  have hA := norm_nonneg (T * f).trace
  have hB : 0 ≤ Real.sqrt T.trace.re * hsSandwich T f :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

theorem re_trace_gW_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) :
    0 ≤ (gW hT fun k => dualLam z (ts_lam hT k)).trace.re ∧
      (gW hT fun k => dualLam z (ts_lam hT k)).trace.re ≤ lamHat z * T.trace.re := by
  rw [trace_gW, Complex.ofReal_re, ← ts_sum_lam hT]
  exact sum_t_dualLam_le hz (ts_lam_nonneg hT) ht1

end BlockBand.Transmission.LawForced
