module

public import BlockBand.Transmission.Dual.GCauchy
public import BlockBand.Transmission.Dual.ExistsCalc
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothness and the logarithmic derivative of `H_q`

* `contDiffAt_cauchyH`: `H_q = det (1/(x_i + y_j))` is `C^∞` wherever every `x_i + y_j ≠ 0`
  (Leibniz expansion).
* `cauchyH_eq_exp_logH`: on the chamber `H_q = exp (log H_q)` with the explicit
  `logH = Σ_{i<k} (log(x_k − x_i) + log(y_k − y_i)) − Σ_{i,j} log(x_i + y_j)`.
* `fderiv_cauchyH`: `DH_q(z) v = H_q(z) · Σ_{i<k} [(v_{x,k} − v_{x,i})/(x_k − x_i) + (y-terms)] −
  Σ_{i,j} (v_{x,i} + v_{y,j})/(x_i + y_j)`, and in the coordinate directions
  (`fderiv_cauchyH_dirX`, `fderiv_cauchyH_dirY`) exactly the brackets of
  `dualDriftX`, `dualDriftY`: `∂_{x_i} log H_q = Σ_{k≠i} (x_i − x_k)⁻¹ − Σ_j (x_i + y_j)⁻¹`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Matrix Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath

variable {q : ℕ}

/-! ## Smoothness -/

theorem cauchyH_eq_sum (w : DualCoord q) :
    cauchyH q w = ∑ σ : Equiv.Perm (Fin q),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (w.1 (σ i) + w.2 i)⁻¹ := by
  rw [cauchyH, det_apply']; rfl

theorem contDiffAt_cauchyH {z : DualCoord q} (hz : ∀ i j, z.1 i + z.2 j ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (cauchyH q) z := by
  have he : cauchyH q = fun w : DualCoord q => ∑ σ : Equiv.Perm (Fin q),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, (w.1 (σ i) + w.2 i)⁻¹ := funext cauchyH_eq_sum
  rw [he]
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => ?_)
  have hc : ContDiff ℝ (⊤ : ℕ∞) fun w : DualCoord q => w.1 (σ i) + w.2 i :=
    ((contDiff_apply ℝ ℝ (σ i)).comp contDiff_fst).add ((contDiff_apply ℝ ℝ i).comp contDiff_snd)
  exact hc.contDiffAt.inv (hz (σ i) i)

theorem contDiffAt_cauchyH_of_mem {z : DualCoord q} (hz : z ∈ dualChamber q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (cauchyH q) z :=
  contDiffAt_cauchyH fun i j => (add_pos_of_mem hz i j).ne'

/-! ## The logarithm of `H_q` on the chamber -/

/-- `log H_q`, written out with the Cauchy formula. -/
def logH (q : ℕ) (w : DualCoord q) : ℝ :=
  (∑ i : Fin q, ∑ k ∈ Ioi i, (Real.log (w.1 k - w.1 i) + Real.log (w.2 k - w.2 i))) -
    ∑ i : Fin q, ∑ j : Fin q, Real.log (w.1 i + w.2 j)

theorem cauchyH_eq_exp_logH {w : DualCoord q} (hw : w ∈ dualChamber q) :
    cauchyH q w = Real.exp (logH q w) := by
  rw [cauchyH_eq hw, logH, Real.exp_sub, Real.exp_sum, Real.exp_sum]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Real.exp_add, Real.exp_log (sub_pos.2 (hw.1 (mem_Ioi.1 hk))),
      Real.exp_log (sub_pos.2 (hw.2.1 (mem_Ioi.1 hk)))]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (add_pos_of_mem hw i j)).symm

/-- The logarithmic derivative of `H_q` at `z` in the direction `v`. -/
def logDerivH (z v : DualCoord q) : ℝ :=
  (∑ i : Fin q, ∑ k ∈ Ioi i,
      ((v.1 k - v.1 i) / (z.1 k - z.1 i) + (v.2 k - v.2 i) / (z.2 k - z.2 i))) -
    ∑ i : Fin q, ∑ j : Fin q, (v.1 i + v.2 j) / (z.1 i + z.2 j)

theorem line_fst (z v : DualCoord q) (r : ℝ) (k : Fin q) :
    (z + r • v).1 k = z.1 k + r * v.1 k := by simp

theorem line_snd (z v : DualCoord q) (r : ℝ) (k : Fin q) :
    (z + r • v).2 k = z.2 k + r * v.2 k := by simp

private theorem hasDerivAt_log_affine (a c : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun r : ℝ => Real.log (a + r * c)) (c / a) 0 := by
  have h : HasDerivAt (fun r : ℝ => a + r * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).const_add a
  simpa using h.log (by simpa using ha)

theorem hasDerivAt_logH_line {z : DualCoord q} (hz : z ∈ dualChamber q) (v : DualCoord q) :
    HasDerivAt (fun r : ℝ => logH q (z + r • v)) (logDerivH z v) 0 := by
  have e : (fun r : ℝ => logH q (z + r • v)) = fun r =>
      (∑ i : Fin q, ∑ k ∈ Ioi i,
        (Real.log ((z.1 k - z.1 i) + r * (v.1 k - v.1 i)) +
          Real.log ((z.2 k - z.2 i) + r * (v.2 k - v.2 i)))) -
      ∑ i : Fin q, ∑ j : Fin q, Real.log ((z.1 i + z.2 j) + r * (v.1 i + v.2 j)) := by
    funext r
    simp only [logH, line_fst, line_snd]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      congr 2 <;> ring
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      congr 1; ring
  rw [e]
  refine HasDerivAt.sub (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun k hk => ?_)
    (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_)
  · exact (hasDerivAt_log_affine _ _ (sub_pos.2 (hz.1 (mem_Ioi.1 hk))).ne').add
      (hasDerivAt_log_affine _ _ (sub_pos.2 (hz.2.1 (mem_Ioi.1 hk))).ne')
  · exact hasDerivAt_log_affine _ _ (add_pos_of_mem hz i j).ne'

theorem hasDerivAt_cauchyH_line {z : DualCoord q} (hz : z ∈ dualChamber q) (v : DualCoord q) :
    HasDerivAt (fun r : ℝ => cauchyH q (z + r • v)) (cauchyH q z * logDerivH z v) 0 := by
  have hc : Continuous fun r : ℝ => z + r • v := continuous_const.add
    (continuous_id.smul continuous_const)
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), z + r • v ∈ dualChamber q :=
    hc.continuousAt.preimage_mem_nhds (by simpa using (isOpen_dualChamber q).mem_nhds hz)
  have h := (hasDerivAt_logH_line hz v).exp
  rw [show (0 : ℝ) = (0 : ℝ) from rfl] at h
  simp only [zero_smul, add_zero] at h
  rw [← cauchyH_eq_exp_logH hz] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hev] with r hr using cauchyH_eq_exp_logH hr

/-- **The derivative of `H_q`**: `DH_q(z) v = H_q(z) · logDerivH z v` on the chamber. -/
theorem fderiv_cauchyH {z : DualCoord q} (hz : z ∈ dualChamber q) (v : DualCoord q) :
    fderiv ℝ (cauchyH q) z v = cauchyH q z * logDerivH z v := by
  rw [Exists.fderiv_eq_deriv_line v
    ((contDiffAt_cauchyH_of_mem hz).differentiableAt (by simp))]
  exact (hasDerivAt_cauchyH_line hz v).deriv

/-! ## The coordinate directions -/

/-- `Σ_{i<k} (s_k − s_i)/(w_k − w_i)` for `s = 𝟙_{m}` is `Σ_{k ≠ m} 1/(w_m − w_k)`. -/
theorem sum_Ioi_single (w : Fin q → ℝ) (m : Fin q) :
    ∑ i : Fin q, ∑ k ∈ Ioi i, ((Pi.single m (1 : ℝ) : Fin q → ℝ) k -
        (Pi.single m (1 : ℝ) : Fin q → ℝ) i) / (w k - w i) =
      ∑ k ∈ univ.erase m, 1 / (w m - w k) := by
  have h1 : ∑ i : Fin q, ∑ k ∈ Ioi i, (Pi.single m (1 : ℝ) : Fin q → ℝ) k / (w k - w i) =
      ∑ i ∈ univ.filter (· < m), 1 / (w m - w i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.single_apply, ite_div, zero_div, Finset.sum_ite_eq', mem_Ioi]
  have h2 : ∑ i : Fin q, ∑ k ∈ Ioi i, (Pi.single m (1 : ℝ) : Fin q → ℝ) i / (w k - w i) =
      ∑ k ∈ Ioi m, 1 / (w k - w m) := by
    simp only [Pi.single_apply, ite_div, zero_div, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', mem_univ, ite_true]
  have hsplit : univ.erase m = univ.filter (· < m) ∪ Ioi m := by
    ext k; simp only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and, mem_Ioi]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : Disjoint (univ.filter (· < m)) (Ioi m) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_filter, mem_univ, true_and] at hk
    exact lt_asymm hk (mem_Ioi.1 hk')
  simp only [sub_div, Finset.sum_sub_distrib]
  rw [h1, h2, hsplit, Finset.sum_union hdisj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show w m - w k = -(w k - w m) by ring, div_neg]

theorem logDerivH_dirX (z : DualCoord q) (m : Fin q) :
    logDerivH z (dirX m) =
      (∑ k ∈ univ.erase m, 1 / (z.1 m - z.1 k)) - ∑ j, 1 / (z.1 m + z.2 j) := by
  have hB : ∑ i : Fin q, ∑ j : Fin q,
      ((Pi.single m (1 : ℝ) : Fin q → ℝ) i + (0 : Fin q → ℝ) j) / (z.1 i + z.2 j) =
      ∑ j, 1 / (z.1 m + z.2 j) := by
    rw [Finset.sum_eq_single m (fun i _ hi => by simp [hi]) (by simp)]
    simp
  have hA : ∑ i : Fin q, ∑ k ∈ Ioi i,
      (((Pi.single m (1 : ℝ) : Fin q → ℝ) k - (Pi.single m (1 : ℝ) : Fin q → ℝ) i) /
        (z.1 k - z.1 i) + ((0 : Fin q → ℝ) k - (0 : Fin q → ℝ) i) / (z.2 k - z.2 i)) =
      ∑ k ∈ univ.erase m, 1 / (z.1 m - z.1 k) := by
    rw [← sum_Ioi_single z.1 m]; simp
  exact (congrArg₂ (· - ·) hA hB : _)

theorem logDerivH_dirY (z : DualCoord q) (m : Fin q) :
    logDerivH z (dirY m) =
      (∑ l ∈ univ.erase m, 1 / (z.2 m - z.2 l)) - ∑ i, 1 / (z.1 i + z.2 m) := by
  have hB : ∑ i : Fin q, ∑ j : Fin q,
      ((0 : Fin q → ℝ) i + (Pi.single m (1 : ℝ) : Fin q → ℝ) j) / (z.1 i + z.2 j) =
      ∑ i, 1 / (z.1 i + z.2 m) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single m (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hA : ∑ i : Fin q, ∑ k ∈ Ioi i,
      (((0 : Fin q → ℝ) k - (0 : Fin q → ℝ) i) / (z.1 k - z.1 i) +
        ((Pi.single m (1 : ℝ) : Fin q → ℝ) k - (Pi.single m (1 : ℝ) : Fin q → ℝ) i) /
          (z.2 k - z.2 i)) =
      ∑ l ∈ univ.erase m, 1 / (z.2 m - z.2 l) := by
    rw [← sum_Ioi_single z.2 m]; simp
  exact (congrArg₂ (· - ·) hA hB : _)

theorem fderiv_cauchyH_dirX {z : DualCoord q} (hz : z ∈ dualChamber q) (m : Fin q) :
    fderiv ℝ (cauchyH q) z (dirX m) = cauchyH q z *
      ((∑ k ∈ univ.erase m, 1 / (z.1 m - z.1 k)) - ∑ j, 1 / (z.1 m + z.2 j)) := by
  rw [fderiv_cauchyH hz, logDerivH_dirX]

theorem fderiv_cauchyH_dirY {z : DualCoord q} (hz : z ∈ dualChamber q) (m : Fin q) :
    fderiv ℝ (cauchyH q) z (dirY m) = cauchyH q z *
      ((∑ l ∈ univ.erase m, 1 / (z.2 m - z.2 l)) - ∑ i, 1 / (z.1 i + z.2 m)) := by
  rw [fderiv_cauchyH hz, logDerivH_dirY]

end BlockBand.Transmission.Dual.G
