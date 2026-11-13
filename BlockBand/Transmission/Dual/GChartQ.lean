module

public import BlockBand.Transmission.Dual.UniqueReg
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A global chart of the chamber `𝒞_q`

* `x_k = Σ_{l ≤ k} e^{u_l}` (`cumExp`), and
* `y_j = 1 − exp(−Σ_{l ≤ j} e^{v_l})` (`yOf ∘ cumExp`).
`chartQ q` maps `ℝ^{q+q}` into the flat chamber (`chartQ_mem`); its inverse on the chamber is
`chartQInv q` (log-gaps of `x` and of `−log(1 − y)`): `chartQInv_chartQ`, `chartQ_chartQInv`.
`chartQ` is `C^∞` and `chartQInv` is differentiable at every point of the chamber, so `D chartQ`
is invertible everywhere (`exists_equiv_fderiv_of_leftInverse`). The flat square root
`flatSigma a = √(flatDiffDiag_a) e_a` is `C^∞` on the chamber and `Σ_a σ_a σ_aᵀ = flatDiff`
(`flatSigma_cov`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual

variable {q : ℕ}

/-!
## Cumulative exponentials and log-gaps on `Fin q`
-/

/-- `ℕ`-indexed `exp ∘ u`, extended by `0`. -/
def expExt (u : Fin q → ℝ) (l : ℕ) : ℝ := if h : l < q then exp (u ⟨l, h⟩) else 0

/-- `Σ_{l ≤ k} e^{u_l}`. -/
def cumExp (u : Fin q → ℝ) (k : Fin q) : ℝ := ∑ l ∈ Finset.range (k.val + 1), expExt u l

/-- The previous value (`0` before the first index). -/
def prevVal (s : Fin q → ℝ) (k : Fin q) : ℝ :=
  if h : k.val = 0 then 0 else s ⟨k.val - 1, by omega⟩

/-- `log(s_k − s_{k−1})`. -/
def logGap (s : Fin q → ℝ) (k : Fin q) : ℝ := Real.log (s k - prevVal s k)

theorem expExt_nonneg (u : Fin q → ℝ) (l : ℕ) : 0 ≤ expExt u l := by
  unfold expExt; split_ifs <;> positivity

theorem expExt_of_lt (u : Fin q → ℝ) {l : ℕ} (h : l < q) : expExt u l = exp (u ⟨l, h⟩) := by
  simp [expExt, h]

theorem cumExp_sub_prevVal (u : Fin q → ℝ) (k : Fin q) :
    cumExp u k - prevVal (cumExp u) k = exp (u k) := by
  have hk : expExt u k.val = exp (u k) := expExt_of_lt u k.2
  unfold prevVal cumExp
  split_ifs with h
  · rw [h] at hk; simp [h, hk]
  · have e : k.val - 1 + 1 = k.val := by omega
    simp only [e, Finset.sum_range_succ, hk]
    ring

theorem logGap_cumExp (u : Fin q → ℝ) : logGap (cumExp u) = u := by
  funext k; rw [logGap, cumExp_sub_prevVal, log_exp]

theorem cumExp_logGap {s : Fin q → ℝ} (hs : ∀ k, prevVal s k < s k) : cumExp (logGap s) = s := by
  have key : ∀ m (hm : m < q), ∑ l ∈ Finset.range (m + 1), expExt (logGap s) l = s ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 := hs ⟨0, hm⟩
      simp only [zero_add, Finset.sum_range_one, expExt_of_lt _ hm, logGap,
        exp_log (sub_pos.2 h0)]
      simp [prevVal]
    | succ m ih =>
      intro hm
      have h1 := hs ⟨m + 1, hm⟩
      rw [Finset.sum_range_succ, ih (by omega), expExt_of_lt _ hm, logGap, exp_log (sub_pos.2 h1)]
      simp [prevVal]
  funext k
  exact key k.val k.2

theorem cumExp_pos (u : Fin q → ℝ) (k : Fin q) : 0 < cumExp u k := by
  have h := cumExp_sub_prevVal u k
  have hp : 0 ≤ prevVal (cumExp u) k := by
    unfold prevVal; split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun l _ => expExt_nonneg u l
  linarith [exp_pos (u k)]

theorem strictMono_cumExp (u : Fin q → ℝ) : StrictMono (cumExp u) := by
  intro k k' hkk'
  have hlt : k.val < k'.val := hkk'
  refine Finset.sum_lt_sum_of_subset (i := k'.val) (Finset.range_subset_range.2 (by omega))
    (Finset.mem_range.2 (by omega)) (by simp; omega) ?_ fun j _ _ => expExt_nonneg u j
  rw [expExt_of_lt u k'.2]; exact exp_pos _

theorem prevVal_lt_of_strictMono {s : Fin q → ℝ} (hs : StrictMono s) (h0 : ∀ k, 0 < s k)
    (k : Fin q) : prevVal s k < s k := by
  unfold prevVal
  split_ifs with h
  · exact h0 k
  · exact hs (Fin.mk_lt_mk.2 (by omega) : (⟨k.val - 1, by omega⟩ : Fin q) < k)

theorem contDiff_cumExp_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → Fin q → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : Fin q) :
    ContDiff ℝ (⊤ : ℕ∞) fun w => cumExp (u w) k := by
  refine ContDiff.sum fun l _ => ?_
  unfold expExt
  split_ifs
  · exact contDiff_exp.comp ((contDiff_apply ℝ ℝ _).comp hu)
  · exact contDiff_const

/-!
## The `y` coordinates
-/

/-- `r ↦ 1 − e^{−r}`. -/
def yOf (r : ℝ) : ℝ := 1 - exp (-r)

/-- Its inverse `y ↦ −log(1 − y)`. -/
def yInv (y : ℝ) : ℝ := -Real.log (1 - y)

theorem strictMono_yOf : StrictMono yOf := fun a b h => by
  unfold yOf; have := exp_lt_exp.2 (neg_lt_neg h); linarith

theorem yOf_pos {r : ℝ} (hr : 0 < r) : 0 < yOf r := by
  unfold yOf; have := Real.exp_lt_one_iff.2 (neg_neg_of_pos hr); linarith

theorem yOf_lt_one (r : ℝ) : yOf r < 1 := by unfold yOf; linarith [exp_pos (-r)]

theorem yInv_yOf (r : ℝ) : yInv (yOf r) = r := by simp [yInv, yOf]

theorem yOf_yInv {y : ℝ} (hy : y < 1) : yOf (yInv y) = y := by
  simp [yInv, yOf, exp_log (sub_pos.2 hy)]

theorem yInv_pos {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 0 < yInv y := by
  unfold yInv; have := Real.log_neg (sub_pos.2 h1) (by linarith); linarith

theorem strictMonoOn_yInv {y y' : ℝ} (h : y < y') (h1 : y' < 1) : yInv y < yInv y' := by
  unfold yInv
  have := Real.log_lt_log (sub_pos.2 h1) (by linarith : 1 - y' < 1 - y)
  linarith

/-!
## The chart
-/

theorem ofFlat_append (a b : Fin q → ℝ) : ofFlat q (Fin.append a b) = (a, b) := by
  rw [ofFlat_apply]; ext i
  · exact Fin.append_left a b i
  · exact Fin.append_right a b i

/-- The global chart of the flat chamber. -/
def chartQ (q : ℕ) (w : Fin (q + q) → ℝ) : Fin (q + q) → ℝ :=
  Fin.append (cumExp (ofFlat q w).1) (fun j => yOf (cumExp (ofFlat q w).2 j))

/-- Its inverse on the chamber (log-gaps). -/
def chartQInv (q : ℕ) (z : Fin (q + q) → ℝ) : Fin (q + q) → ℝ :=
  Fin.append (logGap (ofFlat q z).1) (logGap fun j => yInv ((ofFlat q z).2 j))

theorem chartQ_mem (w : Fin (q + q) → ℝ) : chartQ q w ∈ flatChamber q := by
  show ofFlat q (chartQ q w) ∈ dualChamber q
  rw [chartQ, ofFlat_append]
  exact ⟨strictMono_cumExp _, strictMono_yOf.comp (strictMono_cumExp _),
    fun i => cumExp_pos _ i, fun j => ⟨yOf_pos (cumExp_pos _ j), yOf_lt_one _⟩⟩

theorem chartQInv_chartQ (w : Fin (q + q) → ℝ) : chartQInv q (chartQ q w) = w := by
  rw [chartQInv, chartQ, ofFlat_append]
  simp only [yInv_yOf, logGap_cumExp]
  have h1 : (ofFlat q w).1 = fun i => w (Fin.castAdd q i) := by rw [ofFlat_apply]
  have h2 : (ofFlat q w).2 = fun j => w (Fin.natAdd q j) := by rw [ofFlat_apply]
  rw [h1, h2]
  exact Fin.append_castAdd_natAdd

theorem chartQ_chartQInv {z : Fin (q + q) → ℝ} (hz : z ∈ flatChamber q) :
    chartQ q (chartQInv q z) = z := by
  have hz' : ofFlat q z ∈ dualChamber q := hz
  obtain ⟨hx, hy, hx0, hy0⟩ := hz'
  rw [chartQ, chartQInv, ofFlat_append]
  have e1 : cumExp (logGap (ofFlat q z).1) = (ofFlat q z).1 :=
    cumExp_logGap (prevVal_lt_of_strictMono hx hx0)
  have hyi : StrictMono fun j => yInv ((ofFlat q z).2 j) := fun j j' h =>
    strictMonoOn_yInv (hy h) (hy0 j').2
  have e2 : cumExp (logGap fun j => yInv ((ofFlat q z).2 j)) = fun j => yInv ((ofFlat q z).2 j) :=
    cumExp_logGap (prevVal_lt_of_strictMono hyi fun j => yInv_pos (hy0 j).1 (hy0 j).2)
  rw [e1, e2]
  simp only [fun j => yOf_yInv (hy0 j).2]
  rw [ofFlat_apply]
  exact Fin.append_castAdd_natAdd

theorem contDiff_ofFlat_fst : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (q + q) → ℝ => (ofFlat q w).1 :=
  contDiff_fst.comp (ofFlat q).contDiff

theorem contDiff_ofFlat_snd : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (q + q) → ℝ => (ofFlat q w).2 :=
  contDiff_snd.comp (ofFlat q).contDiff

theorem contDiff_chartQ : ContDiff ℝ (⊤ : ℕ∞) (chartQ q) := by
  refine contDiff_pi.2 fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [chartQ, Fin.append_left]
    exact contDiff_cumExp_apply contDiff_ofFlat_fst i
  · simp only [chartQ, Fin.append_right]
    exact (contDiff_const.sub (contDiff_exp.comp
      (contDiff_cumExp_apply contDiff_ofFlat_snd j).neg))

/-!
## Differentiability of the inverse; the flat square root
-/

theorem differentiableAt_prevVal_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : E → Fin q → ℝ} {z : E} (hs : ∀ k, DifferentiableAt ℝ (fun w => s w k) z) (k : Fin q) :
    DifferentiableAt ℝ (fun w => prevVal (s w) k) z := by
  unfold prevVal
  split_ifs
  · exact differentiableAt_const _
  · exact hs _

theorem differentiableAt_logGap_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : E → Fin q → ℝ} {z : E} (hs : ∀ k, DifferentiableAt ℝ (fun w => s w k) z)
    (hpos : ∀ k, prevVal (s z) k < s z k) (k : Fin q) :
    DifferentiableAt ℝ (fun w => logGap (s w) k) z :=
  ((hs k).sub (differentiableAt_prevVal_comp hs k)).log (sub_pos.2 (hpos k)).ne'

theorem differentiableAt_chartQInv {z : Fin (q + q) → ℝ} (hz : z ∈ flatChamber q) :
    DifferentiableAt ℝ (chartQInv q) z := by
  have hz' : ofFlat q z ∈ dualChamber q := hz
  obtain ⟨hx, hy, hx0, hy0⟩ := hz'
  have dx : ∀ k, DifferentiableAt ℝ (fun w : Fin (q + q) → ℝ => (ofFlat q w).1 k) z := fun k =>
    ((contDiff_apply ℝ ℝ k).comp contDiff_ofFlat_fst).differentiable (by simp) z
  have dy : ∀ k, DifferentiableAt ℝ (fun w : Fin (q + q) → ℝ => yInv ((ofFlat q w).2 k)) z :=
    fun k => by
      have h1 : DifferentiableAt ℝ (fun w : Fin (q + q) → ℝ => (ofFlat q w).2 k) z :=
        ((contDiff_apply ℝ ℝ k).comp contDiff_ofFlat_snd).differentiable (by simp) z
      exact ((differentiableAt_const _).sub h1).log (sub_pos.2 (hy0 k).2).ne' |>.neg
  have hyi : StrictMono fun j => yInv ((ofFlat q z).2 j) := fun j j' h =>
    strictMonoOn_yInv (hy h) (hy0 j').2
  refine differentiableAt_pi.2 fun k => Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [chartQInv, Fin.append_left]
    exact differentiableAt_logGap_comp dx (prevVal_lt_of_strictMono hx hx0) i
  · simp only [chartQInv, Fin.append_right]
    exact differentiableAt_logGap_comp (s := fun w j => yInv ((ofFlat q w).2 j)) dy
      (prevVal_lt_of_strictMono hyi fun j => yInv_pos (hy0 j).1 (hy0 j).2) j

theorem chartQ_injective : Function.Injective (chartQ q) := fun a b h => by
  rw [← chartQInv_chartQ a, h, chartQInv_chartQ]

/-- The flat square root `σ_a = √(flatDiffDiag_a) e_a`. -/
def flatSigma (D0 : ℝ) (q : ℕ) (a : Fin (q + q)) (z : Fin (q + q) → ℝ) : Fin (q + q) → ℝ :=
  Pi.single a (Real.sqrt (flatDiffDiag D0 q z a))

theorem flatDiffDiag_pos {D0 : ℝ} (hD0 : 0 < D0) {z : Fin (q + q) → ℝ} (hz : z ∈ flatChamber q)
    (k : Fin (q + q)) : 0 < flatDiffDiag D0 q z k := by
  have hz' : ofFlat q z ∈ dualChamber q := hz
  obtain ⟨-, -, hx0, hy0⟩ := hz'
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [flatDiffDiag, Fin.append_left]
    have := hx0 i; positivity
  · simp only [flatDiffDiag, Fin.append_right]
    have := hy0 j
    exact mul_pos hD0 (mul_pos this.1 (by linarith [this.2]))

theorem contDiffOn_flatSigma {D0 : ℝ} (hD0 : 0 < D0) (a : Fin (q + q)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (flatSigma D0 q a) (flatChamber q) := by
  intro z hz
  refine (ContDiffAt.contDiffWithinAt ?_)
  refine contDiffAt_pi.2 fun i => ?_
  by_cases h : i = a
  · subst h
    simp only [flatSigma, Pi.single_eq_same]
    exact ((contDiff_flatDiffDiag D0 i).contDiffAt).sqrt (flatDiffDiag_pos hD0 hz i).ne'
  · simp only [flatSigma, Pi.single_apply, h, ite_false]
    exact contDiffAt_const

theorem flatSigma_cov {D0 : ℝ} (hD0 : 0 < D0) {z : Fin (q + q) → ℝ} (hz : z ∈ flatChamber q) :
    (Matrix.of fun i j => ∑ a, flatSigma D0 q a z i * flatSigma D0 q a z j) = flatDiff D0 q z := by
  ext i j
  simp only [Matrix.of_apply, flatSigma, Pi.single_apply, flatDiff, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp [Real.mul_self_sqrt (flatDiffDiag_pos hD0 hz i).le]
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases hi : i = a
    · subst hi; simp [Ne.symm h]
    · simp [hi]

/-- Every compact subset of the chamber lies in the image of some ball. -/
theorem exists_ball_superset {K : Set (Fin (q + q) → ℝ)} (hK : IsCompact K)
    (hKc : K ⊆ flatChamber q) : ∃ n : ℕ, K ⊆ chartQ q '' Metric.ball 0 n := by
  have hc : ContinuousOn (chartQInv q) K := fun z hz =>
    (differentiableAt_chartQInv (hKc hz)).continuousAt.continuousWithinAt
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine ⟨n, fun z hz => ⟨chartQInv q z, ?_, chartQ_chartQInv (hKc hz)⟩⟩
  rw [Metric.mem_ball, dist_zero_right]
  exact (hR _ ⟨z, hz, rfl⟩).trans_lt hn

end BlockBand.Transmission.Dual.G
