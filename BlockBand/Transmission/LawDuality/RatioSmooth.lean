module

public import BlockBand.Transmission.LawDuality.RatioGen

/-!
# `RatioDualityPrinciple`: `z ↦ F_z(ν)` is `C^∞`

All derivatives of `A_ν(x) = ∫ ℓ(x, t) dν(t)` (the first two are in `RatioKernel`). With the
kernels `m_k(x, t) = t^k (1+xt)^{-(k+1)}` (`lkerK`) one has `∂_x m_k = −(k+1) m_{k+1}`
(`hasDerivAt_lkerK`), `|m_k| ≤ δ^{-(k+1)}` when `1 + xt ≥ δ` on `t ∈ [0,1]`, so by
differentiation under `∫ dν` the integrals `G_k(x) = ∫ m_k(x, t) dν(t)` satisfy
`G_k' = −(k+1) G_{k+1}` on `x > −1` (`hasDerivAt_lkerKInt`), and `A_ν' = −G_0`. Induction on the
order gives
* `contDiffOn_lkerInt`: `A_ν` is `C^∞` on `(−1, ∞)`;
* **`contDiffOn_ratioOn`**: `z ↦ F_z(ν)` is `C^∞` on `ratioOpen p = {x_i > −1, y_i < 1}`, an open
  set containing the chamber `𝒞_p`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal ContDiff

/-- `m_k(x, t) = t^k (1+xt)^{-(k+1)}`. -/
def lkerK (k : ℕ) (x t : ℝ) : ℝ := t ^ k * ((1 + x * t)⁻¹) ^ (k + 1)

theorem lker1_eq_neg_lkerK (x t : ℝ) : lker1 x t = -lkerK 0 x t := by
  simp [lker1, lkerK]

theorem hasDerivAt_lkerK (k : ℕ) {x t : ℝ} (h : 0 < 1 + x * t) :
    HasDerivAt (fun x => lkerK k x t) (-((k : ℝ) + 1) * lkerK (k + 1) x t) x := by
  have h1 : HasDerivAt (fun x => 1 + x * t) t x := by
    simpa using ((hasDerivAt_id x).mul_const t).const_add 1
  have h2 := ((h1.inv h.ne').pow (k + 1)).const_mul (t ^ k)
  simp only [Pi.inv_apply, Nat.add_sub_cancel] at h2
  unfold lkerK
  convert h2 using 1
  rw [div_eq_mul_inv, ← inv_pow]
  push_cast
  ring

theorem measurable_lkerK (k : ℕ) (x : ℝ) : Measurable fun t => lkerK k x t :=
  (measurable_id.pow_const k).mul
    ((measurable_const.add (measurable_const.mul measurable_id)).inv.pow_const (k + 1))

theorem abs_lkerK_le (k : ℕ) {δ x t : ℝ} (hδ : 0 < δ) (h : δ ≤ 1 + x * t) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |lkerK k x t| ≤ 1 / δ ^ (k + 1) := by
  unfold lkerK
  have hp : 0 < 1 + x * t := hδ.trans_le h
  rw [abs_mul, abs_pow, abs_of_nonneg ht0, abs_pow, abs_inv, abs_of_pos hp, one_div, ← inv_pow]
  calc t ^ k * (1 + x * t)⁻¹ ^ (k + 1) ≤ 1 * δ⁻¹ ^ (k + 1) := by
        refine mul_le_mul (pow_le_one₀ ht0 ht1)
          (pow_le_pow_left₀ (inv_nonneg.2 hp.le) (inv_anti₀ hδ h) _) (by positivity) zero_le_one
    _ = δ⁻¹ ^ (k + 1) := one_mul _

variable (ν : FiniteMeasure unitInterval)

/-- `G_k(x) = ∫ m_k(x, t) dν(t)`. -/
def lkerKInt (k : ℕ) (x : ℝ) : ℝ := ∫ t, lkerK k x (t : ℝ) ∂(ν : Measure unitInterval)

theorem integrable_lkerK (k : ℕ) {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) :
    Integrable (fun t : unitInterval => lkerK k x (t : ℝ)) (ν : Measure unitInterval) :=
  Integrable.of_bound ((measurable_lkerK k x).comp measurable_subtype_coe).aestronglyMeasurable
    (1 / δ ^ (k + 1)) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact abs_lkerK_le k hδ (one_add_mul_ge hδ1 hx t.2.1 t.2.2) t.2.1 t.2.2)

theorem hasDerivAt_lkerKInt (k : ℕ) {x : ℝ} (hx : -1 < x) :
    HasDerivAt (lkerKInt ν k) (-((k : ℝ) + 1) * lkerKInt ν (k + 1) x) x := by
  have hs : Ioi ((x - 1) / 2) ∈ 𝓝 x := Ioi_mem_nhds (by linarith)
  have hδ := dom_pos hx
  have hx0 : dom x - 1 ≤ x := dom_sub_one_le hx
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x (t : unitInterval) => lkerK k x (t : ℝ))
    (F' := fun x (t : unitInterval) => -((k : ℝ) + 1) * lkerK (k + 1) x (t : ℝ))
    (bound := fun _ => ((k : ℝ) + 1) * (1 / dom x ^ (k + 2))) hs
    (Eventually.of_forall fun x' => ((measurable_lkerK k x').comp
      measurable_subtype_coe).aestronglyMeasurable)
    (integrable_lkerK ν k hδ (dom_le_one x) hx0)
    ((((measurable_lkerK (k + 1) x).comp measurable_subtype_coe).const_mul
      _).aestronglyMeasurable)
    (Eventually.of_forall fun t x' hx' => ?_) (integrable_const _)
    (Eventually.of_forall fun t x' hx' => ?_)).2
  · unfold lkerKInt
    rwa [integral_const_mul] at key
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < k + 1)]
    exact mul_le_mul_of_nonneg_left (abs_lkerK_le (k + 1) hδ (dom_le hx' t.2.1 t.2.2) t.2.1 t.2.2)
      (by positivity)
  · exact hasDerivAt_lkerK k (hδ.trans_le (dom_le hx' t.2.1 t.2.2))

theorem lkerInt1_eq_neg (x : ℝ) : lkerInt1 ν x = -lkerKInt ν 0 x := by
  unfold lkerInt1 lkerKInt
  simp_rw [lker1_eq_neg_lkerK]
  exact integral_neg _

theorem differentiableOn_lkerKInt (k : ℕ) : DifferentiableOn ℝ (lkerKInt ν k) (Ioi (-1)) :=
  fun _ hx => (hasDerivAt_lkerKInt ν k hx).differentiableAt.differentiableWithinAt

theorem contDiffOn_lkerKInt (n : ℕ) : ∀ k : ℕ, ContDiffOn ℝ n (lkerKInt ν k) (Ioi (-1)) := by
  induction n with
  | zero => exact fun k => contDiffOn_zero.2 (differentiableOn_lkerKInt ν k).continuousOn
  | succ n ih =>
    intro k
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨differentiableOn_lkerKInt ν k, by simp, ?_⟩
    refine ((ih (k + 1)).const_smul (-((k : ℝ) + 1))).congr fun x hx => ?_
    rw [(hasDerivAt_lkerKInt ν k hx).deriv]
    rfl

/-- **`A_ν` is `C^∞` on `(−1, ∞)`.** -/
theorem contDiffOn_lkerInt : ContDiffOn ℝ ∞ (lkerInt ν) (Ioi (-1)) := by
  refine contDiffOn_infty.2 fun n => ?_
  cases n with
  | zero => exact contDiffOn_zero.2 fun x hx =>
      (hasDerivAt_lkerInt ν hx).continuousAt.continuousWithinAt
  | succ n =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun x hx => (hasDerivAt_lkerInt ν hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine (contDiffOn_lkerKInt ν n 0).neg.congr fun x hx => ?_
    rw [(hasDerivAt_lkerInt ν hx).deriv, lkerInt1_eq_neg]

variable {p : ℕ}

theorem contDiffOn_ratioExp : ContDiffOn ℝ ∞ (ratioExp ν (p := p)) (ratioOpen p) := by
  unfold ratioExp
  refine ContDiffOn.sum fun i _ => ContDiffOn.sub ?_ ?_
  · exact (contDiffOn_lkerInt ν).comp (prX i).contDiff.contDiffOn fun z hz => (hz i).1
  · exact (contDiffOn_lkerInt ν).comp (prY i).contDiff.neg.contDiffOn fun z hz =>
      hasDerivAt_lkerInt_negY hz i

/-- **`z ↦ F_z(ν)` is `C^∞` on `ratioOpen p`** (an open set containing `𝒞_p`). -/
theorem contDiffOn_ratioOn : ContDiffOn ℝ ∞ (ratioOn ν (p := p)) (ratioOpen p) :=
  (Real.contDiff_exp.comp_contDiffOn (contDiffOn_ratioExp ν)).congr fun _ hz =>
    ratioOn_eq_exp ν hz

end BlockBand.Transmission.LawDuality
