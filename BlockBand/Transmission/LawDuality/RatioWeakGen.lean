module

public import BlockBand.Transmission.LawDuality.RatioWeak

/-!
# `RatioDualityPrinciple`, step (c): `F` and `𝒟F` jointly continuous in `(z, ν)`

* **`continuousAt_ratioOn`**: `(z, ν) ↦ F_z(ν)` is continuous at `(z₀, ν₀)`;
* **`continuousAt_dualGenerator_ratioOn`**: `(z, ν) ↦ 𝒟_pF_·(ν)(z)` is continuous at `(z₀, ν₀)`;
* **`continuousAt_ratioDrift`**: `(u, z, ν) ↦ ratioDrift D₀ E κ u z ν` is continuous at
  `(u₀, z₀, ν₀)` for continuous `κ`.
Proof: `F_z(ν) = F_{z₀}(ν)·exp(Σ_i ΔA)` near `z₀`, with `|A_ν(x) − A_ν(x₀)| ≤ m/δ·|x − x₀|`;
then the closed form `dualGenerator_ratioOn` is a finite combination of jointly continuous
pieces (`RatioWeak`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- `A_ν` is Lipschitz on `[δ−1, ∞)` with constant `ν[0,1]/δ`. -/
theorem abs_lkerInt_sub_le (ν : FiniteMeasure unitInterval) {δ x x₀ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) (hx₀ : δ - 1 ≤ x₀) :
    |lkerInt ν x - lkerInt ν x₀| ≤ 1 / δ * (ν : Measure unitInterval).real univ * |x - x₀| := by
  have hder : ∀ w ∈ Ici (δ - 1), HasDerivWithinAt (lkerInt ν) (lkerInt1 ν w) (Ici (δ - 1)) w :=
    fun w hw => (hasDerivAt_lkerInt ν (by linarith [mem_Ici.1 hw])).hasDerivWithinAt
  have hbd : ∀ w ∈ Ici (δ - 1), ‖lkerInt1 ν w‖ ≤ 1 / δ * (ν : Measure unitInterval).real univ :=
    fun w hw => by
      rw [Real.norm_eq_abs]
      exact abs_lkerInt1_le ν hδ fun t ht0 ht1 => one_add_mul_ge hδ1 (mem_Ici.1 hw) ht0 ht1
  have := (convex_Ici (δ - 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (mem_Ici.2 hx₀) (mem_Ici.2 hx)
  simpa only [Real.norm_eq_abs] using this

theorem dom_sub_one_lt {x₀ : ℝ} (hx₀ : -1 < x₀) : dom x₀ - 1 < x₀ := by
  have := min_le_right 1 ((1 + x₀) / 2); unfold dom; linarith

theorem tendsto_lkerInt_sub {x₀ : ℝ} (hx₀ : -1 < x₀) (ν₀ : FiniteMeasure unitInterval) :
    Tendsto (fun q : ℝ × FiniteMeasure unitInterval => lkerInt q.2 q.1 - lkerInt q.2 x₀)
      (𝓝 (x₀, ν₀)) (𝓝 0) := by
  have hb : Tendsto (fun q : ℝ × FiniteMeasure unitInterval =>
      1 / dom x₀ * (q.2 : Measure unitInterval).real univ * |q.1 - x₀|) (𝓝 (x₀, ν₀)) (𝓝 0) := by
    have : Continuous fun q : ℝ × FiniteMeasure unitInterval =>
        1 / dom x₀ * (q.2 : Measure unitInterval).real univ * |q.1 - x₀| :=
      (continuous_const.mul (continuous_measureReal_univ.comp continuous_snd)).mul
        ((continuous_fst.sub continuous_const).abs)
    simpa using this.tendsto (x₀, ν₀)
  refine squeeze_zero_norm' ?_ hb
  have : ∀ᶠ q : ℝ × FiniteMeasure unitInterval in 𝓝 (x₀, ν₀), dom x₀ - 1 < q.1 :=
    (continuous_fst.tendsto (x₀, ν₀)).eventually (Ioi_mem_nhds (dom_sub_one_lt hx₀))
  filter_upwards [this] with q hq
  rw [Real.norm_eq_abs]
  exact abs_lkerInt_sub_le q.2 (dom_pos hx₀) (dom_le_one x₀) hq.le (dom_sub_one_le hx₀)

variable {p : ℕ}

/-- The coordinate maps `(z, ν) ↦ (±z_i, ν)`. -/
theorem continuous_coordX_nu (i : Fin p) :
    Continuous fun q : DualCoord p × FiniteMeasure unitInterval => (q.1.1 i, q.2) :=
  ((continuous_apply i).comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd

theorem continuous_coordY_nu (i : Fin p) :
    Continuous fun q : DualCoord p × FiniteMeasure unitInterval => (-q.1.2 i, q.2) :=
  ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).neg.prodMk continuous_snd

/-- **`(z, ν) ↦ F_z(ν)` is continuous at `(z₀, ν₀)`, `z₀ ∈ 𝒞_p`.** -/
theorem continuousAt_ratioOn {z₀ : DualCoord p} (hz₀ : z₀ ∈ dualChamber p)
    (ν₀ : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval => ratioOn q.2 q.1)
      (z₀, ν₀) := by
  have hO := dualChamber_subset_ratioOpen hz₀
  have hr := IsRatioParameter.isRatioRange (show IsRatioParameter z₀.1 z₀.2 from hz₀)
  -- the exponent difference tends to `0`
  have hΔ : Tendsto (fun q : DualCoord p × FiniteMeasure unitInterval =>
      ratioExp q.2 q.1 - ratioExp q.2 z₀) (𝓝 (z₀, ν₀)) (𝓝 0) := by
    have e : (fun q : DualCoord p × FiniteMeasure unitInterval =>
        ratioExp q.2 q.1 - ratioExp q.2 z₀) = fun q => ∑ i,
          ((lkerInt q.2 (q.1.1 i) - lkerInt q.2 (z₀.1 i)) -
            (lkerInt q.2 (-q.1.2 i) - lkerInt q.2 (-z₀.2 i))) := by
      funext q; unfold ratioExp; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    have := tendsto_finsetSum (Finset.univ : Finset (Fin p)) fun i _ =>
      ((tendsto_lkerInt_sub (hO i).1 ν₀).comp ((continuous_coordX_nu i).tendsto (z₀, ν₀))).sub
        ((tendsto_lkerInt_sub (by linarith [(hO i).2]) ν₀).comp
          ((continuous_coordY_nu i).tendsto (z₀, ν₀)))
    simpa using this
  have hF0 : Tendsto (fun q : DualCoord p × FiniteMeasure unitInterval => ratioOn q.2 z₀)
      (𝓝 (z₀, ν₀)) (𝓝 (ratioOn ν₀ z₀)) :=
    ((continuous_transmissionRatio_vec hr).tendsto ν₀).comp (continuous_snd.tendsto (z₀, ν₀))
  have hlim := hF0.mul ((Real.continuous_exp.tendsto 0).comp hΔ)
  rw [Real.exp_zero, mul_one] at hlim
  refine hlim.congr' ?_
  have hev : ∀ᶠ q : DualCoord p × FiniteMeasure unitInterval in 𝓝 (z₀, ν₀),
      q.1 ∈ ratioOpen p :=
    (continuous_fst.tendsto (z₀, ν₀)).eventually (isOpen_ratioOpen.mem_nhds hO)
  filter_upwards [hev] with q hq
  simp only [Function.comp_apply]
  rw [ratioOn_eq_exp q.2 hq, ratioOn_eq_exp q.2 hO, ← Real.exp_add]
  ring_nf

/-- **`(z, ν) ↦ 𝒟_pF_·(ν)(z)` is continuous at `(z₀, ν₀)`, `z₀ ∈ 𝒞_p`.** -/
theorem continuousAt_dualGenerator_ratioOn (D0 : ℝ) {z₀ : DualCoord p}
    (hz₀ : z₀ ∈ dualChamber p) (ν₀ : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      dualGenerator D0 (ratioOn q.2) q.1) (z₀, ν₀) := by
  have hO := dualChamber_subset_ratioOpen hz₀
  have hN : dualChamber p ∈ 𝓝 z₀ := (isOpen_dualChamber p).mem_nhds hz₀
  have hev : ∀ᶠ q : DualCoord p × FiniteMeasure unitInterval in 𝓝 (z₀, ν₀),
      q.1 ∈ dualChamber p := (continuous_fst.tendsto (z₀, ν₀)).eventually hN
  have hX : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval => q.1.1 i)
      (z₀, ν₀) := fun i =>
    ((continuous_apply i).comp (continuous_fst.comp continuous_fst)).continuousAt
  have hY : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval => q.1.2 i)
      (z₀, ν₀) := fun i =>
    ((continuous_apply i).comp (continuous_snd.comp continuous_fst)).continuousAt
  have hA1x : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      lkerInt1 q.2 (q.1.1 i)) (z₀, ν₀) := fun i =>
    (continuousAt_lkerInt1 (hO i).1 ν₀).comp_of_eq (continuous_coordX_nu i).continuousAt rfl
  have hA2x : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      lkerInt2 q.2 (q.1.1 i)) (z₀, ν₀) := fun i =>
    (continuousAt_lkerInt2 (hO i).1 ν₀).comp_of_eq (continuous_coordX_nu i).continuousAt rfl
  have hA1y : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      lkerInt1 q.2 (-q.1.2 i)) (z₀, ν₀) := fun i =>
    (continuousAt_lkerInt1 (by linarith [(hO i).2]) ν₀).comp_of_eq
      (continuous_coordY_nu i).continuousAt rfl
  have hA2y : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      lkerInt2 q.2 (-q.1.2 i)) (z₀, ν₀) := fun i =>
    (continuousAt_lkerInt2 (by linarith [(hO i).2]) ν₀).comp_of_eq
      (continuous_coordY_nu i).continuousAt rfl
  have hdx : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      dualDriftX q.1 i) (z₀, ν₀) := fun i =>
    ((continuousOn_dualDriftX i).continuousAt hN).comp_of_eq continuous_fst.continuousAt rfl
  have hdy : ∀ i, ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      dualDriftY q.1 i) (z₀, ν₀) := fun i =>
    ((continuousOn_dualDriftY i).continuousAt hN).comp_of_eq continuous_fst.continuousAt rfl
  have hF := continuousAt_ratioOn hz₀ ν₀
  have hcl : ContinuousAt (fun q : DualCoord p × FiniteMeasure unitInterval =>
      D0 / 2 * ratioOn q.2 q.1 *
        ((∑ i, (q.1.1 i * (1 + q.1.1 i) * (lkerInt1 q.2 (q.1.1 i) ^ 2 + lkerInt2 q.2 (q.1.1 i)) +
            dualDriftX q.1 i * lkerInt1 q.2 (q.1.1 i))) +
          ∑ j, (q.1.2 j * (1 - q.1.2 j) * (lkerInt1 q.2 (-q.1.2 j) ^ 2 - lkerInt2 q.2 (-q.1.2 j)) +
            dualDriftY q.1 j * lkerInt1 q.2 (-q.1.2 j)))) (z₀, ν₀) := by
    refine (continuousAt_const.mul hF).mul (ContinuousAt.add ?_ ?_)
    · exact tendsto_finsetSum _ fun i _ =>
        (((hX i).mul (continuousAt_const.add (hX i))).mul (((hA1x i).pow 2).add (hA2x i))).add
          ((hdx i).mul (hA1x i))
    · exact tendsto_finsetSum _ fun j _ =>
        (((hY j).mul (continuousAt_const.sub (hY j))).mul (((hA1y j).pow 2).sub (hA2y j))).add
          ((hdy j).mul (hA1y j))
  refine hcl.congr ?_
  filter_upwards [hev] with q hq
  exact (dualGenerator_ratioOn q.2 D0 (dualChamber_subset_ratioOpen hq)).symm

/-- **`(u, z, ν) ↦ ratioDrift D₀ E κ u z ν` is continuous at `(u₀, z₀, ν₀)`**, `z₀ ∈ 𝒞_p`,
`κ` continuous. -/
theorem continuousAt_ratioDrift (D0 E : ℝ) {κ : ℝ → ℝ} (hκ : Continuous κ) (u₀ : ℝ)
    {z₀ : DualCoord p} (hz₀ : z₀ ∈ dualChamber p) (ν₀ : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : ℝ × (DualCoord p × FiniteMeasure unitInterval) =>
      ratioDrift D0 E κ q.1 q.2.1 q.2.2) (u₀, (z₀, ν₀)) := by
  unfold ratioDrift
  have hG := (continuousAt_dualGenerator_ratioOn D0 hz₀ ν₀).comp_of_eq
    (continuous_snd.continuousAt (x := (u₀, (z₀, ν₀)))) rfl
  have hF := (continuousAt_ratioOn hz₀ ν₀).comp_of_eq
    (continuous_snd.continuousAt (x := (u₀, (z₀, ν₀)))) rfl
  have hh : Continuous fun q : ℝ × (DualCoord p × FiniteMeasure unitInterval) =>
      absorptionRate E κ q.1 := by
    unfold absorptionRate; exact continuous_const.mul (hκ.comp continuous_fst)
  have hR : Continuous fun q : ℝ × (DualCoord p × FiniteMeasure unitInterval) =>
      ∑ i, (q.2.1.1 i + q.2.1.2 i) :=
    continuous_finsetSum _ fun i _ => by fun_prop
  exact hG.sub ((hh.continuousAt.mul hR.continuousAt).mul hF)

end BlockBand.Transmission.LawDuality
