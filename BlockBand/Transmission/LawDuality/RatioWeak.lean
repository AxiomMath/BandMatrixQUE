module

public import BlockBand.Transmission.LawDuality.RatioMass
public import BlockBand.Transmission.LawDuality.RatioSmooth

/-!
# Duality principle: joint continuity in `(z, ν)`

* `continuousAt_kernel_of_lip`: a family `G ν x` that is continuous in `ν` at `x₀` and
  Lipschitz in `x` with constant `C · ν[0,1]` is jointly continuous at `(x₀, ν₀)`;
* `continuousAt_lkerKInt`, `continuousAt_lkerInt1`, `continuousAt_lkerInt2`: the kernels
  `A₁, A₂` of the closed form, jointly in `(x, ν)`, `x > −1`.

From these the sibling module proves the joint continuity of `(z, ν) ↦ F_z(ν)`
(`continuousAt_ratioOn`) and of `(z, ν) ↦ 𝒟_pF_·(ν)(z)` (`continuousAt_dualGenerator_ratioOn`) at
every `(z₀, ν₀)`, `z₀ ∈ 𝒞_p`, and of `(u, z, ν) ↦ ratioDrift D₀ E κ u z ν` for continuous `κ`
(`continuousAt_ratioDrift`). Consequently, along a path `u ↦ μ_u` continuous on `(0, ∞)`, the
forward drift `u ↦ ratioDrift u z μ_u` is continuous, hence (with `exists_bound_ratioDrift`) a
bounded measurable integrand.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- The total mass as a real number. -/
theorem measureReal_univ_eq_mass (ν : FiniteMeasure unitInterval) :
    (ν : Measure unitInterval).real univ = (ν.mass : ℝ) := rfl

theorem continuous_measureReal_univ :
    Continuous fun ν : FiniteMeasure unitInterval => (ν : Measure unitInterval).real univ := by
  simp_rw [measureReal_univ_eq_mass]
  exact NNReal.continuous_coe.comp FiniteMeasure.continuous_mass

/-- **Joint continuity from continuity in `ν` and a mass-Lipschitz bound in `x`.** -/
theorem continuousAt_kernel_of_lip {G : FiniteMeasure unitInterval → ℝ → ℝ} {x₀ a C : ℝ}
    {ν₀ : FiniteMeasure unitInterval} (ha : a < x₀) (hc : ContinuousAt (fun ν => G ν x₀) ν₀)
    (hL : ∀ ν x, a ≤ x → |G ν x - G ν x₀| ≤ C * (ν : Measure unitInterval).real univ * |x - x₀|) :
    ContinuousAt (fun q : ℝ × FiniteMeasure unitInterval => G q.2 q.1) (x₀, ν₀) := by
  have h1 : Tendsto (fun q : ℝ × FiniteMeasure unitInterval => G q.2 q.1 - G q.2 x₀)
      (𝓝 (x₀, ν₀)) (𝓝 0) := by
    have hb : Tendsto (fun q : ℝ × FiniteMeasure unitInterval =>
        C * (q.2 : Measure unitInterval).real univ * |q.1 - x₀|) (𝓝 (x₀, ν₀)) (𝓝 0) := by
      have : Continuous fun q : ℝ × FiniteMeasure unitInterval =>
          C * (q.2 : Measure unitInterval).real univ * |q.1 - x₀| :=
        (continuous_const.mul (continuous_measureReal_univ.comp continuous_snd)).mul
          ((continuous_fst.sub continuous_const).abs)
      simpa using this.tendsto (x₀, ν₀)
    refine squeeze_zero_norm' ?_ hb
    have : ∀ᶠ q : ℝ × FiniteMeasure unitInterval in 𝓝 (x₀, ν₀), a < q.1 :=
      (continuous_fst.tendsto (x₀, ν₀)).eventually (Ioi_mem_nhds ha)
    filter_upwards [this] with q hq
    rw [Real.norm_eq_abs]; exact hL q.2 q.1 hq.le
  have h2 : Tendsto (fun q : ℝ × FiniteMeasure unitInterval => G q.2 x₀) (𝓝 (x₀, ν₀))
      (𝓝 (G ν₀ x₀)) := hc.tendsto.comp (continuous_snd.tendsto (x₀, ν₀))
  have := h1.add h2
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-!
## The kernels `G_k`, `A₁`, `A₂`
-/

theorem continuous_lkerK_coe (k : ℕ) {x : ℝ} (hx : -1 < x) :
    Continuous fun t : unitInterval => lkerK k x (t : ℝ) := by
  unfold lkerK
  refine (continuous_subtype_val.pow k).mul ((Continuous.inv₀ (continuous_const.add
    (continuous_const.mul continuous_subtype_val)) fun t => ?_).pow (k + 1))
  have := one_add_mul_ge (dom_le_one x) (dom_sub_one_le hx) t.2.1 t.2.2
  exact ((dom_pos hx).trans_le this).ne'

theorem continuous_lkerKInt_nu (k : ℕ) {x : ℝ} (hx : -1 < x) :
    Continuous fun ν : FiniteMeasure unitInterval => lkerKInt ν k x := by
  unfold lkerKInt
  exact FiniteMeasure.continuous_integral_continuousMap
    (⟨fun t : unitInterval => lkerK k x (t : ℝ), continuous_lkerK_coe k hx⟩ : C(unitInterval, ℝ))

theorem abs_lkerKInt_le (ν : FiniteMeasure unitInterval) (k : ℕ) {δ x : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) :
    |lkerKInt ν k x| ≤ 1 / δ ^ (k + 1) * (ν : Measure unitInterval).real univ := by
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure unitInterval))
    (f := fun t : unitInterval => lkerK k x (t : ℝ)) (C := 1 / δ ^ (k + 1))
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact abs_lkerK_le k hδ (one_add_mul_ge hδ1 hx t.2.1 t.2.2) t.2.1 t.2.2)
  rwa [Real.norm_eq_abs] at this

/-- `G_k` is Lipschitz on `[δ−1, ∞)` with constant `(k+1)/δ^{k+2} · ν[0,1]`. -/
theorem abs_lkerKInt_sub_le (ν : FiniteMeasure unitInterval) (k : ℕ) {δ x x₀ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hx : δ - 1 ≤ x) (hx₀ : δ - 1 ≤ x₀) :
    |lkerKInt ν k x - lkerKInt ν k x₀| ≤
      ((k : ℝ) + 1) / δ ^ (k + 2) * (ν : Measure unitInterval).real univ * |x - x₀| := by
  have hder : ∀ w ∈ Ici (δ - 1), HasDerivWithinAt (lkerKInt ν k)
      (-((k : ℝ) + 1) * lkerKInt ν (k + 1) w) (Ici (δ - 1)) w := fun w hw =>
    (hasDerivAt_lkerKInt ν k (by linarith [mem_Ici.1 hw])).hasDerivWithinAt
  have hbd : ∀ w ∈ Ici (δ - 1), ‖-((k : ℝ) + 1) * lkerKInt ν (k + 1) w‖ ≤
      ((k : ℝ) + 1) / δ ^ (k + 2) * (ν : Measure unitInterval).real univ := fun w hw => by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < k + 1)]
    have := abs_lkerKInt_le ν (k + 1) hδ hδ1 (mem_Ici.1 hw)
    calc ((k : ℝ) + 1) * |lkerKInt ν (k + 1) w|
        ≤ ((k : ℝ) + 1) * (1 / δ ^ (k + 1 + 1) * (ν : Measure unitInterval).real univ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have := (convex_Ici (δ - 1)).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (mem_Ici.2 hx₀) (mem_Ici.2 hx)
  simpa only [Real.norm_eq_abs] using this

theorem continuousAt_lkerKInt (k : ℕ) {x₀ : ℝ} (hx₀ : -1 < x₀) (ν₀ : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : ℝ × FiniteMeasure unitInterval => lkerKInt q.2 k q.1) (x₀, ν₀) :=
  continuousAt_kernel_of_lip (a := dom x₀ - 1)
    (by have := dom_le_one x₀; unfold dom at *; have := min_le_right 1 ((1 + x₀) / 2); linarith)
    (continuous_lkerKInt_nu k hx₀).continuousAt
    fun ν x hx => abs_lkerKInt_sub_le ν k (dom_pos hx₀) (dom_le_one x₀) hx (dom_sub_one_le hx₀)

theorem lkerInt2_eq (ν : FiniteMeasure unitInterval) (x : ℝ) : lkerInt2 ν x = lkerKInt ν 1 x := by
  unfold lkerInt2 lkerKInt lker2 lkerK
  simp

theorem continuousAt_lkerInt1 {x₀ : ℝ} (hx₀ : -1 < x₀) (ν₀ : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : ℝ × FiniteMeasure unitInterval => lkerInt1 q.2 q.1) (x₀, ν₀) := by
  simp_rw [lkerInt1_eq_neg]
  exact (continuousAt_lkerKInt 0 hx₀ ν₀).neg

theorem continuousAt_lkerInt2 {x₀ : ℝ} (hx₀ : -1 < x₀) (ν₀ : FiniteMeasure unitInterval) :
    ContinuousAt (fun q : ℝ × FiniteMeasure unitInterval => lkerInt2 q.2 q.1) (x₀, ν₀) := by
  simp_rw [lkerInt2_eq]
  exact continuousAt_lkerKInt 1 hx₀ ν₀

end BlockBand.Transmission.LawDuality
