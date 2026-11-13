module

public import BlockBand.Endpoints.Clock.CommonPortRatiosFamily

/-!
# The common-port ratios theorem and the common-port part of the two-positive-clocks lemma

We prove:
* `twoPositiveClocksCommonPort_of_commonPortMean : CommonPortMeanContract →
  ClocksCommonPort.TwoPositiveClocksCommonPortContract` (both fields `joint` and `ratio`);
* `commonPortRatios_of_commonPortMean : CommonPortMeanContract →
  ClocksCommonPort.CommonPortRatiosContract`.

Proof. `joint` is `commonPort_clockFamily_comparison` for the two clocks `P = (D, C)` (traces
`≤ max(1,K) T`) with the clamped test `ψ ∘ clockPair`. `ratio` is
`commonPort_ratio_comparison` with denominator `D` and `ψ_u(x) = Φ(projIci(x₁ / max(x₀,u)))`.
The `k`-ratio theorem uses the positive clocks `P₀ = Y`, `P_{j+1} = Y + Y_j` (`⪰ 0` by the
sandwich, `Tr ≤ 2 Tr Y`) and `ψ_u(x) = Φ((projIcc(x_{j+1}/max(x₀,u) - 1))_j)`, since
`h*Y_jh/h*Yh = h*(Y+Y_j)h/h*Yh - 1`. The scale `γT` (resp. `T`) cancels from every ratio. In each
case `δ₀, W₀` depend only on `b, κ` and the fixed test data (`K, ψ, Φ, k, ε`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder Matrix BoundedContinuousFunction

/-- `(v ↦ Re v*Qv)` is measurable. -/
theorem CommonPortRatios.measurable_quadForm_left {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) :
    Measurable (fun v : ι → ℂ => quadForm Q v) :=
  (continuous_quadForm.comp (continuous_const.prodMk continuous_id)).measurable

/-- The clamp `x ↦ max(0,x) ∈ [0,∞)` is continuous. -/
theorem CommonPortRatios.continuous_projIci_zero : Continuous (Set.projIci (0 : ℝ)) :=
  (continuous_const.max continuous_id).subtype_mk _

/-- **Two-positive-clocks lemma, common-port part**, from `CommonPortMeanContract`. First
`b ∈ (0,1/2)`, `κ > 0`, `K`, the test (`ψ ∈ C_b([0,∞)²)` for `joint`, `Φ ∈ C_b([0,∞))` for
`ratio`) and `ε > 0`; then `δ₀ > 0`, `W₀`; uniformly in `W ≥ W₀`, Hermitian `X`,
`e ∈ bulkInterval κ` with `δ ≤ δ₀`, `D, C ⪰ 0` with `T = Re Tr D > 0`, `Re Tr C ≤ KT`, and
measurable defaults `d`.
-/
theorem twoPositiveClocksCommonPort_of_commonPortMean (h : CommonPortMeanContract) :
    TwoPositiveClocksCommonPortContract := by
  constructor
  · -- `joint`
    intro b hb hb' κ hκ K ψ ε hε
    set ψ' : (Fin 2 → ℝ) → ℝ := fun x => ψ (clockPair (x 0) (x 1))
    have hψ' : Continuous ψ' := ψ.continuous.comp
      ((CommonPortRatios.continuous_projIci_zero.comp (continuous_apply 0)).prodMk
        (CommonPortRatios.continuous_projIci_zero.comp (continuous_apply 1)))
    have hψM : ∀ x, |ψ' x| ≤ ‖ψ‖ := fun x => by
      rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm _
    obtain ⟨δ₀, hδ₀, W₀, hfam⟩ :=
      commonPort_clockFamily_comparison h hb hb' hκ 2 ψ' hψ' hψM (max 1 K) hε
    refine ⟨δ₀, W₀, hδ₀, ?_⟩
    intro W hW hWW X hX e he hδ D C hD hC hT hCK T γ
    have hP : ∀ i, (![D, C] i).PosSemidef := Fin.forall_fin_two.mpr ⟨hD, hC⟩
    have hPK : ∀ i, (![D, C] i).trace.re ≤ max 1 K * T := Fin.forall_fin_two.mpr
      ⟨by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 K) hT.le,
       by simpa using hCK.trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) hT.le)⟩
    exact hfam W hW hWW X hX e he hδ ![D, C] hP T hT hPK
  · -- `ratio`
    intro b hb hb' κ hκ K Φ ε hε
    set ψ : ℝ → (Fin 2 → ℝ) → ℝ := fun u x => Φ (Set.projIci 0 (x 1 / max (x 0) u))
    have hψc : ∀ u, 0 < u → Continuous (ψ u) := fun u hu => Φ.continuous.comp
      (CommonPortRatios.continuous_projIci_zero.comp ((continuous_apply 1).div
        ((continuous_apply 0).max continuous_const)
        fun x => (lt_of_lt_of_le hu (le_max_right _ _)).ne'))
    have hψM : ∀ u x, |ψ u x| ≤ ‖Φ‖ := fun u x => by
      rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
    obtain ⟨δ₀, hδ₀, W₀, hrat⟩ :=
      commonPort_ratio_comparison h hb hb' hκ 1 ψ hψc hψM (max 1 K) hε
    refine ⟨δ₀, W₀, hδ₀, ?_⟩
    intro W hW hWW X hX e he hδ D C hD hC hT hCK d hd
    have hP : ∀ i, (![D, C] i).PosSemidef := Fin.forall_fin_two.mpr ⟨hD, hC⟩
    have hPK : ∀ i, (![D, C] i).trace.re ≤ max 1 K * (![D, C] 0).trace.re :=
      Fin.forall_fin_two.mpr
        ⟨by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 K) hT.le,
         by simpa using hCK.trans (mul_le_mul_of_nonneg_right (le_max_right 1 K) hT.le)⟩
    have hGm : Measurable (fun v => Φ (ratioHalfLine C D d v)) := by
      refine Φ.continuous.measurable.comp (CommonPortRatios.continuous_projIci_zero.measurable.comp ?_)
      exact Measurable.ite (measurableSet_eq_fun (CommonPortRatios.measurable_quadForm_left D) measurable_const) hd
        ((CommonPortRatios.measurable_quadForm_left C).div (CommonPortRatios.measurable_quadForm_left D))
    have hGM : ∀ v, |Φ (ratioHalfLine C D d v)| ≤ ‖Φ‖ := fun v => by
      rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
    refine hrat W hW hWW X hX e he hδ ![D, C] hP hT hPK _ hGm hGM ?_
    intro u hu v s hs hus
    have hq0 : quadForm D v ≠ 0 := by
      intro h0
      simp only [Matrix.cons_val_zero] at hus
      rw [h0, zero_div] at hus
      linarith
    simp only [ψ, ratioHalfLine, hq0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [Matrix.cons_val_zero] at hus
    rw [max_eq_left hus]
    congr 2
    field_simp

/-- **Common-port ratios theorem**, from `CommonPortMeanContract`. First `b`, `κ`, `k`, a
continuous `Φ : [-1,1]^k → ℝ` and `ε > 0`; then `δ₀`, `W₀`; uniformly in `W ≥ W₀`, Hermitian `X`,
`e ∈ bulkInterval κ` with `δ ≤ δ₀`, `Y ⪰ 0` with `Re Tr Y > 0`, Hermitian `-Y ⪯ Y_j ⪯ Y` (no
condition-number, norm or rank assumption), and measurable defaults.
-/
theorem commonPortRatios_of_commonPortMean (h : CommonPortMeanContract) :
    CommonPortRatiosContract := by
  intro b hb hb' κ hκ k Φ ε hε
  set ψ : ℝ → (Fin (k + 1) → ℝ) → ℝ := fun u x =>
    Φ (fun j => Set.projIcc (-1 : ℝ) 1 (by norm_num) (x j.succ / max (x 0) u - 1))
  have hψc : ∀ u, 0 < u → Continuous (ψ u) := fun u hu => Φ.continuous.comp
    (continuous_pi fun j => continuous_projIcc.comp (((continuous_apply j.succ).div
      ((continuous_apply 0).max continuous_const)
      fun x => (lt_of_lt_of_le hu (le_max_right _ _)).ne').sub continuous_const))
  have hψM : ∀ u x, |ψ u x| ≤ ‖Φ‖ := fun u x => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  obtain ⟨δ₀, hδ₀, W₀, hrat⟩ := commonPort_ratio_comparison h hb hb' hκ k ψ hψc hψM 2 hε
  refine ⟨δ₀, W₀, hδ₀, ?_⟩
  intro W hW hWW X hX e he hδ Y Yt hY hT hYt d hd
  set P : Fin (k + 1) → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
    Fin.cons Y (fun j => Y + Yt j)
  have hP0 : P 0 = Y := rfl
  have hPs : ∀ j, P j.succ = Y + Yt j := fun j => rfl
  have hP : ∀ i, (P i).PosSemidef := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hP0]; exact hY
    · rw [hPs]; exact (hYt j).2.2
  have hPK : ∀ i, (P i).trace.re ≤ 2 * (P 0).trace.re := by
    intro i
    rw [hP0]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hP0]; linarith
    · rw [hPs, Matrix.trace_add, Complex.add_re]
      have h1 : 0 ≤ (Y - Yt j).trace.re := (Complex.nonneg_iff.mp (hYt j).2.1.trace_nonneg).1
      rw [Matrix.trace_sub, Complex.sub_re] at h1
      linarith
  have hGm : Measurable (fun v => Φ (ratioCube Yt Y d v)) := by
    refine Φ.continuous.measurable.comp (measurable_pi_iff.mpr fun j => ?_)
    refine continuous_projIcc.measurable.comp ?_
    exact Measurable.ite (measurableSet_eq_fun (CommonPortRatios.measurable_quadForm_left Y) measurable_const)
      ((measurable_pi_apply j).comp hd)
      ((CommonPortRatios.measurable_quadForm_left (Yt j)).div (CommonPortRatios.measurable_quadForm_left Y))
  have hGM : ∀ v, |Φ (ratioCube Yt Y d v)| ≤ ‖Φ‖ := fun v => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  refine hrat W hW hWW X hX e he hδ P hP (by rw [hP0]; exact hT) hPK _ hGm hGM ?_
  intro u hu v s hs hus
  rw [hP0] at hus
  have hq0 : quadForm Y v ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hus
    linarith
  simp only [ψ]
  congr 1
  funext j
  simp only [ratioCube, hq0, ↓reduceIte]
  rw [hPs, hP0, max_eq_left hus, CommonPortRatios.quadForm_add]
  congr 1
  field_simp
  ring

end BlockBand.Endpoints.Clock
