module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKHyp

/-!
# Conditioning a product of two fresh `u*Δv` steps on `b3Sigma`

For `b3Ext W j`-invariant Borel frames bounded by `C_f` and an invariant Borel input `X` that is
passive a.e., with `a = u₁*Δ(X, F_j)v₁`, `b = u₂*Δ(X, F_j)v₂` and `op ∈ {id, conj}`:

* **`condExp_bilinear_pair`**: `a·op b` is integrable and `E_j[a·op b] = ∫ a·op b dF_j` a.e.
  (by `condExp_closed_fresh`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PathScalar
open BlockBand.Transmission.Bridge
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

/-- `∫ f² ≤ a²` from `‖f‖₂ ≤ a`, `f ≥ 0`. -/
theorem lintegral_sq_le_of_eLpNorm {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a)
    (h : eLpNorm f (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal a) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal (a ^ 2) := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (h.trans_lt ENNReal.ofReal_lt_top).ne
  have h2 : ENNReal.ofReal 2 ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2 ENNReal.ofReal_ne_top hfm,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at h
  have e : ∀ x, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f x ^ 2) := fun x => by
    rw [Real.enorm_eq_ofReal (hf0 x), ENNReal.rpow_ofNat, ENNReal.ofReal_pow (hf0 x)]
  simp_rw [e] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num), ENNReal.rpow_one,
    ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow ha] at h'

/-- **`E‖Δ(X, F_j)‖² ≤ C₂²`** under the closed law, for an invariant input passive a.e. -/
theorem lintegral_freshDelta_sq_le (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (C₂ : ℝ) (W₀ : ℕ), 0 ≤ C₂ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ (np j : ℕ)
      {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ}, Measurable X →
      (∀ y, X (b3Ext W j y) = X y) → (∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef) →
      ∫⁻ y, ENNReal.ofReal (‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2)
        ∂closedLaw b W np ≤ ENNReal.ofReal (C₂ ^ 2) := by
  obtain ⟨C₂, W₀, hC₂, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  refine ⟨C₂, W₀, hC₂, fun W hW E hE np j X hX hX' hXp => ?_⟩
  set Fi : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort := fun y => freshSample W j y.1.1
  have hFi : Measurable Fi :=
    (measurable_freshSample W j).comp (measurable_fst.comp measurable_fst)
  set g : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
      ℝ≥0∞ := fun z => ENNReal.ofReal (‖freshDelta b E (X (b3Rebuild W j z.1)) z.2‖ ^ 2)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E
      (hX.comp ((measurable_b3Rebuild W j).comp measurable_fst)) measurable_snd).norm.pow_const 2)
  have hT : Measurable fun y => (b3Past W j y, Fi y) := (measurable_b3Past W j).prodMk hFi
  have hgT : (fun y => g (b3Past W j y, Fi y)) =
      fun y => ENNReal.ofReal (‖freshDelta b E (X y) (Fi y)‖ ^ 2) := by
    funext y; simp only [g, b3Rebuild_b3Past, hX']
  rw [← hgT, ← lintegral_map hg hT, closedLaw_map_past_fresh,
    lintegral_prod _ hg.aemeasurable, ← closedLaw_map_b3Past b W np j,
    lintegral_map hg.lintegral_prod_right' (measurable_b3Past W j)]
  calc ∫⁻ y, ∫⁻ F, g (b3Past W j y, F) ∂freshLaw W b ∂closedLaw b W np ≤
        ∫⁻ _y, ENNReal.ofReal (C₂ ^ 2) ∂closedLaw b W np := by
        refine lintegral_mono_ae ?_
        filter_upwards [hXp] with y hy
        have h2 := (hM W hW E hE (X y) hy).2.1
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp] at h2
        simp only [g, b3Rebuild_b3Past, hX']
        exact lintegral_sq_le_of_eLpNorm _ (fun _ => norm_nonneg _) hC₂ h2
    _ = ENNReal.ofReal (C₂ ^ 2) := by rw [lintegral_const, measure_univ, mul_one]

/-- The square of the fresh `Δ` is integrable under the closed law. -/
theorem integrable_freshDelta_sq {b E : ℝ} {W np j : ℕ}
    {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ} (hX : Measurable X) {B : ℝ}
    (hL : ∫⁻ y, ENNReal.ofReal (‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2)
        ∂closedLaw b W np ≤ ENNReal.ofReal B) :
    Integrable (fun y => ‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2)
      (closedLaw b W np) := by
  have hm : Measurable fun y => ‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2 :=
    (BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E hX
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))).norm.pow_const 2
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  show ∫⁻ y, ‖‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2‖ₑ ∂closedLaw b W np < ⊤
  have e : ∀ y, ‖‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2‖ₑ =
      ENNReal.ofReal (‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2) := fun y =>
    Real.enorm_of_nonneg (by positivity)
  simp_rw [e]
  exact hL.trans_lt ENNReal.ofReal_lt_top

/-- **Conditioning a product of two fresh steps.** -/
theorem condExp_bilinear_pair (b E : ℝ) {W np : ℕ} (j : ℕ) (op : ℂ → ℂ) (hop : Continuous op)
    (hopn : ∀ z, ‖op z‖ = ‖z‖) {u₁ v₁ u₂ v₂ : ProbedPath W np × ℝ → Fin W → ℂ}
    {X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ} {Cf : ℝ}
    (hu₁ : Measurable u₁) (hv₁ : Measurable v₁) (hu₂ : Measurable u₂) (hv₂ : Measurable v₂)
    (hX : Measurable X) (hu₁' : ∀ y, u₁ (b3Ext W j y) = u₁ y)
    (hv₁' : ∀ y, v₁ (b3Ext W j y) = v₁ y) (hu₂' : ∀ y, u₂ (b3Ext W j y) = u₂ y)
    (hv₂' : ∀ y, v₂ (b3Ext W j y) = v₂ y) (hX' : ∀ y, X (b3Ext W j y) = X y)
    (hb₁ : ∀ y, vecNorm (u₁ y) ≤ Cf) (hb₂ : ∀ y, vecNorm (v₁ y) ≤ Cf)
    (hb₃ : ∀ y, vecNorm (u₂ y) ≤ Cf) (hb₄ : ∀ y, vecNorm (v₂ y) ≤ Cf)
    (hint : Integrable (fun y => ‖freshDelta b E (X y) (freshSample W j y.1.1)‖ ^ 2)
      (closedLaw b W np)) :
    Integrable (fun y => bilinear (u₁ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₁ y) *
        op (bilinear (u₂ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₂ y)))
      (closedLaw b W np) ∧
    (closedLaw b W np)[fun y =>
        bilinear (u₁ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₁ y) *
          op (bilinear (u₂ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₂ y)) |
        b3Sigma W j np] =ᵐ[closedLaw b W np] fun y =>
      ∫ F, bilinear (u₁ y) (freshDelta b E (X y) F) (v₁ y) *
        op (bilinear (u₂ y) (freshDelta b E (X y) F) (v₂ y)) ∂freshLaw W b := by
  have hrb : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => b3Rebuild W j z.1 :=
    (measurable_b3Rebuild W j).comp measurable_fst
  have hΔ := BlockBand.SourceProcess.FullSource.measurable_freshDelta_comp b E (hX.comp hrb)
    measurable_snd
  set Ψ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun z => bilinear (u₁ (b3Rebuild W j z.1)) (freshDelta b E (X (b3Rebuild W j z.1)) z.2)
        (v₁ (b3Rebuild W j z.1)) *
      op (bilinear (u₂ (b3Rebuild W j z.1)) (freshDelta b E (X (b3Rebuild W j z.1)) z.2)
        (v₂ (b3Rebuild W j z.1)))
  have hΨm : Measurable Ψ :=
    (BlockBand.SourceProcess.RawTag.measurable_bilinear_jt (hu₁.comp hrb) hΔ (hv₁.comp hrb)).mul
      (hop.measurable.comp
        (BlockBand.SourceProcess.RawTag.measurable_bilinear_jt (hu₂.comp hrb) hΔ (hv₂.comp hrb)))
  have hΨT : (fun y => Ψ (b3Past W j y, freshSample W j y.1.1)) = fun y =>
      bilinear (u₁ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₁ y) *
        op (bilinear (u₂ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₂ y)) := by
    funext y; simp only [Ψ, b3Rebuild_b3Past, hu₁', hv₁', hu₂', hv₂', hX']
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  have hgi : Integrable (fun y =>
      bilinear (u₁ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₁ y) *
        op (bilinear (u₂ y) (freshDelta b E (X y) (freshSample W j y.1.1)) (v₂ y)))
      (closedLaw b W np) := by
    rw [← hΨT]
    refine (hint.const_mul (Cf ^ 4)).mono' (hΨm.comp hT).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [congrFun hΨT y, norm_mul, hopn]
    have h1 := norm_bilinear_le_of_vecNorm (M := freshDelta b E (X y) (freshSample W j y.1.1))
      (hb₁ y) (hb₂ y)
    have h2 := norm_bilinear_le_of_vecNorm (M := freshDelta b E (X y) (freshSample W j y.1.1))
      (hb₃ y) (hb₄ y)
    calc _ ≤ (Cf ^ 2 * ‖freshDelta b E (X y) (freshSample W j y.1.1)‖) *
          (Cf ^ 2 * ‖freshDelta b E (X y) (freshSample W j y.1.1)‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨hgi, ?_⟩
  have hint' : Integrable (fun y => Ψ (b3Past W j y, freshSample W j y.1.1))
      (closedLaw b W np) := by rw [hΨT]; exact hgi
  have hc := condExp_closed_fresh b j hΨm hint'
  rw [hΨT] at hc
  filter_upwards [hc] with y hy
  rw [hy]
  simp only [Ψ, b3Rebuild_b3Past, hu₁', hv₁', hu₂', hv₂', hX']

end BlockBand.SourceProcess.PhysApprox.B3
