module

public import BlockBand.Internal.Contracts.WindowAngular

/-!
# Statements of the sharper fresh count and the refined count

The statements `SharperFreshCountStatement` and `RefinedCountStatement`. Conventions: `GUE_W(t)` is
`CoareaPalm.gueMeasure (Fin W) t`, `N_-` is `CoareaPalm.negativeCount`, `N_H(e) = #{λ_j < e}` is
`Layers.physicalCount`, compact bulk intervals are `Layers.bulkInterval κ`, `κ > 0`, ranks are
zero-based with the one-based `IsBulkRank`, and `e_α = Layers.classicalLocation p α`. "For every
fixed `p`" is `∀ p ≥ 1, ∃ C_p`, chosen after the model constants and before `n, W` and all
deterministic data.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory
open BlockBand.Model.Construction BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.WindowAngular
open scoped ENNReal NNReal

/-- The sharper fresh count. `A ~ GUE_W(c/W)`, `F` any Hermitian
deformation independent of `A` (here deterministic: the statement is conditional on `F`), no
bound on `‖F‖`, every real deterministic `e`, every fixed `p ≥ 1`:
`‖N_-(A + F - e) - E_A N_-(A + F - e)‖_{L^p(A)} ≤ C_{c,p} W^{1/3}`, with `C` depending only on
`c > 0` and `p`, uniformly in `W ≥ 1`, `F` and `e`. -/
def SharperFreshCountStatement : Prop :=
  ∀ c : ℝ, 0 < c → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ F : Matrix (Fin W) (Fin W) ℂ, F.IsHermitian → ∀ e : ℝ,
      let μ := gueMeasure (Fin W) (Real.toNNReal (c / W))
      eLpNorm (fun A => (negativeCount (A + F - (e : ℂ) • 1) : ℝ) -
          ∫ A', (negativeCount (A' + F - (e : ℂ) • 1) : ℝ) ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * (W : ℝ) ^ (1 / 3 : ℝ))

/-- The refined count, under the physical law, with `a_{n,W} = countScale n W`.
* `count`: `b, T`, a compact bulk interval `bulkInterval κ` and each fixed `p ≥ 1` first; at
  every deterministic `e` in it, `‖N_H(e) - N F_sc(e)‖_p ≤ C_p a_{n,W}`, for `4 ≤ n ≤ TW`.
* `location`: `b, T`, a bulk margin `ϑ` and each fixed `p ≥ 1` first; for every
  deterministic rank with `ϑ ≤ α/N ≤ 1 - ϑ`, `‖λ_α - e_α‖_p ≤ C_p a_{n,W}/N`.
No lower bound on `n/W` is required. (The ratio clause `a_{n,W}/√n → 1` along
`n/W → τ > 0` is elementary and is proved as
`Transfer.critical_refined_scale_ratio_tendsto`.) -/
structure RefinedCountStatement : Prop where
  count : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (e : ℝ), e ∈ bulkInterval κ →
      eLpNorm (fun H => (physicalCount p H e : ℝ) - p.N * semicircleCDF e) (ENNReal.ofReal q)
          (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal (Cq * countScale p.n p.W)
  location : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ T ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (Cq * countScale p.n p.W / p.N)

end BlockBand.Window.Count
