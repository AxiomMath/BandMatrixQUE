module

public import BlockBand.Critical.RelativeVectors.Statement
public import BlockBand.Critical.PointDensity

/-!
# The unmarked sine limit at variance `c`

*Law.* `G ~ gueMeasure (Fin N) (c/N)` (`GUE_N(c/N)`), `F` deterministic.
*Points.* `x_ℓ = Nρ(λ_ℓ(F + G) - E)`, `ρ = unfoldingDensity F c E = π^{-1} Im m_{F,c}(E)`.

* `unfoldedLaplace_shift`: `Inputs.unfoldedLaplace` of `F - E` at energy `0` (Johansson
  coordinate law at `S = c/N`) is the `GUE_N(c/N)` Laplace functional of the points
  `Nρ(λ_ℓ(F+G) - E)` (exact, every `N ≥ 1`, Hermitian `F`, `c > 0`, measurable `f`).
* `unfoldedSine_uniform`: for fixed `A`, `FreshConstants c r₀ s₀ v₀`, nonnegative
  `ψ ∈ C_c(ℝ)` and `δ > 0` there is `N₀` such that for `N ≥ N₀` and every `F` in
  `FreshClass F A c E r₀ s₀ v₀`: `|E e^{-Σ_ℓ ψ(x_ℓ)} - sineLaplaceFunctional ψ| ≤ δ`.
  Uniform in `F` and `E`. It uses `Inputs.ExternalSine` (clause (c)) at `t ∈ [c, c]`, `v = v₀`,
  energy window `[0, 0]`, exponent `A' = max(A,0) + 1` (`‖F - E‖ ≤ 2N^A + 2v₀⁻¹ ≤ N^{A'}` for
  `N ≥ 2 + 2v₀⁻¹`), through the translation `F ↦ F - E` and `M = freshM F c E`
  (`IsBoundaryMDE c (F - E) 0 M`, `⟨M⟩ = m_{F,c}(E)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.External
open BlockBand.Critical.PointDensity
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {N : ℕ}

/-- The full unfolded statistic `Σ_ℓ f(Nρ(λ_ℓ(K) - E))` over increasing ranks. -/
def unfoldedSum (K : Matrix (Fin N) (Fin N) ℂ) (E ρ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ ℓ : Fin N, f ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E))

/-- **Translation of the Johansson Laplace functional.** For `N ≥ 1`, Hermitian `F`, `c > 0`,
real `E, ρ` and measurable `f`: `unfoldedLaplace N c (F - E) 0 ρ f = E exp{-Σ_ℓ f(Nρ(λ_ℓ(F+G) - E))}`
under `G ~ GUE_N(c/N)` (exact identity). -/
theorem unfoldedLaplace_shift (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {c : ℝ} (hc : 0 < c) (E ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hF' : (F - (E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian) :
    BlockBand.Internal.Contracts.Inputs.unfoldedLaplace N (Real.toNNReal c) (F - (E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))
        hF' 0 ρ f =
      ∫ G, Real.exp (-unfoldedSum (F + G) E ρ f) ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) := by
  set F' := F - (E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) with hF'def
  have hraw : Measurable (Johansson.gaussianMatrixRaw (N := N)) :=
    measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix
  have hg : Measurable fun z : Johansson.UpperPair N → ℝ × ℝ =>
      (⟨F' + (Johansson.gaussianMatrix z).1, hF'.add (Johansson.gaussianMatrix z).2⟩ :
        Johansson.HermitianMatrix N) :=
    (BlockBand.Coarea.FixedOmega.measurable_matrix_add measurable_const hraw).subtype_mk
  have hint : Measurable fun A : Johansson.HermitianMatrix N =>
      Real.exp (-(∑ i, f ((N : ℝ) * ρ * (Model.Construction.orderedEigenvalue A i - 0)))) := by
    refine Real.measurable_exp.comp (Measurable.neg ?_)
    refine Finset.measurable_sum _ fun i _ => hf.comp ?_
    exact measurable_const.mul
      ((Model.Construction.measurable_orderedEigenvalue i).sub measurable_const)
  have hfresh : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      Real.exp (-unfoldedSum (F + G) E ρ f) := by
    refine Real.measurable_exp.comp (Measurable.neg ?_)
    refine Finset.measurable_sum _ fun ℓ _ => hf.comp ?_
    exact measurable_const.mul
      (((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).comp
        (continuous_const.add continuous_id).measurable).sub measurable_const)
  have hS : Johansson.sourceTime N (Real.toNNReal c) = Real.toNNReal (c / N) := by
    apply NNReal.coe_injective
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Johansson.sourceTime_coe, Real.coe_toNNReal _ hc.le,
      Real.coe_toNNReal _ (div_pos hc hNr).le]
  unfold BlockBand.Internal.Contracts.Inputs.unfoldedLaplace BlockBand.Internal.Contracts.Inputs.deformedGUELaw
  rw [integral_map hg.aemeasurable hint.aestronglyMeasurable,
    ← BlockBand.Palm.MomentFlow.map_gaussianMatrixRaw, hS,
    integral_map hraw.aemeasurable hfresh.aestronglyMeasurable]
  congr 1
  funext z
  have hz : (Johansson.gaussianMatrix z).1 = Johansson.gaussianMatrixRaw z := rfl
  have hK := hF.add (Johansson.gaussianMatrixRaw_isHermitian z)
  have hsum : F' + (Johansson.gaussianMatrix z).1 =
      (F + Johansson.gaussianMatrixRaw z) + ((-E : ℝ) : ℂ) • 1 := by
    rw [hz, hF'def, Complex.ofReal_neg, neg_smul]
    abel
  congr 2
  unfold unfoldedSum
  refine Fintype.sum_equiv (finCongr (Fintype.card_fin N)) _ _ fun i => ?_
  congr 2
  have hK2 : ((F + Johansson.gaussianMatrixRaw z) + ((-E : ℝ) : ℂ) • 1).IsHermitian := by
    rw [← hsum]; exact hF'.add (Johansson.gaussianMatrix z).2
  have hA : (⟨F' + (Johansson.gaussianMatrix z).1, hF'.add (Johansson.gaussianMatrix z).2⟩ :
      Johansson.HermitianMatrix N) =
      ⟨(F + Johansson.gaussianMatrixRaw z) + ((-E : ℝ) : ℂ) • 1, hK2⟩ := Subtype.ext hsum
  rw [hA]
  have hfe := BlockBand.Coarea.FreshPalm.freshEigenvalue_add_smul_one hK (-E) (finCongr (Fintype.card_fin N) i)
  have hord : Model.Construction.orderedEigenvalue
      (⟨(F + Johansson.gaussianMatrixRaw z) + ((-E : ℝ) : ℂ) • 1, hK2⟩ :
        Johansson.HermitianMatrix N) i =
      freshEigenvalue ((F + Johansson.gaussianMatrixRaw z) + ((-E : ℝ) : ℂ) • 1)
        (finCongr (Fintype.card_fin N) i) := by
    unfold freshEigenvalue Model.Construction.orderedEigenvalue
    rw [Model.Construction.rawIncreasingEigenvalue_eq]
    rfl
  rw [hord, hfe]
  ring

/-- **Unmarked sine limit at variance `c`, uniformly over the regular class.** Fixed `A`,
`FreshConstants c r₀ s₀ v₀`, a nonnegative `ψ ∈ C_c(ℝ)` and `δ > 0`; then there is `N₀` such that
for every `N ≥ N₀` and every `F` in `FreshClass F A c E r₀ s₀ v₀`, under `G ~ GUE_N(c/N)`, with
`ρ = π^{-1} Im m_{F,c}(E)`: `|E exp{-Σ_ℓ ψ(Nρ(λ_ℓ(F+G) - E))} - sineLaplaceFunctional ψ| ≤ δ`.
The only hypothesis is `Inputs.ExternalSine`. -/
theorem unfoldedSine_uniform (hES : BlockBand.Internal.Contracts.Inputs.ExternalSine) {A c r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (ψ : CompactlySupportedContinuousMap ℝ ℝ)
    (hψ : ∀ x, 0 ≤ ψ x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c E r₀ s₀ v₀ →
        |(∫ G, Real.exp (-unfoldedSum (F + G) E (unfoldingDensity F c E) ψ)
            ∂gueMeasure (Fin N) (Real.toNNReal (c / N))) -
          BlockBand.sineLaplaceFunctional ψ| ≤ δ := by
  have hc0 : 0 < c := hK.1
  have hv₀ : 0 < v₀ := hK.2.2.2.2.2
  obtain ⟨N₀, hN₀⟩ := (hES (max A 0 + 1) c c v₀ 0 0 0 hc0 le_rfl hv₀).2 ψ hψ δ hδ
  refine ⟨max N₀ (max 1 ⌈2 + 2 * v₀⁻¹⌉₊), fun N hN F E hC => ?_⟩
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 0 < N := lt_of_lt_of_le Nat.one_pos
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
  have hN2 : 2 + 2 * v₀⁻¹ ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by
      have h3 : ⌈2 + 2 * v₀⁻¹⌉₊ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
      exact_mod_cast h3)
  have hF : F.IsHermitian := hC.1
  obtain ⟨hv, -⟩ := freshDyson_im_bounds hK hC
  have hm : 0 < (freshDyson F c E).im := lt_of_lt_of_le hv₀ hv
  have hF' : (F - (E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian :=
    hF.sub (isHermitian_one.smul (Complex.conj_ofReal E))
  have hnorm : ‖F - (E : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ (N : ℝ) ^ (max A 0 + 1) :=
    (opNorm_sub_center_le hF hN1 hC.2.1 hc0 hv₀ hv).trans (two_rpow_add_le hv₀ hN2)
  obtain ⟨hMDE, htr⟩ := isBoundaryMDE_freshM hF hc0 hm
  have ht : ((Real.toNNReal c : ℝ≥0) : ℝ) = c := Real.coe_toNNReal _ hc0.le
  have h := hN₀ N hNN₀ _ hF' hnorm (Real.toNNReal c) (by rw [ht]; exact ⟨le_rfl, le_rfl⟩)
    0 ⟨le_rfl, le_rfl⟩ (freshM F c E) (by rw [ht]; exact hMDE) (by rw [htr]; exact hv)
  rw [htr, unfoldedLaplace_shift hN1 hF hc0 E _ (map_continuous ψ).measurable hF'] at h
  exact h

end BlockBand.Critical.RelativeVectors
