module
public import BlockBand.SourceProcess.Stochastic.ItoNative.Pair
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Itô formula and the bilinear Itô product rule

Measure: `driverLaw μ` on `DriverSample S κ` (any measurable `S`, probability `μ`, finite `κ`);
filtration: the null-augmented `driverAugmented μ`; integrals: the adopted integral
`nativeIntegralOf` (`L²(dt ⊗ P)` integrands on `(0, T]` with a raw-predictable version);
values in arbitrary finite-dimensional real normed spaces `E, F, G`.

* `itoFormulaFor_holds : ItoFormulaFor μ E F` (proved as `itoFormulaFor_native`).
* `itoProductRuleFor_holds : ItoProductRuleFor μ E F G`: the pair `(X, Y)` is an Itô
  process in `E × F` (`IsNativeItoProcess.prod`), and the Itô formula is applied to
  `φ(t, (x, y)) = β x y`, whose derivatives are `D_xφ[(u, v)] = β x v + β u y`,
  `D_x²φ[(u, v), (u, v)] = 2 β u v`, `∂_tφ = 0` (`fderiv_bilinComp_apply`,
  `fderiv_fderiv_bilinComp_apply`).
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

section Bilinear
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

/-- The time-independent function `φ(t, (x, y)) = β x y`. -/
def bilinComp (β : E →L[ℝ] F →L[ℝ] G) : ℝ × (E × F) → G := fun q => β q.2.1 q.2.2

/-- The derivative of `bilinComp β` as a continuous linear map of the base point. -/
def bilinDeriv (β : E →L[ℝ] F →L[ℝ] G) : ℝ × (E × F) →L[ℝ] (ℝ × (E × F) →L[ℝ] G) :=
  ((ContinuousLinearMap.compL ℝ (ℝ × (E × F)) (E × F) G).flip
    (ContinuousLinearMap.snd ℝ ℝ (E × F))).comp
    ((β.isBoundedBilinearMap.isBoundedLinearMap_deriv.toContinuousLinearMap).comp
      (ContinuousLinearMap.snd ℝ ℝ (E × F)))

theorem bilinDeriv_apply (β : E →L[ℝ] F →L[ℝ] G) (q v : ℝ × (E × F)) :
    bilinDeriv β q v = β q.2.1 v.2.2 + β v.2.1 q.2.2 := by
  show β.isBoundedBilinearMap.deriv q.2 v.2 = _
  rw [IsBoundedBilinearMap.deriv_apply]

theorem hasFDerivAt_bilinComp (β : E →L[ℝ] F →L[ℝ] G) (q : ℝ × (E × F)) :
    HasFDerivAt (bilinComp β) (bilinDeriv β q) q := by
  have h := (β.isBoundedBilinearMap.hasFDerivAt q.2).comp q
    (hasFDerivAt_snd (p := q) (𝕜 := ℝ) (E := ℝ) (F := E × F))
  exact h

theorem fderiv_bilinComp (β : E →L[ℝ] F →L[ℝ] G) :
    fderiv ℝ (bilinComp β) = bilinDeriv β :=
  funext fun q => (hasFDerivAt_bilinComp β q).fderiv

theorem fderiv_bilinComp_apply (β : E →L[ℝ] F →L[ℝ] G) (q v : ℝ × (E × F)) :
    fderiv ℝ (bilinComp β) q v = β q.2.1 v.2.2 + β v.2.1 q.2.2 := by
  rw [fderiv_bilinComp, bilinDeriv_apply]

theorem fderiv_fderiv_bilinComp_apply (β : E →L[ℝ] F →L[ℝ] G) (q v w : ℝ × (E × F)) :
    fderiv ℝ (fderiv ℝ (bilinComp β)) q v w = β v.2.1 w.2.2 + β w.2.1 v.2.2 := by
  rw [fderiv_bilinComp, ContinuousLinearMap.fderiv, bilinDeriv_apply]

theorem contDiff_bilinComp (β : E →L[ℝ] F →L[ℝ] G) : ContDiff ℝ 2 (bilinComp β) :=
  β.isBoundedBilinearMap.contDiff.comp contDiff_snd

end Bilinear

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- **Multidimensional time-dependent Itô formula on the space.** -/
theorem itoFormulaFor_holds : ItoFormulaFor (κ := κ) μ E F := itoFormulaFor_native

/-- **Bilinear Itô product rule on the space.** -/
theorem itoProductRuleFor_holds : ItoProductRuleFor (κ := κ) μ E F G := by
  intro X bX σX Y bY σY hX hY β
  have hP := hX.prod hY
  have key : IsNativeItoProcess μ (fun t x => bilinComp β ((t : ℝ), (X t x, Y t x)))
      (fun t x => timeDeriv (bilinComp β) ((t : ℝ), (X t x, Y t x)) +
        spaceDeriv (bilinComp β) ((t : ℝ), (X t x, Y t x)) (bX t x, bY t x) +
        (1 / 2 : ℝ) • ∑ a, spaceDeriv2 (bilinComp β) ((t : ℝ), (X t x, Y t x))
          (σX a t x, σY a t x) (σX a t x, σY a t x))
      (fun a t x => spaceDeriv (bilinComp β) ((t : ℝ), (X t x, Y t x)) (σX a t x, σY a t x)) :=
    itoFormulaFor_native (κ := κ) (μ := μ) (E := E × F) (F := G) _ _ _ hP (bilinComp β)
      (contDiff_bilinComp β)
  have hd : (fun (t : ℝ≥0) (x : DriverSample S κ) =>
      timeDeriv (bilinComp β) ((t : ℝ), (X t x, Y t x)) +
        spaceDeriv (bilinComp β) ((t : ℝ), (X t x, Y t x)) (bX t x, bY t x) +
        (1 / 2 : ℝ) • ∑ a, spaceDeriv2 (bilinComp β) ((t : ℝ), (X t x, Y t x))
          (σX a t x, σY a t x) (σX a t x, σY a t x)) =
      fun t x => β (bX t x) (Y t x) + β (X t x) (bY t x) + ∑ a, β (σX a t x) (σY a t x) := by
    funext t x
    simp only [timeDeriv, spaceDeriv, spaceDeriv2, fderiv_bilinComp_apply,
      fderiv_fderiv_bilinComp_apply, Prod.snd_zero, Prod.fst_zero, map_zero, zero_apply,
      zero_add, Finset.smul_sum]
    have h2 : ∀ a, (1 / 2 : ℝ) • (β (σX a t x) (σY a t x) + β (σX a t x) (σY a t x)) =
        β (σX a t x) (σY a t x) := fun a => by
      rw [← two_smul ℝ (β (σX a t x) (σY a t x)), smul_smul]
      norm_num
    simp only [h2]
    abel
  have hσ : (fun (a : κ) (t : ℝ≥0) (x : DriverSample S κ) =>
      spaceDeriv (bilinComp β) ((t : ℝ), (X t x, Y t x)) (σX a t x, σY a t x)) =
      fun a t x => β (σX a t x) (Y t x) + β (X t x) (σY a t x) := by
    funext a t x
    simp only [spaceDeriv, fderiv_bilinComp_apply]
    abel
  rw [hd, hσ] at key
  exact key

end BlockBand.SourceProcess.Stochastic.ItoNative
