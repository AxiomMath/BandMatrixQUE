module

public import BlockBand.Critical.PointDensity.MeanDensity
public import BlockBand.Palm.MomentFlow.LocalScaling

/-!
# Point density: the Johansson one-point correlation is the mean measure

For the deformed GUE `F - x I + G`, the order-one factorial correlation measure, shifted back
by `x`, equals `N` times the mean eigenvalue measure of `F + G`.

* `map_deformedFactorialCorrelation_one`: pushing the order-one correlation forward by
  `v ↦ v 0 + x` gives `N • freshMeanEigenvalueMeasure N c F` (via `map_gaussianMatrixRaw`, the
  eigenvalue shift `λ_ℓ(K + a) = λ_ℓ(K) + a`, and a sum over ranks).
* `map_withDensity_of_measurePreserving`, `map_shift_withDensity`: the pushforward of a Lebesgue
  density on `Fin 1 → ℝ` by `v ↦ v 0 + x` is the density `y ↦ f (fun _ => y - x)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.PointDensity

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Critical
  BlockBand.Coarea.FreshPalm BlockBand.External BlockBand.Model.Construction
open scoped ENNReal NNReal

variable {N : ℕ}

/-- `(Fin 1 ↪ Fin N) ≃ Fin N`, `e ↦ e 0`. -/
def embFinOneEquiv (N : ℕ) : (Fin 1 ↪ Fin N) ≃ Fin N where
  toFun e := e 0
  invFun ℓ := ⟨fun _ => ℓ, fun a b _ => Subsingleton.elim a b⟩
  left_inv e := by
    ext i
    rw [Subsingleton.elim i 0]
    rfl
  right_inv _ := rfl

/-- The one-rank Johansson spectral tuple is the `freshEigenvalue`. -/
theorem spectralTuple_zero_eq (e : Fin 1 ↪ Fin N) (K : Matrix (Fin N) (Fin N) ℂ)
    (hK : K.IsHermitian) :
    Johansson.spectralTuple e ⟨K, hK⟩ 0 = freshEigenvalue K (e 0) := by
  unfold Johansson.spectralTuple freshEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ hK]
  rfl

/-- One rank: the Johansson law of `λ_{e 0}(F - x + G) + x` is `Law(λ_{e 0}(F + G))`. -/
theorem map_spectralTuple_shift (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) (x : ℝ)
    (hF' : (F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian) (e : Fin 1 ↪ Fin N) :
    ((BlockBand.Internal.Contracts.Inputs.deformedGUELaw N (Real.toNNReal c)
        (F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) hF').map
        (Johansson.spectralTuple e)).map (fun v => v 0 + x) =
      (gueMeasure (Fin N) (Real.toNNReal (c / N))).map
        (fun G => freshEigenvalue (F + G) (e 0)) := by
  set F' := F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) with hF'def
  have hπ : Measurable fun v : Fin 1 → ℝ => v 0 + x :=
    (measurable_pi_apply 0).add measurable_const
  have hraw : Measurable (Johansson.gaussianMatrixRaw (N := N)) :=
    measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix
  have hg : Measurable fun z : Johansson.UpperPair N → ℝ × ℝ =>
      (⟨F' + (Johansson.gaussianMatrix z).1, hF'.add (Johansson.gaussianMatrix z).2⟩ :
        Johansson.HermitianMatrix N) :=
    (BlockBand.Coarea.FixedOmega.measurable_matrix_add measurable_const hraw).subtype_mk
  have hfe : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => freshEigenvalue (F + G) (e 0) :=
    (measurable_freshEigenvalue (e 0)).comp
      (BlockBand.Coarea.FixedOmega.measurable_matrix_add measurable_const measurable_id)
  have hS : Johansson.sourceTime N (Real.toNNReal c) = Real.toNNReal (c / N) := by
    apply NNReal.coe_injective
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Johansson.sourceTime_coe, Real.coe_toNNReal _ hc.le,
      Real.coe_toNNReal _ (div_pos hc hNr).le]
  unfold BlockBand.Internal.Contracts.Inputs.deformedGUELaw
  rw [Measure.map_map hπ (Johansson.measurable_spectralTuple e),
    Measure.map_map (hπ.comp (Johansson.measurable_spectralTuple e)) hg,
    ← BlockBand.Palm.MomentFlow.map_gaussianMatrixRaw, hS, Measure.map_map hfe hraw]
  congr 1
  funext z
  simp only [Function.comp]
  rw [spectralTuple_zero_eq e _ (hF'.add (Johansson.gaussianMatrix z).2)]
  have hz : (Johansson.gaussianMatrix z).1 = Johansson.gaussianMatrixRaw z := rfl
  have hsum : F' + (Johansson.gaussianMatrix z).1 =
      (F + Johansson.gaussianMatrixRaw z) + ((-x : ℝ) : ℂ) • 1 := by
    rw [hz, hF'def, Complex.ofReal_neg, neg_smul]
    abel
  rw [hsum, freshEigenvalue_add_smul_one (hF.add (Johansson.gaussianMatrixRaw_isHermitian z))]
  ring

/-- **The order-one factorial correlation is `N` times the mean measure.** For `N ≥ 1`,
Hermitian `F`, `c > 0`, real `x`, `F' = F - x I`:
`(deformedFactorialCorrelation N c F' hF' 1).map (v ↦ v 0 + x) =
N • freshMeanEigenvalueMeasure N c F`. -/
theorem map_deformedFactorialCorrelation_one (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c : ℝ} (hc : 0 < c) (x : ℝ)
    (hF' : (F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).IsHermitian) :
    (BlockBand.Internal.Contracts.Inputs.deformedFactorialCorrelation N (Real.toNNReal c)
        (F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) hF' 1).map (fun v => v 0 + x) =
      (N : ℝ≥0∞) • freshMeanEigenvalueMeasure N c F := by
  have hπ : Measurable fun v : Fin 1 → ℝ => v 0 + x :=
    (measurable_pi_apply 0).add measurable_const
  unfold BlockBand.Internal.Contracts.Inputs.deformedFactorialCorrelation
  rw [Measure.map_finset_sum' hπ.aemeasurable]
  simp_rw [map_spectralTuple_shift hN hF hc x hF']
  rw [Fintype.sum_equiv (embFinOneEquiv N)
    (fun e => (gueMeasure (Fin N) (Real.toNNReal (c / N))).map
      (fun G => freshEigenvalue (F + G) (e 0)))
    (fun ℓ => (gueMeasure (Fin N) (Real.toNNReal (c / N))).map
      (fun G => freshEigenvalue (F + G) ℓ)) (fun _ => rfl)]
  unfold freshMeanEigenvalueMeasure
  rw [smul_smul, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hN.ne') (ENNReal.natCast_ne_top N),
    one_smul]

/-- Pushforward of a density by a measure-preserving measurable equivalence. -/
theorem map_withDensity_of_measurePreserving {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} (e : α ≃ᵐ β)
    (he : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = ν.withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← he.setLIntegral_comp_preimage_emb e.measurableEmbedding]
  simp [Function.comp]

/-- The shift `v ↦ v 0 + x` from `Fin 1 → ℝ` to `ℝ` as a measurable equivalence. -/
def shiftEquiv (x : ℝ) : (Fin 1 → ℝ) ≃ᵐ ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).trans (MeasurableEquiv.addRight x)

theorem coe_shiftEquiv (x : ℝ) : ⇑(shiftEquiv x) = fun v : Fin 1 → ℝ => v 0 + x := rfl

theorem shiftEquiv_symm_apply (x y : ℝ) : (shiftEquiv x).symm y = fun _ => y - x := by
  funext i
  simp [shiftEquiv, MeasurableEquiv.funUnique, sub_eq_add_neg]

theorem measurePreserving_shiftEquiv (x : ℝ) :
    MeasurePreserving (shiftEquiv x) (volume : Measure (Fin 1 → ℝ)) (volume : Measure ℝ) :=
  (measurePreserving_add_right volume x).comp (volume_preserving_funUnique (Fin 1) ℝ)

/-- `(volume.withDensity f).map (v ↦ v 0 + x) = volume.withDensity (y ↦ f (fun _ => y - x))`. -/
theorem map_shift_withDensity (x : ℝ) (f : (Fin 1 → ℝ) → ℝ≥0∞) :
    ((volume : Measure (Fin 1 → ℝ)).withDensity f).map (fun v => v 0 + x) =
      volume.withDensity (fun y => f (fun _ => y - x)) := by
  rw [← coe_shiftEquiv, map_withDensity_of_measurePreserving _ (measurePreserving_shiftEquiv x)]
  congr 1

end BlockBand.Critical.PointDensity
