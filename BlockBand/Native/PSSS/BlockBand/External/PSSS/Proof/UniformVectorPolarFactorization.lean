module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorSpectralTrace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar factorization with a radial density

The polar map identifies the nonzero locus with the product of the unit sphere and the positive
radii. Reweighting Haar measure by a radial density keeps this product form: the angular factor
stays uniform and only the radial factor changes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory

/-- The first polar coordinate is the same normalization used by
`complexGaussianDirection`, on the nonzero locus. -/
theorem complexGaussianDirection_eq_polar_fst {N : ℕ}
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin N)))) :
    complexGaussianDirection (x : EuclideanSpace ℂ (Fin N)) =
      ((homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin N))) x).1 := by
  rw [homeomorphUnitSphereProd_apply_fst_coe]
  rfl

/-- The second polar coordinate is exactly the Gaussian radius. -/
theorem norm_eq_polar_snd {N : ℕ}
    (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin N)))) :
    ‖(x : EuclideanSpace ℂ (Fin N))‖ =
      ((homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin N))) x).2 := by
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- A measurable equivalence transports a density pulled back from its target.
This is the measure-theoretic bridge that permits radial weights to be inserted
into the exact Haar polar decomposition. -/
theorem map_withDensity_comp_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (h : MeasurePreserving e μ ν) (w : β → ENNReal) (hw : Measurable w) :
    Measure.map e (μ.withDensity (w ∘ e)) = ν.withDensity w := by
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  rw [withDensity_apply (w ∘ e) (hs.preimage e.measurable)]
  rw [withDensity_apply w hs]
  rw [← lintegral_indicator (hs.preimage e.measurable)]
  rw [← lintegral_indicator hs]
  rw [← h.lintegral_comp (hw.indicator hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s
  · simp [hx]
  · simp [hx]

/-- Any measurable radial density preserves the product form of polar
coordinates.  The angular marginal remains Haar-uniform on the unit sphere;
all weighting is confined to the positive-radius factor. -/
theorem map_polar_withDensity_radial
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure]
    (w : Set.Ioi (0 : ℝ) → ENNReal) (hw : Measurable w) :
    Measure.map ((homeomorphUnitSphereProd E).toMeasurableEquiv)
        ((volume.comap (fun x : ({0}ᶜ : Set E) => (x : E))).withDensity
          (w ∘ fun x => ((homeomorphUnitSphereProd E) x).2)) =
      volume.toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity w) := by
  rw [prod_withDensity_right hw]
  exact map_withDensity_comp_of_measurePreserving
    ((homeomorphUnitSphereProd E).toMeasurableEquiv)
    (volume.comap (fun x : ({0}ᶜ : Set E) => (x : E)))
    (volume.toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ E - 1)))
    (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
    (fun z => w z.2) (hw.comp measurable_snd)

end PSSSNative.BlockBand.PSSS
