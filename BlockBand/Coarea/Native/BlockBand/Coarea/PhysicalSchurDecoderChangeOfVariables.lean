module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurDecoderJacobian
public import BlockBand.Coarea.Native.BlockBand.Coarea.EigenpairIncidenceChangeOfVariables

/-!
# Change of variables for the direct physical Schur decoder

The direct decoder `(E,z,B) ↦ Decode(E,z,B) - F(E)` is transported to finite
real Hermitian coordinates by the coherent-carrier equivalence.  Its derivative
and exact Jacobian `canonicalProjectiveAffineDensity z * |det (E I - B)|² *
vᴴ 𝒟(E) v` are inherited from `PhysicalSchurDecoderJacobian`, which gives the
area formula on every measurable injectivity source.

On a concrete ordered chart source the bare decoder is injective, so injectivity
of the direct decoder is equivalent to `PhysicalSchurEnergySeparation`: equal
images force equal incidence energies.  That deterministic spectral statement is
a hypothesis of the chart theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal

section FiniteCoordinates

variable {d : ℕ} (i : Fin d)

/-- The direct physical decoder `(E,z,B) ↦ Decode(E,z,B) - F(E)` in finite real
Hermitian coordinates. -/
def physicalSchurFinCoordinateDecode
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) : HermitianCoordinateSpace d :=
  coherentHermitianCoordinatesEquiv d
    (coherentPhysicalSchurDecode i F ((coherentHermitianCoordinatesEquiv d).symm x))

/-- The selected energy of the coherent copy of `x` is its incidence energy. -/
theorem coherentEigenpairEnergyCLM_symm (x : HermitianCoordinateSpace d) :
    coherentEigenpairEnergyCLM i ((coherentHermitianCoordinatesEquiv d).symm x) =
      (eigenpairIncidenceCoordinates i x).1 := rfl

/-- The coherent copy of `x` is the global input at its incidence coordinates. -/
theorem coherentEigenpairGlobalInput_incidence (x : HermitianCoordinateSpace d) :
    coherentEigenpairGlobalInput i (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.1 (eigenpairIncidenceCoordinates i x).2.2 =
      (coherentHermitianCoordinatesEquiv d).symm x := by
  apply (coherentSelectedBlockCoordinateLinearEquiv i).injective
  change (coherentSelectedBlockCoordinateLinearEquiv i)
    (coherentEigenpairGlobalInput i (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.1 (eigenpairIncidenceCoordinates i x).2.2) =
    eigenpairIncidenceCoordinates i x
  exact (coherentSelectedBlockCoordinateLinearEquiv i).apply_symm_apply _

/-- Explicit form: the finite-coordinate chart decoder minus the selected
readback of `F` at the incidence energy. -/
theorem physicalSchurFinCoordinateDecode_eq
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) :
    physicalSchurFinCoordinateDecode i F x =
      selectedEigenpairFinCoordinateChartDecode i x -
        (coherentMatrixReadbackCLM i (F (eigenpairIncidenceCoordinates i x).1)).value := by
  rw [physicalSchurFinCoordinateDecode, coherentPhysicalSchurDecode, map_sub,
    selectedEigenpairFinCoordinateChartDecode_eq_coherent_conjugation,
    coherentEigenpairEnergyCLM_symm]
  rfl

/-- The finite-coordinate physical decoder has the conjugated coherent derivative. -/
theorem hasFDerivAt_physicalSchurFinCoordinateDecode
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (F' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d)
    (hF : HasDerivAt F F' (eigenpairIncidenceCoordinates i x).1) :
    HasFDerivAt (physicalSchurFinCoordinateDecode i F)
      ((coherentHermitianCoordinatesEquiv d).toContinuousLinearMap.comp
        ((fderiv ℝ (coherentPhysicalSchurDecode i F)
            ((coherentHermitianCoordinatesEquiv d).symm x)).comp
          (coherentHermitianCoordinatesEquiv d).symm.toContinuousLinearMap)) x := by
  let e := coherentHermitianCoordinatesEquiv d
  have h := hasFDerivAt_coherentPhysicalSchurDecode i F F' (e.symm x) hF
  rw [← h.fderiv] at h
  exact e.hasFDerivAt.comp x (h.comp x e.symm.hasFDerivAt)

/-- Differentiability of the finite-coordinate physical decoder. -/
theorem differentiableAt_physicalSchurFinCoordinateDecode
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (F' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d)
    (hF : HasDerivAt F F' (eigenpairIncidenceCoordinates i x).1) :
    DifferentiableAt ℝ (physicalSchurFinCoordinateDecode i F) x :=
  (hasFDerivAt_physicalSchurFinCoordinateDecode i F F' x hF).differentiableAt

/-- Exact finite-coordinate Jacobian of the direct physical decoder at every
`x`, in terms of its incidence coordinates `(E,z,B)`. -/
theorem abs_det_fderiv_physicalSchurFinCoordinateDecode {n : Type*} [Fintype n]
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ) (x : HermitianCoordinateSpace d)
    (hF : HasDerivAt F (-(Tᴴ * T)) (eigenpairIncidenceCoordinates i x).1) :
    |LinearMap.det (fderiv ℝ (physicalSchurFinCoordinateDecode i F) x).toLinearMap| =
      canonicalProjectiveAffineDensity (eigenpairIncidenceCoordinates i x).2.1 *
        Complex.normSq (eigenpairGapMatrix (eigenpairIncidenceCoordinates i x).1
          (eigenpairIncidenceCoordinates i x).2.2.1).det *
        physicalEigenpairCrossingQuadratic T (eigenpairIncidenceCoordinates i x).2.1 := by
  let e := coherentHermitianCoordinatesEquiv d
  let L := fderiv ℝ (coherentPhysicalSchurDecode i F) (e.symm x)
  rw [(hasFDerivAt_physicalSchurFinCoordinateDecode i F _ x hF).fderiv]
  have hdet : LinearMap.det
      (e.toLinearEquiv.toLinearMap.comp
        (L.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)) =
      LinearMap.det L.toLinearMap := by
    rw [← LinearMap.det_conj L.toLinearMap e.toLinearEquiv]
    congr 1
  change |LinearMap.det (e.toLinearEquiv.toLinearMap.comp
      (L.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap))| = _
  rw [hdet]
  change |LinearMap.det (fderiv ℝ (coherentPhysicalSchurDecode i F)
    ((coherentHermitianCoordinatesEquiv d).symm x)).toLinearMap| = _
  rw [← coherentEigenpairGlobalInput_incidence i x]
  exact abs_det_fderiv_coherentPhysicalSchurDecode_globalInput i F T _ _ _ hF

/-- Physical Jacobian density of the direct decoder in incidence coordinates. -/
def physicalSchurDecoderDensity {n : Type*} [Fintype n]
    (T : ℝ → Matrix n (Unit ⊕ Fin (d - 1)) ℂ) (x : HermitianCoordinateSpace d) : ℝ :=
  canonicalProjectiveAffineDensity (eigenpairIncidenceCoordinates i x).2.1 *
    Complex.normSq (eigenpairGapMatrix (eigenpairIncidenceCoordinates i x).1
      (eigenpairIncidenceCoordinates i x).2.2.1).det *
    physicalEigenpairCrossingQuadratic (T (eigenpairIncidenceCoordinates i x).1)
      (eigenpairIncidenceCoordinates i x).2.1

/-- Exact change of variables for the direct physical decoder on any measurable
source on which it is injective. -/
theorem lintegral_image_physicalSchurFinCoordinateDecode {n : Type*} [Fintype n]
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (T : ℝ → Matrix n (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d)) (hs : MeasurableSet s)
    (hinj : Set.InjOn (physicalSchurFinCoordinateDecode i F) s)
    (hF : ∀ x ∈ s, HasDerivAt F
      (-((T (eigenpairIncidenceCoordinates i x).1)ᴴ * T (eigenpairIncidenceCoordinates i x).1))
      (eigenpairIncidenceCoordinates i x).1)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in physicalSchurFinCoordinateDecode i F '' s, g K) =
      ∫⁻ x in s, ENNReal.ofReal (physicalSchurDecoderDensity i T x) *
        g (physicalSchurFinCoordinateDecode i F x) := by
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x hx => (differentiableAt_physicalSchurFinCoordinateDecode i F _ x
      (hF x hx)).hasFDerivAt.hasFDerivWithinAt) hinj g]
  apply MeasureTheory.setLIntegral_congr_fun hs
  intro x hx
  change ENNReal.ofReal
      |LinearMap.det (fderiv ℝ (physicalSchurFinCoordinateDecode i F) x).toLinearMap| *
        g (physicalSchurFinCoordinateDecode i F x) = _
  rw [abs_det_fderiv_physicalSchurFinCoordinateDecode i F _ x (hF x hx)]
  rfl

/-- The deterministic energy-separation property: on `s`, equal direct-decoder
images force equal incidence energies.  This is the only ingredient of
injectivity not supplied by the concrete chart atlas. -/
def PhysicalSchurEnergySeparation
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d)) : Prop :=
  ∀ x ∈ s, ∀ x' ∈ s, physicalSchurFinCoordinateDecode i F x =
      physicalSchurFinCoordinateDecode i F x' →
    (eigenpairIncidenceCoordinates i x).1 = (eigenpairIncidenceCoordinates i x').1

/-- Equal energies reduce equal direct-decoder images to equal bare decoder
images. -/
theorem selectedEigenpairFinCoordinateChartDecode_eq_of_physical
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    {x x' : HermitianCoordinateSpace d}
    (hG : physicalSchurFinCoordinateDecode i F x = physicalSchurFinCoordinateDecode i F x')
    (hE : (eigenpairIncidenceCoordinates i x).1 = (eigenpairIncidenceCoordinates i x').1) :
    selectedEigenpairFinCoordinateChartDecode i x =
      selectedEigenpairFinCoordinateChartDecode i x' := by
  rw [physicalSchurFinCoordinateDecode_eq, physicalSchurFinCoordinateDecode_eq, hE] at hG
  exact sub_left_injective hG

end FiniteCoordinates

section ChartSource

variable {d : ℕ}

/-- On a concrete ordered chart source, energy separation is exactly what is
needed for injectivity of the direct physical decoder: the bare decoder is
injective there by the concrete atlas. -/
theorem injOn_physicalSchurFinCoordinateDecode_of_energySeparation
    (r : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d))
    (hsource : s ⊆ {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates (ofLex p).1 x ∈ selectedOrderedEigenpairChartSource r p})
    (hsep : PhysicalSchurEnergySeparation (ofLex p).1 F s) :
    Set.InjOn (physicalSchurFinCoordinateDecode (ofLex p).1 F) s := by
  intro x hx x' hx' hG
  exact (injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource r p)
    (hsource hx) (hsource hx')
    (selectedEigenpairFinCoordinateChartDecode_eq_of_physical _ F hG (hsep x hx x' hx' hG))

/-- Conversely, injectivity of the direct decoder on `s` implies energy
separation on `s`; the two are equivalent on a chart source. -/
theorem physicalSchurEnergySeparation_of_injOn (i : Fin d)
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d))
    (hinj : Set.InjOn (physicalSchurFinCoordinateDecode i F) s) :
    PhysicalSchurEnergySeparation i F s := by
  intro x hx x' hx' hG
  rw [hinj hx hx' hG]

/-- **Chart-level change of variables for the physical Schur decoder.**  On a
measurable piece of a concrete ordered chart source with Hermitian exterior block,
pole-free energies, and the deterministic energy-separation property, the direct
decoder `(E,z,B) ↦ Decode(E,z,B) - F(E)` with `F = V - Cᴴ(H_R - E)⁻¹C` satisfies
the exact area formula with Jacobian
`canonicalProjectiveAffineDensity z * |det (E I - B)|² * vᴴ 𝒟(E) v`. -/
theorem lintegral_physicalSchurDecoder_chart {r : ℕ}
    (rk : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d)
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hH : H_R.IsHermitian)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (s : Set (HermitianCoordinateSpace d)) (hs : MeasurableSet s)
    (hsource : s ⊆ {x : HermitianCoordinateSpace d |
      eigenpairIncidenceCoordinates (ofLex p).1 x ∈ selectedOrderedEigenpairChartSource rk p})
    (hpole : ∀ x ∈ s,
      (H_R - ((eigenpairIncidenceCoordinates (ofLex p).1 x).1 : ℂ) • 1).det ≠ 0)
    (hsep : PhysicalSchurEnergySeparation (ofLex p).1 (physicalCoareaF H_R C V) s)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in physicalSchurFinCoordinateDecode (ofLex p).1 (physicalCoareaF H_R C V) '' s,
        g K) =
      ∫⁻ x in s, ENNReal.ofReal
          (physicalSchurDecoderDensity (ofLex p).1 (physicalCoareaT H_R C) x) *
        g (physicalSchurFinCoordinateDecode (ofLex p).1 (physicalCoareaF H_R C V) x) :=
  lintegral_image_physicalSchurFinCoordinateDecode (ofLex p).1 _ _ s hs
    (injOn_physicalSchurFinCoordinateDecode_of_energySeparation rk p _ s hsource hsep)
    (fun x hx => hasDerivAt_physicalCoareaF H_R hH C V _ (hpole x hx)) g

end ChartSource

end CoareaNative.BlockBand
