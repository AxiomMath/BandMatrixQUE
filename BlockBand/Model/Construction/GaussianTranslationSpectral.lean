module

public import BlockBand.Model.Construction.SpectralRealization
public import BlockBand.QUE.Haar.ProjectorTransport

/-!
# Deterministic scalar translation of raw matrices

Adding `t · 1` to a matrix translates its ordered eigenvalues and the spectral locations of the
canonical marked configuration by `t`, leaves the eigenvector selection unchanged, and is
measurable.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Model.Construction
open Matrix MeasureTheory
open BlockBand.Foundations.Spectral
open BlockBand.QUE.Haar
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real scalar translation of raw matrices. -/
def gaussianSpectralTranslate (t : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  H + (t : ℂ) • 1

omit [Fintype ι] in
theorem isHermitian_gaussianSpectralTranslate (t : ℝ) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) : (gaussianSpectralTranslate t H).IsHermitian := by
  apply hH.add
  simp [Matrix.IsHermitian]

/-- Hermitian scalar translation, with its proof of Hermitian-ness. -/
def hermitianSpectralTranslate (t : ℝ) (A : HermitianMatrix ι) : HermitianMatrix ι :=
  ⟨gaussianSpectralTranslate t A.val, isHermitian_gaussianSpectralTranslate t A.val A.property⟩

theorem orderedEigenvalue_gaussianSpectralTranslate (t : ℝ) (A : HermitianMatrix ι) :
    orderedEigenvalue (hermitianSpectralTranslate t A) = fun i => orderedEigenvalue A i + t := by
  apply orderedEigenvalue_eq_of_rank_eigenbasis _ _ (increasingEigenvector A.property)
  · exact increasingEigenvector_orthonormal A.property
  · intro i
    change (A.val + (t : ℂ) • 1) *ᵥ increasingEigenvector A.property i = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      mulVec_increasingEigenvector]
    simp only [orderedEigenvalue, Complex.ofReal_add, add_smul]
  · exact (increasingEigenvalue_monotone A.property).add_const t

theorem orderedProjectorFactor_gaussianSpectralTranslate (t : ℝ) (A : HermitianMatrix ι)
    (i j : Fin (Fintype.card ι)) :
    orderedProjectorFactor i j (hermitianSpectralTranslate t A) = orderedProjectorFactor i j A := by
  by_cases hij : j = i
  · simp [orderedProjectorFactor, hij]
  · simp only [orderedProjectorFactor, hij, ite_false,
      orderedEigenvalue_gaussianSpectralTranslate, add_sub_add_right_eq_sub]
    congr 1
    change A.val + (t : ℂ) • 1 - ((orderedEigenvalue A j + t : ℝ) : ℂ) • 1 = _
    rw [Complex.ofReal_add, add_smul]
    abel

theorem orderedProjector_gaussianSpectralTranslate (t : ℝ) (A : HermitianMatrix ι)
    (i : Fin (Fintype.card ι)) :
    orderedProjector i (hermitianSpectralTranslate t A) = orderedProjector i A := by
  simp only [orderedProjector, orderedProjectorProduct,
    orderedProjectorFactor_gaussianSpectralTranslate]

/-- The explicit projector-column selector itself is unchanged; phases need not be assumed. -/
theorem orderedColumnSelection_gaussianSpectralTranslate (t : ℝ) (A : HermitianMatrix ι)
    (i : Fin (Fintype.card ι)) (x : ι) :
    orderedColumnSelection i (hermitianSpectralTranslate t A) x = orderedColumnSelection i A x := by
  classical
  simp only [orderedColumnSelection]
  apply Finset.sum_congr rfl
  intro j _
  have hr : (hermitianSpectralTranslate t A ∈ orderedColumnRegion i j) ↔
      (A ∈ orderedColumnRegion i j) := by
    simp only [orderedColumnRegion, Set.mem_ofPred_eq, orderedColumnAvailable,
      orderedProjector_gaussianSpectralTranslate]
  have hn : orderedNormalizedColumn i j (hermitianSpectralTranslate t A) x =
      orderedNormalizedColumn i j A x := by
    simp only [orderedNormalizedColumn, orderedProjector_gaussianSpectralTranslate]
  by_cases hj : A ∈ orderedColumnRegion i j
  · simp only [ite_eq_left (hr.mpr hj), ite_eq_left hj, hn]
  · simp only [ite_eq_right (mt hr.mp hj), ite_eq_right hj]

/-- Simple-spectrum characteristic polynomial is preserved as a property. -/
theorem separable_gaussianSpectralTranslate (t : ℝ) (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (hsep : H.charpoly.Separable) :
    (gaussianSpectralTranslate t H).charpoly.Separable := by
  apply charpoly_separable_of_injective_orderedEigenvalue (hermitianSpectralTranslate t ⟨H, hH⟩)
  rw [orderedEigenvalue_gaussianSpectralTranslate]
  intro i j hij
  apply orderedEigenvalue_injective_of_separable (⟨H,hH⟩ : HermitianMatrix ι) hsep
  exact add_right_cancel hij

/-- Physical ordered eigenvalues shift by the same scalar, without simplicity. -/
theorem physicalOrderedEigenvalue_gaussianSpectralTranslate (p : Parameters) (t : ℝ)
    (H : p.SiteMatrix) (hH : H.IsHermitian) (α : Fin p.N) :
    physicalOrderedEigenvalue p (gaussianSpectralTranslate t H) α =
      physicalOrderedEigenvalue p H α + t := by
  simp only [physicalOrderedEigenvalue, rawIncreasingEigenvalue_eq _ _
    (isHermitian_gaussianSpectralTranslate t H hH), rawIncreasingEigenvalue_eq _ _ hH]
  exact congrFun (orderedEigenvalue_gaussianSpectralTranslate t ⟨H,hH⟩) _

theorem physicalOrderedEigenvector_gaussianSpectralTranslate (p : Parameters) (t : ℝ)
    (H : p.SiteMatrix) (hH : H.IsHermitian) (α : Fin p.N) (x : p.Site) :
    physicalOrderedEigenvector p (gaussianSpectralTranslate t H) α x =
      physicalOrderedEigenvector p H α x := by
  simp only [physicalOrderedEigenvector, rawOrderedColumnSelection_eq _ _
    (isHermitian_gaussianSpectralTranslate t H hH), rawOrderedColumnSelection_eq _ _ hH]
  exact orderedColumnSelection_gaussianSpectralTranslate t ⟨H,hH⟩ _ x

theorem physicalOrderedBlockMass_gaussianSpectralTranslate (p : Parameters) (t : ℝ)
    (H : p.SiteMatrix) (hH : H.IsHermitian) (α : Fin p.N) (k : ZMod p.n) :
    physicalOrderedBlockMass p (gaussianSpectralTranslate t H) α k = physicalOrderedBlockMass p H α k := by
  simp only [physicalOrderedBlockMass, physicalOrderedEigenvector_gaussianSpectralTranslate p t H hH]

theorem physicalProfileGood_gaussianSpectralTranslate (p : Parameters) (t : ℝ)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) :
    physicalProfileGood p (gaussianSpectralTranslate t H) :=
  ⟨isHermitian_gaussianSpectralTranslate t H h.1, separable_gaussianSpectralTranslate t H h.1 h.2⟩

theorem physicalMassSimplex_gaussianSpectralTranslate (p : Parameters) (t : ℝ)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) (α : Fin p.N) :
    physicalMassSimplex p (gaussianSpectralTranslate t H) α = physicalMassSimplex p H α := by
  apply Subtype.ext
  rw [physicalMassSimplex_val_eq p _ (physicalProfileGood_gaussianSpectralTranslate p t H h),
    physicalMassSimplex_val_eq p H h α]
  funext k
  exact physicalOrderedBlockMass_gaussianSpectralTranslate p t H h.1 α k

theorem physicalOrderedProfile_gaussianSpectralTranslate (p : Parameters) (t : ℝ)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) (α : Fin p.N) :
    physicalOrderedProfile p (gaussianSpectralTranslate t H) α = physicalOrderedProfile p H α := by
  rw [← physicalSimplexProfile_physicalMassSimplex p _
    (physicalProfileGood_gaussianSpectralTranslate p t H h),
    physicalMassSimplex_gaussianSpectralTranslate p t H h α, physicalSimplexProfile_physicalMassSimplex p H h α]

/-- Measurability of the matrix shift on all raw matrices and scalar inputs. -/
theorem measurable_gaussianSpectralTranslate (p : Parameters) :
    Measurable (fun z : ℝ × p.SiteMatrix => gaussianSpectralTranslate z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  change Measurable (fun z : ℝ × p.SiteMatrix => z.2 x y + (z.1 : ℂ) * (1 : p.SiteMatrix) x y)
  have hm : Measurable (fun z : ℝ × p.SiteMatrix => z.2 x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd)
  have ht : Measurable (fun z : ℝ × p.SiteMatrix => (z.1 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_fst
  exact hm.add (ht.mul_const ((1 : p.SiteMatrix) x y))

/-- The measurable scalar/background event map. -/
def gaussianSpectralMarkedMap (p : Parameters) (E : ℝ) (z : ℝ × p.SiteMatrix) : MarkedPointMeasure :=
  physicalOrderedMarkedConfig p E (gaussianSpectralTranslate z.1 z.2)

theorem measurable_gaussianSpectralMarkedMap (p : Parameters) (E : ℝ) :
    Measurable (gaussianSpectralMarkedMap p E) :=
  (measurable_physicalOrderedMarkedConfig p E).comp (measurable_gaussianSpectralTranslate p)

/-- Shift only the spectral location of a marked atom. -/
def gaussianMarkedLocationTranslate (s : ℝ) (z : MarkedSpectralSpace) : MarkedSpectralSpace :=
  (z.1 + s, z.2)

theorem measurable_gaussianMarkedLocationTranslate (s : ℝ) :
    Measurable (gaussianMarkedLocationTranslate s) :=
  (measurable_fst.add_const s).prodMk measurable_snd

/-- Exact microscopic location shift, with the torus probability mark unchanged. -/
theorem physicalSpectralDataLocations_gaussianSpectralTranslate (p : Parameters) (E t : ℝ)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) (α : Fin p.N) :
    physicalSpectralDataLocations p E (physicalSpectralData p (gaussianSpectralTranslate t H)) α =
      gaussianMarkedLocationTranslate (p.N * Parameters.semicircleDensity E * t)
        (physicalSpectralDataLocations p E (physicalSpectralData p H) α) := by
  simp only [physicalSpectralDataLocations, physicalSpectralData,
    physicalOrderedEigenvalue_gaussianSpectralTranslate p t H h.1,
    physicalMassSimplex_gaussianSpectralTranslate p t H h, gaussianMarkedLocationTranslate]
  congr 1
  ring

/-- The finite marked configuration obtained by translating each indexed canonical atom. -/
def gaussianTranslatedCanonicalMarkedConfig (p : Parameters) (E s : ℝ) (H : p.SiteMatrix) :
    MarkedPointMeasure :=
  finiteAtomicMarkedPointMeasure (fun α => gaussianMarkedLocationTranslate s
    (physicalSpectralDataLocations p E (physicalSpectralData p H) α))

/-- Exact canonical marked-configuration identity on every Hermitian simple raw matrix. -/
theorem physicalOrderedMarkedConfig_gaussianSpectralTranslate (p : Parameters) (E t : ℝ)
    (H : p.SiteMatrix) (h : physicalProfileGood p H) :
    physicalOrderedMarkedConfig p E (gaussianSpectralTranslate t H) =
      gaussianTranslatedCanonicalMarkedConfig p E (p.N * Parameters.semicircleDensity E * t) H := by
  unfold physicalOrderedMarkedConfig physicalSpectralDataMarkedConfig gaussianTranslatedCanonicalMarkedConfig
  congr 1
  funext α
  exact physicalSpectralDataLocations_gaussianSpectralTranslate p E t H h α

/-- The translated configuration is the pushforward of the canonical marked measure. -/
theorem gaussianTranslatedCanonicalMarkedConfig_measure (p : Parameters) (E s : ℝ)
    (H : p.SiteMatrix) :
    (gaussianTranslatedCanonicalMarkedConfig p E s H).marked.measure =
      Measure.map (gaussianMarkedLocationTranslate s) (physicalOrderedMarkedConfig p E H).marked.measure := by
  change Measure.map (fun α => gaussianMarkedLocationTranslate s
    (physicalSpectralDataLocations p E (physicalSpectralData p H) α)) Measure.count =
      Measure.map (gaussianMarkedLocationTranslate s)
        (Measure.map (physicalSpectralDataLocations p E (physicalSpectralData p H)) Measure.count)
  rw [Measure.map_map (measurable_gaussianMarkedLocationTranslate s) (measurable_of_finite _)]
  rfl

/-- Globally measurable translated canonical configurations through the existing data space. -/
theorem measurable_gaussianTranslatedCanonicalMarkedConfig (p : Parameters) (E s : ℝ) :
    Measurable (gaussianTranslatedCanonicalMarkedConfig p E s) := by
  -- Continuity directly in marked atom locations avoids division at zero density.
  have hc : Continuous (fun data : PhysicalSpectralData p =>
      finiteAtomicMarkedPointMeasure (fun α => gaussianMarkedLocationTranslate s
        (physicalSpectralDataLocations p E data α))) := by
    apply (continuous_finiteAtomicMarkedPointMeasure p.N).comp
    apply continuous_pi
    intro α
    exact (((continuous_apply α).fst.sub continuous_const).const_mul
      (p.N * Parameters.semicircleDensity E) |>.add continuous_const).prodMk
      ((continuous_physicalSimplexProfile p).comp (continuous_apply α).snd)
  exact hc.measurable.comp (measurable_physicalSpectralData p)

/-- Microscopic scalar/background map for the scalar marginal of variance `ρ² c n`. -/
def gaussianMicroscopicSpectralMarkedMap (p : Parameters) (E : ℝ)
    (z : ℝ × p.SiteMatrix) : MarkedPointMeasure :=
  gaussianSpectralMarkedMap p E (z.1 / (p.N * Parameters.semicircleDensity E), z.2)

theorem measurable_gaussianMicroscopicSpectralMarkedMap (p : Parameters) (E : ℝ) :
    Measurable (gaussianMicroscopicSpectralMarkedMap p E) :=
  (measurable_gaussianSpectralMarkedMap p E).comp
    ((measurable_fst.div_const _).prodMk measurable_snd)

/-- The scalar/background map is canonical translation by the microscopic input itself. -/
theorem gaussianMicroscopicSpectralMarkedMap_eq (p : Parameters) (E s : ℝ)
    (hρ : Parameters.semicircleDensity E ≠ 0) (H : p.SiteMatrix)
    (h : physicalProfileGood p H) :
    gaussianMicroscopicSpectralMarkedMap p E (s,H) = gaussianTranslatedCanonicalMarkedConfig p E s H := by
  unfold gaussianMicroscopicSpectralMarkedMap gaussianSpectralMarkedMap
  rw [physicalOrderedMarkedConfig_gaussianSpectralTranslate p E _ H h]
  congr 1
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  field_simp

end BlockBand.Model.Construction
