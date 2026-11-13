module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.GUEStationarity
public import BlockBand.Native.CEH.ETH.BlockBand.Published.FixedEnergySineInput
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Matrix-law adapter for the concrete CEH GUE flow

This module pushes the coordinate-product identities of `GUEStationarity` through the measurable
Hermitian reconstruction and identifies the resulting full-matrix law with the normalized GUE law
`normalizedHermitianGUEMatrixLaw` of the fixed-energy interface. The variance parameter is
displayed exactly as `s/N`; no coordinatewise or moment-only surrogate is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open MeasureTheory ProbabilityTheory
open CEHNative.BlockBand

/-- The zero Hermitian matrix. -/
def zeroHermitianMatrix (N : ℕ) : HermitianMatrix (Fin N) :=
  ⟨0, by simp⟩

/-- The concrete normalized Hermitian GUE matrix law of the fixed-energy interface, with
deterministic deformation zero. -/
def normalizedHermitianGUEMatrixLaw (N : ℕ) (s : ℝ) :
    ProbabilityMeasure (HermitianMatrix (Fin N)) :=
  fixedEnergyDeformedGUELaw N (zeroHermitianMatrix N) s

/-- Measurable reconstruction carries the coordinate-level rotation identity
to equality of the complete Hermitian matrix pushforward laws. -/
theorem gueMixBlock_map_eq_hermitianGUEBlock_map
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) :
    Measure.map (gueMixBlock d a b) (guePairMeasure d t ht) =
      Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht) := by
  rw [← gueMix_map_eq_gue d t ht hab]
  rw [Measure.map_map (measurable_hermitianGUEBlock d)
    (measurable_gueMix a b)]
  rfl

/-- Exact full-matrix OU stationarity before specializing the normalized
variance. -/
theorem gueOUBlock_map_eq_hermitianGUEBlock_map
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) {u : ℝ} (hu : 0 ≤ u) :
    Measure.map (gueMixBlock d (ouDecay u) (ouNoise u))
        (guePairMeasure d t ht) =
      Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht) :=
  gueMixBlock_map_eq_hermitianGUEBlock_map d t ht
    (ou_coefficients_unit hu)

/-- For nonnegative `s`, the normalized matrix law unfolds to reconstruction from the
coordinate product of exact variance `s/N`. -/
theorem normalizedHermitianGUEMatrixLaw_eq_reconstruction
    (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (normalizedHermitianGUEMatrixLaw N s :
      Measure (HermitianMatrix (Fin N))) =
      Measure.map (hermitianGUEBlock N)
        (hermitianGUECoordinateMeasure N (s / (N : ℝ))
          (by positivity)) := by
  unfold normalizedHermitianGUEMatrixLaw fixedEnergyDeformedGUELaw
  change Measure.map
      (fixedEnergyDeformedGUEMap N (zeroHermitianMatrix N))
      (hermitianGUECoordinateMeasure N (max 0 (s / (N : ℝ))) _) =
    Measure.map (hermitianGUEBlock N)
      (hermitianGUECoordinateMeasure N (s / (N : ℝ)) _)
  simp only [max_eq_right
    (show (0 : ℝ) ≤ s / (N : ℝ) by positivity)]
  apply Measure.map_congr
  filter_upwards with x
  apply Subtype.ext
  simp [fixedEnergyDeformedGUEMap, hermitianMatrixAdd, zeroHermitianMatrix]

/-- Exact `s/N` full-matrix stationarity, identified with the normalized Hermitian GUE matrix
law. -/
theorem gueOUBlock_map_eq_normalizedHermitianGUEMatrixLaw
    (N : ℕ) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    Measure.map (gueMixBlock N (ouDecay u) (ouNoise u))
        (guePairMeasure N (s / (N : ℝ))
          (by positivity)) =
      (normalizedHermitianGUEMatrixLaw N s :
        Measure (HermitianMatrix (Fin N))) := by
  rw [gueOUBlock_map_eq_hermitianGUEBlock_map N
    (s / (N : ℝ)) (by positivity) hu]
  exact (normalizedHermitianGUEMatrixLaw_eq_reconstruction N hs).symm

/-- A two-element family formed from independent random variables is mutually
independent.  This small bridge is used to flatten the independent coordinate
pairs in `guePairMeasure`. -/
theorem iIndepFun_fin_two_of_indepFun
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXY : IndepFun X Y μ) :
    iIndepFun (fun i : Fin 2 => if i = 0 then X else Y) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have hS : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
    fin_cases S <;> simp [Finset.ext_iff]
  rcases hS with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simpa using hXY.measure_inter_preimage_eq_mul
      (sets 0) (sets 1) (hsets 0 (by simp)) (hsets 1 (by simp))

/-- All scalar entries of both coordinate fields, indexed by
`coordinate × copy`, form one mutually independent family. -/
theorem iIndepFun_guePairScalarCoordinates
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    iIndepFun
      (fun p : Fin (Fintype.card (HermitianCoordinate d)) × Fin 2 =>
        fun x : GUEPairSample d =>
          if p.2 = 0 then (x p.1).1 else (x p.1).2)
      (guePairMeasure d t ht) := by
  refine iIndepFun_uncurry'
    (P := guePairMeasure d t ht)
    (X := fun k (j : Fin 2) (x : GUEPairSample d) =>
      if j = 0 then (x k).1 else (x k).2) ?_ ?_ ?_
  · intro k j
    split_ifs <;> fun_prop
  · exact (iIndepFun_guePairCoordinates d t ht).comp
      (fun _ p j => if j = 0 then p.1 else p.2) (fun k => by
        rw [measurable_pi_iff]
        intro j
        split_ifs <;> fun_prop)
  · intro k
    apply (iIndepFun_fin_two_of_indepFun
      (indepFun_guePairCoordinate_under_pairMeasure d t ht k)).congr
    intro j
    filter_upwards with x
    split_ifs <;> rfl

/-- The two complete coordinate fields are independent under the explicit
paired product law. -/
theorem indepFun_guePairFirst_guePairSecond
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IndepFun (@guePairFirst d) (@guePairSecond d)
      (guePairMeasure d t ht) := by
  let scalar :
      (Fin (Fintype.card (HermitianCoordinate d)) × Fin 2) →
        GUEPairSample d → ℝ :=
    fun p x => if p.2 = 0 then (x p.1).1 else (x p.1).2
  have hscalar : iIndepFun scalar (guePairMeasure d t ht) := by
    exact iIndepFun_guePairScalarCoordinates d t ht
  let S : Finset (Fin (Fintype.card (HermitianCoordinate d)) × Fin 2) :=
    Finset.univ.filter (fun p => p.2 = 0)
  let T : Finset (Fin (Fintype.card (HermitianCoordinate d)) × Fin 2) :=
    Finset.univ.filter (fun p => p.2 = 1)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro p hpS hpT
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hpS hpT
    omega
  have hgroups := hscalar.indepFun_finset S T hST (fun p => by
    unfold scalar
    split_ifs <;> fun_prop)
  -- Reindex each selected family by the underlying Hermitian coordinate.
  have hcomp := hgroups.comp
    (φ := fun (z : S → ℝ) k => z ⟨(k, 0), by simp [S]⟩)
    (ψ := fun (z : T → ℝ) k => z ⟨(k, 1), by simp [T]⟩)
    (by
      rw [measurable_pi_iff]
      intro k
      exact measurable_pi_apply _)
    (by
      rw [measurable_pi_iff]
      intro k
      exact measurable_pi_apply _)
  convert hcomp using 1 <;> ext x k <;>
    simp [Function.comp_apply, scalar, S, T, guePairFirst, guePairSecond]

/-- The first reconstructed Hermitian GUE matrix. -/
def guePairFirstBlock {d : ℕ} (x : GUEPairSample d) :
    HermitianMatrix (Fin d) :=
  hermitianGUEBlock d (guePairFirst x)

/-- The second reconstructed Hermitian GUE matrix. -/
def guePairSecondBlock {d : ℕ} (x : GUEPairSample d) :
    HermitianMatrix (Fin d) :=
  hermitianGUEBlock d (guePairSecond x)

/-- Both full-matrix reconstruction maps are measurable. -/
theorem measurable_guePairFirstBlock {d : ℕ} :
    Measurable (@guePairFirstBlock d) :=
  (measurable_hermitianGUEBlock d).comp measurable_guePairFirst

/-- Measurability of the second full-matrix reconstruction. -/
theorem measurable_guePairSecondBlock {d : ℕ} :
    Measurable (@guePairSecondBlock d) :=
  (measurable_hermitianGUEBlock d).comp measurable_guePairSecond

/-- **Product independence at full-matrix level.**  The two reconstructed
Hermitian GUE matrices are independent, not merely their individual entries. -/
theorem indepFun_guePairFirstBlock_guePairSecondBlock
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    IndepFun (@guePairFirstBlock d) (@guePairSecondBlock d)
      (guePairMeasure d t ht) :=
  (indepFun_guePairFirst_guePairSecond d t ht).comp
    (measurable_hermitianGUEBlock d)
    (measurable_hermitianGUEBlock d)

/-- Each reconstructed marginal has the complete Hermitian-matrix pushforward
of the concrete coordinate GUE law. -/
theorem guePairFirstBlock_map_eq_hermitianGUEBlock_map
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (@guePairFirstBlock d) (guePairMeasure d t ht) =
      Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht) := by
  rw [← guePairFirst_map_eq_gue d t ht]
  rw [Measure.map_map (measurable_hermitianGUEBlock d)
    measurable_guePairFirst]
  rfl

/-- The second reconstructed marginal has the same complete matrix law. -/
theorem guePairSecondBlock_map_eq_hermitianGUEBlock_map
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (@guePairSecondBlock d) (guePairMeasure d t ht) =
      Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht) := by
  rw [← guePairSecond_map_eq_gue d t ht]
  rw [Measure.map_map (measurable_hermitianGUEBlock d)
    measurable_guePairSecond]
  rfl

/-- The joint pushforward of the two reconstructed matrices is exactly the
product of their complete Hermitian GUE matrix laws. -/
theorem guePairBlocks_joint_map_eq_prod
    (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map
        (fun x : GUEPairSample d =>
          (guePairFirstBlock x, guePairSecondBlock x))
        (guePairMeasure d t ht) =
      (Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht)).prod
      (Measure.map (hermitianGUEBlock d)
        (hermitianGUECoordinateMeasure d t ht)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    measurable_guePairFirstBlock.aemeasurable
    measurable_guePairSecondBlock.aemeasurable).mp
      (indepFun_guePairFirstBlock_guePairSecondBlock d t ht)]
  rw [guePairFirstBlock_map_eq_hermitianGUEBlock_map,
    guePairSecondBlock_map_eq_hermitianGUEBlock_map]

/-- At exact variance `s/N`, the joint full-matrix law is the product of two
copies of the normalized Hermitian GUE law. -/
theorem guePairBlocks_joint_map_eq_normalized_prod
    (N : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Measure.map
        (fun x : GUEPairSample N =>
          (guePairFirstBlock x, guePairSecondBlock x))
        (guePairMeasure N (s / (N : ℝ)) (by positivity)) =
      (normalizedHermitianGUEMatrixLaw N s :
        Measure (HermitianMatrix (Fin N))).prod
      (normalizedHermitianGUEMatrixLaw N s :
        Measure (HermitianMatrix (Fin N))) := by
  rw [guePairBlocks_joint_map_eq_prod N (s / (N : ℝ)) (by positivity)]
  rw [← normalizedHermitianGUEMatrixLaw_eq_reconstruction N hs]

/-- Deterministic translation on Hermitian matrices. -/
def translateHermitianMatrix {N : ℕ} (F : HermitianMatrix (Fin N))
    (G : HermitianMatrix (Fin N)) : HermitianMatrix (Fin N) :=
  hermitianMatrixAdd F G

/-- Deterministic Hermitian translation is measurable. -/
theorem measurable_translateHermitianMatrix {N : ℕ}
    (F : HermitianMatrix (Fin N)) :
    Measurable (translateHermitianMatrix F) := by
  apply Measurable.subtype_mk
  apply Measurable.of_eval_matrix
  intro i j
  exact measurable_const.add
    (measurable_subtype_coe.eval_matrix)

/-- The deterministic-deformation reconstruction map of the fixed-energy interface is measurable. -/
theorem measurable_fixedEnergyDeformedGUEMap
    (N : ℕ) (F : HermitianMatrix (Fin N)) :
    Measurable (fixedEnergyDeformedGUEMap N F) := by
  exact (measurable_translateHermitianMatrix F).comp
    (measurable_hermitianGUEBlock N)

/-- The deformed law of the fixed-energy interface is exactly deterministic translation of the
zero-deformation normalized matrix law. -/
theorem fixedEnergyDeformedGUELaw_eq_map_normalized
    (N : ℕ) (F : HermitianMatrix (Fin N)) (s : ℝ) :
    (fixedEnergyDeformedGUELaw N F s :
      Measure (HermitianMatrix (Fin N))) =
      Measure.map (translateHermitianMatrix F)
        (normalizedHermitianGUEMatrixLaw N s :
          Measure (HermitianMatrix (Fin N))) := by
  unfold normalizedHermitianGUEMatrixLaw fixedEnergyDeformedGUELaw
  change Measure.map (fixedEnergyDeformedGUEMap N F)
      (hermitianGUECoordinateMeasure N (max 0 (s / (N : ℝ))) _) =
    Measure.map (translateHermitianMatrix F)
      (Measure.map
        (fixedEnergyDeformedGUEMap N (zeroHermitianMatrix N))
        (hermitianGUECoordinateMeasure N (max 0 (s / (N : ℝ))) _))
  rw [Measure.map_map (measurable_translateHermitianMatrix F)]
  · apply Measure.map_congr
    filter_upwards with x
    apply Subtype.ext
    simp [translateHermitianMatrix, fixedEnergyDeformedGUEMap,
      hermitianMatrixAdd, zeroHermitianMatrix]
  · exact measurable_fixedEnergyDeformedGUEMap N (zeroHermitianMatrix N)

/-- The stationary OU mixture followed by deterministic Hermitian translation
has exactly the deformed matrix law `F + GUE_N(s/N)` of the fixed-energy interface. -/
theorem translatedGueOUBlock_map_eq_fixedEnergyDeformedGUELaw
    (N : ℕ) (F : HermitianMatrix (Fin N)) {s u : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) :
    Measure.map
        (fun x : GUEPairSample N =>
          translateHermitianMatrix F
            (gueMixBlock N (ouDecay u) (ouNoise u) x))
        (guePairMeasure N (s / (N : ℝ)) (by positivity)) =
      (fixedEnergyDeformedGUELaw N F s :
        Measure (HermitianMatrix (Fin N))) := by
  change Measure.map
      (translateHermitianMatrix F ∘
        gueMixBlock N (ouDecay u) (ouNoise u))
      (guePairMeasure N (s / (N : ℝ)) _) = _
  rw [← Measure.map_map (measurable_translateHermitianMatrix F)
    (measurable_gueMixBlock N (ouDecay u) (ouNoise u))]
  rw [gueOUBlock_map_eq_normalizedHermitianGUEMatrixLaw N hs hu]
  exact (fixedEnergyDeformedGUELaw_eq_map_normalized N F s).symm

end CEHNative.BlockBand.CEH
