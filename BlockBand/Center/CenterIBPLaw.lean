module

public import BlockBand.Model.Construction.GaussianSimpleSpectrum
public import BlockBand.Internal.Contracts.Layers

/-!
# Almost-sure band support and invertible bonds of the physical Gaussian law

* `cib_ae_ringBanded`: `H` is supported on the cyclic nearest-neighbour block band
  (`IsRingBanded p H`); off-band coordinates have variance zero and the a.s. active
  reconstruction places zeros there.
* `cib_ae_bonds_det_ne`: every bond block `H_{k,k+1}` (`k : ZMod p.n`) is invertible. The
  determinant of the `(k, k+1)` block of `gaussianUniversalMatrix` is a polynomial in the active
  coordinates, nonzero at the active witness with identity blocks on every bond, hence a.s.
  nonzero (`GaussianRingModel.ae_activePolynomial_ne_zero`); finitely many `k`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped NNReal

/-!
## Variance profile
-/

/-- The band condition of `entryVariance` gives a strictly positive variance. -/
theorem cib_entryVariance_pos {p : Parameters} (x y : p.Site)
    (h : y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) : 0 < p.entryVariance x y := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold Parameters.entryVariance
  split_ifs with h1 h2
  · exact div_pos p.c_pos hW
  · exact div_pos p.b_pos hW
  · exfalso
    rcases h with h | h
    · exact h1 h
    · exact h2 h

/-- Off the band, `entryVariance` vanishes. -/
theorem cib_entryVariance_eq_zero {p : Parameters} (x y : p.Site)
    (h : ¬ (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1)) : p.entryVariance x y = 0 := by
  unfold Parameters.entryVariance
  rw [ite_eq_right (fun h' => h (Or.inl h')), ite_eq_right (fun h' => h (Or.inr h'))]

/-- The band condition is symmetric in the two sites. -/
theorem cib_band_symm {p : Parameters} (x y : p.Site) :
    (y.1 = x.1 ∨ y.1 = x.1 + 1 ∨ y.1 = x.1 - 1) ↔
      (x.1 = y.1 ∨ x.1 = y.1 + 1 ∨ x.1 = y.1 - 1) := by
  constructor
  · rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (eq_sub_iff_add_eq.mpr h.symm))
    · exact Or.inr (Or.inl (sub_eq_iff_eq_add.mp h.symm))
  · rintro (h | h | h)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (eq_sub_iff_add_eq.mpr h.symm))
    · exact Or.inr (Or.inl (sub_eq_iff_eq_add.mp h.symm))

/-- An off-diagonal coordinate label whose complex entry has zero variance is inactive. -/
theorem cib_coordinateVariance_inr_eq_zero {p : Parameters} (x y : p.Site) (bb : Bool)
    (h : p.entryVariance x y = 0) : p.gaussianCoordinateVariance (.inr (x, y, bb)) = 0 := by
  rw [← NNReal.coe_eq_zero]
  by_cases hlt : p.siteIndex x < p.siteIndex y
  · simp only [Parameters.gaussianCoordinateVariance, hlt, h, zero_div]
    rfl
  · simp [Parameters.gaussianCoordinateVariance, hlt]

/-- A strict-upper coordinate label of a positive-variance entry is active. -/
theorem cib_coordinateVariance_inr_ne_zero {p : Parameters} (x y : p.Site) (bb : Bool)
    (hlt : p.siteIndex x < p.siteIndex y) (hpos : 0 < p.entryVariance x y) :
    p.gaussianCoordinateVariance (.inr (x, y, bb)) ≠ 0 := by
  have hv : (p.gaussianCoordinateVariance (.inr (x, y, bb)) : ℝ) = p.entryVariance x y / 2 := by
    simp [Parameters.gaussianCoordinateVariance, hlt]
    rfl
  intro h
  rw [h, NNReal.coe_zero] at hv
  linarith

/-- The active value of an inactive label is zero. -/
theorem cib_activeValue_inactive {p : Parameters} (z : p.GaussianActiveCoordinate → ℝ)
    (i : p.GaussianCoordinate) (h : p.gaussianCoordinateVariance i = 0) :
    p.gaussianActiveValue z i = 0 := by
  unfold Parameters.gaussianActiveValue
  rw [dite_eq_right (not_not.mpr h)]

/-!
## Ring-banded support
-/

/-- Every active reconstruction vanishes off the cyclic block band. -/
theorem cib_activeReconstruction_ringBanded {p : Parameters}
    (z : p.GaussianActiveCoordinate → ℝ) : IsRingBanded p (p.gaussianActiveReconstruction z) := by
  intro x y hxy
  have hxy' : ¬ (x.1 = y.1 ∨ x.1 = y.1 + 1 ∨ x.1 = y.1 - 1) := fun h =>
    hxy ((cib_band_symm x y).mpr h)
  have hne : x ≠ y := fun h => hxy (Or.inl (congrArg Prod.fst h).symm)
  have h1 : p.entryVariance x y = 0 := cib_entryVariance_eq_zero x y hxy
  have h2 : p.entryVariance y x = 0 := cib_entryVariance_eq_zero y x hxy'
  unfold Parameters.gaussianActiveReconstruction Parameters.gaussianReconstruction
  rw [ite_eq_right hne]
  split_ifs
  · rw [cib_activeValue_inactive z _ (cib_coordinateVariance_inr_eq_zero x y false h1),
      cib_activeValue_inactive z _ (cib_coordinateVariance_inr_eq_zero x y true h1)]
    simp
  · rw [cib_activeValue_inactive z _ (cib_coordinateVariance_inr_eq_zero y x false h2),
      cib_activeValue_inactive z _ (cib_coordinateVariance_inr_eq_zero y x true h2)]
    simp

/-- **Almost-sure band support.** Under the exact physical law, `H_xy = 0` unless the blocks
of `x` and `y` are equal or adjacent on the ring. -/
theorem cib_ae_ringBanded {p : Parameters} (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), IsRingBanded p H := by
  filter_upwards [model.ae_gaussianActiveReconstruction_eq] with H hH
  rw [← hH]
  exact cib_activeReconstruction_ringBanded _

/-!
## Invertible bonds
-/

/-- The bond-block determinant polynomial in the active coordinates. -/
def cibBondPolynomial (p : Parameters) (k : ZMod p.n) :
    MvPolynomial p.GaussianActiveCoordinate ℂ :=
  (Matrix.of fun a b : Fin p.W => p.gaussianUniversalMatrix (k, a) (k + 1, b)).det

/-- Evaluation of the bond polynomial is the bond determinant of the active reconstruction. -/
theorem cib_bondPolynomial_eval {p : Parameters} (k : ZMod p.n)
    (z : p.GaussianActiveCoordinate → ℝ) :
    MvPolynomial.eval (fun j => (z j : ℂ)) (cibBondPolynomial p k) =
      (Matrix.of fun a b : Fin p.W => p.gaussianActiveReconstruction z (k, a) (k + 1, b)).det := by
  rw [cibBondPolynomial, RingHom.map_det, ← p.gaussianUniversalMatrix_map_eval z]
  congr 1

/-- In the ring `ZMod n` with `n ≥ 4`, `k + 1 ≠ k`. -/
theorem cib_succ_ne {p : Parameters} (k : ZMod p.n) : k + 1 ≠ k := by
  have : Fact (1 < p.n) := ⟨by have := p.n_ge_four; omega⟩
  intro h
  have h1 : (1 : ZMod p.n) = 0 := by
    have := congrArg (fun t => t - k) h
    simp at this
  exact one_ne_zero h1

/-- Coordinate witness: real part `1` on every bond label pairing `(k, a)` with `(k + 1, a)`,
zero on every other label. -/
def cibBondWitnessFull (p : Parameters) : p.GaussianCoordinate → ℝ
  | .inl _ => 0
  | .inr (x, y, bb) =>
      if bb = false ∧ x.2 = y.2 ∧ (y.1 = x.1 + 1 ∨ x.1 = y.1 + 1) then 1 else 0

/-- The active witness. -/
def cibBondWitness (p : Parameters) : p.GaussianActiveCoordinate → ℝ :=
  fun i => cibBondWitnessFull p i.1

theorem cib_activeValue_witness_active {p : Parameters} (i : p.GaussianCoordinate)
    (h : p.gaussianCoordinateVariance i ≠ 0) :
    p.gaussianActiveValue (cibBondWitness p) i = cibBondWitnessFull p i := by
  unfold Parameters.gaussianActiveValue
  rw [dite_eq_left h]
  rfl

theorem cib_activeValue_witness_true {p : Parameters} (x y : p.Site) :
    p.gaussianActiveValue (cibBondWitness p) (.inr (x, y, true)) = 0 := by
  unfold Parameters.gaussianActiveValue
  split_ifs
  · simp [cibBondWitness, cibBondWitnessFull]
  · rfl

/-- The bond blocks of the witness reconstruction are identity matrices. -/
theorem cib_witness_bond_entry {p : Parameters} (k : ZMod p.n) (a b : Fin p.W) :
    p.gaussianActiveReconstruction (cibBondWitness p) (k, a) (k + 1, b) =
      if a = b then 1 else 0 := by
  have hne : ((k, a) : p.Site) ≠ (k + 1, b) := fun h =>
    cib_succ_ne k (congrArg Prod.fst h).symm
  have hband : (k + 1 = k ∨ k + 1 = k + 1 ∨ k + 1 = k - 1) := Or.inr (Or.inl rfl)
  have hband' : (k = k + 1 ∨ k = k + 1 + 1 ∨ k = k + 1 - 1) := Or.inr (Or.inr (by ring))
  unfold Parameters.gaussianActiveReconstruction Parameters.gaussianReconstruction
  rw [ite_eq_right hne]
  by_cases hlt : p.siteIndex ((k, a) : p.Site) < p.siteIndex (k + 1, b)
  · rw [ite_eq_left hlt, cib_activeValue_witness_active _ (cib_coordinateVariance_inr_ne_zero _ _ false hlt
        (cib_entryVariance_pos _ _ hband)), cib_activeValue_witness_true]
    by_cases hab : a = b
    · subst hab
      simp [cibBondWitnessFull]
    · simp [cibBondWitnessFull, hab]
  · have hlt' : p.siteIndex (k + 1, b) < p.siteIndex (k, a) := by
      have hne' : p.siteIndex (k, a) ≠ p.siteIndex (k + 1, b) := fun h =>
        hne (p.siteIndex_injective h)
      omega
    rw [ite_eq_right hlt, cib_activeValue_witness_active _ (cib_coordinateVariance_inr_ne_zero _ _ false hlt'
        (cib_entryVariance_pos _ _ hband')), cib_activeValue_witness_true]
    by_cases hab : a = b
    · subst hab
      simp [cibBondWitnessFull]
    · simp [cibBondWitnessFull, hab, Ne.symm hab]

/-- The witness has nonzero bond polynomial for every `k`. -/
theorem cib_bondPolynomial_witness_ne_zero {p : Parameters} (k : ZMod p.n) :
    MvPolynomial.eval (fun j => (cibBondWitness p j : ℂ)) (cibBondPolynomial p k) ≠ 0 := by
  rw [cib_bondPolynomial_eval]
  have h1 : (Matrix.of fun a b : Fin p.W =>
      p.gaussianActiveReconstruction (cibBondWitness p) (k, a) (k + 1, b)) = 1 := by
    ext a b
    rw [Matrix.of_apply, cib_witness_bond_entry, Matrix.one_apply]
  rw [h1, Matrix.det_one]
  exact one_ne_zero

/-- **Almost-sure invertible bonds.** Under the exact physical law, every bond block
`H_{k,k+1}` of the ring is invertible. -/
theorem cib_ae_bonds_det_ne {p : Parameters} (model : p.GaussianRingModel) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ k : ZMod p.n,
      (Matrix.of fun a b : Fin p.W => H (k, a) (k + 1, b)).det ≠ 0 := by
  have hall : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∀ k : ZMod p.n,
      MvPolynomial.eval (fun i => (p.gaussianActiveExtraction H i : ℂ))
        (cibBondPolynomial p k) ≠ 0 :=
    ae_all_iff.mpr fun k =>
      model.ae_activePolynomial_ne_zero _ _ (cib_bondPolynomial_witness_ne_zero k)
  filter_upwards [hall, model.ae_gaussianActiveReconstruction_eq] with H hpoly hrec k
  have h := hpoly k
  rwa [cib_bondPolynomial_eval, hrec] at h

end BlockBand.Center
