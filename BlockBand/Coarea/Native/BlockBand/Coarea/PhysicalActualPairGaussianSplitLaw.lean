module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGaussianSplitComplete
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalBlockConditioningReconstruction

/-!
# The adjacent-pair split law

The pair coordinates and the exterior state of a `GaussianRing.Law` are independent, with the
physical adjacent-pair law and the exterior law; the residual-plus-fresh split readback has the
same product law. This proves `Law.actualPairGaussianSplitInput` and the unconditional
transfer `Law.lintegral_actualPairExterior_eq_physicalSplit_unconditional`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace GaussianRing
local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The ordered physical upper-pair label underlying two arbitrary sites. -/
def physicalUpperPair (p : Params) (x y : Site p.n p.W) : UpperPair p :=
  if h : siteLE p x y then ⟨(x, y), h⟩
  else ⟨(y, x), siteLE_of_not_siteLE h⟩

/-- The adjacent two-block site inclusion is injective. -/
theorem adjacentPairSite_injective (p : Params) (j : ZMod p.n) :
    Function.Injective (adjacentPairSite p j) := by
  intro a b hab
  let _ : Fact (1 < p.n) := ⟨lt_of_lt_of_le (by omega) p.n_ge_four⟩
  have hone : (1 : ZMod p.n) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    simp [ZMod.val_one] at hv
  have hj : j ≠ j + 1 := by
    intro h
    apply hone
    exact add_left_cancel (by simpa only [add_zero] using h.symm)
  let a' : Fin (p.W + p.W) := Fin.cast (by omega) a
  let b' : Fin (p.W + p.W) := Fin.cast (by omega) b
  let inc : Fin (p.W + p.W) → Site p.n p.W :=
    Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v))
  change inc a' = inc b' at hab
  have hv : a'.val = b'.val := by
    revert hab
    refine Fin.addCases (fun u => ?_) (fun u => ?_) a'
    · refine Fin.addCases (fun v h => ?_) (fun v h => ?_) b'
      · dsimp [inc] at h
        rw [Fin.addCases_left, Fin.addCases_left] at h
        change (j, u) = (j, v) at h
        exact congrArg Fin.val (by simpa using congrArg Prod.snd h)
      · dsimp [inc] at h
        rw [Fin.addCases_left, Fin.addCases_right] at h
        change (j, u) = (j + 1, v) at h
        exfalso
        exact hj (by simpa using congrArg Prod.fst h)
    · refine Fin.addCases (fun v h => ?_) (fun v h => ?_) b'
      · dsimp [inc] at h
        rw [Fin.addCases_right, Fin.addCases_left] at h
        change (j + 1, u) = (j, v) at h
        exfalso
        exact hj (by simpa using (congrArg Prod.fst h).symm)
      · dsimp [inc] at h
        rw [Fin.addCases_right, Fin.addCases_right] at h
        change (j + 1, u) = (j + 1, v) at h
        have huv : u = v := by simpa using congrArg Prod.snd h
        subst v
        rfl
  apply Fin.ext
  exact hv

/-- The forward bond block weight is exactly `b`. -/
theorem blockWeight_forward (p : Params) (j : ZMod p.n) :
    blockWeight p j (j + 1) = p.b := by
  have h10 : j + 1 ≠ j := by
    intro h
    have hz : (1 : ZMod p.n) = 0 := by
      calc 1 = (j + 1) - j := by ring
           _ = 0 := by rw [h]; ring
    have hn : p.n = 1 := ZMod.one_eq_zero_iff.mp hz
    have h4 := p.n_ge_four
    omega
  have h2 : j + 1 ≠ j - 1 := by
    intro h
    have hz : (2 : ZMod p.n) = 0 := by
      calc 2 = (j + 1) - (j - 1) := by ring
           _ = 0 := by rw [h]; ring
    have hd : p.n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p.n).mp hz
    have hle : p.n ≤ 2 := Nat.le_of_dvd (by omega) hd
    have h4 := p.n_ge_four
    omega
  simp [blockWeight, h10, h2]

/-- Total complex variance of an entry in the adjacent pair, expressed
only in terms of whether its two local indices lie in the same physical block. -/
theorem varianceNNReal_adjacentPair (p : Params) (j : ZMod p.n)
    (a b : Fin (2 * p.W)) :
    varianceNNReal p (adjacentPairSite p j a) (adjacentPairSite p j b) =
      if (a.val < p.W) = (b.val < p.W) then
        ⟨p.diagonalVariance, p.diagonalVariance_pos.le⟩
      else ⟨p.bondVariance, p.bondVariance_pos.le⟩ := by
  let a' : Fin (p.W + p.W) := Fin.cast (by omega) a
  let b' : Fin (p.W + p.W) := Fin.cast (by omega) b
  generalize ha : a' = aa
  generalize hb : b' = bb
  revert ha hb
  refine Fin.addCases (fun u ha => ?_) (fun u ha => ?_) aa
  · have hsa : adjacentPairSite p j a = (j, u) := by
      simp [adjacentPairSite, a', ha]
    have hva : a.val = u.val := by
      have := congrArg Fin.val ha
      dsimp [a'] at this
      omega
    refine Fin.addCases (fun v hb => ?_) (fun v hb => ?_) bb
    · have hsb : adjacentPairSite p j b = (j, v) := by
        simp [adjacentPairSite, b', hb]
      have hvb : b.val = v.val := by
        have := congrArg Fin.val hb
        dsimp [b'] at this
        omega
      apply NNReal.eq
      rw [hsa, hsb]
      simp [varianceNNReal, varianceProfile, hva, hvb,
        blockWeight_self, Params.diagonalVariance,
        Conventions.diagonalEntryVariance]
    · have hsb : adjacentPairSite p j b = (j + 1, v) := by
        unfold adjacentPairSite
        rw [show Fin.cast (by omega) b = Fin.natAdd p.W v by simpa [b'] using hb]
        rw [Fin.addCases_right]
      have hvb : b.val = p.W + v.val := by
        have := congrArg Fin.val hb
        dsimp [b'] at this
        omega
      apply NNReal.eq
      rw [hsa, hsb]
      simp [varianceNNReal, varianceProfile, hva, hvb,
        blockWeight_forward, Params.bondVariance,
        Conventions.bondEntryVariance]
  · have hsa : adjacentPairSite p j a = (j + 1, u) := by
      unfold adjacentPairSite
      rw [show Fin.cast (by omega) a = Fin.natAdd p.W u by simpa [a'] using ha]
      rw [Fin.addCases_right]
    have hva : a.val = p.W + u.val := by
      have := congrArg Fin.val ha
      dsimp [a'] at this
      omega
    refine Fin.addCases (fun v hb => ?_) (fun v hb => ?_) bb
    · have hsb : adjacentPairSite p j b = (j, v) := by
        simp [adjacentPairSite, b', hb]
      have hvb : b.val = v.val := by
        have := congrArg Fin.val hb
        dsimp [b'] at this
        omega
      apply NNReal.eq
      rw [hsa, hsb]
      change varianceProfile p (j + 1, u) (j, v) = _
      rw [varianceProfile_comm]
      simp [varianceNNReal, varianceProfile, hva, hvb,
        blockWeight_forward, Params.bondVariance,
        Conventions.bondEntryVariance]
      rfl
    · have hsb : adjacentPairSite p j b = (j + 1, v) := by
        unfold adjacentPairSite
        rw [show Fin.cast (by omega) b = Fin.natAdd p.W v by simpa [b'] using hb]
        rw [Fin.addCases_right]
      have hvb : b.val = p.W + v.val := by
        have := congrArg Fin.val hb
        dsimp [b'] at this
        omega
      apply NNReal.eq
      rw [hsa, hsb]
      simp [varianceNNReal, varianceProfile, hva, hvb,
        blockWeight_self, Params.diagonalVariance,
        Conventions.diagonalEntryVariance]

/-- Equality of globally ordered upper-pair labels remembers the underlying
unordered pair of sites. -/
theorem physicalUpperPair_eq_iff (p : Params)
    (x y x' y' : Site p.n p.W) :
    physicalUpperPair p x y = physicalUpperPair p x' y' →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  intro h
  by_cases hxy : siteLE p x y <;> by_cases hxy' : siteLE p x' y'
  · left
    simpa [physicalUpperPair, hxy, hxy'] using congrArg Subtype.val h
  · right
    simpa [physicalUpperPair, hxy, hxy'] using congrArg Subtype.val h
  · right
    have hh := congrArg Subtype.val h
    have : (y, x) = (x', y') := by simpa [physicalUpperPair, hxy, hxy'] using hh
    exact ⟨congrArg Prod.snd this, congrArg Prod.fst this⟩
  · left
    have hh := congrArg Subtype.val h
    have : (y, x) = (y', x') := by simpa [physicalUpperPair, hxy, hxy'] using hh
    exact ⟨congrArg Prod.snd this, congrArg Prod.fst this⟩

/-- Global physical real-coordinate label represented by one local adjacent-pair
Hermitian coordinate.  The global upper-triangle orientation is selected by
`physicalUpperPair`. -/
def adjacentPairPhysicalCoordinate (p : Params) (j : ZMod p.n)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    PhysicalRealCoordinate p :=
  match (hermitianCoordinateEquivFin (2 * p.W)).symm k with
  | .inl a =>
      (physicalUpperPair p (adjacentPairSite p j a) (adjacentPairSite p j a), false)
  | .inr (.inl ab) =>
      (physicalUpperPair p (adjacentPairSite p j ab.1.1)
        (adjacentPairSite p j ab.1.2), false)
  | .inr (.inr ab) =>
      (physicalUpperPair p (adjacentPairSite p j ab.1.1)
        (adjacentPairSite p j ab.1.2), true)

/-- Distinct local Hermitian coordinates use distinct global physical
real-coordinate labels. -/
theorem adjacentPairPhysicalCoordinate_injective (p : Params) (j : ZMod p.n) :
    Function.Injective (adjacentPairPhysicalCoordinate p j) := by
  intro k l h
  apply (hermitianCoordinateEquivFin (2 * p.W)).symm.injective
  generalize hk : (hermitianCoordinateEquivFin (2 * p.W)).symm k = c at h ⊢
  generalize hl : (hermitianCoordinateEquivFin (2 * p.W)).symm l = d at h ⊢
  simp only [adjacentPairPhysicalCoordinate, hk, hl] at h
  rcases c with a | c <;> rcases d with b | d
  · have hu := physicalUpperPair_eq_iff p
      (adjacentPairSite p j a) (adjacentPairSite p j a)
      (adjacentPairSite p j b) (adjacentPairSite p j b)
      (congrArg Prod.fst h)
    rcases hu with hu | hu
    · have : a = b := adjacentPairSite_injective p j hu.1
      subst b
      rfl
    · have : a = b := adjacentPairSite_injective p j hu.1
      subst b
      rfl
  · rcases d with bd | bd
    · have hu := physicalUpperPair_eq_iff p
        (adjacentPairSite p j a) (adjacentPairSite p j a)
        (adjacentPairSite p j bd.1.1) (adjacentPairSite p j bd.1.2)
        (congrArg Prod.fst h)
      rcases hu with hu | hu
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        exfalso
        exact bd.2.ne (h1.symm.trans h2)
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        exfalso
        exact bd.2.ne (h2.symm.trans h1)
    · exfalso
      simpa using congrArg Prod.snd h
  · rcases c with ac | ac
    · have hu := physicalUpperPair_eq_iff p
        (adjacentPairSite p j ac.1.1) (adjacentPairSite p j ac.1.2)
        (adjacentPairSite p j b) (adjacentPairSite p j b)
        (congrArg Prod.fst h)
      rcases hu with hu | hu
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        exfalso
        exact ac.2.ne (h1.trans h2.symm)
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        exfalso
        exact ac.2.ne (h2.trans h1.symm).symm
    · exfalso
      simpa using congrArg Prod.snd h
  · rcases c with ac | ac <;> rcases d with bd | bd
    · have hu := physicalUpperPair_eq_iff p
        (adjacentPairSite p j ac.1.1) (adjacentPairSite p j ac.1.2)
        (adjacentPairSite p j bd.1.1) (adjacentPairSite p j bd.1.2)
        (congrArg Prod.fst h)
      rcases hu with hu | hu
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        have hab : ac = bd := Subtype.ext (Prod.ext h1 h2)
        subst bd
        rfl
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        have : ac.1.1 < ac.1.2 := ac.2
        have : ac.1.2 < ac.1.1 := by simpa [h1, h2] using bd.2
        omega
    · exfalso
      simpa using congrArg Prod.snd h
    · exfalso
      simpa using congrArg Prod.snd h
    · have hu := physicalUpperPair_eq_iff p
        (adjacentPairSite p j ac.1.1) (adjacentPairSite p j ac.1.2)
        (adjacentPairSite p j bd.1.1) (adjacentPairSite p j bd.1.2)
        (congrArg Prod.fst h)
      rcases hu with hu | hu
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        have hab : ac = bd := Subtype.ext (Prod.ext h1 h2)
        subst bd
        rfl
      · have h1 := adjacentPairSite_injective p j hu.1
        have h2 := adjacentPairSite_injective p j hu.2
        have : ac.1.1 < ac.1.2 := ac.2
        have : ac.1.2 < ac.1.1 := by simpa [h1, h2] using bd.2
        omega

private theorem nnreal_mk_half (r : ℝ) (hr : 0 ≤ r) :
    (⟨r / 2, div_nonneg hr (by norm_num)⟩ : NNReal) =
      (⟨r, hr⟩ : NNReal) / 2 := by
  apply NNReal.eq
  rfl

/-- The global physical label attached to a local pair coordinate has exactly
the exposed-pair coordinate variance. -/
theorem physicalCoordinateVariance_adjacentPair (p : Params) (j : ZMod p.n)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    physicalCoordinateVariance p (adjacentPairPhysicalCoordinate p j k) =
      physicalExposedPairCoordinateVariance p k := by
  generalize hc : (hermitianCoordinateEquivFin (2 * p.W)).symm k = c
  rcases c with a | c
  · apply NNReal.eq
    simp [adjacentPairPhysicalCoordinate, hc, physicalCoordinateVariance,
      physicalUpperPair, siteLE, physicalExposedPairCoordinateVariance,
      varianceNNReal_adjacentPair]
  · rcases c with ab | ab
    all_goals
      let x := adjacentPairSite p j ab.1.1
      let y := adjacentPairSite p j ab.1.2
      have hxy : x ≠ y := by
        intro h
        exact ab.2.ne (adjacentPairSite_injective p j h)
      have hv := varianceNNReal_adjacentPair p j ab.1.1 ab.1.2
      by_cases hle : siteLE p x y
      · simp [adjacentPairPhysicalCoordinate, hc, physicalCoordinateVariance,
          physicalUpperPair, physicalExposedPairCoordinateVariance,
          exposedPairSamePhysicalBlock, x, y, hle, hxy]
        rw [nnreal_mk_half]
        change varianceNNReal p (adjacentPairSite p j ab.1.1)
          (adjacentPairSite p j ab.1.2) / 2 = _
        split_ifs with hs
        · simp only [hs, ite_true]
          rw [nnreal_mk_half]
          · exact congrArg (fun q : NNReal => q / 2) (by simpa [hs] using hv)
        · simp only [hs, ite_false]
          rw [nnreal_mk_half]
          · exact congrArg (fun q : NNReal => q / 2) (by simpa [hs] using hv)
          all_goals exact p.diagonalVariance_pos.le
      · have hrev := siteLE_of_not_siteLE hle
        simp [adjacentPairPhysicalCoordinate, hc, physicalCoordinateVariance,
          physicalUpperPair, physicalExposedPairCoordinateVariance,
          exposedPairSamePhysicalBlock, x, y, hle, hrev, hxy, Ne.symm hxy]
        rw [nnreal_mk_half]
        change varianceNNReal p (adjacentPairSite p j ab.1.2)
          (adjacentPairSite p j ab.1.1) / 2 = _
        have hcomm : varianceNNReal p (adjacentPairSite p j ab.1.2)
            (adjacentPairSite p j ab.1.1) =
            varianceNNReal p (adjacentPairSite p j ab.1.1)
              (adjacentPairSite p j ab.1.2) := by
          apply NNReal.eq
          exact varianceProfile_comm p _ _
        rw [hcomm]
        split_ifs with hs
        · simp only [hs, ite_true]
          rw [nnreal_mk_half]
          · exact congrArg (fun q : NNReal => q / 2) (by simpa [hs] using hv)
        · simp only [hs, ite_false]
          rw [nnreal_mk_half]
          · exact congrArg (fun q : NNReal => q / 2) (by simpa [hs] using hv)
          all_goals exact p.diagonalVariance_pos.le

/-- Orientation sign for local coordinates.  Only an imaginary strict-upper
coordinate changes sign when the global site ordering reverses. -/
def adjacentPairCoordinateSign (p : Params) (j : ZMod p.n)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) : ℝ :=
  match (hermitianCoordinateEquivFin (2 * p.W)).symm k with
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr ab) =>
      if siteLE p (adjacentPairSite p j ab.1.1)
        (adjacentPairSite p j ab.1.2) then 1 else -1

/-- Deterministic orientation identity, including the imaginary sign at the
cyclic ordering reversal. -/
theorem Law.actualAdjacentPairCoordinates_apply
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    M.actualAdjacentPairCoordinates j ω k =
      adjacentPairCoordinateSign p j k *
        M.physicalCoordinate (adjacentPairPhysicalCoordinate p j k) ω := by
  change coordinatesOfHermitian (M.actualAdjacentPairMatrix j ω)
      ((hermitianCoordinateEquivFin (2 * p.W)).symm k) = _
  generalize hc : (hermitianCoordinateEquivFin (2 * p.W)).symm k = c
  rcases c with a | c
  · simp [adjacentPairCoordinateSign, adjacentPairPhysicalCoordinate,
      hc, Law.actualAdjacentPairMatrix, Law.physicalCoordinate,
      physicalCoordinateMap, physicalUpperPair, coordinatesOfHermitian, siteLE]
  · rcases c with ab | ab
    · let x := adjacentPairSite p j ab.1.1
      let y := adjacentPairSite p j ab.1.2
      have hxy : x ≠ y := by
        intro h
        have := adjacentPairSite_injective p j h
        exact ab.2.ne this
      by_cases hle : siteLE p x y
      · simp [adjacentPairCoordinateSign, adjacentPairPhysicalCoordinate, hc,
          Law.actualAdjacentPairMatrix, Law.physicalCoordinate,
          physicalCoordinateMap, physicalUpperPair, coordinatesOfHermitian,
          x, y, hle, hxy]
      · have hrev := siteLE_of_not_siteLE hle
        have hH := M.H_hermitian ω
        have he := hH.apply y x
        simp [adjacentPairCoordinateSign, adjacentPairPhysicalCoordinate, hc,
          Law.actualAdjacentPairMatrix, Law.physicalCoordinate,
          physicalCoordinateMap, physicalUpperPair, coordinatesOfHermitian,
          x, y, hle, hrev, hxy, ← he]
    · let x := adjacentPairSite p j ab.1.1
      let y := adjacentPairSite p j ab.1.2
      have hxy : x ≠ y := by
        intro h
        have := adjacentPairSite_injective p j h
        exact ab.2.ne this
      by_cases hle : siteLE p x y
      · simp [adjacentPairCoordinateSign, adjacentPairPhysicalCoordinate, hc,
          Law.actualAdjacentPairMatrix, Law.physicalCoordinate,
          physicalCoordinateMap, physicalUpperPair, coordinatesOfHermitian,
          x, y, hle, hxy]
      · have hrev := siteLE_of_not_siteLE hle
        have he := (M.H_hermitian ω).apply y x
        simp [adjacentPairCoordinateSign, adjacentPairPhysicalCoordinate, hc,
          Law.actualAdjacentPairMatrix, Law.physicalCoordinate,
          physicalCoordinateMap, physicalUpperPair, coordinatesOfHermitian,
          x, y, hle, hrev, hxy, Ne.symm hxy, ← he]

/-- The full adjacent-pair real coordinate family is mutually
independent. -/
theorem Law.iIndepFun_actualAdjacentPairCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) :
    iIndepFun (fun k => fun ω => M.actualAdjacentPairCoordinates j ω k) M.P := by
  have h := M.iIndepFun_physicalCoordinate.precomp
    (adjacentPairPhysicalCoordinate_injective p j)
  have hs := h.comp
    (fun k x => adjacentPairCoordinateSign p j k * x)
    (fun k => measurable_const.mul measurable_id)
  apply hs.congr
  intro k
  filter_upwards [] with ω
  exact (M.actualAdjacentPairCoordinates_apply j ω k).symm

/-- Each oriented adjacent-pair coordinate has its expected centered Gaussian law. -/
theorem Law.hasLaw_actualAdjacentPairCoordinate
    {p : Params} (M : Law p) (j : ZMod p.n)
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    HasLaw (fun ω => M.actualAdjacentPairCoordinates j ω k)
      (gaussianReal 0 (physicalExposedPairCoordinateVariance p k)) M.P := by
  have h := M.hasLaw_physicalCoordinate (adjacentPairPhysicalCoordinate p j k)
  rw [physicalCoordinateVariance_adjacentPair p j k] at h
  have heq := M.actualAdjacentPairCoordinates_apply j
  generalize hc : (hermitianCoordinateEquivFin (2 * p.W)).symm k = c
  rcases c with a | c
  · have hs : adjacentPairCoordinateSign p j k = 1 := by
      simp [adjacentPairCoordinateSign, hc]
    simpa [hs, heq] using h
  · rcases c with ab | ab
    · have hs : adjacentPairCoordinateSign p j k = 1 := by
        simp [adjacentPairCoordinateSign, hc]
      simpa [hs, heq] using h
    · by_cases hle : siteLE p (adjacentPairSite p j ab.1.1)
          (adjacentPairSite p j ab.1.2)
      · have hs : adjacentPairCoordinateSign p j k = 1 := by
          simp [adjacentPairCoordinateSign, hc, hle]
        simpa [hs, heq] using h
      · have hs : adjacentPairCoordinateSign p j k = -1 := by
          simp [adjacentPairCoordinateSign, hc, hle]
        have hn := gaussianReal_neg h
        rw [Pi.neg_def] at hn
        simpa [hs, heq] using hn

/-- The adjacent-pair vector has the full finite product Gaussian law. -/
theorem Law.hasLaw_actualAdjacentPairCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) :
    HasLaw (M.actualAdjacentPairCoordinates j)
      (Measure.pi fun k =>
        gaussianReal 0 (physicalExposedPairCoordinateVariance p k)) M.P := by
  exact M.iIndepFun_actualAdjacentPairCoordinates j |>.hasLaw_pi
    (M.hasLaw_actualAdjacentPairCoordinate j)

@[simp] theorem mem_adjacentPairUpperPairs_iff (p : Params) (j : ZMod p.n)
    (q : UpperPair p) :
    q ∈ adjacentPairUpperPairs p j ↔
      (q.1.1.1 = j ∨ q.1.1.1 = j + 1) ∧
        (q.1.2.1 = j ∨ q.1.2.1 = j + 1) := by
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  simp [adjacentPairUpperPairs]

/-- Merge the internal-pair and complementary upper vectors. -/
def mergeAdjacentPairUpperCoordinates (p : Params) (j : ZMod p.n)
    (x : adjacentPairUpperPairs p j → ℂ)
    (y : adjacentPairExteriorUpperPairs p j → ℂ) (q : UpperPair p) : ℂ := by
  classical
  exact if h : q ∈ adjacentPairUpperPairs p j then x ⟨q, h⟩
    else y ⟨q, by
      simp only [adjacentPairExteriorUpperPairs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa only [adjacentPairUpperPairs, Finset.mem_filter,
        Finset.mem_univ, true_and] using h⟩

/-- Merging the two projections recovers every selected upper entry. -/
theorem Law.mergeAdjacentPairUpperCoordinates_apply
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) (q : UpperPair p) :
    mergeAdjacentPairUpperCoordinates p j (M.actualPairUpperCoordinates j ω)
      (M.actualPairExteriorUpperCoordinates j ω) q = M.H ω q.1.1 q.1.2 := by
  by_cases h : q ∈ adjacentPairUpperPairs p j
  · simp [mergeAdjacentPairUpperCoordinates, h, Law.actualPairUpperCoordinates]
  · simp [mergeAdjacentPairUpperCoordinates, h,
      Law.actualPairExteriorUpperCoordinates]

/-- The adjacent merge is measurable. -/
theorem measurable_mergeAdjacentPairUpperCoordinates (p : Params) (j : ZMod p.n) :
    Measurable (fun z : (adjacentPairUpperPairs p j → ℂ) ×
      (adjacentPairExteriorUpperPairs p j → ℂ) =>
      mergeAdjacentPairUpperCoordinates p j z.1 z.2) := by
  rw [measurable_pi_iff]
  intro q
  by_cases h : q ∈ adjacentPairUpperPairs p j
  · simp only [mergeAdjacentPairUpperCoordinates, h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [mergeAdjacentPairUpperCoordinates, h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

/-- A canonical Hermitianization, equal to the input on Hermitian matrices. -/
def hermitianizeMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : HermitianMatrix ι :=
  ⟨((2 : ℂ)⁻¹) • (A.conjTranspose + A),
    (Matrix.isHermitian_transpose_add_self A).smul (by simp [IsSelfAdjoint])⟩

@[simp] theorem hermitianizeMatrix_of_isHermitian {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (hermitianizeMatrix A).1 = A := by
  ext i j
  simp only [hermitianizeMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.conjTranspose_apply, hA.apply]
  ring

/-- Hermitianization is measurable entrywise. -/
theorem measurable_hermitianizeMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (hermitianizeMatrix : Matrix ι ι ℂ → HermitianMatrix ι) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro i j
  exact measurable_const.mul
    ((Complex.continuous_conj.measurable.comp
      ((measurable_pi_apply i).comp (measurable_pi_apply j))).add
      ((measurable_pi_apply j).comp (measurable_pi_apply i)))

/-- Pair coordinates reconstructed from their internal upper vector alone. -/
def adjacentPairCoordinatesFromUpper (p : Params) (j : ZMod p.n)
    (x : adjacentPairUpperPairs p j → ℂ) : HermitianCoordinateSpace (2 * p.W) :=
  hermitianFinCoordinateReadback (2 * p.W)
    ⟨(hermitianizeMatrix (matrixOfUpperCoordinates p
      (mergeAdjacentPairUpperCoordinates p j x (fun _ => 0)))).1.submatrix
        (adjacentPairSite p j) (adjacentPairSite p j),
      (hermitianizeMatrix (matrixOfUpperCoordinates p
        (mergeAdjacentPairUpperCoordinates p j x (fun _ => 0)))).2.submatrix _⟩

/-- Exterior state reconstructed from its complementary upper vector alone. -/
def adjacentPairExteriorStateFromUpper (p : Params) (j : ZMod p.n)
    (y : adjacentPairExteriorUpperPairs p j → ℂ) :
    ActualPairExteriorCouplingState p j :=
  let A := hermitianizeMatrix (matrixOfUpperCoordinates p
    (mergeAdjacentPairUpperCoordinates p j (fun _ => 0) y))
  (⟨A.1.submatrix Subtype.val Subtype.val, A.2.submatrix _⟩,
    A.1.submatrix Subtype.val (adjacentPairSite p j))

/-- The pair reconstruction is measurable. -/
theorem measurable_adjacentPairCoordinatesFromUpper (p : Params) (j : ZMod p.n) :
    Measurable (adjacentPairCoordinatesFromUpper p j) := by
  apply (measurable_hermitianFinCoordinateReadback (2 * p.W)).comp
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro a b
  have hm : Measurable (fun x : adjacentPairUpperPairs p j → ℂ =>
      matrixOfUpperCoordinates p
        (mergeAdjacentPairUpperCoordinates p j x (fun _ => 0))) :=
    (measurable_matrixOfUpperCoordinates p).comp
      ((measurable_mergeAdjacentPairUpperCoordinates p j).comp
        (measurable_id.prodMk
          (show Measurable (fun _ : adjacentPairUpperPairs p j → ℂ =>
            (fun _ : adjacentPairExteriorUpperPairs p j => (0 : ℂ))) from measurable_const)))
  have hh := measurable_hermitianizeMatrix.comp hm
  exact (Matrix.measurable_iff.mp (Measurable.subtype_val hh))
    (adjacentPairSite p j a) (adjacentPairSite p j b)

/-- The exterior reconstruction is measurable. -/
theorem measurable_adjacentPairExteriorStateFromUpper (p : Params) (j : ZMod p.n) :
    Measurable (adjacentPairExteriorStateFromUpper p j) := by
  have hm : Measurable (fun y : adjacentPairExteriorUpperPairs p j → ℂ =>
      matrixOfUpperCoordinates p
        (mergeAdjacentPairUpperCoordinates p j (fun _ => 0) y)) :=
    (measurable_matrixOfUpperCoordinates p).comp
      ((measurable_mergeAdjacentPairUpperCoordinates p j).comp
        ((show Measurable (fun _ : adjacentPairExteriorUpperPairs p j → ℂ =>
          (fun _ : adjacentPairUpperPairs p j => (0 : ℂ))) from measurable_const).prodMk
          measurable_id))
  have hh := measurable_hermitianizeMatrix.comp hm
  apply Measurable.prodMk
  · apply Measurable.subtype_mk
    rw [Matrix.measurable_iff]
    intro a b
    exact (Matrix.measurable_iff.mp (Measurable.subtype_val hh)) a.1 b.1
  · rw [Matrix.measurable_iff]
    intro a b
    exact (Matrix.measurable_iff.mp (Measurable.subtype_val hh)) a.1
      (adjacentPairSite p j b)

/-- Every adjacent-pair local site lies in one of the selected blocks. -/
theorem adjacentPairSite_block (p : Params) (j : ZMod p.n) (a : Fin (2 * p.W)) :
    (adjacentPairSite p j a).1 = j ∨ (adjacentPairSite p j a).1 = j + 1 := by
  let a' : Fin (p.W + p.W) := Fin.cast (by omega) a
  generalize ha : a' = aa
  revert ha
  refine Fin.addCases (fun u ha => ?_) (fun v ha => ?_) aa
  · left
    simp [adjacentPairSite, a', ha]
  · right
    unfold adjacentPairSite
    rw [show Fin.cast (by omega) a = Fin.natAdd p.W v by simpa [a'] using ha]
    rw [Fin.addCases_right]

/-- Internal upper reconstruction recovers the pair coordinates. -/
theorem Law.adjacentPairCoordinatesFromUpper_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    adjacentPairCoordinatesFromUpper p j (M.actualPairUpperCoordinates j ω) =
      M.actualAdjacentPairCoordinates j ω := by
  let A := matrixOfUpperCoordinates p
    (mergeAdjacentPairUpperCoordinates p j (M.actualPairUpperCoordinates j ω)
      (fun _ => 0))
  have hentry (a b : Fin (2 * p.W)) :
      A (adjacentPairSite p j a) (adjacentPairSite p j b) =
        M.H ω (adjacentPairSite p j a) (adjacentPairSite p j b) := by
    have ha := adjacentPairSite_block p j a
    have hb := adjacentPairSite_block p j b
    by_cases h : siteLE p (adjacentPairSite p j a) (adjacentPairSite p j b)
    · let q : UpperPair p :=
        ⟨(adjacentPairSite p j a, adjacentPairSite p j b), h⟩
      have hq : q ∈ adjacentPairUpperPairs p j :=
        (mem_adjacentPairUpperPairs_iff p j q).2 ⟨ha, hb⟩
      dsimp only [A, matrixOfUpperCoordinates]
      rw [dite_eq_left h]
      change mergeAdjacentPairUpperCoordinates p j
        (M.actualPairUpperCoordinates j ω) (fun _ => 0) q = _
      rw [show mergeAdjacentPairUpperCoordinates p j
        (M.actualPairUpperCoordinates j ω) (fun _ => 0) q =
        M.actualPairUpperCoordinates j ω ⟨q, hq⟩ by
          simp [mergeAdjacentPairUpperCoordinates, hq]]
      rfl
    · have hr := siteLE_reverse_of_not p _ _ h
      let q : UpperPair p :=
        ⟨(adjacentPairSite p j b, adjacentPairSite p j a), hr⟩
      have hq : q ∈ adjacentPairUpperPairs p j :=
        (mem_adjacentPairUpperPairs_iff p j q).2 ⟨hb, ha⟩
      dsimp only [A, matrixOfUpperCoordinates]
      rw [dite_eq_right h]
      change star (mergeAdjacentPairUpperCoordinates p j
        (M.actualPairUpperCoordinates j ω) (fun _ => 0) q) = _
      rw [show mergeAdjacentPairUpperCoordinates p j
        (M.actualPairUpperCoordinates j ω) (fun _ => 0) q =
        M.actualPairUpperCoordinates j ω ⟨q, hq⟩ by
          simp [mergeAdjacentPairUpperCoordinates, hq]]
      exact (M.H_hermitian ω).apply _ _
  unfold adjacentPairCoordinatesFromUpper Law.actualAdjacentPairCoordinates
  congr 1
  apply Subtype.ext
  ext a b
  change (hermitianizeMatrix A).1 (adjacentPairSite p j a)
      (adjacentPairSite p j b) = _
  change ((hermitianizeMatrix A).1 (adjacentPairSite p j a)
      (adjacentPairSite p j b)) =
    M.H ω (adjacentPairSite p j a) (adjacentPairSite p j b)
  simp only [hermitianizeMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.conjTranspose_apply]
  rw [hentry b a, hentry a b, (M.H_hermitian ω).apply]
  ring

/-- Membership in the complementary upper set is precisely non-membership in
internal pair coordinates. -/
@[simp] theorem mem_adjacentPairExteriorUpperPairs_iff
    (p : Params) (j : ZMod p.n) (q : UpperPair p) :
    q ∈ adjacentPairExteriorUpperPairs p j ↔
      ¬((q.1.1.1 = j ∨ q.1.1.1 = j + 1) ∧
        (q.1.2.1 = j ∨ q.1.2.1 = j + 1)) := by
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  simp [adjacentPairExteriorUpperPairs]

/-- Complementary upper reconstruction recovers the exterior matrix and its
coupling to the adjacent pair. -/
theorem Law.adjacentPairExteriorStateFromUpper_coordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    adjacentPairExteriorStateFromUpper p j
        (M.actualPairExteriorUpperCoordinates j ω) =
      M.actualPairExteriorCouplingState j ω := by
  let A := matrixOfUpperCoordinates p
    (mergeAdjacentPairUpperCoordinates p j (fun _ => 0)
      (M.actualPairExteriorUpperCoordinates j ω))
  have hentry (x y : Site p.n p.W)
      (hout : ¬((x.1 = j ∨ x.1 = j + 1) ∧
        (y.1 = j ∨ y.1 = j + 1))) : A x y = M.H ω x y := by
    by_cases h : siteLE p x y
    · let q : UpperPair p := ⟨(x, y), h⟩
      have hq : q ∈ adjacentPairExteriorUpperPairs p j :=
        (mem_adjacentPairExteriorUpperPairs_iff p j q).2 hout
      dsimp only [A, matrixOfUpperCoordinates]
      rw [dite_eq_left h]
      change mergeAdjacentPairUpperCoordinates p j (fun _ => 0)
        (M.actualPairExteriorUpperCoordinates j ω) q = _
      rw [show mergeAdjacentPairUpperCoordinates p j (fun _ => 0)
        (M.actualPairExteriorUpperCoordinates j ω) q =
        M.actualPairExteriorUpperCoordinates j ω ⟨q, hq⟩ by
          simp [mergeAdjacentPairUpperCoordinates,
            (mem_adjacentPairUpperPairs_iff p j q).not.mpr hout]]
      rfl
    · have hr := siteLE_reverse_of_not p x y h
      let q : UpperPair p := ⟨(y, x), hr⟩
      have hout' : ¬((y.1 = j ∨ y.1 = j + 1) ∧
          (x.1 = j ∨ x.1 = j + 1)) := by
        intro h'
        exact hout ⟨h'.2, h'.1⟩
      have hq : q ∈ adjacentPairExteriorUpperPairs p j :=
        (mem_adjacentPairExteriorUpperPairs_iff p j q).2 hout'
      dsimp only [A, matrixOfUpperCoordinates]
      rw [dite_eq_right h]
      change star (mergeAdjacentPairUpperCoordinates p j (fun _ => 0)
        (M.actualPairExteriorUpperCoordinates j ω) q) = _
      rw [show mergeAdjacentPairUpperCoordinates p j (fun _ => 0)
        (M.actualPairExteriorUpperCoordinates j ω) q =
        M.actualPairExteriorUpperCoordinates j ω ⟨q, hq⟩ by
          simp [mergeAdjacentPairUpperCoordinates,
            (mem_adjacentPairUpperPairs_iff p j q).not.mpr hout']]
      exact (M.H_hermitian ω).apply _ _
  have hherm (x y : Site p.n p.W)
      (hout : ¬((x.1 = j ∨ x.1 = j + 1) ∧
        (y.1 = j ∨ y.1 = j + 1))) :
      (hermitianizeMatrix A).1 x y = M.H ω x y := by
    have hout' : ¬((y.1 = j ∨ y.1 = j + 1) ∧
        (x.1 = j ∨ x.1 = j + 1)) := by
      intro h'
      exact hout ⟨h'.2, h'.1⟩
    simp only [hermitianizeMatrix, Matrix.smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.conjTranspose_apply]
    rw [hentry y x hout', hentry x y hout, (M.H_hermitian ω).apply]
    ring
  apply Prod.ext
  · apply Subtype.ext
    ext a b
    exact hherm a.1 b.1 (by
      intro h
      rcases h.1 with h | h
      · exact a.2.1 h
      · exact a.2.2 h)
  · ext a b
    exact hherm a.1 (adjacentPairSite p j b) (by
      intro h
      rcases h.1 with h | h
      · exact a.2.1 h
      · exact a.2.2 h)

/-- The pair coordinate vector is independent of the complete physical
exterior/coupling state. -/
theorem Law.indepFun_actualAdjacentPairCoordinates_exteriorState
    {p : Params} (M : Law p) (j : ZMod p.n) :
    IndepFun (M.actualAdjacentPairCoordinates j)
      (M.actualPairExteriorCouplingState j) M.P := by
  have h := (M.indepFun_actualPairUpperCoordinates_exterior j).comp
    (measurable_adjacentPairCoordinatesFromUpper p j)
    (measurable_adjacentPairExteriorStateFromUpper p j)
  have hp : adjacentPairCoordinatesFromUpper p j ∘
      M.actualPairUpperCoordinates j = M.actualAdjacentPairCoordinates j := by
    funext ω
    exact M.adjacentPairCoordinatesFromUpper_coordinates j ω
  have he : adjacentPairExteriorStateFromUpper p j ∘
      M.actualPairExteriorUpperCoordinates j =
        M.actualPairExteriorCouplingState j := by
    funext ω
    exact M.adjacentPairExteriorStateFromUpper_coordinates j ω
  simpa only [hp, he] using h

/-- The pair/exterior pushforward is the product of the physical
pair Gaussian law and the exterior marginal. -/
theorem Law.actualPairExteriorLaw_eq_prod
    {p : Params} (M : Law p) (j : ZMod p.n) :
    M.actualPairExteriorLaw j =
      (Measure.pi fun k =>
        gaussianReal 0 (physicalExposedPairCoordinateVariance p k)).prod
      (M.actualPairExteriorStateLaw j) := by
  have hpair := M.hasLaw_actualAdjacentPairCoordinates j
  have hext : HasLaw (M.actualPairExteriorCouplingState j)
      (M.actualPairExteriorStateLaw j) M.P :=
    ⟨(M.measurable_actualPairExteriorCouplingState j).aemeasurable, rfl⟩
  exact (ProbabilityTheory.IndepFun.hasLaw_prod hpair hext
    (M.indepFun_actualAdjacentPairCoordinates_exteriorState j)).map_eq

/-- The residual/fresh/exterior split readback has the product of the physical
pair law and the unchanged exterior law. -/
theorem physicalActualPairSplitReadback_map_eq_prod
    {p : Params} {j : ZMod p.n} {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure (ActualPairExteriorCouplingState p j))
    [IsProbabilityMeasure exteriorLaw] :
    Measure.map (physicalActualPairSplitReadback (p := p) (j := j))
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw) =
      (Measure.pi fun k =>
        gaussianReal 0 (physicalExposedPairCoordinateVariance p k)).prod
        exteriorLaw := by
  let K := Fin (Fintype.card (HermitianCoordinate (2 * p.W)))
  let μV : Measure (K → ℝ) := physicalExposedPairResidualMeasure p hs0 hsc hsb
  let μG : Measure (K → ℝ) := hermitianGUECoordinateMeasure (2 * p.W)
    (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0)
  let source : Measure (((K → ℝ) × ActualPairExteriorCouplingState p j) ×
      (K → ℝ)) := (μV.prod exteriorLaw).prod μG
  let T : (((K → ℝ) × ActualPairExteriorCouplingState p j) × (K → ℝ)) →
      (((K → ℝ) × (K → ℝ)) × ActualPairExteriorCouplingState p j) :=
    fun z => ((z.1.1, z.2), z.1.2)
  have hTmeas : Measurable T :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have hT : Measure.map T source = (μV.prod μG).prod exteriorLaw := by
    let a₁ : (((K → ℝ) × ActualPairExteriorCouplingState p j) × (K → ℝ)) →
        (K → ℝ) × (ActualPairExteriorCouplingState p j × (K → ℝ)) :=
      MeasurableEquiv.prodAssoc
    let sw : (K → ℝ) × (ActualPairExteriorCouplingState p j × (K → ℝ)) →
        (K → ℝ) × ((K → ℝ) × ActualPairExteriorCouplingState p j) :=
      Prod.map id Prod.swap
    let a₂ : (K → ℝ) × ((K → ℝ) × ActualPairExteriorCouplingState p j) →
        ((K → ℝ) × (K → ℝ)) × ActualPairExteriorCouplingState p j :=
      MeasurableEquiv.prodAssoc.symm
    have ha1 : Measure.map a₁ source = μV.prod (exteriorLaw.prod μG) := by
      exact Measure.prodAssoc_prod
    have hsw : Measure.map sw (μV.prod (exteriorLaw.prod μG)) =
        μV.prod (μG.prod exteriorLaw) := by
      calc
        Measure.map sw (μV.prod (exteriorLaw.prod μG)) =
            (Measure.map id μV).prod (Measure.map Prod.swap
              (exteriorLaw.prod μG)) := by
              exact (Measure.map_prod_map μV (exteriorLaw.prod μG)
                measurable_id measurable_swap).symm
        _ = μV.prod (μG.prod exteriorLaw) := by
          rw [Measure.map_id, Measure.measurePreserving_swap.map_eq]
    have ha2 : Measure.map a₂ (μV.prod (μG.prod exteriorLaw)) =
        (μV.prod μG).prod exteriorLaw := by
      rw [← Measure.prodAssoc_prod]
      change Measure.map MeasurableEquiv.prodAssoc.symm
        (Measure.map MeasurableEquiv.prodAssoc ((μV.prod μG).prod exteriorLaw)) = _
      rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
        MeasurableEquiv.prodAssoc.measurable]
      simp
    have ha1m : Measurable a₁ := MeasurableEquiv.prodAssoc.measurable
    have hswm : Measurable sw := measurable_id.prodMap measurable_swap
    have ha2m : Measurable a₂ := MeasurableEquiv.prodAssoc.symm.measurable
    have hfun : a₂ ∘ sw ∘ a₁ = T := rfl
    calc
      Measure.map T source = Measure.map (a₂ ∘ sw ∘ a₁) source := by rw [hfun]
      _ = Measure.map a₂ (Measure.map sw (Measure.map a₁ source)) := by
        rw [Measure.map_map ha2m hswm]
        rw [Measure.map_map (ha2m.comp hswm) ha1m]
        congr 1
      _ = _ := by rw [ha1, hsw, ha2]
  let sumPair : ((K → ℝ) × (K → ℝ)) → (K → ℝ) := fun q => q.1 + q.2
  have hsum : Measurable sumPair := by
    rw [measurable_pi_iff]
    intro k
    exact ((measurable_pi_apply k).comp measurable_fst).add
      ((measurable_pi_apply k).comp measurable_snd)
  have hpairFull := physicalActualPairSplitReadback_pair_hasLaw
    (p := p) (j := j) hs0 hsc hsb exteriorLaw
  have hpair : Measure.map sumPair (μV.prod μG) =
      Measure.pi fun k => gaussianReal 0
        (physicalExposedPairCoordinateVariance p k) := by
    have hf : Measure.map (fun z => sumPair z.1)
        ((μV.prod μG).prod exteriorLaw) =
        Measure.map sumPair (μV.prod μG) := by
      calc
        _ = Measure.map sumPair
            (Measure.map Prod.fst ((μV.prod μG).prod exteriorLaw)) := by
              rw [Measure.map_map hsum measurable_fst]
              rfl
        _ = _ := by rw [measurePreserving_fst.map_eq]
    calc
      Measure.map sumPair (μV.prod μG) =
          Measure.map (fun z => sumPair z.1)
            ((μV.prod μG).prod exteriorLaw) := hf.symm
      _ = Measure.map (fun z => sumPair z.1) (Measure.map T source) := by rw [hT]
      _ = Measure.map ((fun z => sumPair z.1) ∘ T) source := by
        change Measure.map (sumPair ∘ Prod.fst) (Measure.map T source) = _
        rw [Measure.map_map (hsum.comp measurable_fst) hTmeas]
        congr 1
      _ = _ := hpairFull.map_eq
  change Measure.map (fun z : (((K → ℝ) ×
      ActualPairExteriorCouplingState p j) × (K → ℝ)) =>
      (z.1.1 + z.2, z.1.2)) source = _
  rw [show (fun z : (((K → ℝ) × ActualPairExteriorCouplingState p j) ×
      (K → ℝ)) => (z.1.1 + z.2, z.1.2)) =
      Prod.map sumPair id ∘ T by rfl]
  calc
    Measure.map (Prod.map sumPair id ∘ T) source =
        Measure.map (Prod.map sumPair id) (Measure.map T source) := by
          rw [Measure.map_map (hsum.prodMap measurable_id) hTmeas]
    _ = Measure.map (Prod.map sumPair id) ((μV.prod μG).prod exteriorLaw) := by rw [hT]
    _ = (Measure.map sumPair (μV.prod μG)).prod
        (Measure.map id exteriorLaw) := by
          rw [Measure.map_prod_map (μV.prod μG) exteriorLaw hsum measurable_id]
    _ = _ := by rw [hpair, Measure.map_id]

/-- The adjacent-pair split input follows unconditionally from the
Gaussian ring law, including the cyclic imaginary-coordinate orientation. -/
theorem Law.actualPairGaussianSplitInput
    {p : Params} (M : Law p) (j : ZMod p.n) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b) :
    M.ActualPairGaussianSplitInput j hs0 hsc hsb := by
  constructor
  rw [M.actualPairExteriorLaw_eq_prod j]
  exact (physicalActualPairSplitReadback_map_eq_prod hs0 hsc hsb
    (M.actualPairExteriorStateLaw j)).symm

/-- Unconditional fixed-exterior nonnegative integral splitting for the
physical adjacent pair. -/
theorem Law.lintegral_actualPairExterior_eq_physicalSplit_unconditional
    {p : Params} (M : Law p) (j : ZMod p.n) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (Φ : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ ω, Φ (M.actualAdjacentPairCoordinates j ω,
      M.actualPairExteriorCouplingState j ω) ∂M.P) =
      ∫⁻ z, Φ (physicalActualPairSplitReadback (p := p) (j := j) z)
        ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0)
          (physicalExposedPairResidualMeasure p hs0 hsc hsb)
          (M.actualPairExteriorStateLaw j) :=
  M.lintegral_actualPairExterior_eq_physicalSplit j hs0 hsc hsb
    (M.actualPairGaussianSplitInput j hs0 hsc hsb) Φ hΦ

end GaussianRing
end CoareaNative.BlockBand