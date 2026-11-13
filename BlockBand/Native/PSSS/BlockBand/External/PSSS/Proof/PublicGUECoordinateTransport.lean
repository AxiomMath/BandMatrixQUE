module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GroupedIndependence
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicBlockProductAdapter

/-!
# Scalar-coordinate transport for the public block GUE product

This module flattens all real Hermitian coordinates of all blocks into one
finite product.  It then regroups those independent scalars by blocks and by
upper-matrix entries.  The latter grouping is the exact sigma-index ordering
adapter: reversing an internal strict-upper pair negates its imaginary
coordinate, while diagonal imaginary and cross-block coordinates are zero.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BlockGUE

local instance publicUpperPairFintype {k : ℕ} (d : Fin k → ℕ) :
    Fintype (UpperPair d) := by
  unfold UpperPair
  infer_instance

/-- A real Hermitian coordinate, tagged by its block. -/
abbrev PublicScalarIndex {k : ℕ} (d : Fin k → ℕ) :=
  Σ j, HermitianCoordinate (d j)

/-- The completely flattened real coordinate sample space. -/
abbrev PublicScalarSample {k : ℕ} (d : Fin k → ℕ) :=
  PublicScalarIndex d → ℝ

/-- Variance of a flattened scalar coordinate. -/
def publicScalarVariance {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)
    (s : PublicScalarIndex d) : NNReal :=
  hermitianGUEFinCoordinateVariance (d s.1) (1 / (d s.1 : ℝ))
    (one_div_nonneg.mpr (by exact_mod_cast (hd s.1).le))
    (hermitianCoordinateEquivFin (d s.1) s.2)

/-- One finite product of every scalar used by every public GUE block. -/
def publicScalarMeasure {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    Measure (PublicScalarSample d) :=
  Measure.pi fun s => gaussianReal 0 (publicScalarVariance d hd s)

instance publicScalarMeasure.instIsProbabilityMeasure {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    IsProbabilityMeasure (publicScalarMeasure d hd) := by
  unfold publicScalarMeasure
  infer_instance

/-- Regroup flattened scalars into the finite-coordinate convention of block
`j`. -/
def publicBlockCoordinates {k : ℕ} {d : Fin k → ℕ}
    (x : PublicScalarSample d) (j : Fin k) : HermitianCoordinateSpace (d j) :=
  fun n => x ⟨j, (hermitianCoordinateEquivFin (d j)).symm n⟩

/-- Regroup and reconstruct all public Hermitian blocks. -/
def publicBlocksFromScalars {k : ℕ} {d : Fin k → ℕ}
    (x : PublicScalarSample d) : PublicBlockSample d :=
  fun j => hermitianGUEBlock (d j) (publicBlockCoordinates x j)

theorem measurable_publicBlockCoordinates_fromScalars {k : ℕ}
    (d : Fin k → ℕ) :
    Measurable (fun x : PublicScalarSample d =>
      fun j => publicBlockCoordinates x j) := by
  rw [measurable_pi_iff]
  intro j
  rw [measurable_pi_iff]
  intro n
  exact measurable_pi_apply _

theorem measurable_publicBlocks_reconstruction {k : ℕ}
    (d : Fin k → ℕ) :
    Measurable (fun y : ∀ j, HermitianCoordinateSpace (d j) =>
      fun j => hermitianGUEBlock (d j) (y j)) := by
  rw [measurable_pi_iff]
  intro j
  exact (measurable_hermitianGUEBlock (d j)).comp (measurable_pi_apply j)

/-- Flattened scalar coordinate projections are mutually independent. -/
theorem publicScalar_iIndep {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    iIndepFun (fun s (x : PublicScalarSample d) => x s)
      (publicScalarMeasure d hd) := by
  unfold publicScalarMeasure
  apply iIndepFun_pi (X := fun _ : PublicScalarIndex d => id)
  intro s
  exact measurable_id.aemeasurable

/-- Every flattened scalar has its defining Gaussian marginal. -/
theorem publicScalar_hasLaw {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)
    (s : PublicScalarIndex d) :
    HasLaw (fun x : PublicScalarSample d => x s)
      (gaussianReal 0 (publicScalarVariance d hd s))
      (publicScalarMeasure d hd) := by
  refine ⟨(measurable_pi_apply s).aemeasurable, ?_⟩
  exact (measurePreserving_eval
    (fun q => gaussianReal 0 (publicScalarVariance d hd q)) s).map_eq

/-- The regrouped coordinates of one block have exactly the canonical
coordinate-product GUE law at variance `1/d_j`. -/
theorem publicBlockCoordinates_hasLaw {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (j : Fin k) :
    HasLaw (fun x : PublicScalarSample d => publicBlockCoordinates x j)
      (hermitianGUECoordinateMeasure (d j) (1 / (d j : ℝ))
        (one_div_nonneg.mpr (by exact_mod_cast (hd j).le)))
      (publicScalarMeasure d hd) := by
  unfold hermitianGUECoordinateMeasure
  apply iIndepFun.hasLaw_pi
  · intro n
    simpa [publicBlockCoordinates, publicScalarVariance] using
      publicScalar_hasLaw d hd
        ⟨j, (hermitianCoordinateEquivFin (d j)).symm n⟩
  · exact (publicScalar_iIndep d hd).precomp (by
      intro a b hab
      apply (hermitianCoordinateEquivFin (d j)).symm.injective
      simpa using Sigma.mk.inj_iff.mp hab |>.2)

/-- Scalar indices belonging to one block. -/
def publicBlockPacket {k : ℕ} {d : Fin k → ℕ} (j : Fin k) :
    Set (PublicScalarIndex d) := {s | s.1 = j}

/-- Different block packets are disjoint. -/
theorem publicBlockPacket_pairwiseDisjoint {k : ℕ} (d : Fin k → ℕ) :
    Set.Pairwise Set.univ fun a b =>
      Disjoint (@publicBlockPacket k d a) (publicBlockPacket b) := by
  intro a _ b _ hab
  rw [Set.disjoint_left]
  intro s hsa hsb
  exact hab (hsa.symm.trans hsb)

/-- Regrouping all flattened scalars by block has the nested public coordinate
product law. -/
theorem hasLaw_publicBlockCoordinates {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) :
    HasLaw (fun x j => publicBlockCoordinates x j)
      (Measure.pi fun j => hermitianGUECoordinateMeasure (d j)
        (1 / (d j : ℝ))
        (one_div_nonneg.mpr (by exact_mod_cast (hd j).le)))
      (publicScalarMeasure d hd) := by
  apply iIndepFun.hasLaw_pi
  · exact publicBlockCoordinates_hasLaw d hd
  · apply (publicScalar_iIndep d hd).group_packets_comp
      (fun _ => measurable_pi_apply _)
      (fun j => publicBlockPacket j)
      (publicBlockPacket_pairwiseDisjoint d)
      (fun j z n => z ⟨⟨j, (hermitianCoordinateEquivFin (d j)).symm n⟩, rfl⟩)
    intro j
    fun_prop

/-- Reconstructing the flattened scalar product gives the public
independent product of normalized single-block GUE laws. -/
theorem map_publicBlocksFromScalars_eq_publicBlockProductMeasure {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    Measure.map publicBlocksFromScalars (publicScalarMeasure d hd) =
      publicBlockProductMeasure d hd := by
  have hcoords := hasLaw_publicBlockCoordinates d hd
  have hmap := hcoords.map_eq
  change Measure.map
      ((fun y j => hermitianGUEBlock (d j) (y j)) ∘
        (fun x : PublicScalarSample d => fun j => publicBlockCoordinates x j))
      (publicScalarMeasure d hd) = _
  rw [← Measure.map_map (measurable_publicBlocks_reconstruction d)
    (measurable_publicBlockCoordinates_fromScalars d)]
  rw [hmap]
  rw [Measure.pi_map_pi]
  · unfold publicBlockProductMeasure
    congr
    funext j
    exact map_hermitianGUEBlock_eq_GUE (d j) (1 / (d j : ℝ))
      (one_div_nonneg.mpr (by exact_mod_cast (hd j).le))
  · intro j
    exact (measurable_hermitianGUEBlock (d j)).aemeasurable

/-- The unique sigma-ordered upper entry owning a scalar Hermitian
coordinate.  Real and imaginary strict-upper coordinates have the same owner. -/
def publicScalarOwner {k : ℕ} (d : Fin k → ℕ)
    (s : PublicScalarIndex d) : UpperPair d := by
  rcases s with ⟨j, c⟩
  rcases c with i | c
  · exact ⟨(⟨j, i⟩, ⟨j, i⟩), by simp [indexLE]⟩
  · rcases c with ij | ij
    all_goals
      let x : Index d := ⟨j, ij.1.1⟩
      let y : Index d := ⟨j, ij.1.2⟩
      exact if h : indexLE d x y then ⟨(x, y), h⟩ else
        ⟨(y, x), by
          unfold indexLE at h ⊢
          exact Nat.le_of_lt (lt_of_not_ge h)⟩

/-- The scalar packet owned by a sigma-ordered upper entry.  Cross-block
entries automatically own no scalar. -/
def publicUpperScalarPacket {k : ℕ} (d : Fin k → ℕ) (q : UpperPair d) :
    Set (PublicScalarIndex d) := {s | publicScalarOwner d s = q}

/-- Read a named scalar from a packet, returning zero off the packet. -/
def publicPacketRead {k : ℕ} {d : Fin k → ℕ} {q : UpperPair d}
    (z : publicUpperScalarPacket d q → ℝ) (s : PublicScalarIndex d) : ℝ := by
  classical
  exact if h : s ∈ publicUpperScalarPacket d q then z ⟨s, h⟩ else 0

@[simp] theorem publicPacketRead_fullSample {k : ℕ} {d : Fin k → ℕ}
    {q : UpperPair d} (x : PublicScalarSample d) (s : PublicScalarIndex d)
    (hs : publicScalarOwner d s = q) :
    publicPacketRead (q := q) (fun u => x u) s = x s := by
  simp [publicPacketRead, publicUpperScalarPacket, hs]

/-- Read one sigma-ordered upper entry from its exact scalar packet.  Reversing
the ordinary `Fin` upper orientation negates the imaginary coordinate. -/
def publicUpperPairOfPacket {k : ℕ} (d : Fin k → ℕ) (q : UpperPair d)
    (z : publicUpperScalarPacket d q → ℝ) : UpperRealPair := by
  classical
  let x := q.1.1
  let y := q.1.2
  exact if hb : x.1 = y.1 then
    let y' : Fin (d x.1) := hb ▸ y.2
    if heq : x.2.val = y'.val then
      (publicPacketRead z ⟨x.1, .inl x.2⟩, 0)
    else if hlt : x.2.val < y'.val then
      (publicPacketRead z ⟨x.1, .inr (.inl ⟨(x.2, y'), hlt⟩)⟩,
       publicPacketRead z ⟨x.1, .inr (.inr ⟨(x.2, y'), hlt⟩)⟩)
    else
      (publicPacketRead z ⟨x.1, .inr (.inl ⟨(y', x.2),
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)⟩)⟩,
       -publicPacketRead z ⟨x.1, .inr (.inr ⟨(y', x.2),
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)⟩)⟩)
  else (0, 0)

/-- Packet readback is exactly the public block upper-coordinate readback. -/
theorem publicUpperPairOfPacket_eq {k : ℕ} (d : Fin k → ℕ)
    (x : PublicScalarSample d) (q : UpperPair d) :
    publicUpperPairOfPacket d q
        (fun s => x s) =
      publicBlockUpperCoordinates (publicBlocksFromScalars x) q := by
  rcases q with ⟨⟨⟨j, a⟩, ⟨j', b⟩⟩, hq⟩
  by_cases hb : j = j'
  · subst j'
    by_cases heqv : a.val = b.val
    · have heq : a = b := Fin.ext heqv
      subst b
      have howner : publicScalarOwner d ⟨j, .inl a⟩ =
          (⟨(⟨j, a⟩, ⟨j, a⟩), hq⟩ : UpperPair d) := by
        apply Subtype.ext
        rfl
      simp [publicUpperPairOfPacket, publicUpperScalarPacket,
        publicBlockUpperCoordinates, publicBlocksFromScalars,
        publicBlockDiagonal, publicBlockDiagonalRaw, publicBlockCoordinates,
        hermitianGUEBlock, hermitianOfFinCoordinates,
        hermitianOfCoordinates, hermitianMatrixOfCoordinates]
      exact publicPacketRead_fullSample x _ howner
    · by_cases hlt : a.val < b.val
      · have hne : a ≠ b := fun h => heqv (congrArg Fin.val h)
        have hlt' : a < b := hlt
        have howner₁ : publicScalarOwner d ⟨j, .inr (.inl ⟨(a, b), hlt'⟩)⟩ =
            (⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ : UpperPair d) := by
          simp only [publicScalarOwner, hq, ↓reduceDIte]
          apply Subtype.ext
          rfl
        have howner₂ : publicScalarOwner d ⟨j, .inr (.inr ⟨(a, b), hlt'⟩)⟩ =
            (⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ : UpperPair d) := by
          simp only [publicScalarOwner, hq, ↓reduceDIte]
          apply Subtype.ext
          rfl
        simp [publicUpperPairOfPacket, publicUpperScalarPacket,
          publicBlockUpperCoordinates, publicBlocksFromScalars,
          publicBlockDiagonal, publicBlockDiagonalRaw, publicBlockCoordinates,
          hermitianGUEBlock, hermitianOfFinCoordinates,
          hermitianOfCoordinates, hermitianMatrixOfCoordinates,
          hermitianUpperEntry, heqv, hlt, hne, hlt']
        constructor
        · apply publicPacketRead_fullSample
          simpa only [Subsingleton.elim] using howner₁
        · apply publicPacketRead_fullSample
          simpa only [Subsingleton.elim] using howner₂
      · have hba : b.val < a.val :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heqv)
        have hne : a ≠ b := fun h => heqv (congrArg Fin.val h)
        have hlt' : ¬ a < b := hlt
        have hnot : ¬ indexLE d (⟨j, b⟩ : Index d) ⟨j, a⟩ := by
          intro hrev
          apply hne
          have hxy : (⟨j, a⟩ : Index d) = ⟨j, b⟩ := by
            apply (Fintype.equivFin (Index d)).injective
            apply Fin.ext
            exact Nat.le_antisymm hq hrev
          apply Fin.ext
          exact congrArg (fun z : Index d => z.2.val) hxy
        have howner₁ : publicScalarOwner d ⟨j, .inr (.inl ⟨(b, a), hba⟩)⟩ =
            (⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ : UpperPair d) := by
          simp only [publicScalarOwner, hnot, ↓reduceDIte]
          apply Subtype.ext
          rfl
        have howner₂ : publicScalarOwner d ⟨j, .inr (.inr ⟨(b, a), hba⟩)⟩ =
            (⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ : UpperPair d) := by
          simp only [publicScalarOwner, hnot, ↓reduceDIte]
          apply Subtype.ext
          rfl
        simp [publicUpperPairOfPacket, publicUpperScalarPacket,
          publicBlockUpperCoordinates, publicBlocksFromScalars,
          publicBlockDiagonal, publicBlockDiagonalRaw, publicBlockCoordinates,
          hermitianGUEBlock, hermitianOfFinCoordinates,
          hermitianOfCoordinates, hermitianMatrixOfCoordinates,
          hermitianUpperEntry, heqv, hlt, hne, hlt']
        constructor
        · apply publicPacketRead_fullSample
          simpa only [Subsingleton.elim] using howner₁
        · apply publicPacketRead_fullSample
          simpa only [Subsingleton.elim] using howner₂
  · simp [publicUpperPairOfPacket,
      publicBlockUpperCoordinates,
      publicBlockDiagonal, publicBlockDiagonalRaw, hb]

/-- Distinct sigma-ordered upper entries use disjoint flattened scalar
packets. -/
theorem publicUpperScalarPacket_pairwiseDisjoint {k : ℕ}
    (d : Fin k → ℕ) :
    Set.Pairwise Set.univ fun q r =>
      Disjoint (publicUpperScalarPacket d q)
        (publicUpperScalarPacket d r) := by
  intro q _ r _ hqr
  rw [Set.disjoint_left]
  intro s hs ht
  exact hqr (hs.symm.trans ht)

theorem measurable_publicUpperPairOfPacket {k : ℕ} (d : Fin k → ℕ)
    (q : UpperPair d) :
    Measurable (publicUpperPairOfPacket d q) := by
  classical
  unfold publicUpperPairOfPacket publicPacketRead
  dsimp
  split_ifs <;> fun_prop

/-- The complete sigma-ordered upper-entry readback of the flattened public
scalars is mutually independent. -/
theorem publicUpperPair_iIndep {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) :
    iIndepFun (fun q (x : PublicScalarSample d) =>
      publicUpperPairOfPacket d q (fun s => x s))
      (publicScalarMeasure d hd) := by
  apply (publicScalar_iIndep d hd).group_packets_comp
      (fun _ => measurable_pi_apply _)
      (publicUpperScalarPacket d)
      (publicUpperScalarPacket_pairwiseDisjoint d)
      (publicUpperPairOfPacket d)
  exact measurable_publicUpperPairOfPacket d

/-- Each sigma-ordered packet has the canonical diagonal, strict-upper, or
cross-block component law. -/
theorem publicUpperPair_hasLaw {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (q : UpperPair d) :
    HasLaw (fun x : PublicScalarSample d =>
      publicUpperPairOfPacket d q (fun s => x s))
      (canonicalUpperPairMeasure d hd q)
      (publicScalarMeasure d hd) := by
  rcases q with ⟨⟨⟨j, a⟩, ⟨j', b⟩⟩, hq⟩
  by_cases hb : j = j'
  · subst j'
    by_cases heqv : a.val = b.val
    · have heq : a = b := Fin.ext heqv
      subst b
      rw [show canonicalUpperPairMeasure d hd
          ⟨(⟨j, a⟩, ⟨j, a⟩), hq⟩ =
          Measure.map (fun r : ℝ => (r, 0))
            (gaussianReal 0 ⟨1 / (d j : ℝ),
              one_div_nonneg.mpr (by exact_mod_cast (hd j).le)⟩) by
        simp [canonicalUpperPairMeasure, entryVariance]]
      have hs := publicScalar_hasLaw d hd
        (⟨j, .inl a⟩ : PublicScalarIndex d)
      have hm := (hasLaw_map
        (by fun_prop : AEMeasurable (fun r : ℝ => (r, (0 : ℝ)))
          (gaussianReal 0 (publicScalarVariance d hd ⟨j, .inl a⟩)))).fun_comp hs
      have hm' : HasLaw (fun x : PublicScalarSample d =>
          (x ⟨j, .inl a⟩, (0 : ℝ)))
          (Measure.map (fun r : ℝ => (r, (0 : ℝ)))
            (gaussianReal 0 ⟨1 / (d j : ℝ),
              one_div_nonneg.mpr (by exact_mod_cast (hd j).le)⟩))
          (publicScalarMeasure d hd) := by
        simpa [publicScalarVariance, hermitianGUEFinCoordinateVariance] using hm
      refine HasLaw.congr
        (X := fun x : PublicScalarSample d => (x ⟨j, .inl a⟩, (0 : ℝ)))
        (Y := fun x : PublicScalarSample d =>
          publicUpperPairOfPacket d ⟨(⟨j, a⟩, ⟨j, a⟩), hq⟩
            (fun s => x s)) hm' ?_
      filter_upwards with x
      calc
        _ = publicBlockUpperCoordinates (publicBlocksFromScalars x)
            ⟨(⟨j, a⟩, ⟨j, a⟩), hq⟩ :=
          publicUpperPairOfPacket_eq d x _
        _ = (x ⟨j, .inl a⟩, (0 : ℝ)) := by
          simp [publicBlockUpperCoordinates, publicBlocksFromScalars,
            publicBlockDiagonal, publicBlockDiagonalRaw, publicBlockCoordinates,
            hermitianGUEBlock, hermitianOfFinCoordinates,
            hermitianOfCoordinates, hermitianMatrixOfCoordinates]
    · by_cases hlt : a.val < b.val
      · let sR : PublicScalarIndex d := ⟨j, .inr (.inl ⟨(a, b), hlt⟩)⟩
        let sI : PublicScalarIndex d := ⟨j, .inr (.inr ⟨(a, b), hlt⟩)⟩
        have hsR := publicScalar_hasLaw d hd sR
        have hsI := publicScalar_hasLaw d hd sI
        have hvR : publicScalarVariance d hd sR =
            ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩ := by
          simp [sR, publicScalarVariance,
            hermitianGUEFinCoordinateVariance]
          apply NNReal.eq
          rfl
        have hvI : publicScalarVariance d hd sI =
            ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩ := by
          simp [sI, publicScalarVariance,
            hermitianGUEFinCoordinateVariance]
          apply NNReal.eq
          rfl
        rw [hvR] at hsR
        rw [hvI] at hsI
        have hind := (publicScalar_iIndep d hd).indepFun
          (i := sR) (j := sI) (by simp [sR, sI])
        have hpair := (indepFun_iff_hasLaw_prodMk_prod hsR hsI).mp hind
        rw [show canonicalUpperPairMeasure d hd
            ⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ =
            (gaussianReal 0 ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩).prod
            (gaussianReal 0 ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩) by
          simp [canonicalUpperPairMeasure, entryVariance,
            Fin.ext_iff, heqv]]
        refine hpair.congr ?_
        filter_upwards with x
        have hne : a ≠ b := by
          intro hab
          exact heqv (congrArg Fin.val hab)
        have hlt' : a < b := hlt
        calc
          _ = publicBlockUpperCoordinates (publicBlocksFromScalars x)
              ⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ :=
            publicUpperPairOfPacket_eq d x _
          _ = (x sR, x sI) := by
            simp [sR, sI, publicBlockUpperCoordinates, publicBlocksFromScalars,
              publicBlockDiagonal, publicBlockDiagonalRaw, publicBlockCoordinates,
              hermitianGUEBlock, hermitianOfFinCoordinates,
              hermitianOfCoordinates, hermitianMatrixOfCoordinates,
              hermitianUpperEntry, hne, hlt']
      · have hba : b.val < a.val :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heqv)
        let sR : PublicScalarIndex d := ⟨j, .inr (.inl ⟨(b, a), hba⟩)⟩
        let sI : PublicScalarIndex d := ⟨j, .inr (.inr ⟨(b, a), hba⟩)⟩
        have hsR := publicScalar_hasLaw d hd sR
        have hsI := publicScalar_hasLaw d hd sI
        have hvR : publicScalarVariance d hd sR =
            ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩ := by
          simp [sR, publicScalarVariance,
            hermitianGUEFinCoordinateVariance]
          apply NNReal.eq
          rfl
        have hvI : publicScalarVariance d hd sI =
            ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩ := by
          simp [sI, publicScalarVariance,
            hermitianGUEFinCoordinateVariance]
          apply NNReal.eq
          rfl
        rw [hvR] at hsR
        rw [hvI] at hsI
        have hsInegRaw := gaussianReal_neg hsI
        have hsIneg : HasLaw (fun x : PublicScalarSample d => -x sI)
            (gaussianReal 0 ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩)
            (publicScalarMeasure d hd) := by
          have hcongr : HasLaw (fun x : PublicScalarSample d => -x sI)
              (gaussianReal (-0) ⟨(1 / (d j : ℝ)) / 2,
                div_nonneg (one_div_nonneg.mpr
                  (by exact_mod_cast (hd j).le)) (by norm_num)⟩)
              (publicScalarMeasure d hd) := by
            refine hsInegRaw.congr ?_
            filter_upwards with x
            simp only [Pi.neg_apply]
          simpa only [neg_zero] using hcongr
        have hind := (publicScalar_iIndep d hd).indepFun
          (i := sR) (j := sI) (by simp [sR, sI])
        have hindNeg : IndepFun (fun x : PublicScalarSample d => x sR)
            (fun x : PublicScalarSample d => -x sI)
            (publicScalarMeasure d hd) := by
          simpa only [Function.comp_def, id_eq] using
            hind.comp measurable_id (by fun_prop : Measurable fun r : ℝ => -r)
        have hpair :=
          (indepFun_iff_hasLaw_prodMk_prod hsR hsIneg).mp hindNeg
        rw [show canonicalUpperPairMeasure d hd
            ⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ =
            (gaussianReal 0 ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩).prod
            (gaussianReal 0 ⟨(1 / (d j : ℝ)) / 2,
              div_nonneg (one_div_nonneg.mpr
                (by exact_mod_cast (hd j).le)) (by norm_num)⟩) by
          simp [canonicalUpperPairMeasure, entryVariance,
            Fin.ext_iff, heqv]]
        refine hpair.congr ?_
        filter_upwards with x
        have hne : a ≠ b := by
          intro hab
          exact heqv (congrArg Fin.val hab)
        have hlt' : ¬ a < b := hlt
        calc
          _ = publicBlockUpperCoordinates (publicBlocksFromScalars x)
              ⟨(⟨j, a⟩, ⟨j, b⟩), hq⟩ :=
            publicUpperPairOfPacket_eq d x _
          _ = (x sR, -x sI) := by
            simp [sR, sI, publicBlockUpperCoordinates, publicBlocksFromScalars,
              publicBlockDiagonal, publicBlockDiagonalRaw, publicBlockCoordinates,
              hermitianGUEBlock, hermitianOfFinCoordinates,
              hermitianOfCoordinates, hermitianMatrixOfCoordinates,
              hermitianUpperEntry, hne, hlt']
  · have hc : HasLaw (fun _ : PublicScalarSample d => ((0, 0) : UpperRealPair))
        (Measure.dirac (0, 0)) (publicScalarMeasure d hd) := by
      refine ⟨measurable_const.aemeasurable, ?_⟩
      simp
    rw [show canonicalUpperPairMeasure d hd
        ⟨(⟨j, a⟩, ⟨j', b⟩), hq⟩ = Measure.dirac (0, 0) by
      simp [canonicalUpperPairMeasure, hb]]
    convert hc using 1
    funext x
    simp [publicUpperPairOfPacket, hb]

/-- Regrouping the flattened public GUE scalars by sigma-ordered upper entries
has exactly the canonical finite product law. -/
theorem hasLaw_publicUpperCoordinates_fromScalars {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    HasLaw
      (fun x : PublicScalarSample d =>
        fun q => publicUpperPairOfPacket d q (fun s => x s))
      (canonicalUpperCoordinateMeasure d hd)
      (publicScalarMeasure d hd) := by
  unfold canonicalUpperCoordinateMeasure
  exact (publicUpperPair_iIndep d hd).hasLaw_pi
    (publicUpperPair_hasLaw d hd)

/-- The canonical sigma-ordered upper-coordinate product is the
pushforward of the public product of normalized Hermitian GUE blocks.  This
identity includes reversed strict-upper orientations, diagonal imaginary
zeros, and deterministic cross-block zeros. -/
theorem canonicalUpperCoordinateMeasure_eq_map_publicBlockUpperCoordinates
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    canonicalUpperCoordinateMeasure d hd =
      Measure.map publicBlockUpperCoordinates
        (publicBlockProductMeasure d hd) := by
  have hblocks : Measurable (@publicBlocksFromScalars k d) :=
    (measurable_publicBlocks_reconstruction d).comp
      (measurable_publicBlockCoordinates_fromScalars d)
  rw [← (hasLaw_publicUpperCoordinates_fromScalars d hd).map_eq]
  rw [← map_publicBlocksFromScalars_eq_publicBlockProductMeasure d hd]
  rw [Measure.map_map (measurable_publicBlockUpperCoordinates d) hblocks]
  apply Measure.map_congr
  filter_upwards with x
  funext q
  exact publicUpperPairOfPacket_eq d x q

/-- The executable canonical normalized block-GUE matrix law is exactly the
block-diagonal assembly of the public product of the laws
`GUE (d j) (1 / d j)`. -/
theorem canonicalMatrixMeasure_eq_publicBlockProductMatrixMeasure
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    canonicalMatrixMeasure d hd =
      publicBlockProductMatrixMeasure d hd := by
  unfold canonicalMatrixMeasure
  rw [canonicalUpperCoordinateMeasure_eq_map_publicBlockUpperCoordinates d hd]
  exact (publicBlockProductMatrixMeasure_eq_map_upperCoordinates d hd).symm

/-- Deterministic Hermitian deformation preserves the exact identification
between the canonical normalized block-GUE law and the public block-product
law. -/
theorem map_deformation_canonicalMatrixMeasure_eq_public
    {k : ℕ} (d : Fin k → ℕ) (hd : ∀ j, 0 < d j)
    (A₀ : HermitianMatrix (Index d)) :
    Measure.map (fun H : HermitianMatrix (Index d) =>
      (⟨A₀.1 + H.1, A₀.2.add H.2⟩ : HermitianMatrix (Index d)))
        (canonicalMatrixMeasure d hd) =
      publicDeformedBlockProductMeasure d hd A₀ := by
  rw [canonicalMatrixMeasure_eq_publicBlockProductMatrixMeasure d hd]
  rfl

/-- Every deterministic deformation has exactly the deformed public
block-product law. -/
theorem Law.hasLaw_deformed_publicBlockProduct {k : ℕ}
    {d : Fin k → ℕ} {hd : ∀ j, 0 < d j} (M : Law d hd)
    (A₀ : HermitianMatrix (Index d)) :
    HasLaw (BlockGUE.deformed M A₀)
      (publicDeformedBlockProductMeasure d hd A₀) M.P := by
  rw [← map_deformation_canonicalMatrixMeasure_eq_public d hd A₀]
  exact M.hasLaw_deformed_canonical A₀

end BlockGUE
end PSSSNative.BlockBand
