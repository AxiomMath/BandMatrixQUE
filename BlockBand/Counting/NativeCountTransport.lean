module
public import BlockBand.External.PSSS.SourceStatement
public import BlockBand.Model.Construction.OrderedSpectrum
public import BlockBand.Counting.PhysicalCountTransport

/-!
# Measurable eigenvalue counts and finite index transport

Eigenvalue counts `eigenCount A I` of Hermitian matrices in the PSSS interface are
measurable in `A` for Borel `I`, equal the number of real characteristic roots in `I`, and
are invariant under reindexing by an equivalence of index types.  Consequently the
deformed block-GUE matrix and its interval counts are measurable.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Matrix BlockBand.Foundations.Spectral
open BlockBand.External.PSSS
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem measurable_nativeEigenCount (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (fun A : BlockBand.External.PSSS.HermitianMatrix ι => eigenCount A I) := by
  classical
  have heq : (fun A : BlockBand.External.PSSS.HermitianMatrix ι => eigenCount A I) =
      fun A => ∑ i : Fin (Fintype.card ι), if increasingEigenvalue A.2 i ∈ I then 1 else 0 := by
    funext A
    simp [eigenCount, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hI.preimage (BlockBand.Model.Construction.measurable_increasingEigenvalue i))
    measurable_const measurable_const

theorem nativeEigenCount_eq_orderedEigenvalueCount
    (A : BlockBand.External.PSSS.HermitianMatrix ι) (I : Set ℝ) :
    eigenCount A I = orderedEigenvalueCount A.2 I := rfl

def realRootsCount (A : BlockBand.External.PSSS.HermitianMatrix ι) (I : Set ℝ) : ℕ := by
  classical
  exact ((A.1.charpoly.roots.map Complex.re).filter (fun x => x ∈ I)).card

theorem nativeEigenCount_eq_roots_card
    (A : BlockBand.External.PSSS.HermitianMatrix ι) (I : Set ℝ) :
    eigenCount A I = realRootsCount A I := by
  unfold realRootsCount
  classical
  have hr : A.1.charpoly.roots.map Complex.re =
      Multiset.map (fun i => increasingEigenvalue A.2 i) Finset.univ.val := by
    rw [A.2.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def]
    change Multiset.map A.2.eigenvalues₀ Finset.univ.val =
      Multiset.map (A.2.eigenvalues₀ ∘ Fin.revPerm) Finset.univ.val
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [hr, Multiset.filter_map, Multiset.card_map]
  rfl

theorem nativeEigenCount_eq_of_charpoly_eq
    (A : BlockBand.External.PSSS.HermitianMatrix ι)
    (B : BlockBand.External.PSSS.HermitianMatrix κ)
    (h : A.1.charpoly = B.1.charpoly) (I : Set ℝ) :
    eigenCount A I = eigenCount B I := by
  rw [nativeEigenCount_eq_roots_card, nativeEigenCount_eq_roots_card]
  simp only [realRootsCount, h]

def hermitianReindex (e : ι ≃ κ) (A : BlockBand.External.PSSS.HermitianMatrix ι) :
    BlockBand.External.PSSS.HermitianMatrix κ :=
  ⟨Matrix.reindex e e A.1, by
    ext x y
    exact A.2.apply (e.symm x) (e.symm y)⟩

theorem measurable_hermitianReindex (e : ι ≃ κ) :
    Measurable (hermitianReindex e) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (((measurable_pi_apply (e.symm y) : Measurable (fun row : ι → ℂ => row (e.symm y))).comp
    (measurable_pi_apply (e.symm x) : Measurable (fun H : Matrix ι ι ℂ => H (e.symm x)))).comp
    (measurable_subtype_coe : Measurable (Subtype.val : BlockBand.External.PSSS.HermitianMatrix ι → Matrix ι ι ℂ)))

theorem nativeEigenCount_hermitianReindex (e : ι ≃ κ)
    (A : BlockBand.External.PSSS.HermitianMatrix ι) (I : Set ℝ) :
    eigenCount (hermitianReindex e A) I = eigenCount A I := by
  apply nativeEigenCount_eq_of_charpoly_eq
  exact Matrix.charpoly_reindex e A.1

end BlockBand.Counting
namespace BlockBand.External.PSSS
open MeasureTheory
variable {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}

theorem BlockGUE.measurable_deformed (M : BlockGUE.Law d hd)
    (A : HermitianMatrix (BlockGUE.Index d)) : Measurable (BlockGUE.deformed M A) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact measurable_const.add (M.measurable_entry x y)

theorem BlockGUE.measurable_intervalCount (M : BlockGUE.Law d hd)
    (A : HermitianMatrix (BlockGUE.Index d)) (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (BlockGUE.intervalCount M A I) :=
  (BlockBand.Counting.measurable_nativeEigenCount I hI).comp (BlockGUE.measurable_deformed M A)

end BlockBand.External.PSSS
