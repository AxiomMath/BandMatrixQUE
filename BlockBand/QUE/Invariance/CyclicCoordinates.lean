module

public import BlockBand.QUE.Invariance.SignedGaussian

/-!
# Orientation-correct reindexing of the physical Gaussian coordinates

A site permutation acts on the real Gaussian coordinates by reindexing the site pairs while keeping
the upper/lower orientation, negating the imaginary coefficient when the orientation reverses;
this preserves the coordinate variances and reconstructs the reindexed matrix
(`gaussianReconstruction_oriented`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory

/-- Reindex a pair while preserving its original upper/lower orientation.
Thus even redundant zero labels form a permutation. -/
def orientedSitePair (p : BlockBand.Parameters) (e : p.Site ≃ p.Site)
    (x y : p.Site) : p.Site × p.Site :=
  if (p.siteIndex x < p.siteIndex y ↔ p.siteIndex (e x) < p.siteIndex (e y))
  then (e x, e y) else (e y, e x)

theorem orientedSitePair_injective (p : BlockBand.Parameters) (e : p.Site ≃ p.Site) :
    Function.Injective (fun xy : p.Site × p.Site => p.orientedSitePair e xy.1 xy.2) := by
  rintro ⟨x,y⟩ ⟨a,b⟩ h
  dsimp only at h
  unfold orientedSitePair at h
  split_ifs at h with hxy hab hab
  · exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))
  · have hx : x = b := e.injective (congrArg Prod.fst h)
    have hy : y = a := e.injective (congrArg Prod.snd h)
    subst b; subst a
    have hne : x ≠ y := by intro he; subst y; simp at hab
    have hi : p.siteIndex x ≠ p.siteIndex y := fun he => hne (p.siteIndex_injective he)
    have hj : p.siteIndex (e x) ≠ p.siteIndex (e y) :=
      fun he => hne (e.injective (p.siteIndex_injective he))
    exact False.elim (hab (by omega))
  · have hx : y = a := e.injective (congrArg Prod.fst h)
    have hy : x = b := e.injective (congrArg Prod.snd h)
    subst a; subst b
    have hne : x ≠ y := by intro he; subst y; simp at hxy
    have hi : p.siteIndex x ≠ p.siteIndex y := fun he => hne (p.siteIndex_injective he)
    have hj : p.siteIndex (e x) ≠ p.siteIndex (e y) :=
      fun he => hne (e.injective (p.siteIndex_injective he))
    exact False.elim (hxy (by omega))
  · exact Prod.ext (e.injective (congrArg Prod.snd h)) (e.injective (congrArg Prod.fst h))

/-- Coordinate label reindexing, without the imaginary sign. -/
def orientedGaussianCoordinate (p : BlockBand.Parameters) (e : p.Site ≃ p.Site) :
    p.GaussianCoordinate → p.GaussianCoordinate
  | .inl x => .inl (e x)
  | .inr (x,y,b) => .inr ((p.orientedSitePair e x y).1, (p.orientedSitePair e x y).2,b)

theorem orientedGaussianCoordinate_injective (p : BlockBand.Parameters)
    (e : p.Site ≃ p.Site) : Function.Injective (p.orientedGaussianCoordinate e) := by
  intro i j h
  cases i with
  | inl x =>
    cases j with
    | inl y => exact congrArg Sum.inl (e.injective (Sum.inl.inj h))
    | inr xy => contradiction
  | inr xy =>
    cases j with
    | inl y => contradiction
    | inr ab =>
      rcases xy with ⟨x,y,b⟩
      rcases ab with ⟨a,c,d⟩
      have hh := Sum.inr.inj h
      have hp : p.orientedSitePair e x y = p.orientedSitePair e a c :=
        Prod.ext (congrArg (fun t : p.Site × p.Site × Bool => t.1) hh)
          (congrArg (fun t : p.Site × p.Site × Bool => t.2.1) hh)
      have he : (x,y) = (a,c) := p.orientedSitePair_injective e hp
      have hb := congrArg (fun t => t.2.2) hh
      cases he
      cases hb
      rfl

/-- The coordinate-label equivalence of a site permutation. -/
def orientedGaussianEquiv (p : BlockBand.Parameters) (e : p.Site ≃ p.Site) :
    p.GaussianCoordinate ≃ p.GaussianCoordinate :=
  (⟨p.orientedGaussianCoordinate e, p.orientedGaussianCoordinate_injective e⟩ :
    p.GaussianCoordinate ↪ p.GaussianCoordinate).equivOfFiniteSelfEmbedding

/-- Only the imaginary coefficient is negated when source orientation reverses. -/
def orientedGaussianNegate (p : BlockBand.Parameters) (e : p.Site ≃ p.Site) :
    p.GaussianCoordinate → Bool
  | .inl _ => false
  | .inr (x,y,b) => b && decide (p.siteIndex (e y) < p.siteIndex (e x))

@[simp] theorem orientedGaussianEquiv_apply (p : BlockBand.Parameters)
    (e : p.Site ≃ p.Site) (i : p.GaussianCoordinate) :
    p.orientedGaussianEquiv e i = p.orientedGaussianCoordinate e i := rfl

/-- Component variances are preserved, including all zero labels. -/
theorem gaussianCoordinateVariance_orientedGaussianEquiv (p : BlockBand.Parameters)
    (e : p.Site ≃ p.Site)
    (hvar : ∀ x y, p.entryVariance (e x) (e y) = p.entryVariance x y)
    (hsym : ∀ x y, p.entryVariance y x = p.entryVariance x y)
    (i : p.GaussianCoordinate) :
    p.gaussianCoordinateVariance (p.orientedGaussianEquiv e i) =
      p.gaussianCoordinateVariance i := by
  cases i with
  | inl x =>
    apply NNReal.eq
    change p.entryVariance (e x) (e x) = p.entryVariance x x
    exact hvar x x
  | inr xy =>
    rcases xy with ⟨x,y,b⟩
    by_cases hxy : p.siteIndex x < p.siteIndex y
    · by_cases hexy : p.siteIndex (e x) < p.siteIndex (e y)
      · apply NNReal.eq
        simp [orientedGaussianCoordinate, orientedSitePair, gaussianCoordinateVariance,
          hxy, hexy, hvar]
      · have hne : x ≠ y := fun h => by subst y; omega
        have he : p.siteIndex (e x) ≠ p.siteIndex (e y) :=
          fun h => hne (e.injective (p.siteIndex_injective h))
        have heyx : p.siteIndex (e y) < p.siteIndex (e x) := by omega
        apply NNReal.eq
        simp [orientedGaussianCoordinate, orientedSitePair, gaussianCoordinateVariance,
          hxy, hexy, heyx, hvar, hsym]
    · by_cases hexy : p.siteIndex (e x) < p.siteIndex (e y)
      · have heyn : ¬p.siteIndex (e y) < p.siteIndex (e x) := by omega
        simp [orientedGaussianCoordinate, orientedSitePair, gaussianCoordinateVariance,
          hxy, hexy, heyn]
      · simp [orientedGaussianCoordinate, orientedSitePair, gaussianCoordinateVariance,
          hxy, hexy]

/-- The signed reindexing reconstructs the reindexed matrix, at every coordinate vector. -/
theorem gaussianReconstruction_oriented (p : BlockBand.Parameters)
    (e : p.Site ≃ p.Site) (z : p.GaussianCoordinate → ℝ) :
    p.gaussianReconstruction
      (p.signedGaussianPermutation (p.orientedGaussianEquiv e) (p.orientedGaussianNegate e) z) =
      fun x y => p.gaussianReconstruction z (e x) (e y) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [gaussianReconstruction, signedGaussianPermutation, orientedGaussianNegate,
      orientedGaussianCoordinate]
  · have hyx : y ≠ x := Ne.symm hxy
    have hexy : e x ≠ e y := fun h => hxy (e.injective h)
    have heyx : e y ≠ e x := Ne.symm hexy
    have hi : p.siteIndex x ≠ p.siteIndex y := fun h => hxy (p.siteIndex_injective h)
    have hj : p.siteIndex (e x) ≠ p.siteIndex (e y) :=
      fun h => hexy (p.siteIndex_injective h)
    by_cases hlt : p.siteIndex x < p.siteIndex y
    all_goals
      by_cases helt : p.siteIndex (e x) < p.siteIndex (e y)
      all_goals
        have hylt : (p.siteIndex y < p.siteIndex x) ↔ ¬ (p.siteIndex x < p.siteIndex y) := by omega
        have heylt : (p.siteIndex (e y) < p.siteIndex (e x)) ↔
            ¬ (p.siteIndex (e x) < p.siteIndex (e y)) := by omega
        simp [gaussianReconstruction, signedGaussianPermutation, orientedGaussianNegate,
          orientedGaussianCoordinate, orientedSitePair, hxy, hexy,
          hlt, helt, hylt, heylt] <;> ring

end BlockBand.Parameters
