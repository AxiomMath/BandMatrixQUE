module

public import BlockBand.Native.Johansson.Defs

/-!
# Johansson's formula (2.18): the coordinate bridge

The law `matrixMeasure S d` is built from independent upper coordinate pairs
(`coordinateMeasure N S`, indexed by `UpperPair N`), while the eigenvalue density is computed
with the real coordinate law `hermGaussian N S` on `HermCoord N → ℝ`. This module proves:

* `gaussianMatrixRaw_eq_hermOfCoord`: `gaussianMatrixRaw z = hermOfCoord (coordOfPair z)` for the
  explicit coordinate map `coordOfPair` (`(a,a) ↦ z(a,a).1`, `(a,b) ↦ z(a,b).1` and
  `(b,a) ↦ z(a,b).2` for `a < b`; the second coordinate of a diagonal pair is ignored);
* `map_coordOfPair`: `Measure.map coordOfPair (coordinateMeasure N S) = hermGaussian N S`;
* `spectralTuple_refl`: `spectralTuple (Equiv.refl _).toEmbedding A i = freshEigenvalue A.1 i`;
* **`coordinateBridge_holds : CoordinateBridgeStatement`**.

Domain: every `N`, every `S : ℝ≥0` (including `0`), every `d`, every measurable `g ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory
open BlockBand.External.Johansson
open BlockBand.Internal.Contracts.CoareaPalm (freshEigenvalue)
open BlockBand.DeterminantScore.Sector (HermCoord hermOfCoord hermGaussian hermVariance)
open scoped ENNReal NNReal BigOperators

section Coordinates

variable {N : ℕ}

/-- The upper pair owning the real coordinate `c`: the sorted pair. -/
def coordOwner (c : HermCoord N) : UpperPair N :=
  if h : c.1 ≤ c.2 then ⟨c, h⟩ else ⟨c.swap, le_of_not_ge h⟩

/-- The component of the owning pair read by the coordinate `c`: the first one on and above the
diagonal, the second one below. -/
def coordSelect (c : HermCoord N) (p : ℝ × ℝ) : ℝ :=
  if c.1 ≤ c.2 then p.1 else p.2

/-- The coordinate map `φ` from upper pairs to real coordinates. -/
def coordOfPair (z : UpperPair N → ℝ × ℝ) : HermCoord N → ℝ :=
  fun c => coordSelect c (z (coordOwner c))

theorem measurable_coordOfPair : Measurable (coordOfPair (N := N)) := by
  refine measurable_pi_iff.mpr fun c => ?_
  unfold coordOfPair coordSelect
  split_ifs
  · exact measurable_fst.comp (measurable_pi_apply _)
  · exact measurable_snd.comp (measurable_pi_apply _)

theorem coordOwner_of_le {a b : Fin N} (h : a ≤ b) : coordOwner (a, b) = ⟨(a, b), h⟩ := by
  simp [coordOwner, h]

theorem coordOwner_of_lt {a b : Fin N} (h : a < b) : coordOwner (b, a) = ⟨(a, b), h.le⟩ := by
  simp [coordOwner, not_le.mpr h]

theorem coordOfPair_of_le (z : UpperPair N → ℝ × ℝ) {a b : Fin N} (h : a ≤ b) :
    coordOfPair z (a, b) = (z ⟨(a, b), h⟩).1 := by
  simp [coordOfPair, coordSelect, coordOwner_of_le h, h]

theorem coordOfPair_of_lt (z : UpperPair N → ℝ × ℝ) {a b : Fin N} (h : a < b) :
    coordOfPair z (b, a) = (z ⟨(a, b), h.le⟩).2 := by
  simp [coordOfPair, coordSelect, coordOwner_of_lt h, not_le.mpr h]

/-- **The matrices agree**: `gaussianMatrixRaw z = hermOfCoord (φ z)`. -/
theorem gaussianMatrixRaw_eq_hermOfCoord (z : UpperPair N → ℝ × ℝ) :
    gaussianMatrixRaw z = hermOfCoord (coordOfPair z) := by
  ext i j
  unfold gaussianMatrixRaw hermOfCoord
  by_cases hij : i = j
  · subst hij
    simp [coordOfPair_of_le z (le_refl i)]
  · by_cases hle : i ≤ j
    · have hlt : i < j := lt_of_le_of_ne hle hij
      simp [hij, hle, hlt, complexPair, coordOfPair_of_le z hle, coordOfPair_of_lt z hlt]
    · have hlt : j < i := lt_of_not_ge hle
      have hnlt : ¬ i < j := fun h => hle h.le
      simp [hij, hle, hnlt, complexPair, coordOfPair_of_le z hlt.le, coordOfPair_of_lt z hlt]
      ring

/-- The fibre of `coordOwner` over an upper pair `(a, b)` is `{(a, b), (b, a)}`. -/
theorem coordOwner_eq_iff (c : HermCoord N) (q : UpperPair N) :
    coordOwner c = q ↔ c = q.1 ∨ c = q.1.swap := by
  obtain ⟨⟨a, b⟩, hab⟩ := q
  obtain ⟨x, y⟩ := c
  unfold coordOwner
  by_cases hxy : x ≤ y
  · simp only [hxy, ↓reduceDIte, Subtype.mk.injEq, Prod.mk.injEq, Prod.swap_prod_mk]
    constructor
    · intro h
      exact Or.inl h
    · rintro (h | ⟨rfl, rfl⟩)
      · exact h
      · exact ⟨le_antisymm hxy hab, le_antisymm hab hxy⟩
  · simp only [hxy, ↓reduceDIte, Subtype.mk.injEq, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · intro h
      exact Or.inr ⟨h.2, h.1⟩
    · rintro (⟨rfl, rfl⟩ | h)
      · exact absurd hab hxy
      · exact ⟨h.2, h.1⟩

theorem coordOwner_fibre_diag (a : Fin N) :
    Finset.univ.filter (fun c : HermCoord N => coordOwner c = ⟨(a, a), le_refl a⟩) =
      {(a, a)} := by
  ext c
  simp [coordOwner_eq_iff]

theorem coordOwner_fibre_lt {a b : Fin N} (h : a < b) :
    Finset.univ.filter (fun c : HermCoord N => coordOwner c = ⟨(a, b), h.le⟩) =
      {(a, b), (b, a)} := by
  ext c
  simp [coordOwner_eq_iff]

/-- The set of pairs `p` whose selected components lie in the boxes of the fibre over `q`. -/
def pairSet (s : HermCoord N → Set ℝ) (q : UpperPair N) : Set (ℝ × ℝ) :=
  {p | ∀ c, coordOwner c = q → coordSelect c p ∈ s c}

theorem preimage_coordOfPair_pi (s : HermCoord N → Set ℝ) :
    coordOfPair ⁻¹' Set.univ.pi s = Set.univ.pi (fun q => pairSet s q) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_univ_pi, coordOfPair, pairSet, Set.mem_ofPred_eq]
  constructor
  · intro h q c hc
    subst hc
    exact h c
  · intro h c
    exact h _ c rfl

theorem upperEntryMeasure_pairSet (S : ℝ≥0) (s : HermCoord N → Set ℝ)
    (hs : ∀ c, MeasurableSet (s c)) (q : UpperPair N) :
    upperEntryMeasure S q (pairSet s q) =
      ∏ c ∈ Finset.univ.filter (fun c => coordOwner c = q),
        gaussianReal 0 (hermVariance N S c) (s c) := by
  obtain ⟨⟨a, b⟩, hab⟩ := q
  dsimp only at hab
  rcases eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    rw [coordOwner_fibre_diag, Finset.prod_singleton]
    have hset : pairSet s ⟨(a, a), le_refl a⟩ = Prod.fst ⁻¹' s (a, a) := by
      ext p
      simp only [pairSet, coordOwner_eq_iff, Prod.swap_prod_mk, or_self, Set.mem_ofPred_eq,
        Set.mem_preimage]
      constructor
      · intro h
        simpa [coordSelect] using h (a, a) rfl
      · rintro h c rfl
        simpa [coordSelect] using h
    simp only [hset, upperEntryMeasure, ↓reduceIte]
    rw [Measure.map_apply (by fun_prop) (measurable_fst (hs (a, a)))]
    simp [hermVariance]
    rfl
  · have hne : (a, b) ≠ (b, a) := by
      intro h
      exact (ne_of_lt hab') (Prod.mk.inj h).1
    rw [coordOwner_fibre_lt hab', Finset.prod_pair hne]
    have hset : pairSet s ⟨(a, b), hab⟩ = s (a, b) ×ˢ s (b, a) := by
      ext p
      simp only [pairSet, coordOwner_eq_iff, Prod.swap_prod_mk, Set.mem_ofPred_eq,
        Set.mem_prod]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [coordSelect, hab] using h (a, b) (Or.inl rfl)
        · simpa [coordSelect, not_le.mpr hab'] using h (b, a) (Or.inr rfl)
      · rintro ⟨h1, h2⟩ c (rfl | rfl)
        · simpa [coordSelect, hab] using h1
        · simpa [coordSelect, not_le.mpr hab'] using h2
    simp only [hset, upperEntryMeasure, ne_of_lt hab', ↓reduceIte, Measure.prod_prod]
    simp [hermVariance, ne_of_lt hab', (ne_of_lt hab').symm]

/-- **The laws agree**: `Measure.map φ (coordinateMeasure N S) = hermGaussian N S`. -/
theorem map_coordOfPair (S : ℝ≥0) :
    Measure.map (coordOfPair (N := N)) (coordinateMeasure N S) = hermGaussian N S := by
  have : ∀ q : UpperPair N, IsProbabilityMeasure (upperEntryMeasure S q) :=
    upperEntryMeasure_probability S
  symm
  unfold hermGaussian BlockBand.Internal.Contracts.Inputs.gaussianProduct
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_coordOfPair (MeasurableSet.univ_pi hs),
    preimage_coordOfPair_pi, coordinateMeasure, Measure.pi_pi,
    ← Finset.prod_fiberwise Finset.univ coordOwner]
  exact Finset.prod_congr rfl fun q _ => upperEntryMeasure_pairSet S s hs q

end Coordinates

/-- The identity-rank spectral tuple is the increasing eigenvalue `freshEigenvalue`. -/
theorem spectralTuple_refl {N : ℕ} (A : HermitianMatrix N) :
    spectralTuple (Equiv.refl (Fin N)).toEmbedding A = fun i => freshEigenvalue A.1 i := by
  funext i
  exact (BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ _ A.2).symm

/-- **The coordinate bridge.** -/
theorem coordinateBridge_holds : CoordinateBridgeStatement := by
  intro N S d g hg
  have hmeas : Measurable fun A : HermitianMatrix N =>
      g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) :=
    hg.comp (measurable_spectralTuple _)
  have hmeas' : Measurable fun x : HermCoord N → ℝ =>
      g (BlockBand.DeterminantScore.orderedEigs (Matrix.diagonal fun i => (d i : ℂ)) x) :=
    hg.comp (BlockBand.DeterminantScore.NegativeSpread.measurable_orderedEigs _)
  rw [matrixMeasure, lintegral_map hmeas (measurable_deformedMatrix d), ← map_coordOfPair S,
    lintegral_map hmeas' measurable_coordOfPair]
  refine lintegral_congr fun z => ?_
  rw [spectralTuple_refl]
  simp only [deformedMatrix, gaussianMatrix, gaussianMatrixRaw_eq_hermOfCoord]
  rfl

end BlockBand.Native.Johansson
