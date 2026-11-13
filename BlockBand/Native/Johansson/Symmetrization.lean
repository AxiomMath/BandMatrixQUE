module

public import BlockBand.Native.Johansson.Defs

/-!
# Johansson's formula (2.18): factorial measures from the ordered law

Let `ν` be the law of the increasing spectrum under `matrixMeasure S d`, and assume
`ν = 1_𝒞 f dλ` with `f` symmetric (`𝒞 = weylChamber N`). This module proves:

* (a) `sum_perm_setLIntegral_chamber`: `Σ_σ ∫_𝒞 G(x ∘ σ) f(x) dx = ∫ G f`, for measurable `G ≥ 0`
  (ties `{x_i = x_j}` are Lebesgue-null, `volume_tie`, and every injective tuple has exactly one
  sorting permutation, `filter_strictMono_comp_perm`);
* (b) `sum_perm_restrict`: `Σ_σ F(σ ∘ castLE) = (N-k)! • Σ_e F(e)` over embeddings
  `e : Fin k ↪ Fin N`, since every fibre has `(N-k)!` elements (`card_fibre_permRestrict`);
* (c) `lintegral_proj_mul`: `∫ G(x ∘ castLE) f(x) dx = ∫ G(x) (∫ f(appendCast x y) dy) dx`,
  through the measure-preserving `appendCast` (`measurePreserving_appendCast`) and Tonelli;
* **`factorialFromOrdered_holds : FactorialFromOrderedStatement`**.

Domain: every `N`, `S`, `d`, every `k ≤ N` (including `k = 0` and `k = N`), every measurable
symmetric `f : (Fin N → ℝ) → ℝ≥0∞` for which the ordered-law hypothesis holds.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory
open BlockBand.External.Johansson
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber isOpen_weylChamber)
open scoped ENNReal NNReal BigOperators

/-!
## (a) Symmetrization over the permuted chambers
-/

section Symmetrize

variable {N : ℕ}

/-- Permuting the coordinates preserves Lebesgue measure. -/
theorem lintegral_comp_perm (σ : Equiv.Perm (Fin N)) (H : (Fin N → ℝ) → ℝ≥0∞) :
    ∫⁻ x, H (x ∘ σ) = ∫⁻ y, H y := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) σ.symm
  have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ.symm) = fun x => x ∘ σ := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have h := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) H
  rw [hcoe] at h
  exact h

theorem measurable_comp_perm (σ : Equiv.Perm (Fin N)) :
    Measurable fun x : Fin N → ℝ => x ∘ σ :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- A tie `{x_i = x_j}`, `i ≠ j`, is Lebesgue-null. -/
theorem volume_tie {i j : Fin N} (hij : i ≠ j) :
    (volume : Measure (Fin N → ℝ)) {x | x i = x j} = 0 := by
  let L : (Fin N → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j
  have hs : {x : Fin N → ℝ | x i = x j} = (LinearMap.ker L : Set (Fin N → ℝ)) := by
    ext x
    simp [L, sub_eq_zero]
  rw [hs]
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have : Pi.single i (1 : ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  simp [L, hij.symm] at this

/-- Almost every tuple has distinct coordinates. -/
theorem ae_injective : ∀ᵐ y ∂(volume : Measure (Fin N → ℝ)), Function.Injective y := by
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {x : Fin N → ℝ | x i = x j})
    ?_ (measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => volume_tie hij)
  intro y hy
  simp only [Function.Injective, not_forall] at hy
  obtain ⟨i, j, hyij, hne⟩ := hy
  simp only [Set.mem_iUnion]
  exact ⟨i, j, hne, hyij⟩

/-- An injective tuple has exactly one sorting permutation. -/
theorem filter_strictMono_comp_perm (y : Fin N → ℝ) (hy : Function.Injective y) :
    Finset.univ.filter (fun τ : Equiv.Perm (Fin N) => StrictMono (y ∘ τ)) = {Tuple.sort y} := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    rw [Tuple.eq_sort_iff]
    exact ⟨h.monotone, fun i j hij hfij => absurd hfij (h hij).ne⟩
  · rintro rfl
    exact (Tuple.monotone_sort y).strictMono_of_injective (hy.comp (Tuple.sort y).injective)

/-- The permuted chambers cover each injective tuple exactly once. -/
theorem sum_indicator_chamber (y : Fin N → ℝ) (hy : Function.Injective y) :
    ∑ σ : Equiv.Perm (Fin N), (weylChamber N).indicator (1 : (Fin N → ℝ) → ℝ≥0∞) (y ∘ ⇑σ⁻¹) =
      1 := by
  refine (Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin N)))
    (fun τ => (weylChamber N).indicator (1 : (Fin N → ℝ) → ℝ≥0∞) (y ∘ ⇑τ))).trans ?_
  have h : ∀ τ : Equiv.Perm (Fin N),
      (weylChamber N).indicator (1 : (Fin N → ℝ) → ℝ≥0∞) (y ∘ ⇑τ) =
        if StrictMono (y ∘ ⇑τ) then 1 else 0 := by
    intro τ
    by_cases hτ : StrictMono (y ∘ ⇑τ)
    · rw [Set.indicator_of_mem (show y ∘ ⇑τ ∈ weylChamber N from hτ)]
      simp [hτ]
    · rw [Set.indicator_of_notMem (show y ∘ ⇑τ ∉ weylChamber N from hτ)]
      simp [hτ]
  simp_rw [h]
  rw [Finset.sum_boole, filter_strictMono_comp_perm y hy, Finset.card_singleton, Nat.cast_one]

theorem measurableSet_weylChamber : MeasurableSet (weylChamber N) :=
  isOpen_weylChamber.measurableSet

/-- One permuted chamber, after the change of variables `y = x ∘ σ`. -/
theorem setLIntegral_chamber_comp_perm (f : (Fin N → ℝ) → ℝ≥0∞)
    (hsymm : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x)
    (G : (Fin N → ℝ) → ℝ≥0∞) (σ : Equiv.Perm (Fin N)) :
    ∫⁻ x in weylChamber N, G (x ∘ σ) * f x =
      ∫⁻ y, (weylChamber N).indicator 1 (y ∘ ⇑σ⁻¹) * (G y * f y) := by
  rw [← lintegral_indicator measurableSet_weylChamber]
  refine Eq.trans ?_ (lintegral_comp_perm σ
    (fun y => (weylChamber N).indicator 1 (y ∘ ⇑σ⁻¹) * (G y * f y)))
  refine lintegral_congr fun x => ?_
  have hx : (x ∘ ⇑σ) ∘ ⇑σ⁻¹ = x := by
    funext i
    simp
  rw [hx, hsymm σ x]
  by_cases hxC : x ∈ weylChamber N <;> simp [hxC]

/-- **(a)**: the permuted chambers of a symmetric density reassemble the full density. -/
theorem sum_perm_setLIntegral_chamber (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hsymm : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x)
    (G : (Fin N → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∑ σ : Equiv.Perm (Fin N), ∫⁻ x in weylChamber N, G (x ∘ σ) * f x = ∫⁻ x, G x * f x := by
  have hmeas : ∀ σ : Equiv.Perm (Fin N), Measurable fun y : Fin N → ℝ =>
      (weylChamber N).indicator 1 (y ∘ ⇑σ⁻¹) * (G y * f y) := fun σ =>
    ((measurable_one.indicator measurableSet_weylChamber).comp
      (measurable_comp_perm σ⁻¹)).mul (hG.mul hf)
  simp_rw [setLIntegral_chamber_comp_perm f hsymm G]
  rw [← lintegral_finsetSum _ fun σ _ => hmeas σ]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_injective] with y hy
  rw [← Finset.sum_mul, sum_indicator_chamber y hy, one_mul]

end Symmetrize

/-!
## (b) Counting the permutation extensions of an embedding
-/

section Counting

variable {k N : ℕ}

/-- `σ ∘ castLE` as an embedding `Fin k ↪ Fin N`. -/
def permRestrict (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) : Fin k ↪ Fin N :=
  (Fin.castLEEmb hk).trans σ.toEmbedding

theorem permRestrict_apply (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) (i : Fin k) :
    permRestrict hk σ i = σ (Fin.castLE hk i) := rfl

/-- All fibres of `permRestrict` have the cardinality of the fibre over `castLE`. -/
theorem card_fibre_eq (hk : k ≤ N) (e : Fin k ↪ Fin N) :
    (Finset.univ.filter fun σ => permRestrict hk σ = e).card =
      (Finset.univ.filter fun σ => permRestrict hk σ = Fin.castLEEmb hk).card := by
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hk) e
    (Fin.castLE_injective hk) e.injective
  have hiff : ∀ σ : Equiv.Perm (Fin N),
      permRestrict hk (τ * σ) = e ↔ permRestrict hk σ = Fin.castLEEmb hk := by
    intro σ
    simp only [DFunLike.ext_iff, permRestrict_apply, Equiv.Perm.mul_apply, Fin.castLEEmb_apply]
    refine forall_congr' fun i => ?_
    rw [← hτ i]
    exact τ.injective.eq_iff
  refine Finset.card_nbij' (fun σ => τ⁻¹ * σ) (fun σ => τ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    rw [← hiff, mul_inv_cancel_left]
    exact hσ
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    exact (hiff σ).mpr hσ
  · intro σ _
    simp
  · intro σ _
    simp

/-- **(b), counting**: each embedding `Fin k ↪ Fin N` has exactly `(N-k)!` permutation
extensions. -/
theorem card_fibre_permRestrict (hk : k ≤ N) (e : Fin k ↪ Fin N) :
    (Finset.univ.filter fun σ => permRestrict hk σ = e).card = (N - k).factorial := by
  set c := (Finset.univ.filter fun σ => permRestrict hk σ = Fin.castLEEmb hk).card
  have hsum : (Finset.univ : Finset (Equiv.Perm (Fin N))).card =
      ∑ e : Fin k ↪ Fin N, (Finset.univ.filter fun σ => permRestrict hk σ = e).card :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
  simp_rw [card_fibre_eq hk] at hsum
  rw [Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_perm,
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin, smul_eq_mul,
    ← Nat.factorial_mul_descFactorial hk] at hsum
  rw [card_fibre_eq hk]
  have hpos : 0 < N.descFactorial k := Nat.descFactorial_pos.mpr hk
  exact (Nat.eq_of_mul_eq_mul_right hpos (hsum.trans (mul_comm _ _))).symm

/-- **(b)**: summing over permutations counts every embedding `(N-k)!` times. -/
theorem sum_perm_restrict {M : Type*} [AddCommMonoid M] (hk : k ≤ N)
    (F : (Fin k ↪ Fin N) → M) :
    ∑ σ : Equiv.Perm (Fin N), F (permRestrict hk σ) = (N - k).factorial • ∑ e, F e := by
  rw [← Finset.sum_fiberwise Finset.univ (permRestrict hk) (fun σ => F (permRestrict hk σ)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => congrArg F (Finset.mem_filter.mp hσ).2, Finset.sum_const,
    card_fibre_permRestrict hk e]

end Counting

/-!
## (c) Marginals of a density on `Fin N → ℝ`
-/

section Marginal

variable {k N : ℕ}

theorem appendCast_eq_piCongrLeft (hk : k ≤ N) (x : Fin k → ℝ) (y : Fin (N - k) → ℝ) :
    appendCast hk x y =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ)
        (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk))))
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (N - k) => ℝ)).symm (x, y)) := by
  funext i
  simp only [appendCast, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    cast_eq, Equiv.symm_trans_apply, finCongr_symm, finCongr_apply]
  generalize Fin.cast _ i = j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) j
  · simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]
  · simp [MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi]

/-- `(x, y) ↦ appendCast hk x y` preserves Lebesgue measure. -/
theorem measurePreserving_appendCast (hk : k ≤ N) :
    MeasurePreserving (fun p : (Fin k → ℝ) × (Fin (N - k) → ℝ) => appendCast hk p.1 p.2)
      ((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin (N - k) → ℝ)))
      (volume : Measure (Fin N → ℝ)) := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ)
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk)))
  have h2 := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin (N - k) => ℝ)
  have h := h1.comp h2
  have hfun : (fun p : (Fin k → ℝ) × (Fin (N - k) → ℝ) => appendCast hk p.1 p.2) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ)
        (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk)))) ∘
        ⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin (N - k) => ℝ)).symm := by
    funext p
    exact appendCast_eq_piCongrLeft hk p.1 p.2
  rw [hfun]
  exact h

theorem measurable_appendCast_uncurry (hk : k ≤ N) :
    Measurable fun p : (Fin k → ℝ) × (Fin (N - k) → ℝ) => appendCast hk p.1 p.2 :=
  (measurePreserving_appendCast hk).measurable

theorem measurable_marginal (hk : k ≤ N) (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun x : Fin k → ℝ => ∫⁻ y : Fin (N - k) → ℝ, f (appendCast hk x y) :=
  (hf.comp (measurable_appendCast_uncurry hk)).lintegral_prod_right'

/-- **(c)**: the marginal of `f dλ` on the first `k` coordinates. -/
theorem lintegral_proj_mul (hk : k ≤ N) (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (G : (Fin k → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G (fun i => z (Fin.castLE hk i)) * f z =
      ∫⁻ x, G x * ∫⁻ y : Fin (N - k) → ℝ, f (appendCast hk x y) := by
  have hproj : Measurable fun z : Fin N → ℝ => fun i : Fin k => z (Fin.castLE hk i) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hm : Measurable fun z : Fin N → ℝ => G (fun i => z (Fin.castLE hk i)) * f z :=
    (hG.comp hproj).mul hf
  refine Eq.trans ((measurePreserving_appendCast hk).lintegral_comp hm).symm ?_
  simp only [appendCast_apply_castLE]
  have hm2 : Measurable fun a : (Fin k → ℝ) × (Fin (N - k) → ℝ) =>
      G a.1 * f (appendCast hk a.1 a.2) :=
    (hG.comp measurable_fst).mul (hf.comp (measurable_appendCast_uncurry hk))
  refine (lintegral_prod _ hm2.aemeasurable).trans ?_
  refine lintegral_congr fun x => ?_
  have hu : Measurable (Function.uncurry (appendCast hk)) := measurable_appendCast_uncurry hk
  have hy : Measurable fun y : Fin (N - k) → ℝ => f (appendCast hk x y) :=
    hf.comp hu.of_uncurry_left
  exact lintegral_const_mul (G x) hy

end Marginal

/-!
## Assembly
-/

/-- `spectralTuple e = (· ∘ e) ∘ spectralTuple id`. -/
theorem spectralTuple_eq_comp {N k : ℕ} (e : Fin k ↪ Fin N) (A : HermitianMatrix N) :
    spectralTuple e A = fun i => spectralTuple (Equiv.refl (Fin N)).toEmbedding A (e i) := rfl

/-- One term of the factorial correlation measure, through the ordered law. -/
theorem map_spectralTuple_apply {N k : ℕ} (S : ℝ≥0) (d : Fin N → ℝ)
    (f : (Fin N → ℝ) → ℝ≥0∞)
    (hord : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ A, g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) ∂matrixMeasure S d =
        ∫⁻ lam in weylChamber N, g lam * f lam)
    (e : Fin k ↪ Fin N) {s : Set (Fin k → ℝ)} (hs : MeasurableSet s) :
    Measure.map (spectralTuple e) (matrixMeasure S d) s =
      ∫⁻ x in weylChamber N, s.indicator 1 (fun i => x (e i)) * f x := by
  have hrestr : Measurable fun x : Fin N → ℝ => fun i : Fin k => x (e i) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs)
    (measurable_spectralTuple e)]
  exact hord _ ((measurable_one.indicator hs).comp hrestr)

/-- `(N-k)! · ρ_k(s) = ∫_s ∫ f(appendCast x y) dy dx`. -/
theorem factorial_mul_factorialCorrelationMeasure {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ)
    (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hsymm : ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x)
    (hord : ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ A, g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) ∂matrixMeasure S d =
        ∫⁻ lam in weylChamber N, g lam * f lam)
    {k : ℕ} (hk : k ≤ N) {s : Set (Fin k → ℝ)} (hs : MeasurableSet s) :
    ((N - k).factorial : ℝ≥0∞) * factorialCorrelationMeasure S d k s =
      ∫⁻ x in s, ∫⁻ y : Fin (N - k) → ℝ, f (appendCast hk x y) := by
  have hG : Measurable fun z : Fin N → ℝ => s.indicator (1 : (Fin k → ℝ) → ℝ≥0∞)
      (fun i => z (Fin.castLE hk i)) :=
    (measurable_one.indicator hs).comp (Measurable.of_eval fun _ => measurable_pi_apply _)
  unfold factorialCorrelationMeasure
  rw [Measure.finsetSum_apply]
  simp_rw [map_spectralTuple_apply S d f hord _ hs]
  rw [← nsmul_eq_mul, ← sum_perm_restrict hk
    (fun e => ∫⁻ x in weylChamber N, s.indicator 1 (fun i => x (e i)) * f x)]
  refine (sum_perm_setLIntegral_chamber f hf hsymm _ hG).trans ?_
  rw [lintegral_proj_mul hk f hf _ (measurable_one.indicator hs), ← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ s <;> simp [hx]

/-- **Factorial measures from the ordered law.** -/
theorem factorialFromOrdered_holds : FactorialFromOrderedStatement := by
  intro N S d f hf hsymm hord k hk
  have hc0 : ((N - k).factorial : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (N - k)).ne'
  have hcT : ((N - k).factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  ext s hs
  rw [withDensity_apply _ hs, lintegral_const_mul _ (measurable_marginal hk f hf),
    ← factorial_mul_factorialCorrelationMeasure S d f hf hsymm hord hk hs, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hcT, one_mul]

end BlockBand.Native.Johansson
