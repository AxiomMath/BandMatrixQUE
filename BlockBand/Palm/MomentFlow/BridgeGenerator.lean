module

public import BlockBand.Palm.MomentFlow.BridgeRelabel
public import BlockBand.Palm.MomentFlow.PairGenerator
public import BlockBand.Palm.MomentFlow.FlowRates

/-!
# The angular generator on normalized monomials is the moment-flow generator

The pair generator `c_ij{xy(∂_x-∂_y)² + (y-x)(∂_x-∂_y)}` applied to the normalized monomial
`∏ X_h^{ξ_h}/ξ_h!` gives the jump form of the moment-flow generator, with coefficients
`ξ_i(ξ_j+1)` and `ξ_j(ξ_i+1)`.

*Domain:* every `N`, every coupling vector `lam`, every point `X ∈ ℝ^N`, every configuration `ξ`.
Pure finite-dimensional calculus, no measure.

* `angularGenerator_momentMonomial`: `angularGenerator N lam (mono · ξ) X =
  momentGenerator (dysonCoupling N lam) (mono X ·) ξ` (the sum `∑_{i<j}` with Fréchet
  derivatives along `e_i - e_j` equals the sum `∑_{i≠j}` of the moment generator).
* `momentGenerator_comp_equiv`: relabelling of the moment generator by a permutation of labels.
* `angularGenerator_rev`: in increasing labels, for Hermitian `K` with simple spectrum and the
  test function `Y ↦ mono(Y ∘ rev, ξ)`, the angular generator at
  `(dysonEigenvalue N K, dysonOverlap N q K)` is `momentGenerator` with the rates
  `(N(λ_k - λ_l)²)⁻¹` of `flowRate`, acting on `ζ ↦ mono(X, ζ)` with `X_ℓ = N‖q* u_ℓ‖²`.
* `contDiff_momentMonomial`: the test functions are `C^∞` (in particular `C²`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-!
## Line derivatives
-/

theorem hasDerivAt_line_fderiv {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (X v : Fin N → ℝ)
    (t : ℝ) : HasDerivAt (fun s : ℝ => f (X + s • v)) (fderiv ℝ f (X + t • v) v) t := by
  have hline : HasDerivAt (fun s : ℝ => X + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add X
  exact ((hf.differentiable (by simp)) (X + t • v)).hasFDerivAt.comp_hasDerivAt t hline

theorem deriv_line (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (X v : Fin N → ℝ) :
    deriv (fun s : ℝ => f (X + s • v)) 0 = fderiv ℝ f X v := by
  simpa using (hasDerivAt_line_fderiv hf X v 0).deriv

theorem deriv_deriv_line (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (X v : Fin N → ℝ) :
    deriv (deriv (fun s : ℝ => f (X + s • v))) 0 = fderiv ℝ (fderiv ℝ f) X v v := by
  have h1 : deriv (fun s : ℝ => f (X + s • v)) = fun t => fderiv ℝ f (X + t • v) v :=
    funext fun t => (hasDerivAt_line_fderiv hf X v t).deriv
  rw [h1]
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)
  have hc : HasFDerivAt (fun y => fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) X).flip v) X := by
    have := (hdf X).hasFDerivAt.clm_apply (hasFDerivAt_const v X)
    simpa using this
  have hline : HasDerivAt (fun s : ℝ => X + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add X
  have hc' : HasFDerivAt (fun y => fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) X).flip v)
      (X + (0 : ℝ) • v) := by simpa using hc
  have := hc'.comp_hasDerivAt (0 : ℝ) hline
  simpa [Function.comp_def] using this.deriv

/-!
## Monomials along `e_i - e_j`
-/

theorem contDiff_momentMonomial (n : WithTop ℕ∞) (ξ : Occ N) :
    ContDiff ℝ n (fun Y : Fin N → ℝ => momentMonomial Y ξ) := by
  unfold momentMonomial
  exact contDiff_prod fun i _ => ((contDiff_apply ℝ ℝ i).pow _).div_const _

/-- The two-site split `mono(X, ζ) = X_i^{ζ_i}/ζ_i! · X_j^{ζ_j}/ζ_j! · ∏_{k ≠ i,j}`. -/
theorem momentMonomial_split₂ (X : Fin N → ℝ) (ζ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    momentMonomial X ζ = pairMono (ζ i) (ζ j) (X i) (X j) *
      ∏ k ∈ (univ.erase i).erase j, X k ^ ζ k / ((ζ k).factorial : ℝ) := by
  unfold momentMonomial pairMono
  rw [← Finset.mul_prod_erase _ _ (mem_univ i),
    ← Finset.mul_prod_erase _ _ (mem_erase.2 ⟨Ne.symm hij, mem_univ j⟩)]
  field_simp

theorem prod_rest_congr (X : Fin N → ℝ) (ζ ξ : Occ N) {i j : Fin N}
    (h : ∀ k, k ≠ i → k ≠ j → ζ k = ξ k) :
    ∏ k ∈ (univ.erase i).erase j, X k ^ ζ k / ((ζ k).factorial : ℝ) =
      ∏ k ∈ (univ.erase i).erase j, X k ^ ξ k / ((ξ k).factorial : ℝ) := by
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [h k (mem_erase.1 (mem_erase.1 hk).2).1 (mem_erase.1 hk).1]

theorem single_sub_single_apply_of_ne {i j k : Fin N} (hki : k ≠ i) (hkj : k ≠ j) :
    ((Pi.single i 1 - Pi.single j 1 : Fin N → ℝ)) k = 0 := by
  simp [hki, hkj]

/-- Along `e_i - e_j` the monomial is `R · pairMono(ξ_i, ξ_j)(X_i + t, X_j - t)`. -/
theorem momentMonomial_line (X : Fin N → ℝ) (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    (fun s : ℝ => momentMonomial (X + s • (Pi.single i 1 - Pi.single j 1)) ξ) =
      fun s => (∏ k ∈ (univ.erase i).erase j, X k ^ ξ k / ((ξ k).factorial : ℝ)) *
        ((X i + s) ^ ξ i * (X j - s) ^ ξ j / (((ξ i).factorial : ℝ) * ((ξ j).factorial : ℝ))) := by
  funext s
  rw [momentMonomial_split₂ _ ξ hij]
  have hi : (X + s • (Pi.single i 1 - Pi.single j 1 : Fin N → ℝ)) i = X i + s := by
    simp [hij]
  have hj : (X + s • (Pi.single i 1 - Pi.single j 1 : Fin N → ℝ)) j = X j - s := by
    simp [Ne.symm hij]; ring
  have hrest : ∏ k ∈ (univ.erase i).erase j,
      (X + s • (Pi.single i 1 - Pi.single j 1 : Fin N → ℝ)) k ^ ξ k / ((ξ k).factorial : ℝ) =
      ∏ k ∈ (univ.erase i).erase j, X k ^ ξ k / ((ξ k).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkj : k ≠ j := (mem_erase.1 hk).1
    have hki : k ≠ i := (mem_erase.1 (mem_erase.1 hk).2).1
    simp [hki, hkj]
  rw [hi, hj, hrest, pairMono]
  ring

/-- **Pair term**: the `{i,j}` summand of the angular generator on a monomial is the two jump terms
`c_ij[ξ_i(1+ξ_j)(mono(ξ^{ij}) - mono ξ) + ξ_j(1+ξ_i)(mono(ξ^{ji}) - mono ξ)]`. -/
theorem angular_pair_momentMonomial (X : Fin N → ℝ) (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    X i * X j * fderiv ℝ (fderiv ℝ (fun Y : Fin N → ℝ => momentMonomial Y ξ)) X
        (Pi.single i 1 - Pi.single j 1) (Pi.single i 1 - Pi.single j 1) +
      (X j - X i) * fderiv ℝ (fun Y : Fin N → ℝ => momentMonomial Y ξ) X
        (Pi.single i 1 - Pi.single j 1) =
    jumpCoeff ξ i j * (momentMonomial X (move ξ i j) - momentMonomial X ξ) +
      jumpCoeff ξ j i * (momentMonomial X (move ξ j i) - momentMonomial X ξ) := by
  have hf := contDiff_momentMonomial 2 ξ
  rw [← deriv_line _ hf, ← deriv_deriv_line _ hf, momentMonomial_line X ξ hij,
    deriv_const_mul_field', deriv_const_mul_field']
  set R := ∏ k ∈ (univ.erase i).erase j, X k ^ ξ k / ((ξ k).factorial : ℝ)
  have hp := pairOperator_line (ξ i) (ξ j) (X i) (X j)
  simp only at hp
  have e : X i * X j * (R * deriv (deriv fun s => (X i + s) ^ ξ i * (X j - s) ^ ξ j /
        (((ξ i).factorial : ℝ) * ((ξ j).factorial : ℝ))) 0) +
      (X j - X i) * (R * deriv (fun s => (X i + s) ^ ξ i * (X j - s) ^ ξ j /
        (((ξ i).factorial : ℝ) * ((ξ j).factorial : ℝ))) 0) =
      R * (X i * X j * deriv (deriv fun s => (X i + s) ^ ξ i * (X j - s) ^ ξ j /
        (((ξ i).factorial : ℝ) * ((ξ j).factorial : ℝ))) 0 +
      (X j - X i) * deriv (fun s => (X i + s) ^ ξ i * (X j - s) ^ ξ j /
        (((ξ i).factorial : ℝ) * ((ξ j).factorial : ℝ))) 0) := by ring
  rw [e, hp]
  -- identify the three monomials
  have hm0 : momentMonomial X ξ = pairMono (ξ i) (ξ j) (X i) (X j) * R :=
    momentMonomial_split₂ X ξ hij
  have hmij : ξ i ≠ 0 → momentMonomial X (move ξ i j) =
      pairMono (ξ i - 1) (ξ j + 1) (X i) (X j) * R := by
    intro _
    rw [momentMonomial_split₂ X _ hij, move_apply_source ξ hij, move_apply_target,
      prod_rest_congr X _ ξ (fun k hki hkj => move_apply_of_ne ξ hki hkj)]
  have hmji : ξ j ≠ 0 → momentMonomial X (move ξ j i) =
      pairMono (ξ i + 1) (ξ j - 1) (X i) (X j) * R := by
    intro _
    rw [momentMonomial_split₂ X _ hij, move_apply_source ξ (Ne.symm hij), move_apply_target,
      prod_rest_congr X _ ξ (fun k hki hkj => move_apply_of_ne ξ hkj hki)]
  unfold jumpCoeff
  rw [hm0]
  by_cases hi : ξ i = 0
  · by_cases hj : ξ j = 0
    · simp [hi, hj]
    · rw [hmji hj]; simp only [hi, Nat.cast_zero]; ring
  · by_cases hj : ξ j = 0
    · rw [hmij hi]; simp only [hj, Nat.cast_zero]; ring
    · rw [hmij hi, hmji hj]; ring

/-- `∑_i ∑_{j>i} (S i j + S j i) = ∑_i ∑_{j≠i} S i j`. -/
theorem sum_lt_add_swap (S : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (S i j + S j i) =
      ∑ i, ∑ j ∈ univ.erase i, S i j := by
  simp only [Finset.sum_filter, ← Finset.filter_ne', Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j, (if i < j then S j i else 0) = ∑ i, ∑ j, (if j < i then S i j else 0) := by
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.ne', not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne, not_lt.2 h.le]

/-- **Generator identity.** The angular generator on the normalized monomial `mono(·, ξ)` is the
moment-flow generator `𝓑` with couplings `dysonCoupling N lam`. -/
theorem angularGenerator_momentMonomial (lam : Fin N → ℝ) (ξ : Occ N) (X : Fin N → ℝ) :
    angularGenerator N lam (fun Y => momentMonomial Y ξ) X =
      momentGenerator (dysonCoupling N lam) (fun ζ => momentMonomial X ζ) ξ := by
  unfold angularGenerator momentGenerator
  have hc : ∀ i j, dysonCoupling N lam i j = dysonCoupling N lam j i := fun i j => by
    unfold dysonCoupling; ring
  rw [← sum_lt_add_swap]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (mem_filter.1 hj).2.ne
  rw [angular_pair_momentMonomial X ξ hij, hc j i]
  ring

/-!
## Relabelling the moment generator
-/

theorem move_comp_equiv (e : Fin N ≃ Fin N) (ξ : Occ N) (i j : Fin N) :
    move (ξ ∘ e) (e.symm i) (e.symm j) = move ξ i j ∘ e := by
  funext k
  simp only [move, Function.comp_apply, Function.update_apply]
  by_cases hk : k = e.symm j
  · subst hk; simp
  · by_cases hk' : k = e.symm i
    · subst hk'
      have hij : i ≠ j := fun h => hk (by rw [h])
      simp [hk, hij]
    · have h1 : e k ≠ j := fun h => hk (by rw [← h]; simp)
      have h2 : e k ≠ i := fun h => hk' (by rw [← h]; simp)
      simp [hk, hk', h1, h2]

/-- Relabelling by a permutation `e` of the labels. -/
theorem momentGenerator_comp_equiv (e : Fin N ≃ Fin N) (c : Fin N → Fin N → ℝ)
    (g : Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c g (ξ ∘ e) =
      momentGenerator (fun i j => c (e.symm i) (e.symm j)) (fun ζ => g (ζ ∘ e)) ξ := by
  unfold momentGenerator
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hset : (univ.erase (e.symm i)) = (univ.erase i).map e.symm.toEmbedding := by
    ext k; simp
  rw [hset, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_toEmbedding, move_comp_equiv, jumpCoeff, Function.comp_apply,
    Equiv.apply_symm_apply]

theorem momentMonomial_comp_equiv (e : Fin N ≃ Fin N) (Y : Fin N → ℝ) (ζ : Occ N) :
    momentMonomial (Y ∘ e) ζ = momentMonomial Y (ζ ∘ e.symm) := by
  unfold momentMonomial
  rw [← Equiv.prod_comp e.symm]
  simp

/-- **Generator identity in increasing labels.** For Hermitian `K` with simple spectrum, the
angular generator at the Dyson eigenvalues and overlaps of `K`, on the test function
`Y ↦ mono(Y ∘ rev, ξ)`, is `𝓑` with rates `(N(λ_k - λ_l)²)⁻¹` acting on the monomials of
`X_ℓ = N‖q* u_ℓ‖²`. -/
theorem angularGenerator_rev {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (q : Fin N → ℂ) (ξ : Occ N) :
    angularGenerator N (dysonEigenvalue N K) (fun Y => momentMonomial (Y ∘ Fin.revPerm) ξ)
        (fun i => dysonOverlap N q K i) =
      momentGenerator (fun k l => ((N : ℝ) * (freshEigenvalue K k - freshEigenvalue K l) ^ 2)⁻¹)
        (fun ζ => momentMonomial (fun ℓ => (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K ℓ‖ ^ 2) ζ)
        ξ := by
  have hf : (fun Y : Fin N → ℝ => momentMonomial (Y ∘ Fin.revPerm) ξ) =
      fun Y => momentMonomial Y (ξ ∘ Fin.revPerm) := by
    funext Y; rw [momentMonomial_comp_equiv]; rfl
  rw [hf, angularGenerator_momentMonomial, momentGenerator_comp_equiv Fin.revPerm]
  have hX : ∀ ζ : Occ N, momentMonomial (fun i => dysonOverlap N q K i) (ζ ∘ Fin.revPerm) =
      momentMonomial (fun ℓ => (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K ℓ‖ ^ 2) ζ := by
    intro ζ
    have : (fun ℓ => (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K ℓ‖ ^ 2) =
        (fun i => dysonOverlap N q K i) ∘ Fin.revPerm := by
      funext ℓ; simp [dysonOverlap_rev hK hs]
    rw [this, momentMonomial_comp_equiv]; rfl
  simp only [hX]
  congr 1
  funext k l
  simp only [Fin.revPerm_symm, Fin.revPerm_apply]
  exact dysonCoupling_rev hK k l

end BlockBand.Palm.MomentFlow
