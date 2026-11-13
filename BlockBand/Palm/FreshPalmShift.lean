module

public import BlockBand.Palm.MomentFlow.BridgeLaw
public import BlockBand.Palm.MomentFlow.LocalSpectral
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Coarea.ClockRank

/-!
# Deterministic lemmas for the fresh Palm theorem

Scalar-shift invariance of the selected eigenvector and elementary bounds used in the proof of
the fresh Palm theorem.

* `freshEigenvector_add_smul_one`: for **every** Hermitian `K` and real `ζ`, the selected
  eigenvector of `K + ζ I` equals that of `K` (the selection of
  `BlockBand.Model.Construction.orderedColumnSelection` is a function of the Lagrange projector
  only, and the Lagrange projector is shift invariant). No simple-spectrum hypothesis.
* `sum_norm_sq_freshEigenvector_le`: `‖u_ℓ‖² ≤ 1` for every raw matrix (unit on rank-simple
  Hermitian matrices, zero otherwise).
* `re_trace_eq_sum_freshEigenvalue`: `Re Tr K = ∑_k λ_k(K)` for Hermitian `K`.
* `quadForm_smul`, `palmOverlap_smul`: degree-two homogeneity in a real scalar multiple of `q`.
* `overlap_le_nsq`: raw bound `N|q* u_ℓ|² ≤ N‖q‖²` for every raw matrix.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.FreshPalmAssembly

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction
  BlockBand.Foundations.Spectral BlockBand.Coarea.ClockRank
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

theorem orderedEigenvalue_add_smul_one {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (ζ : ℝ) (h' : (K + (ζ : ℂ) • 1).IsHermitian) (j : Fin (Fintype.card (Fin N))) :
    orderedEigenvalue (⟨K + (ζ : ℂ) • 1, h'⟩ : HermitianMatrix (Fin N)) j =
      orderedEigenvalue (⟨K, hK⟩ : HermitianMatrix (Fin N)) j + ζ := by
  have h := BlockBand.Coarea.FreshPalm.freshEigenvalue_add_smul_one hK ζ
    (Fin.cast (Fintype.card_fin N) j)
  simp only [freshEigenvalue, rawIncreasingEigenvalue_eq _ _ hK, rawIncreasingEigenvalue_eq _ _ h',
    Fin.cast_cast, Fin.cast_eq_self] at h
  exact h

theorem orderedProjector_add_smul_one {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (ζ : ℝ) (h' : (K + (ζ : ℂ) • 1).IsHermitian) (i : Fin (Fintype.card (Fin N))) :
    orderedProjector i (⟨K + (ζ : ℂ) • 1, h'⟩ : HermitianMatrix (Fin N)) =
      orderedProjector i (⟨K, hK⟩ : HermitianMatrix (Fin N)) := by
  unfold orderedProjector orderedProjectorProduct
  congr 1
  apply List.map_congr_left
  intro j _
  unfold orderedProjectorFactor
  split_ifs with hji
  · rfl
  · rw [orderedEigenvalue_add_smul_one hK ζ h' i, orderedEigenvalue_add_smul_one hK ζ h' j]
    congr 1
    · congr 2; ring
    · change K + (ζ : ℂ) • 1 - ((orderedEigenvalue (⟨K, hK⟩ : HermitianMatrix (Fin N)) j + ζ : ℝ) : ℂ) • 1 =
        K - (orderedEigenvalue (⟨K, hK⟩ : HermitianMatrix (Fin N)) j : ℂ) • 1
      push_cast
      rw [add_smul]
      abel

theorem orderedColumnSelection_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i : Fin (Fintype.card ι)} {A B : HermitianMatrix ι}
    (h : orderedProjector i A = orderedProjector i B) :
    orderedColumnSelection i A = orderedColumnSelection i B := by
  funext x
  unfold orderedColumnSelection orderedColumnRegion orderedColumnAvailable orderedNormalizedColumn
  simp only [Set.mem_ofPred_eq, h]
  congr 1
  funext j
  split_ifs <;> rfl

/-- **Scalar-shift invariance of the selected eigenvector** (every Hermitian `K`, every real `ζ`;
no simplicity hypothesis: the selection is a function of the Lagrange projector only). -/
theorem freshEigenvector_add_smul_one {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (ζ : ℝ) (ℓ : Fin N) : freshEigenvector (K + (ζ : ℂ) • 1) ℓ = freshEigenvector K ℓ := by
  have h' : (K + (ζ : ℂ) • 1).IsHermitian :=
    hK.add (isHermitian_one.smul (Complex.conj_ofReal ζ))
  funext x
  unfold freshEigenvector
  rw [rawOrderedColumnSelection_eq _ _ h', rawOrderedColumnSelection_eq _ _ hK]
  exact congrFun (orderedColumnSelection_congr (orderedProjector_add_smul_one hK ζ h' _)) x

/-- The selected eigenvector has `ℓ²` mass at most one (one on rank-simple Hermitian matrices,
zero otherwise), for every raw matrix. -/
theorem sum_norm_sq_freshEigenvector_le (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    ∑ x, ‖freshEigenvector K ℓ x‖ ^ 2 ≤ 1 := by
  unfold freshEigenvector rawOrderedColumnSelection rawHermitianExtension
  split_ifs with hK
  · by_cases hs : RankSimple (⟨K, hK⟩ : HermitianMatrix (Fin N)) (Fin.cast (Fintype.card_fin N).symm ℓ)
    · obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase_of_rankSimple _ _ hs
      beta_reduce
      rw [hsel]
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hz, one_mul]
      rw [sum_norm_sq_increasingEigenvector]
    · beta_reduce
      rw [orderedColumnSelection_eq_zero_of_not_rankSimple _ _ hs]
      simp
  · simp

theorem re_trace_eq_sum_freshEigenvalue {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) :
    K.trace.re = ∑ k, freshEigenvalue K k := by
  rw [hK.trace_eq_sum_eigenvalues, Complex.re_sum]
  change ∑ i, hK.eigenvalues i = _
  simp_rw [BlockBand.Palm.MomentFlow.freshEigenvalue_eq hK]
  have h1 : ∑ k : Fin N, hK.eigenvalues₀ (Fin.cast (Fintype.card_fin N).symm k).rev =
      ∑ j : Fin (Fintype.card (Fin N)), hK.eigenvalues₀ j :=
    Fintype.sum_equiv ((finCongr (Fintype.card_fin N).symm).trans Fin.revPerm) _ _
      (fun k => rfl)
  rw [h1]
  exact (Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))) _ _
    (fun j => by rw [hK.eigenvalues_apply_equivOfCardEq])).symm

theorem quadForm_smul (Γ : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (q : Fin N → ℂ) :
    quadForm Γ ((c : ℂ) • q) = c ^ 2 * quadForm Γ q := by
  unfold quadForm
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem palmOverlap_smul (F : Matrix (Fin N) (Fin N) ℂ) (c : ℝ) (q : Fin N → ℂ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) :
    palmOverlap F ((c : ℂ) • q) ℓ A0 = c ^ 2 * palmOverlap F q ℓ A0 := by
  unfold palmOverlap
  rw [star_smul, smul_dotProduct]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Cauchy–Schwarz: `|q* v|² ≤ ‖q‖² ‖v‖²`. -/
theorem sq_norm_dotProduct_le (q v : Fin N → ℂ) :
    ‖star q ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖q i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  have h1 : ‖star q ⬝ᵥ v‖ ≤ ∑ i, ‖q i‖ * ‖v i‖ := by
    simp only [dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- Raw overlap bound `N|q* u_ℓ|² ≤ N‖q‖²`, every raw matrix. -/
theorem overlap_le_nsq (K : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (ℓ : Fin N) :
    (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector K ℓ‖ ^ 2 ≤ (N : ℝ) * ∑ i, ‖q i‖ ^ 2 := by
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
  refine (sq_norm_dotProduct_le q _).trans ?_
  calc (∑ i, ‖q i‖ ^ 2) * ∑ i, ‖freshEigenvector K ℓ i‖ ^ 2 ≤ (∑ i, ‖q i‖ ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (sum_norm_sq_freshEigenvector_le K ℓ)
          (Finset.sum_nonneg fun _ _ => by positivity)
    _ = ∑ i, ‖q i‖ ^ 2 := mul_one _

end BlockBand.Palm.FreshPalmAssembly
