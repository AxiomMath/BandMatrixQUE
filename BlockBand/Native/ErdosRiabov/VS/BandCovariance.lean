module

public import BlockBand.Native.ErdosRiabov.VS.BandVariance
public import BlockBand.Native.ErdosRiabov.Chains.ChainCovariance

set_option autoImplicit false

/-!
# The band covariance operator in ring coordinates

Setting: `p : BlockBand.Parameters`, `S = p.entryVariance` on sites, the short-ring profile
`shortRingProfile p.b p.n p.W` on `Fin (p.n * p.W)` (row-major equivalence `siteFinEquiv p`,
written `ringSiteEquiv p`).

* `covOp_map_ringBasis`: for every `ℂ`-linear `T : SiteMatrix → Matrix ι ι ℂ`,
  `covOp (T ∘ E) v X = ∑_{a,b} S_ab (T e_ab) X (T e_ba)` (`generator_matrix`, entrywise).
* `covOp_ringBasis_ringVariance` (site level): `covOp E v X = diag(∑_b S_ab X_bb)`.
* **`covOp_ringMatrix_ringVariance`** (`Fin (p.n * p.W)` level): with the matrix directions
  `ringMatrixFin p (e_i)` (`ringMatrix` read through `siteFinEquiv p`),
  `covOp (ringMatrixFin p ∘ e) v X = bandSelfEnergy (shortRingProfile p.b p.n p.W) X`;
  `covOp_ringMatrix_eq_hermBasis`: this is the existing `hermBasis` contraction
  `covOp hermBasis (bandWeight S) X`.
* `sum_mul_fderiv_fderiv_chainTest_ring`: the band contraction of `Chains` in ring coordinates:
  along `y ↦ A₀ + ringMatrixFin p y`,
  `∑_i v_i D²f(y)[e_i, e_i] = 2 ∑_{i ≤ j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)})`,
  `𝒮 = bandSelfEnergy (shortRingProfile p.b p.n p.W)` (and the matrix-valued form
  `sum_smul_fderiv_fderiv_resChain_ring`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Adapters.ErdosRiabov
open Matrix

variable (p : BlockBand.Parameters)

/-- The `ℂ`-bilinear form `(E, F) ↦ (T E · X · T F)_{rs}`. -/
def sandwichEntry {ι : Type} [Fintype ι] (T : p.SiteMatrix →ₗ[ℂ] Matrix ι ι ℂ)
    (X : Matrix ι ι ℂ) (r s : ι) : p.SiteMatrix →ₗ[ℂ] p.SiteMatrix →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun E F => (T E * X * T F) r s)
    (fun E E' F => by simp only [map_add, Matrix.add_mul, Matrix.add_apply])
    (fun c E F => by simp only [map_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul])
    (fun E F F' => by simp only [map_add, Matrix.mul_add, Matrix.add_apply])
    (fun c E F => by simp only [map_smul, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul])

/-- **Covariance operator along a `ℂ`-linear image of the ring directions.** -/
theorem covOp_map_ringBasis {ι : Type} [Fintype ι] (T : p.SiteMatrix →ₗ[ℂ] Matrix ι ι ℂ)
    (X : Matrix ι ι ℂ) :
    covOp (fun i => T (ringBasis p i)) (ringVariance p) X =
      ∑ a, ∑ b, p.entryVariance a b • (T (single a b 1) * X * T (single b a 1)) := by
  ext r s
  have h := generator_matrix p (sandwichEntry p T X r s)
  simp only [sandwichEntry, LinearMap.mk₂_apply] at h
  simp only [covOp, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  exact h

/-- **Site-level band covariance in ring coordinates**:
`∑_i v_i E_i X E_i = diag(∑_b S_ab X_bb)`, `S = p.entryVariance`. -/
theorem covOp_ringBasis_ringVariance (X : p.SiteMatrix) :
    covOp (ringBasis p) (ringVariance p) X =
      Matrix.diagonal fun a => ∑ b, (p.entryVariance a b : ℂ) * X b b := by
  have h := covOp_map_ringBasis p LinearMap.id X
  simp only [LinearMap.id_apply, single_mul_mul_single, one_mul, mul_one] at h
  refine h.trans ?_
  ext r s
  simp only [Matrix.sum_apply, Matrix.smul_apply, single_apply, diagonal_apply,
    Complex.real_smul]
  by_cases hrs : r = s
  · subst hrs
    simp only [and_self, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq']
  · have hn : ∀ a : p.Site, ¬ (a = r ∧ a = s) := fun a h => hrs (h.1.symm.trans h.2)
    simp [hn, hrs]

/-- The row-major site equivalence `siteFinEquiv p`, with codomain written `Fin (p.n * p.W)`
(the index type of `shortRingProfile p.b p.n p.W`; `p.N = p.n * p.W` by definition). -/
def ringSiteEquiv : p.Site ≃ Fin (p.n * p.W) := siteFinEquiv p

theorem shortRingProfile_ringSiteEquiv (x y : p.Site) :
    shortRingProfile p.b p.n p.W (ringSiteEquiv p x) (ringSiteEquiv p y) = p.entryVariance x y :=
  shortRingProfile_siteFinEquiv p x y

/-- `ringMatrix` read on `Fin (p.n * p.W)` through the row-major site equivalence, as a
real-linear map `ℝ^d → Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ`. -/
def ringMatrixFin :
    (Fin (ringDim p) → ℝ) →ₗ[ℝ] Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ :=
  (reindexLinearEquiv ℝ ℂ (ringSiteEquiv p) (ringSiteEquiv p)).toLinearMap ∘ₗ
    ringMatrixLinear p

theorem ringMatrixFin_apply (y : Fin (ringDim p) → ℝ) :
    ringMatrixFin p y = reindex (ringSiteEquiv p) (ringSiteEquiv p) (ringMatrix p y) := rfl

theorem ringMatrixFin_single (i : Fin (ringDim p)) :
    ringMatrixFin p (Pi.single i 1) =
      reindex (ringSiteEquiv p) (ringSiteEquiv p) (ringBasis p i) := rfl

/-- **The band covariance operator in ring coordinates.** With the
matrix directions `ringMatrixFin p (e_i)` of the real ring coordinates and their variances
`ringVariance p`, `∑_i v_i E_i X E_i = bandSelfEnergy (shortRingProfile p.b p.n p.W) X` for
every `X` on `Fin (p.n * p.W)`. -/
theorem covOp_ringMatrix_ringVariance (X : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ) :
    covOp (fun i => ringMatrixFin p (Pi.single i 1)) (ringVariance p) X =
      bandSelfEnergy (shortRingProfile p.b p.n p.W) X := by
  set e := ringSiteEquiv p
  have h := covOp_map_ringBasis p (reindexLinearEquiv ℂ ℂ e e).toLinearMap X
  simp only [LinearEquiv.coe_coe, coe_reindexLinearEquiv, reindex_apply, submatrix_single_equiv,
    Equiv.symm_symm, single_mul_mul_single, one_mul, mul_one] at h
  refine h.trans ?_
  ext r s
  obtain ⟨r', rfl⟩ := e.surjective r
  rw [bandSelfEnergy_apply]
  by_cases hrs : e r' = s
  · subst hrs
    simp only [Matrix.sum_apply, Matrix.smul_apply, single_apply, Complex.real_smul,
      EmbeddingLike.apply_eq_iff_eq, and_self, mul_ite, mul_zero, ite_true]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [shortRingProfile_ringSiteEquiv]
  · have hn : ∀ a : p.Site, ¬ (a = r' ∧ e a = s) := fun a h => hrs (h.1 ▸ h.2)
    simp only [Matrix.sum_apply, Matrix.smul_apply, single_apply, Complex.real_smul,
      EmbeddingLike.apply_eq_iff_eq]
    simp [hn, hrs]

/-- The ring-coordinate contraction is the `hermBasis` contraction
`covOp_hermBasis_bandWeight` (both are `bandSelfEnergy` of the short-ring profile). -/
theorem covOp_ringMatrix_eq_hermBasis (X : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ) :
    covOp (fun i => ringMatrixFin p (Pi.single i 1)) (ringVariance p) X =
      covOp hermBasis (bandWeight (shortRingProfile p.b p.n p.W)) X := by
  rw [covOp_ringMatrix_ringVariance, covOp_hermBasis_bandWeight]
  exact shortRingProfile_symm p.b p.n p.W

section MatrixLevel

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Band contraction of the matrix chain in ring coordinates**: along
`y ↦ A₀ + ringMatrixFin p y`, `∑_i v_i D²C(y)[e_i, e_i] = 2 ∑_{i ≤ j} G_{[0,i]} 𝒮[G_{[i,j]}]
G_{[j,k)}`, `𝒮 = bandSelfEnergy (shortRingProfile p.b p.n p.W)`. -/
theorem sum_smul_fderiv_fderiv_resChain_ring {k : ℕ}
    (A₀ : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ) {y : Fin (ringDim p) → ℝ}
    (hy : ∀ j, IsUnit (A₀ + ringMatrixFin p y -
      z j • (1 : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ)).det) :
    ∑ i, ringVariance p i • fderiv ℝ (fderiv ℝ (resChain A₀ (ringMatrixFin p) z B)) y
        (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) =
      (2 : ℝ) • ∑ j, ∑ i with i ≤ j,
        pairIns B (resSlots A₀ (ringMatrixFin p) z y)
          (bandSelfEnergy (shortRingProfile p.b p.n p.W)) i j := by
  have h := sum_smul_fderiv_fderiv_resChain A₀ (ringMatrixFin p) z B hy (ringVariance p)
    (fun i => Pi.single i (1 : ℝ))
  have hcov : covOp (fun i => ringMatrixFin p (Pi.single i (1 : ℝ))) (ringVariance p) =
      bandSelfEnergy (shortRingProfile p.b p.n p.W) :=
    funext (covOp_ringMatrix_ringVariance p)
  rw [hcov] at h
  exact h

end MatrixLevel

/-- **Band contraction of chain test functions in ring coordinates**: along
`y ↦ A₀ + ringMatrixFin p y`, for `f = Re tr(K · chain)`,
`∑_i v_i ∂²_i f(y) = 2 ∑_{i ≤ j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)})`,
`𝒮[X] = diag(S · diag X)`, `S = shortRingProfile p.b p.n p.W`. -/
theorem sum_mul_fderiv_fderiv_chainTest_ring {k : ℕ}
    (A₀ : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ)
    (K : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ)
    {y : Fin (ringDim p) → ℝ}
    (hy : ∀ j, IsUnit (A₀ + ringMatrixFin p y -
      z j • (1 : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ)).det) :
    ∑ i, ringVariance p i * fderiv ℝ (fderiv ℝ (chainTest A₀ (ringMatrixFin p) z B K)) y
        (Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) =
      2 * ∑ j, ∑ i with i ≤ j,
        reTr K (pairIns B (resSlots A₀ (ringMatrixFin p) z y)
          (bandSelfEnergy (shortRingProfile p.b p.n p.W)) i j) := by
  have h := sum_mul_fderiv_fderiv_chainTest A₀ (ringMatrixFin p) z B K hy (ringVariance p)
    (fun i => Pi.single i (1 : ℝ))
  have hcov : covOp (fun i => ringMatrixFin p (Pi.single i (1 : ℝ))) (ringVariance p) =
      bandSelfEnergy (shortRingProfile p.b p.n p.W) :=
    funext (covOp_ringMatrix_ringVariance p)
  rw [hcov] at h
  exact h

end BlockBand.Native.ErdosRiabov.VS
