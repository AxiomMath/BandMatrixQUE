module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGaussianSplitLaw
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalPairRankReindex
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalPairExteriorPolynomialNull
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurDecoderEnergySeparation

/-!
# Adjacent-pair readback of the selected coarea good event

Setting: the coarea theorem at a fixed adjacent exposed pair `S = {j, j+1}`
of dimension `2W`, at fixed finite parameters `n, W, b` (no limit, no
uniformity in any parameter).

`PhysicalPairExteriorPolynomialNull` proves that the measurable event
`Law.physicalSelectedPairCoareaGoodEvent j r` (simple normalized spectrum,
selected-energy pair-exterior pole avoidance, positive measurable pair mass)
has full probability.  That event is phrased for the *normalized* matrix
`H / √c` indexed by `BlockGUE.Index`, with `j : Fin p.n`.  The
Gaussian split (`PhysicalActualPairGaussianSplitLaw`) and the Schur readback
(`PhysicalPairSchurReadback`, `PhysicalPairRankReindex`) are phrased for the
*unnormalized* site Hamiltonian `H`, with `j : ZMod p.n`, in the
retained-first order `(Unit ⊕ Fin (2W-1)) ⊕ Fin card`.

This file proves the correspondence:

* the site Hamiltonian is `√c` times the normalized matrix, so the
  selected energy at increasing rank `r` (zero-based) is
  `√c · λ_r(H/√c)`, and the read-back exterior `H_R` is `√c` times the
  normalized pair-exterior minor (`physicalPairExteriorSiteEquiv` identifies
  the two exterior index types);
* the good event places the state `(z, ξ)` in the deterministic,
  measurable selected-simple Schur incidence set
  `actualPairSelectedSimpleSchurIncidence` (simple spectrum of the
  reconstructed matrix and pole-free selected energy);
* on that set: ordered rank `r+1` of the block pencil, additive inertia,
  spectral isolation, a nonzero selected Schur-compression kernel vector whose
  Schur reconstruction is the selected eigenvector, one-dimensionality of that
  kernel, phase-free projector readback, and positive pair mass;
* the measurable pair mass of the event equals the site eigenvector's
  squared mass on the two adjacent blocks;
* pushforward and residual-plus-fresh split transfer of the incidence
  condition through `Law.lintegral_actualPairExterior_eq_physicalSplit_unconditional`,
  including an iterated (residual, exterior, fresh) almost-everywhere form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ComplexOrder InnerProductSpace

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-!
### Deterministic spectral lemmas
-/

/-- Courant–Fischer comparison for a Rayleigh quotient dominated by a
nonnegative multiple. -/
theorem orderedEigenvalue_le_mul_of_rayleigh
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₂ A₁ : HermitianMatrix ι) {c : ℝ} (hc : 0 ≤ c)
    (hquad : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 →
      RCLike.re ⟪(Matrix.toEuclideanLin (A₂ : Matrix ι ι ℂ)) x, x⟫_ℂ ≤
        c * RCLike.re ⟪(Matrix.toEuclideanLin (A₁ : Matrix ι ι ℂ)) x, x⟫_ℂ)
    (r : Fin (Fintype.card ι)) :
    orderedEigenvalue A₂ r ≤ c * orderedEigenvalue A₁ r := by
  simp only [orderedEigenvalue, Matrix.IsHermitian.eigenvalues₀]
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr A₂.property
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr A₁.property
  obtain ⟨V, hVdim, hVlow⟩ :=
    hT.exists_submodule_forall_unit_eigenvalue_le_re_inner
      finrank_euclideanSpace r.rev
  obtain ⟨x, hxV, hnx, hup⟩ :=
    hS.exists_unit_vector_re_inner_le_eigenvalue
      finrank_euclideanSpace r.rev V hVdim
  calc
    hT.eigenvalues finrank_euclideanSpace r.rev ≤
        RCLike.re ⟪(Matrix.toEuclideanLin (A₂ : Matrix ι ι ℂ)) x, x⟫_ℂ :=
      hVlow x hxV hnx
    _ ≤ c * RCLike.re ⟪(Matrix.toEuclideanLin (A₁ : Matrix ι ι ℂ)) x, x⟫_ℂ :=
      hquad x hnx
    _ ≤ c * hS.eigenvalues finrank_euclideanSpace r.rev :=
      mul_le_mul_of_nonneg_left hup hc

/-- The Rayleigh quotient is real-homogeneous. -/
theorem re_inner_toEuclideanLin_real_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (c : ℝ) (x : EuclideanSpace ℂ ι) :
    RCLike.re ⟪(Matrix.toEuclideanLin ((c : ℂ) • A)) x, x⟫_ℂ =
      c * RCLike.re ⟪(Matrix.toEuclideanLin A) x, x⟫_ℂ := by
  rw [LinearEquiv.map_smul, LinearMap.smul_apply, inner_smul_left]
  simp [RCLike.mul_re]

/-- Increasingly ordered Hermitian eigenvalues scale linearly under a
positive real dilation. -/
theorem orderedEigenvalue_real_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) {c : ℝ} (hc : 0 < c)
    (hA : ((c : ℂ) • A.1).IsHermitian)
    (r : Fin (Fintype.card ι)) :
    orderedEigenvalue ⟨(c : ℂ) • A.1, hA⟩ r = c * orderedEigenvalue A r := by
  apply le_antisymm
  · apply orderedEigenvalue_le_mul_of_rayleigh _ _ hc.le
    intro x _
    exact (re_inner_toEuclideanLin_real_smul A.1 c x).le
  · have h := orderedEigenvalue_le_mul_of_rayleigh A ⟨(c : ℂ) • A.1, hA⟩
      (inv_nonneg.mpr hc.le) (fun x _ => by
        change _ ≤ c⁻¹ * RCLike.re ⟪(Matrix.toEuclideanLin ((c : ℂ) • A.1)) x, x⟫_ℂ
        rw [re_inner_toEuclideanLin_real_smul, ← mul_assoc,
          inv_mul_cancel₀ hc.ne', one_mul]) r
    calc c * orderedEigenvalue A r ≤
        c * (c⁻¹ * orderedEigenvalue ⟨(c : ℂ) • A.1, hA⟩ r) :=
          mul_le_mul_of_nonneg_left h hc.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- Ordered spectra are strictly increasing exactly when they are injective. -/
theorem orderedEigenvalue_strictMono_of_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hinj : Function.Injective (orderedEigenvalue A)) :
    StrictMono (orderedEigenvalue A) :=
  (orderedEigenvalue_mono A).strictMono_of_injective hinj

/-- With simple spectrum, exactly `r` ordered eigenvalues lie strictly below
the `r`-th one (zero-based rank). -/
theorem eigenCount_Iio_orderedEigenvalue_of_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hinj : Function.Injective (orderedEigenvalue A))
    (r : Fin (Fintype.card ι)) :
    eigenCount A (Set.Iio (orderedEigenvalue A r)) = r.val := by
  rw [eigenCount_def]
  have hsm := orderedEigenvalue_strictMono_of_injective A hinj
  convert Fin.card_Iio r using 2
  ext i
  simp [hsm.lt_iff_lt]

/-- Simplicity of the ordered spectrum is invariant under reindexing. -/
theorem orderedEigenvalue_injective_reindex_iff
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : HermitianMatrix ι) :
    Function.Injective (orderedEigenvalue ⟨Matrix.reindex e e A.1, A.2.reindex e⟩) ↔
      Function.Injective (orderedEigenvalue A) := by
  have h : ∀ r, orderedEigenvalue ⟨Matrix.reindex e e A.1, A.2.reindex e⟩
      (Fin.cast (Fintype.card_congr e) r) = orderedEigenvalue A r :=
    orderedEigenvalue_reindex_equiv e A
  constructor
  · intro hinj r s hrs
    have := hinj (a₁ := Fin.cast (Fintype.card_congr e) r)
      (a₂ := Fin.cast (Fintype.card_congr e) s) (by rw [h, h, hrs])
    exact Fin.cast_injective _ this
  · intro hinj r s hrs
    have hr := h (Fin.cast (Fintype.card_congr e).symm r)
    have hs := h (Fin.cast (Fintype.card_congr e).symm s)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at hr hs
    have := hinj (hr.symm.trans (hrs.trans hs))
    exact Fin.cast_injective _ this

/-- Simplicity of the ordered spectrum is invariant under positive dilation. -/
theorem orderedEigenvalue_injective_real_smul_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) {c : ℝ} (hc : 0 < c)
    (hA : ((c : ℂ) • A.1).IsHermitian) :
    Function.Injective (orderedEigenvalue ⟨(c : ℂ) • A.1, hA⟩) ↔
      Function.Injective (orderedEigenvalue A) := by
  have h := orderedEigenvalue_real_smul A hc hA
  constructor
  · intro hinj r s hrs
    exact hinj (by rw [h, h, hrs])
  · intro hinj r s hrs
    rw [h, h] at hrs
    exact hinj (mul_left_cancel₀ hc.ne' hrs)

/-- A shifted Hermitian determinant vanishes exactly at an ordered
eigenvalue. -/
theorem det_sub_real_smul_one_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι) (E : ℝ) :
    (A.1 - (E : ℂ) • 1).det = 0 ↔
      ∃ s : Fin (Fintype.card ι), orderedEigenvalue A s = E := by
  let S : HermitianMatrix ι :=
    ⟨A.1 - (E : ℂ) • 1,
      A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))⟩
  have h := hermitian_det_eq_zero_iff_exists_orderedEigenvalue_eq_zero S
  change S.1.det = 0 ↔ _
  rw [h]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have := orderedEigenvalue_sub_real_smul_one A E s
    simp only [S] at hs
    rw [this] at hs
    linarith
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have := orderedEigenvalue_sub_real_smul_one A E s
    simp only [S]
    rw [this, hs, sub_self]

/-- With injective Mathlib eigenvalues, every eigenvector at the `k`-th
eigenvalue is a multiple of the `k`-th orthonormal eigenvector. -/
theorem eigenvector_eq_coeff_smul_of_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hinj : Function.Injective hA.eigenvalues) (k : ι) (u : ι → ℂ)
    (hu : A *ᵥ u = (hA.eigenvalues k : ℂ) • u) :
    u = (u ⬝ᵥ star (hA.eigenvectorBasis k).ofLp) • (hA.eigenvectorBasis k).ofLp := by
  have hcoef : ∀ i, i ≠ k → u ⬝ᵥ star (hA.eigenvectorBasis i).ofLp = 0 := by
    intro i hik
    have h1 : (A *ᵥ u) ⬝ᵥ star (hA.eigenvectorBasis i).ofLp =
        (hA.eigenvalues k : ℂ) * (u ⬝ᵥ star (hA.eigenvectorBasis i).ofLp) := by
      rw [hu, smul_dotProduct, smul_eq_mul]
    have hrow : star (hA.eigenvectorBasis i).ofLp ᵥ* A =
        (hA.eigenvalues i : ℂ) • star (hA.eigenvectorBasis i).ofLp := by
      have h := congrArg star (hA.mulVec_eigenvectorBasis i)
      rw [star_mulVec, hA.eq] at h
      rw [h]
      ext a
      simp [Pi.star_apply]
    have h2 : (A *ᵥ u) ⬝ᵥ star (hA.eigenvectorBasis i).ofLp =
        (hA.eigenvalues i : ℂ) * (u ⬝ᵥ star (hA.eigenvectorBasis i).ofLp) := by
      rw [dotProduct_comm, dotProduct_mulVec, hrow, smul_dotProduct, smul_eq_mul,
        dotProduct_comm]
    have hne : (hA.eigenvalues k : ℂ) ≠ (hA.eigenvalues i : ℂ) := by
      intro h
      exact hik (hinj (Complex.ofReal_injective h)).symm
    have h3 : ((hA.eigenvalues k : ℂ) - hA.eigenvalues i) *
        (u ⬝ᵥ star (hA.eigenvectorBasis i).ofLp) = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hne)
  have hsum := congrArg WithLp.ofLp ((hA.eigenvectorBasis).sum_repr' (WithLp.toLp 2 u))
  rw [WithLp.ofLp_sum] at hsum
  simp only [WithLp.ofLp_smul, EuclideanSpace.inner_eq_star_dotProduct] at hsum
  rw [Finset.sum_eq_single k (fun i _ hik => by rw [hcoef i hik, zero_smul])
    (fun h => absurd (Finset.mem_univ k) h)] at hsum
  exact hsum.symm

/-- Mathlib's unordered eigenvalue at the index matching ordered rank `r`. -/
theorem hermitianEigenvalues_orderedIndex
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (r : Fin (Fintype.card ι)) :
    A.property.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) r.rev) =
      orderedEigenvalue A r := by
  simp [Matrix.IsHermitian.eigenvalues, orderedEigenvalue]

/-- Injectivity of the ordered spectrum is injectivity of Mathlib's
unordered eigenvalue family. -/
theorem hermitianEigenvalues_injective_of_orderedEigenvalue_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hinj : Function.Injective (orderedEigenvalue A)) :
    Function.Injective A.property.eigenvalues := by
  intro a b hab
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  have ha : a = e (e.symm a).rev.rev := by simp
  have hb : b = e (e.symm b).rev.rev := by simp
  rw [ha, hb, hermitianEigenvalues_orderedIndex,
    hermitianEigenvalues_orderedIndex] at hab
  rw [ha, hb, hinj hab]

/-- With simple ordered spectrum, every eigenspace is a line: an eigenvector
`u` at the energy of a nonzero eigenvector `w` is a scalar multiple of `w`. -/
theorem eigenvector_mem_line_of_orderedEigenvalue_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hinj : Function.Injective (orderedEigenvalue A)) {E : ℝ} {u w : ι → ℂ}
    (hw0 : w ≠ 0) (hw : A.1 *ᵥ w = (E : ℂ) • w)
    (hu : A.1 *ᵥ u = (E : ℂ) • u) :
    ∃ c : ℂ, u = c • w := by
  have hshift : (A.1 - (E : ℂ) • 1) *ᵥ w = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hw, sub_self]
  obtain ⟨r, hr⟩ := exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero A hw0 hshift
  set k := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) r.rev
  have hk : A.property.eigenvalues k = E := by
    rw [hermitianEigenvalues_orderedIndex, hr]
  have hinj' := hermitianEigenvalues_injective_of_orderedEigenvalue_injective A hinj
  have hu' := eigenvector_eq_coeff_smul_of_injective A.property hinj' k u
    (by rw [hk]; exact hu)
  have hw' := eigenvector_eq_coeff_smul_of_injective A.property hinj' k w
    (by rw [hk]; exact hw)
  set b := (A.property.eigenvectorBasis k).ofLp
  set cu := u ⬝ᵥ star b
  set cw := w ⬝ᵥ star b
  have hcw : cw ≠ 0 := by
    intro h
    apply hw0
    rw [hw', h, zero_smul]
  refine ⟨cu / cw, ?_⟩
  rw [hu', hw', smul_smul, div_mul_cancel₀ _ hcw]

/-- Two unit eigenvectors on one simple eigenline have the same phase-free
rank-one projector. -/
theorem vecMulVec_eq_of_eigenvector_line
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hinj : Function.Injective (orderedEigenvalue A)) {E : ℝ} {u w : ι → ℂ}
    (hw : A.1 *ᵥ w = (E : ℂ) • w) (hu : A.1 *ᵥ u = (E : ℂ) • u)
    (hwn : star w ⬝ᵥ w = 1) (hun : star u ⬝ᵥ u = 1) :
    Matrix.vecMulVec u (star u) = Matrix.vecMulVec w (star w) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hwn
  obtain ⟨c, rfl⟩ := eigenvector_mem_line_of_orderedEigenvalue_injective A hinj hw0 hw hu
  have hcc : star c * c = 1 := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, hwn] at hun
    simpa [smul_eq_mul, mul_comm] using hun
  rw [star_smul, Matrix.vecMulVec_smul, Matrix.smul_vecMulVec, smul_smul, hcc, one_smul]

/-!
### Index correspondence between `Fin p.n` and cyclic `ZMod p.n` labels
-/

/-- Exposed cyclic position at least `2W` is exactly exteriority to the
adjacent pair `{j,j+1}`. -/
theorem two_mul_W_le_exposedSitePos_iff (p : Params) (j : Fin p.n)
    (x : Site p.n p.W) :
    2 * p.W ≤ exposedSitePos p j x ↔
      x.1 ≠ (j : ZMod p.n) ∧ x.1 ≠ (j : ZMod p.n) + 1 := by
  have h := Nat.le_div_iff_mul_le (k := p.W) (x := 2) (y := exposedSitePos p j x) p.W_pos
  rw [exposedSitePos_div] at h
  rw [← h]
  have hn : 1 < p.n := lt_of_lt_of_le (by norm_num) p.n_ge_four
  have h0 : (x.1 - (j : ZMod p.n)).val = 0 ↔ x.1 = (j : ZMod p.n) := by
    rw [ZMod.val_eq_zero, sub_eq_zero]
  have h1 : (x.1 - (j : ZMod p.n)).val = 1 ↔ x.1 = (j : ZMod p.n) + 1 := by
    rw [ZMod.val_eq_one hn, sub_eq_iff_eq_add']
  constructor
  · intro h2
    exact ⟨fun he => by have := h0.mpr he; omega, fun he => by have := h1.mpr he; omega⟩
  · rintro ⟨ha, hb⟩
    have ha' : (x.1 - (j : ZMod p.n)).val ≠ 0 := fun he => ha (h0.mp he)
    have hb' : (x.1 - (j : ZMod p.n)).val ≠ 1 := fun he => hb (h1.mp he)
    omega

/-- The `Fin`-labelled exposed-pair exterior used by the polynomial nullity
argument is the cyclic site exterior used by the Gaussian split. -/
def physicalPairExteriorSiteEquiv (p : Params) (j : Fin p.n) :
    PhysicalPairExteriorIndex p j ≃ AdjacentPairExteriorIndex p (j : ZMod p.n) :=
  (physicalIndexSiteEquiv p).subtypeEquiv fun x => by
    change 2 * p.W ≤ exposedSitePos p j (allDiagonalSite x) ↔ _
    exact two_mul_W_le_exposedSitePos_iff p j (allDiagonalSite x)

@[simp] theorem physicalPairExteriorSiteEquiv_apply_val (p : Params) (j : Fin p.n)
    (x : PhysicalPairExteriorIndex p j) :
    (physicalPairExteriorSiteEquiv p j x).1 = allDiagonalSite x.1 := rfl

/-- The cyclic successor label of `Fin p.n` is the `ZMod` successor. -/
theorem adjacentPairNext_cast (p : Params) (j : Fin p.n) :
    ((adjacentPairNext p j : Fin p.n) : ZMod p.n) = (j : ZMod p.n) + 1 := by
  simp [adjacentPairNext]

/-!
### The normalized physical matrix versus the site Hamiltonian
-/

/-- The site Hamiltonian is `√c` times the normalized physical matrix,
transported along the block-index/site equivalence. -/
theorem Law.actualSiteHamiltonian_eq_smul_reindex {p : Params} (M : Law p)
    (ω : M.Ω) :
    (M.actualSiteHamiltonian ω).1 =
      ((Real.sqrt p.c : ℝ) : ℂ) • Matrix.reindex (physicalIndexSiteEquiv p)
        (physicalIndexSiteEquiv p) (M.normalizedPhysicalMatrix ω).1 := by
  ext x y
  change M.H ω x y = ((Real.sqrt p.c : ℝ) : ℂ) * (((Real.sqrt p.c)⁻¹ : ℂ) *
    M.H ω (allDiagonalSite ((physicalIndexSiteEquiv p).symm x))
      (allDiagonalSite ((physicalIndexSiteEquiv p).symm y)))
  have hx : allDiagonalSite ((physicalIndexSiteEquiv p).symm x) = x :=
    (physicalIndexSiteEquiv p).apply_symm_apply x
  have hy : allDiagonalSite ((physicalIndexSiteEquiv p).symm y) = y :=
    (physicalIndexSiteEquiv p).apply_symm_apply y
  rw [hx, hy, ← mul_assoc, mul_inv_cancel₀ (sqrt_c_complex_ne_zero p), one_mul]

/-- The reindexing used to compare the `Fin`-labelled normalized exterior with
the canonical `Fin card` numbering of the exterior. -/
def physicalPairExteriorFinEquiv (p : Params) (j : Fin p.n) :
    PhysicalPairExteriorIndex p j ≃
      Fin (ActualPairExteriorDimension p (j : ZMod p.n)) :=
  (physicalPairExteriorSiteEquiv p j).trans
    (actualPairExteriorEquivFin p (j : ZMod p.n))

/-- The read-back exterior matrix `H_R` of the state is `√c` times the
normalized adjacent-pair exterior minor of `PhysicalPairExteriorPolynomialNull`,
after the deterministic index equivalence. -/
theorem Law.actualPairStateHR_eq_smul_reindex {p : Params} (M : Law p)
    (j : Fin p.n) (ω : M.Ω) :
    actualPairStateHR p (j : ZMod p.n)
        (M.actualPairExteriorCouplingState (j : ZMod p.n) ω) =
      ((Real.sqrt p.c : ℝ) : ℂ) • Matrix.reindex (physicalPairExteriorFinEquiv p j)
        (physicalPairExteriorFinEquiv p j)
        (M.normalizedPhysicalPairExteriorMatrix j ω).1 := by
  ext a b
  set ea := (actualPairExteriorEquivFin p (j : ZMod p.n)).symm a
  set eb := (actualPairExteriorEquivFin p (j : ZMod p.n)).symm b
  change M.H ω ea.1 eb.1 = ((Real.sqrt p.c : ℝ) : ℂ) * (((Real.sqrt p.c)⁻¹ : ℂ) *
    M.H ω (allDiagonalSite ((physicalPairExteriorSiteEquiv p j).symm ea).1)
      (allDiagonalSite ((physicalPairExteriorSiteEquiv p j).symm eb).1))
  have hx : allDiagonalSite ((physicalPairExteriorSiteEquiv p j).symm ea).1 = ea.1 :=
    congrArg Subtype.val ((physicalPairExteriorSiteEquiv p j).apply_symm_apply ea)
  have hy : allDiagonalSite ((physicalPairExteriorSiteEquiv p j).symm eb).1 = eb.1 :=
    congrArg Subtype.val ((physicalPairExteriorSiteEquiv p j).apply_symm_apply eb)
  rw [hx, hy, ← mul_assoc, mul_inv_cancel₀ (sqrt_c_complex_ne_zero p), one_mul]

/-- The selected site energy is `√c` times the selected normalized
energy, at the same ordered rank. -/
theorem Law.orderedEigenvalue_actualSiteHamiltonian {p : Params} (M : Law p)
    (ω : M.Ω) (r : Fin (PhysicalDimension p)) :
    orderedEigenvalue (M.actualSiteHamiltonian ω) (actualSiteRankCast p r) =
      Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) r := by
  set N := M.normalizedPhysicalMatrix ω
  let R : HermitianMatrix (Site p.n p.W) :=
    ⟨Matrix.reindex (physicalIndexSiteEquiv p) (physicalIndexSiteEquiv p) N.1,
      N.2.reindex (physicalIndexSiteEquiv p)⟩
  have hsm : (((Real.sqrt p.c : ℝ) : ℂ) • R.1).IsHermitian := by
    rw [← M.actualSiteHamiltonian_eq_smul_reindex ω]
    exact (M.actualSiteHamiltonian ω).2
  have hmat : M.actualSiteHamiltonian ω = ⟨((Real.sqrt p.c : ℝ) : ℂ) • R.1, hsm⟩ :=
    Subtype.ext (M.actualSiteHamiltonian_eq_smul_reindex ω)
  rw [hmat, orderedEigenvalue_real_smul R (Real.sqrt_pos.mpr p.c_pos) hsm]
  congr 1
  exact orderedEigenvalue_reindex_equiv (physicalIndexSiteEquiv p) N r

/-- The selected reordered pair/exterior energy is `√c` times the selected
normalized energy. -/
theorem Law.orderedEigenvalue_actualPairReorderedHamiltonian_eq_sqrt_mul
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) :
    orderedEigenvalue (M.actualPairReorderedHamiltonian j ω)
        (actualPairRankCast p j r) =
      Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) r := by
  rw [M.orderedEigenvalue_actualPairReorderedHamiltonian j ω r,
    M.orderedEigenvalue_actualSiteHamiltonian ω r]

/-- The read-back exterior Hermitian matrix as a bundled Hermitian matrix. -/
def actualPairStateHRHermitian (p : Params) (j : ZMod p.n)
    (ξ : ActualPairExteriorCouplingState p j) :
    HermitianMatrix (Fin (ActualPairExteriorDimension p j)) :=
  ⟨actualPairStateHR p j ξ, actualPairStateHR_isHermitian p j ξ⟩

/-- Ordered exterior energies of the read-back state are `√c` times
the normalized adjacent-pair exterior energies. -/
theorem Law.orderedEigenvalue_actualPairStateHR {p : Params} (M : Law p)
    (j : Fin p.n) (ω : M.Ω)
    (s : Fin (Fintype.card (PhysicalPairExteriorIndex p j))) :
    orderedEigenvalue (actualPairStateHRHermitian p (j : ZMod p.n)
        (M.actualPairExteriorCouplingState (j : ZMod p.n) ω))
        (Fin.cast (Fintype.card_congr (physicalPairExteriorFinEquiv p j)) s) =
      Real.sqrt p.c *
        orderedEigenvalue (M.normalizedPhysicalPairExteriorMatrix j ω) s := by
  set N := M.normalizedPhysicalPairExteriorMatrix j ω
  let R : HermitianMatrix (Fin (ActualPairExteriorDimension p (j : ZMod p.n))) :=
    ⟨Matrix.reindex (physicalPairExteriorFinEquiv p j)
      (physicalPairExteriorFinEquiv p j) N.1,
      N.2.reindex (physicalPairExteriorFinEquiv p j)⟩
  have hsm : (((Real.sqrt p.c : ℝ) : ℂ) • R.1).IsHermitian := by
    rw [← M.actualPairStateHR_eq_smul_reindex j ω]
    exact actualPairStateHR_isHermitian _ _ _
  have hmat : actualPairStateHRHermitian p (j : ZMod p.n)
      (M.actualPairExteriorCouplingState (j : ZMod p.n) ω) =
      ⟨((Real.sqrt p.c : ℝ) : ℂ) • R.1, hsm⟩ :=
    Subtype.ext (M.actualPairStateHR_eq_smul_reindex j ω)
  rw [hmat, orderedEigenvalue_real_smul R (Real.sqrt_pos.mpr p.c_pos) hsm]
  congr 1
  exact orderedEigenvalue_reindex_equiv (physicalPairExteriorFinEquiv p j) N s

/-!
### The selected-simple Schur incidence condition on pair states
-/

/-- Retained-first pair/exterior index of the adjacent-pair state. -/
abbrev ActualPairReadbackIndex (p : Params) (j : ZMod p.n) :=
  (Unit ⊕ Fin (2 * p.W - 1)) ⊕ Fin (ActualPairExteriorDimension p j)

/-- The reconstructed full Hermitian matrix of an arbitrary pair/exterior
state `(z, ξ)`. -/
def actualPairStateHamiltonian (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    HermitianMatrix (ActualPairReadbackIndex p j) :=
  ⟨actualPairBlockReconstruction p j z ξ,
    actualPairBlockReconstruction_isHermitian p j z ξ⟩

/-- The selected full energy at physical ordered rank `r` (zero-based,
increasing) of the reconstructed state. -/
def actualPairStateSelectedEnergy (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) : ℝ :=
  orderedEigenvalue (actualPairStateHamiltonian p j z ξ) (actualPairRankCast p j r)

/-- The selected-simple Schur incidence condition on a pair/exterior state:
the reconstructed full matrix has simple ordered spectrum, and its selected
rank-`r` energy avoids the exterior spectrum.  This is a deterministic set in
the state space, independent of any probability measure. -/
def actualPairSelectedSimpleSchurIncidence (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p)) :
    Set (HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j) :=
  {y | Function.Injective (orderedEigenvalue (actualPairStateHamiltonian p j y.1 y.2)) ∧
    actualPairStateSelectedEnergy p j r y.1 y.2 ∈
      physicalCoareaPoleFreeSet (actualPairStateHR p j y.2)}

/-- The sampled reconstructed state is the reordered Hamiltonian. -/
theorem Law.actualPairStateHamiltonian_actual {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) :
    actualPairStateHamiltonian p j (M.actualAdjacentPairCoordinates j ω)
        (M.actualPairExteriorCouplingState j ω) =
      M.actualPairReorderedHamiltonian j ω := rfl

/-- On the sampled state, the selected energy is `√c` times the selected
normalized physical energy. -/
theorem Law.actualPairStateSelectedEnergy_actual {p : Params} (M : Law p)
    (j : ZMod p.n) (r : Fin (PhysicalDimension p)) (ω : M.Ω) :
    actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
        (M.actualPairExteriorCouplingState j ω) =
      Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) r :=
  M.orderedEigenvalue_actualPairReorderedHamiltonian_eq_sqrt_mul j ω r

/-- Simplicity of the normalized physical spectrum is simplicity of the
reconstructed pair/exterior spectrum. -/
theorem Law.orderedEigenvalue_injective_actualPairReordered_iff {p : Params}
    (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    Function.Injective (orderedEigenvalue (M.actualPairReorderedHamiltonian j ω)) ↔
      Function.Injective (orderedEigenvalue (M.normalizedPhysicalMatrix ω)) := by
  set N := M.normalizedPhysicalMatrix ω
  have h1 : M.actualPairReorderedHamiltonian j ω =
      ⟨Matrix.reindex (actualPairReadbackEquiv p j).symm
          (actualPairReadbackEquiv p j).symm (M.actualSiteHamiltonian ω).1,
        (M.actualSiteHamiltonian ω).2.reindex (actualPairReadbackEquiv p j).symm⟩ :=
    Subtype.ext (M.actualPairReorderedHamiltonian_eq_reindex j ω)
  let R : HermitianMatrix (Site p.n p.W) :=
    ⟨Matrix.reindex (physicalIndexSiteEquiv p) (physicalIndexSiteEquiv p) N.1,
      N.2.reindex (physicalIndexSiteEquiv p)⟩
  have hsm : (((Real.sqrt p.c : ℝ) : ℂ) • R.1).IsHermitian := by
    rw [← M.actualSiteHamiltonian_eq_smul_reindex ω]
    exact (M.actualSiteHamiltonian ω).2
  have h2 : M.actualSiteHamiltonian ω = ⟨((Real.sqrt p.c : ℝ) : ℂ) • R.1, hsm⟩ :=
    Subtype.ext (M.actualSiteHamiltonian_eq_smul_reindex ω)
  rw [h1, orderedEigenvalue_injective_reindex_iff, h2,
    orderedEigenvalue_injective_real_smul_iff R (Real.sqrt_pos.mpr p.c_pos),
    orderedEigenvalue_injective_reindex_iff]

/-- On the physical full-simple-spectrum event the normalized ordered
spectrum is injective. -/
theorem Law.orderedEigenvalue_injective_normalized_of_mem {p : Params}
    (M : Law p) {ω : M.Ω} (h : ω ∈ M.physicalFullSimpleSpectrumEvent) :
    Function.Injective (orderedEigenvalue (M.normalizedPhysicalMatrix ω)) := by
  set N := M.normalizedPhysicalMatrix ω
  have hsep : ((hermitianOfFinCoordinates (PhysicalDimension p)
      (physicalHermitianFinCoordinates p N) :
        Matrix (Fin (PhysicalDimension p)) (Fin (PhysicalDimension p)) ℂ)).charpoly.Separable :=
    h
  rw [hermitianOfFinCoordinates_physicalHermitianFinCoordinates] at hsep
  have hinj := orderedEigenvalue_injective_of_separable _ hsep
  exact (orderedEigenvalue_injective_reindex_iff (physicalIndexEquivFin p) N).mp hinj

/-- Full simple spectrum, read back on the pair/exterior state. -/
theorem Law.orderedEigenvalue_injective_actualPairReordered_of_mem {p : Params}
    (M : Law p) (j : ZMod p.n) {ω : M.Ω}
    (h : ω ∈ M.physicalFullSimpleSpectrumEvent) :
    Function.Injective (orderedEigenvalue (M.actualPairReorderedHamiltonian j ω)) :=
  (M.orderedEigenvalue_injective_actualPairReordered_iff j ω).mpr
    (M.orderedEigenvalue_injective_normalized_of_mem h)

/-- Selected-energy pair-exterior pole avoidance in the normalized `Fin`
labels is exactly pole-freeness of the selected energy for the
read-back exterior matrix `H_R`. -/
theorem Law.mem_physicalSelectedEnergyPairExteriorPoleFreeEvent_iff
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p))
    (ω : M.Ω) :
    ω ∈ M.physicalSelectedEnergyPairExteriorPoleFreeEvent j r ↔
      actualPairStateSelectedEnergy p (j : ZMod p.n) r
          (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω)
          (M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∈
        physicalCoareaPoleFreeSet (actualPairStateHR p (j : ZMod p.n)
          (M.actualPairExteriorCouplingState (j : ZMod p.n) ω)) := by
  rw [M.actualPairStateSelectedEnergy_actual]
  set ξ := M.actualPairExteriorCouplingState (j : ZMod p.n) ω
  have hc : 0 < Real.sqrt p.c := Real.sqrt_pos.mpr p.c_pos
  change (∀ s, _ ≠ _) ↔ ((actualPairStateHRHermitian p (j : ZMod p.n) ξ).1 -
    ((Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) r : ℝ) : ℂ) •
      (1 : Matrix _ _ ℂ)).det ≠ 0
  rw [ne_eq, det_sub_real_smul_one_eq_zero_iff]
  constructor
  · rintro hfree ⟨s', hs'⟩
    set s := Fin.cast (Fintype.card_congr (physicalPairExteriorFinEquiv p j)).symm s'
    have hs : Fin.cast (Fintype.card_congr (physicalPairExteriorFinEquiv p j)) s = s' := by
      simp [s]
    rw [← hs, M.orderedEigenvalue_actualPairStateHR j ω s] at hs'
    exact hfree s (mul_left_cancel₀ hc.ne' hs')
  · intro hnot s hs
    apply hnot
    refine ⟨Fin.cast (Fintype.card_congr (physicalPairExteriorFinEquiv p j)) s, ?_⟩
    rw [M.orderedEigenvalue_actualPairStateHR j ω s, hs]

/-- The measurable adjacent-pair good event places the pair/exterior
state in the deterministic selected-simple Schur incidence condition. -/
theorem Law.mem_actualPairSelectedSimpleSchurIncidence_of_mem_goodEvent
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p))
    {ω : M.Ω} (h : ω ∈ M.physicalSelectedPairCoareaGoodEvent j r) :
    (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
        M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∈
      actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r :=
  ⟨M.orderedEigenvalue_injective_actualPairReordered_of_mem (j : ZMod p.n) h.1.1,
    (M.mem_physicalSelectedEnergyPairExteriorPoleFreeEvent_iff j r ω).mp h.1.2⟩

/-- Almost every pair/exterior state lies in the selected-simple Schur
incidence condition. -/
theorem Law.ae_mem_actualPairSelectedSimpleSchurIncidence
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P, (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
        M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∈
      actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r := by
  filter_upwards [M.ae_mem_physicalSelectedPairCoareaGoodEvent j r] with ω hω
  exact M.mem_actualPairSelectedSimpleSchurIncidence_of_mem_goodEvent j r hω

/-!
### Deterministic consequences of the incidence condition
-/

/-- The physical block pencil of the read-back state is the reconstructed full
matrix minus `E I`. -/
theorem actualPairBlockPencil_eq_sub (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) (E : ℝ) :
    physicalBlockPencil (actualPairStateV p z) (actualPairStateC p j ξ)ᴴ
        (actualPairStateHR p j ξ) E =
      (actualPairStateHamiltonian p j z ξ).1 - (E : ℂ) • 1 := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [physicalBlockPencil, physicalRetainedPencil, physicalExteriorPencil,
      actualPairStateHamiltonian, actualPairBlockReconstruction, Matrix.one_apply]

/-- Ordered rank readback: on the incidence condition, the selected energy is
the `(r+1)`-st zero of the physical block pencil (one-based ordered zero
rank), i.e. exactly `r` full energies lie strictly below it. -/
theorem actualPairState_orderedZeroRank_of_mem (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    {y : HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j}
    (hy : y ∈ actualPairSelectedSimpleSchurIncidence p j r) :
    orderedZeroRank
        (physicalBlockHermitian (actualPairStateV p y.1)
          (actualPairStateC p j y.2)ᴴ (actualPairStateHR p j y.2)
          (actualPairStateV_isHermitian p y.1)
          (actualPairStateHR_isHermitian p j y.2)
          (actualPairStateSelectedEnergy p j r y.1 y.2)).property =
      (actualPairRankCast p j r).val + 1 := by
  unfold orderedZeroRank
  congr 1
  set H := actualPairStateHamiltonian p j y.1 y.2
  set E := actualPairStateSelectedEnergy p j r y.1 y.2
  have hshift : (H.1 - (E : ℂ) • 1).IsHermitian :=
    H.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  have hchar : (physicalBlockPencil (actualPairStateV p y.1)
      (actualPairStateC p j y.2)ᴴ (actualPairStateHR p j y.2) E).charpoly =
      (H.1 - (E : ℂ) • 1).charpoly := by
    rw [actualPairBlockPencil_eq_sub]
  refine (negativeEigenvalueCount_eq_of_charpoly_eq _ hshift hchar).trans ?_
  have hcount := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio H E
  simp only at hcount
  rw [hcount]
  exact eigenCount_Iio_orderedEigenvalue_of_injective H hy.1 _

/-- Additive inertia readback: exterior negative index plus Schur-compression
negative index equals the ordered rank `r` of the selected energy. -/
theorem actualPairState_additiveInertia_of_mem (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    {y : HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j}
    (hy : y ∈ actualPairSelectedSimpleSchurIncidence p j r) :
    negativeEigenvalueCount
        (physicalExteriorFamily (actualPairStateHR p j y.2)
          (actualPairStateHR_isHermitian p j y.2)
          (actualPairStateSelectedEnergy p j r y.1 y.2)).property +
      negativeEigenvalueCount
        (physicalSchurFamily (actualPairStateV p y.1)
          (actualPairStateC p j y.2)ᴴ (actualPairStateHR p j y.2)
          (actualPairStateV_isHermitian p y.1)
          (actualPairStateHR_isHermitian p j y.2)
          (actualPairStateSelectedEnergy p j r y.1 y.2)).property + 1 =
      (actualPairRankCast p j r).val + 1 :=
  (actualPairPhysicalOrderedRank_iff_additiveSchurSector p j y.2 y.1
    (actualPairStateSelectedEnergy p j r y.1 y.2) hy.2
    (actualPairRankCast p j r)).mp (actualPairState_orderedZeroRank_of_mem p j r hy)

/-- Spectral isolation of the selected energy: no other full ordered energy
and no exterior energy equals it. -/
theorem actualPairState_selectedEnergy_isolated_of_mem (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    {y : HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j}
    (hy : y ∈ actualPairSelectedSimpleSchurIncidence p j r) :
    (∀ s, s ≠ actualPairRankCast p j r →
        orderedEigenvalue (actualPairStateHamiltonian p j y.1 y.2) s ≠
          actualPairStateSelectedEnergy p j r y.1 y.2) ∧
      ∀ s, orderedEigenvalue (actualPairStateHRHermitian p j y.2) s ≠
          actualPairStateSelectedEnergy p j r y.1 y.2 := by
  refine ⟨fun s hs h => hs (hy.1 h), fun s h => hy.2 ?_⟩
  exact (det_sub_real_smul_one_eq_zero_iff (actualPairStateHRHermitian p j y.2) _).mpr
    ⟨s, h⟩

/-- Schur readback of an arbitrary full eigenvector at a pole-free energy:
its retained part is a kernel vector of the Schur compression `F(E)-E`, and
the full vector is the Schur reconstruction `L_E` of its retained part. -/
theorem actualPairState_eigenvector_schurReadback (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) {E : ℝ}
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    {w : ActualPairReadbackIndex p j → ℂ}
    (hw : (actualPairStateHamiltonian p j z ξ).1 *ᵥ w = (E : ℂ) • w) :
    actualPairPhysicalCoareaF p j ξ z E *ᵥ (fun a => w (Sum.inl a)) =
        (E : ℂ) • (fun a => w (Sum.inl a)) ∧
      w = actualPairPhysicalSchurReconstruction p j ξ E (fun a => w (Sum.inl a)) := by
  set v : Unit ⊕ Fin (2 * p.W - 1) → ℂ := fun a => w (Sum.inl a)
  set u : Fin (ActualPairExteriorDimension p j) → ℂ := fun b => w (Sum.inr b)
  set V := actualPairStateV p z
  set C := actualPairStateC p j ξ
  set HR := actualPairStateHR p j ξ
  set R := (HR - (E : ℂ) • 1)⁻¹
  have hwvu : w = Sum.elim v u := by
    ext a
    rcases a with a | a <;> rfl
  have hblk : (actualPairStateHamiltonian p j z ξ).1 *ᵥ w =
      Sum.elim (V *ᵥ v + Cᴴ *ᵥ u) (C *ᵥ v + HR *ᵥ u) := by
    rw [hwvu]
    exact Matrix.fromBlocks_mulVec V Cᴴ C HR (Sum.elim v u)
  rw [hblk] at hw
  have htop : V *ᵥ v + Cᴴ *ᵥ u = (E : ℂ) • v := by
    funext a
    exact congrFun hw (Sum.inl a)
  have hbot : C *ᵥ v + HR *ᵥ u = (E : ℂ) • u := by
    funext b
    exact congrFun hw (Sum.inr b)
  have hpen : (HR - (E : ℂ) • 1) *ᵥ u = -(C *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← hbot]
    abel
  have hinv : R * (HR - (E : ℂ) • 1) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpole)
  have hu : u = -(physicalCoareaT HR C E *ᵥ v) := by
    calc u = (R * (HR - (E : ℂ) • 1)) *ᵥ u := by rw [hinv, Matrix.one_mulVec]
      _ = R *ᵥ (-(C *ᵥ v)) := by rw [← Matrix.mulVec_mulVec, hpen]
      _ = -(physicalCoareaT HR C E *ᵥ v) := by
        rw [Matrix.mulVec_neg, physicalCoareaT, physicalCoareaResolvent,
          ← Matrix.mulVec_mulVec]
  constructor
  · unfold actualPairPhysicalCoareaF physicalCoareaF
    rw [Matrix.sub_mulVec, ← htop]
    change V *ᵥ v - (Cᴴ * R * C) *ᵥ v = V *ᵥ v + Cᴴ *ᵥ u
    rw [hu, Matrix.mulVec_neg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      physicalCoareaT, physicalCoareaResolvent, ← Matrix.mulVec_mulVec]
    abel
  · rw [hwvu]
    unfold actualPairPhysicalSchurReconstruction actualPairPhysicalCoareaT
    rw [← hu]

/-- Positive pair mass, phase-free: at a pole-free energy every nonzero full
eigenvector has nonzero retained (adjacent-pair) part. -/
theorem actualPairState_eigenvector_retained_ne_zero (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) {E : ℝ}
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    {w : ActualPairReadbackIndex p j → ℂ} (hw0 : w ≠ 0)
    (hw : (actualPairStateHamiltonian p j z ξ).1 *ᵥ w = (E : ℂ) • w) :
    (fun a => w (Sum.inl a)) ≠ 0 := by
  intro hv
  apply hw0
  rw [(actualPairState_eigenvector_schurReadback p j z ξ hpole hw).2, hv]
  ext a
  rcases a with a | a
  · rfl
  · simp [actualPairPhysicalSchurReconstruction]

/-- Positive pair mass in the squared-norm form: at a pole-free energy every
nonzero full eigenvector has strictly positive mass on the retained pair
coordinates. This statement is invariant under eigenvector phase. -/
theorem actualPairState_eigenvector_pairMass_pos (p : Params) (j : ZMod p.n)
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) {E : ℝ}
    (hpole : E ∈ physicalCoareaPoleFreeSet (actualPairStateHR p j ξ))
    {w : ActualPairReadbackIndex p j → ℂ} (hw0 : w ≠ 0)
    (hw : (actualPairStateHamiltonian p j z ξ).1 *ᵥ w = (E : ℂ) • w) :
    0 < ∑ a : Unit ⊕ Fin (2 * p.W - 1), ‖w (Sum.inl a)‖ ^ 2 := by
  have hv := actualPairState_eigenvector_retained_ne_zero p j z ξ hpole hw0 hw
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun b _ => sq_nonneg ‖w (Sum.inl b)‖)
    (Finset.mem_univ a))
  exact pow_pos (norm_pos_iff.mpr ha) 2

/-- The selected orthonormal eigenvector of the reconstructed state. -/
def actualPairStateSelectedEigenvector (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) : ActualPairReadbackIndex p j → ℂ :=
  ((actualPairStateHamiltonian p j z ξ).property.eigenvectorBasis
    (Fintype.equivOfCardEq (Fintype.card_fin _) (actualPairRankCast p j r).rev)).ofLp

/-- The selected eigenvector solves the selected eigen-equation. -/
theorem actualPairStateSelectedEigenvector_eigenvector (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    (actualPairStateHamiltonian p j z ξ).1 *ᵥ
        actualPairStateSelectedEigenvector p j r z ξ =
      (actualPairStateSelectedEnergy p j r z ξ : ℂ) •
        actualPairStateSelectedEigenvector p j r z ξ := by
  unfold actualPairStateSelectedEigenvector actualPairStateSelectedEnergy
  rw [(actualPairStateHamiltonian p j z ξ).property.mulVec_eigenvectorBasis,
    hermitianEigenvalues_orderedIndex]
  ext a
  simp

/-- The selected eigenvector is a unit vector. -/
theorem actualPairStateSelectedEigenvector_normalized (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    star (actualPairStateSelectedEigenvector p j r z ξ) ⬝ᵥ
      actualPairStateSelectedEigenvector p j r z ξ = 1 := by
  unfold actualPairStateSelectedEigenvector
  set b := (actualPairStateHamiltonian p j z ξ).property.eigenvectorBasis
  set k := Fintype.equivOfCardEq (Fintype.card_fin _) (actualPairRankCast p j r).rev
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (b k)
  rw [b.orthonormal.1 k, EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm, h]
  simp

/-- The selected eigenvector is nonzero. -/
theorem actualPairStateSelectedEigenvector_ne_zero (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) :
    actualPairStateSelectedEigenvector p j r z ξ ≠ 0 := by
  intro h
  have hn := actualPairStateSelectedEigenvector_normalized p j r z ξ
  rw [h] at hn
  simp at hn

/-- Retained (adjacent-pair) part of the selected eigenvector. -/
def actualPairStateSelectedRetained (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    (z : HermitianCoordinateSpace (2 * p.W))
    (ξ : ActualPairExteriorCouplingState p j) : Unit ⊕ Fin (2 * p.W - 1) → ℂ :=
  fun a => actualPairStateSelectedEigenvector p j r z ξ (Sum.inl a)

/-- Selected compression kernel: on the incidence condition the retained part
of the selected eigenvector is a nonzero kernel vector of `F(E)-E`, and the
selected eigenvector is its Schur reconstruction. -/
theorem actualPairState_selectedCompressionKernel_of_mem (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p))
    {y : HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j}
    (hy : y ∈ actualPairSelectedSimpleSchurIncidence p j r) :
    actualPairStateSelectedRetained p j r y.1 y.2 ≠ 0 ∧
      actualPairPhysicalCoareaF p j y.2 y.1 (actualPairStateSelectedEnergy p j r y.1 y.2) *ᵥ
          actualPairStateSelectedRetained p j r y.1 y.2 =
        (actualPairStateSelectedEnergy p j r y.1 y.2 : ℂ) •
          actualPairStateSelectedRetained p j r y.1 y.2 ∧
      actualPairStateSelectedEigenvector p j r y.1 y.2 =
        actualPairPhysicalSchurReconstruction p j y.2
          (actualPairStateSelectedEnergy p j r y.1 y.2)
          (actualPairStateSelectedRetained p j r y.1 y.2) := by
  have hw := actualPairStateSelectedEigenvector_eigenvector p j r y.1 y.2
  have hrb := actualPairState_eigenvector_schurReadback p j y.1 y.2 hy.2 hw
  exact ⟨actualPairState_eigenvector_retained_ne_zero p j y.1 y.2 hy.2
      (actualPairStateSelectedEigenvector_ne_zero p j r y.1 y.2) hw, hrb.1, hrb.2⟩

/-- Selected compression gap: on the incidence condition the kernel of
`F(E)-E` at the selected energy is exactly the line through the selected
retained vector. -/
theorem actualPairState_selectedCompressionKernel_line_of_mem (p : Params)
    (j : ZMod p.n) (r : Fin (PhysicalDimension p))
    {y : HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j}
    (hy : y ∈ actualPairSelectedSimpleSchurIncidence p j r)
    {v : Unit ⊕ Fin (2 * p.W - 1) → ℂ}
    (hv : actualPairPhysicalCoareaF p j y.2 y.1
        (actualPairStateSelectedEnergy p j r y.1 y.2) *ᵥ v =
      (actualPairStateSelectedEnergy p j r y.1 y.2 : ℂ) • v) :
    ∃ c : ℂ, v = c • actualPairStateSelectedRetained p j r y.1 y.2 := by
  set E := actualPairStateSelectedEnergy p j r y.1 y.2
  have hL := actualPairSchurReconstruction_eigenvector p j y.2 y.1 E v hy.2 hv
  obtain ⟨c, hc⟩ := eigenvector_mem_line_of_orderedEigenvalue_injective
    (actualPairStateHamiltonian p j y.1 y.2) hy.1
    (actualPairStateSelectedEigenvector_ne_zero p j r y.1 y.2)
    (actualPairStateSelectedEigenvector_eigenvector p j r y.1 y.2) hL
  refine ⟨c, ?_⟩
  funext a
  have := congrFun hc (Sum.inl a)
  simpa [actualPairPhysicalSchurReconstruction, actualPairStateSelectedRetained] using this

/-- Phase-free projector readback on the incidence condition: every unit
Schur reconstruction of a kernel vector of `F(E)-E` has the same rank-one
projector as the selected full eigenvector. -/
theorem actualPairState_schurProjector_eq_selected_of_mem (p : Params)
    (j : ZMod p.n) (r : Fin (PhysicalDimension p))
    {y : HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j}
    (hy : y ∈ actualPairSelectedSimpleSchurIncidence p j r)
    {v : Unit ⊕ Fin (2 * p.W - 1) → ℂ}
    (hv : actualPairPhysicalCoareaF p j y.2 y.1
        (actualPairStateSelectedEnergy p j r y.1 y.2) *ᵥ v =
      (actualPairStateSelectedEnergy p j r y.1 y.2 : ℂ) • v)
    (hn : star (actualPairPhysicalSchurReconstruction p j y.2
        (actualPairStateSelectedEnergy p j r y.1 y.2) v) ⬝ᵥ
      actualPairPhysicalSchurReconstruction p j y.2
        (actualPairStateSelectedEnergy p j r y.1 y.2) v = 1) :
    Matrix.vecMulVec
        (actualPairPhysicalSchurReconstruction p j y.2
          (actualPairStateSelectedEnergy p j r y.1 y.2) v)
        (star (actualPairPhysicalSchurReconstruction p j y.2
          (actualPairStateSelectedEnergy p j r y.1 y.2) v)) =
      Matrix.vecMulVec (actualPairStateSelectedEigenvector p j r y.1 y.2)
        (star (actualPairStateSelectedEigenvector p j r y.1 y.2)) :=
  vecMulVec_eq_of_eigenvector_line (actualPairStateHamiltonian p j y.1 y.2) hy.1
    (actualPairStateSelectedEigenvector_eigenvector p j r y.1 y.2)
    (actualPairSchurReconstruction_eigenvector p j y.2 y.1 _ v hy.2 hv)
    (actualPairStateSelectedEigenvector_normalized p j r y.1 y.2) hn

/-- The reindexed original-site ordered eigenvector is a unit vector. -/
theorem Law.actualPairReindexVector_siteOrdered_normalized {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) (r : Fin (PhysicalDimension p)) :
    star (actualPairReindexVector p j (M.actualSiteOrderedEigenvector ω r)) ⬝ᵥ
      actualPairReindexVector p j (M.actualSiteOrderedEigenvector ω r) = 1 := by
  set b := (M.actualSiteHamiltonian ω).property.eigenvectorBasis
  set k := Fintype.equivOfCardEq (Fintype.card_fin _) (actualSiteRankCast p r).rev
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (b k)
  rw [b.orthonormal.1 k, EuclideanSpace.inner_eq_star_dotProduct] at h
  have hsum : star (actualPairReindexVector p j (M.actualSiteOrderedEigenvector ω r)) ⬝ᵥ
      actualPairReindexVector p j (M.actualSiteOrderedEigenvector ω r) =
      star (b k).ofLp ⬝ᵥ (b k).ofLp := by
    unfold dotProduct
    exact Equiv.sum_comp (actualPairReadbackEquiv p j)
      (fun x => star ((b k).ofLp x) * (b k).ofLp x)
  rw [hsum, dotProduct_comm, h]
  simp

/-- Phase-free projector readback for the sampled state: on the incidence
condition, the projector of every unit Schur reconstruction of a kernel vector
of `F(E)-E` is the deterministic reindexing of the original-site selected
ordered eigenprojector. -/
theorem Law.actualPairSchurProjector_eq_siteProjector_of_mem {p : Params}
    (M : Law p) (j : ZMod p.n) (r : Fin (PhysicalDimension p)) {ω : M.Ω}
    (hy : (M.actualAdjacentPairCoordinates j ω, M.actualPairExteriorCouplingState j ω) ∈
      actualPairSelectedSimpleSchurIncidence p j r)
    {v : Unit ⊕ Fin (2 * p.W - 1) → ℂ}
    (hv : actualPairPhysicalCoareaF p j (M.actualPairExteriorCouplingState j ω)
        (M.actualAdjacentPairCoordinates j ω)
        (actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
          (M.actualPairExteriorCouplingState j ω)) *ᵥ v =
      (actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
        (M.actualPairExteriorCouplingState j ω) : ℂ) • v)
    (hn : star (actualPairPhysicalSchurReconstruction p j
        (M.actualPairExteriorCouplingState j ω)
        (actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
          (M.actualPairExteriorCouplingState j ω)) v) ⬝ᵥ
      actualPairPhysicalSchurReconstruction p j (M.actualPairExteriorCouplingState j ω)
        (actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
          (M.actualPairExteriorCouplingState j ω)) v = 1) :
    Matrix.vecMulVec
        (actualPairPhysicalSchurReconstruction p j (M.actualPairExteriorCouplingState j ω)
          (actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
            (M.actualPairExteriorCouplingState j ω)) v)
        (star (actualPairPhysicalSchurReconstruction p j
          (M.actualPairExteriorCouplingState j ω)
          (actualPairStateSelectedEnergy p j r (M.actualAdjacentPairCoordinates j ω)
            (M.actualPairExteriorCouplingState j ω)) v)) =
      Matrix.reindex (actualPairReadbackEquiv p j).symm (actualPairReadbackEquiv p j).symm
        (Matrix.vecMulVec (M.actualSiteOrderedEigenvector ω r)
          (star (M.actualSiteOrderedEigenvector ω r))) := by
  have hsite := (M.actualPairSelectedRankEigenpairProjector_reindex j ω r)
  simp only at hsite
  rw [← hsite.2]
  exact vecMulVec_eq_of_eigenvector_line (M.actualPairReorderedHamiltonian j ω) hy.1
    hsite.1 (actualPairSchurReconstruction_eigenvector p j _ _ _ v hy.2 hv)
    (M.actualPairReindexVector_siteOrdered_normalized j ω r) hn

/-!
### Measurability of the incidence condition and measure transfer
-/

/-- The reconstructed full Hermitian matrix depends measurably on the state. -/
theorem measurable_actualPairStateHamiltonian (p : Params) (j : ZMod p.n) :
    Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
        ActualPairExteriorCouplingState p j =>
      actualPairStateHamiltonian p j y.1 y.2) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  have hV : Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j =>
        (hermitianOfFinCoordinates (2 * p.W) y.1).1) :=
    measurable_coe_hermitianMatrix.comp
      ((measurable_hermitianOfFinCoordinates _).comp measurable_fst)
  have hHR : Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j => y.2.1.1) :=
    measurable_coe_hermitianMatrix.comp (measurable_fst.comp measurable_snd)
  have hC : Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j => y.2.2) :=
    measurable_snd.comp measurable_snd
  intro a b
  rcases a with a | a <;> rcases b with b | b
  · exact hV.eval_matrix
  · exact Complex.continuous_conj.measurable.comp hC.eval_matrix
  · exact hC.eval_matrix
  · exact hHR.eval_matrix

/-- The selected energy depends measurably on the state. -/
theorem measurable_actualPairStateSelectedEnergy (p : Params) (j : ZMod p.n)
    (r : Fin (PhysicalDimension p)) :
    Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
        ActualPairExteriorCouplingState p j =>
      actualPairStateSelectedEnergy p j r y.1 y.2) :=
  (measurable_orderedEigenvalue _).comp (measurable_actualPairStateHamiltonian p j)

/-- Determinants of measurable complex matrix families are measurable. -/
theorem measurable_det_comp {β ι : Type*} [MeasurableSpace β] [Fintype ι] [DecidableEq ι]
    {A : β → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun x => (A x).det) := by
  simp only [Matrix.det_apply]
  apply Finset.measurable_sum
  intro σ _
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i _
  exact hA.eval_matrix

/-- The selected-simple Schur incidence condition is a measurable subset of
the pair/exterior state space. -/
theorem measurableSet_actualPairSelectedSimpleSchurIncidence (p : Params)
    (j : ZMod p.n) (r : Fin (PhysicalDimension p)) :
    MeasurableSet (actualPairSelectedSimpleSchurIncidence p j r) := by
  have hev : ∀ s, Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j =>
        orderedEigenvalue (actualPairStateHamiltonian p j y.1 y.2) s) := fun s =>
    (measurable_orderedEigenvalue s).comp (measurable_actualPairStateHamiltonian p j)
  have hinj : MeasurableSet {y : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j |
        Function.Injective (orderedEigenvalue (actualPairStateHamiltonian p j y.1 y.2))} := by
    simp only [Function.Injective, Set.ofPred_forall]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
    by_cases hab : a = b
    · simp [hab]
    · have h := (measurableSet_eq_fun (hev a) (hev b)).compl
      convert h using 1
      ext y
      simp [hab]
  have hpole : MeasurableSet {y : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j |
        actualPairStateSelectedEnergy p j r y.1 y.2 ∈
          physicalCoareaPoleFreeSet (actualPairStateHR p j y.2)} := by
    have hmat : Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
        ActualPairExteriorCouplingState p j =>
          actualPairStateHR p j y.2 -
            ((actualPairStateSelectedEnergy p j r y.1 y.2 : ℝ) : ℂ) • 1) := by
      rw [Matrix.measurable_iff]
      intro a b
      have hHR : Measurable (fun y : HermitianCoordinateSpace (2 * p.W) ×
          ActualPairExteriorCouplingState p j => y.2.1.1) :=
        measurable_coe_hermitianMatrix.comp (measurable_fst.comp measurable_snd)
      have hE := Complex.measurable_ofReal.comp
        (measurable_actualPairStateSelectedEnergy p j r)
      exact hHR.eval_matrix.sub (hE.mul_const _)
    exact ((measurableSet_singleton (0 : ℂ)).preimage (measurable_det_comp hmat)).compl
  exact hinj.inter hpole

/-- Pushforward form: the pair/exterior law gives null mass to the
complement of the incidence condition. -/
theorem Law.actualPairExteriorLaw_compl_incidence {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    M.actualPairExteriorLaw (j : ZMod p.n)
      (actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r)ᶜ = 0 := by
  unfold Law.actualPairExteriorLaw
  rw [Measure.map_apply ((M.measurable_actualAdjacentPairCoordinates _).prodMk
      (M.measurable_actualPairExteriorCouplingState _))
    (measurableSet_actualPairSelectedSimpleSchurIncidence p _ r).compl]
  exact ae_iff.mp (M.ae_mem_actualPairSelectedSimpleSchurIncidence j r)

/-- The pair/exterior law is almost surely supported on the incidence
condition. -/
theorem Law.ae_actualPairExteriorLaw_mem_incidence {p : Params} (M : Law p)
    (j : Fin p.n) (r : Fin (PhysicalDimension p)) :
    ∀ᵐ y ∂M.actualPairExteriorLaw (j : ZMod p.n),
      y ∈ actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r :=
  ae_iff.mpr (M.actualPairExteriorLaw_compl_incidence j r)

/-- Transfer through the unconditional Gaussian split: for every measurable
nonnegative observable, the integral equals the split integral of the
observable restricted to the incidence condition. -/
theorem Law.lintegral_actualPairExterior_eq_physicalSplit_incidence
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p))
    {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (Φ : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p (j : ZMod p.n) → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ ω, Φ (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
      M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∂M.P) =
      ∫⁻ z, (actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r).indicator Φ
          (physicalActualPairSplitReadback (p := p) (j := (j : ZMod p.n)) z)
        ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0)
          (physicalExposedPairResidualMeasure p hs0 hsc hsb)
          (M.actualPairExteriorStateLaw (j : ZMod p.n)) := by
  set S := actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r
  have hS := measurableSet_actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r
  calc (∫⁻ ω, Φ (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
        M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∂M.P) =
      ∫⁻ ω, S.indicator Φ (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
        M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∂M.P := by
        apply lintegral_congr_ae
        filter_upwards [M.ae_mem_actualPairSelectedSimpleSchurIncidence j r] with ω hω
        rw [Set.indicator_of_mem hω]
    _ = _ := M.lintegral_actualPairExterior_eq_physicalSplit_unconditional
        (j : ZMod p.n) hs0 hsc hsb (S.indicator Φ) (hΦ.indicator hS)

/-- Split-side incidence: almost every residual-plus-fresh split sample reads
back to a state in the selected-simple Schur incidence condition.  The proof
passes the indicator of the complement through
`Law.lintegral_actualPairExterior_eq_physicalSplit_unconditional`. -/
theorem Law.ae_physicalSplit_readback_mem_incidence
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p))
    {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b) :
    ∀ᵐ z ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb)
        (M.actualPairExteriorStateLaw (j : ZMod p.n)),
      physicalActualPairSplitReadback (p := p) (j := (j : ZMod p.n)) z ∈
        actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r := by
  set S := actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r
  have hS := measurableSet_actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r
  have hR := measurable_physicalActualPairSplitReadback (p := p) (j := (j : ZMod p.n))
  have hactual := (M.measurable_actualAdjacentPairCoordinates (j : ZMod p.n)).prodMk
    (M.measurable_actualPairExteriorCouplingState (j : ZMod p.n))
  have h := M.lintegral_actualPairExterior_eq_physicalSplit_unconditional
    (j : ZMod p.n) hs0 hsc hsb (Sᶜ.indicator 1) (measurable_one.indicator hS.compl)
  have h0 : M.P ((fun ω => (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
      M.actualPairExteriorCouplingState (j : ZMod p.n) ω)) ⁻¹' Sᶜ) = 0 :=
    ae_iff.mp (M.ae_mem_actualPairSelectedSimpleSchurIncidence j r)
  have hsplit : physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
      (coareaGUEVariance_nonneg p hs0)
      (physicalExposedPairResidualMeasure p hs0 hsc hsb)
      (M.actualPairExteriorStateLaw (j : ZMod p.n))
      (physicalActualPairSplitReadback (p := p) (j := (j : ZMod p.n)) ⁻¹' Sᶜ) =
      M.P ((fun ω => (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
        M.actualPairExteriorCouplingState (j : ZMod p.n) ω)) ⁻¹' Sᶜ) := by
    rw [← lintegral_indicator_one (hS.compl.preimage hactual),
      ← lintegral_indicator_one (hS.compl.preimage hR)]
    exact h.symm
  rw [ae_iff]
  exact hsplit.trans h0

/-- Fixed-exterior Fubini form of split-side incidence: for almost every
residual, almost every exterior state, and almost every fresh GUE block, the
total block `residual + fresh` together with that exterior lies in the
incidence condition. -/
theorem Law.ae_ae_ae_physicalSplit_mem_incidence
    {p : Params} (M : Law p) (j : Fin p.n) (r : Fin (PhysicalDimension p))
    {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b) :
    ∀ᵐ v ∂physicalExposedPairResidualMeasure p hs0 hsc hsb,
      ∀ᵐ ξ ∂M.actualPairExteriorStateLaw (j : ZMod p.n),
        ∀ᵐ g ∂hermitianGUECoordinateMeasure (2 * p.W) (coareaGUEVariance p s)
            (coareaGUEVariance_nonneg p hs0),
          (v + g, ξ) ∈ actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r := by
  have h := M.ae_physicalSplit_readback_mem_incidence j r hs0 hsc hsb
  unfold physicalHermitianSplitMeasure at h
  have h1 := Measure.ae_ae_of_ae_prod h
  have h2 := Measure.ae_ae_of_ae_prod h1
  filter_upwards [h2] with v hv
  filter_upwards [hv] with ξ hξ
  exact hξ

/-!
### Phase-free readback of the measurable pair mass
-/

/-- Two unit vectors on one simple eigenline differ by a unimodular phase. -/
theorem eigenvector_eq_unimodular_smul_of_line
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : HermitianMatrix ι)
    (hinj : Function.Injective (orderedEigenvalue A)) {E : ℝ} {u w : ι → ℂ}
    (hw : A.1 *ᵥ w = (E : ℂ) • w) (hu : A.1 *ᵥ u = (E : ℂ) • u)
    (hwn : star w ⬝ᵥ w = 1) (hun : star u ⬝ᵥ u = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ u = c • w := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hwn
  obtain ⟨c, rfl⟩ := eigenvector_mem_line_of_orderedEigenvalue_injective A hinj hw0 hw hu
  refine ⟨c, ?_, rfl⟩
  have hcc : star c * c = 1 := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, hwn] at hun
    simpa [smul_eq_mul, mul_comm] using hun
  have h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hcc, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := norm_nonneg c
  nlinarith

/-- Simplicity of the normalized physical spectrum is simplicity of the
site spectrum. -/
theorem Law.orderedEigenvalue_injective_actualSite_iff {p : Params}
    (M : Law p) (ω : M.Ω) :
    Function.Injective (orderedEigenvalue (M.actualSiteHamiltonian ω)) ↔
      Function.Injective (orderedEigenvalue (M.normalizedPhysicalMatrix ω)) := by
  set N := M.normalizedPhysicalMatrix ω
  let R : HermitianMatrix (Site p.n p.W) :=
    ⟨Matrix.reindex (physicalIndexSiteEquiv p) (physicalIndexSiteEquiv p) N.1,
      N.2.reindex (physicalIndexSiteEquiv p)⟩
  have hsm : (((Real.sqrt p.c : ℝ) : ℂ) • R.1).IsHermitian := by
    rw [← M.actualSiteHamiltonian_eq_smul_reindex ω]
    exact (M.actualSiteHamiltonian ω).2
  have h2 : M.actualSiteHamiltonian ω = ⟨((Real.sqrt p.c : ℝ) : ℂ) • R.1, hsm⟩ :=
    Subtype.ext (M.actualSiteHamiltonian_eq_smul_reindex ω)
  rw [h2, orderedEigenvalue_injective_real_smul_iff R (Real.sqrt_pos.mpr p.c_pos),
    orderedEigenvalue_injective_reindex_iff]

/-- Site/finite-ordinal equivalence used by the measurable eigenvector. -/
def physicalSiteFinEquiv (p : Params) : Site p.n p.W ≃ Fin (PhysicalDimension p) :=
  (physicalIndexSiteEquiv p).symm.trans (physicalIndexEquivFin p)

/-- The measurable phase-fixed ordered eigenvector of the normalized matrix,
read on original sites. -/
def Law.physicalMeasurableSiteEigenvector {p : Params} (M : Law p) (ω : M.Ω)
    (r : Fin (PhysicalDimension p)) : Site p.n p.W → ℂ :=
  fun x => physicalMeasurableOrderedEigenvectorFin p r (M.normalizedPhysicalMatrix ω)
    (physicalSiteFinEquiv p x)

/-- On simple spectrum, the measurable site eigenvector solves the
selected eigen-equation for `H` at energy `√c λ_r`. -/
theorem Law.physicalMeasurableSiteEigenvector_eigenvector {p : Params} (M : Law p)
    {ω : M.Ω} (h : ω ∈ M.physicalFullSimpleSpectrumEvent)
    (r : Fin (PhysicalDimension p)) :
    M.H ω *ᵥ M.physicalMeasurableSiteEigenvector ω r =
      (orderedEigenvalue (M.actualSiteHamiltonian ω) (actualSiteRankCast p r) : ℂ) •
        M.physicalMeasurableSiteEigenvector ω r := by
  set N := M.normalizedPhysicalMatrix ω
  let A : physicalSimpleSpectrumMatrices p := ⟨N, h⟩
  set u := physicalSimpleOrderedEigenvectorFin p r A
  have hu := physicalSimpleOrderedEigenvectorFin_eigenvector p r A
  have hlam : orderedEigenvalue (physicalHermitianFinReindex p N) (physicalEigenRank p r) =
      orderedEigenvalue N r :=
    orderedEigenvalue_reindex_equiv (physicalIndexEquivFin p) N r
  rw [M.orderedEigenvalue_actualSiteHamiltonian ω r]
  have hvec : M.physicalMeasurableSiteEigenvector ω r = fun x => u (physicalSiteFinEquiv p x) := by
    funext x
    unfold Law.physicalMeasurableSiteEigenvector
    rw [show M.normalizedPhysicalMatrix ω = A.1 from rfl,
      physicalMeasurableOrderedEigenvectorFin_apply_simple]
  rw [hvec]
  funext x
  have hrow := congrFun hu (physicalSiteFinEquiv p x)
  rw [hlam] at hrow
  have hH : ∀ y, M.H ω x y = ((Real.sqrt p.c : ℝ) : ℂ) *
      (physicalHermitianFinReindex p N).1 (physicalSiteFinEquiv p x)
        (physicalSiteFinEquiv p y) := by
    intro y
    have := congrFun (congrFun (M.actualSiteHamiltonian_eq_smul_reindex ω) x) y
    simpa [physicalHermitianFinReindex, physicalSiteFinEquiv, Law.actualSiteHamiltonian]
      using this
  simp only [Matrix.mulVec, dotProduct, hH, Pi.smul_apply, smul_eq_mul] at hrow ⊢
  have hsum := Equiv.sum_comp (physicalSiteFinEquiv p)
    (fun k => (physicalHermitianFinReindex p N).1 (physicalSiteFinEquiv p x) k * u k)
  simp only at hsum
  calc ∑ y, ((Real.sqrt p.c : ℝ) : ℂ) * (physicalHermitianFinReindex p N).1
          (physicalSiteFinEquiv p x) (physicalSiteFinEquiv p y) * u (physicalSiteFinEquiv p y) =
        ((Real.sqrt p.c : ℝ) : ℂ) * ∑ y, (physicalHermitianFinReindex p N).1
          (physicalSiteFinEquiv p x) (physicalSiteFinEquiv p y) *
            u (physicalSiteFinEquiv p y) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ((Real.sqrt p.c : ℝ) : ℂ) * ((orderedEigenvalue N r : ℂ) * u (physicalSiteFinEquiv p x)) := by
        rw [hsum, hrow]
        simp [u]
    _ = _ := by push_cast; ring

/-- On simple spectrum, the measurable site eigenvector is a unit vector. -/
theorem Law.physicalMeasurableSiteEigenvector_normalized {p : Params} (M : Law p)
    {ω : M.Ω} (h : ω ∈ M.physicalFullSimpleSpectrumEvent)
    (r : Fin (PhysicalDimension p)) :
    star (M.physicalMeasurableSiteEigenvector ω r) ⬝ᵥ
      M.physicalMeasurableSiteEigenvector ω r = 1 := by
  let A : physicalSimpleSpectrumMatrices p := ⟨M.normalizedPhysicalMatrix ω, h⟩
  set u := physicalSimpleOrderedEigenvectorFin p r A
  have hvec : M.physicalMeasurableSiteEigenvector ω r = fun x => u (physicalSiteFinEquiv p x) := by
    funext x
    unfold Law.physicalMeasurableSiteEigenvector
    rw [show M.normalizedPhysicalMatrix ω = A.1 from rfl,
      physicalMeasurableOrderedEigenvectorFin_apply_simple]
  rw [hvec]
  have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u
  rw [norm_physicalSimpleOrderedEigenvectorFin, EuclideanSpace.inner_eq_star_dotProduct] at hn
  have hsum : star (fun x => u (physicalSiteFinEquiv p x)) ⬝ᵥ
      (fun x => u (physicalSiteFinEquiv p x)) = star u.ofLp ⬝ᵥ u.ofLp := by
    unfold dotProduct
    exact Equiv.sum_comp (physicalSiteFinEquiv p) (fun k => star (u.ofLp k) * u.ofLp k)
  rw [hsum, dotProduct_comm, hn]
  simp

/-- The original-site Mathlib ordered eigenvector is a unit vector. -/
theorem Law.actualSiteOrderedEigenvector_normalized {p : Params} (M : Law p)
    (ω : M.Ω) (r : Fin (PhysicalDimension p)) :
    star ((M.actualSiteOrderedEigenvector ω r).ofLp) ⬝ᵥ
      (M.actualSiteOrderedEigenvector ω r).ofLp = 1 := by
  have hn := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (M.actualSiteOrderedEigenvector ω r)
  rw [Law.actualSiteOrderedEigenvector,
    (M.actualSiteHamiltonian ω).property.eigenvectorBasis.orthonormal.1,
    EuclideanSpace.inner_eq_star_dotProduct] at hn
  rw [dotProduct_comm]
  unfold Law.actualSiteOrderedEigenvector
  rw [hn]
  simp

/-- Phase-free entrywise readback: on simple spectrum the measurable
normalized eigenvector and the site eigenvector have the same entry
moduli. -/
theorem Law.nnnorm_physicalMeasurableSiteEigenvector {p : Params} (M : Law p)
    {ω : M.Ω} (h : ω ∈ M.physicalFullSimpleSpectrumEvent)
    (r : Fin (PhysicalDimension p)) (x : Site p.n p.W) :
    ‖M.physicalMeasurableSiteEigenvector ω r x‖₊ =
      ‖(M.actualSiteOrderedEigenvector ω r).ofLp x‖₊ := by
  have hinj := (M.orderedEigenvalue_injective_actualSite_iff ω).mpr
    (M.orderedEigenvalue_injective_normalized_of_mem h)
  obtain ⟨c, hc, hcu⟩ := eigenvector_eq_unimodular_smul_of_line (M.actualSiteHamiltonian ω)
    hinj (M.actualSiteOrderedEigenvector_eigenvector ω r)
    (M.physicalMeasurableSiteEigenvector_eigenvector h r)
    (M.actualSiteOrderedEigenvector_normalized ω r)
    (M.physicalMeasurableSiteEigenvector_normalized h r)
  rw [hcu, Pi.smul_apply, smul_eq_mul, nnnorm_mul]
  have : ‖c‖₊ = 1 := by
    ext
    exact hc
  rw [this, one_mul]

/-- The measurable block weight is the site eigenvector's mass on that
block, on simple spectrum. -/
theorem Law.physicalMeasurableBlockMassWeight_eq_actualSite {p : Params}
    (M : Law p) {ω : M.Ω} (h : ω ∈ M.physicalFullSimpleSpectrumEvent)
    (r : Fin (PhysicalDimension p)) (k : Fin p.n) :
    physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω) k =
      ∑ a : Fin p.W, ‖(M.actualSiteOrderedEigenvector ω r).ofLp ((k : ZMod p.n), a)‖₊ ^ 2 := by
  unfold physicalMeasurableBlockMassWeight
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← M.nnnorm_physicalMeasurableSiteEigenvector h r]
  unfold Law.physicalMeasurableSiteEigenvector physicalSiteFinEquiv
  rw [Equiv.trans_apply]
  have hx : (physicalIndexSiteEquiv p).symm ((k : ZMod p.n), a) = ⟨k, a⟩ :=
    (physicalIndexSiteEquiv p).symm_apply_apply ⟨k, a⟩
  rw [hx]

/-- Summing over the two blocks of the adjacent pair is summing over the
retained `Fin (2W)` coordinates. -/
theorem sum_adjacentPairSite {p : Params} (j : ZMod p.n) {β : Type*} [AddCommMonoid β]
    (f : Site p.n p.W → β) :
    ∑ b : Fin (2 * p.W), f (adjacentPairSite p j b) =
      ∑ a : Fin p.W, f (j, a) + ∑ a : Fin p.W, f (j + 1, a) := by
  let g : Fin (p.W + p.W) → Site p.n p.W :=
    Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v))
  calc ∑ b : Fin (2 * p.W), f (adjacentPairSite p j b) =
      ∑ c : Fin (p.W + p.W), f (g c) :=
        Equiv.sum_comp (finCongr (two_mul p.W)) (fun c : Fin (p.W + p.W) => f (g c))
    _ = _ := by
        rw [Fin.sum_univ_add]
        simp only [g, Fin.addCases_left, Fin.addCases_right]

/-- Phase-free pair-mass readback: the measurable selected adjacent-pair mass
of the good event is the selected site eigenvector's squared mass on
the two adjacent blocks. -/
theorem Law.physicalSelectedPairMass_eq_actualPairMass {p : Params}
    (M : Law p) (j : Fin p.n) {ω : M.Ω} (h : ω ∈ M.physicalFullSimpleSpectrumEvent)
    (r : Fin (PhysicalDimension p)) :
    physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω) j +
        physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω)
          (adjacentPairNext p j) =
      ∑ b : Fin (2 * p.W),
        ‖(M.actualSiteOrderedEigenvector ω r).ofLp
          (adjacentPairSite p (j : ZMod p.n) b)‖₊ ^ 2 := by
  rw [M.physicalMeasurableBlockMassWeight_eq_actualSite h,
    M.physicalMeasurableBlockMassWeight_eq_actualSite h, adjacentPairNext_cast]
  exact (sum_adjacentPairSite (p := p) (j : ZMod p.n)
    (fun x => ‖(M.actualSiteOrderedEigenvector ω r).ofLp x‖₊ ^ 2)).symm

/-- The retained part of the reindexed site eigenvector is its restriction to
the adjacent-pair sites. -/
theorem sum_retained_actualPairReindexVector {p : Params} (j : ZMod p.n)
    (v : Site p.n p.W → ℂ) :
    ∑ a : Unit ⊕ Fin (2 * p.W - 1), ‖actualPairReindexVector p j v (Sum.inl a)‖₊ ^ 2 =
      ∑ b : Fin (2 * p.W), ‖v (adjacentPairSite p j b)‖₊ ^ 2 := by
  exact Equiv.sum_comp (actualPairSelectedEquiv p).symm
    (fun b => ‖v (adjacentPairSite p j b)‖₊ ^ 2)

/-- Positive pair mass follows deterministically from the incidence condition:
the selected site eigenvector has strictly positive squared mass on the
two adjacent blocks. -/
theorem Law.actualPairMass_pos_of_mem_incidence {p : Params} (M : Law p)
    (j : ZMod p.n) (r : Fin (PhysicalDimension p)) {ω : M.Ω}
    (hy : (M.actualAdjacentPairCoordinates j ω, M.actualPairExteriorCouplingState j ω) ∈
      actualPairSelectedSimpleSchurIncidence p j r) :
    0 < ∑ b : Fin (2 * p.W),
      ‖(M.actualSiteOrderedEigenvector ω r).ofLp (adjacentPairSite p j b)‖₊ ^ 2 := by
  have hsite := M.actualPairSelectedRankEigenpairProjector_reindex j ω r
  simp only at hsite
  set w := actualPairReindexVector p j (M.actualSiteOrderedEigenvector ω r)
  have hw0 : w ≠ 0 := by
    intro hz
    have hn : star w ⬝ᵥ w = 1 := M.actualPairReindexVector_siteOrdered_normalized j ω r
    rw [hz] at hn
    simp at hn
  have hv := actualPairState_eigenvector_retained_ne_zero p j _ _ hy.2 hw0 hsite.1
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  rw [← sum_retained_actualPairReindexVector]
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a))
  exact pow_pos (nnnorm_pos.mpr ha) 2

/-!
### Bundled almost-sure readback
-/

/-- Deterministic readback of the measurable good event: at every outcome of
`physicalSelectedPairCoareaGoodEvent j r` the pair/exterior state lies
in the incidence condition, its selected energy is `√c λ_r`, the ordered rank
and additive inertia identities hold, the selected Schur compression has the
retained selected eigenvector as a nonzero kernel vector, and the measurable
selected pair mass equals the site eigenvector's (positive) mass on the
two adjacent blocks. -/
theorem Law.actualPairGoodEventReadback {p : Params} (M : Law p) (j : Fin p.n)
    (r : Fin (PhysicalDimension p)) {ω : M.Ω}
    (h : ω ∈ M.physicalSelectedPairCoareaGoodEvent j r) :
    let y := (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
      M.actualPairExteriorCouplingState (j : ZMod p.n) ω)
    let E := actualPairStateSelectedEnergy p (j : ZMod p.n) r y.1 y.2
    y ∈ actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r ∧
      E = Real.sqrt p.c * orderedEigenvalue (M.normalizedPhysicalMatrix ω) r ∧
      orderedZeroRank
          (physicalBlockHermitian (actualPairStateV p y.1)
            (actualPairStateC p (j : ZMod p.n) y.2)ᴴ
            (actualPairStateHR p (j : ZMod p.n) y.2)
            (actualPairStateV_isHermitian p y.1)
            (actualPairStateHR_isHermitian p (j : ZMod p.n) y.2) E).property =
        (actualPairRankCast p (j : ZMod p.n) r).val + 1 ∧
      negativeEigenvalueCount
          (physicalExteriorFamily (actualPairStateHR p (j : ZMod p.n) y.2)
            (actualPairStateHR_isHermitian p (j : ZMod p.n) y.2) E).property +
        negativeEigenvalueCount
          (physicalSchurFamily (actualPairStateV p y.1)
            (actualPairStateC p (j : ZMod p.n) y.2)ᴴ
            (actualPairStateHR p (j : ZMod p.n) y.2)
            (actualPairStateV_isHermitian p y.1)
            (actualPairStateHR_isHermitian p (j : ZMod p.n) y.2) E).property + 1 =
        (actualPairRankCast p (j : ZMod p.n) r).val + 1 ∧
      actualPairStateSelectedRetained p (j : ZMod p.n) r y.1 y.2 ≠ 0 ∧
      actualPairPhysicalCoareaF p (j : ZMod p.n) y.2 y.1 E *ᵥ
          actualPairStateSelectedRetained p (j : ZMod p.n) r y.1 y.2 =
        (E : ℂ) • actualPairStateSelectedRetained p (j : ZMod p.n) r y.1 y.2 ∧
      physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω) j +
          physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω)
            (adjacentPairNext p j) =
        ∑ b : Fin (2 * p.W),
          ‖(M.actualSiteOrderedEigenvector ω r).ofLp
            (adjacentPairSite p (j : ZMod p.n) b)‖₊ ^ 2 ∧
      0 < ∑ b : Fin (2 * p.W),
          ‖(M.actualSiteOrderedEigenvector ω r).ofLp
            (adjacentPairSite p (j : ZMod p.n) b)‖₊ ^ 2 := by
  intro y E
  have hy := M.mem_actualPairSelectedSimpleSchurIncidence_of_mem_goodEvent j r h
  have hker := actualPairState_selectedCompressionKernel_of_mem p (j : ZMod p.n) r hy
  exact ⟨hy, M.actualPairStateSelectedEnergy_actual (j : ZMod p.n) r ω,
    actualPairState_orderedZeroRank_of_mem p (j : ZMod p.n) r hy,
    actualPairState_additiveInertia_of_mem p (j : ZMod p.n) r hy,
    hker.1, hker.2.1, M.physicalSelectedPairMass_eq_actualPairMass j h.1.1 r,
    M.actualPairMass_pos_of_mem_incidence (j : ZMod p.n) r hy⟩

/-- Almost-sure form of `Law.actualPairGoodEventReadback`. -/
theorem Law.ae_actualPairGoodEventReadback {p : Params} (M : Law p) (j : Fin p.n)
    (r : Fin (PhysicalDimension p)) :
    ∀ᵐ ω ∂M.P,
      (M.actualAdjacentPairCoordinates (j : ZMod p.n) ω,
          M.actualPairExteriorCouplingState (j : ZMod p.n) ω) ∈
        actualPairSelectedSimpleSchurIncidence p (j : ZMod p.n) r ∧
      physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω) j +
          physicalMeasurableBlockMassWeight p r (M.normalizedPhysicalMatrix ω)
            (adjacentPairNext p j) =
        ∑ b : Fin (2 * p.W),
          ‖(M.actualSiteOrderedEigenvector ω r).ofLp
            (adjacentPairSite p (j : ZMod p.n) b)‖₊ ^ 2 := by
  filter_upwards [M.ae_mem_physicalSelectedPairCoareaGoodEvent j r] with ω hω
  exact ⟨M.mem_actualPairSelectedSimpleSchurIncidence_of_mem_goodEvent j r hω,
    M.physicalSelectedPairMass_eq_actualPairMass j hω.1.1 r⟩

end GaussianRing

end CoareaNative.BlockBand
