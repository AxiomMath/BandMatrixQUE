module

public import BlockBand.Native.CEH.Flow.ResolventCalc
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Resolvent chains: deterministic calculus

## Setting

`V` is a finite-dimensional real normed space, `A(y) = A₀ + L y` an affine family of complex
`ι × ι` matrices, `z : Fin k → ℂ` spectral parameters and `B : Fin k → Matrix` constant slot
observables. The resolvents are `R_j(y) = res A₀ L (z j) y = (A(y) - z_j)⁻¹`, and the chain is the
slot product

`resChain A₀ L z B y = R_0 B_0 R_1 B_1 ⋯ R_{k-1} B_{k-1}` (`slotProd`).

The paper's chain `R_1 B_1 ⋯ B_{k-1} R_k` is the case `B_{k-1} = 1`; the averaged chain
`Tr[G_{[1,k]} S^{x_k}]` is the case `B_{k-1} = S^{x_k}`. Real test functions are
`chainTest A₀ L z B K y = Re tr(K · chain)` (the `reTr` convention); imaginary parts
are `reTr (-i K)` (`reTr_neg_I_smul`) and isotropic entries `Re C_ab` are `reTr (E_ba)`
(`reTr_single`).

## Results (at every `v` where all `A(v) - z_j` are invertible)

* `contDiffAt_resChain`, `contDiffAt_chainTest`: `C^n` for every `n` (in particular `C²`).
* `fderiv_resChain`, `fderiv_chainTest_eq_sum` (chain splitting):
  `D C[u] = -∑_j R_0 B_0 ⋯ (R_j (L u) R_j) B_j ⋯` (`firstVar`).
* `fderiv_fderiv_resChain`, `fderiv_fderiv_chainTest`: `D² C[u, w] = secondVar`, the sum over
  ordered pairs of slots `i ≠ j` of the double insertion (`L u` at `i`, `L w` at `j`) plus the
  diagonal terms `R_j (Lu R_j Lw + Lw R_j Lu) R_j` at a single slot.
* `sum_smul_secondVar`, `sum_smul_fderiv_fderiv_resChain`, `sum_mul_fderiv_fderiv_chainTest`:
  covariance contraction: for weights `v_c` and directions `e_c`,
  `∑_c v_c D²C[e_c, e_c] = 2 ∑_{i ≤ j} G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}` with
  `𝒮[X] = ∑_c v_c (L e_c) X (L e_c)` (`covOp`, `pairIns`).

The band operator `𝒮[X] = diag(S · diag X)` is `bandSelfEnergy`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Chains
open Matrix Filter Topology Function
open BlockBand.Native.CEH.Flow

section Algebra

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The slot list `[M₀ B₀, …, M_{k-1} B_{k-1}]`. -/
def slotList (B M : Fin k → Matrix ι ι ℂ) : List (Matrix ι ι ℂ) :=
  List.ofFn fun l => M l * B l

/-- Slot product `M₀ B₀ M₁ B₁ ⋯ M_{k-1} B_{k-1}`. -/
def slotProd (B M : Fin k → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (slotList B M).prod

/-- Partial slot product `∏_{a ≤ l < b} M_l B_l` (ordered). -/
def segProd (B M : Fin k → Matrix ι ι ℂ) (a b : ℕ) : Matrix ι ι ℂ :=
  (((slotList B M).take b).drop a).prod

/-- First variation: `∑_j M₀B₀ ⋯ (M_j X M_j) B_j ⋯ M_{k-1}B_{k-1}`. -/
def firstVar (B M : Fin k → Matrix ι ι ℂ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ j, slotProd B (update M j (M j * X * M j))

/-- Second variation: double insertions `X` at slot `i`, `Y` at slot `j` (`i ≠ j`, both orders
appear in the double sum), and the single-slot terms `M_j X M_j Y M_j + M_j Y M_j X M_j`. -/
def secondVar (B M : Fin k → Matrix ι ι ℂ) (X Y : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ j, ∑ i, if i = j then
      slotProd B (update M j (M j * X * M j * Y * M j + M j * Y * M j * X * M j))
    else slotProd B (update (update M j (M j * Y * M j)) i (M i * X * M i))

/-- Covariance operator `𝒮[X] = ∑_c v_c E_c X E_c`. -/
def covOp {κ : Type} [Fintype κ] (E : κ → Matrix ι ι ℂ) (v : κ → ℝ) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  ∑ c, v c • (E c * X * E c)

/-- The pair term `G_{[0,i]} T[G_{[i,j]}] G_{[j,k)}` with `G_{[0,i]} = (∏_{l<i} M_l B_l) M_i`,
`G_{[i,j]} = (∏_{i≤l<j} M_l B_l) M_j` and `G_{[j,k)} = M_j B_j ∏_{l>j} M_l B_l`. -/
def pairIns (B M : Fin k → Matrix ι ι ℂ) (T : Matrix ι ι ℂ → Matrix ι ι ℂ) (i j : Fin k) :
    Matrix ι ι ℂ :=
  segProd B M 0 i * M i * T (segProd B M i j * M j) * (M j * B j * segProd B M ((j : ℕ) + 1) k)

theorem ofFn_update_eq_set {α : Type} (g : Fin k → α) (j : Fin k) (a : α) :
    List.ofFn (update g j a) = (List.ofFn g).set j a := by
  simp [List.ofFn_eq_map, (List.nodup_finRange k).map_update]

omit [DecidableEq ι] in
theorem length_slotList (B M : Fin k → Matrix ι ι ℂ) : (slotList B M).length = k := by
  simp [slotList]

omit [DecidableEq ι] in
theorem slotList_update (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) (X : Matrix ι ι ℂ) :
    slotList B (update M j X) = (slotList B M).set j (X * B j) := by
  have h : (fun l => update M j X l * B l) = update (fun l => M l * B l) j (X * B j) := by
    funext l
    exact apply_update (fun l (m : Matrix ι ι ℂ) => m * B l) M j X l
  unfold slotList
  rw [h, ofFn_update_eq_set]

theorem segProd_self (B M : Fin k → Matrix ι ι ℂ) (a : ℕ) : segProd B M a a = 1 := by
  rw [segProd, List.drop_eq_nil_of_le (by simp), List.prod_nil]

/-- Splitting off the first slot of a segment. -/
theorem segProd_succ (B M : Fin k → Matrix ι ι ℂ) {i j : Fin k} (hij : i < j) :
    segProd B M i j = M i * B i * segProd B M ((i : ℕ) + 1) j := by
  have hij' : (i : ℕ) < j := hij
  have hlen : (i : ℕ) < ((slotList B M).take j).length := by simp [length_slotList, hij']
  rw [segProd, segProd, List.drop_eq_getElem_cons hlen, List.prod_cons]
  congr 1
  simp [slotList]

/-- A single slot update. -/
theorem slotProd_update (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) (X : Matrix ι ι ℂ) :
    slotProd B (update M j X) = segProd B M 0 j * (X * B j) * segProd B M ((j : ℕ) + 1) k := by
  have hlt : (j : ℕ) < (slotList B M).length := by simp [length_slotList]
  have hk : (slotList B M).take k = slotList B M :=
    List.take_of_length_le (by simp [length_slotList])
  rw [slotProd, slotList_update, List.prod_set, ite_eq_left hlt]
  simp only [segProd, List.drop_zero, hk]

theorem slotProd_update_neg (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) (X : Matrix ι ι ℂ) :
    slotProd B (update M j (-X)) = -slotProd B (update M j X) := by
  simp only [slotProd_update, neg_mul, mul_neg]

/-- Two slot updates at `i < j`. -/
theorem slotProd_update_update (B M : Fin k → Matrix ι ι ℂ) {i j : Fin k} (hij : i < j)
    (Y X : Matrix ι ι ℂ) :
    slotProd B (update (update M i Y) j X) =
      segProd B M 0 i * (Y * B i) * segProd B M ((i : ℕ) + 1) j * (X * B j) *
        segProd B M ((j : ℕ) + 1) k := by
  have hij' : (i : ℕ) < j := hij
  rw [slotProd_update]
  have hlt : (i : ℕ) < ((slotList B M).take j).length := by simp [length_slotList, hij']
  have h0 : segProd B (update M i Y) 0 j =
      segProd B M 0 i * (Y * B i) * segProd B M ((i : ℕ) + 1) j := by
    simp only [segProd, slotList_update, List.drop_zero, List.take_set]
    rw [List.prod_set, ite_eq_left hlt, List.take_take, min_eq_left hij'.le]
  have hlt' : (i : ℕ) < (j : ℕ) + 1 := by omega
  have h1 : segProd B (update M i Y) ((j : ℕ) + 1) k = segProd B M ((j : ℕ) + 1) k := by
    simp only [segProd, slotList_update, List.take_set]
    rw [List.drop_set_of_lt hlt']
  rw [h0, h1]

omit [DecidableEq ι] in
theorem sum_smul_sandwich {κ : Type} [Fintype κ] (P₁ P₂ : Matrix ι ι ℂ)
    (F : κ → Matrix ι ι ℂ) (v : κ → ℝ) :
    ∑ c, v c • (P₁ * F c * P₂) = P₁ * (∑ c, v c • F c) * P₂ := by
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem slotProd_offdiag (B M : Fin k → Matrix ι ι ℂ) {i j : Fin k} (hij : i < j)
    (E : Matrix ι ι ℂ) :
    slotProd B (update (update M i (M i * E * M i)) j (M j * E * M j)) =
      segProd B M 0 i * M i * (E * (segProd B M i j * M j) * E) *
        (M j * B j * segProd B M ((j : ℕ) + 1) k) := by
  rw [slotProd_update_update B M hij, segProd_succ B M hij]
  simp only [mul_assoc]

theorem slotProd_diag (B M : Fin k → Matrix ι ι ℂ) (j : Fin k) (E : Matrix ι ι ℂ) :
    slotProd B (update M j (M j * E * M j * E * M j + M j * E * M j * E * M j)) =
      (2 : ℝ) • (segProd B M 0 j * M j * (E * (segProd B M j j * M j) * E) *
        (M j * B j * segProd B M ((j : ℕ) + 1) k)) := by
  rw [slotProd_update, segProd_self, one_mul, ← two_smul ℝ (M j * E * M j * E * M j)]
  simp only [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]

theorem sum_offdiag {κ : Type} [Fintype κ] (B M : Fin k → Matrix ι ι ℂ) (E : κ → Matrix ι ι ℂ)
    (v : κ → ℝ) {i j : Fin k} (hij : i < j) :
    ∑ c, v c • slotProd B (update (update M i (M i * E c * M i)) j (M j * E c * M j)) =
      pairIns B M (covOp E v) i j := by
  simp only [slotProd_offdiag B M hij, pairIns, covOp]
  exact sum_smul_sandwich _ _ _ _

theorem sum_diag {κ : Type} [Fintype κ] (B M : Fin k → Matrix ι ι ℂ) (E : κ → Matrix ι ι ℂ)
    (v : κ → ℝ) (j : Fin k) :
    ∑ c, v c • slotProd B (update M j
        (M j * E c * M j * E c * M j + M j * E c * M j * E c * M j)) =
      (2 : ℝ) • pairIns B M (covOp E v) j j := by
  simp only [slotProd_diag B M j, smul_comm (v _) (2 : ℝ), ← Finset.smul_sum, pairIns, covOp]
  rw [sum_smul_sandwich]

/-- **Covariance contraction of the second variation**:
`∑_c v_c D²[E_c, E_c] = 2 ∑_{i ≤ j} G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}`, `𝒮 = covOp E v`. -/
theorem sum_smul_secondVar {κ : Type} [Fintype κ] (B M : Fin k → Matrix ι ι ℂ)
    (E : κ → Matrix ι ι ℂ) (v : κ → ℝ) :
    ∑ c, v c • secondVar B M (E c) (E c) =
      (2 : ℝ) • ∑ j, ∑ i with i ≤ j, pairIns B M (covOp E v) i j := by
  set P := pairIns B M (covOp E v)
  have key : ∀ i j : Fin k, (∑ c, v c • if i = j then
        slotProd B (update M j (M j * E c * M j * E c * M j + M j * E c * M j * E c * M j))
      else slotProd B (update (update M j (M j * E c * M j)) i (M i * E c * M i))) =
      ((if i < j then P i j else 0) + (if j < i then P j i else 0)) +
        (if i = j then (2 : ℝ) • P j j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [ite_eq_right h.ne, ite_eq_left h, ite_eq_right (not_lt.2 h.le), add_zero]
      simp_rw [update_comm h.ne']
      exact sum_offdiag B M E v h
    · simp only [ite_true, lt_irrefl, ite_false, zero_add]
      exact sum_diag B M E v i
    · simp only [ite_eq_right h.ne', ite_eq_right (not_lt.2 h.le), ite_eq_left h, zero_add, add_zero]
      exact sum_offdiag B M E v h
  have hswap : ∀ g : κ → Fin k → Fin k → Matrix ι ι ℂ,
      ∑ c, ∑ j, ∑ i, g c j i = ∑ j, ∑ i, ∑ c, g c j i := by
    intro g
    rw [Finset.sum_comm (s := (Finset.univ : Finset κ))]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have hL : ∑ c, v c • secondVar B M (E c) (E c) =
      ∑ j, ∑ i, (((if i < j then P i j else 0) + (if j < i then P j i else 0)) +
        (if i = j then (2 : ℝ) • P j j else 0)) := by
    simp only [secondVar, Finset.smul_sum]
    exact (hswap _).trans
      (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => key i j)
  have hsplit : ∀ j : Fin k,
      ∑ i with i ≤ j, P i j = ∑ i, (if i < j then P i j else 0) + P j j := by
    intro j
    rw [Finset.sum_filter]
    have h : ∀ i, (if i ≤ j then P i j else 0) =
        (if i < j then P i j else 0) + (if i = j then P i j else 0) := by
      intro i
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h, h.le, h.ne]
      · simp
      · simp [not_le.2 h, not_lt.2 h.le, h.ne']
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib]
    simp
  have hC : (∑ j : Fin k, ∑ i : Fin k, if j < i then P j i else 0) =
      ∑ j : Fin k, ∑ i : Fin k, if i < j then P i j else 0 :=
    Finset.sum_comm
  have hD : (∑ j : Fin k, ∑ i : Fin k, if i = j then (2 : ℝ) • P j j else 0) =
      (2 : ℝ) • ∑ j, P j j := by
    rw [Finset.smul_sum]
    simp
  rw [hL, Finset.sum_congr rfl fun j _ => hsplit j]
  simp only [Finset.sum_add_distrib]
  rw [hC, hD]
  simp only [smul_add, two_smul]

end Algebra

section Calculus

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The resolvent `R(y) = (A₀ + L y - z)⁻¹`. -/
def res (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : ℂ) (y : V) : Matrix ι ι ℂ :=
  (A₀ + L y - z • (1 : Matrix ι ι ℂ))⁻¹

/-- The resolvent slots `j ↦ R_j(y) = (A₀ + L y - z_j)⁻¹`. -/
def resSlots (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ) (y : V) :
    Fin k → Matrix ι ι ℂ :=
  fun j => res A₀ L (z j) y

/-- The resolvent chain `R_0(y) B_0 R_1(y) B_1 ⋯ R_{k-1}(y) B_{k-1}`. -/
def resChain (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (y : V) : Matrix ι ι ℂ :=
  slotProd B (resSlots A₀ L z y)

/-- The real test function `Re tr(K · chain)`. -/
def chainTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) (y : V) : ℝ :=
  reTr K (resChain A₀ L z B y)

omit [FiniteDimensional ℝ V] in
theorem resChain_cons (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z₀ : ℂ) (z : Fin k → ℂ)
    (B₀ : Matrix ι ι ℂ) (B : Fin k → Matrix ι ι ℂ) (y : V) :
    resChain A₀ L (Fin.cons z₀ z) (Fin.cons B₀ B) y = res A₀ L z₀ y * B₀ * resChain A₀ L z B y := by
  simp [resChain, slotProd, slotList, resSlots, List.ofFn_succ]

omit [Fintype ι] [DecidableEq ι] in
/-- `Im tr(K X) = Re tr((-i K) X)`. -/
theorem reTr_neg_I_smul [Fintype ι] (K X : Matrix ι ι ℂ) :
    reTr (-Complex.I • K) X = (trace (K * X)).im := by
  simp [reTr, Matrix.smul_mul, trace_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- Isotropic entries: `Re tr(E_{ba} X) = Re X_{ab}`. -/
theorem reTr_single [Fintype ι] [DecidableEq ι] (a b : ι) (X : Matrix ι ι ℂ) :
    reTr (Matrix.single b a 1) X = (X a b).re := by
  simp [reTr, trace_single_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem reTr_real_smul [Fintype ι] (K X : Matrix ι ι ℂ) (r : ℝ) :
    reTr K (r • X) = r * reTr K X :=
  (reTrLin K).map_smul r X

omit [FiniteDimensional ℝ V] in
theorem res_eq (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : ℂ) (y : V) :
    res A₀ L z y = ((A₀ - z • (1 : Matrix ι ι ℂ)) + L y)⁻¹ := by
  rw [res, sub_add_eq_add_sub]

/-- The invertibility set is a neighbourhood. -/
theorem eventually_isUnit (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) :
    ∀ᶠ y in 𝓝 v, ∀ j, IsUnit (A₀ + L y - z j • (1 : Matrix ι ι ℂ)).det := by
  rw [Filter.eventually_all]
  intro j
  have hmem : v ∈ {v : V | IsUnit ((A₀ - z j • (1 : Matrix ι ι ℂ)) + L v).det} := by
    show IsUnit ((A₀ - z j • (1 : Matrix ι ι ℂ)) + L v).det
    rw [sub_add_eq_add_sub]
    exact hv j
  filter_upwards [(isOpen_isUnit_det (A₀ - z j • (1 : Matrix ι ι ℂ)) L).mem_nhds hmem] with y hy
  have hy' : IsUnit ((A₀ - z j • (1 : Matrix ι ι ℂ)) + L y).det := hy
  rwa [sub_add_eq_add_sub] at hy'

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `slotProd B` as a continuous multilinear map (internal device). -/
def slotML (B : Fin k → Matrix ι ι ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Matrix ι ι ℂ) (Matrix ι ι ℂ) :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ k (Matrix ι ι ℂ)).compContinuousLinearMap
    fun j => (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).flip (B j)

theorem slotML_apply (B M : Fin k → Matrix ι ι ℂ) : slotML B M = slotProd B M :=
  rfl

omit [FiniteDimensional ℝ V] in
/-- Product rule for slot products. -/
theorem hasFDerivAt_slotProd (B : Fin k → Matrix ι ι ℂ) {M : V → Fin k → Matrix ι ι ℂ}
    {M' : Fin k → V →L[ℝ] Matrix ι ι ℂ} {v : V} (h : ∀ j, HasFDerivAt (fun y => M y j) (M' j) v) :
    ∃ D : V →L[ℝ] Matrix ι ι ℂ, HasFDerivAt (fun y => slotProd B (M y)) D v ∧
      ∀ u, D u = ∑ j, slotProd B (update (M v) j (M' j u)) := by
  have hM : HasFDerivAt (fun y j => M y j) (ContinuousLinearMap.pi M') v := hasFDerivAt_pi.2 h
  have hc := ((slotML B).hasFDerivAt (M v)).comp v hM
  have hfun : (fun y => slotProd B (M y)) = (slotML B) ∘ fun y j => M y j :=
    funext fun y => (slotML_apply B (M y)).symm
  refine ⟨((slotML B).linearDeriv (M v)).comp (ContinuousLinearMap.pi M'), ?_, fun u => ?_⟩
  · rw [hfun]
    exact hc
  · simp [slotML_apply]

omit [FiniteDimensional ℝ V] in
theorem contDiffAt_slotProd (B : Fin k → Matrix ι ι ℂ) {M : V → Fin k → Matrix ι ι ℂ} {v : V}
    {n : WithTop ℕ∞} (h : ∀ j, ContDiffAt ℝ n (fun y => M y j) v) :
    ContDiffAt ℝ n (fun y => slotProd B (M y)) v := by
  have hM : ContDiffAt ℝ n (fun y j => M y j) v := contDiffAt_pi.2 h
  have hc := (slotML B).contDiff.contDiffAt.comp v hM
  have hfun : (fun y => slotProd B (M y)) = (slotML B) ∘ fun y j => M y j :=
    funext fun y => (slotML_apply B (M y)).symm
  rw [hfun]
  exact hc

theorem hasFDerivAt_res (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : ℂ) {v : V}
    (hv : IsUnit (A₀ + L v - z • (1 : Matrix ι ι ℂ)).det) :
    ∃ D : V →L[ℝ] Matrix ι ι ℂ, HasFDerivAt (res A₀ L z) D v ∧
      ∀ u, D u = -(res A₀ L z v * L u * res A₀ L z v) := by
  have hv' : IsUnit ((A₀ - z • (1 : Matrix ι ι ℂ)) + L v).det := by rwa [sub_add_eq_add_sub]
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_inv_affine (A₀ - z • (1 : Matrix ι ι ℂ)) L hv'
  have hf : res A₀ L z = fun y => ((A₀ - z • (1 : Matrix ι ι ℂ)) + L y)⁻¹ :=
    funext (res_eq A₀ L z)
  refine ⟨D, by rw [hf]; exact hD, fun u => ?_⟩
  rw [hDu, res_eq]

theorem contDiffAt_res (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : ℂ) {v : V}
    (hv : IsUnit (A₀ + L v - z • (1 : Matrix ι ι ℂ)).det) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (res A₀ L z) v := by
  have hv' : IsUnit ((A₀ - z • (1 : Matrix ι ι ℂ)) + L v).det := by rwa [sub_add_eq_add_sub]
  have hf : res A₀ L z = fun y => ((A₀ - z • (1 : Matrix ι ι ℂ)) + L y)⁻¹ :=
    funext (res_eq A₀ L z)
  rw [hf]
  exact contDiffAt_inv_affine (A₀ - z • (1 : Matrix ι ι ℂ)) L hv'

/-- **Smoothness** of the matrix chain (`C^n` for every `n`). -/
theorem contDiffAt_resChain (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (resChain A₀ L z B) v :=
  contDiffAt_slotProd B (M := resSlots A₀ L z) fun j => contDiffAt_res A₀ L (z j) (hv j)

theorem hasFDerivAt_resChain (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) :
    ∃ D : V →L[ℝ] Matrix ι ι ℂ, HasFDerivAt (resChain A₀ L z B) D v ∧
      ∀ u, D u = -firstVar B (resSlots A₀ L z v) (L u) := by
  choose D hD hDu using fun j => hasFDerivAt_res A₀ L (z j) (hv j)
  obtain ⟨D', hD', hD'u⟩ := hasFDerivAt_slotProd B (M := resSlots A₀ L z) (M' := D) hD
  refine ⟨D', hD', fun u => ?_⟩
  rw [hD'u, firstVar, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hDu, ← slotProd_update_neg]
  rfl

/-- **First derivative (chain splitting)**: `D C(v)[u] = -∑_j ⋯ R_j (L u) R_j ⋯`. -/
theorem fderiv_resChain (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) (u : V) :
    fderiv ℝ (resChain A₀ L z B) v u = -firstVar B (resSlots A₀ L z v) (L u) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_resChain A₀ L z B hv
  rw [hD.fderiv, hDu]

/-- Derivative of the first partial `y ↦ -firstVar(R(y))[L w]`. -/
theorem hasFDerivAt_negFirstVar (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (w : V) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) :
    ∃ D : V →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt (fun y => -firstVar B (resSlots A₀ L z y) (L w)) D v ∧
      ∀ u, D u = secondVar B (resSlots A₀ L z v) (L u) (L w) := by
  choose D hD hDu using fun j => hasFDerivAt_res A₀ L (z j) (hv j)
  have hP : ∀ j, ∃ P : V →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt (fun y => res A₀ L (z j) y * L w * res A₀ L (z j) y) P v ∧
      ∀ u, P u = res A₀ L (z j) v * L w * D j u + D j u * L w * res A₀ L (z j) v :=
    fun j => ⟨_, ((hD j).mul_const' (L w)).mul' (hD j), fun u => rfl⟩
  choose P hP hPu using hP
  have hcomp : ∀ j i, HasFDerivAt
      (fun y => update (resSlots A₀ L z y) j (res A₀ L (z j) y * L w * res A₀ L (z j) y) i)
      (update D j (P j) i) v := by
    intro j i
    by_cases h : i = j
    · subst h
      simp only [update_self]
      exact hP i
    · simp only [update_of_ne h]
      exact hD i
  choose S hS hSu using fun j => hasFDerivAt_slotProd B (hcomp j)
  refine ⟨-(∑ j, S j), (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => hS j).fun_neg, fun u => ?_⟩
  rw [_root_.neg_apply, _root_.sum_apply, secondVar,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hSu, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, update_self, update_idem, hPu, hDu, ← slotProd_update_neg]
    congr 2
    simp only [resSlots, mul_neg, neg_mul, neg_neg, neg_add, mul_assoc]
    abel
  · rw [ite_eq_right h, update_of_ne h, hDu, slotProd_update_neg, neg_neg]
    rfl

omit [FiniteDimensional ℝ V] in
/-- Second derivative from an eventual formula for the first partial. -/
theorem fderiv_fderiv_apply_of_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F H : V → E} {D : V →L[ℝ] E} {v w : V} (hF : ContDiffAt ℝ 2 F v)
    (hev : (fun y => fderiv ℝ F y w) =ᶠ[𝓝 v] H) (hH : HasFDerivAt H D v) (u : V) :
    fderiv ℝ (fderiv ℝ F) v u w = D u := by
  have h2 := hH.congr_of_eventuallyEq hev
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) v :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp v hdiff.hasFDerivAt
  rw [← h1.unique h2]
  rfl

/-- **Second derivative** of the matrix chain: the double/diagonal insertions `secondVar`. -/
theorem fderiv_fderiv_resChain (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) (u w : V) :
    fderiv ℝ (fderiv ℝ (resChain A₀ L z B)) v u w =
      secondVar B (resSlots A₀ L z v) (L u) (L w) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_negFirstVar A₀ L z B w hv
  rw [← hDu u]
  refine fderiv_fderiv_apply_of_eventuallyEq (contDiffAt_resChain A₀ L z B hv) ?_ hD u
  filter_upwards [eventually_isUnit A₀ L z hv] with y hy
  exact fderiv_resChain A₀ L z B hy w

/-- **Covariance contraction** at the derivative level: for weights `c ↦ v_c` and directions
`c ↦ e_c`, `∑_c v_c D²C[e_c, e_c] = 2 ∑_{i ≤ j} G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)}` with
`𝒮[X] = ∑_c v_c (L e_c) X (L e_c)`. -/
theorem sum_smul_fderiv_fderiv_resChain (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℂ) (B : Fin k → Matrix ι ι ℂ) {y : V}
    (hy : ∀ j, IsUnit (A₀ + L y - z j • (1 : Matrix ι ι ℂ)).det)
    {κ : Type} [Fintype κ] (v : κ → ℝ) (e : κ → V) :
    ∑ c, v c • fderiv ℝ (fderiv ℝ (resChain A₀ L z B)) y (e c) (e c) =
      (2 : ℝ) • ∑ j, ∑ i with i ≤ j,
        pairIns B (resSlots A₀ L z y) (covOp (fun c => L (e c)) v) i j := by
  simp only [fderiv_fderiv_resChain A₀ L z B hy]
  exact sum_smul_secondVar _ _ _ _

/-!
### Scalar test functions `Re tr(K · chain)`
-/

/-- **Smoothness** of `Re tr(K · chain)` (`C^n` for every `n`). -/
theorem contDiffAt_chainTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (chainTest A₀ L z B K) v :=
  ((reTrLin K).toContinuousLinearMap.contDiff.contDiffAt).comp v
    (contDiffAt_resChain A₀ L z B hv)

theorem fderiv_chainTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) (u : V) :
    fderiv ℝ (chainTest A₀ L z B K) v u = -reTr K (firstVar B (resSlots A₀ L z v) (L u)) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_resChain A₀ L z B hv
  set T := (reTrLin K).toContinuousLinearMap
  have h := T.hasFDerivAt.comp v hD
  rw [show chainTest A₀ L z B K = T ∘ resChain A₀ L z B from rfl, h.fderiv]
  change reTr K (D u) = _
  rw [hDu, reTr_neg]

/-- **First derivative (chain splitting)** of `Re tr(K · chain)`:
`D f(v)[u] = -∑_j Re tr(K R_0 B_0 ⋯ R_j (L u) R_j B_j ⋯)`. -/
theorem fderiv_chainTest_eq_sum (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) (u : V) :
    fderiv ℝ (chainTest A₀ L z B K) v u =
      -∑ j, reTr K (slotProd B (update (resSlots A₀ L z v) j
        (resSlots A₀ L z v j * L u * resSlots A₀ L z v j))) := by
  rw [fderiv_chainTest A₀ L z B K hv, firstVar, reTr_sum]

/-- **Second derivative** of `Re tr(K · chain)`: `Re tr(K · secondVar)`. -/
theorem fderiv_fderiv_chainTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (z : Fin k → ℂ)
    (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {v : V}
    (hv : ∀ j, IsUnit (A₀ + L v - z j • (1 : Matrix ι ι ℂ)).det) (u w : V) :
    fderiv ℝ (fderiv ℝ (chainTest A₀ L z B K)) v u w =
      reTr K (secondVar B (resSlots A₀ L z v) (L u) (L w)) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_negFirstVar A₀ L z B w hv
  set T := (reTrLin K).toContinuousLinearMap
  have hH : HasFDerivAt (fun y => -reTr K (firstVar B (resSlots A₀ L z y) (L w))) (T.comp D) v := by
    have h := T.hasFDerivAt.comp v hD
    have hfun : (fun y => -reTr K (firstVar B (resSlots A₀ L z y) (L w))) =
        T ∘ fun y => -firstVar B (resSlots A₀ L z y) (L w) := by
      funext y
      change _ = reTr K (-_)
      rw [reTr_neg]
    rw [hfun]
    exact h
  have h := fderiv_fderiv_apply_of_eventuallyEq (w := w) (contDiffAt_chainTest A₀ L z B K hv) ?_ hH u
  · rw [h]
    change reTr K (D u) = _
    rw [hDu]
  · filter_upwards [eventually_isUnit A₀ L z hv] with y hy
    exact fderiv_chainTest A₀ L z B K hy w

/-- **Covariance contraction** for `f = Re tr(K · chain)`:
`∑_c v_c D²f(y)[e_c, e_c] = 2 ∑_{i ≤ j} Re tr(K G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)})`. -/
theorem sum_mul_fderiv_fderiv_chainTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (z : Fin k → ℂ) (B : Fin k → Matrix ι ι ℂ) (K : Matrix ι ι ℂ) {y : V}
    (hy : ∀ j, IsUnit (A₀ + L y - z j • (1 : Matrix ι ι ℂ)).det)
    {κ : Type} [Fintype κ] (v : κ → ℝ) (e : κ → V) :
    ∑ c, v c * fderiv ℝ (fderiv ℝ (chainTest A₀ L z B K)) y (e c) (e c) =
      2 * ∑ j, ∑ i with i ≤ j,
        reTr K (pairIns B (resSlots A₀ L z y) (covOp (fun c => L (e c)) v) i j) := by
  have h := congrArg (reTr K) (sum_smul_secondVar B (resSlots A₀ L z y) (fun c => L (e c)) v)
  simp only [reTr_sum, reTr_real_smul] at h
  simp only [fderiv_fderiv_chainTest A₀ L z B K hy]
  exact h

end Calculus

end BlockBand.Native.ErdosRiabov.Chains
