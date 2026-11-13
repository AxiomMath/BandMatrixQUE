module

public import BlockBand.External.CEH.SourceStatement
public import BlockBand.Native.CEH.Deterministic.EigenpairsGramSchmidt
public import BlockBand.Native.CEH.Deterministic.EigenpairsProjector

/-!
# A measurable increasing orthonormal eigenpair selection

This file proves, with no hypotheses, `eigenpairs_exist : ∀ N, 0 < N → Nonempty
(EigenpairSelection N)`: for every `N` there are maps `H ↦ λ_i(H) ∈ ℝ`, `H ↦ v_i(H) ∈ ℂ^N`,
Borel measurable on `SourceHermitian N` (subtype of the entrywise Borel matrices), with `λ(H)`
monotone, `v(H)` orthonormal (`star v_i ⬝ᵥ v_j = δ_ij`) and `H v_i = λ_i v_i`, for **every**
Hermitian `H` (repeated eigenvalues included; choices inside an eigenspace are arbitrary). The
eigenvectors are obtained by Gram–Schmidt on the columns of the cluster spectral projectors.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH

open Matrix
open BlockBand.External.CEH

namespace Eigenpairs

variable {N : ℕ}

/-- The `μ`-eigenspace of `H` as a submodule. -/
def eigenSubmodule (H : SourceHermitian N) (μ : ℝ) : Submodule ℂ (Fin N → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin H.1 - (μ : ℂ) • LinearMap.id)

theorem mem_eigenSubmodule (H : SourceHermitian N) (μ : ℝ) (v : Fin N → ℂ) :
    v ∈ eigenSubmodule H μ ↔ H.1 *ᵥ v = (μ : ℂ) • v := by
  simp [eigenSubmodule, sub_eq_zero]

/-- Columns `P_μ e_k` of the cluster projector (zero for `k ≥ N`). -/
def clusterColumns (H : SourceHermitian N) (μ : ℝ) (k : ℕ) : Fin N → ℂ :=
  if h : k < N then fun y => clusterProjector H μ y ⟨k, h⟩ else 0

/-- Gram–Schmidt outputs on the cluster columns. -/
def clusterGS (H : SourceHermitian N) (μ : ℝ) (k : ℕ) : Fin N → ℂ :=
  gramSchmidt (clusterColumns H μ) k

open Classical in
/-- Rank of `i` inside its eigenvalue cluster: `#{j < i | λ_j = λ_i}`. -/
def clusterRank (H : SourceHermitian N) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j : Fin N => j < i ∧ eigval H j = eigval H i).card

open Classical in
/-- The selected eigenvector: the `clusterRank`-th nonzero Gram–Schmidt output. -/
def selectedVector (H : SourceHermitian N) (i : Fin N) : Fin N → ℂ :=
  ∑ k ∈ Finset.range N,
    if clusterGS H (eigval H i) k ≠ 0 ∧
        countBelow (fun l => clusterGS H (eigval H i) l ≠ 0) k = clusterRank H i then
      clusterGS H (eigval H i) k else 0

/-!
### Linear algebra
-/

theorem clusterColumns_mem (H : SourceHermitian N) (μ : ℝ) (k : ℕ) :
    clusterColumns H μ k ∈ eigenSubmodule H μ := by
  rw [mem_eigenSubmodule]
  by_cases hk : k < N
  · have hm := mul_clusterProjector H μ
    funext y
    have hy := congrFun (congrFun hm y) ⟨k, hk⟩
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at hy
    simp only [clusterColumns, hk, dite_true, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact hy
  · simp [clusterColumns, hk]

theorem clusterGS_mem (H : SourceHermitian N) (μ : ℝ) (k : ℕ) :
    clusterGS H μ k ∈ eigenSubmodule H μ :=
  gramSchmidt_mem _ _ (clusterColumns_mem H μ) k

theorem clusterProjector_mulVec_eq_sum (H : SourceHermitian N) (μ : ℝ) (v : Fin N → ℂ) :
    clusterProjector H μ *ᵥ v = ∑ x : Fin N, v x • clusterColumns H μ x.val := by
  funext y
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, clusterColumns,
    Fin.eta]
  exact Finset.sum_congr rfl fun x _ => by rw [dite_eq_left x.isLt, mul_comm]

/-- Orthonormal families are linearly independent; dimension count against a spanning family. -/
theorem card_le_of_orthonormal_mem_span {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ]
    (f : κ → Fin N → ℂ) (g : σ → Fin N → ℂ)
    (hf : ∀ a b, star (f a) ⬝ᵥ f b = if a = b then 1 else 0)
    (hmem : ∀ a, f a ∈ Submodule.span ℂ (Set.range g)) :
    Fintype.card κ ≤ Fintype.card σ := by
  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have h := congrArg (fun w => star (f i) ⬝ᵥ w) hs
    simp only [dotProduct_sum, dotProduct_smul, hf, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, hi, ite_true, dotProduct_zero] at h
    exact h
  rw [← finrank_span_eq_card hli]
  exact (Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem))).trans
    (finrank_range_le_card g)

/-- Distinct eigenvalues of a Hermitian matrix have orthogonal eigenvectors. -/
theorem star_dotProduct_eq_zero_of_eigen (H : SourceHermitian N) {a b : ℝ} (hab : a ≠ b)
    {v w : Fin N → ℂ} (hv : H.1 *ᵥ v = (a : ℂ) • v) (hw : H.1 *ᵥ w = (b : ℂ) • w) :
    star v ⬝ᵥ w = 0 := by
  have h1 : star v ⬝ᵥ (H.1 *ᵥ w) = (b : ℂ) * (star v ⬝ᵥ w) := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  have h2 : star v ⬝ᵥ (H.1 *ᵥ w) = (a : ℂ) * (star v ⬝ᵥ w) := by
    rw [dotProduct_mulVec, ← H.2.eq, ← star_mulVec, hv, star_smul, smul_dotProduct,
      Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  have h3 : ((a : ℂ) - (b : ℂ)) * (star v ⬝ᵥ w) = 0 := by
    rw [sub_mul, ← h1, ← h2, sub_self]
  have hne : (a : ℂ) - (b : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hab)
  exact (mul_eq_zero.mp h3).resolve_left hne

/-- At least `#{j | λ_j = μ}` Gram–Schmidt outputs on the cluster columns are nonzero. -/
theorem card_cluster_le_countBelow (H : SourceHermitian N) (μ : ℝ) :
    Fintype.card {j : Fin N // eigval H j = μ} ≤
      countBelow (fun l => clusterGS H μ l ≠ 0) N := by
  let S := belowSet (fun l => clusterGS H μ l ≠ 0) N
  have hS : countBelow (fun l => clusterGS H μ l ≠ 0) N = Fintype.card S := by
    rw [Fintype.card_coe]
    rfl
  rw [hS]
  apply card_le_of_orthonormal_mem_span (fun j => eigbasis H j.1) (fun s : S => clusterGS H μ s.1)
  · intro a b
    rw [eigbasis_orthonormal]
    simp only [Subtype.ext_iff]
  · intro a
    have hw : ∀ l < N, clusterGS H μ l ∈
        Submodule.span ℂ (Set.range (fun s : S => clusterGS H μ s.1)) := by
      intro l hl
      by_cases h0 : clusterGS H μ l = 0
      · rw [h0]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span
          ⟨⟨l, (mem_belowSet _ _ _).mpr ⟨hl, h0⟩⟩, rfl⟩
    have hP := clusterProjector_mulVec H μ a.1
    rw [ite_eq_left a.2, one_smul, clusterProjector_mulVec_eq_sum] at hP
    rw [← hP]
    refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
    exact input_mem _ _ _ fun l hl => hw l (lt_of_le_of_lt hl x.isLt)

theorem clusterRank_lt_card (H : SourceHermitian N) (i : Fin N) :
    clusterRank H i < Fintype.card {j : Fin N // eigval H j = eigval H i} := by
  classical
  rw [Fintype.card_subtype, clusterRank]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp, by simp⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.2

theorem clusterRank_ne (H : SourceHermitian N) {i j : Fin N} (hij : i ≠ j)
    (h : eigval H i = eigval H j) : clusterRank H i ≠ clusterRank H j := by
  classical
  have key : ∀ a b : Fin N, a < b → eigval H a = eigval H b →
      clusterRank H a < clusterRank H b := by
    intro a b hab hev
    rw [clusterRank, clusterRank]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, by simp [hab, hev], by simp⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact ⟨hc.1.trans hab, hc.2.trans hev⟩
  rcases lt_or_gt_of_ne hij with hl | hl
  · exact (key i j hl h).ne
  · exact (key j i hl h.symm).ne'

theorem selectedVector_spec (H : SourceHermitian N) (i : Fin N) :
    ∃ k < N, clusterGS H (eigval H i) k ≠ 0 ∧
      countBelow (fun l => clusterGS H (eigval H i) l ≠ 0) k = clusterRank H i ∧
      selectedVector H i = clusterGS H (eigval H i) k := by
  obtain ⟨k, hk, hpk, hck⟩ := exists_countBelow_eq (fun l => clusterGS H (eigval H i) l ≠ 0) N
    (clusterRank H i) ((clusterRank_lt_card H i).trans_le (card_cluster_le_countBelow H _))
  refine ⟨k, hk, hpk, hck, ?_⟩
  rw [selectedVector, Finset.sum_eq_single k]
  · rw [ite_eq_left ⟨hpk, hck⟩]
  · intro k' _ hk'
    rw [ite_eq_right]
    rintro ⟨hp', hc'⟩
    rcases lt_or_gt_of_ne hk' with hlt | hlt
    · have := countBelow_lt_of_lt (fun l => clusterGS H (eigval H i) l ≠ 0) hp' hlt
      omega
    · have := countBelow_lt_of_lt (fun l => clusterGS H (eigval H i) l ≠ 0) hpk hlt
      omega
  · intro hk'
    exact absurd (Finset.mem_range.mpr hk) hk'

/-!
### Measurability
-/

theorem measurable_clusterGS (f : SourceHermitian N → ℝ) (hf : Measurable f) (k : ℕ) :
    Measurable (fun H => clusterGS H (f H) k) := by
  apply measurable_gramSchmidt (fun H => clusterColumns H (f H))
  intro k
  by_cases hk : k < N
  · simp only [clusterColumns, hk, dite_true]
    exact measurable_pi_iff.mpr fun y =>
      (measurable_pi_apply _).comp ((measurable_pi_apply y).comp (measurable_clusterProjector f hf))
  · simp only [clusterColumns, hk, dite_false]
    exact measurable_const

theorem measurable_countBelow_clusterGS (f : SourceHermitian N → ℝ) (hf : Measurable f) (k : ℕ) :
    Measurable (fun H => countBelow (fun l => clusterGS H (f H) l ≠ 0) k) := by
  classical
  simp only [countBelow_eq_sum]
  refine Finset.measurable_sum _ fun l _ => Measurable.ite ?_ measurable_const measurable_const
  exact ((measurable_clusterGS f hf l) (measurableSet_singleton 0)).compl

theorem measurable_clusterRank (i : Fin N) :
    Measurable (fun H : SourceHermitian N => clusterRank H i) := by
  classical
  simp only [clusterRank, Finset.card_filter]
  refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const (j < i)).inter
    (measurableSet_eq_fun (measurable_eigval j) (measurable_eigval i))

theorem measurable_selectedVector (i : Fin N) :
    Measurable (fun H : SourceHermitian N => selectedVector H i) := by
  classical
  simp only [selectedVector]
  refine measurable_pi_iff.mpr fun y => ?_
  simp only [Finset.sum_apply]
  refine Finset.measurable_sum _ fun k _ => ?_
  have hset : MeasurableSet {H : SourceHermitian N | clusterGS H (eigval H i) k ≠ 0 ∧
      countBelow (fun l => clusterGS H (eigval H i) l ≠ 0) k = clusterRank H i} :=
    (((measurable_clusterGS _ (measurable_eigval i) k) (measurableSet_singleton 0)).compl).inter
      (measurableSet_eq_fun (measurable_countBelow_clusterGS _ (measurable_eigval i) k)
        (measurable_clusterRank i))
  exact (measurable_pi_apply y).comp
    (Measurable.ite hset (measurable_clusterGS _ (measurable_eigval i) k) measurable_const)

/-!
### The selection
-/

/-- The measurable increasing orthonormal eigenpair selection, for every `N`. -/
def eigenpairSelection (N : ℕ) : EigenpairSelection N where
  eigenvalue := eigval
  eigenvector := selectedVector
  measurable_eigenvalue := measurable_eigval
  measurable_eigenvector i a := (measurable_pi_apply a).comp (measurable_selectedVector i)
  increasing := eigval_monotone
  orthonormal H i j := by
    obtain ⟨ki, -, hpi, hci, hsi⟩ := selectedVector_spec H i
    obtain ⟨kj, -, hpj, hcj, hsj⟩ := selectedVector_spec H j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hsi]
      exact star_gramSchmidt_self _ _ hpi
    rw [ite_eq_right hij, hsi, hsj]
    by_cases hev : eigval H i = eigval H j
    · rw [← hev] at hcj ⊢
      apply star_gramSchmidt_dot_of_ne
      rintro rfl
      exact clusterRank_ne H hij hev (hci.symm.trans hcj)
    · exact star_dotProduct_eq_zero_of_eigen H hev
        ((mem_eigenSubmodule _ _ _).mp (clusterGS_mem H _ ki))
        ((mem_eigenSubmodule _ _ _).mp (clusterGS_mem H _ kj))
  eigen_equation H i := by
    obtain ⟨k, -, -, -, hs⟩ := selectedVector_spec H i
    rw [hs]
    exact (mem_eigenSubmodule _ _ _).mp (clusterGS_mem H _ k)

end Eigenpairs

/-- **Existence of an eigenpair selection** (`eigenpairs_exist`): a Borel
measurable, increasing, orthonormal eigenpair selection exists for every Hermitian `N × N` matrix,
repeated eigenvalues included. No hypotheses. -/
theorem eigenpairs_exist : ∀ (N : ℕ), 0 < N → Nonempty (EigenpairSelection N) :=
  fun N _ => ⟨Eigenpairs.eigenpairSelection N⟩

end BlockBand.Native.CEH
