module

public import BlockBand.Endpoints.Response.FractionalTrace
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Pinching and subadditivity of the fractional trace

* `rh_fracTrace_le_sum_diag` — Schur concavity of the diagonal: for PSD `M`, every unitary `V`
  and `0 ≤ p ≤ 1`, `Tr M^p ≤ Σ_j ((V* M V)_{jj})^p` (Jensen for the concave `x ↦ x^p` with the
  doubly stochastic weights `|(U*V)_{ij}|²`).
* `rh_fracTrace_fromBlocks_le` — **pinching**:
  `Tr M^p ≤ Tr M₁₁^p + Tr M₂₂^p` for a PSD block matrix, `0 ≤ p ≤ 1`.
* `rh_fracTrace_le_portBlocks` — the same for the two-port index `Fin 2 × Fin W`:
  `Tr Q^p ≤ Tr Q_near^p + Tr Q_far^p` (near block `portBlock Q 0 0`, far block
  `portBlock Q 1 1`).
* `rh_fracTrace_add_le` — **subadditivity**:
  `Tr (A+B)^p ≤ Tr A^p + Tr B^p` for PSD `A, B`, `0 < p ≤ 1`. Proof: `A = CᴴC`, `B = DᴴD`; with
  `X = [[C, 0], [D, 0]]`, `XᴴX = diag(A + B, 0)` and `XXᴴ = [[CCᴴ, CDᴴ], [DCᴴ, DDᴴ]]` have the
  same fractional trace, and pinching bounds the latter by `Tr (CCᴴ)^p + Tr (DDᴴ)^p`.
  (This replaces the integral-representation proof of the paper.)
* `rh_fracTrace_sum_le` — the finite-sum form.
* `rh_continuous_fracTrace`, `rh_measurable_fracTrace` — `A ↦ Tr A^p` is continuous on Hermitian
  matrices (`0 < p`), so `ω ↦ Tr M(ω)^p` is measurable for a measurable Hermitian-valued `M`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath

/-!
## Schur concavity of the diagonal
-/

section Schur

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For PSD `M`, any unitary `V` and `0 ≤ p ≤ 1`: `Tr M^p ≤ Σ_j (Re (V* M V)_{jj})^p`. -/
theorem rh_fracTrace_le_sum_diag {M : Matrix ι ι ℂ} (hM : M.PosSemidef) {V : Matrix ι ι ℂ}
    (hV : V ∈ unitaryGroup ι ℂ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fracTrace p M ≤ ∑ j, ((star V * M * V) j j).re ^ p := by
  set hH := hM.isHermitian
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  set lam := hH.eigenvalues
  have hspec : M = U * diagonal (fun i => (lam i : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hU : U ∈ unitaryGroup ι ℂ := hH.eigenvectorUnitary.2
  set S : Matrix ι ι ℂ := star U * V
  have hS : S ∈ unitaryGroup ι ℂ := mul_mem (Unitary.star_mem hU) hV
  have hSS : star S * S = 1 := mem_unitaryGroup_iff'.mp hS
  have hSS' : S * star S = 1 := mem_unitaryGroup_iff.mp hS
  set w : ι → ι → ℝ := fun i j => ‖S i j‖ ^ 2
  have hw0 : ∀ i j, 0 ≤ w i j := fun i j => sq_nonneg _
  have hcol : ∀ j, ∑ i, w i j = 1 := by
    intro j
    have h := congrArg (fun A : Matrix ι ι ℂ => (A j j).re) hSS
    simp only [mul_apply, star_apply, one_apply_eq, Complex.one_re] at h
    rw [← h, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, RCLike.star_def]
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hrow : ∀ i, ∑ j, w i j = 1 := by
    intro i
    have h := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) hSS'
    simp only [mul_apply, star_apply, one_apply_eq, Complex.one_re] at h
    rw [← h, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w, RCLike.star_def]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hdiag : ∀ j, ((star V * M * V) j j).re = ∑ i, w i j * lam i := by
    intro j
    have hVM : star V * M * V = star S * diagonal (fun i => (lam i : ℂ)) * S := by
      rw [hspec]
      simp only [S, star_mul, star_star, Matrix.mul_assoc]
    rw [hVM, mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_diagonal, star_apply, RCLike.star_def]
    have : (starRingEnd ℂ) (S i j) * (lam i : ℂ) * S i j =
        (lam i : ℂ) * (S i j * (starRingEnd ℂ) (S i j)) := by ring
    rw [this, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [w]
    push_cast
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hlam0 : ∀ i, 0 ≤ lam i := hM.eigenvalues_nonneg
  have hJ : ∀ j, ∑ i, w i j * lam i ^ p ≤ (∑ i, w i j * lam i) ^ p := by
    intro j
    have := (Real.concaveOn_rpow hp0 hp1).le_map_sum (t := Finset.univ) (w := fun i => w i j)
      (p := lam) (fun i _ => hw0 i j) (hcol j) (fun i _ => Set.mem_Ici.mpr (hlam0 i))
    simpa [smul_eq_mul] using this
  rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hM]
  calc ∑ i, lam i ^ p = ∑ i, ∑ j, w i j * lam i ^ p := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hrow i, one_mul]
    _ = ∑ j, ∑ i, w i j * lam i ^ p := Finset.sum_comm
    _ ≤ ∑ j, (∑ i, w i j * lam i) ^ p := Finset.sum_le_sum fun j _ => hJ j
    _ = ∑ j, ((star V * M * V) j j).re ^ p := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hdiag j]

end Schur

/-!
## Pinching
-/

section Pinching

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem rh_posSemidef_toBlocks11 {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosSemidef) :
    M.toBlocks₁₁.PosSemidef := by
  have : M.toBlocks₁₁ = M.submatrix Sum.inl Sum.inl := by ext; rfl
  rw [this]; exact hM.submatrix _

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
theorem rh_posSemidef_toBlocks22 {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosSemidef) :
    M.toBlocks₂₂.PosSemidef := by
  have : M.toBlocks₂₂ = M.submatrix Sum.inr Sum.inr := by ext; rfl
  rw [this]; exact hM.submatrix _

/-- The diagonal of `U* A U` for the eigenvector unitary of a Hermitian `A`. -/
theorem rh_star_eigenvectorUnitary_mul_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix n n ℂ) * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
  have := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at this
  exact this

/-- **Pinching**: for a PSD block matrix and `0 ≤ p ≤ 1`, `Tr M^p ≤ Tr M₁₁^p + Tr M₂₂^p`. -/
theorem rh_fracTrace_fromBlocks_le {M : Matrix (n ⊕ m) (n ⊕ m) ℂ} (hM : M.PosSemidef) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fracTrace p M ≤ fracTrace p M.toBlocks₁₁ + fracTrace p M.toBlocks₂₂ := by
  have hA := rh_posSemidef_toBlocks11 hM
  have hD := rh_posSemidef_toBlocks22 hM
  set UA : Matrix n n ℂ := (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)
  set UD : Matrix m m ℂ := (hD.isHermitian.eigenvectorUnitary : Matrix m m ℂ)
  have hUA : UA ∈ unitaryGroup n ℂ := hA.isHermitian.eigenvectorUnitary.2
  have hUD : UD ∈ unitaryGroup m ℂ := hD.isHermitian.eigenvectorUnitary.2
  set V : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks UA 0 0 UD
  have hstarV : star V = fromBlocks (star UA) 0 0 (star UD) := by
    simp only [V, star_eq_conjTranspose, fromBlocks_conjTranspose, conjTranspose_zero]
  have hV : V ∈ unitaryGroup (n ⊕ m) ℂ := by
    rw [mem_unitaryGroup_iff', hstarV]
    simp only [V, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      mem_unitaryGroup_iff'.mp hUA, mem_unitaryGroup_iff'.mp hUD, fromBlocks_one]
  have hconj : star V * M * V = fromBlocks (star UA * M.toBlocks₁₁ * UA)
      (star UA * M.toBlocks₁₂ * UD) (star UD * M.toBlocks₂₁ * UA)
      (star UD * M.toBlocks₂₂ * UD) := by
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [hstarV]
    simp only [V, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have h1 := rh_star_eigenvectorUnitary_mul_mul hA.isHermitian
  have h2 := rh_star_eigenvectorUnitary_mul_mul hD.isHermitian
  refine (rh_fracTrace_le_sum_diag hM hV hp0 hp1).trans (le_of_eq ?_)
  rw [Fintype.sum_sum_type, hconj, fracTrace_eq_sum_eigenvalues_of_posSemidef hA,
    fracTrace_eq_sum_eigenvalues_of_posSemidef hD]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [fromBlocks_apply₁₁, h1, diagonal_apply_eq, Complex.ofReal_re]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [fromBlocks_apply₂₂, h2, diagonal_apply_eq, Complex.ofReal_re]

/-- `Tr (diag(P, 0))^p = Tr P^p` for `0 < p`. -/
theorem rh_fracTrace_fromBlocks_zero {P : Matrix n n ℂ} {p : ℝ} (hp : 0 < p) :
    fracTrace p (fromBlocks P 0 0 (0 : Matrix m m ℂ)) = fracTrace p P := by
  unfold fracTrace
  rw [charpoly_fromBlocks_zero₁₂, Polynomial.roots_mul
    (mul_ne_zero P.charpoly_monic.ne_zero (charpoly_monic _).ne_zero), charpoly_zero,
    Polynomial.roots_X_pow, Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul,
    Multiset.sum_nsmul]
  simp [Real.zero_rpow hp.ne']

end Pinching

/-!
## Subadditivity
-/

section Subadditivity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A PSD matrix is a Gram matrix `CᴴC`. -/
theorem rh_exists_eq_conjTranspose_mul_self {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    ∃ C : Matrix n n ℂ, A = Cᴴ * C := by
  set hH := hA.isHermitian
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  refine ⟨diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)) * star U, ?_⟩
  have hspec : A = U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  rw [conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose, star_star]
  have hd : star (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)) =
      fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ) := by
    funext i; simp [Pi.star_apply]
  rw [hd, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
    ← Matrix.mul_assoc]
  convert hspec using 4
  funext i
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]

/-- **Subadditivity** `Tr (A+B)^p ≤ Tr A^p + Tr B^p` for PSD `A, B` and `0 < p ≤ 1`. -/
theorem rh_fracTrace_add_le {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) : fracTrace p (A + B) ≤ fracTrace p A + fracTrace p B := by
  obtain ⟨C, rfl⟩ := rh_exists_eq_conjTranspose_mul_self hA
  obtain ⟨D, rfl⟩ := rh_exists_eq_conjTranspose_mul_self hB
  set X : Matrix (n ⊕ n) (n ⊕ n) ℂ := fromBlocks C 0 D 0
  have hXX : Xᴴ * X = fromBlocks (Cᴴ * C + Dᴴ * D) 0 0 (0 : Matrix n n ℂ) := by
    simp only [X, fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hXX' : X * Xᴴ = fromBlocks (C * Cᴴ) (C * Dᴴ) (D * Cᴴ) (D * Dᴴ) := by
    simp only [X, fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
      Matrix.mul_zero, add_zero]
  have hpsd : (X * Xᴴ).PosSemidef := posSemidef_self_mul_conjTranspose X
  have key := rh_fracTrace_fromBlocks_le hpsd hp0.le hp1
  rw [hXX', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂, ← hXX', ← fracTrace_mul_comm,
    hXX, rh_fracTrace_fromBlocks_zero hp0] at key
  rwa [fracTrace_mul_comm p C Cᴴ, fracTrace_mul_comm p D Dᴴ] at key

/-- Finite-sum subadditivity. -/
theorem rh_fracTrace_sum_le {κ : Type*} (s : Finset κ) (A : κ → Matrix n n ℂ)
    (hA : ∀ k ∈ s, (A k).PosSemidef) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    fracTrace p (∑ k ∈ s, A k) ≤ ∑ k ∈ s, fracTrace p (A k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold fracTrace
    rw [charpoly_zero, Polynomial.roots_X_pow, Multiset.map_nsmul, Multiset.sum_nsmul,
      Multiset.map_singleton, Multiset.sum_singleton]
    simp [Real.zero_rpow hp0.ne']
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have hs : (∑ j ∈ s, A j).PosSemidef :=
      posSemidef_sum _ fun j hj => hA j (Finset.mem_insert_of_mem hj)
    refine (rh_fracTrace_add_le (hA k (Finset.mem_insert_self k s)) hs hp0 hp1).trans ?_
    gcongr
    exact ih fun j hj => hA j (Finset.mem_insert_of_mem hj)

end Subadditivity

/-!
## The two-port index
-/

/-- `Fin 2 × Fin W ≃ Fin W ⊕ Fin W` (port `0` ↦ left, port `1` ↦ right). -/
def rhPortSum (W : ℕ) : Fin 2 × Fin W ≃ Fin W ⊕ Fin W where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun := Sum.elim (fun y => ((0 : Fin 2), y)) (fun y => ((1 : Fin 2), y))
  left_inv x := by
    rcases x with ⟨i, y⟩
    fin_cases i <;> rfl
  right_inv y := by rcases y with y | y <;> rfl

theorem rh_toBlocks11_reindex {W : ℕ} (Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (reindex (rhPortSum W) (rhPortSum W) Q).toBlocks₁₁ = portBlock Q 0 0 := by
  ext x y; rfl

theorem rh_toBlocks22_reindex {W : ℕ} (Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (reindex (rhPortSum W) (rhPortSum W) Q).toBlocks₂₂ = portBlock Q 1 1 := by
  ext x y; rfl

/-- **Near/far pinching** of a positive two-port matrix: `Tr Q^p ≤ Tr Q_near^p + Tr Q_far^p`. -/
theorem rh_fracTrace_le_portBlocks {W : ℕ} {Q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hQ : Q.PosSemidef) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fracTrace p Q ≤ fracTrace p (portBlock Q 0 0) + fracTrace p (portBlock Q 1 1) := by
  have h := rh_fracTrace_fromBlocks_le (M := reindex (rhPortSum W) (rhPortSum W) Q)
    (by simpa [reindex_apply] using hQ.submatrix (rhPortSum W).symm) hp0 hp1
  rwa [fracTrace_reindex, rh_toBlocks11_reindex, rh_toBlocks22_reindex] at h

/-!
## Continuity and measurability
-/

section Measurability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A ↦ Tr A^p` is continuous on Hermitian matrices for `0 < p`. -/
theorem rh_continuous_fracTrace {p : ℝ} (hp : 0 < p) :
    Continuous (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} => fracTrace p A.1) := by
  have hfun : (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} => fracTrace p A.1) =
      fun A => ∑ k, (max (A.2.eigenvalues₀ k) 0) ^ p := by
    funext A; exact fracTrace_eq_sum_eigenvalues₀ A.2 p
  rw [hfun]
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : Continuous (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} => A.2.eigenvalues₀ k) := by
    let _ : PseudoMetricSpace (Matrix ι ι ℂ) :=
      inferInstanceAs (PseudoMetricSpace (ι → ι → ℂ))
    apply (show LipschitzWith (Fintype.card ι : NNReal)
        (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} => A.2.eigenvalues₀ k) from
          LipschitzWith.of_dist_le_mul ?_).continuous
    intro A B
    change |A.2.eigenvalues₀ k - B.2.eigenvalues₀ k| ≤ (Fintype.card ι : ℝ) * dist A B
    refine A.2.abs_eigenvalues₀_sub_le_of_entry_le B.2 (fun i j => ?_) k
    calc ‖(A : Matrix ι ι ℂ) i j - (B : Matrix ι ι ℂ) i j‖ =
          dist ((A : Matrix ι ι ℂ) i j) ((B : Matrix ι ι ℂ) i j) := by rw [dist_eq_norm]
      _ ≤ dist ((A : Matrix ι ι ℂ) i) ((B : Matrix ι ι ℂ) i) := dist_le_pi_dist _ _ j
      _ ≤ dist (A : Matrix ι ι ℂ) (B : Matrix ι ι ℂ) := dist_le_pi_dist _ _ i
      _ = dist A B := rfl
  exact (hk.max continuous_const).rpow_const fun _ => Or.inr hp.le

/-- `ω ↦ Tr M(ω)^p` is measurable for a measurable everywhere-Hermitian `M` and `0 < p`. -/
theorem rh_measurable_fracTrace {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Matrix ι ι ℂ}
    (hM : Measurable M) (hH : ∀ ω, (M ω).IsHermitian) {p : ℝ} (hp : 0 < p) :
    Measurable (fun ω => fracTrace p (M ω)) := by
  have hc : Measurable (fun A : {A : Matrix ι ι ℂ // A.IsHermitian} => fracTrace p A.1) :=
    (rh_continuous_fracTrace (ι := ι) hp).measurable
  exact hc.comp (f := fun ω => (⟨M ω, hH ω⟩ : {A : Matrix ι ι ℂ // A.IsHermitian}))
    (Measurable.subtype_mk hM)

end Measurability

end BlockBand.Endpoints
