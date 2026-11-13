module

public import BlockBand.Model.Construction.OrderedProjector
public import BlockBand.Internal.Contracts.CoareaPalm
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Measurable eigenvectors for every Hermitian matrix

* `eigVec i A`: for every square complex matrix `A` and rank `i`, a vector, Borel measurable in
  `A` (`measurable_eigVec`), which for Hermitian `A` is a unit eigenvector of `A` with the
  `i`-th increasing eigenvalue (`eigVec_spec`), including degenerate spectra. Construction:
  the spectral projector `P_i = ∏_{j : λ_j ≠ λ_i} (A - λ_j)/(λ_i - λ_j)` (Lagrange product over
  the ranks with a different eigenvalue, `eigProj`), whose first column with positive diagonal
  entry is normalized (finite case split, no measurable choice). The Hermitian part
  `(A + A*)/2` makes the map total.
* `norm_le_of_eigen`: if `X` maps every eigenvector of the Hermitian `A` to a multiple of
  itself, and `|w_i*Xw_i| ≤ M` for unit eigenvectors `w_i` of the `i`-th eigenvalue for every
  rank `i`, then `‖X‖ ≤ M` (operator norm): `X` is diagonal in an eigenbasis of `A` with the
  diagonal entry of an eigenvalue independent of the eigenvector.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RbarMoment

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Foundations.Spectral
open BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix.Norms.L2Operator

variable {m : ℕ}

/-!
## The Hermitian part
-/

/-- The Hermitian part `(A + A*)/2`. -/
def hermPart (A : Matrix (Fin m) (Fin m) ℂ) : HermitianMatrix (Fin m) :=
  ⟨(2⁻¹ : ℂ) • (A + Aᴴ), by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    congr 1
    simp⟩

theorem hermPart_val {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    (hermPart A).val = A := by
  change (2⁻¹ : ℂ) • (A + Aᴴ) = A
  rw [hA.eq, ← two_smul ℂ A, smul_smul]
  norm_num

theorem hermPart_eq {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    hermPart A = ⟨A, hA⟩ :=
  Subtype.ext (hermPart_val hA)

theorem measurable_hermPart : Measurable (hermPart (m := m)) := by
  refine Measurable.subtype_mk ?_
  have hc : Continuous fun A : Matrix (Fin m) (Fin m) ℂ => Aᴴ := continuous_id.matrix_conjTranspose
  exact ((continuous_const (y := (2⁻¹ : ℂ))).smul (continuous_id.add hc)).measurable

/-!
## The spectral projector of a rank
-/

/-- One factor of `P_i`: the identity on ranks with eigenvalue `λ_i`. -/
def eigFactor (i j : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  if orderedEigenvalue A j = orderedEigenvalue A i then 1 else
    (((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ)⁻¹) •
      (A.val - (orderedEigenvalue A j : ℂ) • 1)

/-- The spectral projector `P_i` onto the eigenspace of `λ_i` (Lagrange product). -/
def eigProj (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  ((List.finRange (Fintype.card (Fin m))).map fun j => eigFactor i j A).prod

theorem measurable_matrix_entries {X : Type*} [MeasurableSpace X]
    {f : X → Matrix (Fin m) (Fin m) ℂ} (h : ∀ a b, Measurable fun x => f x a b) :
    Measurable f :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => h a b

theorem measurable_eigFactor (i j : Fin (Fintype.card (Fin m))) :
    Measurable (eigFactor (m := m) i j) := by
  have hs : MeasurableSet {A : HermitianMatrix (Fin m) |
      orderedEigenvalue A j = orderedEigenvalue A i} :=
    measurableSet_eq_fun (measurable_orderedEigenvalue j) (measurable_orderedEigenvalue i)
  refine Measurable.ite hs measurable_const (measurable_matrix_entries fun a b => ?_)
  change Measurable fun A : HermitianMatrix (Fin m) =>
    (((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ)⁻¹) *
      (A.val a b - (orderedEigenvalue A j : ℂ) * (1 : Matrix (Fin m) (Fin m) ℂ) a b)
  have hi := Complex.measurable_ofReal.comp (measurable_orderedEigenvalue (ι := Fin m) i)
  have hj := Complex.measurable_ofReal.comp (measurable_orderedEigenvalue (ι := Fin m) j)
  have he : Measurable fun A : HermitianMatrix (Fin m) => A.val a b :=
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_subtype_coe)
  simpa only [Complex.ofReal_sub, Function.comp_apply] using!
    (hi.sub hj).inv.mul (he.sub (hj.mul measurable_const))

theorem measurable_listProd {X β : Type*} [MeasurableSpace X] (l : List β)
    (f : β → X → Matrix (Fin m) (Fin m) ℂ) (hf : ∀ j, Measurable (f j)) :
    Measurable fun x => (l.map fun j => f j x).prod := by
  induction l with
  | nil => exact measurable_const
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons]
    refine measurable_matrix_entries fun a b => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply a).comp (hf j))).mul
        ((measurable_pi_apply b).comp ((measurable_pi_apply k).comp ih))

theorem measurable_eigProj (i : Fin (Fintype.card (Fin m))) :
    Measurable (eigProj (m := m) i) :=
  measurable_listProd _ _ fun j => measurable_eigFactor i j

theorem listProd_mulVec {β : Type*} (l : List β) (F : β → Matrix (Fin m) (Fin m) ℂ)
    (c : β → ℂ) (u : Fin m → ℂ) (h : ∀ j ∈ l, F j *ᵥ u = c j • u) :
    (l.map F).prod *ᵥ u = (l.map c).prod • u := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← mulVec_mulVec, ih (fun k hk => h k (List.mem_cons_of_mem _ hk)), mulVec_smul,
      h j List.mem_cons_self, smul_smul, mul_comm]

/-- The scalar by which a factor acts on the `r`-th eigenvector. -/
def eigScalar (i j r : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) : ℂ :=
  if orderedEigenvalue A j = orderedEigenvalue A i then 1 else
    ((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ)⁻¹ *
      ((orderedEigenvalue A r - orderedEigenvalue A j : ℝ) : ℂ)

theorem eigFactor_mulVec (i j r : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    eigFactor i j A *ᵥ increasingEigenvector A.property r =
      eigScalar i j r A • increasingEigenvector A.property r := by
  unfold eigFactor eigScalar
  split_ifs
  · simp
  · rw [smul_mulVec, sub_mulVec, mulVec_increasingEigenvector, smul_mulVec, one_mulVec,
      ← sub_smul, smul_smul]
    congr 1
    simp only [orderedEigenvalue, Complex.ofReal_sub]

/-- The `0/1` multiplicity indicator `δ_r = 1{λ_r = λ_i}`. -/
def eigDelta (i r : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) : ℝ :=
  if orderedEigenvalue A r = orderedEigenvalue A i then 1 else 0

theorem eigProj_mulVec (i r : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    eigProj i A *ᵥ increasingEigenvector A.property r =
      ((eigDelta i r A : ℝ) : ℂ) • increasingEigenvector A.property r := by
  rw [eigProj, listProd_mulVec _ _ (fun j => eigScalar i j r A) _
    (fun j _ => eigFactor_mulVec i j r A)]
  congr 1
  unfold eigDelta
  split_ifs with h
  · rw [Complex.ofReal_one]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    unfold eigScalar
    split_ifs with h'
    · rfl
    · rw [h]
      have : ((orderedEigenvalue A i - orderedEigenvalue A j : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.2 (Ne.symm h')
      field_simp
  · rw [Complex.ofReal_zero]
    apply List.prod_eq_zero
    exact List.mem_map.2 ⟨r, List.mem_finRange r, by unfold eigScalar; rw [ite_eq_right h]; simp⟩

theorem star_dot_increasingEigenvector (A : HermitianMatrix (Fin m))
    (r s : Fin (Fintype.card (Fin m))) :
    star (increasingEigenvector A.property r) ⬝ᵥ increasingEigenvector A.property s =
      if r = s then 1 else 0 :=
  increasingEigenvector_orthonormal A.property r s

/-- `P_i = Σ_r δ_r u_r u_r*`. -/
theorem eigProj_eq (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    eigProj i A = ∑ r, ((eigDelta i r A : ℝ) : ℂ) •
      vecMulVec (increasingEigenvector A.property r) (star (increasingEigenvector A.property r)) := by
  apply matrix_eq_of_mulVec_increasingEigenvector_eq A
  intro s
  rw [eigProj_mulVec, sum_mulVec, Finset.sum_eq_single s]
  · rw [smul_mulVec, vecMulVec_mulVec, star_dot_increasingEigenvector, ite_eq_left rfl]
    simp
  · intro r _ hr
    rw [smul_mulVec, vecMulVec_mulVec, star_dot_increasingEigenvector, ite_eq_right hr]
    simp
  · simp

theorem eigProj_conjTranspose (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    (eigProj i A)ᴴ = eigProj i A := by
  rw [eigProj_eq, conjTranspose_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [conjTranspose_smul, conjTranspose_vecMulVec, star_star]
  simp

theorem eigProj_mul_self (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    eigProj i A * eigProj i A = eigProj i A := by
  apply matrix_eq_of_mulVec_increasingEigenvector_eq A
  intro s
  rw [← mulVec_mulVec, eigProj_mulVec, mulVec_smul, eigProj_mulVec, smul_smul]
  congr 1
  unfold eigDelta
  split_ifs <;> simp

theorem mul_eigProj (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    A.val * eigProj i A = (orderedEigenvalue A i : ℂ) • eigProj i A := by
  apply matrix_eq_of_mulVec_increasingEigenvector_eq A
  intro s
  rw [← mulVec_mulVec, eigProj_mulVec, mulVec_smul, mulVec_increasingEigenvector, smul_mulVec,
    eigProj_mulVec, smul_smul, smul_smul]
  congr 1
  unfold eigDelta
  split_ifs with h
  · simp [orderedEigenvalue] at h ⊢; rw [h]
  · simp

theorem eigProj_diag_re (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m))
    (y : Fin m) : (eigProj i A y y).re =
      ∑ r, eigDelta i r A * ‖increasingEigenvector A.property r y‖ ^ 2 := by
  rw [eigProj_eq, Matrix.sum_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]

theorem exists_eigProj_diag_pos (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    ∃ y, 0 < (eigProj i A y y).re := by
  by_contra h
  push Not at h
  have hs := Finset.sum_nonpos (s := Finset.univ) (fun y _ => h y)
  simp_rw [eigProj_diag_re] at hs
  rw [Finset.sum_comm] at hs
  have hterm : ∀ r, ∑ y, eigDelta i r A * ‖increasingEigenvector A.property r y‖ ^ 2 =
      eigDelta i r A := fun r => by
    rw [← Finset.mul_sum, sum_norm_sq_increasingEigenvector, mul_one]
  simp_rw [hterm] at hs
  have hnn : ∀ r, 0 ≤ eigDelta i r A := fun r => by unfold eigDelta; split_ifs <;> norm_num
  have hi : eigDelta i i A ≤ ∑ r, eigDelta i r A :=
    Finset.single_le_sum (fun r _ => hnn r) (Finset.mem_univ i)
  have h1 : eigDelta i i A = 1 := by unfold eigDelta; rw [ite_eq_left rfl]
  linarith

/-!
## The normalized column
-/

/-- The `y`-th column of `P_i`, normalized by the square root of its diagonal entry. -/
def eigColumn (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) (y : Fin m) :
    Fin m → ℂ :=
  fun x => eigProj i A x y / (Real.sqrt (eigProj i A y y).re : ℂ)

/-- The region where `y` is the first column of `P_i` with positive diagonal. -/
def eigRegion (i : Fin (Fintype.card (Fin m))) (y : Fin m) : Set (HermitianMatrix (Fin m)) :=
  {A | 0 < (eigProj i A y y).re ∧ ∀ k : Fin m, k < y → ¬ 0 < (eigProj i A k k).re}

/-- The selected eigenvector (zero outside every region, which never happens). -/
def eigSel (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) : Fin m → ℂ := by
  classical
  exact fun x => ∑ y : Fin m, if A ∈ eigRegion i y then eigColumn i A y x else 0

theorem measurableSet_eigRegion (i : Fin (Fintype.card (Fin m))) (y : Fin m) :
    MeasurableSet (eigRegion (m := m) i y) := by
  have hd : ∀ k : Fin m, Measurable fun A : HermitianMatrix (Fin m) => (eigProj i A k k).re :=
    fun k => Complex.measurable_re.comp
      ((measurable_pi_apply k).comp ((measurable_pi_apply k).comp (measurable_eigProj i)))
  have h1 := measurableSet_lt (f := fun _ : HermitianMatrix (Fin m) => (0 : ℝ)) measurable_const
    (hd y)
  have h2 : MeasurableSet {A : HermitianMatrix (Fin m) |
      ∀ k : Fin m, k < y → ¬ 0 < (eigProj i A k k).re} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      (measurableSet_lt (f := fun _ : HermitianMatrix (Fin m) => (0 : ℝ)) measurable_const
        (hd k)).compl
  exact h1.inter h2

theorem measurable_eigSel_apply (i : Fin (Fintype.card (Fin m))) (x : Fin m) :
    Measurable fun A : HermitianMatrix (Fin m) => eigSel i A x := by
  classical
  unfold eigSel
  refine Finset.measurable_sum _ fun y _ => Measurable.ite (measurableSet_eigRegion i y) ?_
    measurable_const
  unfold eigColumn
  exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp (measurable_eigProj i))).div
    (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp
      (Complex.measurable_re.comp
        ((measurable_pi_apply y).comp ((measurable_pi_apply y).comp (measurable_eigProj i))))))

theorem exists_eigRegion (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    ∃ y, A ∈ eigRegion i y := by
  classical
  let S := Finset.univ.filter fun y : Fin m => 0 < (eigProj i A y y).re
  have hS : S.Nonempty := by
    obtain ⟨y, hy⟩ := exists_eigProj_diag_pos i A
    exact ⟨y, by simp [S, hy]⟩
  refine ⟨S.min' hS, (Finset.mem_filter.mp (Finset.min'_mem S hS)).2, fun k hk hpos => ?_⟩
  exact (not_le_of_gt hk) (Finset.min'_le S k (by simp [S, hpos]))

theorem eigRegion_unique (i : Fin (Fintype.card (Fin m))) {A : HermitianMatrix (Fin m)}
    {y z : Fin m} (hy : A ∈ eigRegion i y) (hz : A ∈ eigRegion i z) : y = z := by
  rcases lt_trichotomy y z with h | h | h
  · exact False.elim (hz.2 y h hy.1)
  · exact h
  · exact False.elim (hy.2 z h hz.1)

theorem eigSel_eq (i : Fin (Fintype.card (Fin m))) {A : HermitianMatrix (Fin m)} {y : Fin m}
    (hy : A ∈ eigRegion i y) : eigSel i A = eigColumn i A y := by
  classical
  funext x
  unfold eigSel
  rw [Finset.sum_eq_single y]
  · rw [ite_eq_left hy]
  · intro z _ hz
    rw [ite_eq_right]
    exact fun hz' => hz (eigRegion_unique i hz' hy)
  · simp

theorem l2Norm_eigColumn (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m))
    {y : Fin m} (hy : 0 < (eigProj i A y y).re) : l2Norm (eigColumn i A y) = 1 := by
  set P := eigProj i A
  set d := (P y y).re
  have hcol : ∑ x, ‖P x y‖ ^ 2 = d := by
    have hPH : Pᴴ = P := eigProj_conjTranspose i A
    have hPP : P * P = P := eigProj_mul_self i A
    have hsym : ∀ x, P y x = star (P x y) := fun x => by
      rw [← conjTranspose_apply, hPH]
    have h := congrArg Complex.re (congrFun (congrFun hPP y) y)
    rw [Matrix.mul_apply, Complex.re_sum] at h
    change _ = (P y y).re
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hsym x, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  change Real.sqrt (∑ x, ‖P x y / (Real.sqrt d : ℂ)‖ ^ 2) = 1
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hy
  have hterm : ∀ x, ‖P x y / (Real.sqrt d : ℂ)‖ ^ 2 = ‖P x y‖ ^ 2 / d := fun x => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsq.le, div_pow,
      Real.sq_sqrt hy.le]
  simp_rw [hterm]
  rw [← Finset.sum_div, hcol, div_self hy.ne', Real.sqrt_one]

theorem mulVec_eigColumn (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m))
    (y : Fin m) : A.val *ᵥ eigColumn i A y =
      (orderedEigenvalue A i : ℂ) • eigColumn i A y := by
  have h : eigColumn i A y = ((Real.sqrt (eigProj i A y y).re : ℂ)⁻¹) •
      (eigProj i A *ᵥ Pi.single y 1) := by
    funext x
    rw [mulVec_single_one]
    simp [eigColumn, div_eq_inv_mul]
  rw [h, mulVec_smul, mulVec_mulVec, mul_eigProj, smul_mulVec, smul_comm]

theorem eigSel_spec (i : Fin (Fintype.card (Fin m))) (A : HermitianMatrix (Fin m)) :
    l2Norm (eigSel i A) = 1 ∧
      A.val *ᵥ eigSel i A = (orderedEigenvalue A i : ℂ) • eigSel i A := by
  obtain ⟨y, hy⟩ := exists_eigRegion i A
  rw [eigSel_eq i hy]
  exact ⟨l2Norm_eigColumn i A hy.1, mulVec_eigColumn i A y⟩

/-!
## The total measurable eigenvector map
-/

/-- `eigVec i A`: a unit eigenvector of rank `i` of the Hermitian part of `A`. -/
def eigVec (i : Fin (Fintype.card (Fin m))) (A : Matrix (Fin m) (Fin m) ℂ) : Fin m → ℂ :=
  eigSel i (hermPart A)

theorem measurable_eigVec (i : Fin (Fintype.card (Fin m))) :
    Measurable (eigVec (m := m) i) :=
  measurable_pi_iff.mpr fun x => (measurable_eigSel_apply i x).comp measurable_hermPart

/-- **Measurable unit eigenvectors, degenerate spectra included.** -/
theorem eigVec_spec (i : Fin (Fintype.card (Fin m))) {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) :
    l2Norm (eigVec i A) = 1 ∧
      A *ᵥ eigVec i A = (increasingEigenvalue hA i : ℂ) • eigVec i A := by
  unfold eigVec
  rw [hermPart_eq hA]
  exact eigSel_spec i ⟨A, hA⟩

/-!
## Operator norm of a matrix diagonal in an eigenbasis
-/

theorem star_dot_self_eq (x : Fin m → ℂ) : star x ⬝ᵥ x = ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem star_dot_self_of_unit {x : Fin m → ℂ} (hx : l2Norm x = 1) : star x ⬝ᵥ x = 1 := by
  rw [star_dot_self_eq]
  unfold l2Norm at hx
  have h0 : 0 ≤ ∑ k, ‖x k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have : ∑ k, ‖x k‖ ^ 2 = 1 := by
    have := Real.sq_sqrt h0
    rw [hx] at this
    linarith
  rw [this, Complex.ofReal_one]

theorem ne_zero_of_unit {x : Fin m → ℂ} (hx : l2Norm x = 1) : x ≠ 0 := by
  rintro rfl
  simp [l2Norm] at hx

/-- Two eigenvectors of one eigenvalue have the same `X`-eigenvalue when `X` maps every
eigenvector of `A` to a multiple of itself. -/
theorem eigen_scalar_eq {A X : Matrix (Fin m) (Fin m) ℂ}
    (hX : ∀ (x : Fin m → ℂ) (μ : ℂ), A *ᵥ x = μ • x → ∃ c : ℂ, X *ᵥ x = c • x)
    {u w : Fin m → ℂ} {μ a b : ℂ} (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hu : A *ᵥ u = μ • u)
    (hw : A *ᵥ w = μ • w) (hXu : X *ᵥ u = a • u) (hXw : X *ᵥ w = b • w) : a = b := by
  obtain ⟨e, he⟩ := hX (u + w) μ (by rw [mulVec_add, hu, hw, smul_add])
  rw [mulVec_add, hXu, hXw] at he
  have key : (a - e) • u = (e - b) • w := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, he, smul_add, add_comm]
  by_cases hae : a = e
  · subst hae
    have h0 : (a - b) • w = 0 := by rw [← key, sub_self, zero_smul]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hw0
  · have hu' : u = ((e - b) / (a - e)) • w := by
      rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hae),
        one_smul]
    have h1 : X *ᵥ u = b • u := by rw [hu', mulVec_smul, hXw, smul_comm]
    rw [hXu] at h1
    have h0 : (a - b) • u = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h0 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hu0

theorem l2_opNorm_le_one_of_unitary {U : Matrix (Fin m) (Fin m) ℂ} (hU : Uᴴ * U = 1) :
    ‖U‖ ≤ 1 := by
  have h := l2_opNorm_conjTranspose_mul_self U
  rw [hU] at h
  have h1 : ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ ≤ 1 := by
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by simp
  have := norm_nonneg U
  nlinarith

/-- **`‖X‖ ≤ max_i |w_i*Xw_i|`** when `X` maps every eigenvector of the Hermitian `A` to a
multiple of itself and `w_i` is a unit eigenvector of the `i`-th eigenvalue for every rank. -/
theorem norm_le_of_eigen {A X : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (hX : ∀ (x : Fin m → ℂ) (μ : ℂ), A *ᵥ x = μ • x → ∃ c : ℂ, X *ᵥ x = c • x)
    (w : Fin (Fintype.card (Fin m)) → Fin m → ℂ)
    (hw : ∀ i, l2Norm (w i) = 1 ∧ A *ᵥ w i = (increasingEigenvalue hA i : ℂ) • w i)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ‖star (w i) ⬝ᵥ (X *ᵥ w i)‖ ≤ M) : ‖X‖ ≤ M := by
  set U : Matrix (Fin m) (Fin m) ℂ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  have hcol : ∀ y : Fin m, increasingEigenvector hA (increasingIndex.symm y) = fun z => U z y :=
    fun y => by
      simp only [increasingEigenvector, increasingEigenbasis_apply, Equiv.apply_symm_apply, U,
        Matrix.IsHermitian.eigenvectorUnitary_apply]
  choose d hd using fun y : Fin m =>
    hX _ _ (mulVec_increasingEigenvector hA (increasingIndex.symm y))
  have hdM : ∀ y, ‖d y‖ ≤ M := by
    intro y
    set r := increasingIndex.symm y
    obtain ⟨c, hc⟩ := hX (w r) _ (hw r).2
    have hu0 : increasingEigenvector hA r ≠ 0 := by
      intro h0
      have := sum_norm_sq_increasingEigenvector hA r
      rw [h0] at this
      simp at this
    have hdc := eigen_scalar_eq hX hu0 (ne_zero_of_unit (hw r).1)
      (mulVec_increasingEigenvector hA r) (hw r).2 (hd y) hc
    have hcw : star (w r) ⬝ᵥ (X *ᵥ w r) = c := by
      rw [hc, dotProduct_smul, star_dot_self_of_unit (hw r).1, smul_eq_mul, mul_one]
    rw [hdc, ← hcw]
    exact hM r
  have hXU : X * U = U * diagonal d := by
    ext x y
    rw [mul_diagonal]
    have h := congrFun (hd y) x
    rw [hcol y] at h
    simpa [mulVec, dotProduct, Matrix.mul_apply, mul_comm] using h
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  have hUU' : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have hXe : X = U * diagonal d * Uᴴ := by
    rw [← hXU, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hUU, Matrix.mul_one]
  have hU1 := l2_opNorm_le_one_of_unitary hUU'
  have hUh1 : ‖Uᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact hU1
  have hD : ‖(diagonal d : Matrix (Fin m) (Fin m) ℂ)‖ ≤ M := by
    rw [l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hM0).2 hdM
  rw [hXe]
  calc ‖U * diagonal d * Uᴴ‖ ≤ ‖U * diagonal d‖ * ‖Uᴴ‖ := l2_opNorm_mul _ _
    _ ≤ (‖U‖ * ‖(diagonal d : Matrix (Fin m) (Fin m) ℂ)‖) * ‖Uᴴ‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * M) * 1 := by gcongr
    _ = M := by ring

end BlockBand.DeterminantScore.RbarMoment
