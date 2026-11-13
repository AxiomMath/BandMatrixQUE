module

public import BlockBand.LocalWindow.ProofPartTwoPoleMeasurableLargeRho

/-!
# A measurable isometry onto `w^⊥`

A measurable choice of an isometry onto the orthogonal complement of the pole direction, from
selected eigenvectors of the rank-one projector `ww*`, and the measurability of the compressed
window bad sets.

## Main results

* **`isometry_compl_of_orth`** (generic): `U*U = 1`, `U*w = 0`, `w` unit, `|β| = n + 1` give
  `UU* + ww* = 1` (the square matrix `[U | w]` is unitary).
* **`star_dotProduct_pairEigvecH_eq_zero`**: for `X = ww*` (`w` unit), every selected eigenvector
  of `X` with index `< 2W - 1` is orthogonal to `w` (increasing eigenvalues, at most one
  nonzero eigenvalue).
* **`projIsometry sel X`**: the matrix of the first `2W - 1` selected eigenvectors of `X`;
  **`measurable_projIsometry_comp`**; **`projIsometry_spec`**: for `X = ww*`, `U*U = 1`,
  `U*w = 0`, `UU* + ww* = 1`.
* **`poleIsometry sel j₀ ω = projIsometry sel (poleWW j₀ H_R C)`**, **`measurable_poleIsometry`**,
  **`poleIsometry_spec`**: on the event `PoleSimple`, an isometry onto `(poleDir)^⊥`.
* `measurable_nativeCentre_comp`, `natDeformedH`, **`measurableSet_not_natWindowGood_comp`**:
  along measurable data (`F(y)` Hermitian, any `J(y)`, `X(y)`), the window bad set on `Fin N`
  `{y | ¬ NatWindowGood (F y) sel s E₀ β ε (J y) (X y)}` is measurable.
* **`measurableSet_not_compressWindowGood`**: hence, for measurable exterior data `F(ω)`
  (compressed deformation), `J'(ω)` and the measurable `U(ω) = poleIsometry sel j₀ ω`, the joint
  compressed bad set `{(ω, G) | ¬ NatWindowGood (F ω) sel' s' E₀ β ε (J' ω) (U(ω)* G U(ω))}` is
  measurable; its section at fixed `ω` is the set bounded by `gue_not_compressWindowGood_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.LawBridge
open scoped ENNReal Matrix.Norms.L2Operator

/-!
## The complement of an isometry orthogonal to a unit vector
-/

section Compl

variable {β : Type} [Fintype β] [DecidableEq β]

/-- **The complement identity** (generic): if `U : ℂ^n → ℂ^β` has `U*U = 1`, `U*w = 0`, `w` is a
unit vector and `|β| = n + 1`, then `UU* + ww* = 1` (`[U | w]` is a square isometry, hence
unitary). -/
theorem isometry_compl_of_orth (n : ℕ) (hn : Fintype.card β = n + 1) {U : Matrix β (Fin n) ℂ}
    {w : β → ℂ} (hUU : Uᴴ * U = 1) (hUw : Uᴴ *ᵥ w = 0) (hw : sqNorm w = 1) :
    U * Uᴴ + vecMulVec w (star w) = 1 := by
  set T : Matrix β (Option (Fin n)) ℂ := Matrix.of fun a o => Option.elim o (w a) (fun m => U a m)
    with hTdef
  have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
  have hTT : Tᴴ * T = 1 := by
    ext o o'
    rcases o with _ | m <;> rcases o' with _ | m'
    · simpa [hTdef, Matrix.mul_apply, dotProduct] using hww
    · have h := congrFun hUw m'
      simp only [mulVec, dotProduct, conjTranspose_apply, Pi.zero_apply] at h
      have h' := congrArg star h
      simp only [star_sum, star_mul', star_star, star_zero] at h'
      simp only [hTdef, Matrix.mul_apply, conjTranspose_apply, of_apply, Option.elim_none,
        Option.elim_some, one_apply]
      simp only [reduceCtorEq, ite_false]
      rw [← h']; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · have h := congrFun hUw m
      simp only [mulVec, dotProduct, conjTranspose_apply, Pi.zero_apply] at h
      simp only [hTdef, Matrix.mul_apply, conjTranspose_apply, of_apply, Option.elim_none,
        Option.elim_some, one_apply]
      simp only [reduceCtorEq, ite_false]
      exact h
    · have h := congrFun (congrFun hUU m) m'
      simp only [Matrix.mul_apply, conjTranspose_apply, one_apply] at h
      simp only [hTdef, Matrix.mul_apply, conjTranspose_apply, of_apply, Option.elim_some,
        one_apply, Option.some.injEq]
      exact h
  have hcard : Fintype.card β = Fintype.card (Option (Fin n)) := by
    rw [hn, Fintype.card_option, Fintype.card_fin]
  set e : β ≃ Option (Fin n) := Fintype.equivOfCardEq hcard
  set T' : Matrix β β ℂ := T.submatrix id e with hT'
  have hT'T' : T'ᴴ * T' = 1 := by
    have : T'ᴴ * T' = (Tᴴ * T).submatrix e e := by
      rw [hT', conjTranspose_submatrix]
      exact submatrix_mul_equiv Tᴴ T e (Equiv.refl _) e
    rw [this, hTT, submatrix_one_equiv]
  have h1 : T' * T'ᴴ = 1 := mul_eq_one_comm.mp hT'T'
  have h2 : T' * T'ᴴ = T * Tᴴ := by
    rw [hT', conjTranspose_submatrix, submatrix_mul_equiv T Tᴴ id e id, submatrix_id_id]
  rw [h2] at h1
  rw [← h1]
  ext a b
  simp only [hTdef, Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, of_apply, vecMulVec_apply,
    Pi.star_apply, Fintype.sum_option, Option.elim_none, Option.elim_some]
  ring

end Compl

/-!
## The first `2W - 1` eigenvectors of a rank-one projector
-/

section Proj

variable {p : Parameters} {i : ZMod p.n}

/-- The pair label of the index `m < 2W - 1` (through `pairEquiv`). -/
def projLabel (p : Parameters) (i : ZMod p.n) (m : Fin (2 * p.W - 1)) : PairSite p i :=
  (pairEquiv p i).symm (Fin.castLE (Nat.sub_le _ _) m)

/-- The pair label of the last index `2W - 1` (through `pairEquiv`). -/
def projLast (p : Parameters) (i : ZMod p.n) : PairSite p i :=
  (pairEquiv p i).symm ⟨2 * p.W - 1, by have := p.W_pos; omega⟩

theorem projLabel_injective : Function.Injective (projLabel p i) := by
  intro m m' h
  unfold projLabel at h
  have := (pairEquiv p i).symm.injective h
  exact Fin.castLE_injective _ this

theorem projLabel_ne_last (m : Fin (2 * p.W - 1)) : projLabel p i m ≠ projLast p i := by
  intro h
  unfold projLabel projLast at h
  have h' := congrArg Fin.val ((pairEquiv p i).symm.injective h)
  simp only [Fin.val_castLE] at h'
  have := m.2
  omega

/-- **Eigenvectors of a rank-one projector off the top label are orthogonal to `w`**: for
`X = ww*` with `w` unit, every selected eigenvector of `X` with index `< 2W - 1` has
`w*v = 0` (eigenvalues `|w*v_k|²` are increasing and at most one is nonzero, since two
eigenvectors not orthogonal to `w` would both be parallel to `w`). -/
theorem star_dotProduct_pairEigvecH_eq_zero (sel : CEH.EigenpairSelection (2 * p.W))
    {w : PairSite p i → ℂ} (hw : sqNorm w = 1) (m : Fin (2 * p.W - 1)) :
    star w ⬝ᵥ pairEigvecH sel (vecMulVec w (star w)) (projLabel p i m) = 0 := by
  set X := vecMulVec w (star w) with hXdef
  have hX : X.IsHermitian := by
    unfold Matrix.IsHermitian; rw [hXdef, conjTranspose_vecMulVec, star_star]
  have hww : star w ⬝ᵥ w = 1 := by rw [star_dotProduct_self, hw]; simp
  set v := pairEigvecH sel X with hvdef
  set lam := pairEigvalH sel X with hlamdef
  have hon : IsOrthonormalFamily v := by
    rw [hvdef, ← pairEigvec_eq_H sel hX]; exact isOrthonormalFamily_pairEigvec sel X hX
  have heig : ∀ k, X *ᵥ v k = (lam k : ℂ) • v k := by
    intro k
    have h := mulVec_pairEigvec sel X hX k
    rw [pairEigvec_eq_H sel hX, pairEigval_eq_H sel hX] at h
    exact h
  -- `λ_k v_k = (w*v_k) w`
  have hrank : ∀ k, (lam k : ℂ) • v k = (star w ⬝ᵥ v k) • w := by
    intro k; rw [← heig k, hXdef, vecMulVec_star_mulVec]
  -- `λ_k = |w*v_k|²`
  have hlam : ∀ k, (lam k : ℂ) = (star w ⬝ᵥ v k) * star (star w ⬝ᵥ v k) := by
    intro k
    have h1 : star (v k) ⬝ᵥ ((lam k : ℂ) • v k) = (lam k : ℂ) := by
      rw [dotProduct_smul, hon k k]; simp
    rw [hrank k, dotProduct_smul, smul_eq_mul] at h1
    rw [← h1]
    have h2 : star (v k) ⬝ᵥ w = star (star w ⬝ᵥ v k) := by
      rw [star_dotProduct]
    rw [h2]
  -- two distinct labels cannot both see `w`
  have htwo : ∀ k l, k ≠ l → (star w ⬝ᵥ v k) = 0 ∨ (star w ⬝ᵥ v l) = 0 := by
    intro k l hkl
    have h0 : star ((lam k : ℂ) • v k) ⬝ᵥ ((lam l : ℂ) • v l) = 0 := by
      rw [star_smul, smul_dotProduct, dotProduct_smul, hon k l]; simp [hkl]
    rw [hrank k, hrank l, star_smul, smul_dotProduct, dotProduct_smul, hww, smul_eq_mul,
      smul_eq_mul, mul_one] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · left; exact star_eq_zero.mp h
    · right; exact h
  -- monotonicity of the selected eigenvalues in the index
  have hmono : lam (projLabel p i m) ≤ lam (projLast p i) := by
    rw [hlamdef]
    unfold pairEigvalH projLabel projLast
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine sel.increasing _ ?_
    show (Fin.castLE (Nat.sub_le _ _) m).val ≤ 2 * p.W - 1
    simp only [Fin.val_castLE]; omega
  by_contra hne
  have hpos : 0 < lam (projLabel p i m) := by
    have h := hlam (projLabel p i m)
    have hn : (star w ⬝ᵥ v (projLabel p i m)) * star (star w ⬝ᵥ v (projLabel p i m)) =
        ((‖star w ⬝ᵥ v (projLabel p i m)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hn] at h
    have h' : lam (projLabel p i m) = ‖star w ⬝ᵥ v (projLabel p i m)‖ ^ 2 := by exact_mod_cast h
    rw [h']
    exact pow_pos (norm_pos_iff.mpr hne) 2
  have hlast : star w ⬝ᵥ v (projLast p i) ≠ 0 := by
    intro h0
    have h := hlam (projLast p i)
    rw [h0, zero_mul] at h
    have : lam (projLast p i) = 0 := by exact_mod_cast h
    linarith
  rcases htwo _ _ (projLabel_ne_last m) with h | h
  · exact hne h
  · exact hlast h

/-- **The matrix of the first `2W - 1` selected eigenvectors** of `X` (pair coordinates;
`pairEigvecH` uses the Hermitian part, so no proof enters). -/
def projIsometry (sel : CEH.EigenpairSelection (2 * p.W)) (X : PairMatrix p i) :
    Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ :=
  Matrix.of fun a m => pairEigvecH sel X (projLabel p i m) a

/-- `X ↦ projIsometry sel X` is measurable along measurable data. -/
theorem measurable_projIsometry_comp {X : Type*} [MeasurableSpace X]
    (sel : CEH.EigenpairSelection (2 * p.W)) {Y : X → PairMatrix p i} (hY : Measurable Y) :
    Measurable fun x => projIsometry sel (Y x) := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun m => ?_
  exact measurable_pairEigvecH_comp sel hY (projLabel p i m) a

/-- **The selected isometry onto `w^⊥`**: for `X = ww*` with `w` unit, `U = projIsometry sel X`
has `U*U = 1`, `U*w = 0` and `UU* + ww* = 1`. -/
theorem projIsometry_spec (sel : CEH.EigenpairSelection (2 * p.W)) {w : PairSite p i → ℂ}
    (hw : sqNorm w = 1) :
    (projIsometry sel (vecMulVec w (star w)))ᴴ * projIsometry sel (vecMulVec w (star w)) = 1 ∧
      (projIsometry sel (vecMulVec w (star w)))ᴴ *ᵥ w = 0 ∧
      projIsometry sel (vecMulVec w (star w)) * (projIsometry sel (vecMulVec w (star w)))ᴴ +
        vecMulVec w (star w) = 1 := by
  set X := vecMulVec w (star w) with hXdef
  have hX : X.IsHermitian := by
    unfold Matrix.IsHermitian; rw [hXdef, conjTranspose_vecMulVec, star_star]
  have hon : IsOrthonormalFamily (pairEigvecH sel X) := by
    rw [← pairEigvec_eq_H sel hX]; exact isOrthonormalFamily_pairEigvec sel X hX
  set U := projIsometry sel X with hUdef
  have hUU : Uᴴ * U = 1 := by
    ext m m'
    have h := hon (projLabel p i m) (projLabel p i m')
    simp only [dotProduct, Pi.star_apply] at h
    simp only [hUdef, projIsometry, Matrix.mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [h]
    by_cases hmm : m = m'
    · simp [hmm]
    · have hne : projLabel p i m ≠ projLabel p i m' := fun h' => hmm (projLabel_injective h')
      simp [hmm, hne]
  have hUw : Uᴴ *ᵥ w = 0 := by
    ext m
    have h := star_dotProduct_pairEigvecH_eq_zero sel hw m
    rw [← hXdef] at h
    have h' := congrArg star h
    rw [star_dotProduct, star_star, star_zero] at h'
    simp only [dotProduct, Pi.star_apply] at h'
    simp only [hUdef, projIsometry, mulVec, dotProduct, conjTranspose_apply, of_apply,
      Pi.zero_apply]
    rw [← h']
  refine ⟨hUU, hUw, isometry_compl_of_orth _ ?_ hUU hUw hw⟩
  rw [BlockBand.Angular.FiberAngular.card_pairSite]
  have := p.W_pos
  omega

end Proj

/-!
## The measurable pole isometry
-/

section Pole

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-- **The measurable compression at a pole label** `j₀`: the first `2W - 1` selected eigenvectors
of the basis-free direction projector `poleWW j₀ H_R C`. -/
def poleIsometry (sel : CEH.EigenpairSelection (2 * p.W)) (j₀ : ExteriorSite p i)
    (om : SplitState p i) : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ :=
  projIsometry sel (poleWW j₀ om.1 om.2.1)

/-- **`ω ↦ U(ω)` is Borel measurable**. -/
theorem measurable_poleIsometry (sel : CEH.EigenpairSelection (2 * p.W)) (j₀ : ExteriorSite p i) :
    Measurable (poleIsometry (p := p) (i := i) sel j₀) :=
  measurable_projIsometry_comp sel (measurable_poleWW j₀)

/-- **On the label event `U(ω)` is an isometry onto `(poleDir)^⊥`**: `U*U = 1`, `U*w = 0`,
`UU* + ww* = 1` for `w = poleDir hH j₀ C` (the hypotheses `hUU, hUw, hcompl` of the large-`ρ`
window transfer). -/
theorem poleIsometry_spec (sel : CEH.EigenpairSelection (2 * p.W)) {om : SplitState p i}
    (hH : om.1.IsHermitian) {j₀ : ExteriorSite p i} (hs : PoleSimple hH j₀) :
    (poleIsometry sel j₀ om)ᴴ * poleIsometry sel j₀ om = 1 ∧
      (poleIsometry sel j₀ om)ᴴ *ᵥ poleDir hH j₀ om.2.1 = 0 ∧
      poleIsometry sel j₀ om * (poleIsometry sel j₀ om)ᴴ +
        vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) = 1 := by
  unfold poleIsometry
  rw [poleWW_eq hH hs]
  exact projIsometry_spec sel (sqNorm_poleDir hH j₀ om.2.1)

end Pole

/-!
## The window bad set on `Fin N` is measurable
-/

section NatMeas

variable {Y : Type*} [MeasurableSpace Y] {N : ℕ}

/-- `nativeCentre` along measurable data with Hermitian `F` (`s > 0`, `N ≠ 0`). -/
theorem measurable_nativeCentre_comp [NeZero N] {s : ℝ} (hs : 0 < s)
    {J F : Y → Matrix (Fin N) (Fin N) ℂ} {lam : Y → ℝ} (hJ : Measurable J) (hF : Measurable F)
    (hlam : Measurable lam) (hH : ∀ y, (F y).IsHermitian) :
    Measurable fun y => nativeCentre (J y) (F y) s (lam y) := by
  have hm := measurable_freshDyson_comp hs hF (Complex.measurable_ofReal.comp hlam) hH
    (fun y => by simp)
  have hc : Measurable fun y => ((lam y : ℂ) + (s : ℂ) * freshDyson (F y) s (lam y)) :=
    (Complex.measurable_ofReal.comp hlam).add (measurable_const.mul hm)
  have hcont1 : Continuous fun q : Matrix (Fin N) (Fin N) ℂ × ℂ =>
      q.1 - q.2 • (1 : Matrix (Fin N) (Fin N) ℂ) :=
    continuous_fst.sub (continuous_snd.smul continuous_const)
  have hR := measurable_matrixInverse.comp (hcont1.measurable.comp (hF.prodMk hc))
  have hcont2 : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => (s : ℂ) • (Z * Zᴴ) :=
    (continuous_const_smul _).comp (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
  have hΓ := hcont2.measurable.comp hR
  have hT : Measurable fun y => (J y * (s : ℂ) •
      ((F y - ((lam y : ℂ) + (s : ℂ) * freshDyson (F y) s (lam y)) • 1)⁻¹ *
        ((F y - ((lam y : ℂ) + (s : ℂ) * freshDyson (F y) s (lam y)) • 1)⁻¹)ᴴ)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hJ)).mul
      ((measurable_pi_apply a).comp ((measurable_pi_apply b).comp hΓ))
  exact measurable_const.mul hT

/-- The Hermitian part of `F + X`, as an element of `CEH.SourceHermitian N` (no Hermitian
hypothesis needed). -/
def natDeformedH (F X : Matrix (Fin N) (Fin N) ℂ) : CEH.SourceHermitian N :=
  ⟨(1 / 2 : ℂ) • ((F + X) + (F + X)ᴴ), by
    unfold Matrix.IsHermitian
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    congr 1
    simp⟩

theorem natDeformedH_eq (F : CEH.SourceHermitian N) {X : CEH.SourceMatrix N}
    (hX : X.IsHermitian) : natDeformedH F.1 X = natDeformed F X hX := by
  apply Subtype.ext
  change (1 / 2 : ℂ) • ((F.1 + X) + (F.1 + X)ᴴ) = F.1 + X
  rw [(F.2.add hX).eq, ← two_smul ℂ (F.1 + X), smul_smul]
  norm_num

theorem measurable_natDeformedH_comp {F X : Y → Matrix (Fin N) (Fin N) ℂ} (hF : Measurable F)
    (hX : Measurable X) : Measurable fun y => natDeformedH (F y) (X y) := by
  refine Measurable.subtype_mk ?_
  have hc : Continuous fun Z : Matrix (Fin N) (Fin N) ℂ => (1 / 2 : ℂ) • (Z + Zᴴ) :=
    (continuous_const_smul (1 / 2 : ℂ)).comp (continuous_id.add continuous_id.matrix_conjTranspose)
  exact hc.measurable.comp (hF.add hX)

/-- The overlap `u* J v` is measurable along measurable data. -/
theorem measurable_natOverlap_comp {J : Y → Matrix (Fin N) (Fin N) ℂ} {u v : Y → Fin N → ℂ}
    (hJ : Measurable J) (hu : ∀ a, Measurable fun y => u y a)
    (hv : ∀ a, Measurable fun y => v y a) :
    Measurable fun y => CEH.sourceMatrixElement (J y) (u y) (v y) := by
  simp only [CEH.sourceMatrixElement, dotProduct, mulVec, Pi.star_apply]
  refine Finset.measurable_sum _ fun a _ => ?_
  refine (Complex.continuous_conj.measurable.comp (hu a)).mul ?_
  exact Finset.measurable_sum _ fun b _ =>
    ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hJ)).mul (hv b)

/-- **The window bad set on `Fin N` is measurable along measurable data**: for
measurable `y ↦ F(y)` (Hermitian), `J(y)`, `X(y)`, `s > 0`, `N ≠ 0` and any eigenpair
selection, `{y | ¬ NatWindowGood (F y) sel s E₀ β ε (J y) (X y)}` is measurable.
-/
theorem measurableSet_not_natWindowGood_comp [NeZero N] {F : Y → CEH.SourceHermitian N}
    (hF : Measurable fun y => (F y).1) {J X : Y → Matrix (Fin N) (Fin N) ℂ} (hJ : Measurable J)
    (hX : Measurable X) (sel : CEH.EigenpairSelection N) {s : ℝ} (hs : 0 < s) (E₀ β ε : ℝ) :
    MeasurableSet {y | ¬ NatWindowGood (F y) sel s E₀ β ε (J y) (X y)} := by
  set h := (N : ℝ) ^ (-1 + β) with hh
  set tol := 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-(1 : ℝ) / 2)) with htol
  have hD := measurable_natDeformedH_comp hF hX
  have e : {y | ¬ NatWindowGood (F y) sel s E₀ β ε (J y) (X y)} =
      ({y | (X y).IsHermitian} ∩ {y | ∀ k l : Fin N,
        sel.eigenvalue (natDeformedH (F y).1 (X y)) k ∈ Icc (E₀ - h) (E₀ + h) →
        sel.eigenvalue (natDeformedH (F y).1 (X y)) l ∈ Icc (E₀ - h) (E₀ + h) →
        ‖CEH.sourceMatrixElement (J y) (sel.eigenvector (natDeformedH (F y).1 (X y)) k)
            (sel.eigenvector (natDeformedH (F y).1 (X y)) l) -
          (if k = l then nativeCentre (J y) (F y).1 s
            (sel.eigenvalue (natDeformedH (F y).1 (X y)) k) else 0)‖ ≤ tol})ᶜ := by
    ext y
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, NatWindowGood]
    constructor
    · intro hno ⟨hXh, hall⟩
      refine hno ⟨hXh, fun k l hk hl => ?_⟩
      rw [← natDeformedH_eq (F y) hXh] at hk hl ⊢
      exact hall k l hk hl
    · rintro hno ⟨hXh, hall⟩
      refine hno ⟨hXh, fun k l hk hl => ?_⟩
      rw [natDeformedH_eq (F y) hXh] at hk hl ⊢
      exact hall k l hk hl
  rw [e]
  have hXH : MeasurableSet {y | (X y).IsHermitian} :=
    (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet.preimage hX
  refine MeasurableSet.compl (hXH.inter ?_)
  refine measurableSet_setOfPred.mpr (Measurable.forall fun k => Measurable.forall fun l => ?_)
  have hwin : ∀ k : Fin N, Measurable fun y =>
      sel.eigenvalue (natDeformedH (F y).1 (X y)) k ∈ Icc (E₀ - h) (E₀ + h) :=
    fun k => measurableSet_setOfPred.mp
      (measurableSet_Icc.preimage ((sel.measurable_eigenvalue k).comp hD))
  refine (hwin k).imp ((hwin l).imp (measurableSet_setOfPred.mp ?_))
  refine measurableSet_le (continuous_norm.measurable.comp ?_) measurable_const
  refine (measurable_natOverlap_comp hJ (fun a => (sel.measurable_eigenvector k a).comp hD)
    (fun a => (sel.measurable_eigenvector l a).comp hD)).sub ?_
  by_cases hkl : k = l
  · simp only [hkl, ↓reduceIte]
    exact measurable_nativeCentre_comp hs hJ hF ((sel.measurable_eigenvalue l).comp hD)
      (fun y => (F y).2)
  · simp only [hkl, ↓reduceIte]
    exact measurable_const

end NatMeas

/-!
## The joint compressed bad set at a pole label
-/

section Joint

variable {p : Parameters} {i : ZMod p.n}

instance neZero_compressDim (p : Parameters) : NeZero (2 * p.W - 1) :=
  ⟨by have := p.W_pos; omega⟩

/-- **The joint compressed window bad set is measurable**: for a pole label `j₀`, an eigenpair
selection `sel` (giving the measurable compression `U(ω) = poleIsometry sel j₀ ω`), measurable
compressed data `F(ω)` (Hermitian on `Fin (2W - 1)`) and `J'(ω)`, the set
`{(ω, G) | ¬ NatWindowGood (F ω) sel' s' E₀ β ε (J' ω) (U(ω)* G U(ω))}` is measurable. Its
section at a fixed `ω` is the event bounded by `gue_not_compressWindowGood_le` with
`U = U(ω)`. -/
theorem measurableSet_not_compressWindowGood (sel : CEH.EigenpairSelection (2 * p.W))
    (j₀ : ExteriorSite p i) {F : SplitState p i → CEH.SourceHermitian (2 * p.W - 1)}
    (hF : Measurable fun om => (F om).1)
    {J : SplitState p i → Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ} (hJ : Measurable J)
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {s : ℝ} (hs : 0 < s) (E₀ β ε : ℝ) :
    MeasurableSet {x : SplitState p i × PairMatrix p i |
      ¬ NatWindowGood (F x.1) sel' s E₀ β ε (J x.1)
        ((poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1)} := by
  have hU : Measurable fun x : SplitState p i × PairMatrix p i => poleIsometry sel j₀ x.1 :=
    (measurable_poleIsometry sel j₀).comp measurable_fst
  have hX : Measurable fun x : SplitState p i × PairMatrix p i =>
      (poleIsometry sel j₀ x.1)ᴴ * x.2 * poleIsometry sel j₀ x.1 :=
    ProofCount.measurable_matrix_mul' (ProofCount.measurable_matrix_mul' (measurable_conjTranspose' hU) measurable_snd) hU
  have hF' : Measurable fun x : SplitState p i × PairMatrix p i => (F x.1).1 :=
    hF.comp measurable_fst
  have hJ' : Measurable fun x : SplitState p i × PairMatrix p i => J x.1 := hJ.comp measurable_fst
  exact measurableSet_not_natWindowGood_comp (F := fun x => F x.1) hF' hJ' hX sel' hs E₀ β ε

/-- The compressed matrix `U(ω)* M U(ω)` of a measurable pair matrix is measurable. -/
theorem measurable_poleCompress (sel : CEH.EigenpairSelection (2 * p.W)) (j₀ : ExteriorSite p i)
    {M : SplitState p i → PairMatrix p i} (hM : Measurable M) :
    Measurable fun om => (poleIsometry sel j₀ om)ᴴ * M om * poleIsometry sel j₀ om := by
  have hU := measurable_poleIsometry (p := p) (i := i) sel j₀
  exact ProofCount.measurable_matrix_mul' (ProofCount.measurable_matrix_mul' (measurable_conjTranspose' hU) hM) hU

end Joint

end BlockBand.LocalWindow.ProofPartTwo
