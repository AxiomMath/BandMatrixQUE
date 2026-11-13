module

public import BlockBand.Critical.RelativeVectors.Angular.Selection

/-!
# The angular generator and phase invariance under label reversal

The relabelling `R Z = (Z_{ℓ.rev})_ℓ` is a real linear isometry of `ℂ^{N×r}` (sup norm). For every
`g` (no regularity needed):

* `fderiv_comp_relabel`, `fderiv_fderiv_comp_relabel`: `D(g ∘ R)(Z) = Dg(RZ) ∘ R` and
  `D²(g ∘ R)(Z)[W₁, W₂] = D²g(RZ)[RW₁, RW₂]`;
* `contractGenerator_comp_relabel`: `TransmissionAngular.complexAngularGenerator` with couplings
  `lam' i = lam i.rev`, applied to `g ∘ R` at `Z`, equals `RelativeVectors.complexAngularGenerator`
  with couplings `lam` applied to `g` at `RZ` (the pair term is symmetric: `X_ba = -X_ab`,
  `Y_ba = Y_ab`, `c_ab = c_ba`);
* `contractGenerator_const_mul`: linearity in a scalar factor, for `C²` tests;
* `isPhaseInvariant_const_mul_comp_relabel`: label-phase invariance is preserved by `c · g ∘ R`;
* derivative bounds of `c · g ∘ R`, and the bound `abs_complexAngularGenerator_le` of the generator
  by `N² M C (‖z‖² + ‖z‖)` when the couplings are in `[0, M]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open Matrix Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N r : ℕ}

/-- The array space `ℂ^{N×r}`. -/
abbrev Arr (N r : ℕ) : Type := Fin N → Fin r → ℂ

/-!
## The relabelling as a continuous linear equivalence
-/

/-- `R` as a real linear equivalence (an involution). -/
def relabelLinear (N r : ℕ) : (Arr N r) ≃ₗ[ℝ] (Arr N r) where
  toFun := relabelArray
  invFun := relabelArray
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv Z := relabelArray_relabelArray Z
  right_inv Z := relabelArray_relabelArray Z

/-- `R` as a continuous linear equivalence. -/
def relabelCLE (N r : ℕ) : (Arr N r) ≃L[ℝ] (Arr N r) :=
  (relabelLinear N r).toContinuousLinearEquiv

@[simp] theorem relabelCLE_apply (Z : Arr N r) : relabelCLE N r Z = relabelArray Z := rfl

theorem norm_relabelArray_le (Z : Arr N r) : ‖relabelArray Z‖ ≤ ‖Z‖ :=
  pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun ℓ => norm_le_pi_norm Z ℓ.rev

theorem norm_relabelArray (Z : Arr N r) : ‖relabelArray Z‖ = ‖Z‖ :=
  le_antisymm (norm_relabelArray_le Z) (by
    simpa using norm_relabelArray_le (relabelArray Z))

theorem norm_relabelCLE_le : ‖(relabelCLE N r : (Arr N r) →L[ℝ] (Arr N r))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun Z => by
    simpa using norm_relabelArray_le Z

/-!
## Derivatives of `g ∘ R`
-/

theorem fderiv_comp_relabel_clm (g : (Arr N r) → ℝ) (Z : Arr N r) :
    fderiv ℝ (fun Z => g (relabelArray Z)) Z =
      (fderiv ℝ g (relabelArray Z)).comp (relabelCLE N r : (Arr N r) →L[ℝ] (Arr N r)) :=
  (relabelCLE N r).comp_right_fderiv (f := g)

theorem fderiv_comp_relabel (g : (Arr N r) → ℝ) (Z W : Arr N r) :
    fderiv ℝ (fun Z => g (relabelArray Z)) Z W =
      fderiv ℝ g (relabelArray Z) (relabelArray W) := by
  rw [fderiv_comp_relabel_clm]; rfl

/-- Precomposition with `R` on linear forms, as a continuous linear equivalence. -/
def precompRelabel (N r : ℕ) : ((Arr N r) →L[ℝ] ℝ) ≃L[ℝ] ((Arr N r) →L[ℝ] ℝ) :=
  (relabelCLE N r).symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem precompRelabel_apply (L : (Arr N r) →L[ℝ] ℝ) :
    precompRelabel N r L = L.comp (relabelCLE N r : (Arr N r) →L[ℝ] (Arr N r)) := by
  ext W; rfl

theorem fderiv_fderiv_comp_relabel_clm (g : (Arr N r) → ℝ) (Z W : Arr N r) :
    fderiv ℝ (fderiv ℝ (fun Z => g (relabelArray Z))) Z W =
      (fderiv ℝ (fderiv ℝ g) (relabelArray Z) (relabelArray W)).comp
        (relabelCLE N r : (Arr N r) →L[ℝ] (Arr N r)) := by
  have h1 : fderiv ℝ (fun Z => g (relabelArray Z)) =
      (precompRelabel N r) ∘ (fun Z => fderiv ℝ g (relabelCLE N r Z)) := by
    funext Z
    rw [fderiv_comp_relabel_clm, Function.comp_apply, precompRelabel_apply]; rfl
  have h2 : (fun Z => fderiv ℝ g (relabelCLE N r Z)) = fderiv ℝ g ∘ (relabelCLE N r) := rfl
  rw [h1, (precompRelabel N r).comp_fderiv, h2,
    (relabelCLE N r).comp_right_fderiv (f := fderiv ℝ g)]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [precompRelabel_apply]
  rfl

theorem fderiv_fderiv_comp_relabel (g : (Arr N r) → ℝ) (Z W₁ W₂ : Arr N r) :
    fderiv ℝ (fderiv ℝ (fun Z => g (relabelArray Z))) Z W₁ W₂ =
      fderiv ℝ (fderiv ℝ g) (relabelArray Z) (relabelArray W₁) (relabelArray W₂) := by
  rw [fderiv_fderiv_comp_relabel_clm]; rfl

theorem norm_fderiv_comp_relabel_le (g : (Arr N r) → ℝ) (Z : Arr N r) :
    ‖fderiv ℝ (fun Z => g (relabelArray Z)) Z‖ ≤ ‖fderiv ℝ g (relabelArray Z)‖ := by
  rw [fderiv_comp_relabel_clm]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) norm_relabelCLE_le)

theorem norm_fderiv_fderiv_comp_relabel_le (g : (Arr N r) → ℝ) (Z : Arr N r) :
    ‖fderiv ℝ (fderiv ℝ (fun Z => g (relabelArray Z))) Z‖ ≤
      ‖fderiv ℝ (fderiv ℝ g) (relabelArray Z)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (norm_nonneg (fderiv ℝ (fderiv ℝ g) (relabelArray Z))) fun W => ?_
  rw [fderiv_fderiv_comp_relabel_clm]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) norm_relabelCLE_le).trans ?_
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_relabelArray_le W) (norm_nonneg _)

/-!
## The rotation fields under relabelling
-/

theorem relabel_pairRotX (i j : Fin N) (Z : Arr N r) :
    relabelArray (BlockBand.Internal.Contracts.TransmissionAngular.pairRotX i j Z) =
      rotX i.rev j.rev (relabelArray Z) := by
  funext k
  simp only [relabelArray, BlockBand.Internal.Contracts.TransmissionAngular.pairRotX, rotX,
    Fin.rev_rev]
  by_cases hi : k.rev = i
  · have : k = i.rev := by rw [← hi, Fin.rev_rev]
    subst this; simp
  · have hi' : k ≠ i.rev := fun e => hi (by rw [e, Fin.rev_rev])
    by_cases hj : k.rev = j
    · have : k = j.rev := by rw [← hj, Fin.rev_rev]
      have hji : j ≠ i := fun e => hi' (by rw [this, e])
      subst this; simp [hji]
    · have hj' : k ≠ j.rev := fun e => hj (by rw [e, Fin.rev_rev])
      simp [hi, hi', hj, hj']

theorem relabel_pairRotY (i j : Fin N) (Z : Arr N r) :
    relabelArray (BlockBand.Internal.Contracts.TransmissionAngular.pairRotY i j Z) =
      rotY i.rev j.rev (relabelArray Z) := by
  funext k
  simp only [relabelArray, BlockBand.Internal.Contracts.TransmissionAngular.pairRotY, rotY,
    Fin.rev_rev]
  by_cases hi : k.rev = i
  · have : k = i.rev := by rw [← hi, Fin.rev_rev]
    subst this; simp
  · have hi' : k ≠ i.rev := fun e => hi (by rw [e, Fin.rev_rev])
    by_cases hj : k.rev = j
    · have : k = j.rev := by rw [← hj, Fin.rev_rev]
      have hji : j ≠ i := fun e => hi' (by rw [this, e])
      subst this; simp [hji]
    · have hj' : k ≠ j.rev := fun e => hj (by rw [e, Fin.rev_rev])
      simp [hi, hi', hj, hj']

theorem rotX_swap {a b : Fin N} (hab : a ≠ b) (z : Arr N r) : rotX b a z = -rotX a b z := by
  funext k
  by_cases ha : k = a
  · subst ha; simp [rotX, hab]
  · by_cases hb : k = b
    · subst hb; simp [rotX, Ne.symm hab]
    · simp [rotX, ha, hb]

theorem rotY_swap {a b : Fin N} (hab : a ≠ b) (z : Arr N r) : rotY b a z = rotY a b z := by
  funext k
  by_cases ha : k = a
  · subst ha; simp [rotY, hab]
  · by_cases hb : k = b
    · subst hb; simp [rotY, Ne.symm hab]
    · simp [rotY, ha, hb]

theorem rotX_neg (a b : Fin N) (z : Arr N r) : rotX a b (-z) = -rotX a b z := by
  funext k; simp only [rotX, Pi.neg_apply]; split_ifs <;> simp

theorem fieldSq_rotX_swap {a b : Fin N} (hab : a ≠ b) (g : (Arr N r) → ℝ) (z : Arr N r) :
    fieldSq (rotX b a) g z = fieldSq (rotX a b) g z := by
  simp [fieldSq, rotX_swap hab, rotX_neg]

theorem fieldSq_rotY_swap {a b : Fin N} (hab : a ≠ b) (g : (Arr N r) → ℝ) (z : Arr N r) :
    fieldSq (rotY b a) g z = fieldSq (rotY a b) g z := by
  simp only [fieldSq]
  rw [rotY_swap hab, rotY_swap hab]

theorem dysonCoupling_symm (lam : Fin N → ℝ) (a b : Fin N) :
    dysonCoupling N lam a b = dysonCoupling N lam b a := by
  unfold dysonCoupling; ring

/-- Sum over ordered pairs `i < j` of `P (i.rev) (j.rev)` equals the sum of `P i j`, for `P`
symmetric. -/
theorem sum_pairs_rev (P : Fin N → Fin N → ℝ) (hP : ∀ a b, a ≠ b → P a b = P b a) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), P i.rev j.rev =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j), P i j := by
  simp only [Finset.sum_filter]
  have h1 : ∑ i : Fin N, ∑ j : Fin N, (if i < j then P i.rev j.rev else 0) =
      ∑ a : Fin N, ∑ b : Fin N, (if b < a then P a b else 0) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Fintype.sum_congr _ _ fun a => ?_
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Fintype.sum_congr _ _ fun b => ?_
    simp [Fin.rev_lt_rev]
  rw [h1, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun b => Fintype.sum_congr _ _ fun a => ?_
  split_ifs with h
  · exact hP a b (ne_of_gt h)
  · rfl

/-- `TransmissionAngular.complexAngularGenerator` of `g ∘ R` with couplings `lam' = lam ∘ rev` is
`RelativeVectors.complexAngularGenerator` of `g` at `RZ` with couplings `lam`. -/
theorem contractGenerator_comp_relabel (lam : Fin N → ℝ) (g : (Arr N r) → ℝ) (Z : Arr N r) :
    BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator N r
        (fun i => lam i.rev) (fun Z => g (relabelArray Z)) Z =
      complexAngularGenerator N r lam g (relabelArray Z) := by
  unfold BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator
    complexAngularGenerator
  congr 1
  have hterm : ∀ i j : Fin N,
      dysonCoupling N (fun i => lam i.rev) i j *
        (fderiv ℝ (fderiv ℝ (fun Z => g (relabelArray Z))) Z
            (BlockBand.Internal.Contracts.TransmissionAngular.pairRotX i j Z)
            (BlockBand.Internal.Contracts.TransmissionAngular.pairRotX i j Z) +
          fderiv ℝ (fun Z => g (relabelArray Z)) Z
            (BlockBand.Internal.Contracts.TransmissionAngular.pairRotX i j
              (BlockBand.Internal.Contracts.TransmissionAngular.pairRotX i j Z)) +
          fderiv ℝ (fderiv ℝ (fun Z => g (relabelArray Z))) Z
            (BlockBand.Internal.Contracts.TransmissionAngular.pairRotY i j Z)
            (BlockBand.Internal.Contracts.TransmissionAngular.pairRotY i j Z) +
          fderiv ℝ (fun Z => g (relabelArray Z)) Z
            (BlockBand.Internal.Contracts.TransmissionAngular.pairRotY i j
              (BlockBand.Internal.Contracts.TransmissionAngular.pairRotY i j Z))) =
      dysonCoupling N lam i.rev j.rev *
        (fieldSq (rotX i.rev j.rev) g (relabelArray Z) +
          fieldSq (rotY i.rev j.rev) g (relabelArray Z)) := by
    intro i j
    simp only [fderiv_fderiv_comp_relabel, fderiv_comp_relabel, relabel_pairRotX,
      relabel_pairRotY, fieldSq]
    unfold dysonCoupling
    ring
  simp_rw [hterm]
  refine sum_pairs_rev (fun a b => dysonCoupling N lam a b *
    (fieldSq (rotX a b) g (relabelArray Z) + fieldSq (rotY a b) g (relabelArray Z))) ?_
  intro a b hab
  rw [dysonCoupling_symm, fieldSq_rotX_swap hab.symm, fieldSq_rotY_swap hab.symm]

/-!
## Scalar factors
-/

theorem differentiable_fderiv_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)

theorem fderiv_const_mul_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) :
    fderiv ℝ (fun Z => c * f Z) = fun Z => c • fderiv ℝ f Z := by
  funext Z
  exact fderiv_const_mul ((hf.differentiable (by simp)) Z) c

theorem fderiv_fderiv_const_mul_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun Z => c * f Z)) = fun Z => c • fderiv ℝ (fderiv ℝ f) Z := by
  rw [fderiv_const_mul_fun hf]
  funext Z
  exact fderiv_const_smul ((differentiable_fderiv_of_contDiff hf) Z) c

/-- The generator is linear in a scalar factor of a `C²` test. -/
theorem contractGenerator_const_mul (lam : Fin N → ℝ) {f : (Arr N r) → ℝ} (hf : ContDiff ℝ 2 f)
    (c : ℝ) (Z : Arr N r) :
    BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator N r lam
        (fun Z => c * f Z) Z =
      c * BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator N r lam f Z := by
  unfold BlockBand.Internal.Contracts.TransmissionAngular.complexAngularGenerator
  rw [fderiv_fderiv_const_mul_fun hf, fderiv_const_mul_fun hf]
  simp only [_root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem contDiff_const_mul_comp_relabel {g : (Arr N r) → ℝ} (hg : ContDiff ℝ 2 g) (c : ℝ) :
    ContDiff ℝ 2 (fun Z => c * g (relabelArray Z)) :=
  contDiff_const.mul (hg.comp (relabelCLE N r).contDiff)

theorem norm_fderiv_const_mul_comp_relabel_le {g : (Arr N r) → ℝ} (hg : ContDiff ℝ 2 g)
    (c : ℝ) (Z : Arr N r) :
    ‖fderiv ℝ (fun Z => c * g (relabelArray Z)) Z‖ ≤ |c| * ‖fderiv ℝ g (relabelArray Z)‖ := by
  have hg' : ContDiff ℝ 2 (fun Z => g (relabelArray Z)) := hg.comp (relabelCLE N r).contDiff
  rw [fderiv_const_mul_fun hg' c]
  refine (norm_smul_le c (fderiv ℝ (fun Z => g (relabelArray Z)) Z)).trans ?_
  rw [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_fderiv_comp_relabel_le g Z) (abs_nonneg c)

theorem norm_fderiv_fderiv_const_mul_comp_relabel_le {g : (Arr N r) → ℝ} (hg : ContDiff ℝ 2 g)
    (c : ℝ) (Z : Arr N r) :
    ‖fderiv ℝ (fderiv ℝ (fun Z => c * g (relabelArray Z))) Z‖ ≤
      |c| * ‖fderiv ℝ (fderiv ℝ g) (relabelArray Z)‖ := by
  have hg' : ContDiff ℝ 2 (fun Z => g (relabelArray Z)) := hg.comp (relabelCLE N r).contDiff
  rw [fderiv_fderiv_const_mul_fun hg' c]
  refine (ContinuousLinearMap.opNorm_smul_le c
    (fderiv ℝ (fderiv ℝ (fun Z => g (relabelArray Z))) Z)).trans ?_
  rw [Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_fderiv_fderiv_comp_relabel_le g Z) (abs_nonneg c)

/-!
## Phase invariance
-/

/-- Label-phase invariance of `g` (real angles) gives the phase invariance (unimodular multipliers)
of `c · g ∘ R`. -/
theorem isPhaseInvariant_const_mul_comp_relabel {g : (Arr N r) → ℝ}
    (hg : IsLabelPhaseInvariant g) (c : ℝ) :
    BlockBand.Internal.Contracts.TransmissionAngular.IsPhaseInvariant
      (fun Z => c * g (relabelArray Z)) := by
  intro θ hθ Z
  have e : relabelArray (fun i a => θ i * Z i a) =
      fun ℓ => Complex.exp (((Complex.arg (θ ℓ.rev) : ℝ) : ℂ) * Complex.I) •
        relabelArray Z ℓ := by
    funext ℓ a
    have h1 := Complex.norm_mul_exp_arg_mul_I (θ ℓ.rev)
    rw [hθ ℓ.rev] at h1
    simp only [relabelArray, Pi.smul_apply, smul_eq_mul]
    rw [Complex.ofReal_one, one_mul] at h1
    rw [h1]
  simp only
  rw [e, hg]

/-!
## Bounds on the rotation fields and on the generator
-/

theorem norm_rotX_le (i j : Fin N) (z : Arr N r) : ‖rotX i j z‖ ≤ ‖z‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun k => ?_
  simp only [rotX]
  split_ifs
  · exact norm_le_pi_norm z j
  · rw [norm_neg]; exact norm_le_pi_norm z i
  · simp

theorem norm_rotY_le (i j : Fin N) (z : Arr N r) : ‖rotY i j z‖ ≤ ‖z‖ := by
  refine pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun k => ?_
  simp only [rotY]
  split_ifs
  · rw [norm_smul, Complex.norm_I, one_mul]; exact norm_le_pi_norm z j
  · rw [norm_smul, Complex.norm_I, one_mul]; exact norm_le_pi_norm z i
  · simp

theorem abs_fieldSq_le (W : (Arr N r) → (Arr N r)) (hW : ∀ z, ‖W z‖ ≤ ‖z‖)
    (g : (Arr N r) → ℝ) (z : Arr N r) {C : ℝ} (h1 : ‖fderiv ℝ g z‖ ≤ C)
    (h2 : ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ C) : |fieldSq W g z| ≤ C * (‖z‖ ^ 2 + ‖z‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans h1
  unfold fieldSq
  have a1 : |fderiv ℝ (fderiv ℝ g) z (W z) (W z)| ≤ C * ‖z‖ ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ g) z (W z) (W z)‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) z‖ * ‖W z‖ * ‖W z‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ C * ‖z‖ * ‖z‖ := by
          gcongr
          · exact hW z
          · exact hW z
      _ = C * ‖z‖ ^ 2 := by ring
  have a2 : |fderiv ℝ g z (W (W z))| ≤ C * ‖z‖ := by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ g z (W (W z))‖ ≤ ‖fderiv ℝ g z‖ * ‖W (W z)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖z‖ := by
          gcongr
          exact (hW _).trans (hW z)
  calc |fderiv ℝ (fderiv ℝ g) z (W z) (W z) + fderiv ℝ g z (W (W z))|
      ≤ |fderiv ℝ (fderiv ℝ g) z (W z) (W z)| + |fderiv ℝ g z (W (W z))| := abs_add_le _ _
    _ ≤ C * ‖z‖ ^ 2 + C * ‖z‖ := add_le_add a1 a2
    _ = C * (‖z‖ ^ 2 + ‖z‖) := by ring

/-- The generator is bounded by `N² M C (‖z‖² + ‖z‖)` when the couplings of the ordered pairs
are in `[0, M]` and `‖Dg(z)‖, ‖D²g(z)‖ ≤ C`. -/
theorem abs_complexAngularGenerator_le (lam : Fin N → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i j : Fin N, i < j → 0 ≤ dysonCoupling N lam i j ∧ dysonCoupling N lam i j ≤ M)
    (g : (Arr N r) → ℝ) (z : Arr N r) {C : ℝ} (h1 : ‖fderiv ℝ g z‖ ≤ C)
    (h2 : ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ C) :
    |complexAngularGenerator N r lam g z| ≤ (N : ℝ) ^ 2 * M * C * (‖z‖ ^ 2 + ‖z‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans h1
  set B : ℝ := M * (2 * (C * (‖z‖ ^ 2 + ‖z‖))) with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ i, ∀ j ∈ Finset.univ.filter (fun j => i < j),
      |dysonCoupling N lam i j * (fieldSq (rotX i j) g z + fieldSq (rotY i j) g z)| ≤ B := by
    intro i j hj
    have hij := (Finset.mem_filter.1 hj).2
    obtain ⟨c0, cM⟩ := hM i j hij
    rw [abs_mul, abs_of_nonneg c0]
    refine mul_le_mul cM ?_ (abs_nonneg _) hM0
    refine (abs_add_le _ _).trans ?_
    have := abs_fieldSq_le (rotX i j) (norm_rotX_le i j) g z h1 h2
    have := abs_fieldSq_le (rotY i j) (norm_rotY_le i j) g z h1 h2
    linarith
  unfold complexAngularGenerator
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hS : |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      dysonCoupling N lam i j * (fieldSq (rotX i j) g z + fieldSq (rotY i j) g z)| ≤
      (N : ℝ) * ((N : ℝ) * B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ i : Fin N, |∑ j ∈ Finset.univ.filter (fun j => i < j),
        dysonCoupling N lam i j * (fieldSq (rotX i j) g z + fieldSq (rotY i j) g z)| ≤
        (N : ℝ) * B := by
      intro i
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum (hterm i)).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.filter (fun j => i < j)).card : ℝ) ≤ N := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      exact mul_le_mul_of_nonneg_right hc hB0
    refine (Finset.sum_le_sum fun i _ => hrow i).trans ?_
    simp
  calc 1 / 4 * |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        dysonCoupling N lam i j * (fieldSq (rotX i j) g z + fieldSq (rotY i j) g z)|
      ≤ 1 / 4 * ((N : ℝ) * ((N : ℝ) * B)) := by gcongr
    _ ≤ (N : ℝ) ^ 2 * M * C * (‖z‖ ^ 2 + ‖z‖) := by
      rw [hB]
      have : 0 ≤ (N : ℝ) ^ 2 * M * C * (‖z‖ ^ 2 + ‖z‖) := by positivity
      nlinarith

end BlockBand.Critical.RelativeVectors.Angular
