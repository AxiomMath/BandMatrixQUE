module

public import BlockBand.Angular.DetFactorGUE

/-!
# Orthonormal frames of `v^⊥`: frame independence and smooth Householder frames

Everything is finite-dimensional linear algebra in `ℂ^ι`, `card ι = m + 1`.
* `IsFrame U v`: `UᴴU = 1` and `Uᴴv = 0` (an orthonormal frame of `v^⊥`, `v ≠ 0`).
* `frame_mul_frame`: for two frames `U U'` of the same `v ≠ 0`, `U(UᴴU') = U'` and
  `W = UᴴU'` is unitary (completeness of `[U | v]`, `Matrix.mul_eq_one_comm_of_equiv`).
* `sectorMass_frame_indep`: `Z_ℓ(U'ᴴKU') = Z_ℓ(UᴴKU)` for Hermitian `K` (unitary invariance
  `DetFactor.sectorMass_unitary_conj`): the sector-mass formula is frame independent.
* `hhFrame j₀ e v`: the Householder frame on the patch `{v | v j₀ ≠ 0}`: with
  `w = v + (‖v‖/|v_{j₀}|) v_{j₀} e_{j₀}`, `H = I - 2ww*/‖w‖²`, the columns `H e_{e k}`,
  `e : Fin m ↪ ι \ {j₀}`. `isFrame_hhFrame`: it is a frame of `v`;
  `contDiffOn_hhMatrix_apply`: each entry of `H` is `C^n` on the open patch (every `n`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.DetFactor

open MeasureTheory Matrix Filter
open BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts
open scoped NNReal Topology ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-!
## Frames
-/

/-- `U` is an orthonormal frame of `v^⊥`: `UᴴU = 1`, `Uᴴv = 0`. -/
def IsFrame (U : Matrix ι (Fin m) ℂ) (v : ι → ℂ) : Prop := Uᴴ * U = 1 ∧ Uᴴ *ᵥ v = 0

theorem isFrame_smul {U : Matrix ι (Fin m) ℂ} {v : ι → ℂ} {c : ℂ} (hc : c ≠ 0) :
    IsFrame U (c • v) ↔ IsFrame U v := by
  unfold IsFrame
  rw [Matrix.mulVec_smul, smul_eq_zero, or_iff_right hc]

theorem isFrame_real_smul {U : Matrix ι (Fin m) ℂ} {v : ι → ℂ} {r : ℝ} (hr : r ≠ 0) :
    IsFrame U (r • v) ↔ IsFrame U v := by
  rw [show r • v = (r : ℂ) • v from (Complex.coe_smul r v).symm]
  exact isFrame_smul (by exact_mod_cast hr)

open scoped ComplexOrder in
/-- Completeness: two frames of the same nonzero `v` differ by `W = UᴴU'`: `U(UᴴU') = U'`. -/
theorem frame_mul_frame (hcard : Fintype.card ι = m + 1) {U U' : Matrix ι (Fin m) ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (hU : IsFrame U v) (hU' : IsFrame U' v) :
    U * (Uᴴ * U') = U' := by
  set c : ℂ := star v ⬝ᵥ v
  have hc : c ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.1 h)
  let V : Matrix ι (Fin m ⊕ Unit) ℂ := Matrix.of fun x j => Sum.elim (U x) (fun _ => v x) j
  let V' : Matrix ι (Fin m ⊕ Unit) ℂ :=
    Matrix.of fun x j => Sum.elim (U x) (fun _ => (star c)⁻¹ * v x) j
  have hUv : ∀ k, ∑ x, conj (U x k) * v x = 0 := fun k => by
    have := congrFun hU.2 k
    simpa [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply] using this
  have hU'v : ∀ k, ∑ x, star (v x) * U' x k = 0 := fun k => by
    have h := congrFun hU'.2 k
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply] at h
    have := congrArg star h
    rw [star_sum, star_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul', star_star, mul_comm]
  have hUU : ∀ k l, ∑ x, conj (U x k) * U x l = if k = l then 1 else 0 := fun k l => by
    have := congrFun (congrFun hU.1 k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using this
  have hVV : V'ᴴ * V = 1 := by
    ext j j'
    rcases j with k | _ <;> rcases j' with l | _
    · simp [V, V', Matrix.mul_apply, Matrix.conjTranspose_apply, hUU, Matrix.one_apply]
    · simp [V, V', Matrix.mul_apply, Matrix.conjTranspose_apply, hUv]
    · simp only [V, V', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Sum.elim_inl, Sum.elim_inr, Matrix.one_apply, reduceCtorEq, ite_false, star_mul',
        star_inv₀, star_star]
      have h := hUv l
      have h2 : ∑ x, c⁻¹ * star (v x) * U x l = c⁻¹ * star (∑ x, conj (U x l) * v x) := by
        rw [star_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [star_mul', ← Complex.star_def, star_star]; ring
      rw [h2, h, star_zero, mul_zero]
    · simp only [V, V', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Sum.elim_inr, Matrix.one_apply_eq, star_mul', star_inv₀, star_star]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hc
  have hcardS : Fintype.card (Fin m ⊕ Unit) = Fintype.card ι := by simp [hcard]
  have hVV' : V * V'ᴴ = 1 := (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcardS)).1 hVV
  have hU' : U' = V * (V'ᴴ * U') := by rw [← Matrix.mul_assoc, hVV', Matrix.one_mul]
  conv_rhs => rw [hU']
  ext x l
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, V, V', Matrix.of_apply, Sum.elim_inl,
    Sum.elim_inr, Matrix.conjTranspose_apply, Finset.univ_unique, Finset.sum_singleton,
    star_mul', star_inv₀, star_star]
  have h0 : ∑ y, c⁻¹ * star (v y) * U' y l = 0 := by
    simp_rw [mul_assoc]; rw [← Finset.mul_sum, hU'v, mul_zero]
  rw [h0, mul_zero, add_zero]

theorem frame_unitary (hcard : Fintype.card ι = m + 1) {U U' : Matrix ι (Fin m) ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (hU : IsFrame U v) (hU' : IsFrame U' v) :
    (Uᴴ * U')ᴴ * (Uᴴ * U') = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    frame_mul_frame hcard hv hU hU', hU'.1]

/-- **Frame independence**: `Z_ℓ(U'ᴴKU') = Z_ℓ(UᴴKU)` for two frames of `v ≠ 0`. -/
theorem sectorMass_frame_indep (hcard : Fintype.card ι = m + 1) (t : ℝ≥0)
    {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {U U' : Matrix ι (Fin m) ℂ} {v : ι → ℂ}
    (hv : v ≠ 0) (hU : IsFrame U v) (hU' : IsFrame U' v) (ℓ : ℕ) :
    sectorMass m t (U'ᴴ * K * U') ℓ = sectorMass m t (Uᴴ * K * U) ℓ := by
  have hW := frame_unitary hcard hv hU hU'
  have h : U'ᴴ * K * U' = (Uᴴ * U')ᴴ * (Uᴴ * K * U) * (Uᴴ * U') := by
    conv_lhs => rw [← frame_mul_frame hcard hv hU hU']
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [h, sectorMass_unitary_conj t (isHermitian_conjTranspose_mul_mul U hK) hW]

/-!
## Householder frames
-/

section Householder

variable (j₀ : ι) (e : Fin m → ι)

/-- The Householder vector `w = v + (‖v‖/|v_{j₀}|) v_{j₀} e_{j₀}`. -/
def hhVec (v : ι → ℂ) : ι → ℂ :=
  v + Pi.single j₀ (((CoareaPalm.l2Norm v / ‖v j₀‖ : ℝ) : ℂ) * v j₀)

/-- `‖w‖²`. -/
def hhNorm (v : ι → ℂ) : ℝ := ∑ x, ‖hhVec j₀ v x‖ ^ 2

/-- The Householder reflection `H = I - (2/‖w‖²) ww*`. -/
def hhMatrix (v : ι → ℂ) : Matrix ι ι ℂ :=
  1 - ((2 / hhNorm j₀ v : ℝ) : ℂ) • vecMulVec (hhVec j₀ v) (star (hhVec j₀ v))

/-- The Householder frame: the columns `H e_{e k}`. -/
def hhFrame (v : ι → ℂ) : Matrix ι (Fin m) ℂ := (hhMatrix j₀ v).submatrix id e

theorem star_dotProduct_self_eq (u : ι → ℂ) : star u ⬝ᵥ u = ((∑ x, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

theorem l2Norm_sq (u : ι → ℂ) : CoareaPalm.l2Norm u ^ 2 = ∑ x, ‖u x‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem l2Norm_pos_of_apply {v : ι → ℂ} (hv : v j₀ ≠ 0) : 0 < CoareaPalm.l2Norm v := by
  unfold CoareaPalm.l2Norm
  refine Real.sqrt_pos.2 (lt_of_lt_of_le (by positivity : 0 < ‖v j₀‖ ^ 2) ?_)
  exact Finset.single_le_sum (f := fun x => ‖v x‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j₀)

/-- `w* v = ρ(ρ + α)` and `‖w‖² = 2ρ(ρ + α)`, `ρ = ‖v‖`, `α = |v_{j₀}|`. -/
theorem hhVec_dot {v : ι → ℂ} (hv : v j₀ ≠ 0) :
    star (hhVec j₀ v) ⬝ᵥ v = ((CoareaPalm.l2Norm v * (CoareaPalm.l2Norm v + ‖v j₀‖) : ℝ) : ℂ) ∧
      hhNorm j₀ v = 2 * (CoareaPalm.l2Norm v * (CoareaPalm.l2Norm v + ‖v j₀‖)) := by
  set ρ := CoareaPalm.l2Norm v
  set α := ‖v j₀‖
  have hα : 0 < α := norm_pos_iff.2 hv
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  set s : ℂ := ((ρ / α : ℝ) : ℂ) * v j₀
  have hρ2 : star v ⬝ᵥ v = ((ρ ^ 2 : ℝ) : ℂ) := by rw [star_dotProduct_self_eq, l2Norm_sq]
  have hcv : star (v j₀) * v j₀ = ((α ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.conj_mul']; push_cast; rfl
  have hsv : star s * v j₀ = ((ρ * α : ℝ) : ℂ) := by
    simp only [s, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [mul_assoc, ← Complex.star_def, hcv]
    push_cast
    field_simp
  have hss : star s * s = ((ρ ^ 2 : ℝ) : ℂ) := by
    simp only [s, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [show ((ρ / α : ℝ) : ℂ) * (starRingEnd ℂ) (v j₀) * (((ρ / α : ℝ) : ℂ) * v j₀) =
      ((ρ / α : ℝ) : ℂ) ^ 2 * (star (v j₀) * v j₀) by rw [Complex.star_def]; ring, hcv]
    push_cast
    field_simp
  have h1 : star (hhVec j₀ v) ⬝ᵥ v = ((ρ * (ρ + α) : ℝ) : ℂ) := by
    simp only [hhVec, star_add, add_dotProduct, ← Pi.single_star, single_dotProduct]
    rw [hρ2, hsv]
    push_cast; ring
  refine ⟨h1, ?_⟩
  have h2 : star (hhVec j₀ v) ⬝ᵥ hhVec j₀ v = ((2 * (ρ * (ρ + α)) : ℝ) : ℂ) := by
    rw [show hhVec j₀ v = v + Pi.single j₀ s from rfl, dotProduct_add, ← show hhVec j₀ v =
      v + Pi.single j₀ s from rfl, h1]
    simp only [hhVec, dotProduct_single, Pi.star_apply, Pi.add_apply, Pi.single_eq_same,
      star_add]
    have hvs : star (v j₀) * s = ((ρ * α : ℝ) : ℂ) := by
      rw [show star (v j₀) * s = star (star s * v j₀) by rw [star_mul', star_star, mul_comm],
        hsv, Complex.star_def, Complex.conj_ofReal]
    change _ + (star (v j₀) + star s) * s = _
    rw [add_mul, hvs, hss]
    push_cast; ring
  rw [star_dotProduct_self_eq] at h2
  exact_mod_cast h2

theorem hhNorm_pos {v : ι → ℂ} (hv : v j₀ ≠ 0) : 0 < hhNorm j₀ v := by
  rw [(hhVec_dot j₀ hv).2]
  have := l2Norm_pos_of_apply j₀ hv
  have : 0 < ‖v j₀‖ := norm_pos_iff.2 hv
  positivity

theorem hhMatrix_conjTranspose (v : ι → ℂ) : (hhMatrix j₀ v)ᴴ = hhMatrix j₀ v := by
  unfold hhMatrix
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_vecMulVec, star_star]
  simp [Complex.conj_ofReal]

theorem hhMatrix_mul_self {v : ι → ℂ} (hv : v j₀ ≠ 0) : hhMatrix j₀ v * hhMatrix j₀ v = 1 := by
  have hn := hhNorm_pos j₀ hv
  unfold hhMatrix
  set w := hhVec j₀ v
  have hww : star w ⬝ᵥ w = ((hhNorm j₀ v : ℝ) : ℂ) := star_dotProduct_self_eq w
  set r : ℂ := ((2 / hhNorm j₀ v : ℝ) : ℂ)
  have hr : r * r * ((hhNorm j₀ v : ℝ) : ℂ) = 2 * r := by
    simp only [r]; push_cast
    have : (hhNorm j₀ v : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_vecMulVec, hww, smul_smul]
  rw [vecMulVec_smul, smul_smul, hr, two_mul, add_smul]
  abel

theorem hhMatrix_mulVec {v : ι → ℂ} (hv : v j₀ ≠ 0) :
    hhMatrix j₀ v *ᵥ v = -Pi.single j₀ (((CoareaPalm.l2Norm v / ‖v j₀‖ : ℝ) : ℂ) * v j₀) := by
  have hd := hhVec_dot j₀ hv
  have hρ := l2Norm_pos_of_apply j₀ hv
  have hα : 0 < ‖v j₀‖ := norm_pos_iff.2 hv
  have hc : ((CoareaPalm.l2Norm v * (CoareaPalm.l2Norm v + ‖v j₀‖) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < CoareaPalm.l2Norm v * (CoareaPalm.l2Norm v + ‖v j₀‖)).ne'
  have hsc : ((2 / hhNorm j₀ v : ℝ) : ℂ) *
      ((CoareaPalm.l2Norm v * (CoareaPalm.l2Norm v + ‖v j₀‖) : ℝ) : ℂ) = 1 := by
    rw [hd.2]; push_cast at hc ⊢; field_simp; exact div_self hc
  unfold hhMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, hd.1]
  ext x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, Pi.neg_apply, hhVec, Pi.add_apply]
  rw [mul_comm (v x + _), ← mul_assoc, hsc, one_mul]
  ring

/-- **The Householder frame is an orthonormal frame of `v^⊥`** on the patch `v j₀ ≠ 0`. -/
theorem isFrame_hhFrame (he : Function.Injective e) (hne : ∀ k, e k ≠ j₀) {v : ι → ℂ}
    (hv : v j₀ ≠ 0) : IsFrame (hhFrame j₀ e v) v := by
  constructor
  · unfold hhFrame
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ e id e Function.bijective_id,
      hhMatrix_conjTranspose, hhMatrix_mul_self j₀ hv]
    ext k l
    simp [Matrix.one_apply, he.eq_iff]
  · ext k
    change ((hhMatrix j₀ v)ᴴ *ᵥ v) (e k) = 0
    rw [hhMatrix_conjTranspose, hhMatrix_mulVec j₀ hv]
    simp [hne k]

/-- The patch `{v | v j₀ ≠ 0}`. -/
def patch : Set (ι → ℂ) := {v | v j₀ ≠ 0}

theorem isOpen_patch : IsOpen (patch j₀) :=
  isOpen_ne_fun (continuous_apply j₀) continuous_const

variable {n : WithTop ℕ∞}

theorem contDiffOn_l2Norm : ContDiffOn ℝ n (fun v : ι → ℂ => CoareaPalm.l2Norm v) (patch j₀) := by
  unfold CoareaPalm.l2Norm
  refine ContDiffOn.sqrt (ContDiff.contDiffOn ?_) fun v hv => ?_
  · exact ContDiff.sum fun x _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ x)
  · have h := l2Norm_pos_of_apply j₀ (v := v) hv
    unfold CoareaPalm.l2Norm at h
    exact (Real.sqrt_pos.1 h).ne'

theorem contDiffOn_norm_apply : ContDiffOn ℝ n (fun v : ι → ℂ => ‖v j₀‖) (patch j₀) :=
  fun v hv => (ContDiffAt.norm ℝ (contDiffAt_apply ℝ ℂ j₀ v) hv).contDiffWithinAt

theorem contDiffOn_ofReal {f : (ι → ℂ) → ℝ} {s : Set (ι → ℂ)} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun v => (f v : ℂ)) s :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

theorem contDiffOn_conj {f : (ι → ℂ) → ℂ} {s : Set (ι → ℂ)} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun v => conj (f v)) s :=
  Complex.conjCLE.contDiff.comp_contDiffOn hf

theorem contDiffOn_hhVec_apply (x : ι) :
    ContDiffOn ℝ n (fun v => hhVec j₀ v x) (patch j₀) := by
  have hc : ContDiffOn ℝ n (fun v : ι → ℂ => CoareaPalm.l2Norm v / ‖v j₀‖) (patch j₀) :=
    (contDiffOn_l2Norm j₀).div (contDiffOn_norm_apply j₀) fun v hv => norm_ne_zero_iff.2 hv
  have hv : ∀ y : ι, ContDiffOn ℝ n (fun v : ι → ℂ => v y) (patch j₀) := fun y =>
    (contDiff_apply ℝ ℂ y).contDiffOn
  unfold hhVec
  by_cases hx : x = j₀
  · subst hx
    simp only [Pi.add_apply, Pi.single_eq_same]
    exact (hv x).add ((contDiffOn_ofReal hc).mul (hv x))
  · simp only [Pi.add_apply, Pi.single_apply, hx, ite_false, add_zero]
    exact hv x

theorem contDiffOn_hhNorm : ContDiffOn ℝ n (fun v => hhNorm j₀ v) (patch j₀) := by
  unfold hhNorm
  exact ContDiffOn.sum fun x _ => (contDiff_norm_sq ℝ).comp_contDiffOn (contDiffOn_hhVec_apply j₀ x)

theorem contDiffOn_hhMatrix_apply (x y : ι) :
    ContDiffOn ℝ n (fun v => hhMatrix j₀ v x y) (patch j₀) := by
  have hr : ContDiffOn ℝ n (fun v => 2 / hhNorm j₀ v) (patch j₀) :=
    contDiffOn_const.div (contDiffOn_hhNorm j₀) fun v hv => (hhNorm_pos j₀ hv).ne'
  unfold hhMatrix
  simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    Complex.star_def]
  exact contDiffOn_const.sub ((contDiffOn_ofReal hr).mul
    ((contDiffOn_hhVec_apply j₀ x).mul (contDiffOn_conj (contDiffOn_hhVec_apply j₀ y))))

/-- Each entry of the compressed matrix `U_vᴴ K U_v` (Householder frame) is `C^n` on the patch. -/
theorem contDiffOn_hhCompress_apply (K : Matrix ι ι ℂ) (a b : Fin m) :
    ContDiffOn ℝ n (fun v => ((hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v) a b) (patch j₀) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hhFrame, Matrix.submatrix_apply,
    id, Complex.star_def]
  exact ContDiffOn.sum fun y _ => (ContDiffOn.sum fun x _ =>
    (contDiffOn_conj (contDiffOn_hhMatrix_apply j₀ x (e a))).mul contDiffOn_const).mul
    (contDiffOn_hhMatrix_apply j₀ y (e b))

/-- The Hermitian coordinates of `U_vᴴ K U_v` are `C^n` on the patch. -/
theorem contDiffOn_coord_hhCompress (K : Matrix ι ι ℂ) :
    ContDiffOn ℝ n (fun v => coordOfMatrix ((hhFrame j₀ e v)ᴴ * K * hhFrame j₀ e v))
      (patch j₀) := by
  refine contDiffOn_pi.2 fun c => ?_
  unfold coordOfMatrix
  split_ifs
  · exact Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_hhCompress_apply j₀ e K _ _)
  · exact Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_hhCompress_apply j₀ e K _ _)
  · exact Complex.imCLM.contDiff.comp_contDiffOn (contDiffOn_hhCompress_apply j₀ e K _ _)

end Householder

/-- Column embeddings avoiding `j₀` exist when `card ι = m + 1`. -/
theorem exists_frameEmbedding (hcard : Fintype.card ι = m + 1) (j₀ : ι) :
    ∃ e : Fin m → ι, Function.Injective e ∧ ∀ k, e k ≠ j₀ := by
  have h : Fintype.card {x : ι // ¬ x = j₀} = m := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]; rfl
  let f := Fintype.equivOfCardEq (h.trans (Fintype.card_fin m).symm)
  exact ⟨fun k => (f.symm k).1, fun a b hab => f.symm.injective (Subtype.ext hab),
    fun k => (f.symm k).2⟩

/-- Every nonzero `v` has an orthonormal frame of `v^⊥` (`card ι = m + 1`). -/
theorem exists_isFrame (hcard : Fintype.card ι = m + 1) {v : ι → ℂ} (hv : v ≠ 0) :
    ∃ U : Matrix ι (Fin m) ℂ, IsFrame U v := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, v j₀ ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  obtain ⟨e, he, hne⟩ := exists_frameEmbedding hcard j₀
  exact ⟨hhFrame j₀ e v, isFrame_hhFrame j₀ e he hne hj₀⟩

end BlockBand.Angular.DetFactor
