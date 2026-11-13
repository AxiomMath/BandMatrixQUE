module

public import BlockBand.Angular.RatioBounds

/-!
# The tangent field of the angular ratio lemma and its pairings

The field `Y = Γ∇h - v Re(v*Γ∇h)`, `∇h = Dv/h`, `D = 𝓛ᴴ𝓛`, is represented by the
degree-zero coefficient `c = ‖v‖/‖𝓛v‖` times the linear field `v ↦ ΓDv` (the radial part
drops by Euler). The functions are
* `cfun = Q_D^{-1/2}` (`= 1/h` on the unit sphere),
* `qe = (Q_{B'} + ε²)^{1/2}`, `B' = (𝓛ΓA)ᴴ(𝓛ΓA)` (`= (q² + ε²)^{1/2}` on the sphere): the
  regularization of `q = ‖𝓛ΓAv‖` at `q = 0` (we take `ε² = T_D/N`),
* `ffun = χ(b₂) qe e^{-b₂/t + a²/(2t)} 𝔷`.
Every pairing `Re((ΓDv)* y)` equals `Re((𝓛v)*(𝓛Γy))` (`reInner_ΓD`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul quadQuot_of_unit)
open scoped ComplexConjugate

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Lin

variable {n : Type} [Fintype n] [DecidableEq n]

theorem reInner_add_right (x y z : n → ℂ) : reInner x (y + z) = reInner x y + reInner x z := by
  rw [reInner_eq_dot, reInner_eq_dot, reInner_eq_dot, dotProduct_add, Complex.add_re]

theorem reInner_sub_right (x y z : n → ℂ) : reInner x (y - z) = reInner x y - reInner x z := by
  rw [reInner_eq_dot, reInner_eq_dot, reInner_eq_dot, dotProduct_sub, Complex.sub_re]

theorem reInner_smul_right (x y : n → ℂ) (c : ℝ) : reInner x ((c : ℂ) • y) = c * reInner x y := by
  rw [reInner_eq_dot, reInner_eq_dot, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

end Lin

variable (D : AngularData ι) (L : Matrix κ ι ℂ)

/-- `D = 𝓛ᴴ𝓛`. -/
def Dm : Matrix ι ι ℂ := Lᴴ * L

/-- `B' = (𝓛ΓA)ᴴ(𝓛ΓA)`, so `Re(v*B'v) = ‖𝓛ΓAv‖² = q²`. -/
def Bq (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := (L * D.Γ * A)ᴴ * (L * D.Γ * A)

/-- `T_D = Re Tr(DΓ) = s F`. -/
def TD : ℝ := D.s * Fd D L

/-- Coefficient `c = Q_D^{-1/2}` (`= 1/‖𝓛v‖` on the unit sphere). -/
def cfun (v : ι → ℂ) : ℝ := (Real.sqrt (quadQuot (Dm L) v))⁻¹

/-- Regularized `q`: `(Q_{B'} + ε²)^{1/2}`. -/
def qe (A : Matrix ι ι ℂ) (ε2 : ℝ) (v : ι → ℂ) : ℝ := Real.sqrt (quadQuot (Bq D L A) v + ε2)

/-- `χ(b₂) · qe · e^{q} 𝔷`. -/
def ffun (χ : ℝ → ℝ) (Zf : (ι → ℂ) → ℝ) (A : Matrix ι ι ℂ) (ε2 : ℝ) (v : ι → ℂ) : ℝ :=
  χ (D.b₂ v) * qe D L A ε2 v * (Real.exp (D.expo v) * Zf v)

theorem Dm_isHermitian : (Dm L).IsHermitian := conjTranspose_mul_self_isHermitian L

theorem Bq_isHermitian (A : Matrix ι ι ℂ) : (Bq D L A).IsHermitian :=
  conjTranspose_mul_self_isHermitian _

theorem Dm_mulVec (v : ι → ℂ) : Dm L *ᵥ v = Lᴴ *ᵥ (L *ᵥ v) := by rw [Dm, ← mulVec_mulVec]

theorem quadNum_Dm (v : ι → ℂ) : quadNum (Dm L) v = normSqSum (L *ᵥ v) :=
  quadNum_conjTranspose_mul_self L v

theorem quadNum_Bq (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadNum (Bq D L A) v = normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) := by
  rw [Bq, quadNum_conjTranspose_mul_self, ← mulVec_mulVec, ← mulVec_mulVec]

theorem quadQuot_nonneg_of (M : Matrix κ ι ℂ) (v : ι → ℂ) : 0 ≤ quadQuot (Mᴴ * M) v := by
  rw [AngularData.quadQuot_eq, quadNum_conjTranspose_mul_self]
  exact div_nonneg (normSqSum_nonneg _) (normSqSum_nonneg _)

theorem quadQuot_Dm_pos (hL : ∀ x, L *ᵥ x = 0 → x = 0) {v : ι → ℂ} (hv : v ≠ 0) :
    0 < quadQuot (Dm L) v := by
  rw [AngularData.quadQuot_eq, quadNum_Dm]
  exact div_pos (normSqSum_pos fun h => hv (hL v h)) (normSqSum_pos hv)

/-- **Key pairing**: `Re((ΓDv)* y) = Re((𝓛v)*(𝓛Γy))`. -/
theorem reInner_ΓD (v y : ι → ℂ) :
    reInner (D.Γ *ᵥ (Dm L *ᵥ v)) y = reInner (L *ᵥ v) (L *ᵥ (D.Γ *ᵥ y)) := by
  rw [reInner_mulVec_left, D.Γ_isHermitian.eq, Dm_mulVec, reInner_mulVec_left,
    conjTranspose_conjTranspose]

/-- `Re((ΓDv)*K₀²v) = s‖𝓛v‖² + a_* Re((𝓛v)*𝓛ΓK₀v) - c_* Re((𝓛v)*𝓛Γv)`
(`K₀²Γ = s + a_*K₀Γ - c_*Γ`). -/
theorem reInner_ΓD_KK (v : ι → ℂ) :
    reInner (D.Γ *ᵥ (Dm L *ᵥ v)) ((D.K * D.K) *ᵥ v) =
      D.s * normSqSum (L *ᵥ v) +
        aStar D.ζ * reInner (L *ᵥ v) (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) -
        cStar D.ζ * reInner (L *ᵥ v) (L *ᵥ (D.Γ *ᵥ v)) := by
  rw [reInner_ΓD]
  have e : D.Γ *ᵥ ((D.K * D.K) *ᵥ v) = (D.s : ℂ) • v + (aStar D.ζ : ℂ) • (D.Γ *ᵥ (D.K *ᵥ v)) -
      (cStar D.ζ : ℂ) • (D.Γ *ᵥ v) := by
    rw [mulVec_mulVec, D.Γ_mul_KK, D.KK_mul_Γ, D.K_mul_Γ, sub_mulVec, add_mulVec, smul_mulVec,
      smul_mulVec, smul_mulVec, one_mulVec, mulVec_mulVec]
  rw [e, mulVec_sub, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, reInner_sub_right,
    reInner_add_right, reInner_smul_right, reInner_smul_right, reInner_smul_right, reInner_self]

/-- `Re((ΓDv)*Dv) = s‖R𝓛ᴴ𝓛v‖² ≤ T_D ‖𝓛v‖²`. -/
theorem reInner_ΓD_D_le (v : ι → ℂ) :
    reInner (D.Γ *ᵥ (Dm L *ᵥ v)) (Dm L *ᵥ v) ≤ TD D L * normSqSum (L *ᵥ v) := by
  rw [reInner_comm, AngularData.reInner_mulVec_self, quadNum_Γ, Dm_mulVec, TD, mul_assoc]
  exact mul_le_mul_of_nonneg_left (Rz_Lh_bound D L _) D.hs.le

/-- `‖𝓛ΓMx‖² ≤ s² F c_M ‖x‖²` when `‖RMx‖² ≤ c_M ‖x‖²`. -/
theorem LΓM_bound {M : Matrix ι ι ℂ} {cM : ℝ}
    (hcM : ∀ x, normSqSum (Rz D *ᵥ (M *ᵥ x)) ≤ cM * normSqSum x) (x : ι → ℂ) :
    normSqSum (L *ᵥ (D.Γ *ᵥ (M *ᵥ x))) ≤ D.s ^ 2 * Fd D L * cM * normSqSum x := by
  refine (LΓ_bound D L _).trans ?_
  rw [mul_assoc (D.s ^ 2 * Fd D L)]
  exact mul_le_mul_of_nonneg_left (hcM x) (mul_nonneg (sq_nonneg _) (Fd_nonneg D L))

theorem le_mul_one_add_of_sq_le {x B k : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B) (hk : 0 ≤ k)
    (h : x ^ 2 ≤ B ^ 2 * k) : x ≤ B * (1 + k) := by
  have h1 : x ^ 2 ≤ (B * (1 + k)) ^ 2 := by
    refine h.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg B)
  exact (pow_le_pow_iff_left₀ hx (by positivity) two_ne_zero).1 h1

/-- `|Re((ΓDv)* B'v)| ≤ ‖𝓛v‖ · s²FY(1+c_A) · ‖𝓛ΓAv‖`. -/
theorem abs_reInner_ΓD_Bq {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    {cA : ℝ} (hcA0 : 0 ≤ cA) (hcA : ∀ x, normSqSum (Rz D *ᵥ (A *ᵥ x)) ≤ cA * normSqSum x)
    (v : ι → ℂ) :
    |reInner (D.Γ *ᵥ (Dm L *ᵥ v)) (Bq D L A *ᵥ v)| ≤
      l2Norm (L *ᵥ v) * (D.s ^ 2 * Fd D L * Y * (1 + cA)) *
        l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) := by
  rw [reInner_ΓD]
  refine (abs_reInner_le _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (l2Norm_nonneg _)
  set u := L *ᵥ (D.Γ *ᵥ (A *ᵥ v))
  have hY0 : 0 ≤ Y := (inv_nonneg.2 (im_pos D).le).trans hY
  have eB : D.Γ *ᵥ (Bq D L A *ᵥ v) = D.Γ *ᵥ (A *ᵥ (D.Γ *ᵥ (Lᴴ *ᵥ u))) := by
    rw [Bq, conjTranspose_mul, conjTranspose_mul, hA.eq, D.Γ_isHermitian.eq, ← mulVec_mulVec,
      ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  rw [eB]
  have h1 := LΓM_bound D L hcA (D.Γ *ᵥ (Lᴴ *ᵥ u))
  have h2 := Γ_bound D hY (Lᴴ *ᵥ u)
  have h3 := Rz_Lh_bound D L u
  have hF := Fd_nonneg D L
  have hsq : l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ (D.Γ *ᵥ (Lᴴ *ᵥ u))))) ^ 2 ≤
      (D.s ^ 2 * Fd D L * Y * l2Norm u) ^ 2 * cA := by
    rw [l2Norm_sq, mul_pow, l2Norm_sq]
    calc _ ≤ D.s ^ 2 * Fd D L * cA * normSqSum (D.Γ *ᵥ (Lᴴ *ᵥ u)) := h1
      _ ≤ D.s ^ 2 * Fd D L * cA * (D.s ^ 2 * Y ^ 2 * (Fd D L * normSqSum u)) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ = _ := by ring
  have := le_mul_one_add_of_sq_le (l2Norm_nonneg _) (by positivity [D.hs.le, l2Norm_nonneg u])
    hcA0 hsq
  calc _ ≤ _ := this
    _ = D.s ^ 2 * Fd D L * Y * (1 + cA) * l2Norm u := by ring

/-- `|Re((ΓDv)*∇𝔷)| ≤ ‖𝓛v‖ ‖𝓛Γ∇𝔷‖` and `‖𝓛Γx‖² ≤ s²FY²‖x‖²`. -/
theorem LΓ_bound' {Y : ℝ} (hY : D.ζ.im⁻¹ ≤ Y) (x : ι → ℂ) :
    normSqSum (L *ᵥ (D.Γ *ᵥ x)) ≤ D.s ^ 2 * Fd D L * Y ^ 2 * normSqSum x := by
  refine (LΓ_bound D L x).trans ?_
  rw [mul_assoc (D.s ^ 2 * Fd D L)]
  exact mul_le_mul_of_nonneg_left (Rz_bound D hY x) (mul_nonneg (sq_nonneg _) (Fd_nonneg D L))

/-!
## Regularity
-/

theorem cfun_inv : IsScaleInvariant (cfun L) := fun z r hr => by
  simp only [cfun, quadQuot_scale _ z hr]

theorem cfun_c1 (hL : ∀ x, L *ᵥ x = 0 → x = 0) : ContDiffOn ℝ 1 (cfun L) {z | z ≠ 0} :=
  ((contDiffOn_quadQuot _).sqrt fun _ hz => (quadQuot_Dm_pos L hL hz).ne').inv fun _ hz =>
    (Real.sqrt_pos.2 (quadQuot_Dm_pos L hL hz)).ne'

theorem cfun_meas : Measurable (cfun L) :=
  ((measurable_quadQuot _).sqrt).inv

theorem qe_pos (A : Matrix ι ι ℂ) {ε2 : ℝ} (hε : 0 < ε2) (v : ι → ℂ) : 0 < qe D L A ε2 v :=
  Real.sqrt_pos.2 (by have := quadQuot_nonneg_of (L * D.Γ * A) v; unfold Bq; linarith)

theorem qe_inv (A : Matrix ι ι ℂ) (ε2 : ℝ) : IsScaleInvariant (qe D L A ε2) := fun z r hr => by
  simp only [qe, quadQuot_scale _ z hr]

theorem qe_c1 (A : Matrix ι ι ℂ) {ε2 : ℝ} (hε : 0 < ε2) :
    ContDiffOn ℝ 1 (qe D L A ε2) {z | z ≠ 0} :=
  ((contDiffOn_quadQuot _).add contDiffOn_const).sqrt fun y _ => (Real.sqrt_pos.1
    (qe_pos D L A hε y)).ne'

theorem qe_meas (A : Matrix ι ι ℂ) (ε2 : ℝ) : Measurable (qe D L A ε2) :=
  ((measurable_quadQuot _).add_const _).sqrt

theorem b₂_c1 : ContDiffOn ℝ 1 D.b₂ {z | z ≠ 0} := contDiffOn_quadQuot _

theorem a_c1 : ContDiffOn ℝ 1 D.a {z | z ≠ 0} := contDiffOn_quadQuot _

theorem ffun_inv (χ : ℝ → ℝ) {Zf : (ι → ℂ) → ℝ} (hZi : IsScaleInvariant Zf)
    (A : Matrix ι ι ℂ) (ε2 : ℝ) : IsScaleInvariant (ffun D L χ Zf A ε2) := fun z r hr => by
  simp only [ffun, AngularData.b₂, quadQuot_scale _ z hr, qe_inv D L A ε2 z r hr,
    D.expo_inv z r hr, hZi z r hr]

theorem ffun_c1 {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {Zf : (ι → ℂ) → ℝ}
    (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0}) (A : Matrix ι ι ℂ) {ε2 : ℝ} (hε : 0 < ε2) :
    ContDiffOn ℝ 1 (ffun D L χ Zf A ε2) {z | z ≠ 0} :=
  ((hχ.comp_contDiffOn (b₂_c1 D)).mul (qe_c1 D L A hε)).mul
    ((Real.contDiff_exp.comp_contDiffOn D.expo_c1).mul hZc)

theorem ffun_meas {χ : ℝ → ℝ} (hχ : Continuous χ) {Zf : (ι → ℂ) → ℝ} (hZm : Measurable Zf)
    (A : Matrix ι ι ℂ) (ε2 : ℝ) : Measurable (ffun D L χ Zf A ε2) :=
  ((hχ.measurable.comp (measurable_quadQuot _)).mul (qe_meas D L A ε2)).mul
    ((Real.measurable_exp.comp D.expo_meas).mul hZm)

end BlockBand.Angular.Ratio
