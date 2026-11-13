module

public import BlockBand.Angular.ProjectiveStein
public import BlockBand.Angular.ReferenceIdentities

/-!
# The finite angular measure and its Stein identities

Setting (`AngularData`): a Hermitian `K₀` on a finite index set of cardinality `N`,
`s > 0`, an angular root `ζ = s m` of `m = N⁻¹ Tr (K₀ - sm)⁻¹` with `Im ζ > 0`, `t = s/N`,
`Γ = s (K₀ - ζ̄)⁻¹(K₀ - ζ)⁻¹`. Angular functions are scale-invariant functions on `ℂ^ι`
(`quadQuot M v = Re(v*Mv)/‖v‖²`): `a = Q_{K₀}`, `b₂ = Q_{K₀²}`, `u_k = Q_{K₀^k Γ}`, the
regression exponent `q = -b₂/t + a²/(2t)` of the angular measure, the ratios
`r_A = Q_{ΓA}/u₀` and the fields `W_A(v) = Γ(A - r_A)v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Stein

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.ConeDivergence
open BlockBand.Angular.DegreeZero BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Angular data: Hermitian `K₀`, `s > 0`, an angular root `ζ`. -/
structure AngularData (ι : Type) [Fintype ι] [DecidableEq ι] where
  K : Matrix ι ι ℂ
  s : ℝ
  ζ : ℂ
  hK : K.IsHermitian
  hs : 0 < s
  hroot : IsAngularRoot K s ζ

/-!
## Bounded angular functions
-/

/-- Bounded off the origin. -/
def Bdd (G : (ι → ℂ) → ℝ) : Prop := ∃ M : ℝ, ∀ z, z ≠ 0 → |G z| ≤ M

theorem Bdd.add {G H : (ι → ℂ) → ℝ} (hG : Bdd G) (hH : Bdd H) : Bdd (fun z => G z + H z) := by
  obtain ⟨M, hM⟩ := hG; obtain ⟨M', hM'⟩ := hH
  exact ⟨M + M', fun z hz => (abs_add_le _ _).trans (add_le_add (hM z hz) (hM' z hz))⟩

theorem Bdd.neg {G : (ι → ℂ) → ℝ} (hG : Bdd G) : Bdd (fun z => -G z) := by
  obtain ⟨M, hM⟩ := hG; exact ⟨M, fun z hz => by rw [abs_neg]; exact hM z hz⟩

theorem Bdd.sub {G H : (ι → ℂ) → ℝ} (hG : Bdd G) (hH : Bdd H) : Bdd (fun z => G z - H z) := by
  simpa [sub_eq_add_neg] using hG.add hH.neg

theorem Bdd.mul {G H : (ι → ℂ) → ℝ} (hG : Bdd G) (hH : Bdd H) : Bdd (fun z => G z * H z) := by
  obtain ⟨M, hM⟩ := hG; obtain ⟨M', hM'⟩ := hH
  refine ⟨M * M', fun z hz => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM z hz) (hM' z hz) (abs_nonneg _) ((abs_nonneg _).trans (hM z hz))

theorem bdd_const (c : ℝ) : Bdd (fun _ : ι → ℂ => c) := ⟨|c|, fun _ _ => le_rfl⟩

theorem bdd_of_scaleInvariant {G : (ι → ℂ) → ℝ} (hinv : IsScaleInvariant G)
    (hc : ContDiffOn ℝ 1 G {z | z ≠ 0}) : Bdd G := by
  obtain ⟨M, hM, -⟩ := exists_bound_of_scaleInvariant hinv hc
  exact ⟨M, fun z _ => hM z⟩

theorem bdd_fderiv {G : (ι → ℂ) → ℝ} (hinv : IsScaleInvariant G)
    (hc : ContDiffOn ℝ 1 G {z | z ≠ 0}) (B : Matrix ι ι ℂ) :
    Bdd (fun z => fderiv ℝ G z (B *ᵥ z)) :=
  exists_bound_fderiv_mulVec hinv hc B

theorem Bdd.integrable [Nonempty ι] {G : (ι → ℂ) → ℝ} (hG : Bdd G) (hm : Measurable G) :
    Integrable G (projectiveHaar ι) := by
  obtain ⟨M, hM⟩ := hG; exact integrable_projectiveHaar_of_bound hm hM

namespace AngularData

variable (D : AngularData ι)

/-- `t = s/N_aux`, `N_aux = card ι`. -/
def t : ℝ := D.s / Fintype.card ι

/-- `Γ = s (K₀ - ζ̄)⁻¹ (K₀ - ζ)⁻¹`. -/
def Γ : Matrix ι ι ℂ := angularGamma D.K D.s D.ζ

/-- `a(v) = v*K₀v` (scale-invariant form). -/
def a : (ι → ℂ) → ℝ := quadQuot D.K

/-- `b₂(v) = ‖K₀v‖² = v*K₀²v` (scale-invariant form). -/
def b₂ : (ι → ℂ) → ℝ := quadQuot (D.K * D.K)

/-- The regression exponent `-b₂/t + a²/(2t)` of the angular measure. -/
def expo (v : ι → ℂ) : ℝ := -(D.b₂ v) / D.t + D.a v ^ 2 / (2 * D.t)

/-- `u₀ = v*Γv`. -/
def u₀ : (ι → ℂ) → ℝ := quadQuot D.Γ

/-- `u₁ = v*K₀Γv`. -/
def u₁ : (ι → ℂ) → ℝ := quadQuot (D.K * D.Γ)

/-- `u₂ = v*K₀²Γv`. -/
def u₂ : (ι → ℂ) → ℝ := quadQuot (D.K * D.K * D.Γ)

/-- `r_A = Re(v*ΓAv)/u₀`. -/
def ratio (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := quadQuot (D.Γ * A) v / D.u₀ v

/-- `W_A(v) = Γ(A - r_A)v`. -/
def field (A : Matrix ι ι ℂ) (v : ι → ℂ) : ι → ℂ :=
  D.Γ *ᵥ (A *ᵥ v) - (D.ratio A v : ℂ) • (D.Γ *ᵥ v)

/-- `Re(v*AΓK₀v) - r_A u₁` (for `A = J` this is `b_J`; for `A = K₀` it is `V_Γ`). -/
def corr (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := quadQuot (A * D.Γ * D.K) v - D.ratio A v * D.u₁ v

theorem hz : D.ζ.im ≠ 0 := D.hroot.1.ne'

theorem Γ_eq : D.Γ = (D.s : ℂ) • ((Reference.resolvent D.K D.ζ)ᴴ * Reference.resolvent D.K D.ζ) := by
  rw [Γ, angularGamma, resolvent_conj D.hK]

theorem Γ_isHermitian : D.Γ.IsHermitian := by
  rw [Γ_eq, IsHermitian, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp

theorem K_commute_resolvent {z : ℂ} (hz : z.im ≠ 0) :
    D.K * Reference.resolvent D.K z = Reference.resolvent D.K z * D.K := by
  rw [K_mul_resolvent D.hK hz, resolvent_mul_K D.hK hz]

theorem K_mul_Γ : D.K * D.Γ = D.Γ * D.K := by
  have h1 := D.K_commute_resolvent D.hz
  have h2 := D.K_commute_resolvent (im_conj_ne D.hz)
  rw [Γ, angularGamma, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, h2,
    Matrix.mul_assoc, h1, Matrix.mul_assoc]

/-!
## Rayleigh quotients along lines
-/

/-- `n_M(v) = Re(v*Mv)`. -/
def quadNum (M : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := (∑ a, conj (v a) * (M *ᵥ v) a).re

/-- `Re(x* y)`. -/
def reInner (x y : ι → ℂ) : ℝ := (∑ a, conj (x a) * y a).re

theorem quadQuot_eq (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadQuot M v = quadNum M v / normSqSum v := rfl

theorem normSqSum_eq_reInner (v : ι → ℂ) : normSqSum v = reInner v v := by
  unfold normSqSum reInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.conj_mul']; norm_cast

theorem quadNum_line (M : Matrix ι ι ℂ) (v h : ι → ℂ) (τ : ℝ) :
    quadNum M (v + τ • h) =
      quadNum M v + τ * (reInner h (M *ᵥ v) + reInner v (M *ᵥ h)) + τ ^ 2 * quadNum M h := by
  unfold quadNum reInner
  rw [mulVec_add, mulVec_smul]
  simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, map_add, map_mul,
    Complex.conj_ofReal, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem normSqSum_line (v h : ι → ℂ) (τ : ℝ) :
    normSqSum (v + τ • h) = normSqSum v + τ * (2 * reInner h v) + τ ^ 2 * normSqSum h := by
  have := quadNum_line (1 : Matrix ι ι ℂ) v h τ
  have e : ∀ w : ι → ℂ, quadNum 1 w = normSqSum w := by
    intro w; rw [normSqSum_eq_reInner]; unfold quadNum reInner; rw [one_mulVec]
  rw [e, e, e, one_mulVec, one_mulVec] at this
  rw [this]
  have hsym : reInner v h = reInner h v := by
    unfold reInner
    rw [← Complex.conj_re, map_sum]
    congr 1; refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]
  rw [hsym]; ring

/-- Derivative of a Rayleigh quotient along a line through a unit vector in a tangent
direction: `d/dτ Q_M(v + τh)|₀ = Re(h*Mv) + Re(v*Mh)` when `‖v‖ = 1`, `Re(h*v) = 0`. -/
theorem hasDerivAt_quadQuot_line (M : Matrix ι ι ℂ) (v h : ι → ℂ) (hv : normSqSum v = 1)
    (ht : reInner h v = 0) :
    HasDerivAt (fun τ : ℝ => quadQuot M (v + τ • h))
      (reInner h (M *ᵥ v) + reInner v (M *ᵥ h)) 0 := by
  have hfun : (fun τ : ℝ => quadQuot M (v + τ • h)) = fun τ =>
      (quadNum M v + τ * (reInner h (M *ᵥ v) + reInner v (M *ᵥ h)) + τ ^ 2 * quadNum M h) /
        (1 + τ ^ 2 * normSqSum h) := by
    funext τ
    rw [quadQuot_eq, quadNum_line, normSqSum_line, hv, ht]
    ring_nf
  rw [hfun]
  set p := reInner h (M *ᵥ v) + reInner v (M *ᵥ h)
  have hnum : HasDerivAt (fun τ : ℝ => quadNum M v + τ * p + τ ^ 2 * quadNum M h) p 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const p).const_add (quadNum M v)).fun_add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (quadNum M h))
    simpa using this
  have hden : HasDerivAt (fun τ : ℝ => 1 + τ ^ 2 * normSqSum h) 0 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (normSqSum h)).const_add 1
    simpa using this
  have := hnum.div hden (by simp)
  convert this using 1
  simp [quadNum]

/-- Directional derivatives of a differentiable function agree with derivatives along lines. -/
theorem fderiv_apply_of_line {f : (ι → ℂ) → ℝ} {v h : ι → ℂ} (hf : DifferentiableAt ℝ f v)
    {d : ℝ} (hd : HasDerivAt (fun τ : ℝ => f (v + τ • h)) d 0) : fderiv ℝ f v h = d := by
  have hline : HasDerivAt (fun τ : ℝ => v + τ • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add v
  have hf' : HasFDerivAt f (fderiv ℝ f v) (v + (0 : ℝ) • h) := by simpa using hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt (0 : ℝ) hline).unique hd

theorem reInner_mulVec (B M : Matrix ι ι ℂ) (x : ι → ℂ) :
    reInner (B *ᵥ x) (M *ᵥ x) = quadNum (Bᴴ * M) x := by
  unfold reInner quadNum
  have h1 : (∑ a, conj ((B *ᵥ x) a) * (M *ᵥ x) a) = star (B *ᵥ x) ⬝ᵥ (M *ᵥ x) := rfl
  have h2 : (∑ a, conj (x a) * ((Bᴴ * M) *ᵥ x) a) = star x ⬝ᵥ ((Bᴴ * M) *ᵥ x) := rfl
  rw [h1, h2, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem reInner_mulVec_self (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    reInner x (M *ᵥ x) = quadNum M x := rfl

theorem quadNum_conjTranspose (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadNum Mᴴ x = quadNum M x := by
  unfold quadNum
  have h1 : (∑ a, conj (x a) * (Mᴴ *ᵥ x) a) = star x ⬝ᵥ (Mᴴ *ᵥ x) := rfl
  have h2 : (∑ a, conj (x a) * (M *ᵥ x) a) = star x ⬝ᵥ (M *ᵥ x) := rfl
  have h3 : star x ⬝ᵥ (Mᴴ *ᵥ x) = star (star x ⬝ᵥ (M *ᵥ x)) := by
    calc star x ⬝ᵥ (Mᴴ *ᵥ x) = (star x ᵥ* Mᴴ) ⬝ᵥ x := dotProduct_mulVec _ _ _
      _ = star (M *ᵥ x) ⬝ᵥ x := by rw [star_mulVec]
      _ = star (star x ⬝ᵥ (M *ᵥ x)) := by simp [dotProduct, mul_comm]
  rw [h1, h2, h3]
  exact Complex.conj_re _

theorem quadNum_add (M M' : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadNum (M + M') x = quadNum M x + quadNum M' x := by
  unfold quadNum
  rw [add_mulVec, ← Complex.add_re, ← Finset.sum_add_distrib]
  congr 1; exact Finset.sum_congr rfl fun a _ => by rw [Pi.add_apply, mul_add]

theorem quadNum_sub (M M' : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadNum (M - M') x = quadNum M x - quadNum M' x := by
  unfold quadNum
  rw [sub_mulVec, ← Complex.sub_re, ← Finset.sum_sub_distrib]
  congr 1; exact Finset.sum_congr rfl fun a _ => by rw [Pi.sub_apply, mul_sub]

theorem quadNum_real_smul (c : ℝ) (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadNum ((c : ℂ) • M) x = c * quadNum M x := by
  unfold quadNum
  rw [smul_mulVec, ← Complex.re_ofReal_mul, Finset.mul_sum]
  congr 1; exact Finset.sum_congr rfl fun a _ => by rw [Pi.smul_apply, smul_eq_mul]; ring

theorem quadNum_one (x : ι → ℂ) : quadNum (1 : Matrix ι ι ℂ) x = normSqSum x := by
  rw [normSqSum_eq_reInner]; unfold quadNum reInner; rw [one_mulVec]

theorem quadQuot_of_unit {M : Matrix ι ι ℂ} {x : ι → ℂ} (hx : normSqSum x = 1) :
    quadQuot M x = quadNum M x := by
  rw [quadQuot_eq, hx, div_one]

/-- `Re(v*Γv) = s ‖(K₀ - ζ)⁻¹ v‖² > 0` for `v ≠ 0`. -/
theorem quadNum_Γ_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < quadNum D.Γ v := by
  set R := Reference.resolvent D.K D.ζ
  have hΓ : quadNum D.Γ v = D.s * normSqSum (R *ᵥ v) := by
    rw [Γ_eq, quadNum_real_smul, ← reInner_mulVec, ← normSqSum_eq_reInner]
  rw [hΓ]
  apply mul_pos D.hs (normSqSum_pos _)
  intro h0
  have hu := isUnit_det_sub_smul D.hK D.hz
  have : (D.K - D.ζ • (1 : Matrix ι ι ℂ)) *ᵥ (R *ᵥ v) = v := by
    rw [mulVec_mulVec, resolvent_mul D.hK D.hz, one_mulVec]
  rw [h0, mulVec_zero] at this
  exact hv this.symm

theorem u₀_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < D.u₀ v := by
  unfold u₀; rw [quadQuot_eq]
  exact div_pos (D.quadNum_Γ_pos hv) (normSqSum_pos hv)

theorem reInner_comm (x y : ι → ℂ) : reInner x y = reInner y x := by
  unfold reInner
  rw [← Complex.conj_re, map_sum]
  congr 1; refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_comm]

theorem reInner_mulVec_herm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (x y : ι → ℂ) :
    reInner x (M *ᵥ y) = reInner y (M *ᵥ x) := by
  unfold reInner
  have h1 : (∑ a, conj (x a) * (M *ᵥ y) a) = star x ⬝ᵥ (M *ᵥ y) := rfl
  have h2 : (∑ a, conj (y a) * (M *ᵥ x) a) = star y ⬝ᵥ (M *ᵥ x) := rfl
  rw [h1, h2, ← hM.star_dotProduct_mulVec_comm y x]
  exact Complex.conj_re _

theorem reInner_sub_smul (x y z : ι → ℂ) (c : ℝ) :
    reInner (x - (c : ℂ) • y) z = reInner x z - c * reInner y z := by
  unfold reInner
  rw [← Complex.re_ofReal_mul, ← Complex.sub_re, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1; refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Complex.conj_ofReal]
  ring

/-- `Re((ΓAv)* M v) = Re(v* AΓM v)` for Hermitian `A`. -/
theorem reInner_ΓA (A M : Matrix ι ι ℂ) (hA : A.IsHermitian) (v : ι → ℂ) :
    reInner (D.Γ *ᵥ (A *ᵥ v)) (M *ᵥ v) = quadNum (A * D.Γ * M) v := by
  rw [mulVec_mulVec, reInner_mulVec, conjTranspose_mul, hA.eq, D.Γ_isHermitian.eq]

theorem reInner_Γ (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    reInner (D.Γ *ᵥ v) (M *ᵥ v) = quadNum (D.Γ * M) v := by
  rw [reInner_mulVec, D.Γ_isHermitian.eq]

/-- `Re((W_A)* M v) = Re(v*AΓMv) - r_A Re(v*ΓMv)`. -/
theorem reInner_field (A M : Matrix ι ι ℂ) (hA : A.IsHermitian) (v : ι → ℂ) :
    reInner (D.field A v) (M *ᵥ v) =
      quadNum (A * D.Γ * M) v - D.ratio A v * quadNum (D.Γ * M) v := by
  rw [field, reInner_sub_smul, D.reInner_ΓA A M hA, D.reInner_Γ]

/-- `r_A u₀ = Re(v*ΓAv)` off the origin. -/
theorem ratio_mul_u₀ (A : Matrix ι ι ℂ) {v : ι → ℂ} (hv : v ≠ 0) :
    D.ratio A v * D.u₀ v = quadQuot (D.Γ * A) v := by
  unfold ratio; field_simp [(D.u₀_pos hv).ne']

/-- `W_A` is tangent: `Re(W_A* v) = 0`. -/
theorem reInner_field_self (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {v : ι → ℂ} (hv : v ≠ 0) :
    reInner (D.field A v) v = 0 := by
  have h := D.reInner_field A 1 hA v
  rw [one_mulVec, Matrix.mul_one, Matrix.mul_one] at h
  rw [h]
  have e1 : quadNum (A * D.Γ) v = quadNum (D.Γ * A) v := by
    rw [← quadNum_conjTranspose, conjTranspose_mul, hA.eq, D.Γ_isHermitian.eq]
  have e2 := D.ratio_mul_u₀ A hv
  unfold u₀ at e2
  rw [quadQuot_eq, quadQuot_eq] at e2
  have hS := (normSqSum_pos hv).ne'
  rw [e1]
  field_simp at e2
  linarith

theorem Γ_mul_K : D.Γ * D.K = D.K * D.Γ := D.K_mul_Γ.symm

theorem KK_mul_Γ : D.K * D.K * D.Γ =
    (D.s : ℂ) • 1 + (aStar D.ζ : ℂ) • (D.K * D.Γ) - (cStar D.ζ : ℂ) • D.Γ :=
  K_sq_mul_angularGamma D.hK D.hz

theorem Γ_mul_KK : D.Γ * (D.K * D.K) = D.K * D.K * D.Γ := by
  rw [← Matrix.mul_assoc, D.Γ_mul_K, Matrix.mul_assoc, D.Γ_mul_K, ← Matrix.mul_assoc]

/-- **The regression derivative along `W_A`** (used in the angular ratio
lemma and the angular Stein lemma): at a unit vector, for Hermitian `A`,
`D(-b₂/t + a²/(2t))[W_A] = -2N(Re v*Av - r_A) + (2N/s)(a - a_*)(Re v*AΓK₀v - r_A u₁)`. -/
theorem fderiv_expo_field (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {v : ι → ℂ}
    (hv1 : normSqSum v = 1) (hdiff : DifferentiableAt ℝ D.expo v) :
    fderiv ℝ D.expo v (D.field A v) =
      -(2 * Fintype.card ι) * (quadQuot A v - D.ratio A v) +
        (2 * Fintype.card ι / D.s) * (D.a v - aStar D.ζ) * D.corr A v := by
  have hv : v ≠ 0 := by
    intro h0; rw [h0] at hv1; simp [normSqSum] at hv1
  set W := D.field A v with hW
  have htan : reInner W v = 0 := D.reInner_field_self A hA hv
  have hKK := hasDerivAt_quadQuot_line (D.K * D.K) v W hv1 htan
  have hK := hasDerivAt_quadQuot_line D.K v W hv1 htan
  have hKKh : (D.K * D.K).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, D.hK.eq]
  rw [reInner_mulVec_herm hKKh v W] at hKK
  rw [reInner_mulVec_herm D.hK v W] at hK
  have hfun : (fun τ : ℝ => D.expo (v + τ • W)) = fun τ =>
      (-(1 / D.t)) * quadQuot (D.K * D.K) (v + τ • W) +
        (1 / (2 * D.t)) * (quadQuot D.K (v + τ • W) * quadQuot D.K (v + τ • W)) := by
    funext τ; simp only [expo, b₂, a]; ring
  have hline : HasDerivAt (fun τ : ℝ => D.expo (v + τ • W))
      (-(2 * reInner W ((D.K * D.K) *ᵥ v)) / D.t +
        2 * quadQuot D.K v * (2 * reInner W (D.K *ᵥ v)) / (2 * D.t)) 0 := by
    rw [hfun]
    have := (hKK.const_mul (-(1 / D.t))).add ((hK.mul hK).const_mul (1 / (2 * D.t)))
    convert this using 1
    simp only [zero_smul, add_zero]
    ring
  rw [fderiv_apply_of_line hdiff hline]
  -- evaluate the two inner products
  have hN : (0 : ℝ) < Fintype.card ι := by
    have : Nonempty ι := ⟨(Function.ne_iff.1 hv).choose⟩
    exact_mod_cast Fintype.card_pos
  have hmK : reInner W (D.K *ᵥ v) = D.corr A v := by
    rw [hW, D.reInner_field A D.K hA v, corr, u₁, D.Γ_mul_K, quadQuot_of_unit hv1,
      quadQuot_of_unit hv1]
  have hmKK : reInner W ((D.K * D.K) *ᵥ v) =
      D.s * (quadQuot A v - D.ratio A v) + aStar D.ζ * D.corr A v := by
    rw [hW, D.reInner_field A (D.K * D.K) hA v, D.Γ_mul_KK]
    have hAKK : A * D.Γ * (D.K * D.K) = A * (D.K * D.K * D.Γ) := by
      rw [Matrix.mul_assoc, D.Γ_mul_KK]
    rw [hAKK, D.KK_mul_Γ]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    rw [quadNum_sub, quadNum_add, quadNum_real_smul, quadNum_real_smul, quadNum_real_smul,
      quadNum_sub, quadNum_add, quadNum_real_smul, quadNum_real_smul, quadNum_real_smul,
      quadNum_one, hv1]
    have e1 : quadNum (A * D.Γ) v = D.ratio A v * quadNum D.Γ v := by
      rw [← quadNum_conjTranspose, conjTranspose_mul, hA.eq, D.Γ_isHermitian.eq]
      have := D.ratio_mul_u₀ A hv
      unfold u₀ at this
      rw [quadQuot_of_unit hv1, quadQuot_of_unit hv1] at this
      linarith
    have e2 : quadNum (A * (D.K * D.Γ)) v = quadNum (A * D.Γ * D.K) v := by
      rw [D.K_mul_Γ, Matrix.mul_assoc]
    rw [e1, e2, corr, u₁]
    simp only [quadQuot_of_unit hv1]
    ring
  rw [hmK, hmKK, t]
  unfold a
  have hs0 := D.hs.ne'
  field_simp
  ring

/-!
## Regularity of the angular data
-/

theorem quadQuot_inv (M : Matrix ι ι ℂ) : IsScaleInvariant (quadQuot M) :=
  fun z _ hr => quadQuot_scale M z hr

theorem ratio_inv (A : Matrix ι ι ℂ) : IsScaleInvariant (D.ratio A) := fun z r hr => by
  simp only [ratio, u₀, quadQuot_scale _ z hr]

theorem ratio_c1 (A : Matrix ι ι ℂ) : ContDiffOn ℝ 1 (D.ratio A) {z | z ≠ 0} :=
  (contDiffOn_quadQuot (D.Γ * A)).div (contDiffOn_quadQuot D.Γ) fun _ hz => (D.u₀_pos hz).ne'

theorem ratio_meas (A : Matrix ι ι ℂ) : Measurable (D.ratio A) :=
  (measurable_quadQuot _).div (measurable_quadQuot _)

theorem expo_inv : IsScaleInvariant D.expo := fun z r hr => by
  simp only [expo, a, b₂, quadQuot_scale _ z hr]

theorem expo_c1 : ContDiffOn ℝ 1 D.expo {z | z ≠ 0} :=
  ((contDiffOn_quadQuot (D.K * D.K)).neg.div_const D.t).add
    (((contDiffOn_quadQuot D.K).pow 2).div_const (2 * D.t))

theorem expo_meas : Measurable D.expo :=
  ((measurable_quadQuot _).neg.div_const _).add (((measurable_quadQuot _).pow_const 2).div_const _)

theorem corr_inv (A : Matrix ι ι ℂ) : IsScaleInvariant (D.corr A) := fun z r hr => by
  simp only [corr, u₁, quadQuot_scale _ z hr, D.ratio_inv A z r hr]

theorem corr_c1 (A : Matrix ι ι ℂ) : ContDiffOn ℝ 1 (D.corr A) {z | z ≠ 0} :=
  (contDiffOn_quadQuot _).sub ((D.ratio_c1 A).mul (contDiffOn_quadQuot _))

theorem corr_meas (A : Matrix ι ι ℂ) : Measurable (D.corr A) :=
  (measurable_quadQuot _).sub ((D.ratio_meas A).mul (measurable_quadQuot _))

theorem fderiv_field_apply {G : (ι → ℂ) → ℝ} (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    fderiv ℝ G v (D.field A v) =
      fderiv ℝ G v ((D.Γ * A) *ᵥ v) - D.ratio A v * fderiv ℝ G v (D.Γ *ᵥ v) := by
  rw [field, mulVec_mulVec, map_sub, complex_smul_eq_real_smul, map_smul, smul_eq_mul]

/-- `Re Tr Γ = N_aux`. -/
theorem trace_Γ_re : (D.Γ.trace).re = Fintype.card ι := by
  rw [Γ, trace_angularGamma D.hK D.hs.ne' D.hroot]; simp

/-- **The angular Stein lemma, general Hermitian form**. Under the projective
Haar measure `ν_N`, for scale-invariant `C¹` (off the origin) Borel `Z` (the determinant
factor) and `F` (the test), with `ρ = e^{-b₂/t + a²/(2t)} Z F` the unnormalized angular
density times the test, and every Hermitian `A`:
`2N ν_N[ρ (Re v*Av - N⁻¹ Re Tr ΓA)] = ν_N[e^{q}(Z DF[W_A] + F DZ[W_A])] - ν_N[ρ Δ_A]
  + (2N/s) ν_N[ρ (a - a_*)(Re v*AΓK₀v - r_A u₁)]`, `Δ_A = Dr_A[Γv]`.
For `A = J` this is the contrast Stein identity (`j_* = N⁻¹ Tr ΓJ`); for `A = K₀`
(`N⁻¹ Tr ΓK₀ = a_*`, `Re v*K₀ΓK₀v - r u₁ = V_Γ`) it is the longitudinal Stein identity. The
determinant gradient enters as `F DZ[W_A] = F Z Re(H*W_A)`, `H = ∇ log Z`, so no lower bound
on `Z` is needed. No normalization by the mass of `ν` is used. -/
theorem angular_stein [Nonempty ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (Z F : (ι → ℂ) → ℝ) (hZm : Measurable Z) (hFm : Measurable F)
    (hZi : IsScaleInvariant Z) (hFi : IsScaleInvariant F)
    (hZc : ContDiffOn ℝ 1 Z {z | z ≠ 0}) (hFc : ContDiffOn ℝ 1 F {z | z ≠ 0}) :
    2 * (Fintype.card ι : ℝ) * ∫ v, Real.exp (D.expo v) * Z v * F v *
        (quadQuot A v - (Fintype.card ι : ℝ)⁻¹ * ((D.Γ * A).trace).re) ∂projectiveHaar ι =
      (∫ v, Real.exp (D.expo v) * (Z v * fderiv ℝ F v (D.field A v) +
          F v * fderiv ℝ Z v (D.field A v)) ∂projectiveHaar ι) -
        (∫ v, Real.exp (D.expo v) * Z v * F v * fderiv ℝ (D.ratio A) v (D.Γ *ᵥ v)
          ∂projectiveHaar ι) +
        2 * (Fintype.card ι : ℝ) / D.s * ∫ v, Real.exp (D.expo v) * Z v * F v *
          ((D.a v - aStar D.ζ) * D.corr A v) ∂projectiveHaar ι := by
  have hopen : IsOpen {z : ι → ℂ | z ≠ 0} := isOpen_ne
  have dAt : ∀ {G : (ι → ℂ) → ℝ}, ContDiffOn ℝ 1 G {z | z ≠ 0} → ∀ z : ι → ℂ, z ≠ 0 →
      DifferentiableAt ℝ G z := fun hG z hz =>
    (hG.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hz)
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set E : (ι → ℂ) → ℝ := fun v => Real.exp (D.expo v) with hE
  have hEi : IsScaleInvariant E := fun z r hr => by simp only [hE, D.expo_inv z r hr]
  have hEc : ContDiffOn ℝ 1 E {z | z ≠ 0} := Real.contDiff_exp.comp_contDiffOn D.expo_c1
  have hEm : Measurable E := Real.measurable_exp.comp D.expo_meas
  set ρ : (ι → ℂ) → ℝ := fun v => E v * Z v * F v with hρ
  have hρi : IsScaleInvariant ρ := fun z r hr => by
    simp only [hρ, hEi z r hr, hZi z r hr, hFi z r hr]
  have hρc : ContDiffOn ℝ 1 ρ {z | z ≠ 0} := (hEc.mul hZc).mul hFc
  have hρm : Measurable ρ := (hEm.mul hZm).mul hFm
  set r := D.ratio A with hr
  have S1 := integral_projectiveHaar_fderiv_mulVec ρ hρm hρi hρc (D.Γ * A)
  have S2 := integral_projectiveHaar_coeff_fderiv_mulVec r ρ (D.ratio_meas A) hρm
    (D.ratio_inv A) hρi (D.ratio_c1 A) hρc D.Γ
  -- pointwise identity at unit vectors
  have hpt : ∀ v : ι → ℂ, normSqSum v = 1 →
      E v * (Z v * fderiv ℝ F v (D.field A v) + F v * fderiv ℝ Z v (D.field A v)) -
          ρ v * fderiv ℝ r v (D.Γ *ᵥ v) + 2 * N / D.s * (ρ v * ((D.a v - aStar D.ζ) *
            D.corr A v)) - 2 * N * (ρ v * (quadQuot A v - N⁻¹ * ((D.Γ * A).trace).re)) =
        (fderiv ℝ ρ v ((D.Γ * A) *ᵥ v) - 2 * (ρ v * (N * quadQuot (D.Γ * A) v -
            ((D.Γ * A).trace).re))) -
          (r v * fderiv ℝ ρ v (D.Γ *ᵥ v) - 2 * (r v * ρ v * (N * quadQuot D.Γ v -
            (D.Γ.trace).re)) + ρ v * fderiv ℝ r v (D.Γ *ᵥ v)) := by
    intro v hv1
    have hv : v ≠ 0 := by intro h0; rw [h0] at hv1; simp [normSqSum] at hv1
    have hdE := (dAt D.expo_c1 v hv).hasFDerivAt.exp
    have hdρ : HasFDerivAt (fun y => Real.exp (D.expo y) * Z y * F y)
        ((Real.exp (D.expo v) * Z v) • fderiv ℝ F v + F v • (Real.exp (D.expo v) • fderiv ℝ Z v +
          Z v • (Real.exp (D.expo v) • fderiv ℝ D.expo v))) v :=
      (hdE.mul (dAt hZc v hv).hasFDerivAt).mul (dAt hFc v hv).hasFDerivAt
    have h2 : fderiv ℝ ρ v (D.field A v) = E v * Z v * fderiv ℝ F v (D.field A v) +
        F v * (E v * fderiv ℝ Z v (D.field A v) +
          Z v * (E v * fderiv ℝ D.expo v (D.field A v))) := by
      rw [show ρ = fun y => Real.exp (D.expo y) * Z y * F y from rfl, hdρ.fderiv]
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
      ring
    have h1 := D.fderiv_field_apply (G := ρ) A v
    have h3 := D.fderiv_expo_field A hA hv1 (dAt D.expo_c1 v hv)
    have h4 := D.ratio_mul_u₀ A hv
    unfold u₀ at h4
    have h5 := D.trace_Γ_re
    have hN0 : N ≠ 0 := by
      rw [hNdef]
      have : Nonempty ι := ⟨(Function.ne_iff.1 hv).choose⟩
      exact_mod_cast Fintype.card_ne_zero
    have hs0 := D.hs.ne'
    have hNinv : N * N⁻¹ = 1 := mul_inv_cancel₀ hN0
    simp only [hρ, hr] at h1 h2 ⊢
    rw [h3] at h2
    rw [← hNdef] at h5
    linear_combination (-1 : ℝ) * h2 + h1 + (-2 * N * (E v * Z v * F v)) * h4 +
      (2 * D.ratio A v * (E v * Z v * F v)) * h5 +
      (2 * (E v * Z v * F v) * ((D.Γ * A).trace).re) * hNinv
  -- integrability bookkeeping
  have hQ : ∀ M : Matrix ι ι ℂ, Bdd (quadQuot M) := fun M =>
    bdd_of_scaleInvariant (quadQuot_inv M) (contDiffOn_quadQuot M)
  have hQm : ∀ M : Matrix ι ι ℂ, Measurable (quadQuot M) := measurable_quadQuot
  have hEb : Bdd E := bdd_of_scaleInvariant hEi hEc
  have hZb : Bdd Z := bdd_of_scaleInvariant hZi hZc
  have hFb : Bdd F := bdd_of_scaleInvariant hFi hFc
  have hρb : Bdd ρ := bdd_of_scaleInvariant hρi hρc
  have hrb : Bdd r := bdd_of_scaleInvariant (D.ratio_inv A) (D.ratio_c1 A)
  have hrm : Measurable r := D.ratio_meas A
  have hDW : ∀ G : (ι → ℂ) → ℝ, IsScaleInvariant G → ContDiffOn ℝ 1 G {z | z ≠ 0} →
      Bdd (fun v => fderiv ℝ G v (D.field A v)) ∧
        Measurable (fun v => fderiv ℝ G v (D.field A v)) := by
    intro G hGi hGc
    have e : (fun v => fderiv ℝ G v (D.field A v)) = fun v =>
        fderiv ℝ G v ((D.Γ * A) *ᵥ v) - D.ratio A v * fderiv ℝ G v (D.Γ *ᵥ v) :=
      funext fun v => D.fderiv_field_apply A v
    rw [e]
    exact ⟨(bdd_fderiv hGi hGc _).sub (hrb.mul (bdd_fderiv hGi hGc _)),
      (measurable_fderiv_mulVec G _).sub (hrm.mul (measurable_fderiv_mulVec G _))⟩
  obtain ⟨hDFb, hDFm⟩ := hDW F hFi hFc
  obtain ⟨hDZb, hDZm⟩ := hDW Z hZi hZc
  have I : ∀ {G : (ι → ℂ) → ℝ}, Bdd G → Measurable G → Integrable G (projectiveHaar ι) :=
    fun hb hm => hb.integrable hm
  -- the five pieces of the right side and the four of the left side
  have iR1 : Integrable (fun v => fderiv ℝ ρ v ((D.Γ * A) *ᵥ v)) (projectiveHaar ι) := I (bdd_fderiv hρi hρc (D.Γ * A)) (measurable_fderiv_mulVec ρ (D.Γ * A))
  have iR2 : Integrable (fun v => ρ v * (N * quadQuot (D.Γ * A) v - ((D.Γ * A).trace).re))
      (projectiveHaar ι) := I (hρb.mul ((bdd_const N).mul (hQ (D.Γ * A)) |>.sub (bdd_const _)))
    (hρm.mul ((measurable_const.mul (hQm _)).sub measurable_const))
  have iR3 : Integrable (fun v => r v * fderiv ℝ ρ v (D.Γ *ᵥ v)) (projectiveHaar ι) := I (hrb.mul (bdd_fderiv hρi hρc D.Γ)) (hrm.mul (measurable_fderiv_mulVec ρ D.Γ))
  have iR4 : Integrable (fun v => r v * ρ v * (N * quadQuot D.Γ v - (D.Γ.trace).re))
      (projectiveHaar ι) := I ((hrb.mul hρb).mul ((bdd_const N).mul (hQ D.Γ) |>.sub (bdd_const _)))
    ((hrm.mul hρm).mul ((measurable_const.mul (hQm _)).sub measurable_const))
  have iR5 : Integrable (fun v => ρ v * fderiv ℝ r v (D.Γ *ᵥ v)) (projectiveHaar ι) := I (hρb.mul (bdd_fderiv (D.ratio_inv A) (D.ratio_c1 A) D.Γ))
    (hρm.mul (measurable_fderiv_mulVec r D.Γ))
  have iT1 : Integrable (fun v => E v * (Z v * fderiv ℝ F v (D.field A v) +
      F v * fderiv ℝ Z v (D.field A v))) (projectiveHaar ι) := I (hEb.mul ((hZb.mul hDFb).add (hFb.mul hDZb)))
    (hEm.mul ((hZm.mul hDFm).add (hFm.mul hDZm)))
  have iT3 : Integrable (fun v => ρ v * ((D.a v - aStar D.ζ) * D.corr A v))
      (projectiveHaar ι) := I (hρb.mul ((((hQ D.K).sub (bdd_const _))).mul
      (bdd_of_scaleInvariant (D.corr_inv A) (D.corr_c1 A))))
    (hρm.mul ((((hQm _).sub measurable_const)).mul (D.corr_meas A)))
  have iT4 : Integrable (fun v => ρ v * (quadQuot A v - N⁻¹ * ((D.Γ * A).trace).re))
      (projectiveHaar ι) := I (hρb.mul ((hQ A).sub (bdd_const _)))
    (hρm.mul ((hQm A).sub measurable_const))
  -- the right side integrates to zero
  have hR : (∫ v, ((fderiv ℝ ρ v ((D.Γ * A) *ᵥ v) - 2 * (ρ v * (N * quadQuot (D.Γ * A) v -
            ((D.Γ * A).trace).re))) -
          (r v * fderiv ℝ ρ v (D.Γ *ᵥ v) - 2 * (r v * ρ v * (N * quadQuot D.Γ v -
            (D.Γ.trace).re)) + ρ v * fderiv ℝ r v (D.Γ *ᵥ v))) ∂projectiveHaar ι) = 0 := by
    have hc2 : Integrable (fun v => 2 * (ρ v * (N * quadQuot (D.Γ * A) v -
        ((D.Γ * A).trace).re))) (projectiveHaar ι) := iR2.const_mul 2
    have hc4 : Integrable (fun v => 2 * (r v * ρ v * (N * quadQuot D.Γ v - (D.Γ.trace).re)))
        (projectiveHaar ι) := iR4.const_mul 2
    have hA1 : Integrable (fun v => fderiv ℝ ρ v ((D.Γ * A) *ᵥ v) - 2 * (ρ v *
        (N * quadQuot (D.Γ * A) v - ((D.Γ * A).trace).re))) (projectiveHaar ι) := iR1.sub hc2
    have hA2 : Integrable (fun v => r v * fderiv ℝ ρ v (D.Γ *ᵥ v) - 2 * (r v * ρ v *
        (N * quadQuot D.Γ v - (D.Γ.trace).re))) (projectiveHaar ι) := iR3.sub hc4
    have hA3 : Integrable (fun v => r v * fderiv ℝ ρ v (D.Γ *ᵥ v) - 2 * (r v * ρ v *
        (N * quadQuot D.Γ v - (D.Γ.trace).re)) + ρ v * fderiv ℝ r v (D.Γ *ᵥ v))
        (projectiveHaar ι) := hA2.add iR5
    rw [integral_sub hA1 hA3, integral_sub iR1 hc2, integral_add hA2 iR5,
      integral_sub iR3 hc4, integral_const_mul, integral_const_mul]
    rw [← hNdef] at S1 S2
    rw [S1, S2]
    ring
  -- hence the left side integrates to zero
  have hL : (∫ v, (E v * (Z v * fderiv ℝ F v (D.field A v) + F v * fderiv ℝ Z v (D.field A v)) -
          ρ v * fderiv ℝ r v (D.Γ *ᵥ v) + 2 * N / D.s * (ρ v * ((D.a v - aStar D.ζ) *
            D.corr A v)) - 2 * N * (ρ v * (quadQuot A v - N⁻¹ * ((D.Γ * A).trace).re)))
          ∂projectiveHaar ι) = 0 := by
    rw [← hR]
    exact integral_congr_ae (by filter_upwards [ae_projectiveHaar_unit] with v hv; exact hpt v hv)
  have hc3 : Integrable (fun v => 2 * N / D.s * (ρ v * ((D.a v - aStar D.ζ) * D.corr A v)))
      (projectiveHaar ι) := iT3.const_mul _
  have hc4' : Integrable (fun v => 2 * N * (ρ v * (quadQuot A v - N⁻¹ * ((D.Γ * A).trace).re)))
      (projectiveHaar ι) := iT4.const_mul _
  have hB1 : Integrable (fun v => E v * (Z v * fderiv ℝ F v (D.field A v) +
      F v * fderiv ℝ Z v (D.field A v)) - ρ v * fderiv ℝ r v (D.Γ *ᵥ v)) (projectiveHaar ι) :=
    iT1.sub iR5
  have hB2 : Integrable (fun v => E v * (Z v * fderiv ℝ F v (D.field A v) +
      F v * fderiv ℝ Z v (D.field A v)) - ρ v * fderiv ℝ r v (D.Γ *ᵥ v) +
      2 * N / D.s * (ρ v * ((D.a v - aStar D.ζ) * D.corr A v))) (projectiveHaar ι) :=
    hB1.add hc3
  rw [integral_sub hB2 hc4', integral_add hB1 hc3, integral_sub iT1 iR5, integral_const_mul,
    integral_const_mul] at hL
  simp only [hρ, hE] at hL ⊢
  linarith

end AngularData

end BlockBand.Angular.Stein
