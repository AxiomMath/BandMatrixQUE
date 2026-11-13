module

public import BlockBand.Angular.RatioDeriv

/-!
# The pointwise divergence inequality of the angular ratio lemma

At a unit vector, the integrand `W` of the projective Stein identity for the coefficient
`c = 1/h` times the field `ΓDv`, applied to `f = χ(b₂) qe e^{q}𝔷`, satisfies
`W + T_D c f ≤ G` (`pointwise_bound`): the divergence lower bound
`div Y ≥ T_D/h - (2N-1)‖𝓛Γv‖` (from `Re((ΓDv)*Dv) ≤ T_D h²`), the regression gradient
(`K₀²Γ = s + a_*K₀Γ - c_*Γ`), the cutoff gradient, the derivative of the regularized `q`
(`|Dq[Y]| ≤ CT_D + q‖𝓛Γv‖`) and the determinant gradient (`q‖𝓛Γ∇𝔷‖ ≤ CT_D‖∇𝔷‖`), all with
coefficients bounded on the cutoff `b₂ ≤ R₁`. The majorant `G` is quadratic in
`qe, ‖𝓛v‖, ‖𝓛ΓK₀v‖, ‖𝓛Γv‖` plus `T_D` times the density and `T_D χ‖∇𝔷‖`.
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

/-- A cutoff `χ(b₂)`: `C¹`, `0 ≤ χ ≤ M₀`, `|χ'| ≤ M₁`, `χ = 0` on `(R₁, ∞)`. -/
structure Cutoff where
  χ : ℝ → ℝ
  R₁ : ℝ
  M₀ : ℝ
  M₁ : ℝ
  smooth : ContDiff ℝ 1 χ
  nonneg : ∀ x, 0 ≤ χ x
  le : ∀ x, χ x ≤ M₀
  deriv_le : ∀ x, |deriv χ x| ≤ M₁
  supp : ∀ x, R₁ < x → χ x = 0

namespace Cutoff

variable (X : Cutoff)

theorem M₀_nonneg : 0 ≤ X.M₀ := (X.nonneg 0).trans (X.le 0)

theorem M₁_nonneg : 0 ≤ X.M₁ := (abs_nonneg _).trans (X.deriv_le 0)

theorem deriv_eq_zero {x : ℝ} (hx : X.R₁ < x) : deriv X.χ x = 0 := by
  have h : X.χ =ᶠ[nhds x] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun y hy => X.supp y hy
  rw [h.deriv_eq, deriv_const]

end Cutoff

/-- `Λ = σ + 2Zb + Zb² + |R₁| + 1` bounds every coefficient on the cutoff. -/
def Λc (σ Zb R₁ : ℝ) : ℝ := σ + 2 * Zb + Zb ^ 2 + |R₁| + 1

/-- `K₁ = 4M₀ + 2M₁Λ + 4σΛ²M₀`. -/
def K1c (σ Zb : ℝ) (X : Cutoff) : ℝ :=
  4 * X.M₀ + 2 * X.M₁ * Λc σ Zb X.R₁ + 4 * σ * Λc σ Zb X.R₁ ^ 2 * X.M₀

/-- `K₄ = Y(1 + σ²c_A + σ)`. -/
def K4c (σ Y cA : ℝ) : ℝ := Y * (1 + σ ^ 2 * cA + σ)

variable (D : AngularData ι) (L : Matrix κ ι ℂ)

/-- `ε² = T_D/N`. -/
def eps2 : ℝ := TD D L / Fintype.card ι

/-- The Stein integrand `2cf(NQ_B - Re Tr B) - f Dc[Bv] - c Df[Bv]`, `B = ΓD`. -/
def Wfun (X : Cutoff) (Zf : (ι → ℂ) → ℝ) (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  2 * (cfun L v * ffun D L X.χ Zf A (eps2 D L) v *
      ((Fintype.card ι : ℝ) * quadQuot (D.Γ * Dm L) v - ((D.Γ * Dm L).trace).re)) -
    ffun D L X.χ Zf A (eps2 D L) v * fderiv ℝ (cfun L) v ((D.Γ * Dm L) *ᵥ v) -
    cfun L v * fderiv ℝ (ffun D L X.χ Zf A (eps2 D L)) v ((D.Γ * Dm L) *ᵥ v)

/-- The majorant `G`. -/
def Gfun (σ Y Zb cA : ℝ) (X : Cutoff) (Zf : (ι → ℂ) → ℝ) (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (Fintype.card ι : ℝ) * K1c σ Zb X * (Real.exp (D.expo v) * Zf v) *
      (3 * (normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + eps2 D L) + normSqSum (L *ᵥ v) +
        normSqSum (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) + normSqSum (L *ᵥ (D.Γ *ᵥ v))) +
    X.M₀ * (TD D L * (σ * Y * (1 + cA))) * (Real.exp (D.expo v) * Zf v) +
    TD D L * K4c σ Y cA * (Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v)

theorem b₂_unit {v : ι → ℂ} (hv : normSqSum v = 1) : D.b₂ v = normSqSum (D.K *ᵥ v) := by
  rw [AngularData.b₂, quadQuot_of_unit hv]
  have : D.K * D.K = D.Kᴴ * D.K := by rw [D.hK.eq]
  rw [this, quadNum_conjTranspose_mul_self]

theorem a_sq_le_b₂ {v : ι → ℂ} (hv : normSqSum v = 1) : D.a v ^ 2 ≤ D.b₂ v := by
  rw [b₂_unit D hv, AngularData.a, quadQuot_of_unit hv, ← AngularData.reInner_mulVec_self]
  have h := abs_reInner_le v (D.K *ᵥ v)
  rw [l2Norm_eq v, hv, Real.sqrt_one, one_mul] at h
  calc reInner v (D.K *ᵥ v) ^ 2 = |reInner v (D.K *ᵥ v)| ^ 2 := (sq_abs _).symm
    _ ≤ l2Norm (D.K *ᵥ v) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := l2Norm_sq _

theorem Fd_pos [Nonempty ι] (hL : ∀ x, L *ᵥ x = 0 → x = 0) : 0 < Fd D L := by
  rcases (Fd_nonneg D L).lt_or_eq with h | h
  · exact h
  exfalso
  have hk : ∀ k, Rz D *ᵥ ell L k = 0 := by
    intro k
    have h0 : normSqSum (Rz D *ᵥ ell L k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => normSqSum_nonneg _)).1 h.symm k
        (Finset.mem_univ k)
    by_contra hne; exact (normSqSum_pos hne).ne' h0
  have hl : ∀ k, ell L k = 0 := by
    intro k
    have e := resolvent_mul D.hK D.hz
    calc ell L k = ((D.K - D.ζ • (1 : Matrix ι ι ℂ)) * Rz D) *ᵥ ell L k := by
          rw [Rz, e, one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hk k, mulVec_zero]
  have hL0 : ∀ x, L *ᵥ x = 0 := by
    intro x; funext k
    have hz : ∀ j, L k j = 0 := fun j => by
      have := congrFun (hl k) j; simpa [ell] using this
    simp [mulVec, dotProduct, hz]
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 := congrFun (hL (Pi.single i 1) (hL0 _)) i
  simp at h1

theorem abs_mul_le_of {x y U V : ℝ} (hx : |x| ≤ U) (hy : |y| ≤ V) : |x * y| ≤ U * V := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (|x| - 1)]

theorem sc_cDb {s h a p2 c p1 b Λ gK g1 : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) (hsΛ : s ≤ Λ)
    (ha : |a| ≤ Λ) (hp2 : |p2| ≤ gK) (hc : 0 ≤ c) (hb : 0 ≤ b) (hcb : c + b ≤ Λ)
    (hp1 : |p1| ≤ g1) (hg1 : 0 ≤ g1) :
    |2 * (s * h + a * p2 - c * p1) - 2 * b * p1| ≤ 2 * Λ * (h + gK + g1) := by
  have t1 := abs_le.1 (abs_mul_le_of ha hp2)
  have t2 := abs_le.1 (abs_mul_le_of (abs_of_nonneg hc).le hp1)
  have t3 := abs_le.1 (abs_mul_le_of (abs_of_nonneg hb).le hp1)
  have t4 : s * h ≤ Λ * h := mul_le_mul_of_nonneg_right hsΛ hh
  have t5 : (c + b) * g1 ≤ Λ * g1 := mul_le_mul_of_nonneg_right hcb hg1
  have t6 : 0 ≤ s * h := mul_nonneg hs hh
  rw [abs_le]; constructor <;> nlinarith

theorem sc_cDa {a p2 p1 Λ h gK g1 : ℝ} (hΛ1 : 1 ≤ Λ) (hh : 0 ≤ h) (hgK : 0 ≤ gK)
    (hp2 : |p2| ≤ gK) (ha : |a| ≤ Λ) (hp1 : |p1| ≤ g1) :
    |2 * p2 - 2 * a * p1| ≤ 2 * Λ * (h + gK + g1) := by
  have t1 := abs_le.1 hp2
  have t2 := abs_le.1 (abs_mul_le_of ha hp1)
  have t3 : gK ≤ Λ * gK := le_mul_of_one_le_left hgK hΛ1
  have t4 : 0 ≤ Λ * h := mul_nonneg (by linarith) hh
  rw [abs_le]; constructor <;> nlinarith

theorem sc_cDq {p5 q p1 qv Fa g1 : ℝ} (hqv : 0 < qv) (hq0 : 0 ≤ q) (hqq : q ≤ qv)
    (hFa0 : 0 ≤ Fa) (hg1 : 0 ≤ g1) (hp5 : |p5| ≤ Fa * q) (hp1 : |p1| ≤ g1) :
    |(p5 - q ^ 2 * p1) / qv| ≤ Fa + qv * g1 := by
  rw [abs_div, abs_of_pos hqv, div_le_iff₀ hqv]
  have t1 := abs_le.1 hp5
  have t2 := abs_le.1 (abs_mul_le_of (abs_of_nonneg (sq_nonneg q)).le hp1)
  have t3 : Fa * q ≤ Fa * qv := mul_le_mul_of_nonneg_left hqq hFa0
  have t4 : q ^ 2 * g1 ≤ qv ^ 2 * g1 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hqq 2) hg1
  rw [abs_le]; constructor <;> nlinarith

theorem sc_X (qv h gK g1 : ℝ) : qv * (h + gK + g1) ≤ 3 * qv ^ 2 + h ^ 2 + gK ^ 2 + g1 ^ 2 := by
  nlinarith [sq_nonneg (qv - h), sq_nonneg (qv - gK), sq_nonneg (qv - g1), sq_nonneg qv]

theorem sc_coef {N M₀ M₁ Λ σ : ℝ} (hN1 : 1 ≤ N) (hM0 : 0 ≤ M₀) (hM1 : 0 ≤ M₁) (hΛ : 0 ≤ Λ) :
    2 * N * M₀ + 2 * M₁ * Λ + M₀ + 4 * M₀ * Λ ^ 2 * N * σ ≤
      N * (4 * M₀ + 2 * M₁ * Λ + 4 * σ * Λ ^ 2 * M₀) := by
  have h1 : M₀ ≤ N * M₀ := le_mul_of_one_le_left hM0 hN1
  have h2 : 2 * M₁ * Λ ≤ N * (2 * M₁ * Λ) := le_mul_of_one_le_left (by positivity) hN1
  nlinarith

set_option maxHeartbeats 1000000 in
theorem pointwise_bound [Nonempty ι] (hL : ∀ x, L *ᵥ x = 0 → x = 0) {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {cA : ℝ} (hcA0 : 0 ≤ cA)
    (hcA : ∀ x, normSqSum (Rz D *ᵥ (A *ᵥ x)) ≤ cA * normSqSum x)
    {σ Y Zb : ℝ} (hs1 : D.s ≤ σ) (hs2 : D.s⁻¹ ≤ σ) (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb)
    (X : Cutoff) {Zf : (ι → ℂ) → ℝ} (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0})
    (hZ0 : ∀ v, 0 ≤ Zf v) {v : ι → ℂ} (hv : normSqSum v = 1) :
    Wfun D L X Zf A v + TD D L * (cfun L v * ffun D L X.χ Zf A (eps2 D L) v) ≤
      Gfun D L σ Y Zb cA X Zf A v := by
  have hv0 : v ≠ 0 := ne_zero_of_unit hv
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  have hs := D.hs
  have hF := Fd_nonneg D L
  have hTD : 0 ≤ TD D L := mul_nonneg hs.le hF
  have hY0 : 0 ≤ Y := (inv_nonneg.2 (im_pos D).le).trans hY
  have hZb0 : 0 ≤ Zb := (norm_nonneg _).trans hZb
  have hσ1 : 1 ≤ σ := by
    by_contra hlt; push Not at hlt
    have h1 : D.s < 1 := lt_of_le_of_lt hs1 hlt
    have h2 : 1 < D.s⁻¹ := (one_lt_inv₀ hs).2 h1
    linarith
  have hε : 0 < eps2 D L := div_pos (mul_pos hs (Fd_pos D L hL)) (by linarith)
  have hεle : eps2 D L ≤ TD D L := div_le_self hTD hN1
  have hM0 := X.M₀_nonneg
  have hM1 := X.M₁_nonneg
  -- scalar data at `v`
  set h := l2Norm (L *ᵥ v) with hhdef
  have hh : 0 < h := ConeDivergence.l2Norm_pos fun h0 => hv0 (hL v h0)
  have hh2 : h ^ 2 = normSqSum (L *ᵥ v) := l2Norm_sq _
  have hQD : quadQuot (Dm L) v = h ^ 2 := by rw [quadQuot_of_unit hv, quadNum_Dm, hh2]
  have hc : cfun L v = h⁻¹ := by rw [cfun, hQD, Real.sqrt_sq hh.le]
  set q := l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) with hqdef
  have hq0 : 0 ≤ q := l2Norm_nonneg _
  have hq2 : q ^ 2 = normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) := l2Norm_sq _
  have hQB' : quadQuot (Bq D L A) v = q ^ 2 := by rw [quadQuot_of_unit hv, quadNum_Bq, hq2]
  set qv := qe D L A (eps2 D L) v with hqvdef
  have hqv : 0 < qv := qe_pos D L A hε v
  have hqv2 : qv ^ 2 = q ^ 2 + eps2 D L := by
    rw [hqvdef, qe, hQB', Real.sq_sqrt (by positivity)]
  have hqqv : q ≤ qv := (pow_le_pow_iff_left₀ hq0 hqv.le two_ne_zero).1 (by rw [hqv2]; linarith)
  set g1 := l2Norm (L *ᵥ (D.Γ *ᵥ v)) with hg1def
  set gK := l2Norm (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) with hgKdef
  have hg10 : 0 ≤ g1 := l2Norm_nonneg _
  have hgK0 : 0 ≤ gK := l2Norm_nonneg _
  set gn := gradNorm Zf v with hgndef
  have hgn0 : 0 ≤ gn := gradNorm_nonneg _ _
  set Bv := D.Γ *ᵥ (Dm L *ᵥ v) with hBvdef
  have hBv : (D.Γ * Dm L) *ᵥ v = Bv := by rw [← mulVec_mulVec]
  -- normalized pairings
  set p1 := h⁻¹ * reInner Bv v with hp1def
  set p2 := h⁻¹ * reInner Bv (D.K *ᵥ v) with hp2def
  have hI3 : reInner Bv v = h * p1 := by rw [hp1def]; field_simp
  have hI2 : reInner Bv (D.K *ᵥ v) = h * p2 := by rw [hp2def]; field_simp
  have habs_div : ∀ {x U : ℝ}, |x| ≤ h * U → |h⁻¹ * x| ≤ U := fun {x U} hx => by
    rw [abs_mul, abs_inv, abs_of_pos hh, inv_mul_le_iff₀ hh]; exact hx
  have hp1 : |p1| ≤ g1 := habs_div (by rw [hBvdef, reInner_ΓD]; exact abs_reInner_le _ _)
  have hp2 : |p2| ≤ gK := habs_div (by rw [hBvdef, reInner_ΓD]; exact abs_reInner_le _ _)
  have hI4 : reInner Bv (Dm L *ᵥ v) ≤ TD D L * h ^ 2 := by
    rw [hh2]; exact reInner_ΓD_D_le D L v
  have hI1 : reInner Bv ((D.K * D.K) *ᵥ v) =
      D.s * h ^ 2 + aStar D.ζ * (h * p2) - cStar D.ζ * (h * p1) := by
    rw [hBvdef, reInner_ΓD_KK, ← hh2, ← reInner_ΓD, ← reInner_ΓD, ← hBvdef, hI2, hI3]
  set p5 := h⁻¹ * reInner Bv (Bq D L A *ᵥ v) with hp5def
  have hI5 : reInner Bv (Bq D L A *ᵥ v) = h * p5 := by rw [hp5def]; field_simp
  set Fa := TD D L * (σ * Y * (1 + cA)) with hFadef
  have hFa0 : 0 ≤ Fa := by positivity
  have hp5 : |p5| ≤ Fa * q := by
    refine habs_div ((abs_reInner_ΓD_Bq D L hY hA hcA0 hcA v).trans ?_)
    rw [← hqdef, ← hhdef, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hq0) hh.le
    rw [hFadef, TD]
    have : D.s ^ 2 * Fd D L * Y * (1 + cA) = D.s * Fd D L * (D.s * Y * (1 + cA)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by gcongr) (mul_nonneg hs.le hF)
  set m := l2Norm (L *ᵥ (D.Γ *ᵥ grad Zf v)) with hmdef
  have hm0 : 0 ≤ m := l2Norm_nonneg _
  set pZ := h⁻¹ * fderiv ℝ Zf v Bv with hpZdef
  have hpZ : |pZ| ≤ m := habs_div (by
    rw [fderiv_eq_reInner_grad, hBvdef, reInner_ΓD]; exact abs_reInner_le _ _)
  have hQB : quadQuot (D.Γ * Dm L) v = reInner Bv v := by
    rw [quadQuot_of_unit hv, ← AngularData.reInner_mulVec_self, hBv, reInner_comm]
  have htr : ((D.Γ * Dm L).trace).re = TD D L := trace_ΓD D L
  -- derivatives
  have hKK : (D.K * D.K).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, D.hK.eq]
  have hDc : fderiv ℝ (cfun L) v Bv = -(h ^ 2)⁻¹ * ((1 / (2 * h)) *
      (2 * reInner Bv (Dm L *ᵥ v) - 2 * h ^ 2 * reInner Bv v)) := by
    rw [fderiv_cfun L hL hv0, fderiv_quadQuot_apply (Dm_isHermitian L) hv, hQD,
      Real.sqrt_sq hh.le]
  have hDb : fderiv ℝ D.b₂ v Bv = 2 * reInner Bv ((D.K * D.K) *ᵥ v) -
      2 * D.b₂ v * reInner Bv v := fderiv_quadQuot_apply hKK hv Bv
  have hDa : fderiv ℝ D.a v Bv = 2 * reInner Bv (D.K *ᵥ v) - 2 * D.a v * reInner Bv v :=
    fderiv_quadQuot_apply D.hK hv Bv
  have hDe := fderiv_expo D hv0 Bv
  have hDq : fderiv ℝ (qe D L A (eps2 D L)) v Bv = (1 / (2 * qv)) *
      (2 * reInner Bv (Bq D L A *ᵥ v) - 2 * q ^ 2 * reInner Bv v) := by
    rw [fderiv_qe D L A hε hv0, fderiv_quadQuot_apply (Bq_isHermitian D L A) hv, hQB']
  have hDf := fderiv_ffun D L X.smooth hZc A hε hv0 Bv
  set χb := X.χ (D.b₂ v) with hχbdef
  set χd := deriv X.χ (D.b₂ v) with hχddef
  set ρ := Real.exp (D.expo v) * Zf v with hρdef
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.exp_pos _).le (hZ0 v)
  have hχb0 : 0 ≤ χb := X.nonneg _
  have hfv : ffun D L X.χ Zf A (eps2 D L) v = χb * qv * ρ := rfl
  have hK1 : 0 ≤ K1c σ Zb X := by unfold K1c Λc; positivity
  have hK4 : 0 ≤ K4c σ Y cA := by unfold K4c; positivity
  have hG0 : 0 ≤ Gfun D L σ Y Zb cA X Zf A v := by
    unfold Gfun
    have := normSqSum_nonneg (L *ᵥ (D.Γ *ᵥ (A *ᵥ v)))
    have := normSqSum_nonneg (L *ᵥ v)
    have := normSqSum_nonneg (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v)))
    have := normSqSum_nonneg (L *ᵥ (D.Γ *ᵥ v))
    have := (Real.exp_pos (D.expo v)).le
    have := hZ0 v
    positivity
  by_cases hsupp : D.b₂ v ≤ |X.R₁|
  swap
  · push Not at hsupp
    have hR : X.R₁ < D.b₂ v := lt_of_le_of_lt (le_abs_self _) hsupp
    have h0 : χb = 0 := X.supp _ hR
    have h0' : χd = 0 := X.deriv_eq_zero hR
    have hf0 : ffun D L X.χ Zf A (eps2 D L) v = 0 := by rw [hfv, h0]; ring
    have hW0 : Wfun D L X Zf A v = 0 := by
      unfold Wfun; rw [hf0, hBv, hDf, h0, h0']; ring
    rw [hW0, hf0]; simpa using hG0
  -- coefficient bounds on the cutoff
  have hb0 : 0 ≤ D.b₂ v := by rw [b₂_unit D hv]; exact normSqSum_nonneg _
  have ha2 := a_sq_le_b₂ D hv
  set Λ := Λc σ Zb X.R₁ with hΛdef
  have hR0 := abs_nonneg X.R₁
  have hZ2 := sq_nonneg Zb
  have hΛ1 : 1 ≤ Λ := by rw [hΛdef, Λc]; linarith
  have hsΛ : D.s ≤ Λ := by rw [hΛdef, Λc]; linarith
  have haS : |aStar D.ζ| ≤ Λ := by
    have : |aStar D.ζ| ≤ 2 * Zb := by
      rw [aStar, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hZb) zero_le_two
    rw [hΛdef, Λc]; linarith
  have hcS0 : 0 ≤ cStar D.ζ := Complex.normSq_nonneg _
  have hcb : cStar D.ζ + D.b₂ v ≤ Λ := by
    have : cStar D.ζ ≤ Zb ^ 2 := by
      rw [cStar, Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hZb 2
    rw [hΛdef, Λc]; linarith
  have ha : |D.a v| ≤ Λ := by
    have h1 := abs_le_one_add_sq (D.a v)
    rw [hΛdef, Λc]; linarith
  set H := h + gK + g1 with hHdef
  have hH0 : 0 ≤ H := by positivity
  -- normalized derivatives
  have hcDb : |h⁻¹ * fderiv ℝ D.b₂ v Bv| ≤ 2 * Λ * H := by
    have e : h⁻¹ * fderiv ℝ D.b₂ v Bv =
        2 * (D.s * h + aStar D.ζ * p2 - cStar D.ζ * p1) - 2 * D.b₂ v * p1 := by
      rw [hDb, hI1, hI3]; field_simp
    rw [e]; exact sc_cDb hh.le hs.le hsΛ haS hp2 hcS0 hb0 hcb hp1 hg10
  have hcDa : |h⁻¹ * fderiv ℝ D.a v Bv| ≤ 2 * Λ * H := by
    have e : h⁻¹ * fderiv ℝ D.a v Bv = 2 * p2 - 2 * D.a v * p1 := by
      rw [hDa, hI2, hI3]; field_simp
    rw [e]; exact sc_cDa hΛ1 hh.le hgK0 hp2 ha hp1
  have hcDe : |h⁻¹ * fderiv ℝ D.expo v Bv| ≤ 4 * Λ ^ 2 * H * (N * σ) := by
    have e : h⁻¹ * fderiv ℝ D.expo v Bv = (-(h⁻¹ * fderiv ℝ D.b₂ v Bv) +
        D.a v * (h⁻¹ * fderiv ℝ D.a v Bv)) * (N * D.s⁻¹) := by
      rw [hDe, AngularData.t, ← hNdef]; field_simp
    rw [e, abs_mul]
    have hN0 : 0 ≤ N * D.s⁻¹ := by positivity
    rw [abs_of_nonneg hN0]
    have h1 : |-(h⁻¹ * fderiv ℝ D.b₂ v Bv) + D.a v * (h⁻¹ * fderiv ℝ D.a v Bv)| ≤
        2 * Λ * H + Λ * (2 * Λ * H) := by
      refine (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]; exact hcDb) ?_)
      exact abs_mul_le_of ha hcDa
    have h2 : 2 * Λ * H + Λ * (2 * Λ * H) ≤ 4 * Λ ^ 2 * H := by
      have h4 : Λ * H ≤ Λ ^ 2 * H :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ hΛ1 two_ne_zero) hH0
      calc 2 * Λ * H + Λ * (2 * Λ * H) = 2 * (Λ * H) + 2 * (Λ ^ 2 * H) := by ring
        _ ≤ 2 * (Λ ^ 2 * H) + 2 * (Λ ^ 2 * H) := by linarith
        _ = 4 * Λ ^ 2 * H := by ring
    have h3 : N * D.s⁻¹ ≤ N * σ := mul_le_mul_of_nonneg_left hs2 (by linarith)
    calc _ ≤ (4 * Λ ^ 2 * H) * (N * D.s⁻¹) := mul_le_mul_of_nonneg_right (h1.trans h2) hN0
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hcDq : |h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv| ≤ Fa + qv * g1 := by
    have e : h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv = (p5 - q ^ 2 * p1) / qv := by
      rw [hDq, hI5, hI3]; field_simp
    rw [e]; exact sc_cDq hqv hq0 hqqv hFa0 hg10 hp5 hp1
  have hcDZ : qv * |pZ| ≤ TD D L * K4c σ Y cA * gn := by
    have hm2 : m ^ 2 ≤ D.s ^ 2 * Fd D L * Y ^ 2 * gn ^ 2 := by
      rw [hmdef, l2Norm_sq, hgndef, gradNorm, l2Norm_sq]; exact LΓ_bound' D L hY _
    have hqb : q ^ 2 ≤ D.s ^ 2 * Fd D L * cA := by
      have := LΓM_bound D L hcA v; rw [hv, mul_one] at this; rw [hq2]; exact this
    have hqv2' : qv ^ 2 ≤ D.s ^ 2 * Fd D L * cA + D.s * Fd D L := by
      rw [hqv2]; have := hεle; rw [TD] at this; linarith
    have hprod : (qv * m) ^ 2 ≤ (TD D L * Y * gn) ^ 2 * (D.s ^ 2 * cA + D.s) := by
      rw [mul_pow, TD]
      calc qv ^ 2 * m ^ 2 ≤ (D.s ^ 2 * Fd D L * cA + D.s * Fd D L) *
            (D.s ^ 2 * Fd D L * Y ^ 2 * gn ^ 2) :=
            mul_le_mul hqv2' hm2 (sq_nonneg _) (by positivity)
        _ = _ := by ring
    have h1 := le_mul_one_add_of_sq_le (by positivity) (by positivity) (by positivity) hprod
    have h2 : qv * |pZ| ≤ qv * m := mul_le_mul_of_nonneg_left hpZ hqv.le
    have h3 : 1 + (D.s ^ 2 * cA + D.s) ≤ 1 + σ ^ 2 * cA + σ := by
      have : D.s ^ 2 * cA ≤ σ ^ 2 * cA :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hs1 2) hcA0
      linarith
    calc qv * |pZ| ≤ TD D L * Y * gn * (1 + (D.s ^ 2 * cA + D.s)) := h2.trans h1
      _ ≤ TD D L * Y * gn * (1 + σ ^ 2 * cA + σ) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by rw [K4c]; ring
  -- exact form of `W + T_D c f`
  set I4 := reInner Bv (Dm L *ᵥ v) with hI4def
  set E := Real.exp (D.expo v) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hρE : ρ = E * Zf v := rfl
  have hWeq : Wfun D L X Zf A v + TD D L * (cfun L v * ffun D L X.χ Zf A (eps2 D L) v) =
      (2 * N - 1) * (χb * qv * ρ) * p1 + χb * qv * ρ * (I4 / h ^ 3 - TD D L / h) -
        (χd * (h⁻¹ * fderiv ℝ D.b₂ v Bv) * qv * ρ +
          χb * (h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv) * ρ +
          χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v + E * pZ)) := by
    unfold Wfun
    rw [hfv, hc, hQB, htr, hBv, hDc, hDf, hI3, hpZdef, ← hNdef]
    field_simp
    ring
  rw [hWeq]
  set S := qv * H * ρ with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hqg : qv * g1 * ρ ≤ S := by
    rw [hSdef]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hqv.le) hρ0
    rw [hHdef]; linarith
  have hfv0 : 0 ≤ χb * qv * ρ := by positivity
  have hχbM : χb ≤ X.M₀ := X.le _
  have hχdM : |χd| ≤ X.M₁ := X.deriv_le _
  -- the divergence term
  have hB1 : χb * qv * ρ * (I4 / h ^ 3 - TD D L / h) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos hfv0 ?_
    have e : I4 / h ^ 3 - TD D L / h = (I4 - TD D L * h ^ 2) / h ^ 3 := by field_simp
    rw [e]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hB2 : (2 * N - 1) * (χb * qv * ρ) * p1 ≤ 2 * N * X.M₀ * S := by
    have h1 : (χb * qv * ρ) * p1 ≤ (χb * qv * ρ) * g1 :=
      mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hp1) hfv0
    have h2 : χb * qv * ρ * g1 ≤ X.M₀ * S := by
      calc χb * qv * ρ * g1 = χb * (qv * g1 * ρ) := by ring
        _ ≤ X.M₀ * S := mul_le_mul hχbM hqg (by positivity) hM0
    have h3 : 0 ≤ 2 * N - 1 := by linarith
    calc (2 * N - 1) * (χb * qv * ρ) * p1 = (2 * N - 1) * ((χb * qv * ρ) * p1) := by ring
      _ ≤ (2 * N - 1) * (X.M₀ * S) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) h3
      _ ≤ 2 * N * X.M₀ * S := by
          have e : (2 * N - 1) * (X.M₀ * S) = 2 * N * X.M₀ * S - X.M₀ * S := by ring
          have := mul_nonneg hM0 hS0
          linarith
  -- the four derivative terms
  have hC1 : |χd * (h⁻¹ * fderiv ℝ D.b₂ v Bv) * qv * ρ| ≤ 2 * X.M₁ * Λ * S := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hqv, abs_of_nonneg hρ0]
    calc |χd| * |h⁻¹ * fderiv ℝ D.b₂ v Bv| * qv * ρ ≤ X.M₁ * (2 * Λ * H) * qv * ρ := by
          gcongr
      _ = 2 * X.M₁ * Λ * S := by rw [hSdef]; ring
  have hC2 : |χb * (h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv) * ρ| ≤
      X.M₀ * Fa * ρ + X.M₀ * S := by
    rw [abs_mul, abs_mul, abs_of_nonneg hχb0, abs_of_nonneg hρ0]
    calc χb * |h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv| * ρ ≤ X.M₀ * (Fa + qv * g1) * ρ := by
          gcongr
      _ = X.M₀ * Fa * ρ + X.M₀ * (qv * g1 * ρ) := by ring
      _ ≤ X.M₀ * Fa * ρ + X.M₀ * S := by gcongr
  have hC3 : |χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v)| ≤
      4 * X.M₀ * Λ ^ 2 * N * σ * S := by
    have e : χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v) =
        χb * (h⁻¹ * fderiv ℝ D.expo v Bv) * (qv * ρ) := by rw [hρE]; ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg hχb0, abs_of_nonneg (by positivity : 0 ≤ qv * ρ)]
    calc χb * |h⁻¹ * fderiv ℝ D.expo v Bv| * (qv * ρ) ≤
          X.M₀ * (4 * Λ ^ 2 * H * (N * σ)) * (qv * ρ) := by gcongr
      _ = 4 * X.M₀ * Λ ^ 2 * N * σ * S := by rw [hSdef]; ring
  have hC4 : |χb * qv * (E * pZ)| ≤ TD D L * K4c σ Y cA * (E * χb * gn) := by
    have e : χb * qv * (E * pZ) = (χb * E) * (qv * pZ) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ χb * E), abs_mul, abs_of_pos hqv]
    calc χb * E * (qv * |pZ|) ≤ χb * E * (TD D L * K4c σ Y cA * gn) := by gcongr
      _ = _ := by ring
  have hsum : -(χd * (h⁻¹ * fderiv ℝ D.b₂ v Bv) * qv * ρ +
          χb * (h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv) * ρ +
          χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v + E * pZ)) ≤
      2 * X.M₁ * Λ * S + (X.M₀ * Fa * ρ + X.M₀ * S) + 4 * X.M₀ * Λ ^ 2 * N * σ * S +
        TD D L * K4c σ Y cA * (E * χb * gn) := by
    have e : χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v + E * pZ) =
        χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v) + χb * qv * (E * pZ) := by ring
    rw [e]
    have := neg_abs_le (χd * (h⁻¹ * fderiv ℝ D.b₂ v Bv) * qv * ρ)
    have := neg_abs_le (χb * (h⁻¹ * fderiv ℝ (qe D L A (eps2 D L)) v Bv) * ρ)
    have := neg_abs_le (χb * qv * (E * (h⁻¹ * fderiv ℝ D.expo v Bv) * Zf v))
    have := neg_abs_le (χb * qv * (E * pZ))
    linarith
  -- comparison with the majorant
  have hX : qv * H ≤ 3 * qv ^ 2 + h ^ 2 + gK ^ 2 + g1 ^ 2 := by
    rw [hHdef]; exact sc_X qv h gK g1
  have hXs : 3 * qv ^ 2 + h ^ 2 + gK ^ 2 + g1 ^ 2 =
      3 * (normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + eps2 D L) + normSqSum (L *ᵥ v) +
        normSqSum (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) + normSqSum (L *ᵥ (D.Γ *ᵥ v)) := by
    rw [hqv2, hq2, hh2, hgKdef, hg1def, l2Norm_sq, l2Norm_sq]
  have hcoef : 2 * N * X.M₀ + 2 * X.M₁ * Λ + X.M₀ + 4 * X.M₀ * Λ ^ 2 * N * σ ≤
      N * K1c σ Zb X := by
    rw [K1c, ← hΛdef]; exact sc_coef hN1 hM0 hM1 (by linarith)
  have hfin : (2 * N * X.M₀ + 2 * X.M₁ * Λ + X.M₀ + 4 * X.M₀ * Λ ^ 2 * N * σ) * S ≤
      N * K1c σ Zb X * ρ * (3 * (normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + eps2 D L) +
        normSqSum (L *ᵥ v) + normSqSum (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) +
        normSqSum (L *ᵥ (D.Γ *ᵥ v))) := by
    rw [← hXs]
    calc (2 * N * X.M₀ + 2 * X.M₁ * Λ + X.M₀ + 4 * X.M₀ * Λ ^ 2 * N * σ) * S ≤
          N * K1c σ Zb X * S := mul_le_mul_of_nonneg_right hcoef hS0
      _ = N * K1c σ Zb X * ((qv * H) * ρ) := by rw [hSdef]
      _ ≤ N * K1c σ Zb X * ((3 * qv ^ 2 + h ^ 2 + gK ^ 2 + g1 ^ 2) * ρ) := by gcongr
      _ = _ := by ring
  have hGeq : Gfun D L σ Y Zb cA X Zf A v =
      N * K1c σ Zb X * ρ * (3 * (normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + eps2 D L) +
        normSqSum (L *ᵥ v) + normSqSum (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) +
        normSqSum (L *ᵥ (D.Γ *ᵥ v))) + X.M₀ * Fa * ρ +
      TD D L * K4c σ Y cA * (E * χb * gn) := by
    rw [Gfun, ← hNdef, ← hFadef]
  rw [hGeq]
  have hlin : 2 * N * X.M₀ * S + (2 * X.M₁ * Λ * S + (X.M₀ * Fa * ρ + X.M₀ * S) +
      4 * X.M₀ * Λ ^ 2 * N * σ * S) =
      (2 * N * X.M₀ + 2 * X.M₁ * Λ + X.M₀ + 4 * X.M₀ * Λ ^ 2 * N * σ) * S + X.M₀ * Fa * ρ := by
    ring
  linarith

end BlockBand.Angular.Ratio
