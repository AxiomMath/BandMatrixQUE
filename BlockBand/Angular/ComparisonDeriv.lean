module

public import BlockBand.Angular.ComparisonBounds

/-!
# Derivative bounds on the cutoff for the angular comparison

* `VB f B B'`: `|f 0| ≤ B` and `f` has a derivative at `0` of size `≤ B'`; closed under
  sums, products, constant multiples and quotients with a lower bound on the denominator.
* `abs_Delta_le`: `|Δ_A| = |Dr_A[Γv]| ≤ K_Δ` on the cutoff for `ΓA` bounded.
* `htil`: the function `b_J/(s g)` written as
  `(u₀ Re(v*JΓK₀v) - Re(v*ΓJv) u₁)/((u₁ - Re ζ u₀)² + (Im ζ)² u₀²)`; the two agree off the origin
  by the positive longitudinal identity (`htil_mul_gLong`: `h̃ g = b_J/s`).
* `abs_htil_le`, `abs_fderiv_htil_le`: `|h̃| ≤ K_h`, `|Dh̃[W_{K₀}]| ≤ K_{dh}` on the cutoff; the
  denominator is at least `(Im ζ)² u₀² ≥ Y⁻² (σP²)⁻²`.
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

/-!
## Value-and-derivative bounds along a line
-/

/-- `|f 0| ≤ B` and `f'(0)` exists with `|f'(0)| ≤ B'`. -/
def VB (f : ℝ → ℝ) (B B' : ℝ) : Prop := |f 0| ≤ B ∧ ∃ d, HasDerivAt f d 0 ∧ |d| ≤ B'

namespace VB

variable {f g : ℝ → ℝ} {B B' C C' : ℝ}

theorem nonneg (hf : VB f B B') : 0 ≤ B := (abs_nonneg _).trans hf.1

theorem nonneg' (hf : VB f B B') : 0 ≤ B' := by
  obtain ⟨-, d, -, hd⟩ := hf; exact (abs_nonneg _).trans hd

theorem mono (hf : VB f B B') {B₂ B₂' : ℝ} (h : B ≤ B₂) (h' : B' ≤ B₂') : VB f B₂ B₂' := by
  obtain ⟨h0, d, hd, hdb⟩ := hf; exact ⟨h0.trans h, d, hd, hdb.trans h'⟩

theorem add (hf : VB f B B') (hg : VB g C C') : VB (fun τ => f τ + g τ) (B + C) (B' + C') := by
  obtain ⟨h0, d, hd, hdb⟩ := hf; obtain ⟨k0, e, he, heb⟩ := hg
  exact ⟨(abs_add_le _ _).trans (add_le_add h0 k0), d + e, hd.add he,
    (abs_add_le _ _).trans (add_le_add hdb heb)⟩

theorem sub (hf : VB f B B') (hg : VB g C C') : VB (fun τ => f τ - g τ) (B + C) (B' + C') := by
  obtain ⟨h0, d, hd, hdb⟩ := hf; obtain ⟨k0, e, he, heb⟩ := hg
  exact ⟨(abs_sub _ _).trans (add_le_add h0 k0), d - e, hd.sub he,
    (abs_sub _ _).trans (add_le_add hdb heb)⟩

theorem mul (hf : VB f B B') (hg : VB g C C') :
    VB (fun τ => f τ * g τ) (B * C) (B' * C + B * C') := by
  have hB := hf.nonneg; have hB' := hf.nonneg'
  obtain ⟨h0, d, hd, hdb⟩ := hf; obtain ⟨k0, e, he, heb⟩ := hg
  refine ⟨?_, d * g 0 + f 0 * e, hd.mul he, ?_⟩
  · rw [abs_mul]; exact mul_le_mul h0 k0 (abs_nonneg _) hB
  · refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul hdb k0 (abs_nonneg _) hB'
    · exact mul_le_mul h0 heb (abs_nonneg _) hB

theorem const_mul_le (hf : VB f B B') {c c' : ℝ} (hc : |c| ≤ c') :
    VB (fun τ => c * f τ) (c' * B) (c' * B') := by
  have hB := hf.nonneg; have hB' := hf.nonneg'
  obtain ⟨h0, d, hd, hdb⟩ := hf
  refine ⟨?_, c * d, hd.const_mul c, ?_⟩ <;> rw [abs_mul]
  · exact mul_le_mul hc h0 (abs_nonneg _) ((abs_nonneg _).trans hc)
  · exact mul_le_mul hc hdb (abs_nonneg _) ((abs_nonneg _).trans hc)

theorem div (hf : VB f B B') (hg : VB g C C') {ℓ : ℝ} (hℓ : 0 < ℓ) (hg0 : ℓ ≤ g 0) :
    VB (fun τ => f τ / g τ) (B / ℓ) (B' / ℓ + B * C' / ℓ ^ 2) := by
  have hB := hf.nonneg; have hB' := hf.nonneg'; have hC' := hg.nonneg'
  obtain ⟨h0, d, hd, hdb⟩ := hf; obtain ⟨-, e, he, heb⟩ := hg
  have hgp : 0 < g 0 := hℓ.trans_le hg0
  refine ⟨?_, (d * g 0 - f 0 * e) / g 0 ^ 2, hd.div he hgp.ne', ?_⟩
  · rw [abs_div, abs_of_pos hgp]
    calc |f 0| / g 0 ≤ B / g 0 := div_le_div_of_nonneg_right h0 hgp.le
      _ ≤ B / ℓ := div_le_div_of_nonneg_left hB hℓ hg0
  · have e1 : (d * g 0 - f 0 * e) / g 0 ^ 2 = d / g 0 - f 0 * e / g 0 ^ 2 := by
      field_simp
    rw [e1]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos hgp]
      calc |d| / g 0 ≤ B' / g 0 := div_le_div_of_nonneg_right hdb hgp.le
        _ ≤ B' / ℓ := div_le_div_of_nonneg_left hB' hℓ hg0
    · rw [abs_div, abs_mul, abs_of_pos (pow_pos hgp 2)]
      have h2 : ℓ ^ 2 ≤ g 0 ^ 2 := pow_le_pow_left₀ hℓ.le hg0 2
      calc |f 0| * |e| / g 0 ^ 2 ≤ B * C' / g 0 ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul h0 heb (abs_nonneg _) hB) (by positivity)
        _ ≤ B * C' / ℓ ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) h2

end VB

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem abs_fderiv_le_of_VB {G : (ι → ℂ) → ℝ} {v w : ι → ℂ} (hG : DifferentiableAt ℝ G v)
    {B B' : ℝ} (h : VB (fun τ => G (v + τ • w)) B B') : |fderiv ℝ G v w| ≤ B' := by
  obtain ⟨-, d, hd, hb⟩ := h
  rw [AngularData.fderiv_apply_of_line hG hd]; exact hb

theorem abs_le_of_VB {G : (ι → ℂ) → ℝ} {v w : ι → ℂ} {B B' : ℝ}
    (h : VB (fun τ => G (v + τ • w)) B B') : |G v| ≤ B := by
  simpa using h.1

/-- A Rayleigh quotient with bounded matrix along a line through a unit vector. -/
theorem vb_quadQuot {M : Matrix ι ι ℂ} {m : ℝ} (hM : OpB M m) {v : ι → ℂ} (hv : normSqSum v = 1)
    (w : ι → ℂ) : VB (fun τ => quadQuot M (v + τ • w)) m (4 * m * l2Norm w) := by
  have hm : 0 ≤ m := by
    have := (l2Norm_nonneg _).trans (hM v); rwa [l2Norm_unit hv, mul_one] at this
  refine ⟨by simpa using abs_quadQuot_le_of_opB hM hv, _, hasDerivAt_quadQuot_line' M v w hv, ?_⟩
  have hw := l2Norm_nonneg w
  have h1 : |reInner w (M *ᵥ v)| ≤ l2Norm w * m :=
    (abs_reInner_le _ _).trans (mul_le_mul_of_nonneg_left
      (by simpa [l2Norm_unit hv] using hM v) hw)
  have h2 : |reInner v (M *ᵥ w)| ≤ m * l2Norm w := by
    refine (abs_reInner_le _ _).trans ?_
    rw [l2Norm_unit hv, one_mul]; exact hM w
  have h3 : |quadNum M v| ≤ m := by
    have := abs_quadQuot_le_of_opB hM hv; rwa [quadQuot_of_unit hv] at this
  have h4 : |2 * reInner w v| ≤ 2 * l2Norm w := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ((abs_reInner_le _ _).trans ?_) zero_le_two
    rw [l2Norm_unit hv, mul_one]
  calc |reInner w (M *ᵥ v) + reInner v (M *ᵥ w) - quadNum M v * (2 * reInner w v)| ≤
      |reInner w (M *ᵥ v)| + |reInner v (M *ᵥ w)| + |quadNum M v| * |2 * reInner w v| := by
        rw [← abs_mul]; exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ l2Norm w * m + m * l2Norm w + m * (2 * l2Norm w) := by
        gcongr
    _ = 4 * m * l2Norm w := by ring

/-!
## The constants
-/

/-- `ℓ₀ = (σP²)⁻¹ ≤ u₀` on the cutoff. -/
def ell0 (σ Zb R₁ : ℝ) : ℝ := (σ * Pc Zb R₁ ^ 2)⁻¹

/-- Bound for `|Δ_A|` on the cutoff. -/
def KDelta (σ Y Zb R₁ : ℝ) : ℝ :=
  4 * mOp σ Y Zb * mOp σ Y Zb / ell0 σ Zb R₁ +
    mOp σ Y Zb * (4 * mOp σ Y Zb * mOp σ Y Zb) / ell0 σ Zb R₁ ^ 2

/-- `d_W = 4 m K_W` bounds the derivative of each Rayleigh quotient along `W_{K₀}`. -/
def dW (σ Y Zb R₁ : ℝ) : ℝ := 4 * mOp σ Y Zb * KW σ Y Zb R₁

/-- Value bound of the numerator of `h̃`. -/
def Bnum (σ Y Zb : ℝ) : ℝ := mOp σ Y Zb * mOp σ Y Zb + mOp σ Y Zb * mOp σ Y Zb

/-- Derivative bound of the numerator of `h̃`. -/
def Bnum' (σ Y Zb R₁ : ℝ) : ℝ :=
  (dW σ Y Zb R₁ * mOp σ Y Zb + mOp σ Y Zb * dW σ Y Zb R₁) +
    (dW σ Y Zb R₁ * mOp σ Y Zb + mOp σ Y Zb * dW σ Y Zb R₁)

/-- Derivative bound of the denominator of `h̃`. -/
def Bden' (σ Y Zb R₁ : ℝ) : ℝ :=
  ((dW σ Y Zb R₁ + Zb * dW σ Y Zb R₁) * (mOp σ Y Zb + Zb * mOp σ Y Zb) +
      (mOp σ Y Zb + Zb * mOp σ Y Zb) * (dW σ Y Zb R₁ + Zb * dW σ Y Zb R₁)) +
    Zb ^ 2 * (dW σ Y Zb R₁ * mOp σ Y Zb + mOp σ Y Zb * dW σ Y Zb R₁)

/-- Lower bound `Y⁻² ℓ₀²` of the denominator of `h̃` on the cutoff. -/
def ellh (σ Y Zb R₁ : ℝ) : ℝ := Y⁻¹ ^ 2 * ell0 σ Zb R₁ ^ 2

/-- Bound for `|h̃| = |b_J/(sg)|` on the cutoff. -/
def Kh (σ Y Zb R₁ : ℝ) : ℝ := Bnum σ Y Zb / ellh σ Y Zb R₁

/-- Bound for `|Dh̃[W_{K₀}]|` on the cutoff. -/
def Kdh (σ Y Zb R₁ : ℝ) : ℝ :=
  Bnum' σ Y Zb R₁ / ellh σ Y Zb R₁ + Bnum σ Y Zb * Bden' σ Y Zb R₁ / ellh σ Y Zb R₁ ^ 2

/-!
## `Δ_A`
-/

namespace Scales

variable {D : AngularData ι} {σ Y Zb : ℝ} (S : Scales D σ Y Zb) {R₁ : ℝ} {v : ι → ℂ}
include S

theorem ell0_pos (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) : 0 < ell0 σ Zb R₁ := by
  unfold ell0; have := S.σ_pos; have := S.Pc_pos hv hb; positivity

/-- **`|Δ_A| ≤ K_Δ`** on the cutoff, for `‖ΓA‖ ≤ m`. -/
theorem abs_Delta_le {A : Matrix ι ι ℂ} (hA : OpB (D.Γ * A) (mOp σ Y Zb))
    (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) :
    |fderiv ℝ (D.ratio A) v (D.Γ *ᵥ v)| ≤ KDelta σ Y Zb R₁ := by
  have hw : l2Norm (D.Γ *ᵥ v) ≤ mOp σ Y Zb := by simpa [l2Norm_unit hv] using S.opB_Γ v
  have hm := S.mOp_nonneg
  have h4 : 4 * mOp σ Y Zb * l2Norm (D.Γ *ᵥ v) ≤ 4 * mOp σ Y Zb * mOp σ Y Zb := by gcongr
  have hf := (vb_quadQuot hA hv (D.Γ *ᵥ v)).mono le_rfl h4
  have hg := (vb_quadQuot S.opB_Γ hv (D.Γ *ᵥ v)).mono le_rfl h4
  have hg0 : ell0 σ Zb R₁ ≤ quadQuot D.Γ (v + (0 : ℝ) • (D.Γ *ᵥ v)) := by
    rw [zero_smul, add_zero]; exact S.u₀_lower hv hb
  have hdiv := hf.div hg (S.ell0_pos hv hb) hg0
  have hd : DifferentiableAt ℝ (D.ratio A) v :=
    ((D.ratio_c1 A).differentiableOn one_ne_zero).differentiableAt
      (isOpen_ne.mem_nhds (ne_zero_of_unit hv))
  exact abs_fderiv_le_of_VB hd hdiv

end Scales

end BlockBand.Angular.Ratio

/-!
## `h̃ = b_J/(sg)`
-/

namespace BlockBand.Angular.Stein.AngularData

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul quadQuot_of_unit)
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (D : AngularData ι)

/-- The denominator `(u₁ - Re ζ u₀)² + (Im ζ)² u₀² = s g u₀`. -/
def hden (v : ι → ℂ) : ℝ :=
  (D.u₁ v - D.ζ.re * D.u₀ v) * (D.u₁ v - D.ζ.re * D.u₀ v) + D.ζ.im ^ 2 * (D.u₀ v * D.u₀ v)

/-- `h̃ = (u₀ Re(v*JΓK₀v) - Re(v*ΓJv) u₁)/((u₁ - Re ζ u₀)² + (Im ζ)² u₀²)`; off the origin it
equals `b_J/(sg)` (`htil_eq`). -/
def htil (J : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (D.u₀ v * quadQuot (J * D.Γ * D.K) v - quadQuot (D.Γ * J) v * D.u₁ v) / D.hden v

theorem hden_ge {v : ι → ℂ} : D.ζ.im ^ 2 * (D.u₀ v * D.u₀ v) ≤ D.hden v := by
  unfold hden; nlinarith [mul_self_nonneg (D.u₁ v - D.ζ.re * D.u₀ v)]

theorem hden_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < D.hden v := by
  have hu := D.u₀_pos hv
  have hy := D.hroot.1
  exact lt_of_lt_of_le (by positivity) D.hden_ge

/-- `s g u₀ = (u₁ - Re ζ u₀)² + (Im ζ)² u₀²` (from the positive longitudinal identity). -/
theorem s_gLong_u₀ {v : ι → ℂ} (hv : v ≠ 0) : D.s * D.gLong v * D.u₀ v = D.hden v := by
  have hg := (D.positive_longitudinal hv).1
  have hu := (D.u₀_pos hv).ne'
  have hs := D.hs.ne'
  rw [hg, hden, aStar]
  field_simp

/-- `h̃ = b_J/(sg)` off the origin. -/
theorem htil_eq (J : Matrix ι ι ℂ) {v : ι → ℂ} (hv : v ≠ 0) :
    D.htil J v = D.corr J v / (D.s * D.gLong v) := by
  have hu := (D.u₀_pos hv).ne'
  have hd := (D.hden_pos hv).ne'
  have hsg : D.s * D.gLong v = D.hden v / D.u₀ v := by
    rw [← D.s_gLong_u₀ hv]; field_simp
  rw [hsg, htil, corr, ratio]
  field_simp

/-- `h̃ g = b_J/s` off the origin. -/
theorem htil_mul_gLong (J : Matrix ι ι ℂ) {v : ι → ℂ} (hv : v ≠ 0) :
    D.htil J v * D.gLong v = D.corr J v / D.s := by
  have hg := (D.positive_longitudinal hv).2.ne'
  rw [D.htil_eq J hv]; field_simp

theorem hden_c1 : ContDiffOn ℝ 1 D.hden {z | z ≠ 0} := by
  unfold hden u₁ u₀
  have h1 := contDiffOn_quadQuot (D.K * D.Γ)
  have h0 := contDiffOn_quadQuot D.Γ
  exact ((h1.sub (contDiffOn_const.mul h0)).mul (h1.sub (contDiffOn_const.mul h0))).add
    (contDiffOn_const.mul (h0.mul h0))

theorem htil_c1 (J : Matrix ι ι ℂ) : ContDiffOn ℝ 1 (D.htil J) {z | z ≠ 0} := by
  have h1 := contDiffOn_quadQuot (D.K * D.Γ)
  have h0 := contDiffOn_quadQuot D.Γ
  exact ((h0.mul (contDiffOn_quadQuot _)).sub ((contDiffOn_quadQuot _).mul h1)).div D.hden_c1
    fun z hz => (D.hden_pos hz).ne'

theorem htil_meas (J : Matrix ι ι ℂ) : Measurable (D.htil J) := by
  unfold htil hden u₁ u₀
  have h1 := measurable_quadQuot (D.K * D.Γ)
  have h0 := measurable_quadQuot D.Γ
  exact ((h0.mul (measurable_quadQuot _)).sub ((measurable_quadQuot _).mul h1)).div
    (((h1.sub (measurable_const.mul h0)).mul (h1.sub (measurable_const.mul h0))).add
      (measurable_const.mul (h0.mul h0)))

theorem htil_inv (J : Matrix ι ι ℂ) : IsScaleInvariant (D.htil J) := fun z r hr => by
  simp only [htil, hden, u₀, u₁, quadQuot_scale _ z hr]

end BlockBand.Angular.Stein.AngularData

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul quadQuot_of_unit)
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace Scales

variable {D : AngularData ι} {σ Y Zb : ℝ} (S : Scales D σ Y Zb) {R₁ : ℝ} {v : ι → ℂ}
include S

/-- `h̃` along `v + τw` has value `≤ K_h` and derivative `≤ K_{dh}` at a cutoff unit vector,
for `‖w‖ ≤ K_W`. -/
theorem vb_htil {J : Matrix ι ι ℂ} (hJ : IsContraction J) (hv : normSqSum v = 1)
    (hb : D.b₂ v ≤ R₁) {w : ι → ℂ} (hw : l2Norm w ≤ KW σ Y Zb R₁) :
    VB (fun τ => D.htil J (v + τ • w)) (Kh σ Y Zb R₁) (Kdh σ Y Zb R₁) := by
  have hm := S.mOp_nonneg
  have h4 : 4 * mOp σ Y Zb * l2Norm w ≤ dW σ Y Zb R₁ := by unfold dW; gcongr
  have q0 := (vb_quadQuot S.opB_Γ hv w).mono le_rfl h4
  have q1 := (vb_quadQuot S.opB_KΓ hv w).mono le_rfl h4
  have q2 := (vb_quadQuot (S.opB_ΓJ hJ) hv w).mono le_rfl h4
  have q3 := (vb_quadQuot (S.opB_JΓK hJ) hv w).mono le_rfl h4
  have hnum := (q0.mul q3).sub (q2.mul q1)
  have hre : |D.ζ.re| ≤ Zb := (Complex.abs_re_le_norm _).trans S.hZb
  have him : |D.ζ.im ^ 2| ≤ Zb ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_of_pos (im_pos D)).le.trans S.im_le) 2
  have f1 := q1.sub (q0.const_mul_le hre)
  have hden := (f1.mul f1).add ((q0.mul q0).const_mul_le him)
  have hl : ellh σ Y Zb R₁ ≤ D.hden (v + (0 : ℝ) • w) := by
    simp only [zero_smul, add_zero]
    refine le_trans ?_ D.hden_ge
    unfold ellh
    have h0 := S.ell0_pos hv hb
    have hu := S.u₀_lower hv hb
    have hY := S.inv_Y_le
    have hYp : 0 < Y⁻¹ := inv_pos.2 S.Y_pos
    rw [← pow_two]
    exact mul_le_mul (pow_le_pow_left₀ hYp.le hY 2) (pow_le_pow_left₀ h0.le hu 2)
      (by positivity) (by positivity)
  have hlp : 0 < ellh σ Y Zb R₁ := by
    unfold ellh; have := S.ell0_pos hv hb; have := S.Y_pos; positivity
  exact hnum.div hden hlp hl

theorem abs_htil_le {J : Matrix ι ι ℂ} (hJ : IsContraction J) (hv : normSqSum v = 1)
    (hb : D.b₂ v ≤ R₁) : |D.htil J v| ≤ Kh σ Y Zb R₁ :=
  abs_le_of_VB (S.vb_htil hJ hv hb (w := 0) (by
    rw [show l2Norm (0 : ι → ℂ) = 0 by simp [l2Norm_eq, normSqSum]]
    unfold KW; have := S.mOp_nonneg; have := S.Kr_nonneg hv hb; positivity))

theorem l2_field_K_le (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) :
    l2Norm (D.field D.K v) ≤ KW σ Y Zb R₁ :=
  S.l2_field_le S.opB_ΓK hv (S.abs_ratio_K_le hv hb)

theorem l2_field_J_le {J : Matrix ι ι ℂ} (hJ : IsContraction J) (hv : normSqSum v = 1)
    (hb : D.b₂ v ≤ R₁) : l2Norm (D.field J v) ≤ KW σ Y Zb R₁ :=
  S.l2_field_le (S.opB_ΓJ hJ) hv (S.abs_ratio_J_le hv hb hJ)

/-- **`|D(b_J/(sg))[W_{K₀}]| ≤ K_{dh}`** on the cutoff. -/
theorem abs_fderiv_htil_le {J : Matrix ι ι ℂ} (hJ : IsContraction J) (hv : normSqSum v = 1)
    (hb : D.b₂ v ≤ R₁) : |fderiv ℝ (D.htil J) v (D.field D.K v)| ≤ Kdh σ Y Zb R₁ := by
  have hd : DifferentiableAt ℝ (D.htil J) v :=
    ((D.htil_c1 J).differentiableOn one_ne_zero).differentiableAt
      (isOpen_ne.mem_nhds (ne_zero_of_unit hv))
  exact abs_fderiv_le_of_VB hd (S.vb_htil hJ hv hb (S.l2_field_K_le hv hb))

end Scales

end BlockBand.Angular.Ratio
