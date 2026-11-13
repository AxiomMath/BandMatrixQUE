module

public import BlockBand.Angular.RatioPointwise

/-!
# The angular ratio lemma: the reconstruction ratio under the finite angular measure

The angular measure is `ν(f) = ∫ e^{-b₂/t + a²/(2t)} 𝔷 f dν_N` with `ν_N` the
projective Haar measure (`CoareaPalm.projectiveHaar`) and `𝔷 ≥ 0` scale-invariant, `C¹` off
the origin (the normalizing constant `C` is absorbed into `𝔷`); `Z = ν(1)`, and
`ν(χ‖H‖) = ∫ e^{q} χ(b₂) ‖∇𝔷‖ dν_N` (`H = ∇ log 𝔷`, real metric `Df[h] = Re(h*∇f)`).
The angular first-moment bound is tested against every vector `w`:
`ν(|w*v|²) ≤ C₀(Z+r)/N · Re(w*Γw)`. All norms are Euclidean.

`angular_ratio_core` proves, for `A` Hermitian with `‖(K₀-ζ)⁻¹Ax‖² ≤ c_A‖x‖²`,
`ν(χ ‖𝓛ΓAv‖/‖𝓛v‖) ≤ C (Z + r + ν(χ‖H‖))` with the explicit constant
`ratioConst σ Y Zb c_A C₀ χ`, which depends only on bounds `σ ≥ s, s⁻¹`, `Y ≥ (Im ζ)⁻¹`,
`Zb ≥ |ζ|`, `c_A`, `C₀`, the cutoff support `R₁` and the bounds `M₀ ≥ χ`, `M₁ ≥ |χ'|`; it is
independent of `N`, of `𝓛` (only injectivity is used) and of `𝔷`.
`angular_ratio` specializes to the three cases `A` a Hermitian contraction,
`A = I`, `A = K₀`, with one common constant.

Proof: integrate the divergence of `χ q Y`, `Y = Γ∇h - v Re(v*Γ∇h)`, by the projective
Stein identity with coefficient `c = 1/h` and linear field `ΓDv`; `q` is regularized as
`(q² + ε²)^{1/2}` with `ε² = T_D/N` (`T_D = Re Tr DΓ`), which costs `T_D Z` only.
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

/-- The constant of the angular ratio bound. -/
def ratioConst (σ Y Zb cA C₀ : ℝ) (X : Cutoff) : ℝ :=
  K1c σ Zb X * (C₀ * (3 * σ ^ 2 * cA * Y ^ 2 + 1 + σ ^ 2 * (1 + Zb * Y) ^ 2 * Y ^ 2 +
      σ ^ 2 * Y ^ 4) + 3) + X.M₀ * (σ * Y * (1 + cA)) + K4c σ Y cA

variable (D : AngularData ι) (L : Matrix κ ι ℂ)

theorem ratio_arith {N K1 M0 K4 cA cK Y s σ F C₀ Zm r Hn ε2 Fa Cm Ia Ib Ic Id : ℝ}
    (hN : 1 ≤ N) (hK1 : 0 ≤ K1) (hM0 : 0 ≤ M0) (hK4 : 0 ≤ K4) (hcA : 0 ≤ cA) (hcK : 0 ≤ cK)
    (hY : 0 ≤ Y) (hs : 0 < s) (hsσ : s ≤ σ) (hF : 0 ≤ F) (hC₀ : 0 ≤ C₀) (hZm : 0 ≤ Zm)
    (hr : 0 ≤ r) (hHn : 0 ≤ Hn) (hε : ε2 = s * F / N) (hFa : Fa = s * F * (σ * Y * (1 + cA)))
    (hCm : Cm = C₀ * (Zm + r) / N)
    (hIa : Ia ≤ Cm * (s * (cA * s ^ 2 * Y ^ 2 * F))) (hIb : Ib ≤ Cm * (s * F))
    (hIc : Ic ≤ Cm * (s * (cK * s ^ 2 * Y ^ 2 * F)))
    (hId : Id ≤ Cm * (s * (Y ^ 2 * s ^ 2 * Y ^ 2 * F))) :
    N * K1 * 3 * Ia + (N * K1 * 3 * ε2 + M0 * Fa) * Zm + N * K1 * Ib + N * K1 * Ic +
        N * K1 * Id + s * F * K4 * Hn ≤
      s * F * (K1 * (C₀ * (3 * σ ^ 2 * cA * Y ^ 2 + 1 + σ ^ 2 * cK * Y ^ 2 + σ ^ 2 * Y ^ 4) + 3) +
        M0 * (σ * Y * (1 + cA)) + K4) * (Zm + r + Hn) := by
  have hN0 : 0 < N := by linarith
  have hNK : 0 ≤ N * K1 := by positivity
  set U := C₀ * (Zm + r) with hU
  have hU0 : 0 ≤ U := by positivity
  set T := s * F with hT
  have hT0 : 0 ≤ T := by positivity
  have ea : N * K1 * 3 * Ia ≤ T * (K1 * U * (3 * s ^ 2 * cA * Y ^ 2)) := by
    calc N * K1 * 3 * Ia ≤ N * K1 * 3 * (Cm * (s * (cA * s ^ 2 * Y ^ 2 * F))) := by gcongr
      _ = _ := by rw [hCm, hT]; field_simp
  have eb : N * K1 * Ib ≤ T * (K1 * U * 1) := by
    calc N * K1 * Ib ≤ N * K1 * (Cm * (s * F)) := by gcongr
      _ = _ := by rw [hCm, hT]; field_simp
  have ec : N * K1 * Ic ≤ T * (K1 * U * (s ^ 2 * cK * Y ^ 2)) := by
    calc N * K1 * Ic ≤ N * K1 * (Cm * (s * (cK * s ^ 2 * Y ^ 2 * F))) := by gcongr
      _ = _ := by rw [hCm, hT]; field_simp
  have ed : N * K1 * Id ≤ T * (K1 * U * (s ^ 2 * Y ^ 4)) := by
    calc N * K1 * Id ≤ N * K1 * (Cm * (s * (Y ^ 2 * s ^ 2 * Y ^ 2 * F))) := by gcongr
      _ = _ := by rw [hCm, hT]; field_simp
  have ee : (N * K1 * 3 * ε2 + M0 * Fa) * Zm = T * (3 * K1 * Zm + M0 * (σ * Y * (1 + cA)) * Zm) := by
    rw [hε, hFa]; field_simp
  have hs2 : s ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hs.le hsσ 2
  have hP : 3 * s ^ 2 * cA * Y ^ 2 + 1 + s ^ 2 * cK * Y ^ 2 + s ^ 2 * Y ^ 4 ≤
      3 * σ ^ 2 * cA * Y ^ 2 + 1 + σ ^ 2 * cK * Y ^ 2 + σ ^ 2 * Y ^ 4 := by gcongr
  set P := 3 * σ ^ 2 * cA * Y ^ 2 + 1 + σ ^ 2 * cK * Y ^ 2 + σ ^ 2 * Y ^ 4 with hPdef
  have hP0 : 0 ≤ P := by positivity
  have inner : K1 * U * (3 * s ^ 2 * cA * Y ^ 2) + K1 * U * 1 + K1 * U * (s ^ 2 * cK * Y ^ 2) +
      K1 * U * (s ^ 2 * Y ^ 4) + (3 * K1 * Zm + M0 * (σ * Y * (1 + cA)) * Zm) + K4 * Hn ≤
      (K1 * (C₀ * P + 3) + M0 * (σ * Y * (1 + cA)) + K4) * (Zm + r + Hn) := by
    have h1 : K1 * U * (3 * s ^ 2 * cA * Y ^ 2 + 1 + s ^ 2 * cK * Y ^ 2 + s ^ 2 * Y ^ 4) ≤
        K1 * U * P := by gcongr
    have h2 : K1 * U * P ≤ K1 * C₀ * P * (Zm + r + Hn) := by
      rw [hU]
      have : C₀ * (Zm + r) ≤ C₀ * (Zm + r + Hn) := mul_le_mul_of_nonneg_left (by linarith) hC₀
      calc K1 * (C₀ * (Zm + r)) * P ≤ K1 * (C₀ * (Zm + r + Hn)) * P := by gcongr
        _ = _ := by ring
    have h3 : 3 * K1 * Zm ≤ 3 * K1 * (Zm + r + Hn) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : M0 * (σ * Y * (1 + cA)) * Zm ≤ M0 * (σ * Y * (1 + cA)) * (Zm + r + Hn) := by
      have : 0 ≤ σ := by linarith
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : K4 * Hn ≤ K4 * (Zm + r + Hn) := mul_le_mul_of_nonneg_left (by linarith) hK4
    have e1 : K1 * U * (3 * s ^ 2 * cA * Y ^ 2) + K1 * U * 1 + K1 * U * (s ^ 2 * cK * Y ^ 2) +
        K1 * U * (s ^ 2 * Y ^ 4) =
        K1 * U * (3 * s ^ 2 * cA * Y ^ 2 + 1 + s ^ 2 * cK * Y ^ 2 + s ^ 2 * Y ^ 4) := by ring
    have e2 : (K1 * (C₀ * P + 3) + M0 * (σ * Y * (1 + cA)) + K4) * (Zm + r + Hn) =
        K1 * C₀ * P * (Zm + r + Hn) + 3 * K1 * (Zm + r + Hn) +
          M0 * (σ * Y * (1 + cA)) * (Zm + r + Hn) + K4 * (Zm + r + Hn) := by ring
    linarith
  have hfin := mul_le_mul_of_nonneg_left inner hT0
  have e3 : T * (K1 * U * (3 * s ^ 2 * cA * Y ^ 2) + K1 * U * 1 + K1 * U * (s ^ 2 * cK * Y ^ 2) +
      K1 * U * (s ^ 2 * Y ^ 4) + (3 * K1 * Zm + M0 * (σ * Y * (1 + cA)) * Zm) + K4 * Hn) =
      T * (K1 * U * (3 * s ^ 2 * cA * Y ^ 2)) + T * (K1 * U * 1) +
        T * (K1 * U * (s ^ 2 * cK * Y ^ 2)) + T * (K1 * U * (s ^ 2 * Y ^ 4)) +
        T * (3 * K1 * Zm + M0 * (σ * Y * (1 + cA)) * Zm) + T * K4 * Hn := by ring
  have e4 : T * ((K1 * (C₀ * P + 3) + M0 * (σ * Y * (1 + cA)) + K4) * (Zm + r + Hn)) =
      T * (K1 * (C₀ * P + 3) + M0 * (σ * Y * (1 + cA)) + K4) * (Zm + r + Hn) := by ring
  linarith

theorem continuous_mulVec' {m n : Type} [Fintype n] (M : Matrix m n ℂ) :
    Continuous fun v : n → ℂ => M *ᵥ v :=
  Continuous.matrix_mulVec continuous_const continuous_id

theorem continuous_nsq_mulVec {m : Type} [Fintype m] [DecidableEq m] {f : (ι → ℂ) → (m → ℂ)}
    (hf : Continuous f) : Continuous fun v => normSqSum (f v) :=
  contDiff_normSqSum.continuous.comp hf

/-- **The angular ratio lemma, core form**. Let `𝓛 : ℂ^ι → ℂ^κ` be injective,
`A` Hermitian with `‖(K₀-ζ)⁻¹Ax‖² ≤ c_A ‖x‖²`, `χ` a cutoff (`Cutoff`), `𝔷 ≥ 0`
scale-invariant and `C¹` off `0`, `Z = ∫ e^{q}𝔷 dν_N`, and suppose the angular first-moment bound
in the tested form `∫ e^{q}𝔷 |w*v|² dν_N ≤ C₀(Z+r)/N · Re(w*Γw)` for all `w`. Then
`ν(χ ‖𝓛ΓAv‖/‖𝓛v‖) ≤ C (Z + r + ν(χ‖∇𝔷‖/𝔷))` with
`C = ratioConst σ Y Zb c_A C₀ χ` (bounds `s, s⁻¹ ≤ σ`, `(Im ζ)⁻¹ ≤ Y`, `|ζ| ≤ Zb`). -/
theorem angular_ratio_core [Nonempty ι] (hL : ∀ x, L *ᵥ x = 0 → x = 0) {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) {cA : ℝ} (hcA0 : 0 ≤ cA)
    (hcA : ∀ x, normSqSum (Rz D *ᵥ (A *ᵥ x)) ≤ cA * normSqSum x)
    {σ Y Zb : ℝ} (hs1 : D.s ≤ σ) (hs2 : D.s⁻¹ ≤ σ) (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb)
    (X : Cutoff) {Zf : (ι → ℂ) → ℝ} (hZm : Measurable Zf) (hZi : IsScaleInvariant Zf)
    (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0}) (hZ0 : ∀ v, 0 ≤ Zf v)
    {C₀ r : ℝ} (hC₀ : 0 ≤ C₀) (hr : 0 ≤ r)
    (hFM : ∀ w : ι → ℂ, ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤
      C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r) / Fintype.card ι *
        (star w ⬝ᵥ (D.Γ *ᵥ w)).re) :
    ∫ v, Real.exp (D.expo v) * Zf v *
        (X.χ (D.b₂ v) * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) / l2Norm (L *ᵥ v))) ∂projectiveHaar ι ≤
      ratioConst σ Y Zb cA C₀ X *
        ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r +
          ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar ι) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  set Zm := ∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι with hZmdef
  set Hn := ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar ι
    with hHndef
  have hs := D.hs
  have hFpos := Fd_pos D L hL
  have hTD : 0 < TD D L := mul_pos hs hFpos
  have hε : 0 < eps2 D L := div_pos hTD (by linarith)
  have hY0 : 0 ≤ Y := (inv_nonneg.2 (im_pos D).le).trans hY
  have hZb0 : 0 ≤ Zb := (norm_nonneg _).trans hZb
  have hσ1 : 1 ≤ σ := by
    by_contra hlt; push Not at hlt
    have h2 : 1 < D.s⁻¹ := (one_lt_inv₀ hs).2 (lt_of_le_of_lt hs1 hlt)
    linarith
  have hI : ∀ {G : (ι → ℂ) → ℝ}, ContinuousOn G {z | z ≠ 0} → Integrable G (projectiveHaar ι) :=
    fun hG => integrable_of_continuousOn hG
  set B := D.Γ * Dm L with hBdef
  set c := cfun L with hcdef
  set f := ffun D L X.χ Zf A (eps2 D L) with hfdef
  have hcc := cfun_c1 L hL
  have hfc := ffun_c1 D L X.smooth hZc A hε
  have hBc : Continuous fun v : ι → ℂ => B *ᵥ v := continuous_mulVec' B
  have hχc : Continuous X.χ := X.smooth.continuous
  have hEc : ContinuousOn (fun v => Real.exp (D.expo v)) {z | z ≠ 0} :=
    Real.continuous_exp.comp_continuousOn D.expo_c1.continuousOn
  have hρc : ContinuousOn (fun v => Real.exp (D.expo v) * Zf v) {z | z ≠ 0} :=
    hEc.mul hZc.continuousOn
  have hχbc : ContinuousOn (fun v => X.χ (D.b₂ v)) {z | z ≠ 0} :=
    hχc.comp_continuousOn (b₂_c1 D).continuousOn
  -- the Stein identity
  have S := integral_projectiveHaar_coeff_fderiv_mulVec c f (cfun_meas L)
    (ffun_meas D L hχc hZm A _) (cfun_inv L) (ffun_inv D L X.χ hZi A _) hcc hfc B
  have i1 : Integrable (fun v => c v * f v * (N * quadQuot B v - (B.trace).re))
      (projectiveHaar ι) :=
    hI ((hcc.continuousOn.mul hfc.continuousOn).mul
      ((continuousOn_const.mul (contDiffOn_quadQuot B).continuousOn).sub continuousOn_const))
  have i2 : Integrable (fun v => f v * fderiv ℝ c v (B *ᵥ v)) (projectiveHaar ι) :=
    hI (hfc.continuousOn.mul (continuousOn_fderiv_apply hcc hBc))
  have i3 : Integrable (fun v => c v * fderiv ℝ f v (B *ᵥ v)) (projectiveHaar ι) :=
    hI (hcc.continuousOn.mul (continuousOn_fderiv_apply hfc hBc))
  have iW : Integrable (Wfun D L X Zf A) (projectiveHaar ι) :=
    ((i1.const_mul 2).sub i2).sub i3
  have hW : ∫ v, Wfun D L X Zf A v ∂projectiveHaar ι = 0 := by
    change ∫ v, (2 * (c v * f v * (N * quadQuot B v - (B.trace).re)) -
        f v * fderiv ℝ c v (B *ᵥ v) - c v * fderiv ℝ f v (B *ᵥ v)) ∂projectiveHaar ι = 0
    have i0 : Integrable (fun v => 2 * (c v * f v * (N * quadQuot B v - (B.trace).re)))
        (projectiveHaar ι) := i1.const_mul 2
    have iA : Integrable (fun v => 2 * (c v * f v * (N * quadQuot B v - (B.trace).re)) -
        f v * fderiv ℝ c v (B *ᵥ v)) (projectiveHaar ι) := i0.sub i2
    rw [integral_sub iA i3, integral_sub i0 i2,
      integral_const_mul, S]
    ring
  have icf : Integrable (fun v => c v * f v) (projectiveHaar ι) :=
    hI (hcc.continuousOn.mul hfc.continuousOn)
  -- the majorant and its integral
  have iG : Integrable (Gfun D L σ Y Zb cA X Zf A) (projectiveHaar ι) := by
    refine hI ?_
    unfold Gfun
    have h1 : Continuous fun v => 3 * (normSqSum (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) + eps2 D L) +
        normSqSum (L *ᵥ v) + normSqSum (L *ᵥ (D.Γ *ᵥ (D.K *ᵥ v))) +
        normSqSum (L *ᵥ (D.Γ *ᵥ v)) := by
      have := continuous_mulVec' L; have := continuous_mulVec' D.Γ
      have := continuous_mulVec' A; have := continuous_mulVec' D.K
      refine (((continuous_const.mul ((continuous_nsq_mulVec ?_).add continuous_const)).add
        (continuous_nsq_mulVec ?_)).add (continuous_nsq_mulVec ?_)).add
        (continuous_nsq_mulVec ?_) <;> fun_prop
    exact ((continuousOn_const.mul hρc).mul h1.continuousOn).add
      (continuousOn_const.mul hρc) |>.add (continuousOn_const.mul
        ((hEc.mul hχbc).mul (continuousOn_gradNorm hZc)))
  have hmono : ∫ v, (Wfun D L X Zf A v + TD D L * (c v * f v)) ∂projectiveHaar ι ≤
      ∫ v, Gfun D L σ Y Zb cA X Zf A v ∂projectiveHaar ι := by
    refine integral_mono_ae (iW.add (icf.const_mul _)) iG ?_
    filter_upwards [ae_projectiveHaar_unit] with v hv
    exact pointwise_bound D L hL hA hcA0 hcA hs1 hs2 hY hZb X hZc hZ0 hv
  have icf' : Integrable (fun v => TD D L * (c v * f v)) (projectiveHaar ι) := icf.const_mul _
  rw [integral_add iW icf', hW, zero_add, integral_const_mul] at hmono
  -- integral of the majorant
  set ρ := fun v => Real.exp (D.expo v) * Zf v with hρdef
  set K1 := K1c σ Zb X
  set K4 := K4c σ Y cA
  set Fa := TD D L * (σ * Y * (1 + cA)) with hFadef
  have hGe : Gfun D L σ Y Zb cA X Zf A = fun v =>
      N * K1 * 3 * (ρ v * normSqSum (L *ᵥ ((D.Γ * A) *ᵥ v))) +
        (N * K1 * 3 * eps2 D L + X.M₀ * Fa) * ρ v +
        N * K1 * (ρ v * normSqSum (L *ᵥ ((1 : Matrix ι ι ℂ) *ᵥ v))) +
        N * K1 * (ρ v * normSqSum (L *ᵥ ((D.Γ * D.K) *ᵥ v))) +
        N * K1 * (ρ v * normSqSum (L *ᵥ ((D.Γ * 1) *ᵥ v))) +
        TD D L * K4 * (Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v) := by
    funext v
    simp only [Gfun, hρdef, ← mulVec_mulVec, one_mulVec, Matrix.mul_one]
    ring
  have hnc : ∀ P : Matrix ι ι ℂ, Integrable (fun v => ρ v * normSqSum (L *ᵥ (P *ᵥ v)))
      (projectiveHaar ι) := fun P =>
    hI (hρc.mul (continuous_nsq_mulVec ((continuous_mulVec' L).comp
      (continuous_mulVec' P))).continuousOn)
  have iρ : Integrable ρ (projectiveHaar ι) := hI hρc
  have iH : Integrable (fun v => Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v)
      (projectiveHaar ι) := hI ((hEc.mul hχbc).mul (continuousOn_gradNorm hZc))
  have hGint : ∫ v, Gfun D L σ Y Zb cA X Zf A v ∂projectiveHaar ι =
      N * K1 * 3 * (∫ v, ρ v * normSqSum (L *ᵥ ((D.Γ * A) *ᵥ v)) ∂projectiveHaar ι) +
        (N * K1 * 3 * eps2 D L + X.M₀ * Fa) * Zm +
        N * K1 * (∫ v, ρ v * normSqSum (L *ᵥ ((1 : Matrix ι ι ℂ) *ᵥ v)) ∂projectiveHaar ι) +
        N * K1 * (∫ v, ρ v * normSqSum (L *ᵥ ((D.Γ * D.K) *ᵥ v)) ∂projectiveHaar ι) +
        N * K1 * (∫ v, ρ v * normSqSum (L *ᵥ ((D.Γ * 1) *ᵥ v)) ∂projectiveHaar ι) +
        TD D L * K4 * Hn := by
    rw [hGe, integral_add, integral_add, integral_add, integral_add, integral_add,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul]
    all_goals first
      | rfl
      | exact ((hnc _).const_mul _)
      | exact (iρ.const_mul _)
      | exact (iH.const_mul _)
      | (repeat' apply Integrable.add) <;> first
          | exact ((hnc _).const_mul _)
          | exact (iρ.const_mul _)
  -- first-moment bounds
  have hZm0 : 0 ≤ Zm := integral_nonneg fun v => mul_nonneg (Real.exp_pos _).le (hZ0 v)
  have hHn0 : 0 ≤ Hn := integral_nonneg fun v =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (X.nonneg _)) (gradNorm_nonneg _ _)
  set Cm := C₀ * (Zm + r) / N with hCmdef
  have hCm0 : 0 ≤ Cm := by positivity
  have hFM' : ∀ w : ι → ℂ, ∫ v, ρ v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤
      Cm * quadNum D.Γ w := fun w => hFM w
  have FMG := fun P => integral_firstMoment D L hρc hFM' P
  have hIa : (∫ v, ρ v * normSqSum (L *ᵥ ((D.Γ * A) *ᵥ v)) ∂projectiveHaar ι) ≤
      Cm * (D.s * (cA * D.s ^ 2 * Y ^ 2 * Fd D L)) :=
    (FMG _).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (sum_ΓM_bound D L hY hA hcA0 hcA) hs.le) hCm0)
  have hIb : (∫ v, ρ v * normSqSum (L *ᵥ ((1 : Matrix ι ι ℂ) *ᵥ v)) ∂projectiveHaar ι) ≤
      Cm * (D.s * Fd D L) := by
    refine (FMG _).trans (le_of_eq ?_)
    simp only [conjTranspose_one, one_mulVec, Fd]
  have hKh := D.hK
  have hIc : (∫ v, ρ v * normSqSum (L *ᵥ ((D.Γ * D.K) *ᵥ v)) ∂projectiveHaar ι) ≤
      Cm * (D.s * ((1 + Zb * Y) ^ 2 * D.s ^ 2 * Y ^ 2 * Fd D L)) :=
    (FMG _).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (sum_ΓM_bound D L hY hKh (sq_nonneg _) (RzK_bound D hY hZb)) hs.le) hCm0)
  have hone : ∀ x, normSqSum (Rz D *ᵥ ((1 : Matrix ι ι ℂ) *ᵥ x)) ≤ Y ^ 2 * normSqSum x :=
    fun x => by rw [one_mulVec]; exact Rz_bound D hY x
  have hId : (∫ v, ρ v * normSqSum (L *ᵥ ((D.Γ * 1) *ᵥ v)) ∂projectiveHaar ι) ≤
      Cm * (D.s * (Y ^ 2 * D.s ^ 2 * Y ^ 2 * Fd D L)) :=
    (FMG _).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (sum_ΓM_bound D L hY isHermitian_one (sq_nonneg _) hone) hs.le) hCm0)
  have hK1 : 0 ≤ K1 := by unfold K1 K1c Λc; have := X.M₀_nonneg; have := X.M₁_nonneg; positivity
  have hK4 : 0 ≤ K4 := by unfold K4 K4c; positivity
  have harith := ratio_arith (ε2 := eps2 D L) (Fa := Fa) hN1 hK1 X.M₀_nonneg hK4 hcA0 (sq_nonneg (1 + Zb * Y)) hY0 hs hs1
    (Fd_nonneg D L) hC₀ hZm0 hr hHn0 rfl rfl hCmdef
    hIa hIb hIc hId
  have hG' : ∫ v, Gfun D L σ Y Zb cA X Zf A v ∂projectiveHaar ι ≤
      TD D L * (ratioConst σ Y Zb cA C₀ X * (Zm + r + Hn)) := by
    rw [hGint]; refine harith.trans (le_of_eq ?_); unfold ratioConst TD; ring
  have hcf : ∫ v, c v * f v ∂projectiveHaar ι ≤ ratioConst σ Y Zb cA C₀ X * (Zm + r + Hn) := by
    have h1 := hmono.trans hG'
    exact le_of_mul_le_mul_left h1 hTD
  refine le_trans ?_ hcf
  refine integral_mono_of_nonneg ?_ icf ?_
  · filter_upwards with v
    have := X.nonneg (D.b₂ v)
    have := hZ0 v
    have := l2Norm_nonneg (L *ᵥ (D.Γ *ᵥ (A *ᵥ v)))
    have := l2Norm_nonneg (L *ᵥ v)
    positivity
  · filter_upwards [ae_projectiveHaar_unit] with v hv
    have hcv : c v = (l2Norm (L *ᵥ v))⁻¹ := by
      rw [hcdef, cfun, quadQuot_of_unit hv, quadNum_Dm]; rfl
    have hqv : l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) ≤ qe D L A (eps2 D L) v := by
      rw [qe, quadQuot_of_unit hv, quadNum_Bq, l2Norm_eq]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [hcv, hfdef, ffun, div_eq_mul_inv]
    have h0 : 0 ≤ Real.exp (D.expo v) * Zf v * X.χ (D.b₂ v) * (l2Norm (L *ᵥ v))⁻¹ := by
      have := X.nonneg (D.b₂ v); have := hZ0 v
      have := l2Norm_nonneg (L *ᵥ v)
      positivity
    calc Real.exp (D.expo v) * Zf v * (X.χ (D.b₂ v) *
          (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) * (l2Norm (L *ᵥ v))⁻¹)) =
        Real.exp (D.expo v) * Zf v * X.χ (D.b₂ v) * (l2Norm (L *ᵥ v))⁻¹ *
          l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) := by ring
      _ ≤ Real.exp (D.expo v) * Zf v * X.χ (D.b₂ v) * (l2Norm (L *ᵥ v))⁻¹ *
          qe D L A (eps2 D L) v := mul_le_mul_of_nonneg_left hqv h0
      _ = _ := by ring

/-- The common resolvent constant `c_A = Y² + (1 + Zb Y)²` of the three cases. -/
def cAll (Y Zb : ℝ) : ℝ := Y ^ 2 + (1 + Zb * Y) ^ 2

/-- **The angular ratio lemma**. For `A` a Hermitian contraction, `A = I` or
`A = K₀`, under the hypotheses of `angular_ratio_core`,
`ν(χ ‖𝓛ΓAv‖/‖𝓛v‖) ≤ C (Z + r + ν(χ‖H‖))`, with the single constant
`C = ratioConst σ Y Zb (cAll Y Zb) C₀ χ`. It depends only on the bounds `σ ≥ s, s⁻¹`,
`Y ≥ (Im ζ)⁻¹`, `Zb ≥ |ζ|`, on `C₀` and on the cutoff data `R₁, M₀ ≥ χ, M₁ ≥ |χ'|`; it is
independent of the cardinality of `ι`, of every singular value of `𝓛` and of `𝔷`. -/
theorem angular_ratio [Nonempty ι] (hL : ∀ x, L *ᵥ x = 0 → x = 0) {A : Matrix ι ι ℂ}
    (hAcase : (A.IsHermitian ∧ ∀ x, normSqSum (A *ᵥ x) ≤ normSqSum x) ∨ A = 1 ∨ A = D.K)
    {σ Y Zb : ℝ} (hs1 : D.s ≤ σ) (hs2 : D.s⁻¹ ≤ σ) (hY : D.ζ.im⁻¹ ≤ Y) (hZb : ‖D.ζ‖ ≤ Zb)
    (X : Cutoff) {Zf : (ι → ℂ) → ℝ} (hZm : Measurable Zf) (hZi : IsScaleInvariant Zf)
    (hZc : ContDiffOn ℝ 1 Zf {z | z ≠ 0}) (hZ0 : ∀ v, 0 ≤ Zf v)
    {C₀ r : ℝ} (hC₀ : 0 ≤ C₀) (hr : 0 ≤ r)
    (hFM : ∀ w : ι → ℂ, ∫ v, Real.exp (D.expo v) * Zf v * ‖star w ⬝ᵥ v‖ ^ 2 ∂projectiveHaar ι ≤
      C₀ * ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r) / Fintype.card ι *
        (star w ⬝ᵥ (D.Γ *ᵥ w)).re) :
    ∫ v, Real.exp (D.expo v) * Zf v *
        (X.χ (D.b₂ v) * (l2Norm (L *ᵥ (D.Γ *ᵥ (A *ᵥ v))) / l2Norm (L *ᵥ v))) ∂projectiveHaar ι ≤
      ratioConst σ Y Zb (cAll Y Zb) C₀ X *
        ((∫ v, Real.exp (D.expo v) * Zf v ∂projectiveHaar ι) + r +
          ∫ v, Real.exp (D.expo v) * X.χ (D.b₂ v) * gradNorm Zf v ∂projectiveHaar ι) := by
  have h0 : 0 ≤ cAll Y Zb := by unfold cAll; positivity
  have hY2 : ∀ x : ι → ℂ, Y ^ 2 * normSqSum x ≤ cAll Y Zb * normSqSum x := fun x =>
    mul_le_mul_of_nonneg_right (by unfold cAll; nlinarith [sq_nonneg (1 + Zb * Y)])
      (normSqSum_nonneg x)
  have hherm : A.IsHermitian := by
    rcases hAcase with ⟨h, -⟩ | h | h
    · exact h
    · rw [h]; exact isHermitian_one
    · rw [h]; exact D.hK
  refine angular_ratio_core D L hL hherm h0 ?_ hs1 hs2 hY hZb X hZm hZi hZc hZ0 hC₀ hr hFM
  intro x
  rcases hAcase with ⟨-, hc⟩ | h | h
  · exact (Rz_bound D hY _).trans ((mul_le_mul_of_nonneg_left (hc x) (sq_nonneg Y)).trans
      (hY2 x))
  · rw [h, one_mulVec]; exact (Rz_bound D hY x).trans (hY2 x)
  · rw [h]
    refine (RzK_bound D hY hZb x).trans (mul_le_mul_of_nonneg_right ?_ (normSqSum_nonneg x))
    unfold cAll; nlinarith [sq_nonneg Y]

end BlockBand.Angular.Ratio
