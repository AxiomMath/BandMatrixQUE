module

public import BlockBand.Critical.MatrixClosing.Boundary.Twist
public import BlockBand.Critical.MatrixClosing.MiddleShift.Bound
public import BlockBand.Critical.MatrixClosing.Bridge

/-!
# Matrix closing, boundary clause: the Poisson estimate for the closing phase

Law: `collarLaw W b`; deterministic Hermitian `X`.

* `closedScattering b e s X ω = U_s r`, `closedQuad b e s t X u ω = u*(I - tU_s r)⁻¹u`.
* `quadForm_middleKernel_twistOld`: for Hermitian collar blocks and `0 ≤ t < 1`,
  `u*𝒫(tU_s r')u = P(wζ_t)` with `r' = r(X')`, `X' = twistOld b e w u X`, and `Re q_t ≥ 1/2`.
* `ae_isUnit_det_one_sub_closedScattering`: `I - U_s r` is a.s. invertible for `s = x/(Wρ)`.
* **`abs_integral_pk_sub_one_le`**: if the radially regulated middle-shifted kernel at `X'`
  satisfies `‖E𝒫(tU_s r') - I‖ ≤ err + δ` for `t` near one, then `|E P(wζ) - 1| ≤ err`,
  `ζ = 1 - (u*(I - U_s r)⁻¹u)⁻¹` (dominated convergence as `t ↑ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Boundary

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Kernel
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The closed product `V = U_s r` of the middle-shifted collar and the old scattering. -/
abbrev closedScattering (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  middleScattering b e s ω * oldScattering b e X

/-- `q = u*(I - tV)⁻¹u` (`t = 1`: the closing quadratic form). -/
def closedQuad (b e s t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) (ω : CollarSample W) : ℂ :=
  star u ⬝ᵥ ((1 - (t : ℂ) • closedScattering b e s X ω)⁻¹ *ᵥ u)

theorem middleScattering_mul_conjTranspose (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian) :
    middleScattering b e s ω * (middleScattering b e s ω)ᴴ = 1 :=
  cayley_mul_conjTranspose (middleReaction_isHermitian b e s hA hG) hη

theorem closedScattering_mul_conjTranspose (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian) :
    closedScattering b e s X ω * (closedScattering b e s X ω)ᴴ = 1 := by
  have h := posSemidef_one_sub_unitary_mul (middleScattering_mul_conjTranspose b e s hη hA hG)
    (V := oldScattering b e X) (by
      rw [oldScattering_mul_conjTranspose b e hη hX, sub_self]; exact PosSemidef.zero)
  have e1 : closedScattering b e s X ω * (closedScattering b e s X ω)ᴴ =
      middleScattering b e s ω * (oldScattering b e X * (oldScattering b e X)ᴴ) *
        (middleScattering b e s ω)ᴴ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, oldScattering_mul_conjTranspose b e hη hX, Matrix.mul_one,
    middleScattering_mul_conjTranspose b e s hη hA hG]

theorem smul_contraction {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Matrix ι ι ℂ}
    (hV : V * Vᴴ = 1) {t : ℝ} (ht : t ^ 2 ≤ 1) :
    (1 - ((t : ℂ) • V) * ((t : ℂ) • V)ᴴ).PosSemidef := by
  have e : 1 - ((t : ℂ) • V) * ((t : ℂ) • V)ᴴ = ((1 - t ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    module
  rw [e]
  exact PosSemidef.one.smul (by exact_mod_cast (sub_nonneg.2 ht))

/-- **The regulated twisted kernel is the scalar Poisson kernel** (deterministic, Hermitian
collar blocks): for `0 ≤ t < 1`, `u*𝒫(tU_s r')u = P(wζ_t)`, `ζ_t = 1 - (u*(1 - tV)⁻¹u)⁻¹`,
`r' = oldScattering (twistOld b e w u X)`. -/
theorem quadForm_middleKernel_twistOld (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {u : Fin 2 × Fin W → ℂ} (hu : star u ⬝ᵥ u = 1) {w : ℂ} (hw : ‖w‖ < 1)
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    quadForm (middleKernel b e s t (twistOld b e w u X) ω) u =
        pk w (1 - (closedQuad b e s t X u ω)⁻¹) ∧
      1 / 2 ≤ (closedQuad b e s t X u ω).re := by
  set V := closedScattering b e s X ω
  have hV := closedScattering_mul_conjTranspose b e s hη hX hA hG
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hT : IsUnit (1 - (t : ℂ) • V).det :=
    isUnit_det_one_sub_smul (by rw [hV, sub_self]; exact PosSemidef.zero) ht0 ht1
  have hT' : IsUnit (1 - ((t : ℂ) • V) * twist w u).det := by
    rw [Matrix.smul_mul]
    exact isUnit_det_one_sub_smul (posSemidef_one_sub_mul_twist hV hw hu) ht0 ht1
  have hre : 1 / 2 ≤ (closedQuad b e s t X u ω).re :=
    re_quad_inv_ge ((t : ℂ) • V) hu hT (smul_contraction hV ht2)
  have hq : closedQuad b e s t X u ω ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hre; norm_num at hre
  refine ⟨?_, hre⟩
  have hk : middleKernel b e s t (twistOld b e w u X) ω =
      poissonKernel (((t : ℂ) • V) * twist w u) := by
    rw [middleKernel, oldScattering_twistOld hη hX hu hw, Matrix.smul_mul]
    simp only [V, closedScattering, Matrix.mul_assoc]
  rw [hk]
  exact quadForm_poissonKernel_twist _ hu w hT hT' hq

/-- **`I - U_sr` is invertible almost surely** (`s = x/(Wρ)`): otherwise the closing matrix of the
rank-one frame `u` would be `iI`, which is not Hermitian, while it equals the Hermitian value
`F_W(x)` a.s. (`ae_collarFunction_eval_eq`). -/
theorem ae_isUnit_det_one_sub_closedScattering {b : ℝ} (hb : b < 1 / 2) (hW : 0 < W) (e : ℝ)
    (hη : 0 < (boundaryZ b e).im) (hc : 0 < poleScale W e)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {u : Fin 2 × Fin W → ℂ} (hu : star u ⬝ᵥ u = 1) (x : ℝ) :
    ∀ᵐ ω ∂collarLaw W b, IsUnit (1 - closedScattering b e (microShift W e x) X ω).det := by
  set J₁ : Matrix (Fin 2 × Fin W) (Fin 1) ℂ := Matrix.of fun i _ => u i
  have hJ : J₁ᴴ * J₁ = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp only [J₁, mul_apply, conjTranspose_apply, of_apply, one_apply_eq]
    rw [← hu]; rfl
  filter_upwards [ae_collarFunction_eval_eq hb hW e hη hc hX J₁ x] with ω hω
  by_contra hnot
  have hH := collarFunction_eval_ofReal_isHermitian b e X J₁ ω x
  rw [hω] at hH
  have hinv : (1 - middleScattering b e (microShift W e x) ω * oldScattering b e X)⁻¹ = 0 :=
    nonsing_inv_apply_not_isUnit _ hnot
  have hC : closingMatrix b e (microShift W e x) X J₁ ω = Complex.I • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [closingMatrix, hinv, smul_zero, zero_sub, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one,
      hJ, smul_neg, ← neg_smul, neg_neg]
  rw [hC] at hH
  have := congrFun (congrFun hH 0) 0
  simp only [conjTranspose_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one,
    Complex.star_def, Complex.conj_I] at this
  have h2 := congrArg Complex.im this
  simp at h2
  norm_num at h2

theorem quadForm_sub' {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (u : ι → ℂ) :
    quadForm (A - B) u = quadForm A u - quadForm B u := by
  unfold quadForm; rw [sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem sum_norm_sq_eq_one {ι : Type} [Fintype ι] {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    ∑ i, ‖u i‖ ^ 2 = 1 := by
  rw [← BlockBand.Wegner.re_star_dotProduct_self, hu, Complex.one_re]

/-- Continuity of `t ↦ u*(I - tV)⁻¹u` at `t = 1` when `I - V` is invertible. -/
theorem continuousAt_closedQuad (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) (ω : CollarSample W)
    (h : IsUnit (1 - closedScattering b e s X ω).det) :
    ContinuousAt (fun t : ℝ => closedQuad b e s t X u ω) 1 := by
  set V := closedScattering b e s X ω
  have hp : Continuous fun t : ℝ => (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - (t : ℂ) • V :=
    continuous_const.sub ((Complex.continuous_ofReal).smul continuous_const)
  have h1 : (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - ((1 : ℝ) : ℂ) • V = 1 - V := by
    rw [Complex.ofReal_one, one_smul]
  have hdinv : ContinuousAt Ring.inverse
      ((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - ((1 : ℝ) : ℂ) • V).det := by
    rw [h1, ← h.unit_spec]
    exact (analyticAt_inverse (𝕜 := ℂ) h.unit).continuousAt
  have hinv : ContinuousAt (fun t : ℝ => ((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      (t : ℂ) • V)⁻¹) 1 :=
    ContinuousAt.comp (g := Inv.inv) (f := fun t : ℝ => (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      (t : ℂ) • V) (continuousAt_matrix_inv _ hdinv) hp.continuousAt
  unfold closedQuad
  have hmv : Continuous fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => star u ⬝ᵥ (M *ᵥ u) := by
    unfold dotProduct mulVec dotProduct
    fun_prop
  exact hmv.continuousAt.comp hinv

/-- **The Poisson estimate for the closing phase** (the shifted kernel estimate is uniform
in every twist, and its scalar Poisson kernels are integrated before letting `ρ ↑ 1`). Fix a Hermitian old response, a unit vector `u` and
`‖w‖ < 1`. If the radially regulated middle-shifted kernel at the twisted response
`X' = twistOld b e w u X` satisfies `‖E𝒫(tU_s r') - I‖ ≤ err + δ` for all `t` close to one (every
`δ > 0`), and `I - U_s r` is a.s. invertible, then `|E P(wζ) - 1| ≤ err`,
`ζ = 1 - (u*(I - U_s r)⁻¹u)⁻¹`. -/
theorem abs_integral_pk_sub_one_le {b e s : ℝ} (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {u : Fin 2 × Fin W → ℂ} (hu : star u ⬝ᵥ u = 1) {w : ℂ} (hw : ‖w‖ < 1)
    (hinv : ∀ᵐ ω ∂collarLaw W b, IsUnit (1 - closedScattering b e s X ω).det) {err : ℝ}
    (hk : ∀ δ : ℝ, 0 < δ → ∃ t₀ : ℝ, t₀ < 1 ∧ ∀ t ∈ Set.Ioo t₀ 1,
      MiddleKernelIntegrable b e s t (twistOld b e w u X) ∧
        ‖expectedMiddleKernel b e s t (twistOld b e w u X) - 1‖ ≤ err + δ) :
    |∫ ω, pk w (1 - (closedQuad b e s 1 X u ω)⁻¹) ∂collarLaw W b - 1| ≤ err := by
  have hH := Collar.Density.ae_collarMatrix_isHermitian b e hX (W := W)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨t₀, ht₀, hk'⟩ := hk δ hδ
  set t₁ := max t₀ 0
  have ht₁ : t₁ < 1 := max_lt ht₀ (by norm_num)
  set τ : ℕ → ℝ := fun m => 1 - (1 - t₁) / ((m : ℝ) + 2)
  have hτ : ∀ m, τ m ∈ Set.Ioo t₀ 1 ∧ 0 ≤ τ m := by
    intro m
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h1 : (1 - t₁) / ((m : ℝ) + 2) < 1 - t₁ := by
      rw [div_lt_iff₀ hm]; nlinarith [sub_pos.2 ht₁, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h2 : 0 < (1 - t₁) / ((m : ℝ) + 2) := div_pos (by linarith) hm
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := le_max_left t₀ 0; simp only [τ]; linarith
    · simp only [τ]; linarith
    · have := le_max_right t₀ 0; simp only [τ]; linarith
  have hτlim : Tendsto τ atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => (1 - t₁) / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [τ] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  set X' := twistOld b e w u X
  set F : ℕ → CollarSample W → ℝ := fun m ω => quadForm (middleKernel b e s (τ m) X' ω) u
  set f : CollarSample W → ℝ := fun ω => pk w (1 - (closedQuad b e s 1 X u ω)⁻¹)
  have hFmeas : ∀ m, AEStronglyMeasurable (F m) (collarLaw W b) := by
    intro m
    have hm := measurable_middleKernel b e s (τ m) X' (W := W)
    have hq : Continuous fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => quadForm M u := by
      unfold quadForm dotProduct mulVec dotProduct
      fun_prop
    exact (hq.measurable.comp hm).aestronglyMeasurable
  have hFeq : ∀ m, ∀ᵐ ω ∂collarLaw W b,
      F m ω = pk w (1 - (closedQuad b e s (τ m) X u ω)⁻¹) ∧
        ‖1 - (closedQuad b e s (τ m) X u ω)⁻¹‖ ≤ 1 := by
    intro m
    filter_upwards [hH] with ω hω
    obtain ⟨h1, h2⟩ := quadForm_middleKernel_twistOld b e s hη hX hu hw hω.2.1 hω.2.2
      (hτ m).2 (hτ m).1.2
    exact ⟨h1, norm_one_sub_inv_le h2⟩
  have hbound : ∀ m, ∀ᵐ ω ∂collarLaw W b, ‖F m ω‖ ≤ 2 * (1 - ‖w‖)⁻¹ + 1 := by
    intro m
    filter_upwards [hFeq m] with ω hω
    rw [hω.1, Real.norm_eq_abs]
    exact abs_pk_le hw hω.2
  have hlim : ∀ᵐ ω ∂collarLaw W b, Tendsto (fun m => F m ω) atTop (𝓝 (f ω)) := by
    have hall : ∀ᵐ ω ∂collarLaw W b, ∀ m, F m ω = pk w (1 - (closedQuad b e s (τ m) X u ω)⁻¹) :=
      ae_all_iff.2 fun m => (hFeq m).mono fun ω h => h.1
    filter_upwards [hall, hinv, hH] with ω hω hinvω hHω
    simp only [hω]
    have hq1 := continuousAt_closedQuad b e s X u ω hinvω
    have hV := closedScattering_mul_conjTranspose b e s hη hX hHω.2.1 hHω.2.2
    have hre : (closedQuad b e s 1 X u ω).re = 1 / 2 := by
      have := re_quad_inv_eq (closedScattering b e s X ω) hu hinvω hV
      simpa [closedQuad] using this
    have hq0 : closedQuad b e s 1 X u ω ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hre; norm_num at hre
    have hζ : ‖1 - (closedQuad b e s 1 X u ω)⁻¹‖ ≤ 1 := norm_one_sub_inv_le hre.symm.le
    have hc : ContinuousAt (fun t : ℝ => pk w (1 - (closedQuad b e s t X u ω)⁻¹)) 1 := by
      exact ContinuousAt.comp (g := fun z => pk w z)
        (f := fun t : ℝ => 1 - (closedQuad b e s t X u ω)⁻¹)
        (continuousAt_pk (one_sub_ne_zero_of_norm_lt (norm_mul_lt_one hw hζ)))
        (continuousAt_const.sub (hq1.inv₀ hq0))
    exact hc.tendsto.comp hτlim
  have hDCT := tendsto_integral_of_dominated_convergence (μ := collarLaw W b)
    (fun _ => 2 * (1 - ‖w‖)⁻¹ + 1) hFmeas (integrable_const _) hbound hlim
  have hmean : ∀ m, |∫ ω, F m ω ∂collarLaw W b - 1| ≤ err + δ := by
    intro m
    obtain ⟨hint, hnorm⟩ := hk' (τ m) (hτ m).1
    obtain ⟨-, hEq⟩ := integral_quadForm_eq hint u
    have hE : ∫ ω, F m ω ∂collarLaw W b = quadForm (expectedMiddleKernel b e s (τ m) X') u := hEq
    rw [hE]
    have h1 : quadForm (expectedMiddleKernel b e s (τ m) X') u - 1 =
        quadForm (expectedMiddleKernel b e s (τ m) X' - 1) u := by
      rw [quadForm_sub', quadForm_one, sum_norm_sq_eq_one hu]
    rw [h1]
    refine (abs_quadForm_le_opNorm _ u).trans ?_
    rw [sum_norm_sq_eq_one hu, mul_one]
    exact hnorm
  have hcl : Tendsto (fun m => |∫ ω, F m ω ∂collarLaw W b - 1|) atTop
      (𝓝 |∫ ω, f ω ∂collarLaw W b - 1|) :=
    (continuous_abs.tendsto _).comp (hDCT.sub_const 1)
  exact le_of_tendsto' hcl hmean

end BlockBand.Critical.MatrixClosing.Boundary
