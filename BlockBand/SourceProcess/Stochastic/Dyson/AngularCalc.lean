module

public import BlockBand.SourceProcess.Stochastic.Dyson.Partials
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Generator calculus for time-independent test functions)

For `g : ℝ^d → ℝ` the generator with drift `b` and covariance `a` is
`genL g y b a = Dg(y)[b] + ½ ∑_{k,l} a_kl D²g(y)[e_k, e_l]`; for `C²` functions it is the
contract's `itoDrift` of `(t, y) ↦ g(y)` (`itoDrift_eq_genL`). Product rule (`genL_mul`) and
composition with continuous linear maps (`fderiv2_comp_clm_apply`) are recorded, together with
one-variable second derivatives (`fderiv2_real_apply`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open Filter Topology
open scoped NNReal ContDiff
open BlockBand.Internal.Contracts.Transmission

variable {d : ℕ}

/-- Generator of a time-independent function: `Dg(y)[b] + ½ ∑ a_kl D²g(y)[e_k, e_l]`. -/
def genL (g : (Fin d → ℝ) → ℝ) (y b : Fin d → ℝ) (a : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  fderiv ℝ g y b + (1 / 2 : ℝ) * ∑ k, ∑ l, a k l *
    fderiv ℝ (fderiv ℝ g) y (Pi.single k 1) (Pi.single l 1)

/-- A real linear functional on `ℝ^d` in coordinates. -/
theorem clm_apply_eq_sum (L : (Fin d → ℝ) →L[ℝ] ℝ) (b : Fin d → ℝ) :
    L b = ∑ i, b i * L (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ' b]
  simp [map_sum]

/-- **The contract's Itô drift of a time-independent `C²` function is `genL`.** -/
theorem itoDrift_eq_genL {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ} (hg : ContDiffAt ℝ 2 g y)
    (t : ℝ≥0) (b : Fin d → ℝ) (a : Matrix (Fin d) (Fin d) ℝ) :
    itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) y t b a = genL g y b a := by
  unfold itoDrift genL
  rw [partialTime_comp_snd (hg.differentiableAt (by norm_num)), zero_add,
    clm_apply_eq_sum (fderiv ℝ g y) b]
  simp_rw [partialSpace_comp_snd (hg.differentiableAt (by norm_num)), partialSpace2_comp_snd hg]

theorem diff_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    {y : E} (hg : ContDiffAt ℝ 2 g y) (v : E) :
    DifferentiableAt ℝ (fun y' => fderiv ℝ g y' v) y :=
  ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const v)

theorem fderiv2_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}
    {y : E} (hg : ContDiffAt ℝ 2 g y) (u v : E) :
    fderiv ℝ (fderiv ℝ g) y u v = fderiv ℝ (fun y' => fderiv ℝ g y' v) y u :=
  fderiv_fderiv_apply' ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)) u v

theorem fderiv_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g₁ g₂ : E → ℝ}
    {y : E} (h₁ : DifferentiableAt ℝ g₁ y) (h₂ : DifferentiableAt ℝ g₂ y) (v : E) :
    fderiv ℝ (fun y => g₁ y * g₂ y) y v = g₁ y * fderiv ℝ g₂ y v + g₂ y * fderiv ℝ g₁ y v := by
  rw [fderiv_fun_mul h₁ h₂]; simp

/-- Second derivative of a product. -/
theorem fderiv2_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g₁ g₂ : E → ℝ}
    {y : E} (h₁ : ContDiffAt ℝ 2 g₁ y) (h₂ : ContDiffAt ℝ 2 g₂ y) (u v : E) :
    fderiv ℝ (fderiv ℝ fun y => g₁ y * g₂ y) y u v =
      fderiv ℝ g₁ y u * fderiv ℝ g₂ y v + g₁ y * fderiv ℝ (fderiv ℝ g₂) y u v +
        (fderiv ℝ g₂ y u * fderiv ℝ g₁ y v + g₂ y * fderiv ℝ (fderiv ℝ g₁) y u v) := by
  rw [fderiv2_eq (h₁.mul h₂), fderiv2_eq h₁, fderiv2_eq h₂]
  have hev : (fun y' => fderiv ℝ (fun y => g₁ y * g₂ y) y' v) =ᶠ[𝓝 y]
      fun y' => g₁ y' * fderiv ℝ g₂ y' v + g₂ y' * fderiv ℝ g₁ y' v := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' e1 e2
    exact fderiv_mul_apply (e1.differentiableAt (by norm_num)) (e2.differentiableAt (by norm_num)) v
  rw [hev.fderiv_eq]
  have d1 := h₁.differentiableAt (by norm_num)
  have d2 := h₂.differentiableAt (by norm_num)
  have m1 : DifferentiableAt ℝ (fun y' => g₁ y' * fderiv ℝ g₂ y' v) y :=
    d1.mul (diff_fderiv_apply h₂ v)
  have m2 : DifferentiableAt ℝ (fun y' => g₂ y' * fderiv ℝ g₁ y' v) y :=
    d2.mul (diff_fderiv_apply h₁ v)
  rw [fderiv_fun_add m1 m2]
  simp only [FunLike.coe_add, Pi.add_apply]
  rw [fderiv_mul_apply d1 (diff_fderiv_apply h₂ v),
    fderiv_mul_apply d2 (diff_fderiv_apply h₁ v)]
  ring

/-- **Product rule for the generator.** -/
theorem genL_mul {g₁ g₂ : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ} (h₁ : ContDiffAt ℝ 2 g₁ y)
    (h₂ : ContDiffAt ℝ 2 g₂ y) (b : Fin d → ℝ) (a : Matrix (Fin d) (Fin d) ℝ) :
    genL (fun y => g₁ y * g₂ y) y b a = g₁ y * genL g₂ y b a + g₂ y * genL g₁ y b a +
      (1 / 2 : ℝ) * ∑ k, ∑ l, a k l * (fderiv ℝ g₁ y (Pi.single k 1) *
        fderiv ℝ g₂ y (Pi.single l 1) + fderiv ℝ g₂ y (Pi.single k 1) *
          fderiv ℝ g₁ y (Pi.single l 1)) := by
  unfold genL
  rw [fderiv_mul_apply (h₁.differentiableAt (by norm_num)) (h₂.differentiableAt (by norm_num))]
  simp_rw [fderiv2_mul_apply h₁ h₂]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∀ k l, a k l * (g₁ y * fderiv ℝ (fderiv ℝ g₂) y (Pi.single k 1) (Pi.single l 1)) =
      g₁ y * (a k l * fderiv ℝ (fderiv ℝ g₂) y (Pi.single k 1) (Pi.single l 1)) :=
    fun _ _ => by ring
  have e2 : ∀ k l, a k l * (g₂ y * fderiv ℝ (fderiv ℝ g₁) y (Pi.single k 1) (Pi.single l 1)) =
      g₂ y * (a k l * fderiv ℝ (fderiv ℝ g₁) y (Pi.single k 1) (Pi.single l 1)) :=
    fun _ _ => by ring
  simp_rw [e1, e2, ← Finset.mul_sum]
  ring

/-- **Vanishing cross term** when the covariance does not couple the supports. -/
theorem cross_eq_zero {g₁ g₂ : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ} (a : Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ k l, a k l ≠ 0 → (fderiv ℝ g₁ y (Pi.single k 1) = 0 ∨
      fderiv ℝ g₂ y (Pi.single l 1) = 0) ∧ (fderiv ℝ g₂ y (Pi.single k 1) = 0 ∨
      fderiv ℝ g₁ y (Pi.single l 1) = 0)) :
    ∑ k, ∑ l, a k l * (fderiv ℝ g₁ y (Pi.single k 1) * fderiv ℝ g₂ y (Pi.single l 1) +
      fderiv ℝ g₂ y (Pi.single k 1) * fderiv ℝ g₁ y (Pi.single l 1)) = 0 := by
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  by_cases hkl : a k l = 0
  · simp [hkl]
  obtain ⟨h1, h2⟩ := h k l hkl
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

/-!
### Composition with continuous linear maps
-/

theorem fderiv_comp_clm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (L : (Fin d → ℝ) →L[ℝ] E) {y : Fin d → ℝ} (hh : DifferentiableAt ℝ h (L y))
    (v : Fin d → ℝ) : fderiv ℝ (fun y => h (L y)) y v = fderiv ℝ h (L y) (L v) := by
  rw [show (fun y => h (L y)) = h ∘ L from rfl, (hh.hasFDerivAt.comp y L.hasFDerivAt).fderiv]
  rfl

theorem fderiv2_comp_clm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {h : E → ℝ}
    (L : (Fin d → ℝ) →L[ℝ] E) {y : Fin d → ℝ} (hh : ContDiffAt ℝ 2 h (L y))
    (u v : Fin d → ℝ) :
    fderiv ℝ (fderiv ℝ fun y => h (L y)) y u v = fderiv ℝ (fderiv ℝ h) (L y) (L u) (L v) := by
  have hc : ContDiffAt ℝ 2 (fun y => h (L y)) y := hh.comp y L.contDiff.contDiffAt
  rw [fderiv2_eq hc, fderiv2_eq hh]
  have hev : (fun y' => fderiv ℝ (fun y => h (L y)) y' v) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ h (L y') (L v) := by
    have : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 h (L y') :=
      (L.continuous.tendsto y).eventually (hh.eventually (by simp))
    filter_upwards [this] with y' hy'
    exact fderiv_comp_clm_apply L (hy'.differentiableAt (by norm_num)) v
  rw [hev.fderiv_eq]
  exact fderiv_comp_clm_apply (h := fun z => fderiv ℝ h z (L v)) L (diff_fderiv_apply hh _) u

/-!
### One-variable functions
-/

theorem fderiv_real_apply {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x) (x w : ℝ) :
    fderiv ℝ h x w = h' x * w := by
  rw [(hd x).hasFDerivAt.fderiv]; simp [mul_comm]

theorem fderiv2_real_apply {h h' h'' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hd' : ∀ x, HasDerivAt h' (h'' x) x) (x w w' : ℝ) :
    fderiv ℝ (fderiv ℝ h) x w w' = h'' x * w * w' := by
  have e : fderiv ℝ h = fun x => h' x • ContinuousLinearMap.id ℝ ℝ := by
    funext x; ext; simp [fderiv_real_apply hd]
  rw [e, ((hd' x).hasFDerivAt.smul_const (ContinuousLinearMap.id ℝ ℝ)).fderiv]
  simp [mul_comm, mul_left_comm]

theorem contDiff_real_of_deriv {h h' h'' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hd' : ∀ x, HasDerivAt h' (h'' x) x) (hc : Continuous h'') : ContDiff ℝ 2 h := by
  have h1 : ContDiff ℝ 1 h' := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun x => (hd' x).differentiableAt, by
      rw [show deriv h' = h'' from funext fun x => (hd' x).deriv]; exact hc⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
  rw [show deriv h = h' from funext fun x => (hd x).deriv]; exact h1

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
