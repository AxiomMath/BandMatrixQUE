module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Theorem
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Operator.Bilinear
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Second-order calculus for the Itô reduction)

Deterministic. For `f` of class `C²` on an open set:

* `fderiv_comp_clm_apply`, `fderiv2_comp_clm_apply`: first and second derivatives of `φ ∘ L`
  for a continuous linear map `L`: `D(φ∘L)(z) v = Dφ(Lz)(Lv)`,
  `D²(φ∘L)(z) v w = D²φ(Lz)(Lv)(Lw)`;
* `fderiv_sub_clm`, `fderiv2_sub_clm`: subtracting a continuous linear map `ℓ` changes
  the first derivative by `ℓ` and leaves the second derivative unchanged;
* `fderiv_sq`, `fderiv2_sq_apply`: for `ψ = h·h`,
  `Dψ = 2h Dh` and `D²ψ v w = 2 (h D²h v w + Dh v Dh w)`;
* `schemeGen_sq`: the generator of `h·h` is `2 h 𝓛h + Σ_{ij} α^{ij} ∂_ih ∂_jh` (no symmetry of
  `α` used).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem differentiableAt_of_contDiffOn {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 2 f O) {z : E} (hz : z ∈ O) : DifferentiableAt ℝ f z :=
  (hf.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds hz)

theorem differentiableAt_fderiv_of_contDiffOn {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 2 f O) {z : E} (hz : z ∈ O) : DifferentiableAt ℝ (fderiv ℝ f) z :=
  ((hf.fderiv_of_isOpen hO (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt
    (hO.mem_nhds hz)

theorem fderiv_comp_clm {φ : F → ℝ} {O : Set F} (hO : IsOpen O) (hφ : ContDiffOn ℝ 2 φ O)
    (L : E →L[ℝ] F) {z : E} (hz : L z ∈ O) :
    fderiv ℝ (fun y => φ (L y)) z = (fderiv ℝ φ (L z)).comp L := by
  have := fderiv_comp (𝕜 := ℝ) (g := φ) (f := L) z (differentiableAt_of_contDiffOn hO hφ hz)
    L.differentiableAt
  rw [show (fun y => φ (L y)) = φ ∘ L from rfl, this, L.fderiv]

theorem fderiv_comp_clm_apply {φ : F → ℝ} {O : Set F} (hO : IsOpen O) (hφ : ContDiffOn ℝ 2 φ O)
    (L : E →L[ℝ] F) {z : E} (hz : L z ∈ O) (v : E) :
    fderiv ℝ (fun y => φ (L y)) z v = fderiv ℝ φ (L z) (L v) := by
  rw [fderiv_comp_clm hO hφ L hz]; rfl

theorem fderiv2_comp_clm_apply {φ : F → ℝ} {O : Set F} (hO : IsOpen O)
    (hφ : ContDiffOn ℝ 2 φ O) (L : E →L[ℝ] F) {z : E} (hz : L z ∈ O) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => φ (L y))) z v w = fderiv ℝ (fderiv ℝ φ) (L z) (L v) (L w) := by
  set P : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E F ℝ).flip L
  have hO' : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have hev : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z] fun y => P (fderiv ℝ φ (L y)) := by
    filter_upwards [hO'.mem_nhds hz] with y hy
    rw [fderiv_comp_clm hO hφ L hy]; rfl
  rw [hev.fderiv_eq]
  have h1 : HasFDerivAt (fun y => fderiv ℝ φ (L y)) ((fderiv ℝ (fderiv ℝ φ) (L z)).comp L) z :=
    (differentiableAt_fderiv_of_contDiffOn hO hφ hz).hasFDerivAt.comp z L.hasFDerivAt
  have h2 := (P.hasFDerivAt.comp z h1).fderiv
  rw [show (fun y => P (fderiv ℝ φ (L y))) = P ∘ fun y => fderiv ℝ φ (L y) from rfl, h2]
  rfl

theorem fderiv_sub_clm {g : E → ℝ} {O : Set E} (hO : IsOpen O) (hg : ContDiffOn ℝ 2 g O)
    (ℓ : E →L[ℝ] ℝ) {z : E} (hz : z ∈ O) :
    fderiv ℝ (fun y => g y - ℓ y) z = fderiv ℝ g z - ℓ := by
  rw [fderiv_fun_sub (differentiableAt_of_contDiffOn hO hg hz) ℓ.differentiableAt, ℓ.fderiv]

theorem fderiv2_sub_clm {g : E → ℝ} {O : Set E} (hO : IsOpen O) (hg : ContDiffOn ℝ 2 g O)
    (ℓ : E →L[ℝ] ℝ) {z : E} (hz : z ∈ O) :
    fderiv ℝ (fderiv ℝ (fun y => g y - ℓ y)) z = fderiv ℝ (fderiv ℝ g) z := by
  have hev : fderiv ℝ (fun y => g y - ℓ y) =ᶠ[𝓝 z] fun y => fderiv ℝ g y - ℓ := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact fderiv_sub_clm hO hg ℓ hy
  rw [hev.fderiv_eq, fderiv_sub_const]

theorem fderiv_sq {h : E → ℝ} {O : Set E} (hO : IsOpen O) (hh : ContDiffOn ℝ 2 h O) {z : E}
    (hz : z ∈ O) : fderiv ℝ (fun y => h y * h y) z = (2 * h z) • fderiv ℝ h z := by
  rw [fderiv_fun_mul (differentiableAt_of_contDiffOn hO hh hz)
    (differentiableAt_of_contDiffOn hO hh hz), ← add_smul, two_mul]

theorem fderiv2_sq_apply {h : E → ℝ} {O : Set E} (hO : IsOpen O) (hh : ContDiffOn ℝ 2 h O)
    {z : E} (hz : z ∈ O) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => h y * h y)) z v w =
      2 * h z * fderiv ℝ (fderiv ℝ h) z v w + 2 * fderiv ℝ h z v * fderiv ℝ h z w := by
  have hev : fderiv ℝ (fun y => h y * h y) =ᶠ[𝓝 z] fun y => (2 * h y) • fderiv ℝ h y := by
    filter_upwards [hO.mem_nhds hz] with y hy
    exact fderiv_sq hO hh hy
  have hd : DifferentiableAt ℝ h z := differentiableAt_of_contDiffOn hO hh hz
  rw [hev.fderiv_eq, fderiv_fun_smul (hd.const_mul 2)
    (differentiableAt_fderiv_of_contDiffOn hO hh hz), fderiv_const_mul hd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]

variable {Ω : Type*} {d : ℕ}

/-- **Generator of a square**: `𝓛(h²) = 2 h 𝓛h + Σ_{ij} α^{ij} ∂_ih ∂_jh` at points of the open
set where `h` is `C²`. -/
theorem schemeGen_sq {h : (Fin d → ℝ) → ℝ} {O : Set (Fin d → ℝ)} (hO : IsOpen O)
    (hh : ContDiffOn ℝ 2 h O) (Z β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Fin d → Fin d → ℝ)
    {u : ℝ≥0} {ω : Ω} (hz : Z u ω ∈ O) :
    schemeGen (fun y => h y * h y) Z β α u ω = 2 * h (Z u ω) * schemeGen h Z β α u ω +
      ∑ i, ∑ j, α u ω i j * fderiv ℝ h (Z u ω) (ev i) * fderiv ℝ h (Z u ω) (ev j) := by
  unfold schemeGen
  simp only [fderiv_sq hO hh hz, fderiv2_sq_apply hO hh hz, smul_apply,
    smul_eq_mul]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∀ i, β u ω i * (2 * h (Z u ω) * fderiv ℝ h (Z u ω) (ev i)) =
      2 * h (Z u ω) * (β u ω i * fderiv ℝ h (Z u ω) (ev i)) := fun i => by ring
  have e2 : ∀ i j, 1 / 2 * (α u ω i j * (2 * h (Z u ω) * fderiv ℝ (fderiv ℝ h) (Z u ω) (ev i)
      (ev j))) = 2 * h (Z u ω) * (1 / 2 * (α u ω i j * fderiv ℝ (fderiv ℝ h) (Z u ω) (ev i)
      (ev j))) := fun i j => by ring
  have e3 : ∀ i j, 1 / 2 * (α u ω i j * (2 * fderiv ℝ h (Z u ω) (ev i) *
      fderiv ℝ h (Z u ω) (ev j))) =
      α u ω i j * fderiv ℝ h (Z u ω) (ev i) * fderiv ℝ h (Z u ω) (ev j) := fun i j => by ring
  simp only [e1, e2, e3]
  ring

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
