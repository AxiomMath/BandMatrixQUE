module

public import BlockBand.Transmission.LawDuality.RatioKernel
public import BlockBand.Transmission.LawDuality.Interface

/-!
# `RatioDualityPrinciple`: `𝒟_p F_·(ν)` in closed form

For a fixed finite measure `ν` on `[0,1]`, on the open set `ratioOpen p = {z | x_i > −1, y_i < 1}`
(which contains the chamber), with `A₁ = lkerInt1 ν` (`= −∫(1+xt)⁻¹dν`), `A₂ = lkerInt2 ν`
(`= ∫t(1+xt)⁻²dν`) and `F = F_{x,y}(ν)`:
* `∂_{x_i}F = F·A₁(x_i)`, `∂_{y_j}F = F·A₁(−y_j)` (`fderiv_ratioOn_dirX`, `fderiv_ratioOn_dirY`);
* `∂²_{x_i}F = F·(A₁(x_i)² + A₂(x_i))`, `∂²_{y_j}F = F·(A₁(−y_j)² − A₂(−y_j))`
  (`fderiv_fderiv_ratioOn_dirX`, `fderiv_fderiv_ratioOn_dirY`), in exactly the iterated-`fderiv` form used by
  `dualGenerator`;
* **`dualGenerator_ratioOn`**: the closed form of `𝒟_p F_·(ν)(z)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable (ν : FiniteMeasure unitInterval) {p : ℕ}

/-- The open domain of the closed forms: `x_i > −1`, `y_i < 1`. -/
def ratioOpen (p : ℕ) : Set (DualCoord p) := {z | ∀ i, -1 < z.1 i ∧ z.2 i < 1}

theorem isOpen_ratioOpen : IsOpen (ratioOpen p) := by
  have e : ratioOpen p = ⋂ i, ({z : DualCoord p | -1 < z.1 i} ∩ {z | z.2 i < 1}) := by
    ext z; simp [ratioOpen, forall_and]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)).inter
      (isOpen_lt ((continuous_apply i).comp continuous_snd) continuous_const)

theorem dualChamber_subset_ratioOpen : dualChamber p ⊆ ratioOpen p := fun z hz i =>
  ⟨by linarith [hz.2.2.1 i], (hz.2.2.2 i).2⟩

/-- The exponent `Λ(z) = Σ_i (A_ν(x_i) − A_ν(−y_i))`. -/
def ratioExp (z : DualCoord p) : ℝ := ∑ i, (lkerInt ν (z.1 i) - lkerInt ν (-z.2 i))

theorem ratioOn_eq_exp {z : DualCoord p} (hz : z ∈ ratioOpen p) :
    ratioOn ν z = Real.exp (ratioExp ν z) :=
  transmissionRatio_eq_exp_lker ν (fun i => (hz i).1) fun i => (hz i).2

/-- Coordinate projections. -/
def prX (i : Fin p) : DualCoord p →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin p → ℝ) (Fin p → ℝ))

def prY (i : Fin p) : DualCoord p →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Fin p → ℝ) (Fin p → ℝ))

theorem prX_apply (i : Fin p) (v : DualCoord p) : prX i v = v.1 i := rfl
theorem prY_apply (i : Fin p) (v : DualCoord p) : prY i v = v.2 i := rfl

/-- The derivative of the exponent. -/
def ratioExpD (z : DualCoord p) : DualCoord p →L[ℝ] ℝ :=
  ∑ i, (lkerInt1 ν (z.1 i) • prX i + lkerInt1 ν (-z.2 i) • prY i)

theorem hasDerivAt_lkerInt_negY {z : DualCoord p} (hz : z ∈ ratioOpen p) (i : Fin p) :
    -1 < -z.2 i := by linarith [(hz i).2]

theorem hasFDerivAt_ratioExp {z : DualCoord p} (hz : z ∈ ratioOpen p) :
    HasFDerivAt (ratioExp ν) (ratioExpD ν z) z := by
  unfold ratioExp ratioExpD
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have h1 := (hasDerivAt_lkerInt ν (hz i).1).comp_hasFDerivAt z (prX i).hasFDerivAt
  have h2 := (hasDerivAt_lkerInt ν (hasDerivAt_lkerInt_negY hz i)).comp_hasFDerivAt z
    (prY i).hasFDerivAt.neg
  convert h1.sub h2 using 1
  · funext w; rfl
  · rw [smul_neg, sub_neg_eq_add]

theorem ratioExpD_dirX (z : DualCoord p) (i : Fin p) :
    ratioExpD ν z (dirX i) = lkerInt1 ν (z.1 i) := by
  simp [ratioExpD, dirX, prX_apply, prY_apply, Pi.single_apply]

theorem ratioExpD_dirY (z : DualCoord p) (j : Fin p) :
    ratioExpD ν z (dirY j) = lkerInt1 ν (-z.2 j) := by
  simp [ratioExpD, dirY, prX_apply, prY_apply, Pi.single_apply]

theorem hasFDerivAt_ratioOn {z : DualCoord p} (hz : z ∈ ratioOpen p) :
    HasFDerivAt (ratioOn ν) (Real.exp (ratioExp ν z) • ratioExpD ν z) z := by
  have h := (hasFDerivAt_ratioExp ν hz).exp
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ratioOpen.mem_nhds hz] with w hw using ratioOn_eq_exp ν hw

/-- **`∂_{x_i}F = F·A₁(x_i)`.** -/
theorem fderiv_ratioOn_dirX {z : DualCoord p} (hz : z ∈ ratioOpen p) (i : Fin p) :
    fderiv ℝ (ratioOn ν) z (dirX i) = ratioOn ν z * lkerInt1 ν (z.1 i) := by
  rw [(hasFDerivAt_ratioOn ν hz).fderiv]
  change Real.exp (ratioExp ν z) * ratioExpD ν z (dirX i) = _
  rw [ratioExpD_dirX, ratioOn_eq_exp ν hz]

/-- **`∂_{y_j}F = F·A₁(−y_j)`.** -/
theorem fderiv_ratioOn_dirY {z : DualCoord p} (hz : z ∈ ratioOpen p) (j : Fin p) :
    fderiv ℝ (ratioOn ν) z (dirY j) = ratioOn ν z * lkerInt1 ν (-z.2 j) := by
  rw [(hasFDerivAt_ratioOn ν hz).fderiv]
  change Real.exp (ratioExp ν z) * ratioExpD ν z (dirY j) = _
  rw [ratioExpD_dirY, ratioOn_eq_exp ν hz]

/-- **`∂²_{x_i}F = F·(A₁(x_i)² + A₂(x_i))`** (iterated `fderiv`, as in `dualGenerator`). -/
theorem fderiv_fderiv_ratioOn_dirX {z : DualCoord p} (hz : z ∈ ratioOpen p) (i : Fin p) :
    fderiv ℝ (fun w => fderiv ℝ (ratioOn ν) w (dirX i)) z (dirX i) =
      ratioOn ν z * (lkerInt1 ν (z.1 i) ^ 2 + lkerInt2 ν (z.1 i)) := by
  have hE := (hasFDerivAt_ratioExp ν hz).exp
  have hA := (hasDerivAt_lkerInt1 ν (hz i).1).comp_hasFDerivAt z (prX i).hasFDerivAt
  have h := hE.mul hA
  have h' := h.congr_of_eventuallyEq (f₁ := fun w => fderiv ℝ (ratioOn ν) w (dirX i)) (by
    filter_upwards [isOpen_ratioOpen.mem_nhds hz] with w hw
    rw [fderiv_ratioOn_dirX ν hw i, ratioOn_eq_exp ν hw]
    rfl)
  rw [h'.fderiv, ratioOn_eq_exp ν hz]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [ratioExpD_dirX]
  simp only [Function.comp_apply, prX_apply, dirX, Pi.single_eq_same]
  ring

/-- **`∂²_{y_j}F = F·(A₁(−y_j)² − A₂(−y_j))`.** -/
theorem fderiv_fderiv_ratioOn_dirY {z : DualCoord p} (hz : z ∈ ratioOpen p) (j : Fin p) :
    fderiv ℝ (fun w => fderiv ℝ (ratioOn ν) w (dirY j)) z (dirY j) =
      ratioOn ν z * (lkerInt1 ν (-z.2 j) ^ 2 - lkerInt2 ν (-z.2 j)) := by
  have hE := (hasFDerivAt_ratioExp ν hz).exp
  have hA := (hasDerivAt_lkerInt1 ν (hasDerivAt_lkerInt_negY hz j)).comp_hasFDerivAt z
    (prY j).hasFDerivAt.neg
  have h := hE.mul hA
  have h' := h.congr_of_eventuallyEq (f₁ := fun w => fderiv ℝ (ratioOn ν) w (dirY j)) (by
    filter_upwards [isOpen_ratioOpen.mem_nhds hz] with w hw
    rw [fderiv_ratioOn_dirY ν hw j, ratioOn_eq_exp ν hw]
    rfl)
  rw [h'.fderiv, ratioOn_eq_exp ν hz]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [ratioExpD_dirY]
  simp only [neg_apply, Function.comp_apply, Pi.neg_apply, prY_apply, dirY,
    Pi.single_eq_same]
  ring

/-- **`𝒟_p F_·(ν)` in closed form** on `ratioOpen p` (in particular on the chamber). -/
theorem dualGenerator_ratioOn (D0 : ℝ) {z : DualCoord p} (hz : z ∈ ratioOpen p) :
    dualGenerator D0 (ratioOn ν) z = D0 / 2 * ratioOn ν z *
      ((∑ i, (z.1 i * (1 + z.1 i) * (lkerInt1 ν (z.1 i) ^ 2 + lkerInt2 ν (z.1 i)) +
          dualDriftX z i * lkerInt1 ν (z.1 i))) +
        ∑ j, (z.2 j * (1 - z.2 j) * (lkerInt1 ν (-z.2 j) ^ 2 - lkerInt2 ν (-z.2 j)) +
          dualDriftY z j * lkerInt1 ν (-z.2 j))) := by
  unfold dualGenerator
  simp_rw [fderiv_fderiv_ratioOn_dirX ν hz, fderiv_fderiv_ratioOn_dirY ν hz,
    fderiv_ratioOn_dirX ν hz, fderiv_ratioOn_dirY ν hz]
  conv_rhs => rw [mul_assoc, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

end BlockBand.Transmission.LawDuality
