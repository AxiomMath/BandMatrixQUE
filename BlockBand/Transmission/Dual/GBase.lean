module

public import BlockBand.Transmission.Dual.GHTransform

/-!
# The base generator in flat coordinates

The base process `P⁰` (independent scalar diffusions) has, in the flat coordinates `ℝ^{q+q}`,
drift `flatBaseDrift D₀ q = (D₀/2)(1 + 2x, 1 − 2y)` and the same diagonal diffusion
`flatDiff D₀ q = D₀ diag(x(1+x), y(1−y))` as the dual.
* `mpGenerator_flatBase`: the martingale-problem generator of `(flatBaseDrift, flatDiff)` on
  `F ∘ ofFlat` is `baseGen D₀ F ∘ ofFlat`, for `F` of class `C²` at the point only (so
  `F = H_q f` is allowed).
* `mpGenerator_flatBase_cauchyH_mul`: hence `𝓛⁰((H_q f) ∘ ofFlat) = (H_q · 𝒟_q f) ∘ ofFlat` and
  `𝓛⁰(H_q ∘ ofFlat) = 0` on the flat chamber: the generator inputs of the local Doob identity
  (Itô's formula for `H_q f` and `H_q` under `P⁰`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Matrix Finset Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ}

/-- Flat drift of the base process: `(D₀/2)(1 + 2x_i)` and `(D₀/2)(1 − 2y_j)`. -/
def flatBaseDrift (D0 : ℝ) (q : ℕ) (w : Fin (q + q) → ℝ) : Fin (q + q) → ℝ :=
  Fin.append (fun i => D0 / 2 * (1 + 2 * (ofFlat q w).1 i))
    (fun j => D0 / 2 * (1 - 2 * (ofFlat q w).2 j))

theorem fderiv_comp_ofFlat_apply {F : DualCoord q → ℝ} {w : Fin (q + q) → ℝ}
    (hF : DifferentiableAt ℝ F (ofFlat q w)) (u : Fin (q + q) → ℝ) :
    fderiv ℝ (F ∘ ofFlat q) w u = fderiv ℝ F (ofFlat q w) (ofFlat q u) := by
  rw [fderiv_comp w hF (ofFlat q).differentiableAt, ContinuousLinearMap.fderiv]; rfl

theorem fderiv_fderiv_comp_ofFlat_apply {F : DualCoord q → ℝ} {w : Fin (q + q) → ℝ}
    (hF : ContDiffAt ℝ 2 F (ofFlat q w)) (u : Fin (q + q) → ℝ) :
    fderiv ℝ (fderiv ℝ (F ∘ ofFlat q)) w u u =
      fderiv ℝ (fderiv ℝ F) (ofFlat q w) (ofFlat q u) (ofFlat q u) := by
  have hc : ContDiffAt ℝ 2 (F ∘ ofFlat q) w := hF.comp w (ofFlat q).contDiff.contDiffAt
  rw [Exists.fderiv_fderiv_eq_deriv_line u hc, Exists.fderiv_fderiv_eq_deriv_line _ hF]
  congr 2

/-- **The flat base generator** is `baseGen ∘ ofFlat`, for `F` of class `C²` at the point. -/
theorem mpGenerator_flatBase (D0 : ℝ) {F : DualCoord q → ℝ} {w : Fin (q + q) → ℝ}
    (hF : ContDiffAt ℝ 2 F (ofFlat q w)) :
    mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) (F ∘ ofFlat q) w =
      baseGen D0 F (ofFlat q w) := by
  have hd : DifferentiableAt ℝ F (ofFlat q w) := hF.differentiableAt (by norm_num)
  unfold mpGenerator
  simp only [flatDiff, Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [fderiv_comp_ofFlat_apply hd, fderiv_fderiv_comp_ofFlat_apply hF, Fin.sum_univ_add,
    ofFlat_single_castAdd, ofFlat_single_natAdd, flatBaseDrift, flatDiffDiag, Fin.append_left,
    Fin.append_right]
  unfold baseGen
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Generator input of the local Doob identity**: on the flat chamber,
`𝓛⁰((H_q f) ∘ ofFlat) = (H_q 𝒟_q f) ∘ ofFlat`. -/
theorem mpGenerator_flatBase_cauchyH_mul (D0 : ℝ) {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    {w : Fin (q + q) → ℝ} (hw : w ∈ flatChamber q) :
    mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) ((fun z => cauchyH q z * f z) ∘ ofFlat q) w =
      cauchyH q (ofFlat q w) * dualGenerator D0 f (ofFlat q w) := by
  have hH : ContDiffAt ℝ 2 (cauchyH q) (ofFlat q w) :=
    (contDiffAt_cauchyH_of_mem hw).of_le (by simp)
  rw [mpGenerator_flatBase D0 (hH.mul hf.contDiffAt), baseGen_cauchyH_mul D0 hf hw]

/-- On the flat chamber `𝓛⁰(H_q ∘ ofFlat) = 0`. -/
theorem mpGenerator_flatBase_cauchyH (D0 : ℝ) {w : Fin (q + q) → ℝ} (hw : w ∈ flatChamber q) :
    mpGenerator (flatBaseDrift D0 q) (flatDiff D0 q) (cauchyH q ∘ ofFlat q) w = 0 := by
  rw [mpGenerator_flatBase D0 ((contDiffAt_cauchyH_of_mem hw).of_le (by simp)),
    baseGen_cauchyH D0 fun i j => (add_pos_of_mem hw i j).ne']

end BlockBand.Transmission.Dual.G
