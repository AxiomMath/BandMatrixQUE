module

public import BlockBand.Transmission.DualLift.Coeff
public import BlockBand.Transmission.Dual.ExistsCoord

/-!
# The lifted generator pushes forward to `dualGenerator`

Deterministic. For the lifted coefficients `(liftDrift D₀, liftSigma D₀)` and `ξ` on the
invariant manifold `liftM`:
* `genAt_lx`, `genAt_ly`: generator data of `x = |w|²` and `y = (1 − v₃)/2` (everywhere);
* `vecGen_liftProj`, `liftCov_eq`: the drift and covariance of `π = liftProj` are the flat
  `p = 1` dual characteristics `flatDrift D₀ 1 (π ξ)`, `flatDiff D₀ 1 (π ξ)` (Itô for `π`);
* **`sdeGenerator_comp_liftProj`**: for every `C²` function `F` of the flat coordinates,
  `𝓛̃(F ∘ π)(ξ) = mpGenerator (flatDrift D₀ 1) (flatDiff D₀ 1) F (π ξ)`;
* **`sdeGenerator_dualLift`**: for `f : DualCoord 1 → ℝ` of class `C²`,
  `𝓛̃(f ∘ ofFlat 1 ∘ π)(ξ) = dualGenerator D₀ f (ofFlat 1 (π ξ))`, at every point of `liftM`,
  including the faces `x = 0` (`w = 0`), `y = 0`, `y = 1` (`v = ±e₃`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualLift

open Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists

variable {D0 : ℝ} {ξ : Fin 6 → ℝ}

/-- Noise derivatives of `x`. -/
def gx (D0 : ℝ) (ξ : Fin 6 → ℝ) : Fin 5 → ℝ := ![ξ 0 * rho D0 ξ, ξ 1 * rho D0 ξ, 0, 0, 0]

/-- Noise derivatives of `y`. -/
def gy (D0 : ℝ) (ξ : Fin 6 → ℝ) : Fin 5 → ℝ :=
  ![0, 0, √D0 * (ξ 4 * ξ 2) / 2, √D0 * (ξ 4 * ξ 3) / 2, -(√D0 * (1 - ξ 4 * ξ 4)) / 2]

theorem genAt_lx (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    GenAt (liftDrift D0) (liftSigma D0) lx ξ
      (D0 / 2 * (1 + 2 * lx ξ) - D0 * lx ξ * (1 + lx ξ) * ξ 5) (gx D0 ξ) := by
  have h := ((GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 0).sq).add
    ((GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 1).sq)
  refine (h.congr_fun rfl).congr ?_ fun a => ?_
  · simp only [Fin.sum_univ_five, liftDrift, liftSigma, Matrix.cons_val, Fin.isValue]
    have hr := rho_sq hD0 ξ
    unfold lx at hr ⊢
    linear_combination (1 / 2 : ℝ) * hr
  · fin_cases a <;> simp [gx, liftSigma] <;> ring

theorem genAt_ly (ξ : Fin 6 → ℝ) :
    GenAt (liftDrift D0) (liftSigma D0) ly ξ
      (D0 / 2 * (1 - 2 * ly ξ) - D0 * ly ξ * (1 - ly ξ) * ξ 5) (gy D0 ξ) := by
  have h := ((GenAt.const (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 1).sub
    (GenAt.coord (b := liftDrift D0) (σ := liftSigma D0) (y := ξ) 4)).const_mul (1 / 2)
  refine (h.congr_fun (funext fun q => by unfold ly; ring)).congr ?_ fun a => ?_
  · simp only [liftDrift, Matrix.cons_val, Fin.isValue]
    unfold ly
    ring
  · fin_cases a <;> simp [gy, liftSigma] <;> ring

/-!
## Flat characteristics on the manifold
-/

theorem gx_cov (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    ∑ a, gx D0 ξ a * gx D0 ξ a = D0 * (lx ξ * (1 + lx ξ)) := by
  simp only [Fin.sum_univ_five, gx, Matrix.cons_val, Fin.isValue]
  have hr := rho_sq hD0 ξ
  unfold lx at hr ⊢
  linear_combination (ξ 0 * ξ 0 + ξ 1 * ξ 1) * hr

theorem gy_cov (hD0 : 0 ≤ D0) {ξ : Fin 6 → ℝ} (h : ξ ∈ liftM) :
    ∑ a, gy D0 ξ a * gy D0 ξ a = D0 * (ly ξ * (1 - ly ξ)) := by
  have h1 := h.1
  unfold vSq at h1
  have hD := Real.mul_self_sqrt hD0
  simp only [Fin.sum_univ_five, gy, Matrix.cons_val, Fin.isValue]
  unfold ly
  linear_combination ((ξ 4 * ξ 4 * (ξ 2 * ξ 2 + ξ 3 * ξ 3) + (1 - ξ 4 * ξ 4) * (1 - ξ 4 * ξ 4)) / 4)
    * hD + (D0 / 4 * (ξ 4 * ξ 4)) * h1

theorem gxy_cov (ξ : Fin 6 → ℝ) : ∑ a, gx D0 ξ a * gy D0 ξ a = 0 := by
  simp [Fin.sum_univ_five, gx, gy]

/-!
## Expansion in the flat basis
-/

theorem clm_fin2 (L : (Fin 2 → ℝ) →L[ℝ] ℝ) (v : Fin 2 → ℝ) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) := by
  have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → ℝ) + v 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
    funext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

theorem bilin_fin2 (B : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ) (u v : Fin 2 → ℝ) :
    B u v = u 0 * v 0 * B (Pi.single 0 1) (Pi.single 0 1) +
      u 0 * v 1 * B (Pi.single 0 1) (Pi.single 1 1) +
      u 1 * v 0 * B (Pi.single 1 1) (Pi.single 0 1) +
      u 1 * v 1 * B (Pi.single 1 1) (Pi.single 1 1) := by
  rw [clm_fin2 (B u) v]
  have h : ∀ e : Fin 2 → ℝ, B u e = u 0 * B (Pi.single 0 1) e + u 1 * B (Pi.single 1 1) e :=
    fun e => clm_fin2 (B.flip e) u
  rw [h, h]
  ring

theorem sum_bilin_fin2 {ι : Type*} [Fintype ι] (B : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ)
    (u : ι → Fin 2 → ℝ) :
    ∑ a, B (u a) (u a) = (∑ a, u a 0 * u a 0) * B (Pi.single 0 1) (Pi.single 0 1) +
      (∑ a, u a 0 * u a 1) * B (Pi.single 0 1) (Pi.single 1 1) +
      (∑ a, u a 1 * u a 0) * B (Pi.single 1 1) (Pi.single 0 1) +
      (∑ a, u a 1 * u a 1) * B (Pi.single 1 1) (Pi.single 1 1) := by
  rw [Finset.sum_congr rfl fun a _ => bilin_fin2 B (u a) (u a)]
  simp only [Finset.sum_add_distrib, Finset.sum_mul]

theorem vecGen_liftProj (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) :
    SourceSDE.vecGen (liftDrift D0) (liftSigma D0) liftProj ξ =
      ![D0 / 2 * (1 + 2 * lx ξ) - D0 * lx ξ * (1 + lx ξ) * ξ 5,
        D0 / 2 * (1 - 2 * ly ξ) - D0 * ly ξ * (1 - ly ξ) * ξ 5] := by
  have hP : ContDiff ℝ 2 liftProj := contDiff_liftProj.of_le le_top
  funext i
  have h := vecGen_clm (liftDrift D0) (liftSigma D0)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) hP ξ
  simp only [ContinuousLinearMap.proj_apply] at h
  rw [← h]
  fin_cases i
  · exact (genAt_lx hD0 ξ).vecGen
  · exact (genAt_ly ξ).vecGen

theorem fderiv_liftProj (hD0 : 0 ≤ D0) (ξ : Fin 6 → ℝ) (a : Fin 5) :
    fderiv ℝ liftProj ξ (liftSigma D0 a ξ) = ![gx D0 ξ a, gy D0 ξ a] := by
  have hP : DifferentiableAt ℝ liftProj ξ :=
    (contDiff_liftProj.differentiable (by simp)) ξ
  funext i
  have h := fderiv_clm_apply' (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)
    hP (liftSigma D0 a ξ)
  simp only [ContinuousLinearMap.proj_apply] at h
  rw [← h]
  fin_cases i
  · simpa using ((genAt_lx hD0 ξ).dir a)
  · simpa using ((genAt_ly (D0 := D0) ξ).dir a)

theorem gyx_cov (ξ : Fin 6 → ℝ) : ∑ a, gy D0 ξ a * gx D0 ξ a = 0 := by
  simp [Fin.sum_univ_five, gx, gy]

/-- **Push-forward of the generator (flat form).** On the invariant manifold, the lifted generator of `F ∘ π` is the flat
`p = 1` dual generator of `F` at `π ξ`.
-/
theorem sdeGenerator_comp_liftProj (hD0 : 0 ≤ D0) {F : (Fin 2 → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (hξ : ξ ∈ liftM) :
    sdeGenerator (liftDrift D0) (liftSigma D0) (fun q => F (liftProj q)) ξ =
      mpGenerator (flatDrift D0 1) (flatDiff D0 1) F (liftProj ξ) := by
  rw [sdeGenerator_comp _ _ hF (contDiff_liftProj.of_le le_top), vecGen_liftProj hD0]
  simp only [fderiv_liftProj hD0]
  rw [clm_fin2]
  rw [sum_bilin_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [gx_cov hD0, gy_cov hD0 hξ, gxy_cov, gyx_cov]
  unfold mpGenerator
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [flatDrift_one_zero, flatDrift_one_one]
  simp only [flatDiff, Matrix.diagonal_apply, Fin.isValue, ite_true,
    show ((0 : Fin (1 + 1)) = 1) ↔ False by decide, show ((1 : Fin (1 + 1)) = 0) ↔ False by decide,
    ite_false, flatDiffDiag_one_zero, flatDiffDiag_one_one, liftProj_zero, liftProj_one]
  rw [s_eq_inv hξ]
  have hS := lS_pos hξ
  unfold lS at hS ⊢
  field_simp
  ring

/-- **Push-forward of the generator (dual coordinates).** On the invariant manifold (faces included), the lifted generator of
`f ∘ ofFlat 1 ∘ π` is the `dualGenerator D₀ f` at `π ξ`.
-/
theorem sdeGenerator_dualLift (hD0 : 0 ≤ D0) {f : DualCoord 1 → ℝ} (hf : ContDiff ℝ 2 f)
    (hξ : ξ ∈ liftM) :
    sdeGenerator (liftDrift D0) (liftSigma D0) (fun q => f (ofFlat 1 (liftProj q))) ξ =
      dualGenerator D0 f (ofFlat 1 (liftProj ξ)) :=
  (sdeGenerator_comp_liftProj hD0 (F := f ∘ ofFlat 1) (hf.comp (ofFlat 1).contDiff) hξ).trans
    (mpGenerator_flat D0 hf _)

end BlockBand.Transmission.DualLift
