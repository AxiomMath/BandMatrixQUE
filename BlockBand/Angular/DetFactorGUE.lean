module

public import BlockBand.DeterminantScore.Sector.MassDerivative
public import BlockBand.DeterminantScore.Sector.GUELaw
public import BlockBand.Window.Count.SchurInertia

/-!
# Unitary invariance and `C¹` regularity of the complete sector mass

* `re_trace_hermOfCoord_mul`: `Re Tr(G(x)G(y)) = Σ_c w_c x_c y_c` (`w = 1` on the diagonal,
  `2` off it): the Frobenius pairing in the Hermitian coordinates.
* `charFunDual_hermGaussian`: the characteristic function of `G_m(t)` at the functional
  `x ↦ Re Tr(B G(x))` (`B` Hermitian) is `exp(-t Re Tr(B²)/2)`.
* `map_unitaryCoord_hermGaussian`: **unitary invariance of `G_m(t)`**: for `VᴴV = 1` the law of
  `VᴴGV` is that of `G` (in coordinates `unitaryCoord V x = coord(VᴴG(x)V)`), every `t ≥ 0`.
  No such lemma for `CoareaPalm.gueMeasure` existed in the tree; the proof is by equality of
  characteristic functions (`Measure.ext_of_charFunDual`).
* `sectorMass_unitary_conj`: `Z_ℓ(WᴴKW) = Z_ℓ(K)` for Hermitian `K`, unitary `W`
  (`det` and, by Sylvester's law of inertia `negativeCount_conj`, `N_-` are conjugation
  invariant).
* `contDiff_massCoord`: the coordinate sector mass `y ↦ Z_ℓ(G(y))` is `C¹` on the whole
  coordinate space: its derivative `y ↦ E[1{N_-=ℓ} D(P²)(y+x)]` (`hasFDerivAt_massCoord`) is
  continuous by dominated convergence, because the sector-cut derivative `cutFDeriv ℓ` is
  continuous (it vanishes on `{P = 0}` together with `D(P²)`, and inertia is locally constant
  off `{P = 0}`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.DetFactor

open MeasureTheory ProbabilityTheory Matrix Filter
open BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts
open scoped NNReal Topology

variable {m : ℕ}

/-!
## The Frobenius pairing in Hermitian coordinates
-/

/-- Coordinate weights of the Frobenius pairing: `1` on the diagonal, `2` off it. -/
def coordWeight (c : HermCoord m) : ℝ := if c.1 = c.2 then 1 else 2

theorem coordWeight_pos (c : HermCoord m) : 0 < coordWeight c := by
  unfold coordWeight; split_ifs <;> norm_num

theorem sum_swap_coord (f : Fin m × Fin m → ℝ) : ∑ c : Fin m × Fin m, f c.swap = ∑ c, f c :=
  (Equiv.prodComm (Fin m) (Fin m)).sum_comp f

/-- `Re Tr(G(x)G(y)) = Σ_c w_c x_c y_c`. -/
theorem re_trace_hermOfCoord_mul (x y : HermCoord m → ℝ) :
    (hermOfCoord x * hermOfCoord y).trace.re = ∑ c, coordWeight c * x c * y c := by
  set D : Fin m × Fin m → ℝ := fun c => if c.1 = c.2 then x c * y c else 0
  set O : Fin m × Fin m → ℝ := fun c => if c.1 = c.2 then 0 else x c * y c
  have h1 : ∀ c : Fin m × Fin m,
      (hermOfCoord x c.1 c.2 * hermOfCoord y c.2 c.1).re = D c + O c + O c.swap := fun c => by
    obtain ⟨a, b⟩ := c
    simp only [D, O, hermOfCoord_apply, Prod.swap_prod_mk]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h.ne, h.ne', h, not_lt_of_gt h]
    · simp
    · simp [h.ne, h.ne', h, not_lt_of_gt h]
      ring
  have htr : (hermOfCoord x * hermOfCoord y).trace.re =
      ∑ c : Fin m × Fin m, (hermOfCoord x c.1 c.2 * hermOfCoord y c.2 c.1).re := by
    rw [Matrix.trace, Complex.re_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  rw [htr]
  simp_rw [h1, Finset.sum_add_distrib]
  rw [sum_swap_coord O, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [D, O, coordWeight]
  split_ifs <;> ring

/-- The dual functional `x ↦ Σ_c w_c b_c x_c = Re Tr(G(b)G(x))`. -/
def pairingDual (b : HermCoord m → ℝ) : StrongDual ℝ (HermCoord m → ℝ) :=
  ∑ c, (coordWeight c * b c) • ContinuousLinearMap.proj c

theorem pairingDual_apply (b x : HermCoord m → ℝ) :
    pairingDual b x = (hermOfCoord b * hermOfCoord x).trace.re := by
  rw [re_trace_hermOfCoord_mul, pairingDual]
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem dual_eq_sum (L : StrongDual ℝ (HermCoord m → ℝ)) (x : HermCoord m → ℝ) :
    L x = ∑ c, L (Pi.single c 1) * x c := by
  have h := LinearMap.pi_apply_eq_sum_univ (L : (HermCoord m → ℝ) →ₗ[ℝ] ℝ) x
  have hs : ∀ i : HermCoord m, (fun j : HermCoord m => if i = j then (1 : ℝ) else 0) =
      Pi.single i 1 := fun i => by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simp [hji, Ne.symm hji]
  simp only [hs, smul_eq_mul, ContinuousLinearMap.coe_coe] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Every functional is a Frobenius pairing. -/
theorem dual_eq_pairingDual (L : StrongDual ℝ (HermCoord m → ℝ)) :
    L = pairingDual (fun c => L (Pi.single c 1) / coordWeight c) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [dual_eq_sum, pairingDual]
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_div_cancel₀ _ (coordWeight_pos c).ne']

/-- Characteristic function of `G_m(t)` at a Frobenius pairing: `exp(-t Re Tr(G(b)²)/2)`. -/
theorem charFunDual_hermGaussian_term (t : ℝ≥0) (b : HermCoord m → ℝ) (c : HermCoord m) :
    (hermVariance m t c : ℝ) * pairingDual b (Pi.single c 1) ^ 2 =
      (t : ℝ) * (coordWeight c * b c * b c) := by
  have hL : pairingDual b (Pi.single c 1) = coordWeight c * b c := by
    rw [pairingDual]
    simp only [_root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [hL]
  simp only [hermVariance, coordWeight]
  split_ifs <;> push_cast <;> ring

/-- Characteristic function of `G_m(t)` at a Frobenius pairing: `exp(-t Re Tr(G(b)²)/2)`. -/
theorem charFunDual_hermGaussian (t : ℝ≥0) (b : HermCoord m → ℝ) :
    charFunDual (hermGaussian m t) (pairingDual b) =
      Complex.exp (-(((t : ℝ) * (hermOfCoord b * hermOfCoord b).trace.re : ℝ) : ℂ) / 2) := by
  rw [hermGaussian, Inputs.gaussianProduct, charFunDual_gaussianPi, re_trace_hermOfCoord_mul]
  have hs : (∑ i, (hermVariance m t i : ℝ) * pairingDual b (Pi.single i 1) ^ 2) =
      (t : ℝ) * ∑ c, coordWeight c * b c * b c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => charFunDual_hermGaussian_term t b c
  rw [hs]

/-!
## Unitary invariance of `G_m(t)`
-/

/-- Coordinates of the conjugate `VᴴG(x)V`. -/
def unitaryCoord (V : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) : HermCoord m → ℝ :=
  coordOfMatrix (Vᴴ * hermOfCoord x * V)

theorem continuous_coordOfMatrix : Continuous (coordOfMatrix (m := m)) := by
  refine continuous_pi fun c => ?_
  unfold coordOfMatrix
  split_ifs
  · exact Complex.continuous_re.comp ((continuous_apply c.1).comp (continuous_apply c.1))
  · exact Complex.continuous_re.comp ((continuous_apply c.2).comp (continuous_apply c.1))
  · exact Complex.continuous_im.comp ((continuous_apply c.1).comp (continuous_apply c.2))

theorem continuous_unitaryCoord (V : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (unitaryCoord V) :=
  continuous_coordOfMatrix.comp
    ((continuous_const.matrix_mul continuous_hermOfCoord).matrix_mul continuous_const)

theorem hermOfCoord_unitaryCoord (V : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) :
    hermOfCoord (unitaryCoord V x) = Vᴴ * hermOfCoord x * V :=
  hermOfCoord_coordOfMatrix (isHermitian_conjTranspose_mul_mul V (isHermitian_hermOfCoord x))

/-- **Unitary invariance of `G_m(t)`** (`VᴴV = 1`, every `t ≥ 0`). -/
theorem map_unitaryCoord_hermGaussian (t : ℝ≥0) {V : Matrix (Fin m) (Fin m) ℂ}
    (hV : Vᴴ * V = 1) : (hermGaussian m t).map (unitaryCoord V) = hermGaussian m t := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  apply Measure.ext_of_charFunDual
  funext L
  set b := fun c => L (Pi.single c 1) / coordWeight c
  set B := V * hermOfCoord b * Vᴴ
  have hBH : B.IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Vᴴ (isHermitian_hermOfCoord b)
    simpa [B, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using this
  set b' := coordOfMatrix B
  have hb' : hermOfCoord b' = B := hermOfCoord_coordOfMatrix hBH
  have hLx : ∀ x, L (unitaryCoord V x) = pairingDual b' x := fun x => by
    rw [dual_eq_pairingDual L, pairingDual_apply, pairingDual_apply, hermOfCoord_unitaryCoord,
      hb']
    simp only [B]
    rw [show hermOfCoord b * (Vᴴ * hermOfCoord x * V) = (hermOfCoord b * Vᴴ * hermOfCoord x) * V by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm,
      show V * (hermOfCoord b * Vᴴ * hermOfCoord x) = V * hermOfCoord b * Vᴴ * hermOfCoord x by
      simp only [Matrix.mul_assoc]]
  rw [charFunDual_apply, integral_map (continuous_unitaryCoord V).aemeasurable (by fun_prop)]
  simp_rw [hLx]
  rw [← charFunDual_apply, charFunDual_hermGaussian, dual_eq_pairingDual L,
    charFunDual_hermGaussian, hb']
  have htr : (B * B).trace = (hermOfCoord b * hermOfCoord b).trace := by
    simp only [B]
    rw [show V * hermOfCoord b * Vᴴ * (V * hermOfCoord b * Vᴴ) =
        V * (hermOfCoord b * (Vᴴ * V) * hermOfCoord b * Vᴴ) by simp only [Matrix.mul_assoc],
      hV, Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hV,
      Matrix.mul_one]
  rw [htr]

/-!
## Conjugation invariance of the sector mass
-/

theorem negativeCount_unitary_conj {M W : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
    (hW : Wᴴ * W = 1) : CoareaPalm.negativeCount (Wᴴ * M * W) = CoareaPalm.negativeCount M := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  let _ : Invertible W := ⟨Wᴴ, hW, hW'⟩
  exact BlockBand.Window.Count.negativeCount_conj hM W

theorem det_unitary_conj (M : Matrix (Fin m) (Fin m) ℂ) {W : Matrix (Fin m) (Fin m) ℂ}
    (hW : Wᴴ * W = 1) : (Wᴴ * M * W).det = M.det := by
  have h := congrArg Matrix.det hW
  rw [Matrix.det_mul, Matrix.det_one] at h
  rw [Matrix.det_mul, Matrix.det_mul]
  linear_combination M.det * h

theorem sectorDetSq_unitary_conj {K W : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (hW : Wᴴ * W = 1) (ℓ : ℕ) (x : HermCoord m → ℝ) :
    sectorDetSq (Wᴴ * K * W) ℓ x = sectorDetSq K ℓ (unitaryCoord Wᴴ x) := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  have hM : Wᴴ * K * W + hermOfCoord x = Wᴴ * (K + hermOfCoord (unitaryCoord Wᴴ x)) * W := by
    rw [hermOfCoord_unitaryCoord, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul]
    congr 1
    rw [show Wᴴ * (W * hermOfCoord x * Wᴴ) * W = (Wᴴ * W) * hermOfCoord x * (Wᴴ * W) by
      simp only [Matrix.mul_assoc], hW, Matrix.one_mul, Matrix.mul_one]
  have hH := hK.add (isHermitian_hermOfCoord (unitaryCoord Wᴴ x))
  simp only [sectorDetSq, InSector, hM, negativeCount_unitary_conj hH hW, det_unitary_conj _ hW]
  congr 1

/-- `Z_ℓ(WᴴKW) = Z_ℓ(K)` for Hermitian `K` and unitary `W` (every `t ≥ 0`, every `ℓ`). -/
theorem sectorMass_unitary_conj (t : ℝ≥0) {K W : Matrix (Fin m) (Fin m) ℂ}
    (hK : K.IsHermitian) (hW : Wᴴ * W = 1) (ℓ : ℕ) :
    sectorMass m t (Wᴴ * K * W) ℓ = sectorMass m t K ℓ := by
  have hW' : Wᴴᴴ * Wᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.1 hW
  unfold sectorMass
  simp_rw [sectorDetSq_unitary_conj hK hW ℓ]
  have hmeas : Measurable (sectorDetSq K ℓ) := by
    rw [sectorDetSq_eq_cut]; exact measurable_cut hK ℓ _
  rw [← integral_map (continuous_unitaryCoord Wᴴ).aemeasurable hmeas.aestronglyMeasurable,
    map_unitaryCoord_hermGaussian t hW']

/-!
## `C¹` regularity of the coordinate sector mass
-/

/-- The sector-cut derivative is continuous. -/
theorem continuous_cutFDeriv (ℓ : ℕ) : Continuous (cutFDeriv (m := m) ℓ) := by
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ).IsHermitian := isHermitian_zero
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hdet : ((0 : Matrix (Fin m) (Fin m) ℂ) + hermOfCoord z).det = 0
  · exact continuousAt_ite_zero_of_continuousAt_of_eq_zero _ _
      (continuous_realEvalFDeriv _).continuousAt (realEvalFDeriv_detSqPoly_eq_zero 0 hdet)
  · have hev : cutFDeriv ℓ =ᶠ[𝓝 z] (if InSector (0 : Matrix (Fin m) (Fin m) ℂ) ℓ z then
        realEvalFDeriv (detSqPoly 0) else fun _ => 0) := by
      filter_upwards [eventually_inSector_iff h0 ℓ hdet] with y hy
      by_cases hx : InSector (0 : Matrix (Fin m) (Fin m) ℂ) ℓ z
      · simp [cutFDeriv, hx, hy.mpr hx]
      · simp [cutFDeriv, hx, mt hy.mp hx]
    refine ContinuousAt.congr ?_ hev.symm
    by_cases hx : InSector (0 : Matrix (Fin m) (Fin m) ℂ) ℓ z
    · simpa [hx] using (continuous_realEvalFDeriv _).continuousAt
    · simpa [hx] using continuousAt_const

/-- The derivative of the coordinate sector mass, `y ↦ E[1{N_-=ℓ} D(P²)(y + x)]`. -/
def massCoordFDeriv (m : ℕ) (t : ℝ≥0) (ℓ : ℕ) (y : HermCoord m → ℝ) :
    (HermCoord m → ℝ) →L[ℝ] ℂ :=
  ∫ x, cutFDeriv ℓ (y + x) ∂hermGaussian m t

theorem continuous_massCoordFDeriv (t : ℝ≥0) (ℓ : ℕ) :
    Continuous (massCoordFDeriv m t ℓ) := by
  refine continuous_iff_continuousAt.2 fun y0 => ?_
  have hball : ∀ y ∈ Metric.ball y0 1, ‖y‖ ≤ ‖y0‖ + 1 := fun y hy => by
    rw [mem_ball_iff_norm] at hy
    have := norm_add_le (y - y0) y0
    rw [sub_add_cancel] at this
    linarith
  refine continuousAt_of_dominated (bound := massBound (‖y0‖ + 1))
    (Eventually.of_forall fun y => aestronglyMeasurable_cutFDeriv t ℓ y) ?_
    (integrable_massBound t _) (ae_of_all _ fun x => ?_)
  · filter_upwards [Metric.ball_mem_nhds y0 one_pos] with y hy
    exact ae_of_all _ fun x => norm_cutFDeriv_le ℓ (hball y hy)
  · exact ((continuous_cutFDeriv ℓ).comp (continuous_id.add continuous_const)).continuousAt

/-- **The coordinate sector mass is `C¹`** on the whole coordinate space (every `t ≥ 0`,
every `ℓ`). -/
theorem contDiff_massCoord (t : ℝ≥0) (ℓ : ℕ) : ContDiff ℝ 1 (massCoord m t ℓ) :=
  contDiff_one_iff_hasFDerivAt.2
    ⟨massCoordFDeriv m t ℓ, continuous_massCoordFDeriv t ℓ, hasFDerivAt_massCoord t ℓ⟩

end BlockBand.Angular.DetFactor
