module

public import BlockBand.Internal.Contracts.Layers
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# One Ginibre column: the circular Gaussian vector and its unitary invariance

* `toC r = (r(x,0) + i r(x,1))_x`, `colLaw W t = (⊗ N(0,t/2)).map toC`: iid circular
  Gaussians with `E|g_x|² = t`, the law of one column of `ginibreMeasure (Fin W) (Fin W) t`.
* `realify`: the real isometry `ℝ^{W×2} ≅ ℂ^W`.
* **`colLaw_map_repr`**: for every orthonormal basis `u` of `ℂ^W`, the coordinates
  `(⟪u_l, g⟫)_l` of `g ~ colLaw W t` again have law `colLaw W t` (from Mathlib's
  `stdGaussian_map`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

variable {W : ℕ}

/-- Real coordinates to a complex vector: `x ↦ r(x,0) + i r(x,1)`. -/
def toC (r : Fin W × Fin 2 → ℝ) : Fin W → ℂ := fun x => (r (x, 0) : ℂ) + (r (x, 1) : ℂ) * Complex.I

/-- Complex vector to real coordinates (inverse of `toC`). -/
def ofC (v : Fin W → ℂ) : Fin W × Fin 2 → ℝ := fun p => if p.2 = 0 then (v p.1).re else (v p.1).im

theorem ofC_toC (r : Fin W × Fin 2 → ℝ) : ofC (toC r) = r := by
  funext ⟨x, c⟩
  fin_cases c <;> simp [ofC, toC]

theorem toC_ofC (v : Fin W → ℂ) : toC (ofC v) = v := by
  funext x
  simp [ofC, toC, Complex.re_add_im]

theorem measurable_toC : Measurable (toC : (Fin W × Fin 2 → ℝ) → Fin W → ℂ) := by
  unfold toC; fun_prop

/-- The law of one Ginibre column: iid circular Gaussians with `E|g_x|² = t`. -/
def colLaw (W : ℕ) (t : ℝ≥0) : Measure (Fin W → ℂ) :=
  (Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 (t / 2)).map toC

instance (t : ℝ≥0) : IsProbabilityMeasure (colLaw W t) := by
  unfold colLaw; infer_instance

theorem norm_toLp_toC_sq (r : Fin W × Fin 2 → ℝ) :
    ‖WithLp.toLp 2 (toC r)‖ ^ 2 = ‖WithLp.toLp 2 r‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fin.sum_univ_two]
  simp only [toC, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- The real isometry `ℝ^{W×2} ≅ ℂ^W`, `r ↦ toC r`. -/
def realify (W : ℕ) :
    EuclideanSpace ℝ (Fin W × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin W) where
  toFun r := WithLp.toLp 2 (toC (WithLp.ofLp r))
  invFun v := WithLp.toLp 2 (ofC (WithLp.ofLp v))
  map_add' r s := by
    ext x; simp [toC]; ring
  map_smul' c r := by
    ext x; simp [toC]; ring
  left_inv r := by simp [ofC_toC]
  right_inv v := by simp [toC_ofC]
  norm_map' r := by
    have h := norm_toLp_toC_sq (WithLp.ofLp r)
    simp only [WithLp.toLp_ofLp] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- A complex linear isometry equivalence, as a real one. -/
def realIsometry (U : EuclideanSpace ℂ (Fin W) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin W)) :
    EuclideanSpace ℂ (Fin W) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin W) :=
  { U.toLinearEquiv.restrictScalars ℝ with norm_map' := U.norm_map }

/-- The coordinate map `g ↦ (⟪u_l, g⟫)_l` of an orthonormal basis, on plain vectors. -/
def reprMap (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W))) (g : Fin W → ℂ) :
    Fin W → ℂ :=
  WithLp.ofLp (u.repr (WithLp.toLp 2 g))

theorem reprMap_apply (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W)))
    (g : Fin W → ℂ) (l : Fin W) : reprMap u g l = ⟪u l, WithLp.toLp 2 g⟫_ℂ := by
  simp [reprMap, OrthonormalBasis.repr_apply_apply]

theorem measurable_reprMap (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W))) :
    Measurable (reprMap u) := by
  have : Continuous (reprMap u) :=
    (PiLp.continuous_ofLp 2 _).comp (u.repr.continuous.comp (PiLp.continuous_toLp 2 _))
  exact this.measurable

theorem reprMap_smul (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W))) (c : ℂ)
    (g : Fin W → ℂ) : reprMap u (c • g) = c • reprMap u g := by
  simp [reprMap]

/-- The standard real Gaussian product law, as a pushforward of Mathlib's `stdGaussian`. -/
theorem pi_std_eq :
    (Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 1) =
      (stdGaussian (EuclideanSpace ℝ (Fin W × Fin 2))).map WithLp.ofLp := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id.symm

/-- Unitary invariance at unit variance. -/
theorem pi_std_map_repr (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W))) :
    ((Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 1).map toC).map (reprMap u) =
      (Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 1).map toC := by
  set Ψ : EuclideanSpace ℝ (Fin W × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin W × Fin 2) :=
    ((realify W).trans (realIsometry u.repr)).trans (realify W).symm
  have hcomm : reprMap u ∘ toC ∘ WithLp.ofLp = toC ∘ WithLp.ofLp ∘ Ψ := by
    funext r
    show reprMap u (toC (WithLp.ofLp r)) =
      toC (ofC (WithLp.ofLp (u.repr (WithLp.toLp 2 (toC (WithLp.ofLp r))))))
    rw [toC_ofC]
    rfl
  have hΨ : Measurable Ψ := Ψ.continuous.measurable
  rw [pi_std_eq, Measure.map_map measurable_toC (by fun_prop),
    Measure.map_map (measurable_reprMap u) (measurable_toC.comp (by fun_prop))]
  rw [show reprMap u ∘ toC ∘ WithLp.ofLp = (toC ∘ WithLp.ofLp) ∘ Ψ from hcomm,
    ← Measure.map_map (measurable_toC.comp (by fun_prop)) hΨ, stdGaussian_map Ψ]

/-- `N(0, t/2) = (c·)_* N(0,1)` with `c = √(t/2)`, coordinatewise. -/
theorem pi_gauss_eq (t : ℝ≥0) :
    (Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 (t / 2)) =
      (Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 1).map
        (fun r p => Real.sqrt ((t : ℝ) / 2) * r p) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul _).aemeasurable)]
  congr 1
  funext p
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp only [NNReal.coe_mk, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.sq_sqrt (by positivity)]

theorem colLaw_eq (t : ℝ≥0) :
    colLaw W t = ((Measure.pi fun _ : Fin W × Fin 2 => gaussianReal 0 1).map toC).map
      (fun g => ((Real.sqrt ((t : ℝ) / 2) : ℝ) : ℂ) • g) := by
  rw [colLaw, pi_gauss_eq, Measure.map_map measurable_toC (by fun_prop),
    Measure.map_map (by fun_prop) measurable_toC]
  congr 1
  funext r
  funext x
  simp [toC]
  ring

/-- **Unitary invariance of a Ginibre column**: `(⟪u_l, g⟫)_l ~ colLaw W t` for `g ~ colLaw W t`
and every orthonormal basis `u` of `ℂ^W`. -/
theorem colLaw_map_repr (t : ℝ≥0) (u : OrthonormalBasis (Fin W) ℂ (EuclideanSpace ℂ (Fin W))) :
    (colLaw W t).map (reprMap u) = colLaw W t := by
  set c : ℂ := ((Real.sqrt ((t : ℝ) / 2) : ℝ) : ℂ)
  have hs : Measurable fun g : Fin W → ℂ => c • g := by fun_prop
  rw [colLaw_eq, Measure.map_map (measurable_reprMap u) hs]
  rw [show reprMap u ∘ (fun g : Fin W → ℂ => c • g) = (fun g => c • g) ∘ reprMap u from
    funext fun g => reprMap_smul u c g]
  rw [← Measure.map_map hs (measurable_reprMap u), pi_std_map_repr]

end BlockBand.Transmission.LawFinite
