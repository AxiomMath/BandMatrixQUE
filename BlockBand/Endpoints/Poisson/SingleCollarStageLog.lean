module

public import BlockBand.Endpoints.Poisson.SingleCollarAnalytic
public import BlockBand.Endpoints.Poisson.SingleCollarComparison

/-!
# Single-collar log error: the stage log difference is a collar log difference

Law: the original prior in Gaussian coordinates `ringCoordLaw p.n p.W p.b`, for every admissible
`p : Parameters`. Domain: every collar layout, pairing, stage `S`, collar `k ∉ S`, buffer, real
energy `e ∈ (-2, 2)` with matched leads `z = z_b(e)` (`boundaryZ`), each fixed source `κ ≥ 0`.

* `scs_ae_isUnit_det_stageMatrix`: every stage determinant is almost surely nonzero (any stage,
  including `S = ∅`; same active-polynomial witness as `ae_isUnit_det_oldInterior`).
* `scs_stageLog_sub_ae`, `scs_svStageLog_sub_ae`: almost surely the stage log difference equals
  `log|det(I - U r_κ)| - log|det(I - U r₀)|`.
* `scs_scatteringDistance_oldScattering`: the certificate distance of `r₀` is that of `X₀`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (boundaryZ matchedDistance matchedA)
open BlockBand.Internal.Contracts.Critical (collarScattering oldScattering)
open BlockBand.Endpoints.PhaseFractional (scatteringDistance twoIEta twoIEta_ne_zero)

section Witness

variable (p : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)

open Classical in
/-- `det H_κ^{π,S} ≠ 0` at the scalar witness `(e+1) I` (any stage `S`, `Im z > 0`). -/
theorem scs_det_stageMatrix_scalarWitness_ne_zero (π : Pairing) (S : Finset (Fin m)) (e : ℝ)
    {z : ℂ} (hz : 0 < z.im) (buf : ℕ) (κ : ℝ) :
    (stageMatrix L s π S e z buf κ (ringCoordsOf (scalarWitness p e))).det ≠ 0 := by
  set g : StageSite L s S p.W → ℂ := fun x =>
    (if IsMatched L s S x.1.1 then (z.re : ℂ) else 1) +
      ((stageAbsorption L s S buf κ z.im p.W x.1.1 : ℝ) : ℂ) * Complex.I
  have hdiag : stageMatrix L s π S e z buf κ (ringCoordsOf (scalarWitness p e)) = diagonal g := by
    ext x y
    simp only [stageMatrix, submatrix_apply, stageFull_scalarWitness, diagonal_apply,
      Subtype.ext_iff, g]
  rw [hdiag, det_diagonal, Finset.prod_ne_zero_iff]
  intro x _
  simp only [g]
  by_cases hm : IsMatched L s S x.1.1
  · simp only [hm, ite_true, stageAbsorption]
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  · simp only [hm, ite_false]
    intro h
    have := congrArg Complex.re h
    simp at this

theorem scs_measurable_stageMatrix (π : Pairing) (S : Finset (Fin m)) (e : ℝ) (z : ℂ)
    (buf : ℕ) (κ : ℝ) :
    Measurable (stageMatrix (W := p.W) L s π S e z buf κ) := by
  have hf := measurable_stageFull (W := p.W) (L := L) (s := s) π S e z buf κ
  exact Measurable.of_eval_matrix _ fun _ _ => hf.eval_matrix

/-- **Every stage determinant is almost surely nonzero** under the original prior, for each
fixed `κ`, real `e` and `Im z > 0` (any stage, in particular the empty one). -/
theorem scs_ae_isUnit_det_stageMatrix (π : Pairing) (S : Finset (Fin m)) (e : ℝ) {z : ℂ}
    (hz : 0 < z.im) (buf : ℕ) (κ : ℝ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b), IsUnit (stageMatrix L s π S e z buf κ ω).det := by
  have hX := (hasLaw_ringCoordsOf p p.constructGaussianRingModel).1
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_isUnit_det
    (scs_measurable_stageMatrix p L s π S e z buf κ))]
  have hpoly : IsActivePoly p
      (fun H => (stageMatrix L s π S e z buf κ (ringCoordsOf H)).det) :=
    IsActivePoly.det fun x y => isActivePoly_stageFull p L s π S e z buf κ x.1 y.1
  filter_upwards [hpoly.ae_ne_zero _ (z₀ := p.gaussianActiveExtraction (scalarWitness p e))
    (by rw [activeReconstruction_scalarWitness]
        exact scs_det_stageMatrix_scalarWitness_ne_zero p L s π S e hz buf κ)] with H hH
  exact isUnit_iff_ne_zero.mpr hH

end Witness

/-!
## The log difference
-/

/-- Real algebra of the cancellation: if `a_κ = P D_κ c_κ` and `a_0 = P D_0 c_0` with all
`a, c ≠ 0`, then `log(|a_κ|/|a_0|) - log(|c_κ|/|c_0|) = log|D_κ| - log|D_0|`. -/
theorem scs_log_ratio_cancel {aκ a0 cκ c0 P Dκ D0 : ℂ} (haκ : aκ ≠ 0) (ha0 : a0 ≠ 0)
    (hcκ : cκ ≠ 0) (hc0 : c0 ≠ 0) (hκ : aκ / cκ = P * Dκ) (h0 : a0 / c0 = P * D0) :
    Real.log (‖aκ‖ / ‖a0‖) - Real.log (‖cκ‖ / ‖c0‖) = Real.log ‖Dκ‖ - Real.log ‖D0‖ := by
  have hqκ : aκ / cκ ≠ 0 := div_ne_zero haκ hcκ
  have hq0 : a0 / c0 ≠ 0 := div_ne_zero ha0 hc0
  have hP : P ≠ 0 := by rintro rfl; rw [zero_mul] at hκ; exact hqκ hκ
  have hDκ : Dκ ≠ 0 := by rintro rfl; rw [mul_zero] at hκ; exact hqκ hκ
  have hD0 : D0 ≠ 0 := by rintro rfl; rw [mul_zero] at h0; exact hq0 h0
  have hn : ∀ {x : ℂ}, x ≠ 0 → ‖x‖ ≠ 0 := fun h => norm_ne_zero_iff.mpr h
  have e1 : Real.log ‖aκ‖ - Real.log ‖cκ‖ = Real.log ‖P‖ + Real.log ‖Dκ‖ := by
    rw [← Real.log_div (hn haκ) (hn hcκ), ← norm_div, hκ, norm_mul,
      Real.log_mul (hn hP) (hn hDκ)]
  have e0 : Real.log ‖a0‖ - Real.log ‖c0‖ = Real.log ‖P‖ + Real.log ‖D0‖ := by
    rw [← Real.log_div (hn ha0) (hn hc0), ← norm_div, h0, norm_mul,
      Real.log_mul (hn hP) (hn hD0)]
  rw [Real.log_div (hn haκ) (hn ha0), Real.log_div (hn hcκ) (hn hc0)]
  linarith

section Stage

variable (p : Parameters) {m : ℕ} (L : Fin m → ℕ) (s : ZMod p.n)

/-- `r_κ = oldScattering b e X_κ`, the compressed response of the old network with source `κ`
at the matched value `z_b(e)` (the `r_κ` of the stage factorization). -/
abbrev scsResponse (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (b e : ℝ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords p.n p.W) : Matrix (Fin 2 × Fin p.W) (Fin 2 × Fin p.W) ℂ :=
  oldScattering b e (oldSchur (oldInterior L s π S k e (boundaryZ b e) buf κ ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf κ ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf κ ω)ᴴ)

/-- **The stage log difference is the collar log difference.** Almost surely under the original
prior,
`log(|det H^S_κ|/|det H^S_0|) - log(|det H^{S∪k}_κ|/|det H^{S∪k}_0|)
= log|det(I - U r_κ)| - log|det(I - U r₀)|`, with `U = collarScattering b e 0 0` of the fresh
collar and `r_κ = oldScattering b e X_κ`, at every `e ∈ (-2,2)` with
`z = z_b(e)` and each fixed `κ ≥ 0`.
-/
theorem scs_stageLog_sub_ae (hL : IsCollarLayout p.n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) {e : ℝ} (he1 : -2 < e) (he2 : e < 2) (buf : ℕ) {κ : ℝ}
    (hκ : 0 ≤ κ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      Real.log (‖(stageMatrix L s π S e (boundaryZ p.b e) buf κ ω).det‖ /
          ‖(stageMatrix L s π S e (boundaryZ p.b e) buf 0 ω).det‖) -
        Real.log (‖(stageMatrix L s π (insert k S) e (boundaryZ p.b e) buf κ ω).det‖ /
          ‖(stageMatrix L s π (insert k S) e (boundaryZ p.b e) buf 0 ω).det‖) =
      Real.log ‖(1 - collarScattering p.b e 0 0 (toCriticalCollar (freshCollar L s k ω)) *
          scsResponse p L s π S k p.b e buf κ ω).det‖ -
        Real.log ‖(1 - collarScattering p.b e 0 0 (toCriticalCollar (freshCollar L s k ω)) *
          scsResponse p L s π S k p.b e buf 0 ω).det‖ := by
  have hz : 0 < (boundaryZ p.b e).im := boundaryZ_im_pos (by linarith [p.b_lt_half]) he1 he2
  have hbr := collarKc_eq_collarReaction (W := p.W) p.b e
  filter_upwards [stageMatrix_factorization_ae p L s hL hk π e hz buf hκ,
    stageMatrix_factorization_ae p L s hL hk π e hz buf le_rfl,
    scs_ae_isUnit_det_stageMatrix p L s π S e hz buf κ,
    scs_ae_isUnit_det_stageMatrix p L s π S e hz buf 0,
    scs_ae_isUnit_det_stageMatrix p L s π (insert k S) e hz buf κ,
    scs_ae_isUnit_det_stageMatrix p L s π (insert k S) e hz buf 0] with ω hfκ hf0 h1 h2 h3 h4
  rw [scs_log_ratio_cancel h1.ne_zero h2.ne_zero h3.ne_zero h4.ne_zero hfκ hf0,
    (hbr (freshCollar L s k ω)).2.1, (hbr (freshCollar L s k ω)).2.2,
    (hbr (freshCollar L s k ω)).2.2]

/-- The same in the vocabulary of `svStageLog` (base block `0`, unfolded energy `x`, physical
source `κ = δW²/Λ`): for `E + x/Λ ∈ (-2, 2)` and `δ W²/Λ ≥ 0`, almost surely
`svStageLog S - svStageLog (S ∪ {k}) = log|det(I - U r_κ)| - log|det(I - U r₀)|`. -/
theorem scs_svStageLog_sub_ae (hL : IsCollarLayout p.n L) {S : Finset (Fin m)} {k : Fin m}
    (hk : k ∉ S) (π : Pairing) {E Λ δ x : ℝ} (he1 : -2 < E + x / Λ) (he2 : E + x / Λ < 2)
    (hκ : 0 ≤ δ * (p.W : ℝ) ^ 2 / Λ) (buf : ℕ) :
    ∀ᵐ ω ∂(ringCoordLaw p.n p.W p.b),
      svStageLog L π S p.b E Λ δ buf x ω - svStageLog L π (insert k S) p.b E Λ δ buf x ω =
      Real.log ‖(1 - collarScattering p.b (E + x / Λ) 0 0
            (toCriticalCollar (freshCollar L 0 k ω)) *
          scsResponse p L 0 π S k p.b (E + x / Λ) buf (δ * (p.W : ℝ) ^ 2 / Λ) ω).det‖ -
        Real.log ‖(1 - collarScattering p.b (E + x / Λ) 0 0
            (toCriticalCollar (freshCollar L 0 k ω)) *
          scsResponse p L 0 π S k p.b (E + x / Λ) buf 0 ω).det‖ :=
  scs_stageLog_sub_ae p L 0 hL hk π he1 he2 buf hκ

end Stage

/-!
## The certificate distance
-/

/-- `d(r₀) = d(X₀)`: the scattering form of the scalar certificate distance of
`oldScattering b e X` is the matched distance of `X` (`Im z_b(e) > 0`). -/
theorem scs_scatteringDistance_oldScattering {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    scatteringDistance b e (oldScattering b e X) = matchedDistance b e X := by
  have h2 : (twoIEta b e)⁻¹ • (1 - oldScattering b e X) = (boundaryZ b e • 1 - X)⁻¹ := by
    rw [oldScattering, sub_sub_cancel, smul_smul]
    have : (twoIEta b e)⁻¹ * (2 * ((boundaryZ b e).im : ℂ) * Complex.I) = 1 := by
      rw [← twoIEta]; exact inv_mul_cancel₀ (twoIEta_ne_zero hη)
    rw [this, one_smul]
  rw [scatteringDistance, h2, matchedDistance]

end BlockBand.Endpoints
