module

public import BlockBand.GaussianBulk.ExternalSineRemainderRate
public import BlockBand.GaussianBulk.ExternalSineDensity
public import BlockBand.GaussianBulk.ExternalSineCoreRepeated
public import BlockBand.GaussianBulk.ExternalSineCoreMDE
public import BlockBand.Adapters.CEH.ETHNorms

/-!
# The normalized kernel minus the sine kernel

No law: these are exact identities and norms for the Johansson kernel `Johansson.kernel S d R L`,
`S = t/N`, for `N > 0`, `t > 0`, `ρ > 0`, arbitrary real `d`, admissible `(R, L)`, the loop
`γ = nativeGraftedLevelLoop hN d t tmax η x₀`, `0 < η ≤ y₀ = levelHeight d t x₀ = tπρ`, `L' ≥ L` with
`γ ⊆ ball 0 L'`.

The difference between the gauged, rescaled Johansson kernel and the sine kernel is written as
a curve integral of the remainder over the grafted level loop.

* `gaugedKernel_sub_sine_eq`: with `u = E + ξ/(Nρ)`, `v = E + ζ/(Nρ)` and the real
  gauge `g = realSineGauge N E t ρ x₀`,
  `e^{-g(ξ)} K(u,v) e^{g(ζ)}/(Nρ) - sinc(π(ξ-ζ)) = ∫_γ (gauge · W) dz / ((2πi)² tρ)`: the segment
  residue of `kernel_eq_residue_add_remainder` is exactly
  `normalizedSegmentResidue`, i.e. the sine kernel with diagonal `1`.
* `pieceIntegrable_gaugedRemainder`: the gauged remainder integrand is curve integrable on
  every good path in `{Re z < L'} \ {d_j}`.
* `abs_spectralSource_le_norm`: `|d_j| ≤ ‖F‖` (Euclidean operator norm), so
  `Σ|d_j| ≤ N ‖F‖` (the loop length is polynomial when `‖F‖ ≤ N^A`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology Matrix
open BlockBand.External
open scoped NNReal Matrix.Norms.L2Operator

/-- Eigenvalues are bounded by the Euclidean operator norm. -/
theorem abs_spectralSource_le_norm {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    (j : Fin N) : |spectralSource F hF j| ≤ ‖F‖ := by
  obtain ⟨U, hU⟩ := exists_unitary_diagonal_spectralSource F hF
  have : Nonempty (Fin N) := ⟨j⟩
  set D := Matrix.diagonal (fun i => (spectralSource F hF i : ℂ)) with hDdef
  have hUU : (U : Matrix (Fin N) (Fin N) ℂ)ᴴ * (U : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  have hD : D = (U : Matrix (Fin N) (Fin N) ℂ)ᴴ * F * (U : Matrix (Fin N) (Fin N) ℂ) := by
    rw [hU]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hUn : ‖(U : Matrix (Fin N) (Fin N) ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary U.2
  have hUhn : ‖(U : Matrix (Fin N) (Fin N) ℂ)ᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose, hUn]
  have hDn : ‖D‖ ≤ ‖F‖ := by
    rw [hD]
    calc ‖(U : Matrix (Fin N) (Fin N) ℂ)ᴴ * F * (U : Matrix (Fin N) (Fin N) ℂ)‖
        ≤ ‖(U : Matrix (Fin N) (Fin N) ℂ)ᴴ * F‖ * ‖(U : Matrix (Fin N) (Fin N) ℂ)‖ :=
          norm_mul_le _ _
      _ ≤ ‖(U : Matrix (Fin N) (Fin N) ℂ)ᴴ‖ * ‖F‖ * ‖(U : Matrix (Fin N) (Fin N) ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = ‖F‖ := by rw [hUhn, hUn]; ring
  have he := Adapters.CEH.norm_entry_le D j j
  simp only [hDdef, Matrix.diagonal_apply_eq, Complex.norm_real, Real.norm_eq_abs] at he
  exact he.trans hDn

/-- `Σ_j |d_j| ≤ N ‖F‖`. -/
theorem graftedDeformationRadius_spectralSource_le {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) : graftedDeformationRadius (spectralSource F hF) ≤ N * ‖F‖ := by
  unfold graftedDeformationRadius
  have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin N))
    (fun j => |spectralSource F hF j|) ‖F‖ (fun j _ => abs_spectralSource_le_norm F hF j)
  simpa using this

/-- The gauged remainder integrand is curve integrable on every good path in
`K = {Re z < L'} \ {d_j}`. -/
theorem pieceIntegrable_gaugedRemainder {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (u v L' x₀ : ℝ) (c : ℂ) :
    PieceIntegrable (fun z => c * remainderIntegrand S d u v L' x₀ z)
      {z | z.re < L' ∧ ∀ j, z ≠ (d j : ℂ)} := by
  intro a b δ hδ hr
  have hnot : ∀ z ∈ range δ, ∀ p ∈ sourcePoleList d, z ≠ p := by
    intro z hz p hp h
    obtain ⟨j, rfl⟩ := mem_sourcePoles_of_mem_list d p hp
    exact (hr hz).2 j h
  have hVc : ContinuousOn (Johansson.verticalIntegral S d u v L') (range δ) := by
    rw [show Johansson.verticalIntegral S d u v L' =
        fun z => kernelNumerator S d u v L' z * (poleProd (sourcePoleList d) z)⁻¹ from
      funext (verticalIntegral_eq_numerator S d u v L')]
    exact ((differentiableOn_kernelNumerator S hS d u v L').continuousOn.mono
      (fun z hz => (hr hz).1)).mul
      ((continuous_poleProd _).continuousOn.inv₀ (fun z hz => poleProd_ne_zero (hnot z hz)))
  have iV := hδ.integrable (fun z => c * Johansson.verticalIntegral S d u v L' z)
    (continuousOn_const.mul hVc)
  obtain ⟨C, hCb⟩ := (isCompact_range δ.continuous).exists_bound_of_continuousOn
    (continuous_residueExp ((u - v) / S)).continuousOn
  have iI : CurveIntegrable (scalarForm (fun z => c * (2 * Real.pi * Complex.I *
      residueIndicator ((u - v) / S) x₀ z))) δ := by
    refine hδ.integrable_of_bdd _ (measurable_const.mul (measurable_const.mul
      (measurable_residueIndicator _ x₀))) (‖c‖ * (‖(2 * Real.pi * Complex.I : ℂ)‖ * C))
      (fun z hz => ?_)
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold residueIndicator
    split_ifs
    · exact hCb z hz
    · simpa using (norm_nonneg _).trans (hCb z hz)
  have hW : scalarForm (fun z => c * remainderIntegrand S d u v L' x₀ z) =
      scalarForm (fun z => c * Johansson.verticalIntegral S d u v L' z) -
        scalarForm (fun z => c * (2 * Real.pi * Complex.I *
          residueIndicator ((u - v) / S) x₀ z)) := by
    funext z
    simp only [scalarForm, remainderIntegrand, Pi.sub_apply, mul_sub]
    exact sub_smul _ _ (ContinuousLinearMap.id ℂ ℂ)
  rw [hW]
  exact iV.sub iI

/-- **Item (a): the gauged normalized kernel minus the sine kernel is the gauged loop
remainder.** -/
theorem gaugedKernel_sub_sine_eq {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) (R L : ℝ)
    (hC : Johansson.AdmissibleContours d R L) (E rho xi zeta : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (hrho : 0 < rho) (tmax η x₀ : ℝ) (htmax : (t:ℝ) ≤ tmax) (hη : 0 < η)
    (hheight : η ≤ levelHeight d t x₀) (hy : levelHeight d t x₀ = t * Real.pi * rho)
    (L' : ℝ) (hLL' : L ≤ L')
    (hball : range (nativeGraftedLevelLoop hN d t tmax η x₀ (by exact_mod_cast ht)) ⊆
      Metric.ball 0 L') :
    Complex.exp (-((realSineGauge N E t rho x₀ xi : ℝ) : ℂ)) *
        Johansson.kernel (Johansson.sourceTime N t) d R L (E + xi/((N:ℝ)*rho))
          (E + zeta/((N:ℝ)*rho)) *
        Complex.exp ((realSineGauge N E t rho x₀ zeta : ℝ) : ℂ) / (((N:ℝ)*rho : ℝ) : ℂ) -
      (sineKernel xi zeta : ℂ) =
    curveIntegral (scalarForm (fun z => remainderGauge N E t rho x₀ xi zeta *
        remainderIntegrand (Johansson.sourceTime N t) d (E + xi/((N:ℝ)*rho))
          (E + zeta/((N:ℝ)*rho)) L' x₀ z))
        (nativeGraftedLevelLoop hN d t tmax η x₀ (by exact_mod_cast ht)) /
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2 * ((t * rho : ℝ) : ℂ)) := by
  have htr : (0:ℝ) < t := ht
  have hS : 0 < Johansson.sourceTime N t := by
    rw [Johansson.sourceTime]; exact div_pos ht (by exact_mod_cast hN)
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hRG : remainderGauge N E t rho x₀ xi zeta =
      Complex.exp ((((N:ℝ)*((E + zeta/((N:ℝ)*rho))^2-(E + xi/((N:ℝ)*rho))^2)/(2*t) : ℝ)) : ℂ) *
        Complex.exp (-((realSineGauge N E t rho x₀ xi : ℝ) : ℂ)) *
        Complex.exp ((realSineGauge N E t rho x₀ zeta : ℝ) : ℂ) := by
    unfold remainderGauge
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  set u := E + xi/((N:ℝ)*rho)
  set v := E + zeta/((N:ℝ)*rho)
  set γ := nativeGraftedLevelLoop hN d t tmax η x₀ (by exact_mod_cast ht)
  rw [kernel_eq_residue_add_remainder hN _ hS d R L hC u v t tmax η x₀ htr htmax hη hheight L'
    hLL' hball]
  -- the segment residue
  have hκ : (u - v) / (Johansson.sourceTime N t : ℝ) = (xi - zeta)/(t*rho) := by
    rw [Johansson.sourceTime_coe]
    simp only [u, v]
    field_simp
    ring
  rw [hκ, hy]
  have hres := normalizedSegmentResidue_eq N hN E t rho x₀ (t*Real.pi*rho) xi zeta htr hrho rfl
  unfold normalizedSegmentResidue at hres
  set seg := upwardExponentialSegment x₀ (t*Real.pi*rho) ((xi - zeta)/(t*rho))
  set β : ℝ := (N:ℝ)*(v^2-u^2)/(2*t) with hβ
  have hβc : (((v:ℂ))^2 - ((u:ℂ))^2)/(2*((Johansson.sourceTime N t : ℝ) : ℂ)) = ((β:ℝ):ℂ) := by
    rw [Johansson.sourceTime_coe, hβ]
    push_cast
    field_simp
  rw [show ((Johansson.sourceTime N t : ℝ≥0) : ℂ) = ((Johansson.sourceTime N t : ℝ) : ℂ) from rfl,
    hβc]
  set gx := realSineGauge N E t rho x₀ xi
  set gz := realSineGauge N E t rho x₀ zeta
  -- pull the gauge out of the curve integral
  have hsm : scalarForm (fun z => remainderGauge N E t rho x₀ xi zeta *
      remainderIntegrand (Johansson.sourceTime N t) d u v L' x₀ z) =
      remainderGauge N E t rho x₀ xi zeta •
        scalarForm (remainderIntegrand (Johansson.sourceTime N t) d u v L' x₀) := by
    funext z
    simp only [scalarForm, Pi.smul_apply]
    exact mul_smul _ _ (ContinuousLinearMap.id ℂ ℂ)
  rw [hsm, curveIntegral_smul, smul_eq_mul, hRG]
  set Iγ := curveIntegral (scalarForm (remainderIntegrand (Johansson.sourceTime N t) d u v L' x₀)) γ
  have hsine : (sineKernel xi zeta : ℂ) = (unitSineKernel xi zeta : ℂ) := rfl
  rw [hsine]
  have hQ : Complex.exp (((gx - gz : ℝ)) : ℂ) * Complex.exp (-((gx:ℝ):ℂ)) *
      Complex.exp ((gz:ℝ):ℂ) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
    exact Complex.exp_zero
  have hP : Complex.exp ((β:ℝ):ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hseg : seg = Complex.exp (((gx - gz : ℝ)) : ℂ) * (unitSineKernel xi zeta : ℂ) *
      (((2*Real.pi*t*rho:ℝ):ℂ)*Complex.I) / Complex.exp ((β:ℝ):ℂ) := by
    have hD : (((2*Real.pi*t*rho:ℝ):ℂ)*Complex.I) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
    have hX : ((2*Real.pi*t*rho:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    rw [eq_div_iff hP, ← hres]
    field_simp
  rw [hseg, Johansson.sourceTime_coe]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htc : ((t:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htr.ne'
  have hrc : (rho:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrho.ne'
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hG1 : Complex.exp (-((gx:ℝ):ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hG2 : Complex.exp ((gz:ℝ):ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hG2' : Complex.exp ((gz:ℝ):ℂ) = (Complex.exp (((gx - gz : ℝ)) : ℂ) *
      Complex.exp (-((gx:ℝ):ℂ)))⁻¹ := by
    exact (inv_eq_of_mul_eq_one_right hQ).symm
  rw [hG2']
  push_cast
  field_simp
  ring

end BlockBand.GaussianBulk
