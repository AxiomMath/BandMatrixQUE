module

public import BlockBand.GaussianBulk.ExternalSineRemainderMesh
public import BlockBand.GaussianBulk.HorizontalPhaseIntegration

/-!
# The remainder on the central graph (local crossing) piece

On the central graph `z = x₀ + a + i y(x₀+a)`, `0 < |a| ≤ r` (`r = graftedCentralRadius`):
the vertical majorant is split at `|v - y₀| ≤ η/2`. The near part is the local amplitude
`localGraphVerticalAmplitude` (whose planar integral over `localCrossingBox` is `O(N^{-1/2})`,
`integral_localGraphVerticalAmplitude_le`); on the rest `|w - z| ≥ η/4` and the vertical mass
is bounded (`integral_norm_relativeVerticalExp_le`), leaving the horizontal Gaussian
`horizontalPhaseWeight` (`integral_horizontalPhaseWeight_core_le`, `O(N^{-1/2})`).
The opposite-saddle region `v ≈ -y₀` is part of the rest (denominator `≥ η/4`, bounded mass).

* `remainderMajorant_central_le`: the pointwise split, for `a ≠ 0`;
* in the sibling module `ExternalSineRemainderCrossing`, `centralMajorant` and
  `integral_centralGraphMajorant_le`: Fubini (`setIntegral_prod`, the measure
  preserving `Complex.measurableEquivRealProd`) and the explicit bound `centralCrossingBound`.

Domain: `N ≥ 1`, `0 < t ≤ tmax`, `ρ > 0`, positive level root `y₀ ≥ η > 0` at `x₀`,
`levelPsi d t x₀ = E`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology

/-- Measurability of the vertical density `v ↦ ‖G(z,x₀+iv)‖/‖x₀+iv-z‖`. -/
theorem measurable_verticalDensity {N : ℕ} (d : Fin N → ℝ) (E t rho x₀ xi zeta : ℝ) (z : ℂ) :
    Measurable (fun v : ℝ => ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ /
      ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖) := by
  have hphase : Measurable (saddlePhase d E t) := by
    unfold saddlePhase complexMean
    fun_prop
  have hw : Measurable (fun v : ℝ => (x₀:ℂ)+(v:ℂ)*Complex.I) := by fun_prop
  have hG : Measurable (fun v : ℝ => gaugedJohanssonExp d E t rho x₀ xi zeta z
      ((x₀:ℂ)+(v:ℂ)*Complex.I)) := by
    unfold gaugedJohanssonExp
    have hzw := hphase.comp hw
    fun_prop
  exact hG.norm.div (hw.sub_const z).norm

/-- The vertical density is integrable off `Re z = x₀`. -/
theorem integrable_verticalDensity {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ y₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hrho : 0 < rho) (hr : PositiveLevelRoot d t x₀ y₀) (hheight : η ≤ y₀) (z : ℂ)
    (hz : z.re ≠ x₀) :
    Integrable (fun v : ℝ => ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ /
      ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hint := (integrable_relativeVerticalExp hN d E t x₀ y₀ η tmax (N:ℝ) ht hr hη hheight
    htmax hN0).norm
  set Ez := Real.exp (-(N:ℝ)*(verticalRealAction d E t z.re z.im-verticalRealAction d E t x₀ y₀)+
          xi*(z.re-x₀)/(t*rho))
  have hδ : 0 < |z.re - x₀| := abs_pos.mpr (sub_ne_zero.mpr hz)
  refine (hint.const_mul (Ez / |z.re - x₀|)).mono'
    (measurable_verticalDensity d E t rho x₀ xi zeta z).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
    norm_gaugedJohanssonExp_factor hN d E t rho x₀ y₀ v xi zeta ht hrho z]
  have hden : |z.re - x₀| ≤ ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖ := by
    refine (abs_sub_comm _ _).le.trans ?_
    have := Complex.abs_re_le_norm (((x₀:ℂ)+(v:ℂ)*Complex.I)-z)
    simpa using this
  have hnum : 0 ≤ ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ * Ez := by positivity
  calc ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ * Ez / ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖
      ≤ ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ * Ez / |z.re - x₀| :=
        div_le_div_of_nonneg_left hnum hδ hden
    _ = Ez / |z.re - x₀| * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖ := by ring

/-- The local amplitude at `⟨a, b⟩` is the vertical density at height `y₀ + b` times the graph
speed. -/
theorem localGraphVerticalAmplitude_mk {N : ℕ} (d : Fin N → ℝ) (E t rho x₀ y₀ xi zeta a b : ℝ) :
    localGraphVerticalAmplitude d E t rho x₀ y₀ xi zeta ⟨a, b⟩ =
      ‖gaugedJohanssonExp d E t rho x₀ xi zeta (actualLevelGraphPoint d t (x₀+a))
          ((x₀:ℂ)+((y₀+b:ℝ):ℂ)*Complex.I)‖ /
        ‖((x₀:ℂ)+((y₀+b:ℝ):ℂ)*Complex.I)-actualLevelGraphPoint d t (x₀+a)‖ *
        ‖levelGraphVelocity d t (x₀+a)‖ := by
  unfold localGraphVerticalAmplitude actualLevelGraphPoint
  simp only
  ring

/-- The graph speed bound on the central strip. -/
def centralSpeedBound (η tmax : ℝ) : ℝ := Real.sqrt (1+(2*Real.sqrt tmax/η)^2)

/-- The constant of the far vertical part: `(4/η) · speed · vertical mass`. -/
def centralFarConstant (η tmax : ℝ) : ℝ :=
  4/η * centralSpeedBound η tmax * verticalMassConstant η tmax

/-- **Pointwise central split.** For `0 < |a| ≤ r`, `z = x₀ + a + i y(x₀+a)`:
`m(z) · |1 + i y'| ≤ ∫_{|b| ≤ η/2} amp(a + ib) db + (4/η)·speed·mass · e^{-N(A(x₀+a)-A(x₀)) + k|a|}`. -/
theorem remainderMajorant_central_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ y₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hrho : 0 < rho) (hr : PositiveLevelRoot d t x₀ y₀) (hheight : η ≤ y₀) (a : ℝ)
    (ha0 : a ≠ 0) (ha : |a| ≤ graftedCentralRadius tmax η) :
    remainderMajorant d E t rho x₀ xi zeta (actualLevelGraphPoint d t (x₀+a)) *
        ‖levelGraphVelocity d t (x₀+a)‖ ≤
      (∫ b in Icc (-(η/2)) (η/2), localGraphVerticalAmplitude d E t rho x₀ y₀ xi zeta ⟨a, b⟩) +
        centralFarConstant η tmax *
          horizontalPhaseWeight d E t x₀ (N:ℝ) (|xi|/(t*rho)) a := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  set z := actualLevelGraphPoint d t (x₀+a) with hzdef
  set V := ‖levelGraphVelocity d t (x₀+a)‖ with hV
  set F : ℝ → ℝ := fun v => ‖gaugedJohanssonExp d E t rho x₀ xi zeta z ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ /
      ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-z‖ with hF
  set I := Icc (-(η/2)) (η/2) with hI
  have hzre : z.re = x₀ + a := by simp [hzdef, actualLevelGraphPoint]
  have hzim : z.im = levelHeight d t (x₀+a) := by simp [hzdef, actualLevelGraphPoint]
  have hz : z.re ≠ x₀ := by rw [hzre]; intro h; apply ha0; linarith
  have hFi : Integrable F :=
    integrable_verticalDensity hN d E t tmax η rho x₀ y₀ xi zeta ht htmax hη hrho hr hheight z hz
  have hFs : Integrable (fun b => F (y₀ + b)) := hFi.comp_add_left y₀
  have hy := levelHeight_eq_of_root hN d t x₀ y₀ ht hr
  have hb0 : η ≤ levelHeight d t x₀ := by rw [hy]; exact hheight
  have hclose : |x₀ + a - x₀| ≤ η^2/(4*Real.sqrt tmax) := by
    have : graftedCentralRadius tmax η ≤ η^2/(4*Real.sqrt tmax) := by
      unfold graftedCentralRadius
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [Real.sqrt_pos.mpr htm]
    simpa using ha.trans this
  -- speed bound
  have hVB : V ≤ centralSpeedBound η tmax := by
    have hs := levelGraphVelocity_norm_sq_le hN d t tmax η x₀ (x₀+a) ht htmax hη hb0 hclose
    unfold centralSpeedBound
    rw [hV]
    exact Real.le_sqrt_of_sq_le hs
  have hV0 : 0 ≤ V := norm_nonneg _
  -- shift and split
  have hm : remainderMajorant d E t rho x₀ xi zeta z = ∫ b, F (y₀ + b) := by
    unfold remainderMajorant
    exact (integral_add_left_eq_self F y₀).symm
  have hIm : MeasurableSet I := measurableSet_Icc
  rw [hm, ← integral_add_compl hIm hFs, add_mul]
  apply add_le_add
  · -- near part: the local amplitude
    rw [← integral_mul_const]
    apply le_of_eq
    apply setIntegral_congr_fun hIm
    intro b _
    dsimp only
    rw [localGraphVerticalAmplitude_mk]
  · -- far part
    set Ez := Real.exp (-(N:ℝ)*(verticalRealAction d E t z.re z.im -
        verticalRealAction d E t x₀ y₀) + xi*(z.re-x₀)/(t*rho)) with hEz
    have hEzle : Ez ≤ horizontalPhaseWeight d E t x₀ (N:ℝ) (|xi|/(t*rho)) a := by
      unfold horizontalPhaseWeight
      rw [hEz]
      apply Real.exp_le_exp.mpr
      have hla : verticalRealAction d E t z.re z.im = levelAction d E t (x₀+a) := by
        rw [hzre, hzim, levelAction_eq_saddlePhase_re, verticalRealAction_eq_saddlePhase_re]
      have hl0 : verticalRealAction d E t x₀ y₀ = levelAction d E t x₀ := by
        rw [levelAction_eq_saddlePhase_re, verticalRealAction_eq_saddlePhase_re, hy]
      rw [hla, hl0, hzre]
      have hmic : xi*(x₀+a-x₀)/(t*rho) ≤ |xi|/(t*rho)*|a| := by
        rw [show x₀+a-x₀ = a by ring]
        calc xi*a/(t*rho) ≤ |xi*a|/(t*rho) :=
              div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
          _ = |xi|/(t*rho)*|a| := by rw [abs_mul]; ring
      linarith
    -- denominator on the far part
    have hyclose : |levelHeight d t (x₀+a) - y₀| ≤ η/4 := by
      have h1 := levelHeight_abs_sub_base_le hN d t tmax η x₀ (x₀+a) ht htmax hη hb0
      rw [hy] at h1
      have h2 : (2*Real.sqrt tmax/η)*|x₀+a-x₀| ≤ η/4 := by
        rw [show x₀+a-x₀ = a by ring]
        have hs : 0 < Real.sqrt tmax := Real.sqrt_pos.mpr htm
        have : (2*Real.sqrt tmax/η)*graftedCentralRadius tmax η = η/4 := by
          unfold graftedCentralRadius; field_simp; ring
        rw [← this]
        exact mul_le_mul_of_nonneg_left ha (by positivity)
      linarith
    have hfar : ∀ b ∈ Iᶜ, F (y₀ + b) ≤
        4/η * Ez * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ := by
      intro b hb
      have hb' : η/2 < |b| := by
        simp only [hI, mem_compl_iff, mem_Icc, not_and_or, not_le] at hb
        rcases hb with hb | hb
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have hden : η/4 ≤ ‖((x₀:ℂ)+((y₀+b:ℝ):ℂ)*Complex.I)-z‖ := by
        have h1 := Complex.abs_im_le_norm (((x₀:ℂ)+((y₀+b:ℝ):ℂ)*Complex.I)-z)
        have h2 : (((x₀:ℂ)+((y₀+b:ℝ):ℂ)*Complex.I)-z).im = y₀ + b - levelHeight d t (x₀+a) := by
          simp [hzim]
        rw [h2] at h1
        have h3 : |b| - |levelHeight d t (x₀+a) - y₀| ≤ |y₀ + b - levelHeight d t (x₀+a)| := by
          have := abs_sub_abs_le_abs_sub b (levelHeight d t (x₀+a) - y₀)
          rwa [show b - (levelHeight d t (x₀+a) - y₀) = y₀ + b - levelHeight d t (x₀+a) by ring]
            at this
        linarith
      simp only [hF]
      rw [norm_gaugedJohanssonExp_factor hN d E t rho x₀ y₀ (y₀+b) xi zeta ht hrho z, ← hEz]
      have hnum : 0 ≤ ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ * Ez := by positivity
      calc ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ * Ez /
            ‖((x₀:ℂ)+((y₀+b:ℝ):ℂ)*Complex.I)-z‖
          ≤ ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ * Ez / (η/4) :=
            div_le_div_of_nonneg_left hnum (by positivity) hden
        _ = 4/η * Ez * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ := by field_simp
    have hrel := (integrable_relativeVerticalExp hN d E t x₀ y₀ η tmax (N:ℝ) ht hr hη hheight
      htmax hN0).norm
    have hrels : Integrable (fun b => ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖) :=
      hrel.comp_add_left y₀
    have hmass := integral_norm_relativeVerticalExp_le hN d E t x₀ y₀ η tmax (N:ℝ) ht hr hη
      hheight htmax (by exact_mod_cast hN)
    have hmass' : (∫ b, ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖) ≤
        verticalMassConstant η tmax := by
      rw [integral_add_left_eq_self (fun v => ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) v‖) y₀]
      exact hmass
    have h1 : (∫ b in Iᶜ, F (y₀ + b)) ≤
        ∫ b in Iᶜ, 4/η * Ez * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ :=
      setIntegral_mono_on hFs.integrableOn (hrels.const_mul _).integrableOn hIm.compl hfar
    have h2 : (∫ b in Iᶜ, 4/η * Ez * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖) ≤
        ∫ b, 4/η * Ez * ‖relativeVerticalExp d E t x₀ y₀ (N:ℝ) (y₀+b)‖ :=
      setIntegral_le_integral (hrels.const_mul _) (Eventually.of_forall fun b => by positivity)
    have hF0 : 0 ≤ ∫ b in Iᶜ, F (y₀ + b) := setIntegral_nonneg hIm.compl (fun b _ => by
      simp only [hF]; positivity)
    have hCv : 0 ≤ verticalMassConstant η tmax := by unfold verticalMassConstant; positivity
    calc (∫ b in Iᶜ, F (y₀ + b)) * V
        ≤ (4/η * Ez * verticalMassConstant η tmax) * centralSpeedBound η tmax := by
          apply mul_le_mul _ hVB hV0 (by positivity)
          refine h1.trans (h2.trans ?_)
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left hmass' (by positivity)
      _ ≤ (4/η * horizontalPhaseWeight d E t x₀ (N:ℝ) (|xi|/(t*rho)) a *
            verticalMassConstant η tmax) * centralSpeedBound η tmax := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          apply mul_le_mul_of_nonneg_right _ hCv
          exact mul_le_mul_of_nonneg_left hEzle (by positivity)
      _ = centralFarConstant η tmax * horizontalPhaseWeight d E t x₀ (N:ℝ) (|xi|/(t*rho)) a := by
          unfold centralFarConstant
          ring

end BlockBand.GaussianBulk
