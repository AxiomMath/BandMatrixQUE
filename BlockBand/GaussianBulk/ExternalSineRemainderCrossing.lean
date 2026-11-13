module

public import BlockBand.GaussianBulk.ExternalSineRemainderCentral

/-!
# Fubini for the local crossing and the central bound

`centralNear a = ∫_{|b| ≤ η/2} amp(a + ib) db` (local amplitude `amp`) is integrable on
`[-r, r]` and `∫_{-r}^{r} centralNear ≤ ∫_{localCrossingBox} amp` by Fubini for Lebesgue measure
on `ℂ ≅ ℝ × ℝ` (`Complex.volume_preserving_equiv_real_prod`, `setIntegral_prod`);
`integral_localGraphVerticalAmplitude_le` bounds the box integral. With the far part
(`integral_horizontalPhaseWeight_core_le`) this gives `integral_centralGraphMajorant_le`:
`∫_{x₀-r}^{x₀+r} g ≤ centralCrossingBound`, `g(x) = centralMajorant (x - x₀)`, the majorant used
on the central graph by `norm_curveIntegral_actualLevelGraphPath_le`.

Domain: `N ≥ 1`, `0 < t ≤ tmax`, `ρ > 0`, positive level root `y₀ ≥ η > 0` at `x₀`,
`levelPsi d t x₀ = E`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology

/-- The near vertical part at horizontal offset `a`. -/
def centralNear {N : ℕ} (d : Fin N → ℝ) (E t η rho x₀ y₀ xi zeta : ℝ) (a : ℝ) : ℝ :=
  ∫ b in Icc (-(η/2)) (η/2), localGraphVerticalAmplitude d E t rho x₀ y₀ xi zeta ⟨a, b⟩

/-- The central majorant at offset `a`. -/
def centralMajorant {N : ℕ} (d : Fin N → ℝ) (E t tmax η rho x₀ y₀ xi zeta : ℝ) (a : ℝ) : ℝ :=
  centralNear d E t η rho x₀ y₀ xi zeta a +
    centralFarConstant η tmax * horizontalPhaseWeight d E t x₀ (N:ℝ) (|xi|/(t*rho)) a

/-- The explicit `O(N^{-1/2})` central bound: local crossing box plus far vertical part. -/
def centralCrossingBound (N : ℕ) (t tmax η rho xi : ℝ) : ℝ :=
  localCrossingConstant η tmax*
      Real.exp ((|xi|/(t*rho))^2/(2*((N:ℝ)*η^2/(16*tmax^2))))*
        (Real.pi*Real.sqrt Real.pi/Real.sqrt ((η^2/(32*tmax^2))*(N:ℝ))) +
    centralFarConstant η tmax *
      (Real.exp ((|xi|/(t*rho))^2/(2*(N:ℝ)*horizontalGaussianCoefficient η tmax))*
        Real.sqrt (Real.pi/((N:ℝ)*horizontalGaussianCoefficient η tmax/2)))

/-- The far-part constant is nonnegative. -/
theorem centralFarConstant_nonneg (η tmax : ℝ) (hη : 0 < η) : 0 ≤ centralFarConstant η tmax := by
  unfold centralFarConstant centralSpeedBound verticalMassConstant
  positivity

/-- **Fubini for the local crossing.** -/
theorem centralNear_integrableOn_and_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ y₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hrho : 0 < rho) (hr : PositiveLevelRoot d t x₀ y₀) (hheight : η ≤ y₀)
    (hpsi : levelPsi d t x₀ = E) :
    IntegrableOn (centralNear d E t η rho x₀ y₀ xi zeta)
        (Icc (-graftedCentralRadius tmax η) (graftedCentralRadius tmax η)) ∧
      (∫ a in Icc (-graftedCentralRadius tmax η) (graftedCentralRadius tmax η),
          centralNear d E t η rho x₀ y₀ xi zeta a) ≤
        localCrossingConstant η tmax*
          Real.exp ((|xi|/(t*rho))^2/(2*((N:ℝ)*η^2/(16*tmax^2))))*
            (Real.pi*Real.sqrt Real.pi/Real.sqrt ((η^2/(32*tmax^2))*(N:ℝ))) := by
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  set r := graftedCentralRadius tmax η with hrdef
  set amp := localGraphVerticalAmplitude d E t rho x₀ y₀ xi zeta with hamp
  set e := Complex.measurableEquivRealProd
  have hmp : MeasurePreserving e.symm (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
    Complex.volume_preserving_equiv_real_prod.symm _
  have hemb : MeasurableEmbedding e.symm := e.symm.measurableEmbedding
  set Φ : ℝ × ℝ → ℝ := fun p => amp (e.symm p) with hΦ
  have hbox := integrable_localGraphVerticalAmplitude hN d E t tmax rho η x₀ y₀ xi zeta ht htmax
    hrho hη hr hheight hpsi
  have hΦbox : IntegrableOn Φ (e.symm ⁻¹' localCrossingBox η tmax) :=
    (hmp.integrableOn_comp_preimage hemb).mpr hbox
  set Rect : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc (-(η/2)) (η/2) with hRect
  have hsub : Rect ⊆ e.symm ⁻¹' localCrossingBox η tmax := by
    intro p hp
    simp only [hRect, mem_prod, mem_Icc] at hp
    have hr4 : r ≤ η^2/(4*Real.sqrt tmax) := by
      simp only [hrdef, graftedCentralRadius]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [Real.sqrt_pos.mpr htm]
    simp only [mem_preimage, localCrossingBox, mem_ofPred_eq, e,
      Complex.measurableEquivRealProd_symm_apply]
    exact ⟨abs_le.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      abs_le.mpr ⟨hp.2.1, hp.2.2⟩⟩
  have hΦR : IntegrableOn Φ Rect := hΦbox.mono_set hsub
  have hnn : ∀ p, 0 ≤ Φ p := fun p => by
    simp only [hΦ, hamp, localGraphVerticalAmplitude]; positivity
  -- Fubini
  have hprod : (∫ p in Rect, Φ p) =
      ∫ a in Icc (-r) r, centralNear d E t η rho x₀ y₀ xi zeta a := by
    rw [Measure.volume_eq_prod, setIntegral_prod Φ (by rw [← Measure.volume_eq_prod]; exact hΦR)]
    rfl
  have hint : IntegrableOn (centralNear d E t η rho x₀ y₀ xi zeta) (Icc (-r) r) := by
    have h1 : Integrable Φ (((volume : Measure ℝ).restrict (Icc (-r) r)).prod
        ((volume : Measure ℝ).restrict (Icc (-(η/2)) (η/2)))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hΦR
    exact h1.integral_prod_left
  refine ⟨hint, ?_⟩
  rw [← hprod]
  have hle : (∫ p in Rect, Φ p) ≤ ∫ p in e.symm ⁻¹' localCrossingBox η tmax, Φ p :=
    setIntegral_mono_set hΦbox (Eventually.of_forall hnn) (Eventually.of_forall hsub)
  have heq : (∫ p in e.symm ⁻¹' localCrossingBox η tmax, Φ p) =
      ∫ z in localCrossingBox η tmax, amp z :=
    hmp.setIntegral_preimage_emb hemb amp _
  refine hle.trans (le_of_eq heq |>.trans ?_)
  exact integral_localGraphVerticalAmplitude_le hN d E t tmax rho η x₀ y₀ xi zeta ht htmax hrho
    hη hr hheight hpsi

/-- **The central majorant is integrable and `∫_{x₀-r}^{x₀+r} centralMajorant(x - x₀) dx ≤
centralCrossingBound`.** -/
theorem integral_centralGraphMajorant_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax η rho x₀ y₀ xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (hη : 0 < η)
    (hrho : 0 < rho) (hr : PositiveLevelRoot d t x₀ y₀) (hheight : η ≤ y₀)
    (hpsi : levelPsi d t x₀ = E) :
    IntervalIntegrable (fun x => centralMajorant d E t tmax η rho x₀ y₀ xi zeta (x - x₀)) volume
        (x₀ - graftedCentralRadius tmax η) (x₀ + graftedCentralRadius tmax η) ∧
      (∫ x in (x₀ - graftedCentralRadius tmax η)..(x₀ + graftedCentralRadius tmax η),
          centralMajorant d E t tmax η rho x₀ y₀ xi zeta (x - x₀)) ≤
        centralCrossingBound N t tmax η rho xi := by
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  set r := graftedCentralRadius tmax η with hrdef
  have hr0 : 0 < r := by simp only [hrdef, graftedCentralRadius]; positivity
  set k := |xi|/(t*rho)
  obtain ⟨hnearI, hnearB⟩ := centralNear_integrableOn_and_le hN d E t tmax η rho x₀ y₀ xi zeta ht
    htmax hη hrho hr hheight hpsi
  rw [← hrdef] at hnearI hnearB
  have hcontW : Continuous (horizontalPhaseWeight d E t x₀ (N:ℝ) k) := by
    unfold horizontalPhaseWeight
    have := levelAction_continuous hN d E t ht
    fun_prop
  have hWI : IntegrableOn (horizontalPhaseWeight d E t x₀ (N:ℝ) k) (Icc (-r) r) :=
    hcontW.continuousOn.integrableOn_Icc
  have hK := centralFarConstant_nonneg η tmax hη
  have hMI : IntegrableOn (centralMajorant d E t tmax η rho x₀ y₀ xi zeta) (Icc (-r) r) :=
    hnearI.add (hWI.const_mul _)
  -- far part bound
  have hy := levelHeight_eq_of_root hN d t x₀ y₀ ht hr
  have hcore := integral_horizontalPhaseWeight_core_le hN d E t x₀ η tmax (N:ℝ) k ht htmax hη
    (by rw [hy]; exact hheight) hpsi hN0
  set ρh := horizontalGaussianRadius η tmax
  have hrh : r ≤ ρh := by
    simp only [hrdef, graftedCentralRadius, ρh, horizontalGaussianRadius]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [Real.sqrt_pos.mpr htm]
  have hsubW : Icc (-r) r ⊆ {a : ℝ | |a| ≤ ρh} := fun a ha =>
    (abs_le.mpr ⟨ha.1, ha.2⟩).trans hrh
  have hWbig : IntegrableOn (horizontalPhaseWeight d E t x₀ (N:ℝ) k) {a : ℝ | |a| ≤ ρh} := by
    refine (hcontW.continuousOn.integrableOn_Icc (a := -ρh) (b := ρh)).mono_set ?_
    intro a ha
    exact ⟨(abs_le.mp ha).1, (abs_le.mp ha).2⟩
  have hWle : (∫ a in Icc (-r) r, horizontalPhaseWeight d E t x₀ (N:ℝ) k a) ≤
      Real.exp (k^2/(2*(N:ℝ)*horizontalGaussianCoefficient η tmax))*
        Real.sqrt (Real.pi/((N:ℝ)*horizontalGaussianCoefficient η tmax/2)) :=
    (setIntegral_mono_set hWbig (Eventually.of_forall fun a => by
      unfold horizontalPhaseWeight; positivity) (Eventually.of_forall hsubW)).trans hcore
  -- change of variables `x = x₀ + a`
  have hII : IntervalIntegrable (centralMajorant d E t tmax η rho x₀ y₀ xi zeta) volume (-r) r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hMI
  have hshift := hII.comp_sub_right x₀
  have e1 : -r + x₀ = x₀ - r := by ring
  have e2 : r + x₀ = x₀ + r := by ring
  rw [e1, e2] at hshift
  refine ⟨hshift, ?_⟩
  rw [intervalIntegral.integral_comp_sub_right, show x₀ - r - x₀ = -r by ring,
    show x₀ + r - x₀ = r by ring, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  unfold centralMajorant
  rw [integral_add hnearI (hWI.const_mul _), integral_const_mul]
  unfold centralCrossingBound
  exact add_le_add hnearB (mul_le_mul_of_nonneg_left hWle hK)

end BlockBand.GaussianBulk
