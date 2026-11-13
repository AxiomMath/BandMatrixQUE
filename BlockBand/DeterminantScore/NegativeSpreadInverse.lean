module

public import BlockBand.DeterminantScore.NegativeSpreadPrekopa
public import BlockBand.DeterminantScore.NegativeSpread

/-!
# The negative spread: inverse moments and the full statement

Hypotheses: `IndexedSpectralConvexityStatement` and Prékopa's theorem
(`BlockBand.External.Prekopa.SourceContract`, Prékopa 1973, Theorem 6).

* `tail_le_exp`: from `P(f ≥ r)^θ ≤ P(f ≥ θr)` (`tail_rpow_le`) and `P(f ≥ a) ≤ 1/2`,
  `P(f ≥ r) ≤ 2exp(-(log 2/a) r)` for all `r > 0`;
* Markov with `a = 2E f`, the layer-cake formula (`lintegral_rpow_eq_lintegral_meas_le_mul`) and
  the Gamma integral (`lintegral_two_exp_mul_rpow`) give `E f^{2q} ≤ 2q·2·Γ(2q)·(2E f/log 2)^{2q}`;
  with `(E f)² ≤ E U⁻¹ ≤ 64e⁸/E U` (product clause, `integral_mul_integral_inv_le`):
  `E U^{-q} ≤ C_q (E U)^{-q}`, `C_q = 2q·2·(2/log 2)^{2q}Γ(2q)·(64e⁸)^q`, independent of
  `K, m, t, ℓ` (`negativeSpread_inverse_moment_of_prekopa`).
* `negativeSpread_of_convexity_of_prekopa`: `NegativeSpreadStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal

variable {m : ℕ} {t : ℝ≥0} {K : Matrix (Fin m) (Fin m) ℂ} {ℓ : ℕ}

/-- Exponential tail: if `P(f ≥ a) ≤ 1/2` then `P(f ≥ r) ≤ 2 exp(-(log 2/a) r)`. -/
theorem tail_le_exp (hP : BlockBand.External.Prekopa.SourceContract)
    (hconv : IndexedSpectralConvexityStatement) (hm : 0 < m) (ht : 0 < t)
    (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) {a : ℝ} (ha : 0 < a)
    (hhalf : sectorLaw m t K ℓ {x | a ≤ spreadF (orderedEigs K x)} ≤ ENNReal.ofReal (1 / 2))
    {r : ℝ} (hr : 0 < r) :
    sectorLaw m t K ℓ {x | r ≤ spreadF (orderedEigs K x)} ≤
      ENNReal.ofReal (2 * Real.exp (-(Real.log 2 / a * r))) := by
  have hprob := isProbabilityMeasure_sectorLaw hK hZ
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rcases le_or_gt r a with hra | hra
  · calc sectorLaw m t K ℓ {x | r ≤ spreadF (orderedEigs K x)} ≤ 1 := prob_le_one
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have h1 : Real.log 2 / a * r ≤ Real.log 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ ha]; nlinarith
        have h2 := Real.exp_le_exp.2 (neg_le_neg h1)
        rw [Real.exp_neg, Real.exp_log two_pos] at h2
        linarith
  · set θ := a / r
    have hθ : 0 < θ := div_pos ha hr
    have hθ1 : θ < 1 := (div_lt_one hr).2 hra
    have h := tail_rpow_le hP hconv hm ht hK hZ r hθ hθ1
    have hθr : θ * r = a := by simp only [θ]; field_simp
    rw [hθr] at h
    have h2 := ENNReal.rpow_le_rpow (h.trans hhalf) (z := 1 / θ) (by positivity)
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hθ.ne', ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_pos (by norm_num)] at h2
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
    have : -Real.log 2 * (1 / θ) = -(Real.log 2 / a * r) := by simp only [θ]; field_simp
    rw [this]
    have := Real.exp_pos (-(Real.log 2 / a * r))
    linarith

/-- `∫_0^∞ 2e^{-ρt} t^{p-1} dt = 2ρ^{-p}Γ(p)`, as a lower integral. -/
theorem lintegral_two_exp_mul_rpow {ρ p : ℝ} (hρ : 0 < ρ) (hp : 0 < p) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-(ρ * s))) * ENNReal.ofReal (s ^ (p - 1)) =
      ENNReal.ofReal (2 * ((1 / ρ) ^ p * Real.Gamma p)) := by
  have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi hp hρ
  have hI : IntegrableOn (fun s : ℝ => s ^ (p - 1) * Real.exp (-(ρ * s))) (Ioi 0) := by
    by_contra h
    have h0 := integral_undef h
    rw [hval] at h0
    have : 0 < (1 / ρ) ^ p * Real.Gamma p := by
      have := Real.Gamma_pos_of_pos hp; positivity
    linarith
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun s : ℝ => 2 * (s ^ (p - 1) * Real.exp (-(ρ * s))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < s from hs)) (p - 1)
    positivity
  have h := ofReal_integral_eq_lintegral_ofReal (hI.const_mul 2) hnn
  rw [integral_const_mul, hval] at h
  rw [h]
  refine lintegral_congr fun s => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- The product clause in real form: `E U · E U⁻¹ ≤ 64e⁸` (`U = Σλ⁻²`). -/
theorem integral_mul_integral_inv_le (hconv : IndexedSpectralConvexityStatement) (hm : 0 < m)
    (ht : 0 < t) (hK : K.IsHermitian) (hZ : 0 < (sectorMass m t K ℓ).re) :
    (∫ x, invSqSum (orderedEigs K x) ∂sectorLaw m t K ℓ) *
        (∫ x, (invSqSum (orderedEigs K x))⁻¹ ∂sectorLaw m t K ℓ) ≤ 64 * Real.exp 8 := by
  have hUV : ∀ᵐ x ∂sectorLaw m t K ℓ, sectorInvSq K x = invSqSum (orderedEigs K x) :=
    (ae_det_ne_zero_sectorLaw ht).mono fun x h => (invSqSum_orderedEigs hK h).symm
  obtain ⟨-, hprod⟩ := negativeSpread_product_of_convexity hconv m t K ℓ ht hK hZ
  have h1 : ∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ =
      ENNReal.ofReal (∫ x, invSqSum (orderedEigs K x) ∂sectorLaw m t K ℓ) := by
    rw [lintegral_congr_ae (hUV.mono fun x h => by rw [h]),
      ofReal_integral_eq_lintegral_ofReal (integrable_invSqSum hK hZ)
        (ae_of_all _ fun x => invSqSum_nonneg _)]
  have h2 : ∫⁻ x, ENNReal.ofReal (sectorInvSq K x)⁻¹ ∂sectorLaw m t K ℓ =
      ENNReal.ofReal (∫ x, (invSqSum (orderedEigs K x))⁻¹ ∂sectorLaw m t K ℓ) := by
    rw [lintegral_congr_ae (hUV.mono fun x h => by rw [h]),
      ofReal_integral_eq_lintegral_ofReal (integrable_inv_invSqSum hm hK hZ)
        (ae_of_all _ fun x => inv_nonneg.2 (invSqSum_nonneg _))]
  rw [h1, h2, ← ENNReal.ofReal_mul (integral_nonneg fun x => invSqSum_nonneg _)] at hprod
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hprod

/-- **The negative spread, inverse moments**, from `IndexedSpectralConvexityStatement` and
Prékopa's theorem: for every `q > 0` there is `C_q` (depending only on `q`) with
`E U^{-q} ≤ C_q (E U)^{-q}` under every normalized sector law. -/
theorem negativeSpread_inverse_moment_of_prekopa
    (hconv : IndexedSpectralConvexityStatement) (hP : BlockBand.External.Prekopa.SourceContract)
    (q : ℝ) (hq : 0 < q) : ∃ C : ℝ, ∀ (m : ℕ) (t : ℝ≥0)
    (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t → K.IsHermitian →
    0 < (sectorMass m t K ℓ).re →
      (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
        ENNReal.ofReal C * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹ := by
  set p : ℝ := 2 * q with hpdef
  have hp : 0 < p := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨p * (2 * ((2 / Real.log 2) ^ p * Real.Gamma p)) * (64 * Real.exp 8) ^ q, ?_⟩
  intro m t K ℓ ht hK hZ
  have hprob := isProbabilityMeasure_sectorLaw hK hZ
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : ∀ x, sectorInvSq K x = 0 := fun x => by simp [sectorInvSq]
    simp [h0, Real.zero_rpow hq.ne']
  set μ := sectorLaw m t K ℓ with hμ
  set V : (HermCoord m → ℝ) → ℝ := fun x => invSqSum (orderedEigs K x) with hVdef
  set W : (HermCoord m → ℝ) → ℝ := fun x => (invSqSum (orderedEigs K x))⁻¹ with hWdef
  set f : (HermCoord m → ℝ) → ℝ := fun x => spreadF (orderedEigs K x) with hfdef
  have hVint : Integrable V μ := integrable_invSqSum hK hZ
  have hWint : Integrable W μ := integrable_inv_invSqSum hm hK hZ
  have hch := ae_mem_chamber hconv ht hK hZ
  have hVpos : ∀ᵐ x ∂μ, 0 < V x :=
    hch.mono fun x hx => invSqSum_pos (ne_zero_of_mem_chamber hx) ⟨0, hm⟩
  have hWpos : ∀ᵐ x ∂μ, 0 < W x := hVpos.mono fun x hx => inv_pos.2 hx
  have hUV : ∀ᵐ x ∂μ, sectorInvSq K x = V x :=
    (ae_det_ne_zero_sectorLaw ht).mono fun x h => (invSqSum_orderedEigs hK h).symm
  have hfm : Measurable f := measurable_spreadF.comp (measurable_orderedEigs K)
  have hfW : ∀ x, f x ^ 2 = W x := fun x => spreadF_sq _
  set A := ∫ x, V x ∂μ with hAdef
  have hA : 0 < A := by
    rcases (integral_nonneg (fun x => invSqSum_nonneg _) : 0 ≤ A).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := (integral_eq_zero_iff_of_nonneg (fun x => invSqSum_nonneg _) hVint).1 h.symm
      obtain ⟨x, hx1, hx2⟩ := (hVpos.and h0).exists
      simp only [Pi.zero_apply] at hx2
      linarith
  have hf2 : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 (by simpa only [hfW] using hWint)
  have hfint : Integrable f μ := hf2.integrable one_le_two
  set α := ∫ x, f x ∂μ with hαdef
  have hα : 0 < α := by
    rcases (integral_nonneg (fun x => spreadF_nonneg _) : 0 ≤ α).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := (integral_eq_zero_iff_of_nonneg (fun x => spreadF_nonneg _) hfint).1 h.symm
      obtain ⟨x, hx1, hx2⟩ := (hWpos.and h0).exists
      simp only [Pi.zero_apply] at hx2
      have := hfW x
      change spreadF (orderedEigs K x) ^ 2 = W x at this
      rw [hx2, sq, mul_zero] at this
      linarith
  have hα2 : α ^ 2 ≤ ∫ x, W x ∂μ := by
    have h := variance_nonneg f μ
    rw [variance_eq_sub hf2] at h
    have e : μ[f ^ 2] = ∫ x, W x ∂μ := integral_congr_ae (ae_of_all _ fun x => by
      simp only [Pi.pow_apply, hfW])
    rw [e] at h
    linarith
  have hhalf : μ {x | 2 * α ≤ f x} ≤ ENNReal.ofReal (1 / 2) := by
    have hε : ENNReal.ofReal (2 * α) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    calc μ {x | 2 * α ≤ f x}
        ≤ μ {x | ENNReal.ofReal (2 * α) ≤ ENNReal.ofReal (f x)} :=
          measure_mono fun x hx => ENNReal.ofReal_le_ofReal hx
      _ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal (2 * α) :=
          meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp hfm).aemeasurable hε
            ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (1 / 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hfint (ae_of_all _ fun x => spreadF_nonneg _),
            ← ENNReal.ofReal_div_of_pos (by positivity)]
          congr 1
          rw [← hαdef]
          field_simp
  set ρ := Real.log 2 / (2 * α) with hρdef
  have hρ : 0 < ρ := div_pos hl2 (by positivity)
  have htail : ∀ s ∈ Ioi (0 : ℝ), μ {x | s ≤ f x} * ENNReal.ofReal (s ^ (p - 1)) ≤
      ENNReal.ofReal (2 * Real.exp (-(ρ * s))) * ENNReal.ofReal (s ^ (p - 1)) := fun s hs => by
    gcongr
    exact tail_le_exp hP hconv hm ht hK hZ (by positivity) hhalf hs
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul (μ := μ)
    (ae_of_all _ fun x => spreadF_nonneg (orderedEigs K x)) hfm.aemeasurable hp
  have hmom : ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ ≤
      ENNReal.ofReal (p * (2 * ((1 / ρ) ^ p * Real.Gamma p))) := by
    rw [hlayer, ENNReal.ofReal_mul hp.le, ← lintegral_two_exp_mul_rpow hρ hp]
    exact mul_le_mul_right (setLIntegral_mono (by fun_prop) htail) _
  have hL : ∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂μ =
      ∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ := by
    refine lintegral_congr_ae (hUV.mono fun x h => ?_)
    show ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) = ENNReal.ofReal (f x ^ p)
    rw [h]
    congr 1
    simp only [hfdef, spreadF, hpdef, hVdef]
    rw [Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two,
      Real.sq_sqrt (inv_nonneg.2 (invSqSum_nonneg _))]
  have h1 : ∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂μ = ENNReal.ofReal A := by
    rw [lintegral_congr_ae (hUV.mono fun x h => by rw [h]),
      ofReal_integral_eq_lintegral_ofReal hVint (ae_of_all _ fun x => invSqSum_nonneg _)]
  rw [hL, h1, ENNReal.ofReal_rpow_of_pos hA, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hA q),
    ← ENNReal.ofReal_mul (by positivity)]
  refine hmom.trans (ENNReal.ofReal_le_ofReal ?_)
  have hprodR := integral_mul_integral_inv_le hconv hm ht hK hZ
  have hEW : ∫ x, W x ∂μ ≤ 64 * Real.exp 8 / A := by
    rw [le_div_iff₀ hA]; linarith [mul_comm A (∫ x, W x ∂μ)]
  have hW0 : 0 ≤ ∫ x, W x ∂μ := integral_nonneg fun x => inv_nonneg.2 (invSqSum_nonneg _)
  have hαp : α ^ p ≤ (64 * Real.exp 8) ^ q * (A ^ q)⁻¹ := by
    rw [hpdef, Real.rpow_mul hα.le, Real.rpow_two]
    calc (α ^ 2) ^ q ≤ (∫ x, W x ∂μ) ^ q := Real.rpow_le_rpow (by positivity) hα2 hq.le
      _ ≤ (64 * Real.exp 8 / A) ^ q := Real.rpow_le_rpow hW0 hEW hq.le
      _ = _ := by rw [Real.div_rpow (by positivity) hA.le, div_eq_mul_inv]
  have e : (1 / ρ) ^ p = (2 / Real.log 2) ^ p * α ^ p := by
    rw [← Real.mul_rpow (by positivity) hα.le]
    congr 1
    rw [hρdef]
    field_simp
  rw [e]
  have hG := Real.Gamma_pos_of_pos hp
  calc p * (2 * ((2 / Real.log 2) ^ p * α ^ p * Real.Gamma p))
      = p * (2 * ((2 / Real.log 2) ^ p * Real.Gamma p)) * α ^ p := by ring
    _ ≤ p * (2 * ((2 / Real.log 2) ^ p * Real.Gamma p)) * ((64 * Real.exp 8) ^ q * (A ^ q)⁻¹) :=
        mul_le_mul_of_nonneg_left hαp (by positivity)
    _ = _ := by ring

/-- **The negative spread** (`NegativeSpreadStatement`), from `IndexedSpectralConvexityStatement`
and Prékopa's theorem (1973, Theorem 6). -/
theorem negativeSpread_of_convexity_of_prekopa (hconv : IndexedSpectralConvexityStatement)
    (hP : BlockBand.External.Prekopa.SourceContract) : NegativeSpreadStatement where
  product := negativeSpread_product_of_convexity hconv
  inverse_moment := negativeSpread_inverse_moment_of_prekopa hconv hP

end BlockBand.DeterminantScore.NegativeSpread
