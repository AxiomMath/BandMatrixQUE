module

public import BlockBand.Transmission.Bridge.GueNull
public import BlockBand.Transmission.PassiveCovariance.GaussianIBP

/-!
# Gaussian integration by parts for `gueMeasure`

For the GUE law, `E[A_ab F(A)] = (t/2) E[F_H + iF_K]`, with `F_H`, `F_K` the derivatives of `F`
along the Hermitian directions `E_ab + E_ba` and `i(E_ab - E_ba)`, required only at Hermitian
matrices (`stein_gue`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Transmission.Bridge BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess
open scoped NNReal ComplexConjugate

variable {n : ℕ}

theorem sqrt_half_div (t : ℝ≥0) : (Real.sqrt ((t : ℝ) / 2) : ℂ) / (Real.sqrt 2 : ℂ) = (Real.sqrt t : ℂ) / 2 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
  push_cast
  field_simp
  rw [show ((Real.sqrt 2 : ℂ)) ^ 2 = 2 by rw [pow_two]; exact_mod_cast h2]

theorem gueRaw_add_smul (t : ℝ≥0) (ρ e : (Fin n × Fin n) × Fin 2 → ℝ) (c : ℝ) :
    gueRaw t (ρ + c • e) = gueRaw t ρ + (c : ℂ) • gueRaw t e := by
  ext a b
  simp only [gueRaw, gueSample, circularBrownianCoordinates, Matrix.of_apply, Matrix.add_apply,
    Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, map_div₀,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem update_eq_add (ρ : (Fin n × Fin n) × Fin 2 → ℝ) (j : (Fin n × Fin n) × Fin 2) (s : ℝ) :
    Function.update ρ j s = ρ + (s - ρ j) • Pi.single j 1 := by
  funext v
  by_cases h : v = j
  · subst h; simp
  · simp [h]

/-- The Hermitian direction `E_ab + E_ba`. -/
def hermDir (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 + Matrix.single b a 1
/-- The Hermitian direction `i(E_ab - E_ba)`. -/
def skewDir (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Complex.I • (Matrix.single a b 1 - Matrix.single b a 1)

theorem cbc_single (u : Fin n × Fin n) (k : Fin 2) (v : Fin n × Fin n) :
    circularBrownianCoordinates (Pi.single (u, k) (1 : ℝ)) v =
      (if v = u then (if k = 0 then 1 else Complex.I) else 0) / (Real.sqrt 2 : ℂ) := by
  simp only [circularBrownianCoordinates, Pi.single_apply, Prod.mk.injEq]
  obtain rfl | rfl : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  · by_cases h : v = u <;> simp [h]
  · by_cases h : v = u <;> simp [h]

theorem gueRaw_entry (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) (c d : Fin n) :
    gueRaw t ρ c d = (Real.sqrt ((t : ℝ) / 2) : ℂ) *
      (circularBrownianCoordinates ρ (c, d) + conj (circularBrownianCoordinates ρ (d, c))) := rfl

theorem gueRaw_single0 (t : ℝ≥0) (a b : Fin n) :
    gueRaw t (Pi.single ((a, b), 0) 1) = ((Real.sqrt t : ℂ) / 2) • hermDir a b := by
  rw [← sqrt_half_div]
  ext c d
  rw [gueRaw_entry, cbc_single, cbc_single, Matrix.smul_apply, smul_eq_mul, hermDir,
    Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  simp only [ite_true, map_div₀, Complex.conj_ofReal]
  by_cases h1 : a = c ∧ b = d <;> by_cases h2 : b = c ∧ a = d
  · obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, -⟩ := h2; simp; ring
  · obtain ⟨rfl, rfl⟩ := h1
    have : ¬ (b, a) = (a, b) := by
      intro e; apply h2; simp only [Prod.mk.injEq] at e; tauto
    simp [this, h2]; ring
  · obtain ⟨rfl, rfl⟩ := h2
    have : ¬ (a, b) = (b, a) := by
      intro e; apply h1; simp only [Prod.mk.injEq] at e; tauto
    have h1' : ¬ (b = a ∧ a = b) := fun h => h1 ⟨h.2, h.1⟩
    simp [Prod.mk.injEq, h1, h1']
    ring
  · have e1 : ¬ (c, d) = (a, b) := by
      intro e; apply h1; simp only [Prod.mk.injEq] at e; tauto
    have e2 : ¬ (d, c) = (a, b) := by
      intro e; apply h2; simp only [Prod.mk.injEq] at e; tauto
    simp [e1, e2, h1, h2]

theorem gueRaw_single1 (t : ℝ≥0) (a b : Fin n) :
    gueRaw t (Pi.single ((a, b), 1) 1) = ((Real.sqrt t : ℂ) / 2) • skewDir a b := by
  rw [← sqrt_half_div]
  ext c d
  rw [gueRaw_entry, cbc_single, cbc_single, Matrix.smul_apply, smul_eq_mul, skewDir,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply, smul_eq_mul]
  simp only [one_ne_zero, ite_false, map_div₀, Complex.conj_ofReal]
  by_cases h1 : a = c ∧ b = d <;> by_cases h2 : b = c ∧ a = d
  · obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, -⟩ := h2; simp
    right; ring
  · obtain ⟨rfl, rfl⟩ := h1
    have : ¬ (b, a) = (a, b) := by
      intro e; apply h2; simp only [Prod.mk.injEq] at e; tauto
    simp [this, h2]; ring
  · obtain ⟨rfl, rfl⟩ := h2
    have : ¬ (a, b) = (b, a) := by
      intro e; apply h1; simp only [Prod.mk.injEq] at e; tauto
    have h1' : ¬ (b = a ∧ a = b) := fun h => h1 ⟨h.2, h.1⟩
    simp [Prod.mk.injEq, h1, h1']
    ring
  · have e1 : ¬ (c, d) = (a, b) := by
      intro e; apply h1; simp only [Prod.mk.injEq] at e; tauto
    have e2 : ¬ (d, c) = (a, b) := by
      intro e; apply h2; simp only [Prod.mk.injEq] at e; tauto
    simp [e1, e2, h1, h2]

theorem hermDir_comm (a b : Fin n) : hermDir b a = hermDir a b := by
  rw [hermDir, hermDir, add_comm]

theorem skewDir_comm (a b : Fin n) : skewDir b a = -skewDir a b := by
  rw [skewDir, skewDir, ← smul_neg, neg_sub]

theorem gueRaw_apply_ab (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) (a b : Fin n) :
    gueRaw t ρ a b = ((Real.sqrt t : ℂ) / 2) * ((ρ ((a, b), 0) : ℂ) + ρ ((b, a), 0)) +
      Complex.I * (((Real.sqrt t : ℂ) / 2) * ((ρ ((a, b), 1) : ℂ) - ρ ((b, a), 1))) := by
  rw [gueRaw_entry, ← sqrt_half_div]
  simp only [circularBrownianCoordinates, map_div₀, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  field_simp
  ring

/-- Directional derivative of `F ∘ gueRaw` in one real coordinate. -/
theorem coord_deriv (t : ℝ≥0) (j : (Fin n × Fin n) × Fin 2) (D : Matrix (Fin n) (Fin n) ℂ)
    (k : ℝ) (hD : gueRaw t (Pi.single j 1) = (k : ℂ) • D) (F FD : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (ρ : (Fin n × Fin n) × Fin 2 → ℝ)
    (hFD : HasDerivAt (fun s : ℝ => F (gueRaw t ρ + (s : ℂ) • D)) (FD (gueRaw t ρ)) 0) :
    HasDerivAt (fun s => F (gueRaw t (Function.update ρ j s))) ((k : ℂ) * FD (gueRaw t ρ))
      (ρ j) := by
  have hin : HasDerivAt (fun s : ℝ => (s - ρ j) * k) k (ρ j) := by
    simpa using ((hasDerivAt_id (ρ j)).sub_const (ρ j)).mul_const k
  have hout : HasDerivAt (fun u : ℝ => F (gueRaw t ρ + (u : ℂ) • D)) (FD (gueRaw t ρ))
      ((ρ j - ρ j) * k) := by
    rw [sub_self, zero_mul]; exact hFD
  have h := hout.scomp (ρ j) hin
  rw [Complex.real_smul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show F (gueRaw t (Function.update ρ j s)) = F (gueRaw t ρ + (((s - ρ j) * k : ℝ) : ℂ) • D)
  rw [update_eq_add, gueRaw_add_smul, hD, smul_smul]
  push_cast; ring_nf

/-- Every sample `gueRaw t ρ` is Hermitian. -/
theorem gueRaw_isHermitian (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) :
    (gueRaw t ρ).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, gueRaw_entry, star_mul', star_add, Complex.star_def,
    Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- **Gaussian IBP for the `gueMeasure`**:
`E[A_ab F(A)] = (t/2)E[F_H + iF_K]`, with
`F_H`, `F_K` the real derivatives of `F` along `E_ab + E_ba` and `i(E_ab - E_ba)`, needed only at
Hermitian `A` (the support of the law).
-/
theorem stein_gue (t : ℝ≥0) (a b : Fin n) (F FH FK : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hH : ∀ A, A.IsHermitian → HasDerivAt (fun s : ℝ => F (A + (s : ℂ) • hermDir a b)) (FH A) 0)
    (hK : ∀ A, A.IsHermitian → HasDerivAt (fun s : ℝ => F (A + (s : ℂ) • skewDir a b)) (FK A) 0)
    (hF : MemLp F 2 (gueMeasure (Fin n) t)) (hFH : Integrable FH (gueMeasure (Fin n) t))
    (hFK : Integrable FK (gueMeasure (Fin n) t)) :
    ∫ A, A a b * F A ∂gueMeasure (Fin n) t =
      ((t : ℂ) / 2) * ∫ A, FH A + Complex.I * FK A ∂gueMeasure (Fin n) t := by
  have hm := measurable_gueRaw n t
  have hsum : Integrable (fun A => FH A + Complex.I * FK A) (gueMeasure (Fin n) t) :=
    hFH.add (hFK.const_mul _)
  have hmeasL : AEStronglyMeasurable (fun A : Matrix (Fin n) (Fin n) ℂ => A a b * F A)
      (gueMeasure (Fin n) t) :=
    (Matrix.measurable_apply.aestronglyMeasurable).mul hF.aestronglyMeasurable
  rw [gueMeasure_eq_map] at hF hFH hFK hsum hmeasL ⊢
  set μ := Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1
  rw [integral_map hm.aemeasurable hmeasL, integral_map hm.aemeasurable hsum.aestronglyMeasurable]
  have hG : MemLp (fun ρ => F (gueRaw t ρ)) 2 μ := hF.comp_of_map hm.aemeasurable
  have hGi : Integrable (fun ρ => F (gueRaw t ρ)) μ := hG.integrable one_le_two
  have hco : ∀ j, Integrable (fun ρ : (Fin n × Fin n) × Fin 2 → ℝ => (ρ j : ℂ) * F (gueRaw t ρ)) μ := by
    intro j
    have hj : MemLp (fun ρ : (Fin n × Fin n) × Fin 2 → ℝ => ((ρ j : ℝ) : ℂ)) 2 μ :=
      (((memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
        (measurePreserving_eval _ j))).ofReal
    exact hj.integrable_mul hG
  have hFH' : Integrable (fun ρ => FH (gueRaw t ρ)) μ := hFH.comp_measurable hm
  have hFK' : Integrable (fun ρ => FK (gueRaw t ρ)) μ := hFK.comp_measurable hm
  have st : ∀ (j : (Fin n × Fin n) × Fin 2) (D : Matrix (Fin n) (Fin n) ℂ) (k : ℝ)
      (FD : Matrix (Fin n) (Fin n) ℂ → ℂ), gueRaw t (Pi.single j 1) = (k : ℂ) • D →
      (∀ A, A.IsHermitian → HasDerivAt (fun s : ℝ => F (A + (s : ℂ) • D)) (FD A) 0) →
      Integrable (fun ρ => FD (gueRaw t ρ)) μ →
      ∫ ρ, (ρ j : ℂ) * F (gueRaw t ρ) ∂μ = (k : ℂ) * ∫ ρ, FD (gueRaw t ρ) ∂μ := by
    intro j D k FD hD hFD hint
    have := stein_pi (fun _ => (1 : ℝ≥0)) j (fun ρ => F (gueRaw t ρ))
      (fun ρ => (k : ℂ) * FD (gueRaw t ρ)) (fun ρ => coord_deriv t j D k hD F FD ρ (hFD _ (gueRaw_isHermitian t ρ))) hGi
      (hint.const_mul _) (hco j)
    rw [this, integral_const_mul]; simp only [NNReal.coe_one, Complex.ofReal_one, one_mul]
    rfl
  set c : ℝ := Real.sqrt t / 2
  have hc : ((Real.sqrt t : ℂ) / 2) = (c : ℂ) := by simp only [c]; push_cast; ring
  have s1 := st ((a, b), 0) (hermDir a b) c FH (by rw [gueRaw_single0, hc]) hH hFH'
  have s2 := st ((b, a), 0) (hermDir a b) c FH (by rw [gueRaw_single0, hermDir_comm, hc]) hH hFH'
  have s3 := st ((a, b), 1) (skewDir a b) c FK (by rw [gueRaw_single1, hc]) hK hFK'
  have s4 := st ((b, a), 1) (skewDir a b) (-c) FK
    (by rw [gueRaw_single1, skewDir_comm, hc]; push_cast; rw [smul_neg, neg_smul]) hK hFK'
  simp only [gueRaw_apply_ab]
  have hsplit : (fun ρ : (Fin n × Fin n) × Fin 2 → ℝ =>
      (((Real.sqrt t : ℂ) / 2) * ((ρ ((a, b), 0) : ℂ) + ρ ((b, a), 0)) +
        Complex.I * (((Real.sqrt t : ℂ) / 2) * ((ρ ((a, b), 1) : ℂ) - ρ ((b, a), 1)))) *
        F (gueRaw t ρ)) = fun ρ =>
      (c : ℂ) * ((ρ ((a, b), 0) : ℂ) * F (gueRaw t ρ)) + (c : ℂ) * ((ρ ((b, a), 0) : ℂ) * F (gueRaw t ρ)) +
        (Complex.I * c) * ((ρ ((a, b), 1) : ℂ) * F (gueRaw t ρ)) -
          (Complex.I * c) * ((ρ ((b, a), 1) : ℂ) * F (gueRaw t ρ)) := by
    funext ρ; rw [hc]; ring
  rw [hsplit, integral_sub, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, s1, s2, s3, s4,
    integral_add hFH' (hFK'.const_mul _), integral_const_mul]
  · have hct : (c : ℂ) * c = (t : ℂ) / 4 := by
      have : (c : ℝ) * c = t / 4 := by
        simp only [c]; rw [div_mul_div_comm, Real.mul_self_sqrt (NNReal.coe_nonneg t)]; ring
      have h' : ((c * c : ℝ) : ℂ) = ((t / 4 : ℝ) : ℂ) := by rw [this]
      push_cast at h'; rw [h']
    push_cast
    linear_combination (2 * ∫ ρ, FH (gueRaw t ρ) ∂μ + 2 * Complex.I * ∫ ρ, FK (gueRaw t ρ) ∂μ) * hct
  all_goals first
    | exact (hco _).const_mul _
    | exact ((hco _).const_mul _).add ((hco _).const_mul _)
    | exact (((hco _).const_mul _).add ((hco _).const_mul _)).add ((hco _).const_mul _)

end BlockBand.Transmission.PassiveCovariance
