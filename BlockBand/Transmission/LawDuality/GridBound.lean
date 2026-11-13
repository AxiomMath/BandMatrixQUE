module

public import BlockBand.Transmission.LawDuality.GridMeas

/-!
# The strip estimate, bounds: mass-linear domination of the strip integrands

With the forward time clamped to `[a₀, t]` (`clampT a₀ t s = max a₀ (min s t)`), the mean mass
is bounded uniformly in `s` (`exists_mass_bound`, from `HasLocalMassBound`), and on
`StaysIn N X Y τ M ε`:
* `|dualInteg ν v ω'| ≤ genC·ν[0,1] + C_k p(M+1)`, `|fwdInteg u ν v ω'| ≤ genC·ν[0,1] + C_h p(M+1)`
  (`abs_dualInteg_le`, `abs_fwdInteg_le`; `genC` the sum of the `genMass` coefficients);
* `0 ≤ R_v1{v<τ} ≤ p(M+1)` (`totalInd_mem`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- The clamp `max a₀ (min s t)`. -/
def clampT (a0 t s : ℝ) : ℝ := max a0 (min s t)

theorem clampT_mem {a0 t : ℝ} (hat : a0 ≤ t) (s : ℝ) : clampT a0 t s ∈ Icc a0 t :=
  ⟨le_max_left _ _, max_le hat (min_le_right _ _)⟩

theorem clampT_of_mem {a0 t s : ℝ} (hs : s ∈ Icc a0 t) : clampT a0 t s = s := by
  unfold clampT; rw [min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clampT (a0 t : ℝ) : Continuous (clampT a0 t) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The forward process at the clamped time is jointly measurable. -/
theorem measurable_muClamp {Ω : Type*} [MeasurableSpace Ω] {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
    {a0 t : ℝ} (ha0 : 0 < a0) : Measurable fun q : ℝ × Ω => μ (clampT a0 t q.1) q.2 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun s ω => μ (clampT a0 t s) ω)
    (fun ω => (hcont ω).comp_continuous (continuous_clampT a0 t)
      fun _ => lt_of_lt_of_le ha0 (le_max_left _ _))
    fun _ => hmeas _ (lt_of_lt_of_le ha0 (le_max_left _ _))

/-- **Uniform mean-mass bound at clamped times.** -/
theorem exists_mass_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hmeas : ∀ t, 0 < t → Measurable (μ t))
    (hmass : HasLocalMassBound P μ) {a0 t : ℝ} (ha0 : 0 < a0) (hat : a0 ≤ t) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ s, Integrable (fun ω => (μ (clampT a0 t s) ω : Measure unitInterval).real univ) P ∧
      ∫ ω, (μ (clampT a0 t s) ω : Measure unitInterval).real univ ∂P ≤ Cm := by
  obtain ⟨C, hC⟩ := hmass a0 t ha0
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  have hc := clampT_mem hat s
  have hb := hC _ hc
  have hm : Measurable fun ω => (μ (clampT a0 t s) ω : Measure unitInterval).real univ :=
    measurable_mass.comp (hmeas _ (lt_of_lt_of_le ha0 hc.1))
  have e : ∀ ω, ENNReal.ofReal ((μ (clampT a0 t s) ω : Measure unitInterval).real univ) =
      (μ (clampT a0 t s) ω : Measure unitInterval) univ := fun ω =>
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hlt : ∫⁻ ω, (μ (clampT a0 t s) ω : Measure unitInterval) univ ∂P < ⊤ :=
    lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal measureReal_nonneg, e]
    exact hlt
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => measureReal_nonneg)
      hm.aestronglyMeasurable]
    simp_rw [e]
    exact (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) (hb.trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))))

/-- The sum of the `genMass` coefficients. -/
def genC (D0 : ℝ) (p : ℕ) (M ε : ℝ) : ℝ :=
  ∑ j ∈ Finset.range p, |D0| / 2 * ((6 * ((j + 1 : ℕ) : ℝ) + 8 * ((j + 1 : ℕ) : ℝ) ^ 2) *
    ((1 + M) ^ 2 / ε ^ 2))

theorem sum_genMass_eq (D0 : ℝ) (p : ℕ) (M ε : ℝ) (ν : FiniteMeasure unitInterval) :
    ∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν =
      genC D0 p M ε * (ν : Measure unitInterval).real univ := by
  unfold genC genMass; rw [Finset.sum_mul]

theorem genC_nonneg (D0 : ℝ) (p : ℕ) (M ε : ℝ) : 0 ≤ genC D0 p M ε :=
  Finset.sum_nonneg fun j _ => by positivity

section Bounds

variable {Ω : Type*} {p : ℕ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {τ : Ω → WithTop ℝ≥0}
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  (hstart : ∀ ω, N 0 ω = p) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
  (hU : StaysIn N X Y τ M ε)
include hpath hstart hM hε hε1 hU

omit hε1 in
theorem totalInd_mem (ω : Ω) (v : ℝ) :
    0 ≤ dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) * killInd (τ ω) v ∧
      dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) * killInd (τ ω) v ≤
        p * (M + 1) := by
  have hR0 := dualTotal_nonneg (hpath ω) v.toNNReal
  have hpM : 0 ≤ (p : ℝ) * (M + 1) := by positivity
  unfold killInd
  split_ifs with h1
  · refine ⟨by simpa using hR0, ?_⟩
    have hN : N v.toNNReal ω ≤ p := hstart ω ▸ (hpath ω).antitone zero_le
    rw [mul_one]
    calc dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω)
        ≤ ∑ _i ∈ Finset.range (N v.toNNReal ω), (M + 1) := Finset.sum_le_sum fun i hi => by
          obtain ⟨a, b⟩ := hU ω _ h1.le i (Finset.mem_range.1 hi)
          linarith [hε]
      _ = (N v.toNNReal ω : ℝ) * (M + 1) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ p * (M + 1) := mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by linarith)
  · simp [hpM]

theorem abs_dualInteg_le (D0 : ℝ) {k : ℝ → ℝ} (hk0 : ∀ v, 0 ≤ k v) {Ck : ℝ}
    (hkC : ∀ v, k v ≤ Ck) (ν : FiniteMeasure unitInterval) (v : ℝ) (ω : Ω) :
    |dualInteg D0 k N X Y τ ν v ω| ≤
      genC D0 p M ε * (ν : Measure unitInterval).real univ + Ck * (p * (M + 1)) := by
  unfold dualInteg
  have hK := killFac_mem (τ := τ) (hpath ω) hk0 v
  have hG := abs_genStop_le hpath hstart hM hε hε1 hU D0 ν ω v
  rw [sum_genMass_eq] at hG
  have hD := abs_killDer_le hpath hstart hM hε hU hk0 hkC ω v
  have hF := abs_pathRatio_le (hpath ω) ν (stopAt τ v.toNNReal ω)
  have hF' : |ratioStop ν N X Y τ v ω| ≤ 1 := hF
  calc _ ≤ |killFac k N X Y τ v ω * genStop D0 ν N X Y τ v ω| +
        |ratioStop ν N X Y τ v ω * killDer k N X Y τ v ω| := abs_add_le _ _
    _ ≤ 1 * (genC D0 p M ε * (ν : Measure unitInterval).real univ) + 1 * (Ck * (p * (M + 1))) := by
      rw [abs_mul, abs_mul, abs_of_pos hK.1]
      exact add_le_add (mul_le_mul hK.2 hG (abs_nonneg _) zero_le_one)
        (mul_le_mul hF' hD (abs_nonneg _) zero_le_one)
    _ = _ := by ring

theorem abs_fwdInteg_le (D0 E : ℝ) (κ : ℝ → ℝ) {k : ℝ → ℝ} (hk0 : ∀ v, 0 ≤ k v) {Ch : ℝ}
    (hhC : ∀ u, |absorptionRate E κ u| ≤ Ch) (u : ℝ) (ν : FiniteMeasure unitInterval)
    (v : ℝ) (ω : Ω) :
    |fwdInteg D0 E κ k N X Y τ u ν v ω| ≤
      genC D0 p M ε * (ν : Measure unitInterval).real univ + Ch * (p * (M + 1)) := by
  unfold fwdInteg
  have hK := killFac_mem (τ := τ) (hpath ω) hk0 v
  have hR := totalInd_mem hpath hstart hM hε hU ω v
  have hF := abs_pathRatio_le (hpath ω) ν v.toNNReal
  have hCh : 0 ≤ Ch := (abs_nonneg _).trans (hhC 0)
  have hm : 0 ≤ (ν : Measure unitInterval).real univ := measureReal_nonneg
  have hG : |pathGen D0 ν N X Y v.toNNReal ω * killInd (τ ω) v| ≤
      genC D0 p M ε * (ν : Measure unitInterval).real univ := by
    unfold killInd
    split_ifs with h1
    · rw [mul_one, ← sum_genMass_eq]
      exact abs_pathGen_le hpath hstart hM hε hε1 hU D0 ν ω h1.le
    · simpa using mul_nonneg (genC_nonneg D0 p M ε) hm
  have h2 : |absorptionRate E κ u * (dualTotal (N v.toNNReal ω) (X v.toNNReal ω)
      (Y v.toNNReal ω) * killInd (τ ω) v) * pathRatio ν N X Y v.toNNReal ω| ≤
        Ch * (p * (M + 1)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hR.1]
    calc _ ≤ Ch * (p * (M + 1)) * 1 := mul_le_mul (mul_le_mul (hhC u) hR.2 hR.1 hCh) hF
          (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  rw [abs_mul, abs_of_pos hK.1]
  calc _ ≤ 1 * (genC D0 p M ε * (ν : Measure unitInterval).real univ + Ch * (p * (M + 1))) :=
        mul_le_mul hK.2 ((abs_sub _ _).trans (add_le_add hG h2)) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

end Bounds

end BlockBand.Transmission.LawDuality
