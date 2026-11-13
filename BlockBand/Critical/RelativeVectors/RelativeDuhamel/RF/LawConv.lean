module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Stability

/-!
# Weak continuity of the reference-kernel law in the coefficients

**Setting.** Window `[a, u]`, `a ≤ u`, `s ∈ [a, u]`; `P = driverLaw (dirac ())` on
`DriverSample Unit (RotIdx N)`; matrices carry the Frobenius norm. `canonFlow a u r κ` is the
rotation flow started at `a` with the reflected coefficients `r(a+u−·)`, `κ(a+u−·)`
(`canonFlow_isRotationFlow`), and `refKernelLaw a u s r κ` is the law of
`K_s = (canonFlow a u r κ)_{u−s}ᴴ` (`refKernel`).

**Proof.**
* Uniform convergence of `(rn, κn)` on `[a, u]` gives, for every `η ∈ (0, 1]`, eventually
  `|rn − r| ≤ η²` and `|κn − κ| ≤ η²` entrywise on `[a, u]`, hence `|√rn − √r| ≤ η`
  (`|√x − √y|² ≤ |x − y|`), `|κn − κ| ≤ η`, and the uniform bound `R = R₀ + 1`
  (`R₀` bounds the continuous `(r, κ)` on the compact `[a, u]`). The reflection maps `[a, u]`
  to itself, so these hold for the reflected coefficients.
* The `L²` stability of rotation flows (`lintegral_enorm_sub_sq_le_of_isRotationFlow`) gives
  `E‖𝓝ⁿ_t − 𝓝_t‖² ≤ stabConst N R t · η²`, so the flows converge in `L²(P)` at every time
  (`tendsto_lintegral_canonFlow_sub`).
* `‖Aᴴ − Bᴴ‖ = ‖A − B‖`, so the kernels converge in `L²`, hence in probability (Chebyshev,
  `meas_ge_le_lintegral_div`).
* For bounded continuous `φ`: along every subsequence there is an a.e. convergent further
  subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`), along which
  `∫ φ(Kⁿ) dP → ∫ φ(K) dP` by dominated convergence; `tendsto_of_subseq_tendsto` concludes.
  No Lipschitz property of `φ` is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow)

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

variable {N : ℕ}

/-- `|√x − √y| ≤ η` whenever `|x − y| ≤ η²` (`x, y, η ≥ 0`). -/
private theorem abs_sqrt_sub_sqrt_le_of_abs_sub_le {x y η : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hη : 0 ≤ η)
    (h : |x - y| ≤ η ^ 2) : |Real.sqrt x - Real.sqrt y| ≤ η := by
  have e : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
    calc x - y = Real.sqrt x ^ 2 - Real.sqrt y ^ 2 := by
          rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
      _ = _ := by ring
  have h1 : |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt x + Real.sqrt y :=
    (abs_sub _ _).trans (by rw [abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _)])
  have h2 : |Real.sqrt x - Real.sqrt y| ^ 2 ≤ |x - y| := by
    rw [e, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), sq]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hη two_ne_zero).1 (h2.trans h)

/-- The time-reflected coefficients of admissible coefficients are admissible. -/
private theorem admissible_reflect {a u : ℝ} {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    (h : Admissible a u r κ) : Admissible a u (reflectRate a u r) (reflectDamp a u κ) :=
  ⟨continuousOn_reflect h.1, continuousOn_reflect h.2.1, fun _ k l => h.2.2.1 _ k l,
    fun _ k l => h.2.2.2.1 _ k l, fun _ k => h.2.2.2.2 _ k⟩

/-- Admissible coefficients are bounded on `[a, u]`. -/
private theorem exists_admissible_le {a u : ℝ} {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    (h : Admissible a u r κ) :
    ∃ R₀, 0 ≤ R₀ ∧ ∀ x ∈ Icc a u, (∀ k l, r x k l ≤ R₀) ∧ ∀ k, κ x k ≤ R₀ := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := a) (b := u)).exists_bound_of_continuousOn h.1
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := a) (b := u)).exists_bound_of_continuousOn h.2.1
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun x hx => ⟨fun k l => ?_, fun k => ?_⟩⟩
  · have h1 : ‖r x k l‖ ≤ ‖r x‖ := (norm_le_pi_norm (r x k) l).trans (norm_le_pi_norm (r x) k)
    have h2 := hC₁ x hx
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (r x k l), le_max_left (max C₁ C₂) 0, le_max_left C₁ C₂]
  · have h1 : ‖κ x k‖ ≤ ‖κ x‖ := norm_le_pi_norm (κ x) k
    have h2 := hC₂ x hx
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (κ x k), le_max_left (max C₁ C₂) 0, le_max_right C₁ C₂]

/-- Entrywise form of uniform convergence of the coefficients on `[a, u]`. -/
private theorem eventually_coeff_close {a u : ℝ} {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    {rn : ℕ → ℝ → Fin N → Fin N → ℝ} {κn : ℕ → ℝ → Fin N → ℝ}
    (hconv : TendstoUniformlyOn (fun n x => (rn n x, κn n x)) (fun x => (r x, κ x)) atTop
      (Icc a u)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ x ∈ Icc a u,
      (∀ k l, |rn n x k l - r x k l| ≤ δ) ∧ ∀ k, |κn n x k - κ x k| ≤ δ := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv δ hδ] with n hn x hx
  have hd := (hn x hx).le
  rw [Prod.dist_eq] at hd
  refine ⟨fun k l => ?_, fun k => ?_⟩
  · have h1 : dist (r x k l) (rn n x k l) ≤ dist (r x) (rn n x) :=
      (dist_le_pi_dist (r x k) (rn n x k) l).trans (dist_le_pi_dist (r x) (rn n x) k)
    rw [Real.dist_eq, abs_sub_comm] at h1
    linarith [le_max_left (dist (r x) (rn n x)) (dist (κ x) (κn n x))]
  · have h1 : dist (κ x k) (κn n x k) ≤ dist (κ x) (κn n x) := dist_le_pi_dist (κ x) (κn n x) k
    rw [Real.dist_eq, abs_sub_comm] at h1
    linarith [le_max_right (dist (r x) (rn n x)) (dist (κ x) (κn n x))]

/-- **`L²` convergence of the canonical flows** (`L²` stability on the reflected coefficients):
along a uniformly convergent sequence of admissible coefficients on `[a, u]`,
`E‖canonFlow(rn, κn)_t − canonFlow(r, κ)_t‖² → 0` for every `t`. -/
theorem tendsto_lintegral_canonFlow_sub {a u : ℝ} (hau : a ≤ u) {r : ℝ → Fin N → Fin N → ℝ}
    {κ : ℝ → Fin N → ℝ} {rn : ℕ → ℝ → Fin N → Fin N → ℝ} {κn : ℕ → ℝ → Fin N → ℝ}
    (h : Admissible a u r κ) (hn : ∀ n, Admissible a u (rn n) (κn n))
    (hconv : TendstoUniformlyOn (fun n x => (rn n x, κn n x)) (fun x => (r x, κ x)) atTop
      (Icc a u)) (t : ℝ≥0) :
    Tendsto (fun n => ∫⁻ y, ‖canonFlow a u (rn n) (κn n) t y - canonFlow a u r κ t y‖ₑ ^ 2
      ∂driverLaw (κ := RotIdx N) (Measure.dirac ())) atTop (𝓝 0) := by
  obtain ⟨R₀, hR₀, hb⟩ := exists_admissible_le h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  set C := stabConst N (R₀ + 1) t with hCdef
  have hC : 0 ≤ C := stabConst_nonneg N (R₀ + 1) t.2
  set e := ε.toReal with hedef
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεt
  set η := min 1 (Real.sqrt (e / (C + 1))) with hηdef
  have hη0 : 0 < η := lt_min one_pos (Real.sqrt_pos.2 (div_pos he (by linarith)))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηe : C * η ^ 2 ≤ e := by
    have h1 : η ^ 2 ≤ e / (C + 1) := by
      calc η ^ 2 ≤ Real.sqrt (e / (C + 1)) ^ 2 := pow_le_pow_left₀ hη0.le (min_le_right _ _) 2
        _ = e / (C + 1) := Real.sq_sqrt (by positivity)
    calc C * η ^ 2 ≤ C * (e / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC
      _ ≤ e := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  have hη2 : η ^ 2 ≤ η := by nlinarith
  have hη21 : η ^ 2 ≤ 1 := hη2.trans hη1
  filter_upwards [eventually_coeff_close hconv (pow_pos hη0 2)] with n hn'
  have hF := canonFlow_isRotationFlow hau h
  have hFn := canonFlow_isRotationFlow hau (hn n)
  refine (lintegral_enorm_sub_sq_le_of_isRotationFlow (R := R₀ + 1) (ε := η) hau
    (admissible_reflect (hn n)) (admissible_reflect h) (by positivity) ?_ ?_ ?_ ?_ hFn hF t).trans ?_
  · intro x hx k l
    have hy : a + u - x ∈ Icc a u := mapsTo_reflect hx
    have h1 := (hn' _ hy).1 k l
    have h2 := (hb _ hy).1 k l
    simp only [reflectRate]
    exact ⟨by linarith [le_abs_self (rn n (a + u - x) k l - r (a + u - x) k l)], by linarith⟩
  · intro x hx k
    have hy : a + u - x ∈ Icc a u := mapsTo_reflect hx
    have h1 := (hn' _ hy).2 k
    have h2 := (hb _ hy).2 k
    simp only [reflectDamp]
    exact ⟨by linarith [le_abs_self (κn n (a + u - x) k - κ (a + u - x) k)], by linarith⟩
  · intro x hx k l
    have hy : a + u - x ∈ Icc a u := mapsTo_reflect hx
    simp only [reflectRate]
    exact abs_sqrt_sub_sqrt_le_of_abs_sub_le ((hn n).2.2.2.1 _ k l) (h.2.2.2.1 _ k l) hη0.le
      ((hn' _ hy).1 k l)
  · intro x hx k
    have hy : a + u - x ∈ Icc a u := mapsTo_reflect hx
    simp only [reflectDamp]
    exact ((hn' _ hy).2 k).trans hη2
  · rw [← ENNReal.ofReal_toReal hεt]
    exact ENNReal.ofReal_le_ofReal hηe

/-- **Weak continuity of the reference-kernel law in the coefficients.**
Along a sequence of admissible coefficients converging uniformly on `[a, u]`, the laws
`refKernelLaw a u s (rn n) (κn n)` converge to `refKernelLaw a u s r κ` against every bounded
continuous test function. Proof: `L²` convergence of the flows
(`tendsto_lintegral_canonFlow_sub`), hence convergence in probability of the kernels
`K = (𝓝_{u−s})ᴴ` (Chebyshev), hence, along every subsequence, an a.e. convergent further
subsequence and dominated convergence. -/
theorem refKernelLawContinuity (N : ℕ) : RefKernelLawContinuity N := by
  intro a u s hau _ r κ rn κn h hn hconv φ hφ hφb
  obtain ⟨Cφ, hCφ⟩ := hφb
  set P := driverLaw (κ := RotIdx N) (Measure.dirac ()) with hP
  set t : ℝ≥0 := (u - s).toNNReal with ht
  have hF := canonFlow_isRotationFlow hau h
  have hFn := fun n => canonFlow_isRotationFlow hau (hn n)
  have hL2 := tendsto_lintegral_canonFlow_sub hau h hn hconv t
  set K := refKernel u (canonFlow a u r κ) s with hK
  set Kn : ℕ → DriverSample Unit (RotIdx N) → Matrix (Fin N) (Fin N) ℂ :=
    fun n => refKernel u (canonFlow a u (rn n) (κn n)) s with hKn
  have hedist : ∀ n y, edist (Kn n y) (K y) =
      ‖canonFlow a u (rn n) (κn n) t y - canonFlow a u r κ t y‖ₑ := by
    intro n y
    simp only [hKn, hK, refKernel, ht]
    rw [edist_eq_enorm_sub, ← Matrix.conjTranspose_sub, ← ofReal_norm, ← ofReal_norm,
      Matrix.frobenius_norm_conjTranspose]
  have hm : ∀ n, AEMeasurable
      (fun y => ‖canonFlow a u (rn n) (κn n) t y - canonFlow a u r κ t y‖ₑ ^ 2) P := by
    intro n
    have h1 := ((hFn n).1.adapted t).mono
      ((driverAugmented (κ := RotIdx N) (Measure.dirac ())).le t)
    have h2 := (hF.1.adapted t).mono ((driverAugmented (κ := RotIdx N) (Measure.dirac ())).le t)
    exact ((h1.aestronglyMeasurable.sub h2.aestronglyMeasurable).enorm).pow_const 2
  have hmeas : TendstoInMeasure P Kn atTop K := by
    refine tendstoInMeasure_of_ne_top fun δ hδ hδt => ?_
    have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 hδ.ne'
    have hδ2t : δ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hδt
    have hlim := ENNReal.Tendsto.div_const hL2 (Or.inr hδ2)
    rw [ENNReal.zero_div] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun n => ?_
    calc P {y | δ ≤ edist (Kn n y) (K y)} ≤ P {y | δ ^ 2 ≤
          ‖canonFlow a u (rn n) (κn n) t y - canonFlow a u r κ t y‖ₑ ^ 2} := by
          refine measure_mono fun y hy => ?_
          simp only [mem_ofPred_eq, hedist] at hy ⊢
          exact pow_le_pow_left₀ zero_le hy 2
      _ ≤ _ := meas_ge_le_lintegral_div (hm n) hδ2 hδ2t
  have hKm : Measurable K := measurable_refKernel hF s
  have hKnm : ∀ n, Measurable (Kn n) := fun n => measurable_refKernel (hFn n) s
  have hφm := hφ.measurable
  have hI : ∀ n, ∫ M, φ M ∂P.map (Kn n) = ∫ y, φ (Kn n y) ∂P := fun n =>
    integral_map (hKnm n).aemeasurable hφm.aestronglyMeasurable
  have hI0 : ∫ M, φ M ∂P.map K = ∫ y, φ (K y) ∂P :=
    integral_map hKm.aemeasurable hφm.aestronglyMeasurable
  show Tendsto (fun n => ∫ M, φ M ∂P.map (Kn n)) atTop (𝓝 (∫ M, φ M ∂P.map K))
  simp only [hI, hI0]
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, -, hms⟩ := (hmeas.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_integral_of_dominated_convergence (F := fun k y => φ (Kn (ns (ms k)) y))
    (fun _ => Cφ) (fun k => (hφm.comp (hKnm _)).aestronglyMeasurable) (integrable_const Cφ)
    (fun k => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hCφ _) ?_⟩
  filter_upwards [hms] with y hy
  exact (hφ.tendsto (K y)).comp hy

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
