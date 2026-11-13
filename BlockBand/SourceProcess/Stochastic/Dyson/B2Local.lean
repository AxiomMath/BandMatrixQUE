module

public import BlockBand.SourceProcess.Stochastic.Dyson.B2Path

/-!
# Dyson Brownian motion: compensated components and their bounds)

With `Y_u = hermVec(F + G_{s+u})` and `X_u = dysonState(F + G_{s+u})`:
* `locComp_stateFn`: the compensated `stateFn k` process is the contract's
  `smCompensated X b k`;
* `locComp_add`, `two_mul_target`: on non-collision samples, the compensated process of
  `ψ_k + ψ_l` is the sum, and polarization expresses the bracket-compensated product
  `M_k M_l - ∫ a_kl` through three bracket-compensated squares;
* `dom_single`, `hdom_single`, `hdom_pair`: bounds up to `dysonRho n` (hypothesis `hdom` of
  `localized_hasMM`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- Coordinates path. -/
def Ypath (N : ℕ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s u : ℝ≥0) (ω : Ω) : Fin (N * N) → ℝ := hermVec N (F ω + G (s + u) ω)

/-- State path. -/
def Xpath (N : ℕ) (q : Fin N → ℂ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s u : ℝ≥0) (ω : Ω) : Fin (N + N) → ℝ :=
  dysonState N q (F ω + G (s + u) ω)

/-- Drift of component `k` in coordinates. -/
def driftK (N : ℕ) (q : Fin N → ℂ) (k : Fin (N + N)) (y : Fin (N * N) → ℝ) : ℝ :=
  dysonStateDrift N (dysonState N q (vecHerm N y)) k

/-- Covariance entry in coordinates. -/
def covKL (N : ℕ) (q : Fin N → ℂ) (k l : Fin (N + N)) (y : Fin (N * N) → ℝ) : ℝ :=
  dysonStateCov N (dysonState N q (vecHerm N y)) k l

theorem vecHerm_Ypath (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (s u : ℝ≥0) (ω : Ω) : vecHerm N (Ypath N G F s u ω) = F ω + G (s + u) ω :=
  vecHerm_hermVec (herm_add hG hFh _ ω)

theorem locComp_stateFn (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (q : Fin N → ℂ) (s : ℝ≥0) (k : Fin (N + N)) (t : ℝ≥0) (ω : Ω) :
    locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) t ω =
      smCompensated (Xpath N q G F s) (fun u ω => dysonStateDrift N (Xpath N q G F s u ω)) k t ω := by
  simp only [locComp, smCompensated, stateFn, driftK, Xpath, vecHerm_Ypath hG hFh]

theorem integrableOn_driftK (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) (k : Fin (N + N))
    (t : ℝ≥0) :
    IntegrableOn (fun r : ℝ => driftK N q k (Ypath N G F s r.toNNReal ω)) (Ioc 0 t) := by
  simp only [driftK, vecHerm_Ypath hG hFh]
  exact ((continuous_apply k).comp (continuous_drift_path hG hs hω q)).integrableOn_Ioc

theorem integrableOn_covKL (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ)
    (k l : Fin (N + N)) (t : ℝ≥0) :
    IntegrableOn (fun r : ℝ => covKL N q k l (Ypath N G F s r.toNNReal ω)) (Ioc 0 t) := by
  simp only [covKL, vecHerm_Ypath hG hFh]
  exact ((continuous_apply l).comp ((continuous_apply k).comp
    (continuous_cov_path hG hs hω q))).integrableOn_Ioc

theorem locComp_add (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ)
    (k l : Fin (N + N)) (t : ℝ≥0) :
    locComp (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
        (fun y => driftK N q k y + driftK N q l y) t ω =
      locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) t ω +
        locComp (Ypath N G F s) (stateFn N q l) (driftK N q l) t ω := by
  simp only [locComp]
  rw [integral_add (integrableOn_driftK hG hFh hs hω q k t) (integrableOn_driftK hG hFh hs hω q l t)]
  ring

/-- **Polarization** of the bracket-compensated product. -/
theorem two_mul_target (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ)
    (k l : Fin (N + N)) (t : ℝ≥0) :
    2 * (locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) t ω *
          locComp (Ypath N G F s) (stateFn N q l) (driftK N q l) t ω -
        ∫ r in Ioc (0 : ℝ) t, covKL N q k l (Ypath N G F s r.toNNReal ω)) =
      locSq (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
          (fun y => driftK N q k y + driftK N q l y)
          (fun y => covKL N q k k y + 2 * covKL N q k l y + covKL N q l l y) t ω -
        locSq (Ypath N G F s) (stateFn N q k) (driftK N q k) (covKL N q k k) t ω -
        locSq (Ypath N G F s) (stateFn N q l) (driftK N q l) (covKL N q l l) t ω := by
  have i1 := integrableOn_covKL hG hFh hs hω q k k t
  have i2 := integrableOn_covKL hG hFh hs hω q k l t
  have i3 := integrableOn_covKL hG hFh hs hω q l l t
  simp only [locSq, locComp_add hG hFh hs hω q k l t]
  rw [integral_add (f := fun r : ℝ => covKL N q k k (Ypath N G F s r.toNNReal ω) +
      2 * covKL N q k l (Ypath N G F s r.toNNReal ω))
      (g := fun r : ℝ => covKL N q l l (Ypath N G F s r.toNNReal ω)) (i1.add (i2.const_mul 2)) i3,
    integral_add (f := fun r : ℝ => covKL N q k k (Ypath N G F s r.toNNReal ω))
      (g := fun r : ℝ => 2 * covKL N q k l (Ypath N G F s r.toNNReal ω)) i1 (i2.const_mul 2),
    integral_const_mul]
  ring

/-- Drift constant. -/
def kCd (N : ℕ) (q : Fin N → ℂ) (n : ℕ) : ℝ :=
  1 / (1 / ((n : ℝ) + 1)) + kB N q / (1 / ((n : ℝ) + 1)) ^ 2

/-- Covariance constant. -/
def kCc (N : ℕ) (q : Fin N → ℂ) (n : ℕ) : ℝ :=
  1 / N + 2 * kB N q ^ 2 / (1 / ((n : ℝ) + 1)) ^ 2

/-- Compensated-process constant. -/
def kK (N : ℕ) (q : Fin N → ℂ) (n : ℕ) (t : ℝ≥0) : ℝ :=
  N * ((n : ℝ) + 1) + kB N q + kCd N q n * t

theorem kCd_nonneg (q : Fin N → ℂ) (n : ℕ) : 0 ≤ kCd N q n := by
  unfold kCd; have := kB_nonneg q; positivity

theorem kCc_nonneg (q : Fin N → ℂ) (n : ℕ) : 0 ≤ kCc N q n := by
  unfold kCc; have := kB_nonneg q; positivity

/-- **Domination up to `dysonRho n`** for a single component. -/
theorem dom_single (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) {ω : Ω} (hω : NoCollision N G F ω) (q : Fin N → ℂ) (n : ℕ)
    {t v : ℝ≥0} (hvt : v ≤ t) (hv : (v : WithTop ℝ≥0) ≤ dysonRho G F s n ω) (k : Fin (N + N)) :
    |locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) v ω| ≤ kK N q n t ∧
      ∀ l, |∫ r in Ioc (0 : ℝ) v, covKL N q k l (Ypath N G F s r.toNNReal ω)| ≤ kCc N q n * t := by
  obtain ⟨b1, b2, b3⟩ := state_bounds hG hs hFh hω q n hv
  have hvt' : (v : ℝ) ≤ t := by exact_mod_cast hvt
  refine ⟨?_, fun l => ?_⟩
  · have hint : |∫ r in Ioc (0 : ℝ) v, driftK N q k (Ypath N G F s r.toNNReal ω)| ≤
        kCd N q n * t := by
      refine (abs_setIntegral_Ioc_le v fun r hr => ?_).trans
        (mul_le_mul_of_nonneg_left hvt' (kCd_nonneg q n))
      simp only [driftK, vecHerm_Ypath hG hFh]
      exact b2 r hr k
    have hX := b1 k
    simp only [locComp, stateFn, vecHerm_Ypath hG hFh] at hint ⊢
    unfold kK
    calc _ ≤ |dysonState N q (F ω + G (s + v) ω) k - dysonState N q (F ω + G (s + 0) ω) k| +
          |∫ r in Ioc (0 : ℝ) v, driftK N q k (Ypath N G F s r.toNNReal ω)| := abs_sub _ _
      _ ≤ _ := by
          simp only [driftK, vecHerm_Ypath hG hFh] at hint ⊢
          linarith
  · refine (abs_setIntegral_Ioc_le v fun r hr => ?_).trans
      (mul_le_mul_of_nonneg_left hvt' (kCc_nonneg q n))
    simp only [covKL, vecHerm_Ypath hG hFh]
    exact b3 r hr k l

/-- The `hdom` hypothesis of `localized_hasMM` for a single component. -/
theorem hdom_single (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) (hb1 : ∀ᵐ ω ∂Q, NoCollision N G F ω) (q : Fin N → ℂ) (n : ℕ)
    (k : Fin (N + N)) (t : ℝ≥0) :
    ∃ C, ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ dysonRho G F s n ω →
      |locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) v ω| ≤ C ∧
      |locSq (Ypath N G F s) (stateFn N q k) (driftK N q k) (covKL N q k k) v ω| ≤ C := by
  refine ⟨kK N q n t + kK N q n t ^ 2 + kCc N q n * t, ?_⟩
  filter_upwards [hb1] with ω hω v hvt hv
  obtain ⟨h1, h2⟩ := dom_single hG hFh hs hω q n hvt hv k
  have hK : 0 ≤ kK N q n t := (abs_nonneg _).trans h1
  have hc := h2 k
  have hcc : 0 ≤ kCc N q n * t := (abs_nonneg _).trans hc
  refine ⟨by nlinarith, ?_⟩
  unfold locSq
  calc _ ≤ |locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) v ω *
        locComp (Ypath N G F s) (stateFn N q k) (driftK N q k) v ω| +
      |∫ r in Ioc (0 : ℝ) v, covKL N q k k (Ypath N G F s r.toNNReal ω)| := abs_sub _ _
    _ ≤ kK N q n t ^ 2 + kCc N q n * t := by
        rw [abs_mul, sq]
        exact add_le_add (mul_le_mul h1 h1 (abs_nonneg _) hK) hc
    _ ≤ _ := by nlinarith

/-- The `hdom` hypothesis of `localized_hasMM` for a sum of two components. -/
theorem hdom_pair (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : 0 < s) (hb1 : ∀ᵐ ω ∂Q, NoCollision N G F ω) (q : Fin N → ℂ) (n : ℕ)
    (k l : Fin (N + N)) (t : ℝ≥0) :
    ∃ C, ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ dysonRho G F s n ω →
      |locComp (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
        (fun y => driftK N q k y + driftK N q l y) v ω| ≤ C ∧
      |locSq (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
        (fun y => driftK N q k y + driftK N q l y)
        (fun y => covKL N q k k y + 2 * covKL N q k l y + covKL N q l l y) v ω| ≤ C := by
  refine ⟨2 * kK N q n t + (2 * kK N q n t) ^ 2 + 4 * (kCc N q n * t), ?_⟩
  filter_upwards [hb1] with ω hω v hvt hv
  obtain ⟨h1, h2⟩ := dom_single hG hFh hs hω q n hvt hv k
  obtain ⟨h1', -⟩ := dom_single hG hFh hs hω q n hvt hv l
  have hK : 0 ≤ kK N q n t := (abs_nonneg _).trans h1
  have hcc : 0 ≤ kCc N q n * t := (abs_nonneg _).trans (h2 k)
  have hA : |locComp (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
      (fun y => driftK N q k y + driftK N q l y) v ω| ≤ 2 * kK N q n t := by
    rw [locComp_add hG hFh hs hω q k l v]
    exact (abs_add_le _ _).trans (by linarith)
  refine ⟨by nlinarith, ?_⟩
  have hint : |∫ r in Ioc (0 : ℝ) v, (covKL N q k k (Ypath N G F s r.toNNReal ω) +
      2 * covKL N q k l (Ypath N G F s r.toNNReal ω) + covKL N q l l (Ypath N G F s r.toNNReal ω))|
        ≤ 4 * (kCc N q n * t) := by
    obtain ⟨b1, b2, b3⟩ := state_bounds hG hs hFh hω q n hv
    have hvt' : (v : ℝ) ≤ t := by exact_mod_cast hvt
    refine (abs_setIntegral_Ioc_le (C := 4 * kCc N q n) v fun r hr => ?_).trans ?_
    · simp only [covKL, vecHerm_Ypath hG hFh]
      have e1 := b3 r hr k k; have e2 := b3 r hr k l; have e3 := b3 r hr l l
      unfold kCc
      calc _ ≤ |dysonStateCov N (dysonState N q (F ω + G (s + r.toNNReal) ω)) k k| +
            |2 * dysonStateCov N (dysonState N q (F ω + G (s + r.toNNReal) ω)) k l| +
            |dysonStateCov N (dysonState N q (F ω + G (s + r.toNNReal) ω)) l l| :=
            (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
        _ ≤ _ := by rw [abs_mul, abs_two]; linarith
    · rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hvt' (kCc_nonneg q n)) (by norm_num)
  unfold locSq
  calc _ ≤ |locComp (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
        (fun y => driftK N q k y + driftK N q l y) v ω *
        locComp (Ypath N G F s) (fun y => stateFn N q k y + stateFn N q l y)
        (fun y => driftK N q k y + driftK N q l y) v ω| +
      |∫ r in Ioc (0 : ℝ) v, (covKL N q k k (Ypath N G F s r.toNNReal ω) +
      2 * covKL N q k l (Ypath N G F s r.toNNReal ω) + covKL N q l l (Ypath N G F s r.toNNReal ω))| :=
        abs_sub _ _
    _ ≤ (2 * kK N q n t) ^ 2 + 4 * (kCc N q n * t) := by
        rw [abs_mul, sq]
        exact add_le_add (mul_le_mul hA hA (abs_nonneg _) (by linarith)) hint
    _ ≤ _ := by nlinarith

end BlockBand.SourceProcess.Stochastic.Dyson
