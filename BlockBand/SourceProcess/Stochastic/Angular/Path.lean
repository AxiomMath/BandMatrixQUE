module

public import BlockBand.SourceProcess.Stochastic.Angular.Jet
public import BlockBand.SourceProcess.Stochastic.Angular.Deterministic
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularBounds
public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionStop

/-!
# Complex angular contract: pathwise estimates of the stopped variable

Fix a sample `ω` at which `H_{s+v}` has simple spectrum for every `v`.
* `angVar_eq_coordVar_of`: the contract's variable of a phase-invariant random test is
  `coordVar` of `arrayFn V (f ω)` and `arrGen V (f ω)` (no selection left);
* `abs_coordVar_le`: `|coordVar a b| ≤ 2α + u β` when `|a| ≤ α` on the simple set and
  `|b| ≤ β` at gaps `≥ 1/n` (before the gap stop all gaps exceed `1/n`);
* `coordVar_sub`: linearity in `(a, b)` for path-integrable densities;
* `abs_coordVar_jet_sub_le`: `|Ψ(g) - Ψ(h)| ≤ (2 + u N² n²/N) · dist(jet g, jet h)`;
* `abs_coordVar_test_le`: a bound uniform over tests with uniform `C²` bounds on the ball.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

theorem abs_coupling_sum_le (lam : Fin N → ℝ) (t : Fin N → Fin N → ℝ) {c K : ℝ} (hc0 : 0 ≤ c)
    (hK0 : 0 ≤ K) (hc : ∀ i j, i ≠ j → dysonCoupling N lam i j ≤ c) (hK : ∀ i j, |t i j| ≤ K) :
    |(1 / 4 : ℝ) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      dysonCoupling N lam i j * t i j| ≤ N * N * c * K := by
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hsum : |∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      dysonCoupling N lam i j * t i j| ≤ ∑ _i : Fin N, ∑ _j : Fin N, c * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j hj => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ => mul_nonneg hc0 hK0)
    have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
    rw [abs_mul, abs_of_nonneg (coupling_nonneg lam i j)]
    exact mul_le_mul (hc i j hij) (hK i j) (abs_nonneg _) hc0
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith [mul_nonneg hc0 hK0, mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) N)
    (Nat.cast_nonneg (α := ℝ) N)) (mul_nonneg hc0 hK0)]

section Path

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : MeasureTheory.Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}
  {s : ℝ≥0} {n : ℕ} {ω : Ω}

/-- **The contract's variable in coordinates**, at a sample with simple spectrum. -/
theorem angVar_eq_coordVar_of (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {ev : Matrix (Fin N) (Fin N) ℂ → Fin N → Fin N → ℂ} (hev : IsEigenSelection N ev)
    (V : Matrix (Fin N) (Fin r) ℂ) {f : Ω → AngularArray N r → ℝ} (hfp : IsPhaseInvariant (f ω))
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) (u : ℝ≥0) :
    angVar F G ev s V n f u ω =
      coordVar F G s n (arrayFn V (f ω)) (arrGen V (f ω)) u ω := by
  have hpt := fun v => arrayFn_hermVec hfp V hev ((hFh ω).add (hG.hermitian (s + v) ω)) (hω v)
  simp only [angVar, coordVar, stoppedProcess]
  rw [(hpt _).1, (hpt 0).1]
  congr 2
  funext w
  exact (hpt _).2

theorem path_mem (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) (v : ℝ≥0) :
    hermVec N (F ω + G (s + v) ω) ∈ simpleSet N :=
  hermVec_mem_simpleSet' ((hFh ω).add (hG.hermitian (s + v) ω)) (hω v)

/-- Path integrability of a density continuous on the simple-spectrum set. -/
theorem integrableOn_path (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) {b : (Fin (N * N) → ℝ) → ℝ}
    (hb : ContinuousOn b (simpleSet N)) (T : ℝ) :
    IntegrableOn (fun w : ℝ => b (hermVec N (F ω + G (s + w.toNNReal) ω))) (Ioc 0 T) := by
  have hp : Continuous fun w : ℝ => hermVec N (F ω + G (s + w.toNNReal) ω) :=
    continuous_hermVec.comp ((continuous_hermBM_add hG F ω).comp
      (continuous_const.add continuous_real_toNNReal))
  exact (hb.comp_continuous hp fun w => path_mem hG hFh hω _).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

omit [MeasurableSpace Ω] in
/-- **Linearity of `coordVar`** in path-integrable densities. -/
theorem coordVar_sub {a a' b b' : (Fin (N * N) → ℝ) → ℝ}
    (hb : ∀ T : ℝ, IntegrableOn (fun w : ℝ => b (hermVec N (F ω + G (s + w.toNNReal) ω))) (Ioc 0 T))
    (hb' : ∀ T : ℝ,
      IntegrableOn (fun w : ℝ => b' (hermVec N (F ω + G (s + w.toNNReal) ω))) (Ioc 0 T))
    (u : ℝ≥0) :
    coordVar F G s n a b u ω - coordVar F G s n a' b' u ω =
      coordVar F G s n (a - a') (b - b') u ω := by
  simp only [coordVar, stoppedProcess, Pi.sub_apply]
  rw [integral_sub (hb _) (hb' _)]
  ring

/-- The compensator integral before the gap stop. -/
theorem abs_integral_path_le (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) {b : (Fin (N * N) → ℝ) → ℝ}
    {β : ℝ} (hb : ∀ y ∈ simpleSet N, (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) →
      |b y| ≤ β) {τ : ℝ≥0} (hτσ : (τ : WithTop ℝ≥0) ≤ gapStop N (fun t ω => F ω + G t ω) s n ω) :
    |∫ w in Ioc (0 : ℝ) τ, b (hermVec N (F ω + G (s + w.toNNReal) ω))| ≤ β * τ := by
  rw [integral_Ioc_eq_integral_Ioo, ← Real.norm_eq_abs]
  have hb' : ∀ x ∈ Ioo (0 : ℝ) τ, ‖b (hermVec N (F ω + G (s + x.toNNReal) ω))‖ ≤ β := by
    intro x hx
    have hxσ : (x.toNNReal : WithTop ℝ≥0) < gapStop N (fun t ω => F ω + G t ω) s n ω := by
      refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hτσ
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx.1.le]; exact hx.2
    have hH := (hFh ω).add (hG.hermitian (s + x.toNNReal) ω)
    rw [Real.norm_eq_abs]
    refine hb _ (path_mem hG hFh hω _) fun i j hij => ?_
    have hg : 1 / (n : ℝ) < |dysonEigenvalue N (F ω + G (s + x.toNNReal) ω) i -
        dysonEigenvalue N (F ω + G (s + x.toNNReal) ω) j| :=
      Angular.gap_of_lt_gapStop (H := fun t ω => F ω + G t ω) hxσ i j hij
    rw [lam_hermVec hH, lam_hermVec hH]
    exact hg.le
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) τ)
    (by simp) hb'
  rwa [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by simp), sub_zero] at this

/-- **Bound of `coordVar`.** -/
theorem abs_coordVar_le (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) {a b : (Fin (N * N) → ℝ) → ℝ}
    {α β : ℝ} (ha : ∀ y ∈ simpleSet N, |a y| ≤ α) (hβ : 0 ≤ β)
    (hb : ∀ y ∈ simpleSet N, (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) →
      |b y| ≤ β) (u : ℝ≥0) :
    |coordVar F G s n a b u ω| ≤ 2 * α + u * β := by
  have hτu := untopA_min_le u (gapStop N (fun t ω => F ω + G t ω) s n ω)
  have hτσ := untopA_min_le_rho u (gapStop N (fun t ω => F ω + G t ω) s n ω)
  simp only [coordVar, stoppedProcess]
  generalize (min (u : WithTop ℝ≥0) (gapStop N (fun t ω => F ω + G t ω) s n ω)).untopA = τ
    at hτu hτσ ⊢
  have h1 := ha _ (path_mem hG hFh hω τ)
  have h2 := ha _ (path_mem hG hFh hω 0)
  have h3 := abs_integral_path_le hG hFh hω hb hτσ
  have h4 : β * (τ : ℝ) ≤ (u : ℝ) * β := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hτu) hβ
  have h5 := abs_sub (a (hermVec N (F ω + G (s + τ) ω)) - a (hermVec N (F ω + G (s + 0) ω)))
    (∫ w in Ioc (0 : ℝ) τ, b (hermVec N (F ω + G (s + w.toNNReal) ω)))
  have h6 := abs_sub (a (hermVec N (F ω + G (s + τ) ω))) (a (hermVec N (F ω + G (s + 0) ω)))
  linarith

/-- **Lipschitz dependence on the jet.** -/
theorem abs_coordVar_jet_sub_le (hG : IsHermitianBrownian Q 𝓖 N G)
    (hFh : ∀ ω, (F ω).IsHermitian) (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω))
    (V : Matrix (Fin N) (Fin r) ℂ) {g h : AngularArray N r → ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (hgp : IsPhaseInvariant g) (hhp : IsPhaseInvariant h) (hn : 0 < n)
    (u : ℝ≥0) :
    |coordVar F G s n (arrayFn V g) (arrGen V g) u ω -
        coordVar F G s n (arrayFn V h) (arrGen V h) u ω| ≤
      (2 + u * (N * N * (1 / (N * (1 / (n : ℝ)) ^ 2)))) *
        dist (jet hg (frameBound V)) (jet hh (frameBound V)) := by
  rw [coordVar_sub (integrableOn_path hG hFh hω (continuousOn_arrGen hg hgp))
    (integrableOn_path hG hFh hω (continuousOn_arrGen hh hhp))]
  set d := dist (jet hg (frameBound V)) (jet hh (frameBound V))
  set c := 1 / (N * (1 / (n : ℝ)) ^ 2)
  have hd : 0 ≤ d := dist_nonneg
  have hc : 0 ≤ c := by positivity
  have key := abs_coordVar_le (n := n) (a := arrayFn V g - arrayFn V h) (b := arrGen V g - arrGen V h)
    (α := d) (β := N * N * c * d) hG hFh hω (fun y hy => ?_) (by positivity) (fun y hy hgap => ?_) u
  · nlinarith [key]
  · simp only [Pi.sub_apply, arrayFn_of_mem hy]
    exact abs_sub_le_dist_jet hg hh (norm_arrZ_le V hy)
  · simp only [Pi.sub_apply, arrGen_of_mem hy, gen_eq_sum]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    exact abs_coupling_sum_le _ _ hc hd (coupling_le_gap hn hgap) fun i j =>
      abs_pairTerm_sub_le_dist_jet hg hh (norm_arrZ_le V hy) i j

/-- **A bound uniform over tests** with uniform `C²` bounds on the ball. -/
theorem abs_coordVar_test_le (hG : IsHermitianBrownian Q 𝓖 N G)
    (hFh : ∀ ω, (F ω).IsHermitian) (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω))
    (V : Matrix (Fin N) (Fin r) ℂ) {g : AngularArray N r → ℝ} (hn : 0 < n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ Z : AngularArray N r, ‖Z‖ ≤ frameBound V →
      |g Z| ≤ C ∧ ‖fderiv ℝ g Z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ g) Z‖ ≤ C) (u : ℝ≥0) :
    |coordVar F G s n (arrayFn V g) (arrGen V g) u ω| ≤ 2 * C + u * (N * N *
      (1 / (N * (1 / (n : ℝ)) ^ 2)) * (2 * C * (frameBound V ^ 2 + frameBound V))) := by
  have hR := frameBound_nonneg V
  refine abs_coordVar_le hG hFh hω (fun y hy => ?_) (by positivity) (fun y hy hgap => ?_) u
  · rw [arrayFn_of_mem hy]; exact (hC _ (norm_arrZ_le V hy)).1
  · rw [arrGen_of_mem hy]
    have hZ := norm_arrZ_le V hy
    obtain ⟨-, h1, h2⟩ := hC _ hZ
    refine abs_gen_le _ _ _ (by positivity) (by positivity) (coupling_le_gap hn hgap)
      fun i j => (abs_pairTerm_le g i j _ h1 h2).trans ?_
    have : ‖arrZ V y‖ ^ 2 ≤ frameBound V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hZ 2
    gcongr

end Path

end BlockBand.SourceProcess.Stochastic.ComplexAngular
