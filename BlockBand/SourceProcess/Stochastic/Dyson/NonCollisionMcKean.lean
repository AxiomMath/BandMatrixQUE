module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionPath
public import BlockBand.SourceProcess.Stochastic.Dyson.MMTools
public import BlockBand.SourceProcess.Stochastic.Dyson.B2Path

/-!
# McKean's argument: the expectation estimate

Fix `s > 0`, `T`, levels `k ≥ 1`, `m ≥ 1`, and `n ≥ max k 2`. With `Y_u = hermVec(F + G_{s+u})`
stopped at `ρ = ncRho G F s n m` (a.s. in `simpleSet N`, by `simple_fixedTime` at time `s`),
the Itô formula (a1) applied to the log-Vandermonde function `lyap` gives the compensated process
`K_t = lyap(Yρ_t) - lyap(Yρ_0) - ∫_0^t β`, `β ≥ 0` (`itoDrift_lyap`, `lyapDrift_nonneg`), whose
localizations have martingale modifications. On the `𝓖_s`-event `A = initGood G F s k` all the
quantities are bounded, so dominated convergence gives `∫_A K_T = 0` (`setIntegral_lyapK_eq_zero`).
Since `K_T ≤ c` on `A` and `K_T ≤ c - log n` on `badSet G F s T k m ⊆ A`, Markov's inequality
yields `log n · P(badSet) ≤ c` (`mcKean_bound`), with `c` independent of `n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

theorem switchAfter_of_le' {Ω' G' : Type*} [Zero G'] {σ : Ω' → WithTop ℝ≥0}
    {f : ℝ≥0 → Ω' → G'} {u : ℝ≥0} {ω : Ω'} (h : (u : WithTop ℝ≥0) ≤ σ ω) :
    switchAfter σ f u ω = f u ω := by
  unfold switchAfter; split_ifs; rfl

theorem switchAfter_of_not_le' {Ω' G' : Type*} [Zero G'] {σ : Ω' → WithTop ℝ≥0}
    {f : ℝ≥0 → Ω' → G'} {u : ℝ≥0} {ω : Ω'} (h : ¬ (u : WithTop ℝ≥0) ≤ σ ω) :
    switchAfter σ f u ω = 0 := by
  unfold switchAfter; split_ifs; rfl

/-- The Itô drift of the stopped Lyapunov process. -/
def lyapBeta (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n m : ℕ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  itoDrift (fun p : ℝ × (Fin (N * N) → ℝ) => lyap N p.2) (Ystop G F s n m r ω) r
    (switchAfter (ncRho G F s n m) (fun _ _ => (0 : Fin (N * N) → ℝ)) r ω)
    (switchAfter (ncRho G F s n m) (fun _ _ => gueCovVec N) r ω)

/-- The compensated stopped Lyapunov process. -/
def lyapK (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  lyap N (Ystop G F s n m t ω) - lyap N (Ystop G F s n m 0 ω) -
    ∫ r in Ioc (0 : ℝ) t, lyapBeta G F s n m r.toNNReal ω

variable {s T : ℝ≥0} {n m k : ℕ}

theorem lyapBeta_bounds (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ initGood G F s k) (r : ℝ≥0) :
    0 ≤ lyapBeta G F s n m r ω ∧
      lyapBeta G F s n m r ω ≤ (N : ℝ) ^ 2 * ((1 / (n : ℝ))⁻¹) ^ 2 := by
  have hy := stopped_mem_simpleSet hG hFh hk hkn hm hω r
  have hn : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
    positivity
  have hD : (N : ℝ) ^ 2 * ((1 / (n : ℝ))⁻¹) ^ 2 ≥ 0 := by positivity
  unfold lyapBeta
  by_cases h : (r : WithTop ℝ≥0) ≤ ncRho G F s n m ω
  · rw [switchAfter_of_le' h, switchAfter_of_le' h, itoDrift_lyap hy]
    exact ⟨lyapDrift_nonneg _, lyapDrift_le hn (stopped_region hG hFh hk hkn hm hω r).1⟩
  · rw [switchAfter_of_not_le' h, switchAfter_of_not_le' h,
      itoDrift_zero_cov ((contDiffAt_lyap (n := 2) hy).differentiableAt (by norm_num))]
    exact ⟨le_rfl, hD⟩

/-- The bound constant of `|K_t|`, `t ≤ T`. -/
def kBound (N k m n : ℕ) (T : ℝ≥0) : ℝ :=
  (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (n : ℝ))) +
    (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (k : ℝ))) +
    (N : ℝ) ^ 2 * ((1 / (n : ℝ))⁻¹) ^ 2 * T

theorem abs_lyapK_le (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ initGood G F s k) {t : ℝ≥0}
    (ht : t ≤ T) : |lyapK G F s n m t ω| ≤ kBound N k m n T := by
  have h1 := abs_lyap_stopped_le hG hFh hk hkn hm hω t
  have h2 := abs_lyap_init_le (n := n) (m := m) hG hFh hk hω
  have h3 := abs_setIntegral_Ioc_le (f := fun r : ℝ => lyapBeta G F s n m r.toNNReal ω)
    (C := (N : ℝ) ^ 2 * ((1 / (n : ℝ))⁻¹) ^ 2) t fun r _ => by
      have hb := lyapBeta_bounds hG hFh hk hkn hm hω r.toNNReal
      rw [abs_of_nonneg hb.1]; exact hb.2
  have h4 : (N : ℝ) ^ 2 * ((1 / (n : ℝ))⁻¹) ^ 2 * t ≤ (N : ℝ) ^ 2 * ((1 / (n : ℝ))⁻¹) ^ 2 * T :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (by positivity)
  unfold lyapK kBound
  have := abs_sub (lyap N (Ystop G F s n m t ω) - lyap N (Ystop G F s n m 0 ω))
    (∫ r in Ioc (0 : ℝ) t, lyapBeta G F s n m r.toNNReal ω)
  have := abs_sub (lyap N (Ystop G F s n m t ω)) (lyap N (Ystop G F s n m 0 ω))
  linarith

theorem lyapK_upper (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ initGood G F s k) (t : ℝ≥0) :
    lyapK G F s n m t ω ≤ lyap N (Ystop G F s n m t ω) +
      (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (k : ℝ))) := by
  have h2 := abs_lyap_init_le (n := n) (m := m) hG hFh hk hω
  have h3 : 0 ≤ ∫ r in Ioc (0 : ℝ) t, lyapBeta G F s n m r.toNNReal ω :=
    setIntegral_nonneg measurableSet_Ioc fun r _ =>
      (lyapBeta_bounds hG hFh hk hkn hm hω r.toNNReal).1
  unfold lyapK
  linarith [neg_abs_le (lyap N (Ystop G F s n m 0 ω))]

end BlockBand.SourceProcess.Stochastic.Dyson
