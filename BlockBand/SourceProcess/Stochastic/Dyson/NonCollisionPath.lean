module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionStop
public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionFixedTime

/-!
# McKean's argument: pathwise estimates along the stopped coordinates

With `Y_u = hermVec(F + G_{s+u})`, `ρ = ncRho G F s n m`, `Yρ = Y` stopped at `ρ`:
* `initGood G F s k`: the time-`s` spectrum has gaps `> 1/k` and lies in `[-k, k]`
  (an `𝓖_s`-event, `measurableSet_initGood`);
* `badSet G F s T k m`: `initGood`, the increment entry sum stays `< m` on `[0, T]`, and the
  spectrum of `F + G_{s+u}` is not simple for some `u ≤ T`;
* on `initGood` (`n ≥ k`): `stopped_region` (gaps `≥ 1/n`, spread `≤ 2(k + Nm)` at all times),
  `abs_lyap_stopped_le`, `abs_lyap_init_le`;
* on `badSet`: `lyap_stopped_bad_le`, the stopped Lyapunov function at time `T` is
  `≤ 2N² log R - log n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory Filter Topology
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- Good initial spectrum at level `k`. -/
def initGood (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | (∀ i j, i ≠ j → 1 / (k : ℝ) <
      |dysonEigenvalue N (F ω + G s ω) i - dysonEigenvalue N (F ω + G s ω) j|) ∧
    ∀ i, |dysonEigenvalue N (F ω + G s ω) i| ≤ k}

/-- A collision on `[s, s + T]` from a good start, with increments below `m`. -/
def badSet (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s T : ℝ≥0) (k m : ℕ) : Set Ω :=
  initGood G F s k ∩ {ω | (T : WithTop ℝ≥0) < normStop G s m ω ∧
    ∃ u ≤ T, ¬ HasSimpleSpectrum N (F ω + G (s + u) ω)}

theorem measurableSet_initGood (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (s : ℝ≥0) (k : ℕ) : MeasurableSet[𝓖 s] (initGood G F s k) := by
  have hS : MeasurableSet {M : Matrix (Fin N) (Fin N) ℂ | (∀ i j, i ≠ j → 1 / (k : ℝ) <
      |dysonEigenvalue N M i - dysonEigenvalue N M j|) ∧ ∀ i, |dysonEigenvalue N M i| ≤ k} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
      (MeasurableSet.iInter fun i => measurableSet_le
        (continuous_dysonEigenvalue i).abs.measurable measurable_const)
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ne_eq, not_false_eq_true, Set.iInter_true]
      exact measurableSet_lt measurable_const
        (((continuous_dysonEigenvalue i).sub (continuous_dysonEigenvalue j)).abs.measurable :
          Measurable fun M : Matrix (Fin N) (Fin N) ℂ =>
            |dysonEigenvalue N M i - dysonEigenvalue N M j|)
  exact (measurable_hermBM_add hG hF s) hS

/-- The stopped coordinate process. -/
abbrev Ystop (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n m : ℕ) : ℝ≥0 → Ω → Fin (N * N) → ℝ :=
  stoppedProcess (fun u ω => hermVec N (F ω + G (s + u) ω)) (ncRho G F s n m)

/-- Spread constant `R = 2(k + N m)`. -/
def sprR (N k m : ℕ) : ℝ := 2 * (k + N * m)

theorem one_le_sprR {k m : ℕ} (hk : 1 ≤ k) : 1 ≤ sprR N k m := by
  unfold sprR
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : (0 : ℝ) ≤ N * m := by positivity
  linarith

variable {s T : ℝ≥0} {n m k : ℕ}

theorem stopped_region (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ initGood G F s k) (t : ℝ≥0) :
    (∀ i j, i ≠ j → 1 / (n : ℝ) ≤ |lam N i (Ystop G F s n m t ω) - lam N j (Ystop G F s n m t ω)|) ∧
    ∀ i j, |lam N i (Ystop G F s n m t ω) - lam N j (Ystop G F s n m t ω)| ≤ sprR N k m :=
  region_le_ncRho hG hFh hk hkn hm hω.1 hω.2 (untopA_min_le_rho t _)

theorem stopped_mem_simpleSet (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ initGood G F s k) (t : ℝ≥0) :
    Ystop G F s n m t ω ∈ simpleSet N := by
  have hn : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
    positivity
  exact hasSimpleSpectrum_of_gap hn (stopped_region hG hFh hk hkn hm hω t).1

theorem abs_lyap_stopped_le (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ initGood G F s k) (t : ℝ≥0) :
    |lyap N (Ystop G F s n m t ω)| ≤
      (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (n : ℝ))) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hk.trans hkn
  exact abs_lyap_le (by positivity) ((div_le_one (by positivity)).mpr hn) (one_le_sprR hk)
    (stopped_region hG hFh hk hkn hm hω t).1 (stopped_region hG hFh hk hkn hm hω t).2

theorem abs_lyap_init_le (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) {ω : Ω} (hω : ω ∈ initGood G F s k) :
    |lyap N (Ystop G F s n m 0 ω)| ≤
      (N : ℝ) ^ 2 * (Real.log (sprR N k m) - Real.log (1 / (k : ℝ))) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hH : (F ω + G s ω).IsHermitian := (hFh ω).add (hG.hermitian _ ω)
  have h0 : Ystop G F s n m 0 ω = hermVec N (F ω + G s ω) := by
    rw [Ystop, stoppedProcess_zero', add_zero]
  rw [h0]
  refine abs_lyap_le (by positivity) ((div_le_one (by positivity)).mpr hk') (one_le_sprR hk)
    (fun i j hij => ?_) (fun i j => ?_)
  · rw [lam_hermVec hH, lam_hermVec hH]; exact (hω.1 i j hij).le
  · rw [lam_hermVec hH, lam_hermVec hH]
    have := abs_sub (dysonEigenvalue N (F ω + G s ω) i) (dysonEigenvalue N (F ω + G s ω) j)
    have h1 := hω.2 i
    have h2 := hω.2 j
    have : (0 : ℝ) ≤ N * m := by positivity
    unfold sprR; linarith

/-- On a collision event, the stopped Lyapunov function at time `T` is small. -/
theorem lyap_stopped_bad_le (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω} (hω : ω ∈ badSet G F s T k m) :
    lyap N (Ystop G F s n m T ω) ≤
      2 * (N : ℝ) ^ 2 * Real.log (sprR N k m) + Real.log (1 / (n : ℝ)) := by
  obtain ⟨hA, hT, u, huT, hu⟩ := hω
  have hHc := continuous_hermBM_add hG F
  obtain ⟨i, j, hij, heq⟩ := exists_eq_of_not_simple hu
  have hgu : u ∈ gapSet N (fun t ω => F ω + G t ω) s n ω :=
    ⟨i, j, hij, by simp only [heq, sub_self, abs_zero]; positivity⟩
  have hσu : gapStop N (fun t ω => F ω + G t ω) s n ω ≤ u := by
    rw [gapStop_eq]; exact iInf₂_le u hgu
  have hσT : gapStop N (fun t ω => F ω + G t ω) s n ω ≤ T :=
    hσu.trans (WithTop.coe_le_coe.mpr huT)
  have hρ : ncRho G F s n m ω = gapStop N (fun t ω => F ω + G t ω) s n ω :=
    min_eq_left (hσT.trans hT.le)
  obtain ⟨w, hw⟩ : ∃ w : ℝ≥0, gapStop N (fun t ω => F ω + G t ω) s n ω = w :=
    WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hσT) |>.imp
      fun _ h => h.symm
  have hwgap : w ∈ gapSet N (fun t ω => F ω + G t ω) s n ω := by
    obtain ⟨v, hv, hvw⟩ := (gapStop_le_iff hHc s n ω w).mp hw.le
    have : (w : WithTop ℝ≥0) ≤ v := by rw [← hw, gapStop_eq]; exact iInf₂_le v hv
    rwa [le_antisymm hvw (WithTop.coe_le_coe.mp this)] at hv
  have hYT : Ystop G F s n m T ω = hermVec N (F ω + G (s + w) ω) := by
    have hmin : min (T : WithTop ℝ≥0) (ncRho G F s n m ω) = w := by
      rw [hρ, hw]; exact min_eq_right (hw ▸ hσT)
    simp only [Ystop, stoppedProcess, hmin, untopA_coe']
  obtain ⟨i₀, j₀, hij₀, hle⟩ := hwgap
  have hreg := stopped_region hG hFh hk hkn hm hA T
  rw [hYT] at hreg ⊢
  have hH : (F ω + G (s + w) ω).IsHermitian := (hFh ω).add (hG.hermitian _ ω)
  have hn : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hk hkn)
    positivity
  refine lyap_le_of_close (one_le_sprR hk) hreg.2 hij₀ (hn.trans_le (hreg.1 i₀ j₀ hij₀)) ?_
  rw [lam_hermVec hH, lam_hermVec hH]; exact hle

end BlockBand.SourceProcess.Stochastic.Dyson
