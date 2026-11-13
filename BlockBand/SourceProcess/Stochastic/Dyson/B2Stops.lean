module

public import BlockBand.SourceProcess.Stochastic.Dyson.Stops
public import BlockBand.SourceProcess.Stochastic.Dyson.Bounds

/-!
# Dyson Brownian motion: the localizing sequence of clause and its bounds

`dysonRho G F s n = min (gapStop (n+1)) (normStop (n+1))`, where `normStop m` is the first time the
entry sum `∑_{ab} |(G_{s+u} - G_s)_{ab}|` reaches `m`. These are stopping times of `u ↦ 𝓖_{s+u}`
(`isStoppingTime_dysonRho`), they tend to `⊤` on every non-collision sample
(`tendsto_dysonRho`), and up to them (`bounds_le_dysonRho`): all gaps are `≥ 1/(n+1)` at positive
times, eigenvalues move by at most `N(n+1)`, and overlaps stay in `[0, N‖q‖²]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- Entry sum of the increment `G_{s+u} - G_s`. -/
def incrSum (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ a, ∑ b, ‖(G (s + u) ω - G s ω) a b‖

/-- First time the increment entry sum reaches `m`. -/
def normStop (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (m : ℕ) : Ω → WithTop ℝ≥0 :=
  hitStop (fun u ω => -incrSum G s u ω) (-(m : ℝ))

/-- The localizing sequence of (b2). -/
def dysonRho (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (gapStop N (fun t ω => F ω + G t ω) s (n + 1) ω) (normStop G s (n + 1) ω)

theorem continuous_incrSum (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0) (ω : Ω) :
    Continuous fun u => incrSum G s u ω := by
  unfold incrSum
  have hc : Continuous fun u => G (s + u) ω - G s ω :=
    ((hG.continuous ω).comp (continuous_const.add continuous_id)).sub continuous_const
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact ((continuous_apply b).comp ((continuous_apply a).comp hc)).norm

theorem isStoppingTime_dysonRho (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (s : ℝ≥0) (n : ℕ) : IsStoppingTime (shiftFiltration 𝓖 s) (dysonRho G F s n) := by
  refine IsStoppingTime.min (isStoppingTime_gapStop (continuous_hermBM_add hG F)
    (measurable_hermBM_add hG hF) s (n + 1)) ?_
  refine isStoppingTime_hitStop (fun ω => (continuous_incrSum hG s ω).neg) (fun v => ?_) _
  have hm : Measurable[shiftFiltration 𝓖 s v] fun ω => G (s + v) ω - G s ω :=
    (hG.adapted (s + v)).sub ((hG.adapted s).mono (𝓖.mono le_self_add) le_rfl)
  have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => -∑ a, ∑ b, ‖M a b‖ :=
    (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((continuous_apply b).comp (continuous_apply a)).norm).neg
  exact hc.measurable.comp hm

omit [MeasurableSpace Ω] in
theorem incrSum_zero (s : ℝ≥0) (ω : Ω) : incrSum G s 0 ω = 0 := by simp [incrSum]

theorem tendsto_normStop (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => normStop G s (n + 1) ω) atTop (𝓝 ⊤) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  lift a to ℝ≥0 using ha.ne
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).exists_bound_of_continuousOn
    (continuous_incrSum hG s ω).continuousOn
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop n₀] with n hn
  by_contra hle
  rw [not_lt, normStop, hitStop_le_iff (continuous_incrSum hG s ω).neg] at hle
  obtain ⟨v, hva, hv⟩ := hle
  have h1 := hM v ⟨zero_le, hva⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : ((n : ℝ) + 1) ≤ incrSum G s v ω := by push_cast at hv; linarith
  have h3 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  linarith [le_abs_self (incrSum G s v ω)]

theorem tendsto_dysonRho (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s) {ω : Ω}
    (hω : ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)) :
    Tendsto (fun n => dysonRho G F s n ω) atTop (𝓝 ⊤) := by
  have h1 := (gapStop_tendsto_top (continuous_hermBM_add hG F) hs hω).comp
    (tendsto_add_atTop_nat 1)
  have h2 := tendsto_normStop hG s ω
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => absurd ha not_top_lt⟩
  filter_upwards [(tendsto_order.1 h1).1 a ha, (tendsto_order.1 h2).1 a ha] with n hn1 hn2
  exact lt_min hn1 hn2

omit [MeasurableSpace Ω] in
/-- Each gap hitting time dominates the gap stop. -/
theorem gapStop_le_hitStop (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (m : ℕ)
    {i j : Fin N} (hij : i ≠ j) (ω : Ω) :
    gapStop N H s m ω ≤ hitStop (fun v ω => |dysonEigenvalue N (H (s + v) ω) i -
      dysonEigenvalue N (H (s + v) ω) j|) (1 / (m : ℝ)) ω := by
  rw [gapStop_eq, hitStop]
  exact biInf_mono fun v hv => ⟨i, j, hij, hv⟩

theorem dist_le_sum_norm (A B : Matrix (Fin N) (Fin N) ℂ) :
    @dist (Fin N → Fin N → ℂ) _ A B ≤ ∑ a, ∑ b, ‖(A - B) a b‖ := by
  have h0 : 0 ≤ ∑ a, ∑ b, ‖(A - B) a b‖ :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  refine (dist_pi_le_iff h0).2 fun a => (dist_pi_le_iff h0).2 fun b => ?_
  rw [dist_eq_norm]
  calc ‖A a b - B a b‖ = ‖(A - B) a b‖ := rfl
    _ ≤ ∑ b, ‖(A - B) a b‖ := Finset.single_le_sum (f := fun b => ‖(A - B) a b‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ a, ∑ b, ‖(A - B) a b‖ := Finset.single_le_sum (f := fun a => ∑ b, ‖(A - B) a b‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)

/-- **Bounds up to the localizing time.** -/
theorem bounds_le_dysonRho (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} (hs : 0 < s)
    (hFh : ∀ ω, (F ω).IsHermitian) {ω : Ω}
    (hω : ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)) (q : Fin N → ℂ) (n : ℕ)
    {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ dysonRho G F s n ω) :
    (0 < v → ∀ i j : Fin N, i ≠ j → 1 / ((n : ℝ) + 1) ≤
      |dysonEigenvalue N (F ω + G (s + v) ω) i - dysonEigenvalue N (F ω + G (s + v) ω) j|) ∧
    (∀ i, |dysonEigenvalue N (F ω + G (s + v) ω) i - dysonEigenvalue N (F ω + G (s + 0) ω) i| ≤
      N * ((n : ℝ) + 1)) ∧
    (∀ i, 0 ≤ dysonOverlap N q (F ω + G (s + v) ω) i ∧
      dysonOverlap N q (F ω + G (s + v) ω) i ≤ N * qNormSq q) := by
  have hH : (F ω + G (s + v) ω).IsHermitian := (hFh ω).add (hG.hermitian _ ω)
  have hsimp : HasSimpleSpectrum N (F ω + G (s + v) ω) := hω _ (add_pos_of_pos_of_nonneg hs zero_le)
  refine ⟨fun hv0 i j hij => ?_, fun i => ?_, fun i => ⟨overlap_nonneg hH hsimp q i,
    overlap_le hH hsimp q i⟩⟩
  · have hle := (hv.trans (min_le_left _ _)).trans (gapStop_le_hitStop _ s (n + 1) hij ω)
    have := le_of_le_hitStop (continuous_gap ((continuous_hermBM_add hG F ω).comp
      (continuous_const.add continuous_id)) i j) hle (Or.inl hv0)
    simpa using this
  · have hS : incrSum G s v ω ≤ (n : ℝ) + 1 := by
      have hle := hv.trans (min_le_right _ _)
      have := le_of_le_hitStop (continuous_incrSum hG s ω).neg hle
        (Or.inr (by rw [incrSum_zero]; push_cast; linarith))
      push_cast at this; linarith
    refine (abs_dysonEigenvalue_sub_le _ _ i).trans ?_
    refine mul_le_mul_of_nonneg_left ((dist_le_sum_norm _ _).trans ?_) (Nat.cast_nonneg N)
    refine le_of_eq_of_le ?_ hS
    unfold incrSum
    simp only [add_zero, add_sub_add_left_eq_sub]

end BlockBand.SourceProcess.Stochastic.Dyson
