module

public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionRegion
public import BlockBand.SourceProcess.Stochastic.Dyson.Localize

/-!
# McKean's argument: the stopping time and the stopped region

* `ncRho G F s n m = min (gapStop n) (normStop m)`, a stopping time of `u ↦ 𝓖_{s+u}`
  (`isStoppingTime_ncRho`);
* `region_le_ncRho`: up to `ncRho`, if the initial spectrum of `F + G_s` has gaps `> 1/k ≥ 1/n`
  and eigenvalues in `[-k, k]`, the spectrum of `F + G_{s+v}` (in the coordinates `lam`) has
  gaps `≥ 1/n` and spread `≤ 2(k + N m)`;
* `simple_le_ncRho`: up to `ncRho`, the spectrum stays simple if it is simple at time `s`;
* `exists_eq_of_not_simple`, `hasSimpleSpectrum_of_gap`: simple spectrum versus gaps.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory Filter Topology
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ}

theorem antitone_dysonEigenvalue (H : Matrix (Fin N) (Fin N) ℂ) :
    Antitone (dysonEigenvalue N H) := fun i j hij => by
  unfold dysonEigenvalue
  exact div_le_div_of_nonneg_right ((Matrix.isHermitian_add_transpose_self H).eigenvalues₀_antitone
    (Fin.le_def.mpr (Fin.le_def.mp hij))) (by norm_num)

theorem exists_eq_of_not_simple {H : Matrix (Fin N) (Fin N) ℂ} (h : ¬ HasSimpleSpectrum N H) :
    ∃ i j, i ≠ j ∧ dysonEigenvalue N H i = dysonEigenvalue N H j := by
  by_contra hne
  push Not at hne
  exact h ((antitone_dysonEigenvalue H).strictAnti_of_injective fun i j hij =>
    by_contra fun h' => hne i j h' hij)

theorem hasSimpleSpectrum_of_gap {H : Matrix (Fin N) (Fin N) ℂ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ i j, i ≠ j → δ ≤ |dysonEigenvalue N H i - dysonEigenvalue N H j|) :
    HasSimpleSpectrum N H :=
  (antitone_dysonEigenvalue H).strictAnti_of_injective fun i j hij => by
    by_contra h'
    have := h i j h'
    rw [hij, sub_self, abs_zero] at this
    linarith

theorem lam_hermVec {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (i : Fin N) :
    lam N i (hermVec N H) = dysonEigenvalue N H i := by
  unfold lam; rw [vecHerm_hermVec hH]

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- Gap stop at level `n` and increment-norm stop at level `m`. -/
def ncRho (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n m : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  min (gapStop N (fun t ω => F ω + G t ω) s n ω) (normStop G s m ω)

theorem isStoppingTime_ncRho (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F)
    (s : ℝ≥0) (n m : ℕ) : IsStoppingTime (shiftFiltration 𝓖 s) (ncRho G F s n m) := by
  refine IsStoppingTime.min (isStoppingTime_gapStop (continuous_hermBM_add hG F)
    (measurable_hermBM_add hG hF) s n) ?_
  refine isStoppingTime_hitStop (fun ω => (continuous_incrSum hG s ω).neg) (fun v => ?_) _
  have hm : Measurable[shiftFiltration 𝓖 s v] fun ω => G (s + v) ω - G s ω :=
    (hG.adapted (s + v)).sub ((hG.adapted s).mono (𝓖.mono le_self_add) le_rfl)
  have hc : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => -∑ a, ∑ b, ‖M a b‖ :=
    (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((continuous_apply b).comp (continuous_apply a)).norm).neg
  exact hc.measurable.comp hm

theorem gap_le_ncRho (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} {n m : ℕ} {ω : Ω}
    {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ ncRho G F s n m ω) (hv0 : 0 < v) {i j : Fin N}
    (hij : i ≠ j) : 1 / (n : ℝ) ≤
      |dysonEigenvalue N (F ω + G (s + v) ω) i - dysonEigenvalue N (F ω + G (s + v) ω) j| := by
  have hle := (hv.trans (min_le_left _ _)).trans (gapStop_le_hitStop _ s n hij ω)
  have := le_of_le_hitStop (continuous_gap ((continuous_hermBM_add hG F ω).comp
    (continuous_const.add continuous_id)) i j) hle (Or.inl hv0)
  simpa using this

theorem eig_le_ncRho (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} {n m : ℕ} (hm : 0 < m)
    {ω : Ω} {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ ncRho G F s n m ω) (i : Fin N) :
    |dysonEigenvalue N (F ω + G (s + v) ω) i - dysonEigenvalue N (F ω + G s ω) i| ≤
      N * (m : ℝ) := by
  have hS : incrSum G s v ω ≤ m := by
    have hle := hv.trans (min_le_right _ _)
    have := le_of_le_hitStop (continuous_incrSum hG s ω).neg hle
      (Or.inr (by rw [incrSum_zero]; linarith [(show (0 : ℝ) < m by exact_mod_cast hm)]))
    linarith
  refine (abs_dysonEigenvalue_sub_le _ _ i).trans ?_
  refine mul_le_mul_of_nonneg_left ((dist_le_sum_norm _ _).trans ?_) (Nat.cast_nonneg N)
  refine le_of_eq_of_le ?_ hS
  unfold incrSum
  simp only [add_sub_add_left_eq_sub]

/-- **The stopped region.** -/
theorem region_le_ncRho (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} {n m k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hm : 0 < m) {ω : Ω}
    (h0gap : ∀ i j, i ≠ j → 1 / (k : ℝ) <
      |dysonEigenvalue N (F ω + G s ω) i - dysonEigenvalue N (F ω + G s ω) j|)
    (h0b : ∀ i, |dysonEigenvalue N (F ω + G s ω) i| ≤ k)
    {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) ≤ ncRho G F s n m ω) :
    (∀ i j, i ≠ j → 1 / (n : ℝ) ≤ |lam N i (hermVec N (F ω + G (s + v) ω)) -
      lam N j (hermVec N (F ω + G (s + v) ω))|) ∧
    ∀ i j, |lam N i (hermVec N (F ω + G (s + v) ω)) - lam N j (hermVec N (F ω + G (s + v) ω))|
      ≤ 2 * (k + N * m) := by
  have hH : (F ω + G (s + v) ω).IsHermitian := (hFh ω).add (hG.hermitian _ ω)
  simp only [lam_hermVec hH]
  refine ⟨fun i j hij => ?_, fun i j => ?_⟩
  · rcases (zero_le : (0 : ℝ≥0) ≤ v).lt_or_eq with hv0 | hv0
    · exact gap_le_ncRho hG hv hv0 hij
    · subst hv0
      have hkn' : 1 / (n : ℝ) ≤ 1 / (k : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hk) (by exact_mod_cast hkn)
      simpa using (hkn'.trans (h0gap i j hij).le)
  · have hb : ∀ l, |dysonEigenvalue N (F ω + G (s + v) ω) l| ≤ k + N * m := fun l => by
      have h1 := eig_le_ncRho hG hm hv l
      have h2 := h0b l
      have := abs_sub_abs_le_abs_sub (dysonEigenvalue N (F ω + G (s + v) ω) l)
        (dysonEigenvalue N (F ω + G s ω) l)
      linarith
    have := abs_sub (dysonEigenvalue N (F ω + G (s + v) ω) i)
      (dysonEigenvalue N (F ω + G (s + v) ω) j)
    linarith [hb i, hb j]

/-- Up to `ncRho` the spectrum stays simple if it is simple at time `s` (`n > 0`). -/
theorem simple_le_ncRho (hG : IsHermitianBrownian Q 𝓖 N G) {s : ℝ≥0} {n m : ℕ} (hn : 0 < n)
    {ω : Ω} (h0 : HasSimpleSpectrum N (F ω + G s ω)) {v : ℝ≥0}
    (hv : (v : WithTop ℝ≥0) ≤ ncRho G F s n m ω) : HasSimpleSpectrum N (F ω + G (s + v) ω) := by
  rcases (zero_le : (0 : ℝ≥0) ≤ v).lt_or_eq with hv0 | hv0
  · exact hasSimpleSpectrum_of_gap (by positivity) fun i j hij => gap_le_ncRho hG hv hv0 hij
  · subst hv0; simpa using h0

end BlockBand.SourceProcess.Stochastic.Dyson
