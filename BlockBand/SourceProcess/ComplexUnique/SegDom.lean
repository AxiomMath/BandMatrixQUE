module

public import BlockBand.SourceProcess.ComplexUnique.NoiseLip
public import BlockBand.SourceProcess.ComplexUnique.LocalLaw
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartGap
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankBarrierUniform

/-!
# Chart domains for the restarted joint process on a stratum

For ranks `(r, r')`, horizon `h` and level `n` (`η = 1/(n+1)`, `T = n+1`):
* `segW`: `‖y‖ < T`, time `< h - η`, `η < e_r(B)`, `η < e_{r'}(M - B)`, `Re Tr M < T`;
  `isInteriorDomain_segW`: a relatively compact subdomain of `{t < h}`;
* `segF`: the set where the restarted process lives: time `≥ h`, or `G` feasible on the stratum
  `e_{r+1}(B) = e_{r'+1}(M - B) = 0`;
* `chartGood_seg`: on `segF ∩ segW` the Gram part is `ChartGood` with gap `segδ`;
* **`segAgree`**: there the joint chart noise has the joint brackets `jΓ`, `jΓ'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π]

/-- The Gram part of a real joint vector. -/
abbrev gOf (y : Fin (rDim (JIdx (SrcCol K π) π)) → ℝ) : GramState (SrcCol K π) := gramOf (zOf y)

/-- The chart domain. -/
def segW (K : ℕ) (π : Type*) [Fintype π] [DecidableEq π] (r r' : ℕ) (h : ℝ≥0) (n : ℕ) :
    Set (Fin (rDim (JIdx (SrcCol K π) π)) → ℝ) :=
  {y | ‖y‖ < n + 1} ∩ ({y | tOf y < (h : ℝ) - 1 / (n + 1)} ∩
    ({y | 1 / ((n : ℝ) + 1) < principalMinorSum r (gOf y).2} ∩
      ({y | 1 / ((n : ℝ) + 1) < principalMinorSum r' ((gOf y).1 - (gOf y).2)} ∩
        {y | ((gOf y).1.trace).re < n + 1})))

/-- The set where the restarted stratum process lives. -/
def segF (D : Matrix (SrcCol K π) (SrcCol K π) ℂ) (r r' : ℕ) (h : ℝ≥0) :
    Set (Fin (rDim (JIdx (SrcCol K π) π)) → ℝ) :=
  {y | (h : ℝ) ≤ tOf y ∨ (GramFeasible D (gOf y) ∧ principalMinorSum (r + 1) (gOf y).2 = 0 ∧
    principalMinorSum (r' + 1) ((gOf y).1 - (gOf y).2) = 0)}

/-- The chart gap. -/
def segδ (c : Type*) [Fintype c] (r r' n : ℕ) : ℝ :=
  (1 / ((n : ℝ) + 1)) / (2 ^ Fintype.card c * ((n : ℝ) + 1) ^ (r + r'))

theorem segδ_pos (c : Type*) [Fintype c] (r r' n : ℕ) : 0 < segδ c r r' n := by
  unfold segδ; positivity

omit [DecidableEq π] in
theorem continuous_gOf : Continuous (gOf (K := K) (π := π)) :=
  continuous_gramOf.comp continuous_zOf

theorem isInteriorDomain_segW (r r' : ℕ) (h : ℝ≥0) (n : ℕ) :
    IsInteriorDomain (segW K π r r' h n) {y | tOf y < h} := by
  have hB : Continuous fun y => principalMinorSum r (gOf (K := K) (π := π) y).2 :=
    (contDiff_ek_snd r).continuous.comp continuous_gOf
  have hC : Continuous fun y => principalMinorSum r' ((gOf (K := K) (π := π) y).1 -
      (gOf (K := K) (π := π) y).2) := (contDiff_ek_fst_sub_snd r').continuous.comp continuous_gOf
  have hT : Continuous fun y => ((gOf (K := K) (π := π) y).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp continuous_gOf).matrix_trace)
  refine ⟨?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_norm continuous_const).inter
      ((isOpen_lt continuous_tOf continuous_const).inter ((isOpen_lt continuous_const hB).inter
        ((isOpen_lt continuous_const hC).inter (isOpen_lt hT continuous_const))))
  · refine Bornology.IsBounded.isCompact_closure ((Metric.isBounded_closedBall (x := 0)
      (r := (n : ℝ) + 1)).subset fun y hy => ?_)
    rw [Metric.mem_closedBall, dist_zero_right]; exact hy.1.le
  · have hcl : closure (segW K π r r' h n) ⊆ {y | tOf y ≤ (h : ℝ) - 1 / (n + 1)} :=
      closure_minimal (fun y hy => (show tOf y < _ from hy.2.1).le) (isClosed_le continuous_tOf continuous_const)
    intro y hy
    have := hcl hy
    simp only [mem_ofPred_eq] at this ⊢
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem chartGood_seg {D : Matrix (SrcCol K π) (SrcCol K π) ℂ} {r r' : ℕ} {h : ℝ≥0} {n : ℕ}
    {y : Fin (rDim (JIdx (SrcCol K π) π)) → ℝ} (hy : y ∈ segF D r r' h ∩ segW K π r r' h n) :
    ChartGood D (segδ (SrcCol K π) r r' n) (gOf y) := by
  obtain ⟨hF, hW⟩ := hy
  have ht : tOf y < h := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [(show tOf y < _ from hW.2.1)]
  rcases hF with hF | ⟨hf, hzB, hzC⟩
  · exact absurd hF (not_le.2 ht)
  have hT1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
  have hle : ∀ k, k ≤ r + r' → segδ (SrcCol K π) r r' n ≤
      (1 / ((n : ℝ) + 1)) / (2 ^ Fintype.card (SrcCol K π) * ((n : ℝ) + 1) ^ k) :=
    fun k hk => div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT1 hk) (by positivity))
  exact chartGood_of_stratum hf hT1 hW.2.2.2.2.le hzB hW.2.2.1.le hzC hW.2.2.2.1.le
    (hle r (by omega)) (hle r' (by omega))

/-- **The joint chart noise has the joint brackets on `segF ∩ segW`.** -/
theorem segAgree {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) {D : Matrix (SrcCol K π) (SrcCol K π) ℂ}
    (hD : IsSignature D) (r r' : ℕ) (h : ℝ≥0) (n : ℕ) :
    ∀ y ∈ segF D r r' h ∩ segW K π r r' h n, ∀ p q,
      (∑ a, jNoise D0 η (segδ (SrcCol K π) r r' n) D a (zOf y) p *
          jNoise D0 η (segδ (SrcCol K π) r r' n) D a (zOf y) q = jΓ D0 η D (zOf y) p q) ∧
      ∑ a, jNoise D0 η (segδ (SrcCol K π) r r' n) D a (zOf y) p *
          star (jNoise D0 η (segδ (SrcCol K π) r r' n) D a (zOf y) q) = jΓ' D0 η D (zOf y) p q :=
  fun _ hy p q => ⟨sum_jNoise_mul hD0 hD (segδ_pos _ r r' n) (chartGood_seg hy) p q,
    sum_jNoise_mul_star hD0 hD (segδ_pos _ r r' n) (chartGood_seg hy) p q⟩

end BlockBand.SourceProcess.ComplexUnique
