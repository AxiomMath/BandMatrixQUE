module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWitness

/-!
# Stop removal for the explicit witness: definitions and lemmas

Objects (one tag of birth index `k`, no interval source; law `growthPathLaw W b` for the path and
`circularVectorLaw` for the probe `h`):
* `tcw_F b e W l k m ω = E_h Z_{l;k}^m` and
  `tcw_H b e W l k m ω = (D₀/2) m(m-1) E_h[X^{m-2}(v*Pv)(v*P'v)]` (the probe averages at a fixed
  path), and `tcw_rem = F_{l+1} - F_l - W⁻¹H_l`, the one-step remainder of the monomial `X^m` at
  a fixed path.

## Main results

* `tcw_mem_alive_iff`: `ω ∈ {l < σ_K}` iff no `i ≤ l` with `i ≥ εW` and load `> K`.
* `tcw_mul_le_split`: `E[cS] ≤ L E c + E S²/L` (`0 ≤ c ≤ 1`, `S ≥ 0`).

The identity `ε_l(m) - d_l(m) = E tcw_rem` (`tcs_monoErr - tcw_deficit`) is proved in the sibling
module, `tcw_remainder_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-!
## Definitions
-/

/-- The one-tag source family (tag of birth index `k`). -/
abbrev tcw_tagFamily (k : ℕ) : Fin 1 → ℕ := fun _ => k

/-- No interval source. -/
abbrev tcw_noInterval : Fin 0 → ℝ → ℝ := fun a => a.elim0

/-- The survival event `{l < σ_K}` of the trace stop for the one-tag family. -/
def tcw_alive (b e : ℝ) (W k : ℕ) (K ε : ℝ) (l : ℕ) : Set (GrowthPath W) :=
  alive b e (tcw_tagFamily k) tcw_noInterval K ε W l

/-- `F_l(ω) = E_h Z_{l;k}^m` at a fixed path `ω`. -/
def tcw_F (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) : ℝ :=
  ∫ h, lmf_tagResponseClock b e W l k (ω, h) ^ m ∂circularVectorLaw (Fin 2 × Fin W)

/-- `H_l(ω) = (D₀/2) m(m-1) E_h[X^{m-2}(v*Pv)(v*P'v)]` at a fixed path `ω`, `D₀ = D₀(e)` (the
opposite-sign covariance term of the one-step expansion for the test `X^m`). -/
def tcw_H (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) : ℝ :=
  ∫ h, transportD0 b e / 2 * ((m : ℝ) * ((m : ℝ) - 1)) * tcw_X b e W l k (ω, h) ^ (m - 2) *
    tcw_G b e W l k (ω, h) ∂circularVectorLaw (Fin 2 × Fin W)

/-- The one-step remainder of the monomial `X^m` at a fixed path: `F_{l+1} - F_l - W⁻¹H_l`
(`r_l` for `φ = X^m`). -/
def tcw_rem (b e : ℝ) (W l k m : ℕ) (ω : GrowthPath W) : ℝ :=
  tcw_F b e W (l + 1) k m ω - tcw_F b e W l k m ω - (W : ℝ)⁻¹ * tcw_H b e W l k m ω

/-!
## The stop
-/

theorem tcw_mem_alive_iff {b e : ℝ} {nT nI : ℕ} {k : Fin nT → ℕ} {q : Fin nI → ℝ → ℝ} {K ε : ℝ}
    {W j : ℕ} {ω : GrowthPath W} :
    ω ∈ alive b e k q K ε W j ↔ ∀ i ≤ j, ¬ (ε * W ≤ i ∧ K < traceLoad b e k q W i ω) := by
  unfold alive traceStop
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h i hi hP
    have : (⨅ (i : ℕ) (_ : ε * W ≤ i ∧ K < traceLoad b e k q W i ω), (i : ℕ∞)) ≤ (i : ℕ∞) :=
      iInf₂_le i hP
    exact absurd (h.trans_le this) (not_lt.2 (by exact_mod_cast hi))
  · intro h
    refine lt_of_lt_of_le (b := ((j + 1 : ℕ) : ℕ∞)) (by exact_mod_cast Nat.lt_succ_self j) ?_
    refine le_iInf₂ fun i hP => ?_
    by_contra hlt
    have : i ≤ j := by
      have : (i : ℕ∞) < ((j + 1 : ℕ) : ℕ∞) := not_le.1 hlt
      exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
    exact h i this hP

theorem tcw_alive_succ_subset {b e : ℝ} {W k : ℕ} {K ε : ℝ} (l : ℕ) :
    tcw_alive b e W k K ε (l + 1) ⊆ tcw_alive b e W k K ε l := by
  intro ω hω
  unfold tcw_alive at *
  rw [tcw_mem_alive_iff] at *
  exact fun i hi => hω i (hi.trans (Nat.le_succ l))

/-- **Measurability of the nuclear norm**: `Tr|M| = Σ|λ_i|` (`nuclearNorm`, through
`charpoly.roots`) is Borel measurable on `2W × 2W` matrices. A deterministic qualitative fact
(the root multiset depends continuously on the matrix). It makes the survival events measurable
(`tcw_measurableSet_alive`). It is a hypothesis here; the route through
`tcx_measurableSet_alive_growthSigma` does not need it.
-/
def TcwNuclearNormMeasurable : Prop :=
  ∀ W : ℕ, Measurable (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => nuclearNorm M)

theorem tcw_measurable_pathCurrent (b e : ℝ) (W l : ℕ) :
    Measurable (fun ω : GrowthPath W => pathCurrent b e W l ω) := by
  have hc : Continuous (fun S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      Sᴴ * nearProjection W * S - nearProjection W) :=
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id).sub continuous_const
  exact hc.measurable.comp (tcw_measurable_scattering b e W l)

theorem tcw_measurable_traceLoad (hNuc : TcwNuclearNormMeasurable) (b e : ℝ) (W k i : ℕ) :
    Measurable (fun ω : GrowthPath W =>
      traceLoad b e (tcw_tagFamily k) tcw_noInterval W i ω) := by
  unfold traceLoad
  refine Measurable.add (Finset.measurable_sum _ fun a _ => ?_)
    ((hNuc W).comp (tcw_measurable_pathCurrent b e W i))
  rcases a with a | a
  · unfold sourceTrace
    have hm : Measurable (fun ω : GrowthPath W => (W : ℂ)⁻¹ • tagResponse b e W i k ω) :=
      (continuous_const_smul _).measurable.comp (tco_measurable_tagResponse b e W i k)
    exact Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp hm)
  · exact a.elim0

theorem tcw_measurableSet_alive (hNuc : TcwNuclearNormMeasurable) (b e : ℝ) (W k : ℕ) (K ε : ℝ)
    (l : ℕ) : MeasurableSet (tcw_alive b e W k K ε l) := by
  have : tcw_alive b e W k K ε l = ⋂ i ∈ Finset.range (l + 1),
      {ω | ¬ (ε * W ≤ i ∧ K < traceLoad b e (tcw_tagFamily k) tcw_noInterval W i ω)} := by
    ext ω
    simp only [tcw_alive, tcw_mem_alive_iff, Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨fun h i hi => h i (by omega), fun h i hi => h i (by omega)⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun i _ => ?_
  by_cases hi : ε * W ≤ i
  · simp only [hi, true_and]
    exact (measurableSet_lt measurable_const (tcw_measurable_traceLoad hNuc b e W k i)).compl
  · simp [hi]

/-!
## Abstract telescoping after the stop
-/

theorem tcw_sum_Ico_telescope (f : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ l ∈ Ico a b, (f (l + 1) - f l) = f b - f a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hb ih => rw [sum_Ico_succ_top hb, ih]; ring

/-- Telescoping against a monotone `[0,1]` weight: for `c` monotone, `c ≥ 0`, and `|f_i| ≤ S` on
`[a,b]`, `|Σ_{a≤l<b} c_l(f_{l+1} - f_l)| ≤ 4c_bS` (Abel summation, `tcs_abel_bound`). -/
theorem tcw_stop_abel (c f : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) (hc0 : ∀ l, 0 ≤ c l)
    (hmono : Monotone c) {S : ℝ} (hf : ∀ i, a ≤ i → i ≤ b → |f i| ≤ S) :
    |∑ l ∈ Ico a b, c l * (f (l + 1) - f l)| ≤ 4 * (c b * S) := by
  have hR : ∀ l', a ≤ l' → l' ≤ b → |∑ i ∈ Ico a l', (f (i + 1) - f i)| ≤ 2 * S := by
    intro l' h1 h2
    rw [tcw_sum_Ico_telescope f h1]
    have h3 := hf l' h1 h2
    have h4 := hf a le_rfl h
    calc |f l' - f a| ≤ |f l'| + |f a| := abs_sub _ _
      _ ≤ 2 * S := by linarith
  have hbv : ∑ l ∈ Ico a b, |c (l + 1) - c l| ≤ c b := by
    have e : ∀ l ∈ Ico a b, |c (l + 1) - c l| = c (l + 1) - c l := fun l _ =>
      abs_of_nonneg (sub_nonneg.2 (hmono (Nat.le_succ l)))
    rw [sum_congr rfl e, tcw_sum_Ico_telescope c h]
    linarith [hc0 a]
  have := tcs_abel_bound c (fun l => f (l + 1) - f l) h (le_of_eq (abs_of_nonneg (hc0 b))) hbv hR
  calc _ ≤ c b * (2 * S) + c b * (2 * S) := this
    _ = 4 * (c b * S) := by ring

/-- **The off-stop part**: with weights `c_l ∈ [0,1]` monotone in `l` (the indicator of
`{σ ≤ l}`), `|F_i| ≤ S` and `|g_l| ≤ κS` a.s.,
`|Σ_{a≤l<b} E[c_l(F_{l+1} - F_l - wg_l)]| ≤ (4 + (b-a)wκ) E[c_bS]`. -/
theorem tcw_offStop_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F g c : ℕ → Ω → ℝ) (S : Ω → ℝ) {a b : ℕ} (hab : a ≤ b) {w κ : ℝ} (hw : 0 ≤ w)
    (hc0 : ∀ l ω, 0 ≤ c l ω) (hc1 : ∀ l ω, c l ω ≤ 1)
    (hmono : ∀ ω, Monotone (fun l => c l ω)) (hcm : ∀ l, AEStronglyMeasurable (c l) μ)
    (hF : ∀ i, a ≤ i → i ≤ b → Integrable (F i) μ) (hg : ∀ l, a ≤ l → l < b → Integrable (g l) μ)
    (hS : Integrable S μ)
    (hFS : ∀ᵐ ω ∂μ, ∀ i, a ≤ i → i ≤ b → |F i ω| ≤ S ω)
    (hgS : ∀ᵐ ω ∂μ, ∀ l, a ≤ l → l < b → |g l ω| ≤ κ * S ω) :
    |∑ l ∈ Ico a b, ∫ ω, c l ω * (F (l + 1) ω - F l ω - w * g l ω) ∂μ| ≤
      (4 + (b - a : ℕ) * w * κ) * ∫ ω, c b ω * S ω ∂μ := by
  have hint : ∀ l ∈ Ico a b, Integrable (fun ω => c l ω * (F (l + 1) ω - F l ω - w * g l ω)) μ := by
    intro l hl
    obtain ⟨h1, h2⟩ := mem_Ico.1 hl
    refine Integrable.bdd_mul (c := 1) (((hF (l + 1) (by omega) (by omega)).sub
      (hF l h1 (by omega))).sub ((hg l h1 h2).const_mul w)) (hcm l)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 l ω)]; exact hc1 l ω
  have hcS : Integrable (fun ω => c b ω * S ω) μ :=
    Integrable.bdd_mul (c := 1) hS (hcm b) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hc0 b ω)]; exact hc1 b ω)
  rw [← integral_finsetSum _ hint, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae (integrable_finsetSum _ hint).abs
    (hcS.const_mul _) ?_)
  filter_upwards [hFS, hgS] with ω hFω hgω
  have hS0 : 0 ≤ S ω := (abs_nonneg _).trans (hFω a le_rfl hab)
  have e : ∑ l ∈ Ico a b, c l ω * (F (l + 1) ω - F l ω - w * g l ω) =
      ∑ l ∈ Ico a b, c l ω * (F (l + 1) ω - F l ω) - w * ∑ l ∈ Ico a b, c l ω * g l ω := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun l _ => by ring
  have h1 := tcw_stop_abel (fun l => c l ω) (fun i => F i ω) hab (fun l => hc0 l ω) (hmono ω) hFω
  have h2 : |∑ l ∈ Ico a b, c l ω * g l ω| ≤ (b - a : ℕ) * (κ * (c b ω * S ω)) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ l ∈ Ico a b, |c l ω * g l ω| ≤ ∑ l ∈ Ico a b, κ * (c b ω * S ω) := by
          refine sum_le_sum fun l hl => ?_
          obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
          rw [abs_mul, abs_of_nonneg (hc0 l ω)]
          have hcl : c l ω ≤ c b ω := hmono ω hl2.le
          calc c l ω * |g l ω| ≤ c b ω * (κ * S ω) :=
                mul_le_mul hcl (hgω l hl1 hl2) (abs_nonneg _) ((hc0 l ω).trans hcl)
            _ = κ * (c b ω * S ω) := by ring
      _ = (b - a : ℕ) * (κ * (c b ω * S ω)) := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcb : 0 ≤ c b ω * S ω := mul_nonneg (hc0 b ω) hS0
  rw [e]
  calc |∑ l ∈ Ico a b, c l ω * (F (l + 1) ω - F l ω) - w * ∑ l ∈ Ico a b, c l ω * g l ω|
      ≤ |∑ l ∈ Ico a b, c l ω * (F (l + 1) ω - F l ω)| +
          |w * ∑ l ∈ Ico a b, c l ω * g l ω| := abs_sub _ _
    _ ≤ 4 * (c b ω * S ω) + w * ((b - a : ℕ) * (κ * (c b ω * S ω))) := by
        rw [abs_mul, abs_of_nonneg hw]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hw)
    _ = (4 + (b - a : ℕ) * w * κ) * (c b ω * S ω) := by ring

/-- `cS ≤ Lc + S²/L` for `0 ≤ c ≤ 1`, `S ≥ 0`, `L > 0`. -/
theorem tcw_mul_le_split {c S L : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hS : 0 ≤ S) (hL : 0 < L) :
    c * S ≤ L * c + S ^ 2 / L := by
  rcases le_or_gt S L with h | h
  · have : 0 ≤ S ^ 2 / L := by positivity
    nlinarith
  · have h1 : S ≤ S ^ 2 / L := by
      rw [le_div_iff₀ hL]; nlinarith
    nlinarith

end BlockBand.Endpoints
