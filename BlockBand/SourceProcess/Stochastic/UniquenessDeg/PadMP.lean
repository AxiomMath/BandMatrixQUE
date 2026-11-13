module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.Pad
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Exhaust
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The padded process solves the padded martingale problem

* `locallyLipschitzOn_padB`, `locallyLipschitzOn_padS`: padding preserves local Lipschitz
  continuity (Frobenius norm on matrices).
* **`isMPSolutionOn_pad`**: if `Y` solves the `(b, σσᵀ)` martingale problem in `W`, then
  `padV ∘ Y` solves the `(padB b, padS σ (padS σ)ᵀ)` martingale problem in `padW W`, on the same
  filtered space (interior domains `W''` of `padW W` slice to interior domains `padV⁻¹' W''` of
  `W`, with the same exit times; the padded coordinates and their brackets vanish).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d m : ℕ}

theorem locallyLipschitzOn_comp {α β γ δ : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] [PseudoEMetricSpace δ] {L : γ → δ} {f : β → γ} {g : α → β}
    {s : Set α} {t : Set β} {KL Kg : ℝ≥0} (hL : LipschitzWith KL L) (hf : LocallyLipschitzOn t f)
    (hg : LipschitzWith Kg g) (hst : MapsTo g s t) :
    LocallyLipschitzOn s fun x => L (f (g x)) := by
  intro x hx
  obtain ⟨K, u, hu, hfu⟩ := hf (hst hx)
  refine ⟨KL * (K * Kg), s ∩ g ⁻¹' u, inter_mem self_mem_nhdsWithin
    ((hg.continuous.continuousWithinAt.tendsto_nhdsWithin hst) hu), ?_⟩
  exact hL.comp_lipschitzOnWith (hfu.comp hg.lipschitzOnWith fun y hy => hy.2)

theorem padV_sub (x y : Fin d → ℝ) : padV (m := m) (x - y) = padV x - padV y := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;> simp

theorem lipschitzWith_padV : LipschitzWith 1 (padV (d := d) (m := m)) := by
  refine LipschitzWith.mk_one fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← padV_sub]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i
  · rw [padV_left]; exact norm_le_pi_norm _ i
  · rw [padV_right, norm_zero]; exact norm_nonneg _

theorem lipschitzWith_prj : LipschitzWith 1 (prj (d := d) (m := m)) :=
  LipschitzWith.mk_one fun x y => by
    rw [dist_eq_norm, dist_eq_norm]; exact norm_prj_le (x - y)

theorem padM_sub (A B : Matrix (Fin d) (Fin m) ℝ) : padM (A - B) = padM A - padM B := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun l => ?_) j <;> simp [padM]

theorem norm_padM (A : Matrix (Fin d) (Fin m) ℝ) : ‖padM A‖ = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  congr 1
  simp [padM, Fin.sum_univ_add]

theorem lipschitzWith_padM : LipschitzWith 1 (padM (d := d) (m := m)) :=
  LipschitzWith.mk_one fun A B => by
    rw [dist_eq_norm, dist_eq_norm, ← padM_sub, norm_padM]

theorem locallyLipschitzOn_padB {b : (Fin d → ℝ) → Fin d → ℝ} {U : Set (Fin d → ℝ)}
    (hb : LocallyLipschitzOn U b) : LocallyLipschitzOn (prj (m := m) ⁻¹' U) (padB b) :=
  locallyLipschitzOn_comp lipschitzWith_padV hb lipschitzWith_prj fun _ h => h

theorem locallyLipschitzOn_padS {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ}
    {U : Set (Fin d → ℝ)} (hσ : LocallyLipschitzOn U σ) :
    LocallyLipschitzOn (prj (m := m) ⁻¹' U) (padS σ) :=
  locallyLipschitzOn_comp lipschitzWith_padM hσ lipschitzWith_prj fun _ h => h

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem mpComp_pad_left (b : (Fin d → ℝ) → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (i : Fin d) :
    mpCompensated (padB b) (fun t ω => padV (m := m) (Y t ω)) (Fin.castAdd m i) =
      mpCompensated b Y i := by
  funext t ω
  simp [mpCompensated, padB]

omit [MeasurableSpace Ω] in
theorem mpComp_pad_right (b : (Fin d → ℝ) → Fin d → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) (k : Fin m) :
    mpCompensated (padB b) (fun t ω => padV (m := m) (Y t ω)) (Fin.natAdd d k) = 0 := by
  funext t ω
  simp [mpCompensated, padB]

/-- **The padded process solves the padded martingale problem.** -/
theorem isMPSolutionOn_pad {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {b : (Fin d → ℝ) → Fin d → ℝ} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ}
    {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : IsMPSolutionOn Q 𝓖 b (fun y => σ y * (σ y).transpose) W Y) :
    IsMPSolutionOn Q 𝓖 (padB b) (fun z => padS σ z * (padS σ z).transpose) (padW W)
      (fun t ω => padV (m := m) (Y t ω)) := by
  refine ⟨fun t => continuous_padV.comp_stronglyMeasurable (hY.adapted t), ?_, ?_, ?_⟩
  · filter_upwards [hY.continuous] with ω hω using continuous_padV.comp hω
  · intro W'' hW'' i
    refine Fin.addCases (fun i => ?_) (fun k => ?_) i
    · obtain ⟨N, hN, hNe⟩ := hY.drift _ (isInteriorDomain_slice hW'') i
      refine ⟨N, hN, fun t => ?_⟩
      rw [mpComp_pad_left]
      exact hNe t
    · refine ⟨0, martingale_zero ℝ 𝓖 Q, fun t => ae_of_all _ fun ω => ?_⟩
      rw [mpComp_pad_right]
      rfl
  · intro W'' hW'' i j
    have hzero : ∀ i j, (∀ t ω, (fun t ω => mpCompensated (padB b) (fun t ω => padV (m := m) (Y t ω)) i t ω *
        mpCompensated (padB b) (fun t ω => padV (m := m) (Y t ω)) j t ω -
        ∫ s in Ioc (0 : ℝ) t, (padS σ (padV (Y s.toNNReal ω)) *
          (padS σ (padV (Y s.toNNReal ω))).transpose) i j) t ω = 0) →
        ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] stoppedProcess (fun t ω =>
          mpCompensated (padB b) (fun t ω => padV (m := m) (Y t ω)) i t ω *
          mpCompensated (padB b) (fun t ω => padV (m := m) (Y t ω)) j t ω -
          ∫ s in Ioc (0 : ℝ) t, (padS σ (padV (Y s.toNNReal ω)) *
            (padS σ (padV (Y s.toNNReal ω))).transpose) i j)
          (exitTimeFrom W'' fun t ω => padV (Y t ω)) t := fun i j h =>
      ⟨0, martingale_zero ℝ 𝓖 Q, fun t => ae_of_all _ fun ω => (h _ ω).symm⟩
    refine Fin.addCases (fun i => ?_) (fun k => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · obtain ⟨N, hN, hNe⟩ := hY.bracket _ (isInteriorDomain_slice hW'') i j
      refine ⟨N, hN, fun t => ?_⟩
      simp only [mpComp_pad_left, padS, prj_padV, padM_cov_left]
      exact hNe t
    · exact hzero _ _ fun t ω => by simp [mpComp_pad_right, padS, padM_cov_right']
    · exact hzero _ _ fun t ω => by simp [mpComp_pad_right, padS, padM_cov_right]
    · exact hzero _ _ fun t ω => by simp [mpComp_pad_right, padS, padM_cov_right]

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
