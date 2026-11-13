module

public import BlockBand.Transmission.Bridge.Complete

/-!
# The passive initial scalar lemma: the unabsorbed fixed-moment clause

Bridge: `R_r = [(z - 𝕏_r)⁻¹]₀₀` (`portBlock_twoPortResolvent_zero_zero`,
under `z - (𝕏_r)₁₁` invertible, which holds on `PassiveSample` by `isUnit_farPencil`, a.s. by
`ae_passiveSample`), and the `r`-marginal of the grown path is `pathLaw W r b`
(`growthPathLaw_map_pathAt`, `r ≥ 1`).

Main results:
* `nearPortDistance`, `measurable_nearPortDistance`;
* `jetDistance0_pathX_eq`: `δ_{0,r}(ω) = nearPortDistance b E (pathAt W r ω)` on `PassiveSample`;
* `passiveInitialScalar_moment`: the `moment` field, from `MatchedTracesContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge
open scoped ENNReal NNReal Matrix

variable {W : ℕ}

/-- The near-port component of the matched-trace distance of a path sample,
`|W⁻¹ Tr [(z - 𝕏)⁻¹]₀₀ - a|` (the first argument of the max in `MatchedTracesContract.path`). -/
def nearPortDistance (b E : ℝ) {r : ℕ} (p : PathSample W r) : ℝ :=
  ‖blockTrace (pathPortResolvent b E p) 0 - matchedA E‖

theorem nearPortDistance_nonneg (b E : ℝ) {r : ℕ} (p : PathSample W r) :
    0 ≤ nearPortDistance b E p :=
  norm_nonneg _

theorem measurable_pathSchur (E : ℝ) (r : ℕ) :
    Measurable fun p : PathSample W r => pathSchur E p := by
  have hH : Measurable fun p : PathSample W r => pathMatrix p - (E : ℂ) • 1 := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [Matrix.sub_apply]
    exact (measurable_pathMatrix r).eval_matrix.sub measurable_const
  exact measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_matrix_conjTranspose' (measurable_pathPortCoupling r))
    (measurable_matrix_inv.comp hH)) (measurable_pathPortCoupling r)

theorem measurable_pathPortResolvent (b E : ℝ) (r : ℕ) :
    Measurable fun p : PathSample W r => pathPortResolvent b E p := by
  refine measurable_matrix_inv.comp (Measurable.of_eval_matrix _ fun x y => ?_)
  simp only [Matrix.sub_apply]
  exact measurable_const.sub (measurable_pathSchur E r).eval_matrix

theorem measurable_blockTrace_pathPortResolvent (b E : ℝ) (r : ℕ) (j : Fin 2) :
    Measurable fun p : PathSample W r => blockTrace (pathPortResolvent b E p) j := by
  simp only [blockTrace]
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ =>
    (measurable_pathPortResolvent b E r).eval_matrix)

theorem measurable_nearPortDistance (b E : ℝ) (r : ℕ) :
    Measurable fun p : PathSample W r => nearPortDistance b E p :=
  ((measurable_blockTrace_pathPortResolvent b E r 0).sub measurable_const).norm

theorem measurable_pathAt (W r : ℕ) : Measurable (pathAt W r) := by
  rw [pathAt_eq_pathOfPast]; exact (measurable_pathOfPast r).comp (measurable_pastCoords W r)

/-- `z - (𝕏_r)₁₁` is invertible along every passive sample (unabsorbed path). -/
theorem isUnit_far_pathSchur {b E : ℝ} {ω : GrowthPath W} (h : PassiveSample b E (fun _ => 0) ω)
    (r : ℕ) : IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) -
      portBlock (pathSchur E (pathAt W r ω)) 1 1) := by
  have hb := portBlock_absorbedPathSchur E (fun _ => 0) r ω 1 1
  rw [absorbedPathSchur_zero] at hb
  rw [hb]
  exact isUnit_farPencil h r

/-- **Identification**: along every passive sample, `δ_{0,r} = |W⁻¹ Tr R_r - a|` equals the
near-port distance of the length-`r` path sample. -/
theorem jetDistance0_pathX_eq {b E : ℝ} {ω : GrowthPath W} (h : PassiveSample b E (fun _ => 0) ω)
    (r : ℕ) : jetDistance0 b E (pathX b E W r ω) = nearPortDistance b E (pathAt W r ω) := by
  rw [jetDistance0, pathX_eq, ← portBlock_twoPortResolvent_zero_zero b E _ (isUnit_far_pathSchur h r)]
  rfl

/-- The `L^p` transfer: for `r ≥ 1`, bulk `E` and `b < 1`, the `L^p(growthPathLaw)` norm of
`δ_{0,r}` is the `L^p(pathLaw W r b)` norm of the near-port distance. -/
theorem eLpNorm_jetDistance0_eq {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {r : ℕ}
    (hr : 1 ≤ r) (q : ℝ≥0∞) :
    eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) q (growthPathLaw W b) =
      eLpNorm (fun p : PathSample W r => nearPortDistance b E p) q (pathLaw W r b) := by
  have hae : (fun ω => jetDistance0 b E (pathX b E W r ω)) =ᵐ[growthPathLaw W b]
      (fun p : PathSample W r => nearPortDistance b E p) ∘ pathAt W r :=
    (ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2).mono fun ω h =>
      jetDistance0_pathX_eq h r
  rw [eLpNorm_congr_ae hae, ← growthPathLaw_map_pathAt W b hr,
    eLpNorm_map_measure (measurable_nearPortDistance b E r).aestronglyMeasurable
      (measurable_pathAt W r).aemeasurable]

theorem bulk_bounds {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : -2 < E ∧ E < 2 :=
  ⟨by linarith [hE.1], by linarith [hE.2]⟩

/-- **`PassiveInitialScalarContract.moment`**, from `MatchedTracesContract` (field `path`). -/
theorem passiveInitialScalar_moment (hMT : MatchedTracesContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r →
        (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
            (growthPathLaw W b) ≤ ENNReal.ofReal (C / W) := by
  intro b hb hb' κ T p hκ hp
  obtain ⟨ε₀, C, hε₀, hC⟩ := hMT.path b hb hb' κ T hκ
  set q : ℝ := max p 2 with hq
  refine ⟨C * Real.sqrt q, ⌈q / ε₀⌉₊ + 1, ?_⟩
  intro W hW E hE r hr hrT
  have hW0 : 0 < W := by omega
  have hqW : q ≤ ε₀ * W := by
    have h1 : q / ε₀ ≤ (W : ℝ) := by
      have := Nat.le_ceil (q / ε₀)
      have h2 : ((⌈q / ε₀⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈q / ε₀⌉₊ ≤ W)
      linarith
    rwa [div_le_iff₀ hε₀, mul_comm] at h1
  have key := hC W hW0 q (le_max_right _ _) hqW r hr hrT E hE
  obtain ⟨hE1, hE2⟩ := bulk_bounds hκ hE
  rw [eLpNorm_jetDistance0_eq (by linarith) hE1 hE2 hr]
  calc eLpNorm (fun p : PathSample W r => nearPortDistance b E p) (ENNReal.ofReal p) (pathLaw W r b)
      ≤ eLpNorm (fun p : PathSample W r => nearPortDistance b E p) (ENNReal.ofReal q)
          (pathLaw W r b) :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ ≤ eLpNorm (fun ω => max ‖blockTrace (pathPortResolvent b E ω) 0 - matchedA E‖
          ‖blockTrace (pathPortResolvent b E ω) 1 - matchedA E‖) (ENNReal.ofReal q)
          (pathLaw W r b) := by
        refine eLpNorm_mono_real (measurable_nearPortDistance b E r).aestronglyMeasurable
          fun x => ?_
        rw [Real.norm_of_nonneg (nearPortDistance_nonneg b E x)]
        exact le_max_left _ _
    _ ≤ ENNReal.ofReal (C * Real.sqrt q / W) := key

end BlockBand.Transmission.PathScalar
