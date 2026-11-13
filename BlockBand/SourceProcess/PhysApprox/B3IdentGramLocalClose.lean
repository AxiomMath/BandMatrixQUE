module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalBox

/-!
# Uniform continuity on the boxes

States carry no metric; `eZ` embeds them by their entries into the normed space
`(GIdx → ℂ)³` (inverse `gZ`). `eDist z' z` is the sum of the entry distances.
* **`exists_close_F`**: a continuous `F` with `|F| ≤ C_F` at both states satisfies
  `|F z' − F z| ≤ ε + K₀ eDist(z', z)` for `z` in a box (`K₀ = 2C_F/δ`);
* **`exists_close_Λ`**: `Λ(J, ·)` moves by `≤ ε` under a perturbation of `x` by `≤ δ`, uniformly
  over the jump values and a box.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

variable {K np : ℕ}

/-- The entry embedding. -/
def eZ (z : ZSt K np) : (GIdx K np → ℂ) × (GIdx K np → ℂ) × (GIdx K np → ℂ) :=
  (fun c => gramEntry c z.1, z.2.1, fun c => gramEntry c z.2.2)

/-- Its inverse. -/
def gZ (p : (GIdx K np → ℂ) × (GIdx K np → ℂ) × (GIdx K np → ℂ)) : ZSt K np :=
  (gramOfEntries p.1, p.2.1, gramOfEntries p.2.2)

theorem gZ_eZ (z : ZSt K np) : gZ (eZ z) = z := by
  simp [gZ, eZ, gramOfEntries_entries]

theorem continuous_gZ : Continuous (gZ (K := K) (np := np)) :=
  (continuous_gramOfEntries.comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_gramOfEntries.comp (continuous_snd.comp continuous_snd)))

/-- The sum of the entry distances. -/
def eDist (z' z : ZSt K np) : ℝ :=
  ∑ c, ‖gramEntry c z'.1 - gramEntry c z.1‖ + ∑ e, ‖z'.2.1 e - z.2.1 e‖ +
    ∑ c, ‖gramEntry c z'.2.2 - gramEntry c z.2.2‖

theorem eDist_nonneg (z' z : ZSt K np) : 0 ≤ eDist z' z := by
  unfold eDist; positivity

theorem norm_pi_le_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) : ‖f‖ ≤ ∑ i, ‖f i‖ :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i =>
    Finset.single_le_sum (f := fun i => ‖f i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem dist_eZ_le (z' z : ZSt K np) : dist (eZ z') (eZ z) ≤ eDist z' z := by
  rw [dist_eq_norm, Prod.norm_def, Prod.norm_def]
  have h1 := norm_pi_le_sum ((eZ z' - eZ z).1)
  have h2 := norm_pi_le_sum ((eZ z' - eZ z).2.1)
  have h3 := norm_pi_le_sum ((eZ z' - eZ z).2.2)
  simp only [eZ, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply] at h1 h2 h3
  have := eDist_nonneg z' z
  simp only [eDist] at this ⊢
  refine max_le (h1.trans (by
    have := Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => norm_nonneg (z'.2.1 e - z.2.1 e)
    have := Finset.sum_nonneg fun c (_ : c ∈ Finset.univ) =>
      norm_nonneg (gramEntry c z'.2.2 - gramEntry c z.2.2)
    linarith)) (max_le (h2.trans (by
    have := Finset.sum_nonneg fun c (_ : c ∈ Finset.univ) =>
      norm_nonneg (gramEntry c z'.1 - gramEntry c z.1)
    have := Finset.sum_nonneg fun c (_ : c ∈ Finset.univ) =>
      norm_nonneg (gramEntry c z'.2.2 - gramEntry c z.2.2)
    linarith)) (h3.trans (by
    have := Finset.sum_nonneg fun c (_ : c ∈ Finset.univ) =>
      norm_nonneg (gramEntry c z'.1 - gramEntry c z.1)
    have := Finset.sum_nonneg fun e (_ : e ∈ Finset.univ) => norm_nonneg (z'.2.1 e - z.2.1 e)
    linarith)))

theorem norm_eZ_le {B : ℝ} (hB : 0 ≤ B) {z : ZSt K np} (hz : z ∈ kBox B) : ‖eZ z‖ ≤ B := by
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le ((pi_norm_le_iff_of_nonneg hB).2 hz.1)
    (max_le ((pi_norm_le_iff_of_nonneg hB).2 hz.2.1) ((pi_norm_le_iff_of_nonneg hB).2 hz.2.2))

/-- **Closeness for `F`.** -/
theorem exists_close_F {F : ZSt K np → ℂ} (hF : Continuous F) {B : ℝ} (hB : 0 ≤ B) {CF : ℝ}
    (hCF : 0 ≤ CF) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ z ∈ kBox (K := K) (np := np) B, ∀ z' : ZSt K np, ‖F z‖ ≤ CF →
      ‖F z'‖ ≤ CF → ‖F z' - F z‖ ≤ ε + K₀ * eDist z' z := by
  have hc : Continuous fun p => F (gZ (K := K) (np := np) p) := hF.comp continuous_gZ
  have hU := (isCompact_closedBall (0 : (GIdx K np → ℂ) × (GIdx K np → ℂ) × (GIdx K np → ℂ))
    (B + 1)).uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.1 hU ε hε
  set δ' := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  refine ⟨2 * CF / δ', by positivity, fun z hz z' h1 h2 => ?_⟩
  by_cases hd : eDist z' z < δ'
  · have hzB : eZ z ∈ Metric.closedBall (0 : (GIdx K np → ℂ) × (GIdx K np → ℂ) × (GIdx K np → ℂ))
        (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [norm_eZ_le hB hz]
    have hdz := (dist_eZ_le z' z).trans_lt hd
    have hz'B : eZ z' ∈ Metric.closedBall (0 : (GIdx K np → ℂ) × (GIdx K np → ℂ) ×
        (GIdx K np → ℂ)) (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have := norm_eZ_le hB hz
      have h3 : ‖eZ z'‖ ≤ ‖eZ z‖ + dist (eZ z') (eZ z) := by
        rw [dist_eq_norm]; exact norm_le_insert' _ _
      linarith [min_le_right δ 1]
    have := hδU _ hz'B _ hzB (hdz.trans_le (min_le_left _ _))
    rw [dist_eq_norm, gZ_eZ, gZ_eZ] at this
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * CF / δ') (eDist_nonneg z' z)]
  · rw [not_lt] at hd
    have : ‖F z' - F z‖ ≤ 2 * CF := (norm_sub_le _ _).trans (by linarith)
    have h4 : 2 * CF ≤ 2 * CF / δ' * eDist z' z := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ']
      exact mul_le_mul_of_nonneg_left hd (by positivity)
    linarith

/-- **Closeness for `Λ` under a perturbation of the drift coordinates.** -/
theorem exists_close_Λ {Λ : GSt K np × ZSt K np → ℂ} (hΛ : Continuous Λ) {b : ℝ}
    {m : Fin np → ℝ} {B : ℝ} (hB : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) B,
      ∀ ξ : GIdx K np → ℂ, (∀ e, ‖ξ e‖ ≤ δ) →
        ‖Λ (J, (z.1, fun e => z.2.1 e - ξ e, z.2.2)) - Λ (J, z)‖ ≤ ε := by
  have key : ∀ x : Fin np → Bool, ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ kBox (K := K) (np := np) B,
      ∀ ξ : GIdx K np → ℂ, (∀ e, ‖ξ e‖ ≤ δ) →
        ‖Λ (jSel b m x, (z.1, fun e => z.2.1 e - ξ e, z.2.2)) - Λ (jSel b m x, z)‖ ≤ ε := by
    intro x
    have hc : Continuous fun p => Λ (jSel (K := K) b m x, gZ (K := K) (np := np) p) :=
      hΛ.comp (continuous_const.prodMk continuous_gZ)
    have hU := (isCompact_closedBall (0 : (GIdx K np → ℂ) × (GIdx K np → ℂ) × (GIdx K np → ℂ))
      (B + 1)).uniformContinuousOn_of_continuous hc.continuousOn
    obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.1 hU ε hε
    refine ⟨min (δ / 2) 1, lt_min (half_pos hδ) one_pos, fun z hz ξ hξ => ?_⟩
    set z' : ZSt K np := (z.1, fun e => z.2.1 e - ξ e, z.2.2)
    have hξn : ‖ξ‖ ≤ min (δ / 2) 1 := (pi_norm_le_iff_of_nonneg (by positivity)).2 hξ
    have hd : dist (eZ z') (eZ z) ≤ ‖ξ‖ := by
      rw [dist_eq_norm, Prod.norm_def, Prod.norm_def]
      have e1 : (eZ z' - eZ z).1 = 0 := by funext c; simp [eZ, z']
      have e3 : (eZ z' - eZ z).2.2 = 0 := by funext c; simp [eZ, z']
      have e2 : (eZ z' - eZ z).2.1 = -ξ := by funext e; simp [eZ, z']
      rw [e1, e2, e3, norm_zero, norm_neg]
      exact max_le (norm_nonneg _) (max_le le_rfl (norm_nonneg _))
    have hzB : eZ z ∈ Metric.closedBall (0 : (GIdx K np → ℂ) × (GIdx K np → ℂ) ×
        (GIdx K np → ℂ)) (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]; linarith [norm_eZ_le hB hz]
    have hz'B : eZ z' ∈ Metric.closedBall (0 : (GIdx K np → ℂ) × (GIdx K np → ℂ) ×
        (GIdx K np → ℂ)) (B + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have := norm_eZ_le hB hz
      have h3 : ‖eZ z'‖ ≤ ‖eZ z‖ + dist (eZ z') (eZ z) := by
        rw [dist_eq_norm]; exact norm_le_insert' _ _
      linarith [min_le_right (δ / 2) 1]
    have := hδU _ hz'B _ hzB (hd.trans_lt (hξn.trans_lt ((min_le_left _ _).trans_lt
      (half_lt_self hδ))))
    rw [dist_eq_norm, gZ_eZ, gZ_eZ] at this
    exact this.le
  choose δx hδx hδU using key
  obtain ⟨x0, -, hx0⟩ := Finset.univ.exists_min_image δx Finset.univ_nonempty
  refine ⟨δx x0, hδx x0, ?_⟩
  rintro _ ⟨x, rfl⟩ z hz ξ hξ
  exact hδU x z hz ξ fun e => (hξ e).trans (hx0 x (Finset.mem_univ x))

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
