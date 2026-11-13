module

public import BlockBand.Transmission.LawFinite.CorePoint

/-!
# One fresh layer of the finite core: `q₊/W` bounded below in probability

Hypothesis `PassiveBoundsStatement` (only its `moments` clause, for `‖K𝒢₁₁‖`).

**`fresh_core_step`**: `b, κ, δ, a₀, ξ` first; then `a₁ > 0`, `W₀`; for `W ≥ W₀`,
`E ∈ bulkInterval κ` and every passive `X` with `‖X‖ ≤ ξ` and `q(X) ≥ a₀W`,
`P(q(X₊) < a₁W) ≤ δ` under one fresh layer. Proof: `core_point` on the good event
`‖A‖ ≤ α`, `‖B‖ ≤ β`, `‖K𝒢₁₁‖ ≤ γ`, `#{s_i(B)² < h²} ≤ εW` (A Hermitian, B invertible, the Ward
identity `Q₊ = L*QL`, all a.s.); Markov at `p = 1` for the norms (`gue_moment`,
`ginibre_moment`, the `moments` clause of `PassiveBoundsStatement`) and `smallFraction_prob_le`
with `log(1/h²) = 2t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

variable {W : ℕ}

/-- Markov at `p = 1` from an `L¹` bound. -/
theorem markov_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : ∀ ω, 0 ≤ f ω) {C d : ℝ} (hd : 0 < d) (hC : 0 ≤ C)
    (hm : eLpNorm f (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal C) :
    μ {ω | d < f ω} ≤ ENNReal.ofReal (C / d) := by
  have h := PathScalar.markov_ofReal μ hf one_pos hd hC hm
  simp only [Real.rpow_one] at h
  refine h.trans (le_of_eq ?_)
  congr 1; field_simp

theorem four_quarters (δ : ℝ) (hδ : 0 ≤ δ) :
    ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) +
      ENNReal.ofReal (δ / 4) = ENNReal.ofReal δ := by
  have h4 : 0 ≤ δ / 4 := by positivity
  rw [← ENNReal.ofReal_add h4 h4, ← ENNReal.ofReal_add (by positivity) h4,
    ← ENNReal.ofReal_add (by positivity) h4]
  congr 1; ring

/-- `C/(4C/δ + 1) ≤ δ/4`. -/
theorem quarter_bound {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) : C / (4 * C / δ + 1) ≤ δ / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : δ / 4 * (4 * C / δ + 1) = C + δ / 4 := by field_simp
  rw [this]; linarith

/-- `C/(ε·2t) ≤ δ/4` for `t = 2C'/(εδ) + 1`, `C ≤ C'`, `0 ≤ C'`. -/
theorem log_quarter_bound {C C' ε δ : ℝ} (hC : C ≤ C') (hC' : 0 ≤ C') (hε : 0 < ε) (hδ : 0 < δ) :
    C / (ε * (2 * (2 * C' / (ε * δ) + 1))) ≤ δ / 4 := by
  rw [div_le_iff₀ (by positivity)]
  have : δ / 4 * (ε * (2 * (2 * C' / (ε * δ) + 1))) = C' + ε * δ / 2 := by field_simp; ring
  rw [this]; nlinarith [mul_pos hε hδ]

theorem eps_gamma_le {a₀ Γ : ℝ} (ha : 0 < a₀) (hΓ : 0 ≤ Γ) : a₀ / (4 * (Γ + 1)) * Γ ≤ a₀ / 4 := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem core_final {q qp F₀ a₀ W mΓ : ℝ} (hF : 0 < F₀) (hpt : q ≤ F₀ ^ 2 * qp + q / 4 + mΓ)
    (hm : mΓ ≤ q / 4) (hq : a₀ * W ≤ q) (h0 : 0 ≤ a₀ * W) : a₀ / (4 * F₀ ^ 2) * W ≤ qp := by
  have hF2 : 0 < F₀ ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The good sample: `q(X₊) ≥ a₀W/(4F₀²)`. -/
theorem core_good {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0))
    (hQ' : passiveQ b E (freshSchur E X ω) =
      (freshL b E X ω)ᴴ * passiveQ b E X * freshL b E X ω)
    {h Li p₀ β ξ γ ε a₀ : ℝ} (hh : 0 < h) (hz : ‖boundaryZ b E‖ ≤ 3) (hLi : (etaZ b E)⁻¹ ≤ Li)
    (hp : ‖ω.1 0‖ + |E| + ‖X‖ ≤ p₀) (hβ : ‖ω.2 0 0‖ ≤ β) (hξ : ‖X‖ ≤ ξ)
    (hγ : ‖kG11 E (boundaryZ b E) X ω‖ ≤ γ) (hΓ0 : 0 ≤ p₀ * Li * (Li ^ 2 * ξ) * γ)
    (hm : (smallSingularCount (h ^ 2) (ω.2 0 0) : ℝ) ≤ ε * W)
    (hεΓ : ε * (p₀ * Li * (Li ^ 2 * ξ) * γ) ≤ a₀ / 4) (hq : a₀ * W ≤ passiveMass b E X)
    (h0 : 0 ≤ a₀ * W) (hF₀ : 0 < (β + 3 * h⁻¹ * p₀) * Li + 1) :
    a₀ / (4 * ((β + 3 * h⁻¹ * p₀) * Li + 1) ^ 2) * W ≤ passiveMass b E (freshSchur E X ω) := by
  have hpt := core_point hb0 hb h1 h2 hY hA hB hh hz hLi hp hβ hξ hγ
  have hqp : passiveMass b E (freshSchur E X ω) =
      ((freshL b E X ω)ᴴ * passiveQ b E X * freshL b E X ω).trace.re := by
    rw [passiveMass, hQ']
  rw [← hqp] at hpt
  refine core_final hF₀ hpt ?_ hq h0
  calc (smallSingularCount (h ^ 2) (ω.2 0 0) : ℝ) * (p₀ * Li * (Li ^ 2 * ξ) * γ)
      ≤ ε * W * (p₀ * Li * (Li ^ 2 * ξ) * γ) := mul_le_mul_of_nonneg_right hm hΓ0
    _ = ε * (p₀ * Li * (Li ^ 2 * ξ) * γ) * W := by ring
    _ ≤ a₀ / 4 * W := mul_le_mul_of_nonneg_right hεΓ (Nat.cast_nonneg _)
    _ ≤ _ := by linarith

/-- **One fresh layer keeps `q/W` bounded below in probability, uniformly in the passive input
of bounded norm**. `b, κ, δ, a₀, ξ` first; then `a₁ > 0` and `W₀`; for `W ≥ W₀`,
`E ∈ bulkInterval κ` and every passive `X` with `‖X‖ ≤ ξ` and `q(X) ≥ a₀W`:
`P(q(X₊) < a₁W) ≤ δ`. Hypothesis: `PassiveBoundsStatement` (only `moments`). -/
theorem fresh_core_step (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) {δ a₀ ξ : ℝ} (hδ : 0 < δ) (ha₀ : 0 < a₀) (hξ : 0 ≤ ξ) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ‖X‖ ≤ ξ →
        a₀ * W ≤ passiveMass b E X →
          freshLaw W b {ω | passiveMass b E (freshSchur E X ω) < a₁ * W} ≤
            ENNReal.ofReal δ := by
  obtain ⟨CA, hCA0, hCA⟩ := blockA_mom hb (p := 1) le_rfl
  obtain ⟨CB, hCB0, hCB⟩ := bondB_mom hb0 (p := 1) le_rfl
  obtain ⟨CG, WG, hCG⟩ := hA.moments b hb0 hb κ hκ 1 le_rfl
  obtain ⟨Cs, hCs⟩ := smallFraction_prob_le ginibreSmallSingularFraction_holds hb0 hb
  set CG' := max CG 0
  set Cs' := max Cs 0
  set α := 4 * CA / δ + 1
  set β := 4 * CB / δ + 1
  set γ := 4 * CG' / δ + 1
  have hηL : 0 < PathScalar.etaLow b κ := PathScalar.etaLow_pos (by linarith) hκ
  set Li := (PathScalar.etaLow b κ)⁻¹
  have hLi0 : 0 < Li := inv_pos.mpr hηL
  set p₀ := α + 2 + ξ
  set Γ := p₀ * Li * (Li ^ 2 * ξ) * γ
  have hα0 : 0 < α := by positivity
  have hβ0 : 0 < β := by positivity
  have hγ0 : 0 < γ := by positivity
  have hp₀ : 0 < p₀ := by positivity
  have hΓ0 : 0 ≤ Γ := by positivity
  set ε := a₀ / (4 * (Γ + 1))
  have hε : 0 < ε := by positivity
  set t := 2 * Cs' / (ε * δ) + 1
  have ht : 0 < t := by positivity
  set h := Real.exp (-t)
  have hh : 0 < h := Real.exp_pos _
  set F₀ := (β + 3 * h⁻¹ * p₀) * Li + 1
  have hF₀ : 0 < F₀ := by positivity
  refine ⟨a₀ / (4 * F₀ ^ 2), by positivity, max WG 1, fun W hW E hE X hY hXn hq => ?_⟩
  have hWG : WG ≤ W := le_of_max_le_left hW
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have h1' : -2 < E := by linarith [hE.1]
  have h2' : E < 2 := by linarith [hE.2]
  have hzD : boundaryZ b E ∈ paramDisk b E := Metric.mem_closedBall_self
    (by have := PassiveCovariance.etaZ_pos b E (by linarith) h1' h2'; positivity)
  obtain ⟨-, hz3, h1, h2⟩ := disk_bounds hb0 hb hκ hE hzD
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (PathScalar.etaLow_le (by linarith) hκ hE)
  have hE2 : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  set μ := freshLaw W b
  -- the four bad events
  set T₁ := {ω : LayerSample W .oneBlockOnePort | α < ‖ω.1 0‖}
  set T₂ := {ω : LayerSample W .oneBlockOnePort | β < ‖ω.2 0 0‖}
  set T₃ := {ω : LayerSample W .oneBlockOnePort | γ < ‖kG11 E (boundaryZ b E) X ω‖}
  set T₄ := {ω : LayerSample W .oneBlockOnePort |
    ε * W < (smallSingularCount (h ^ 2) (ω.2 0 0) : ℝ)}
  have hT₁ : μ T₁ ≤ ENNReal.ofReal (δ / 4) := by
    refine (markov_one (fun _ => norm_nonneg _) hα0 hCA0 (hCA W hW1).2).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact quarter_bound hCA0 hδ
  have hT₂ : μ T₂ ≤ ENNReal.ofReal (δ / 4) := by
    refine (markov_one (fun _ => norm_nonneg _) hβ0 hCB0 (hCB W hW1).2).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact quarter_bound hCB0 hδ
  have hT₃ : μ T₃ ≤ ENNReal.ofReal (δ / 4) := by
    obtain ⟨-, -, hk, -⟩ := hCG W hWG E hE (boundaryZ b E) hzD X hY
    refine (markov_one (fun _ => norm_nonneg _) hγ0 (le_max_right CG 0)
      (hk.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact quarter_bound (le_max_right CG 0) hδ
  have hT₄ : μ T₄ ≤ ENNReal.ofReal (δ / 4) := by
    have hm : Measurable fun ω : LayerSample W .oneBlockOnePort => ω.2 0 0 :=
      (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp measurable_snd)
    have hS : MeasurableSet {B : Matrix (Fin W) (Fin W) ℂ |
        ε * W < (smallSingularCount (h ^ 2) B : ℝ)} :=
      measurableSet_lt measurable_const
        (measurable_from_nat.comp (measurable_smallSingularCount (h ^ 2)))
    have hmap : μ T₄ = ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
        {B | ε * W < (smallSingularCount (h ^ 2) B : ℝ)} := by
      rw [← layerLaw_map_bond W b .oneBlockOnePort 0 0, Measure.map_apply hm hS]; rfl
    have hh2 : h ^ 2 = Real.exp (-(2 * t)) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have hh21 : h ^ 2 < 1 := by rw [hh2]; exact Real.exp_lt_one_iff.mpr (by linarith)
    have hlog : Real.log (h ^ 2)⁻¹ = 2 * t := by
      rw [hh2, ← Real.exp_neg, neg_neg, Real.log_exp]
    rw [hmap]
    refine (hCs W (by omega) (h ^ 2) ε (by positivity) hh21 hε).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [hlog]
    exact log_quarter_bound (le_max_left _ _) (le_max_right _ _) hε hδ
  -- the good event
  have hgood : ∀ᵐ ω ∂μ, (ω.1 0).IsHermitian ∧ IsUnit (ω.2 0 0) ∧
      passiveQ b E (freshSchur E X ω) = (freshL b E X ω)ᴴ * passiveQ b E X * freshL b E X ω := by
    filter_upwards [PathScalar.ae_layer_herm (W := W) b,
      Bridge.ae_isUnit_layerLaw_bond hb0 hW1 .oneBlockOnePort,
      SourceMixing.ae_passiveQ_freshSchur hb0 hb hW1 h1 h2 hY] with ω hA' hB' hQ'
    exact ⟨hA', hB' 0 0, hQ'⟩
  have hsub : {ω | passiveMass b E (freshSchur E X ω) < a₀ / (4 * F₀ ^ 2) * W} ≤ᵐ[μ]
      (T₁ ∪ T₂ ∪ T₃ ∪ T₄ : Set _) := by
    filter_upwards [hgood] with ω ⟨hA', hB', hQ'⟩ hlt
    by_contra hn
    simp only [Set.mem_union, T₁, T₂, T₃, T₄, Set.mem_ofPred_eq, not_or, not_lt] at hn
    obtain ⟨⟨⟨hα, hβ⟩, hγ⟩, hm⟩ := hn
    have hgd := core_good hb0 hb h1 h2 hY hA' hB' hQ' hh hz3 hLi
      (show ‖ω.1 0‖ + |E| + ‖X‖ ≤ p₀ by simp only [p₀]; linarith) hβ hXn hγ hΓ0 hm
      (eps_gamma_le ha₀ hΓ0) hq (by positivity) hF₀
    exact absurd hlt (not_lt.mpr hgd)
  calc μ {ω | passiveMass b E (freshSchur E X ω) < a₀ / (4 * F₀ ^ 2) * W}
      ≤ μ (T₁ ∪ T₂ ∪ T₃ ∪ T₄) := measure_mono_ae hsub
    _ ≤ μ T₁ + μ T₂ + μ T₃ + μ T₄ := by
        refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
    _ ≤ ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) +
          ENNReal.ofReal (δ / 4) := by gcongr
    _ = ENNReal.ofReal δ := four_quarters δ hδ.le

end BlockBand.Transmission.LawFinite
