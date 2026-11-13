module

public import BlockBand.Endpoints.Transmission.AlongDefs
public import BlockBand.Transmission.LawDuality.FddMulti

/-!
# `W`-free multi-time uniqueness of ratio martingale processes

Two limit processes that solve the same ratio martingale problem, with the entrance condition and
locally bounded mean mass, have the same finite-dimensional distributions
(`fddUnique_of_ratioMP_free`).

Setting: `0 < b < 1/2`, `-2 < E < 2`, `IsAbsorptionProfile κ`, and two objects `(Ω₁, P₁, μ₁)`,
`(Ω₂, P₂, μ₂)`, each with `IsFiniteLimitProcess`, the ratio martingale
problem `LawDuality.IsRatioMartingale (transportD0 b E) E κ`, `LawDuality.HasRatioEntrance` and
`LawDuality.HasLocalMassBound`. No width `W`, no subsequence and no energy sequence appear.
The sample spaces may live in arbitrary (different) universes.

The proofs follow those for transmission sub-limits, with `IsTransmissionSubLimit` and the ratio
martingale problem replaced by `IsFiniteLimitProcess` and the three properties:
* `ratioDualLawValue_free` follows `LawDuality.ratioDualityPrinciple_holds`,
  with the sample space in an arbitrary universe instead of `Type`;
* `IsFiniteLimitProcess.measurable_fdd` follows `LawDuality.measurable_fdd`;
* `oneTimeLaw_of_ratioMP_free` follows `LawDuality.subLimit_map_eq`;
* `jointLaw_le_one_of_ratioMP_free` follows `LawDuality.subLimit_jointLaw_le_one`;
* `sameTilted_of_ratioMP_free` follows `LawDuality.subLimit_sameTilted`;
* `jointLaw_strictMono_of_ratioMP_free` follows `LawDuality.subLimit_jointLaw_strictMono`;
* `jointLawUnique_of_ratioMP_free` follows `LawDuality.subLimitJointLawUnique_of_ratioMP`;
* `fddUnique_of_ratioMP_free` follows `LawDuality.subLimitFddUnique_of_ratioMP` through
  `LawDuality.subLimitFddUnique_of_jointLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Dual
open scoped NNReal ENNReal BoundedContinuousFunction

universe u v

/-- **The dual identity for one ratio martingale process, in any universe**: the analogue of
`LawDuality.ratioDualityPrinciple_holds` with the sample space in an arbitrary universe. -/
theorem ratioDualLawValue_free {D0 : ℝ} (hD0 : 0 < D0) {E : ℝ} {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (hfin : IsFiniteLimitProcess P μ)
    (hM : IsRatioMartingale D0 E κ P μ) (hent : HasRatioEntrance P μ)
    (hmass : HasLocalMassBound P μ) {t : ℝ} (ht : 0 < t) {p : ℕ} {x y : Fin p → ℝ}
    (hxy : IsRatioParameter x y) :
    DualLawValue E κ t D0 x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) := by
  have := hfin.prob
  obtain ⟨μ', hmeas', hcont', hae⟩ := exists_continuous_version hfin.measurable hfin.continuous
  have hM' := isRatioMartingale_congr hae hM
  have hent' := hasRatioEntrance_congr hae hent
  have hmass' := hasLocalMassBound_congr hae hmass
  have hU : ∫ ω, transmissionRatio x y (μ t ω) ∂P = ∫ ω, transmissionRatio x y (μ' t ω) ∂P :=
    integral_congr_ae (by filter_upwards [hae] with ω hω; rw [hω])
  rw [hU]
  intro Ω' m' 𝓖 P' N X Y hD
  obtain ⟨N', X', Y', hD', hpath', hst', hae'⟩ := exists_normalized hxy hD
  have := hD'.prob
  rw [← dualTransform_congr hae' E κ t, dualTransform_eq_lt hD0 hxy hD' E κ ht]
  set k : ℝ → ℝ := fun v => absorptionRate E κ (t - v) with hkdef
  obtain ⟨Kκ, hKκ⟩ := hκ.2.2
  have hκc : Continuous κ := hκ.1
  have hhc := BlockBand.Transmission.DualBoundary.continuous_absorptionRate hκc E
  have hk : Continuous k := hhc.comp (continuous_const.sub continuous_id)
  have hh0 : ∀ u, 0 ≤ absorptionRate E κ u := fun u =>
    BlockBand.Transmission.DualBoundary.absorptionRate_nonneg hκ E u
  have hhC : ∀ u, |absorptionRate E κ u| ≤ BlockBand.Transmission.DualBoundary.rateBound E Kκ :=
    fun u => by
      rw [abs_of_nonneg (hh0 u)]
      exact BlockBand.Transmission.DualBoundary.absorptionRate_le hKκ E u
  have hk0 : ∀ v, 0 ≤ k v := fun v => hh0 _
  have hkC : ∀ v, k v ≤ BlockBand.Transmission.DualBoundary.rateBound E Kκ := fun v =>
    (le_abs_self _).trans (hhC _)
  have key : ∀ a0, 0 < a0 → a0 < t → ∫ ω, transmissionRatio x y (μ' t ω) ∂P =
      stripV P μ' a0 t P' k N' X' Y' (fun _ => ⊤) a0 (t - a0) := fun a0 ha0 hat =>
    ratio_eq_stripV_top hD' hpath' hk hk0 hmeas' hcont' ha0 hkC hκc hhC (fun v => rfl) hM'
      hmass' hxy hst' hat
  have hlim := tendsto_stripV_top (P := P) hD' hpath' hk hk0 hmeas' hent' ht
    (ae_dualExtinction_ne hD0 hxy hD' ht)
  have hconst : Tendsto (fun a0 => stripV P μ' a0 t P' k N' X' Y' (fun _ => ⊤) a0 (t - a0))
      (𝓝[>] 0) (𝓝 (∫ ω, transmissionRatio x y (μ' t ω) ∂P)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with a0 ha0 using key a0 ha0.1 ha0.2
  rw [tendsto_nhds_unique hconst hlim]
  refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
  by_cases hζ : dualExtinction N' ω' < ENNReal.ofReal t
  · simp only [hζ, ↓reduceIte]
    rw [killFac_top_eq k N' X' Y' ω' ht.le]
  · simp only [hζ, ↓reduceIte]

/-- Measurability of the finite-dimensional vector `ω ↦ (μ(τ_i)(ω))_i`.
A copy of
`LawDuality.measurable_fdd`.
-/
theorem IsFiniteLimitProcess.measurable_fdd {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsFiniteLimitProcess P μ) {k : ℕ}
    {τ : Fin k → ℝ} (hτ : ∀ i, 0 < τ i) : Measurable fun ω i => μ (τ i) ω :=
  measurable_pi_iff.2 fun i => h.measurable (τ i) (hτ i)

/-- The coordinate identity `(ν(σ_i))_i = snoc ((ν(σ_{castSucc i}))_i, ν(σ_last))`, stated
for one sample space (used twice, once per universe, in the induction step). -/
theorem fdd_eq_snoc_comp {Ω : Type u} {n : ℕ} (σ : Fin (n + 2) → ℝ)
    (ν : ℝ → Ω → FiniteMeasure unitInterval) :
    (fun ω i => ν (σ i) ω) = (fun q : (Fin (n + 1) → FiniteMeasure unitInterval) ×
      FiniteMeasure unitInterval => (Fin.snoc q.1 q.2 : Fin (n + 2) → FiniteMeasure unitInterval))
      ∘ fun ω => ((fun i => ν (σ (Fin.castSucc i)) ω), ν (σ (Fin.last (n + 1))) ω) :=
  funext fun ω => (Fin.snoc_init_self (fun i => ν (σ i) ω)).symm

section

variable {b E : ℝ} {κ : ℝ → ℝ} (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2)
  (hκ : IsAbsorptionProfile κ)
  {Ω₁ : Type u} {Ω₂ : Type v} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁}
  {P₂ : Measure Ω₂} {μ₁ : ℝ → Ω₁ → FiniteMeasure unitInterval}
  {μ₂ : ℝ → Ω₂ → FiniteMeasure unitInterval}
  (hf₁ : IsFiniteLimitProcess P₁ μ₁) (hM₁ : IsRatioMartingale (transportD0 b E) E κ P₁ μ₁)
  (hent₁ : HasRatioEntrance P₁ μ₁) (hmass₁ : HasLocalMassBound P₁ μ₁)
  (hf₂ : IsFiniteLimitProcess P₂ μ₂) (hM₂ : IsRatioMartingale (transportD0 b E) E κ P₂ μ₂)
  (hent₂ : HasRatioEntrance P₂ μ₂) (hmass₂ : HasLocalMassBound P₂ μ₂)
include hb hE1 hE2 hκ hf₁ hM₁ hent₁ hmass₁ hf₂ hM₂ hent₂ hmass₂

/-- **One-time uniqueness, `W`-free.** The one-time laws `P(μ_t ∈ ·)` (Giry σ-algebra) of the
two processes agree at every `t > 0`.
-/
theorem oneTimeLaw_of_ratioMP_free {t : ℝ} (ht : 0 < t) : P₁.map (μ₁ t) = P₂.map (μ₂ t) := by
  have := hf₁.prob
  have := hf₂.prob
  have hD0 := BlockBand.Transmission.DualBoundary.transportD0_pos hb hE1 hE2
  refine map_eq_of_sameRatioTransforms (hf₁.measurable t ht) (hf₂.measurable t ht) ?_
  intro p x y hxy
  exact dualLawValue_unique (hasDualDeletionProcess_transport hb hE1 hE2 hxy)
    (ratioDualLawValue_free hD0 hκ hf₁ hM₁ hent₁ hmass₁ ht hxy)
    (ratioDualLawValue_free hD0 hκ hf₂ hM₂ hent₂ hmass₂ ht hxy)

/-- **The cases `k ≤ 1`, `W`-free**: the analogue of `LawDuality.subLimit_jointLaw_le_one`. -/
theorem jointLaw_le_one_of_ratioMP_free {k : ℕ} (hk : k ≤ 1) {τ : Fin k → ℝ}
    (hτ : ∀ i, 0 < τ i) :
    P₁.map (fun ω i => μ₁ (τ i) ω) = P₂.map (fun ω i => μ₂ (τ i) ω) := by
  have := hf₁.prob
  have := hf₂.prob
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · have e1 : (fun ω i => μ₁ (τ i) ω) = fun _ => (fun i => i.elim0) :=
      funext fun _ => funext fun i => i.elim0
    have e2 : (fun ω i => μ₂ (τ i) ω) = fun _ => (fun i => i.elim0) :=
      funext fun _ => funext fun i => i.elim0
    rw [e1, e2, Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  · let ι : FiniteMeasure unitInterval → Fin 1 → FiniteMeasure unitInterval := fun ν _ => ν
    have hι : Measurable ι := measurable_pi_iff.2 fun _ => measurable_id
    have e1 : (fun ω i => μ₁ (τ i) ω) = ι ∘ μ₁ (τ 0) := by
      funext ω i; rw [Subsingleton.elim i 0]; rfl
    have e2 : (fun ω i => μ₂ (τ i) ω) = ι ∘ μ₂ (τ 0) := by
      funext ω i; rw [Subsingleton.elim i 0]; rfl
    rw [e1, e2, ← Measure.map_map hι (hf₁.measurable _ (hτ 0)),
      ← Measure.map_map hι (hf₂.measurable _ (hτ 0)),
      oneTimeLaw_of_ratioMP_free hb hE1 hE2 hκ hf₁ hM₁ hent₁ hmass₁ hf₂ hM₂ hent₂ hmass₂ (hτ 0)]

omit hent₁ hent₂ in

/-- **The induction step's input, `W`-free: tilted ratio transforms of `(Y, μ_t)` agree.**
A copy of `LawDuality.subLimit_sameTilted`: for sorted positive
times `σ_0 ≤ … ≤ σ_n < t`, equal joint laws of `Y = (μ_{σ_i})_i` give equal tilted ratio
transforms, by the conditional duality `integral_pastTest_mul_ratio` against one normalized
dual.
The entrance is not needed here.
-/
theorem sameTilted_of_ratioMP_free {n : ℕ} {σ : Fin (n + 1) → ℝ} (hpos : ∀ i, 0 < σ i)
    (hmono : Monotone σ) {t : ℝ} (hat : σ (Fin.last n) < t)
    (hIH : P₁.map (fun ω i => μ₁ (σ i) ω) = P₂.map (fun ω i => μ₂ (σ i) ω)) :
    SameTiltedRatioTransforms P₁ (fun ω i => μ₁ (σ i) ω) (μ₁ t) P₂ (fun ω i => μ₂ (σ i) ω)
      (μ₂ t) := by
  intro ψ hψ p x y hxy
  have := hf₁.prob
  have := hf₂.prob
  obtain ⟨Ω'', m'', 𝓖, P'', N, X, Y, hD⟩ := hasDualDeletionProcess_transport hb hE1 hE2 hxy
  obtain ⟨N', X', Y', hD', hpath', hst', -⟩ := exists_normalized hxy hD
  have hu : ∀ l, 0 < σ l ∧ σ l ≤ σ (Fin.last n) := fun l => ⟨hpos l, hmono (Fin.le_last l)⟩
  have c1 := integral_pastTest_mul_ratio ψ hκ hf₁.measurable hf₁.continuous hM₁ hmass₁ hψ
    (hpos _) hu hat hD' hpath' hst' hxy
  have c2 := integral_pastTest_mul_ratio ψ hκ hf₂.measurable hf₂.continuous hM₂ hmass₂ hψ
    (hpos _) hu hat hD' hpath' hst' hxy
  show ∫ ω, pastTest ψ μ₁ σ ω * transmissionRatio x y (μ₁ t ω) ∂P₁ =
    ∫ ω, pastTest ψ μ₂ σ ω * transmissionRatio x y (μ₂ t ω) ∂P₂
  rw [c1, c2]
  refine integral_congr_ae (ae_of_all _ fun ω'' => ?_)
  beta_reduce
  congr 1
  set G : (Fin (n + 1) → FiniteMeasure unitInterval) → ℝ := fun v =>
    ψ v * ratioStop (v (Fin.last n)) N' X' Y' (fun _ => ⊤) (t - σ (Fin.last n)) ω'' with hGdef
  have hG : Continuous G :=
    ψ.continuous.mul ((continuous_pathRatio_nu (hpath' ω'') _).comp (continuous_apply _))
  show ∫ ω, G (fun i => μ₁ (σ i) ω) ∂P₁ = ∫ ω, G (fun i => μ₂ (σ i) ω) ∂P₂
  rw [← integral_map (hf₁.measurable_fdd hpos).aemeasurable hG.aestronglyMeasurable, hIH,
    integral_map (hf₂.measurable_fdd hpos).aemeasurable hG.aestronglyMeasurable]

/-- **Joint laws at strictly increasing positive times agree, `W`-free.** A copy of
`LawDuality.subLimit_jointLaw_strictMono`.
-/
theorem jointLaw_strictMono_of_ratioMP_free : ∀ (n : ℕ) (σ : Fin n → ℝ), StrictMono σ →
    (∀ i, 0 < σ i) → P₁.map (fun ω i => μ₁ (σ i) ω) = P₂.map (fun ω i => μ₂ (σ i) ω) := by
  intro n
  induction n with
  | zero =>
    intro σ _ hpos
    exact jointLaw_le_one_of_ratioMP_free hb hE1 hE2 hκ hf₁ hM₁ hent₁ hmass₁ hf₂ hM₂ hent₂ hmass₂
      (Nat.zero_le 1) hpos
  | succ n ih =>
    intro σ hmono hpos
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact jointLaw_le_one_of_ratioMP_free hb hE1 hE2 hκ hf₁ hM₁ hent₁ hmass₁ hf₂ hM₂ hent₂
        hmass₂ le_rfl hpos
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set σ0 : Fin (n + 1) → ℝ := fun i => σ (Fin.castSucc i) with hσ0
    have hmono0 : StrictMono σ0 := hmono.comp Fin.strictMono_castSucc
    have hpos0 : ∀ i, 0 < σ0 i := fun i => hpos _
    have hIH := ih σ0 hmono0 hpos0
    have hat : σ0 (Fin.last n) < σ (Fin.last (n + 1)) := hmono (Fin.castSucc_lt_last _)
    have hT := sameTilted_of_ratioMP_free hb hE1 hE2 hκ hf₁ hM₁ hmass₁ hf₂ hM₂ hmass₂ hpos0
      hmono0.monotone hat hIH
    have := hf₁.prob
    have := hf₂.prob
    have hm := (hf₁.measurable_fdd hpos0).prodMk (hf₁.measurable _ (hpos (Fin.last (n + 1))))
    have hm' := (hf₂.measurable_fdd hpos0).prodMk (hf₂.measurable _ (hpos (Fin.last (n + 1))))
    have hprod := map_prod_eq_of_sameTilted (hf₁.measurable_fdd hpos0) (hf₂.measurable_fdd hpos0)
      (hf₁.measurable _ (hpos _)) (hf₂.measurable _ (hpos _)) hIH hT
    rw [fdd_eq_snoc_comp σ μ₁, fdd_eq_snoc_comp σ μ₂,
      ← Measure.map_map (measurable_snoc_pair n) hm,
      ← Measure.map_map (measurable_snoc_pair n) hm', hprod]

/-- **Joint laws at arbitrary positive times agree, `W`-free** (unsorted, repeated times).
A copy
of `LawDuality.subLimitJointLawUnique_of_ratioMP`: sort the distinct
values (`Finset.orderEmbOfFin`) and apply a coordinate map.
-/
theorem jointLawUnique_of_ratioMP_free (k : ℕ) (τ : Fin k → ℝ) (hτ : ∀ i, 0 < τ i) :
    P₁.map (fun ω i => μ₁ (τ i) ω) = P₂.map (fun ω i => μ₂ (τ i) ω) := by
  classical
  set S := Finset.univ.image τ with hS
  set σ := S.orderEmbOfFin rfl with hσ
  have hσpos : ∀ j, 0 < σ j := fun j => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.orderEmbOfFin_mem S rfl j)
    rw [← hi]; exact hτ i
  have hJ : ∀ i, ∃ j, σ j = τ i := fun i => by
    have : τ i ∈ Set.range σ := by
      rw [hσ, Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem τ (Finset.mem_univ i))
    exact this
  choose J hJ using hJ
  have hg : Measurable fun (v : Fin S.card → FiniteMeasure unitInterval) (i : Fin k) => v (J i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (J i)
  have e1 : (fun ω i => μ₁ (τ i) ω) = (fun (v : Fin S.card → FiniteMeasure unitInterval)
      (i : Fin k) => v (J i)) ∘ fun ω j => μ₁ (σ j) ω :=
    funext fun ω => funext fun i => by simp only [Function.comp_apply, hJ i]
  have e2 : (fun ω i => μ₂ (τ i) ω) = (fun (v : Fin S.card → FiniteMeasure unitInterval)
      (i : Fin k) => v (J i)) ∘ fun ω j => μ₂ (σ j) ω :=
    funext fun ω => funext fun i => by simp only [Function.comp_apply, hJ i]
  rw [e1, e2, ← Measure.map_map hg (hf₁.measurable_fdd hσpos),
    ← Measure.map_map hg (hf₂.measurable_fdd hσpos),
    jointLaw_strictMono_of_ratioMP_free hb hE1 hE2 hκ hf₁ hM₁ hent₁ hmass₁ hf₂ hM₂ hent₂ hmass₂ _
      σ σ.strictMono hσpos]

end

/-- **`W`-free multi-time uniqueness**.
For `0 < b < 1/2`,
`-2 < E < 2` and an admissible profile `κ`, two random finite-measure processes, each with
`IsFiniteLimitProcess`, the ratio martingale problem with `D₀ = transportD0 b E`, the entrance
and the local mass bound, have the same finite-dimensional distributions: every bounded
continuous test of `(μ(τ_1), …, μ(τ_k))`, `τ_i > 0`, has the same mean.
The proof follows
`LawDuality.subLimitFddUnique_of_ratioMP`, via `integral_bcf_eq_of_map_eq`.
The
hypothesis `b < 1/2` is part of the stated setting; the proof does not use it.
-/
theorem fddUnique_of_ratioMP_free {b E : ℝ} (hb : 0 < b) (_hb2 : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ)
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {μ₁ : ℝ → Ω₁ → FiniteMeasure unitInterval}
    (hf₁ : IsFiniteLimitProcess P₁ μ₁) (hM₁ : IsRatioMartingale (transportD0 b E) E κ P₁ μ₁)
    (hent₁ : HasRatioEntrance P₁ μ₁) (hmass₁ : HasLocalMassBound P₁ μ₁)
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
    {μ₂ : ℝ → Ω₂ → FiniteMeasure unitInterval}
    (hf₂ : IsFiniteLimitProcess P₂ μ₂) (hM₂ : IsRatioMartingale (transportD0 b E) E κ P₂ μ₂)
    (hent₂ : HasRatioEntrance P₂ μ₂) (hmass₂ : HasLocalMassBound P₂ μ₂)
    (k : ℕ) (τ : Fin k → ℝ) (hτ : ∀ i, 0 < τ i)
    (Φ : (Fin k → FiniteMeasure unitInterval) →ᵇ ℝ) :
    ∫ ω, Φ (fun i => μ₁ (τ i) ω) ∂P₁ = ∫ ω, Φ (fun i => μ₂ (τ i) ω) ∂P₂ :=
  integral_bcf_eq_of_map_eq (hf₁.measurable_fdd hτ) (hf₂.measurable_fdd hτ)
    (jointLawUnique_of_ratioMP_free hb hE1 hE2 hκ hf₁ hM₁ hent₁ hmass₁ hf₂ hM₂ hent₂ hmass₂ k τ
      hτ) Φ

end BlockBand.Endpoints.Transmission
