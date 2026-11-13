module

public import BlockBand.Transmission.LawDuality.FddCond
public import BlockBand.Transmission.LawDuality.FddDetermine

/-!
# `SubLimitFddUnique` for every `k`

The only hypothesis is the statement `SubLimitRatioMP`, defined in the interface module: every
subsequential limit is a ratio martingale with entrance and local mass bound. The duality principle
is used through its proof `ratioDualityPrinciple_holds`, the dual through
`hasDualDeletionProcess_transport`.

* `subLimit_sameTilted`: for sorted times `σ_0 ≤ … ≤ σ_n = a₀ < t`, if the joint laws of
  `Y = (μ_{σ_i})_i` agree, then the tilted ratio transforms of `(Y, μ_t)` agree:
  `E[ψ(Y) F_{x,y}(μ_t)] = E'[ψ(Y') F_{x,y}(μ'_t)]`. By the conditional duality
  (`integral_pastTest_mul_ratio`) against the same normalized dual, both sides are
  `E''[E[G_{ω''}(Y)] K(ω'')]` with `G_{ω''}(v) = ψ(v)·F_{Z_L(ω'')}(v_n)` continuous and bounded.
* `subLimit_jointLaw_strictMono`: induction on the number of strictly increasing times
  (`k ≤ 1`: `subLimit_jointLaw_le_one`); step: `map_prod_eq_of_sameTilted`, then `Fin.snoc`.
* **`subLimitJointLawUnique_of_ratioMP`**: arbitrary times (unsorted, repeated) by
  sorting the distinct values (`Finset.orderEmbOfFin`) and a coordinate map.
* **`subLimitFddUnique_of_ratioMP`**: the implication from `SubLimitRatioMP` to
  `SubLimitFddUnique`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal BoundedContinuousFunction

theorem measurable_snoc_pair (n : ℕ) :
    Measurable fun q : (Fin (n + 1) → FiniteMeasure unitInterval) × FiniteMeasure unitInterval =>
      (Fin.snoc q.1 q.2 : Fin (n + 2) → FiniteMeasure unitInterval) := by
  refine measurable_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact measurable_snd
  | cast j => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_fst

section

variable {b E : ℝ} {κ : ℝ → ℝ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
  (hκ : IsAbsorptionProfile κ) (hMP : SubLimitRatioMP)
  {φ φ' : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (hφ' : Tendsto φ' atTop atTop)
  {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {μ : ℝ → Ω → FiniteMeasure unitInterval} {μ' : ℝ → Ω' → FiniteMeasure unitInterval}
  (hs : IsTransmissionSubLimit b E κ φ P μ) (hs' : IsTransmissionSubLimit b E κ φ' P' μ')
include hb hb2 hE1 hE2 hκ hMP hφ hφ' hs hs'

/-- **The induction step's input: tilted ratio transforms of `(Y, μ_t)` agree.** -/
theorem subLimit_sameTilted {n : ℕ} {σ : Fin (n + 1) → ℝ} (hpos : ∀ i, 0 < σ i)
    (hmono : Monotone σ) {t : ℝ} (hat : σ (Fin.last n) < t)
    (hIH : P.map (fun ω i => μ (σ i) ω) = P'.map (fun ω i => μ' (σ i) ω)) :
    SameTiltedRatioTransforms P (fun ω i => μ (σ i) ω) (μ t) P' (fun ω i => μ' (σ i) ω)
      (μ' t) := by
  intro ψ hψ p x y hxy
  have := hs.prob
  have := hs'.prob
  obtain ⟨Ω'', m'', 𝓖, P'', N, X, Y, hD⟩ := hasDualDeletionProcess_transport hb hE1 hE2 hxy
  obtain ⟨N', X', Y', hD', hpath', hst', -⟩ := exists_normalized hxy hD
  obtain ⟨h1, -, h3⟩ := hMP b hb hb2 E hE1 hE2 κ hκ φ hφ Ω inferInstance P μ hs
  obtain ⟨h1', -, h3'⟩ := hMP b hb hb2 E hE1 hE2 κ hκ φ' hφ' Ω' inferInstance P' μ' hs'
  have hu : ∀ l, 0 < σ l ∧ σ l ≤ σ (Fin.last n) := fun l => ⟨hpos l, hmono (Fin.le_last l)⟩
  have c1 := integral_pastTest_mul_ratio ψ hκ hs.measurable hs.continuous h1 h3 hψ (hpos _) hu
    hat hD' hpath' hst' hxy
  have c2 := integral_pastTest_mul_ratio ψ hκ hs'.measurable hs'.continuous h1' h3' hψ (hpos _) hu
    hat hD' hpath' hst' hxy
  show ∫ ω, pastTest ψ μ σ ω * transmissionRatio x y (μ t ω) ∂P =
    ∫ ω, pastTest ψ μ' σ ω * transmissionRatio x y (μ' t ω) ∂P'
  rw [c1, c2]
  refine integral_congr_ae (ae_of_all _ fun ω'' => ?_)
  beta_reduce
  congr 1
  set G : (Fin (n + 1) → FiniteMeasure unitInterval) → ℝ := fun v =>
    ψ v * ratioStop (v (Fin.last n)) N' X' Y' (fun _ => ⊤) (t - σ (Fin.last n)) ω'' with hGdef
  have hG : Continuous G :=
    ψ.continuous.mul ((continuous_pathRatio_nu (hpath' ω'') _).comp (continuous_apply _))
  show ∫ ω, G (fun i => μ (σ i) ω) ∂P = ∫ ω, G (fun i => μ' (σ i) ω) ∂P'
  rw [← integral_map (measurable_fdd hs hpos).aemeasurable hG.aestronglyMeasurable, hIH,
    integral_map (measurable_fdd hs' hpos).aemeasurable hG.aestronglyMeasurable]

/-- **Joint laws at strictly increasing positive times agree.** -/
theorem subLimit_jointLaw_strictMono : ∀ (n : ℕ) (σ : Fin n → ℝ), StrictMono σ →
    (∀ i, 0 < σ i) → P.map (fun ω i => μ (σ i) ω) = P'.map (fun ω i => μ' (σ i) ω) := by
  intro n
  induction n with
  | zero =>
    intro σ _ hpos
    exact subLimit_jointLaw_le_one hMP ratioDualityPrinciple_holds hb hb2 hE1 hE2 hκ hφ hφ' hs hs'
      (Nat.zero_le 1) hpos
  | succ n ih =>
    intro σ hmono hpos
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact subLimit_jointLaw_le_one hMP ratioDualityPrinciple_holds hb hb2 hE1 hE2 hκ hφ hφ' hs
        hs' le_rfl hpos
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    set σ0 : Fin (n + 1) → ℝ := fun i => σ (Fin.castSucc i) with hσ0
    have hmono0 : StrictMono σ0 := hmono.comp Fin.strictMono_castSucc
    have hpos0 : ∀ i, 0 < σ0 i := fun i => hpos _
    have hIH := ih σ0 hmono0 hpos0
    have hat : σ0 (Fin.last n) < σ (Fin.last (n + 1)) := hmono (Fin.castSucc_lt_last _)
    have hT := subLimit_sameTilted hb hb2 hE1 hE2 hκ hMP hφ hφ' hs hs' hpos0 hmono0.monotone hat
      hIH
    have := hs.prob
    have := hs'.prob
    have hm := (measurable_fdd hs hpos0).prodMk (hs.measurable _ (hpos (Fin.last (n + 1))))
    have hm' := (measurable_fdd hs' hpos0).prodMk (hs'.measurable _ (hpos (Fin.last (n + 1))))
    have hprod := map_prod_eq_of_sameTilted (measurable_fdd hs hpos0) (measurable_fdd hs' hpos0)
      (hs.measurable _ (hpos _)) (hs'.measurable _ (hpos _)) hIH hT
    have e : ∀ {Ω : Type} (ν : ℝ → Ω → FiniteMeasure unitInterval),
        (fun ω i => ν (σ i) ω) = (fun q : (Fin (n + 1) → FiniteMeasure unitInterval) ×
          FiniteMeasure unitInterval => (Fin.snoc q.1 q.2 : Fin (n + 2) → FiniteMeasure unitInterval))
          ∘ fun ω => ((fun i => ν (σ0 i) ω), ν (σ (Fin.last (n + 1))) ω) :=
      fun ν => funext fun ω => (Fin.snoc_init_self (fun i => ν (σ i) ω)).symm
    rw [e μ, e μ', ← Measure.map_map (measurable_snoc_pair n) hm,
      ← Measure.map_map (measurable_snoc_pair n) hm', hprod]

end

/-- **`SubLimitJointLawUnique` from `SubLimitRatioMP`.** -/
theorem subLimitJointLawUnique_of_ratioMP (hMP : SubLimitRatioMP) : SubLimitJointLawUnique := by
  intro b hb hb2 E hE1 hE2 κ hκ φ φ' hφ hφ' Ω m P μ Ω' m' P' μ' hs hs' k τ hτ
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
  have e : ∀ {Ω : Type} (ν : ℝ → Ω → FiniteMeasure unitInterval),
      (fun ω i => ν (τ i) ω) = (fun (v : Fin S.card → FiniteMeasure unitInterval) (i : Fin k) =>
        v (J i)) ∘ fun ω j => ν (σ j) ω :=
    fun ν => funext fun ω => funext fun i => by simp only [Function.comp_apply, hJ i]
  rw [e μ, e μ', ← Measure.map_map hg (measurable_fdd hs hσpos),
    ← Measure.map_map hg (measurable_fdd hs' hσpos),
    subLimit_jointLaw_strictMono hb hb2 hE1 hE2 hκ hMP hφ hφ' hs hs' _ σ σ.strictMono hσpos]

/-- **`SubLimitFddUnique` from `SubLimitRatioMP`.** -/
theorem subLimitFddUnique_of_ratioMP (hMP : SubLimitRatioMP) : SubLimitFddUnique :=
  subLimitFddUnique_of_jointLaw (subLimitJointLawUnique_of_ratioMP hMP)

/-- **The `law` field from `TransmissionSubLimitExists`, `TransmissionTraceModulus` and
`SubLimitRatioMP`** (`RatioDualityPrinciple` is `ratioDualityPrinciple_holds`, and
`SubLimitFddUnique` follows by `subLimitFddUnique_of_ratioMP`). -/
theorem law_of_ratioMP (hEx : TransmissionSubLimitExists) (hMod : TransmissionTraceModulus)
    (hMP : SubLimitRatioMP) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) :=
  law_of hEx hMod hMP ratioDualityPrinciple_holds (subLimitFddUnique_of_ratioMP hMP)

end BlockBand.Transmission.LawDuality
