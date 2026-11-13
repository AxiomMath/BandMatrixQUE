module

public import BlockBand.Palm.MomentFlow.IndProps
public import BlockBand.Palm.MomentFlow.Tail6
public import BlockBand.Palm.MomentFlow.EventTime
public import BlockBand.Palm.MomentFlow.Steps2LongUnif
public import BlockBand.Palm.MomentFlow.RemUnif

/-!
# The a priori local bound `M_loc`: `F_r ≤ N^{Cε}`, uniform in time

* `momentMonomial_le_pow`, `momentMonomial_nonneg`.
* **`mloc_uniform`** (from `ExternalLocalGUE`, `MDEBranchIdentification`,
  `GaussianLpGradient` via `overlap_event_uniform`, and `DysonBrownianMotion` via
  `ae_noCollision`): for every `RegVersion Φ`, a.e. off one 𝓛-measurable
  `B` with `P(B) ≤ N^{-D}`, at every time `σ ∈ [a, c₀]`: `0 ≤ Φ(σ, ξ)`, and if all particles of `ξ`
  stay within `r₀/2` of `E` on `[a, c₀]`, `Φ(σ, ξ) ≤ (Cst N^{4ε})^r + max(1, N‖q‖²)^r N^{-D}`.
  Proof: pathwise overlap line on the bulk (𝓛-measurable weight `1_{S_ξ}`), the pull-out
  `condExp_weighted_sum_le` at a countable dense set of times, one 𝓛-set for the
  conditional probability of the bad event (`condExp_indicator_compl_small`), continuity in `σ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.Palm BlockBand.Palm.CoarseRelative

variable {N : ℕ}

/-- `mono(X, ξ) ≤ b^r` when the occupied coordinates are `≤ b` (`X ≥ 0`). -/
theorem momentMonomial_le_pow {X : Fin N → ℝ} {b : ℝ} (hX0 : ∀ i, 0 ≤ X i)
    {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) (hb : ∀ i, 0 < ξ i → X i ≤ b) :
    momentMonomial X ξ ≤ b ^ r := by
  rw [← mem_sector.1 hξ, ← Finset.prod_pow_eq_pow_sum]
  unfold momentMonomial
  refine Finset.prod_le_prod₀ (fun i _ => div_nonneg (pow_nonneg (hX0 i) _) (Nat.cast_nonneg _))
    fun i _ => ?_
  rcases Nat.eq_zero_or_pos (ξ i) with h | h
  · simp [h]
  · have hf : (1 : ℝ) ≤ (ξ i).factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    calc X i ^ ξ i / ((ξ i).factorial : ℝ) ≤ X i ^ ξ i := div_le_self (pow_nonneg (hX0 i) _) hf
      _ ≤ b ^ ξ i := pow_le_pow_left₀ (hX0 i) (hb i h) _

theorem momentMonomial_nonneg {X : Fin N → ℝ} (hX0 : ∀ i, 0 ≤ X i) (ξ : Occ N) :
    0 ≤ momentMonomial X ξ :=
  Finset.prod_nonneg fun i _ => div_nonneg (pow_nonneg (hX0 i) _) (Nat.cast_nonneg _)

/-- **M_loc** (a priori local bound, uniform in time; from `ExternalLocalGUE`,
`MDEBranchIdentification`, `GaussianLpGradient` through the overlap line, and
`DysonBrownianMotion` for simple spectrum). For every regular version `Φ` of the `r`-particle
conditional moments, a.e. off one `𝓛`-measurable `B` (`P(B) ≤ N^{-D}`), at all times `σ`:
`0 ≤ Φ(σ, ξ)`, and if every particle of `ξ` stays in the bulk (`r₀/2`) on `[a, c₀]`,
`Φ(σ, ξ) ≤ (Cst N^{4ε})^r + max(1, N‖q‖²)^r N^{-D}`. -/
theorem mloc_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hDBM : ∀ N : ℕ, DysonBrownianMotion N) {A c₀ r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (r : ℕ) (D : ℝ), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
          flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ Φ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q r Φ →
            ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B → ∀ ξ ∈ sector N r,
              ∀ σ ∈ Icc (c₀ - cmTau N) c₀, 0 ≤ Φ σ ξ ω ∧
                ((∀ k : Fin N, 0 < ξ k → ∀ σ' ∈ Icc (c₀ - cmTau N) c₀,
                    |flowEigenvalue F (c₀ - cmTau N) ω σ' k - E| ≤ r₀ / 2) →
                  Φ σ ξ ω ≤ (Cst * (N : ℝ) ^ (4 * ε)) ^ r +
                    max 1 ((N : ℝ) * nsq q) ^ r * (N : ℝ) ^ (-D)) := by
  obtain ⟨Cst, hCst, hOv⟩ := overlap_event_uniform hELG hMDE hLp (A := A) hK hε hε4
  refine ⟨Cst, hCst, fun r D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hOv (2 * D)
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((hτ0.eventually (ge_mem_nhds hK.2.2.2.1)).and
    ((hτ0.eventually (ge_mem_nhds hK.1)).and (eventually_ge_atTop (max N₁ 1))))
  refine ⟨N₂, fun N hN F E hC q hq => ?_⟩
  obtain ⟨hτs, hτc, hNN⟩ := hN₂ N hN
  have hNpos : 0 < N := le_of_max_le_right hNN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  set τ := cmTau N with hτdef
  set a := c₀ - τ
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hNp _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hNpos) (by norm_num)
  have ha0 : 0 < a := by
    simp only [a, hτdef, cmTau]
    have : (N : ℝ) ^ (-(1 / 100 : ℝ)) < c₀ := by
      have h2 : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ c₀ := hτc
      rcases h2.lt_or_eq with h | h
      · exact h
      · exfalso
        have h3 : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ s₀ := hτs
        linarith [hK.2.2.2.2.1, hK.1]
    linarith
  have hac : a ≤ c₀ := by linarith
  obtain ⟨Bad, hBadm, hPBad, hBad⟩ := hN₁ N (le_of_max_le_left hNN) F E hC a τ ha0.le hτpos hτ1
    (by simp only [a]; linarith [show τ ≤ s₀ from hτs]) (by simp only [a]; linarith) q
  set μ := flowLaw N a
  have hm := pathSigma_le F a a c₀
  set Null : Set (FlowSample N) := {ω | ¬ (ω.1.IsHermitian ∧ ∀ σ : ℝ, a ≤ σ → ∀ i j : Fin N,
    i ≠ j → flowEigenvalue F a ω σ i ≠ flowEigenvalue F a ω σ j)}
  have hNull : μ Null = 0 := by
    have h := ae_noCollision (hDBM N) hC.1 ha0
    rwa [ae_iff] at h
  set Bad' := Bad ∪ toMeasurable μ Null
  have hBad'm : MeasurableSet Bad' := hBadm.union (measurableSet_toMeasurable _ _)
  have hPBad' : μ Bad' ≤ ENNReal.ofReal ((N : ℝ) ^ (-(2 * D))) :=
    (measure_union_le _ _).trans (by rw [measure_toMeasurable, hNull, add_zero]; exact hPBad)
  have ht : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hNp _
  obtain ⟨B, hB, hμB, hoff⟩ := condExp_indicator_compl_small (μ := μ) hm hBad'm.compl ht
  rw [compl_compl] at hμB hoff
  refine ⟨B, hB, ?_, fun Φ hΦ => ?_⟩
  · have h1 : μ.real Bad' ≤ (N : ℝ) ^ (-(2 * D)) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hPBad'
    have h2 : μ.real Bad' / (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-D) := by
      rw [div_le_iff₀ ht, ← Real.rpow_add hNp]
      convert h1 using 2; ring
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hμB.trans h2)
  set B₁ : ℝ := max 1 ((N : ℝ) * nsq q)
  have hB₁ : 1 ≤ B₁ := le_max_left _ _
  set b : ℝ := (Cst * (N : ℝ) ^ (4 * ε)) ^ r
  have hb0 : 0 ≤ b := by positivity
  set X : ℝ → Occ N → FlowSample N → ℝ := fun σ ξ ω =>
    momentMonomial (fun k => flowOverlap F a q σ k ω) ξ
  have hX0' : ∀ σ k ω, 0 ≤ flowOverlap F a q σ k ω := fun σ k ω => by
    simp only [flowOverlap]; positivity
  have hX0 : ∀ σ ξ ω, 0 ≤ X σ ξ ω := fun σ ξ ω => momentMonomial_nonneg (hX0' σ · ω) ξ
  have hXB : ∀ σ ξ, ξ ∈ sector N r → ∀ ω, X σ ξ ω ≤ B₁ ^ r := fun σ ξ hξ ω =>
    momentMonomial_le_pow (hX0' σ · ω) hξ fun k _ =>
      (FreshPalmAssembly.overlap_le_nsq (flowMatrix F a ω σ) q k).trans (le_max_right _ _)
  have hXm : ∀ σ ξ, Measurable (X σ ξ) := fun σ ξ =>
    (measurable_momentMonomial ξ).comp (Measurable.of_eval fun k => measurable_flowOverlap F a q σ k)
  -- the bulk weight
  set S : Occ N → Set (FlowSample N) := fun ξ => {ω | ∀ v ∈ Icc a c₀, ∀ k : Fin N, 0 < ξ k →
    |flowEigenvalue F a ω v k - E| ≤ r₀ / 2}
  have hSm : ∀ ξ, MeasurableSet[pathSigma F a a c₀] (S ξ) := fun ξ =>
    measurableSet_bulk F hC.1 le_rfl le_rfl ξ E (r₀ / 2)
  set w : Occ N → FlowSample N → ℝ := fun ξ => (S ξ).indicator 1
  have hgood : ∀ σ ∈ Icc a c₀, ∀ ξ ∈ sector N r, ∀ ω ∉ Bad',
      ∑ _j : Unit, w ξ ω * X σ ξ ω ≤ b := by
    intro σ hσ ξ hξ ω hω
    simp only [Finset.univ_unique, Finset.sum_singleton]
    by_cases hS : ω ∈ S ξ
    · simp only [w, indicator_of_mem hS, Pi.one_apply, one_mul]
      have hω1 : ω ∉ Bad := fun h => hω (Or.inl h)
      have hω2 : ω ∉ Null := fun h => hω (Or.inr (subset_toMeasurable _ _ h))
      simp only [Null, mem_ofPred_eq, not_not] at hω2
      have hH := hω2.1
      have hsimp : HasSimpleSpectrum N (flowMatrix F a ω σ) :=
        hasSimpleSpectrum_of_injective (BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hC.1 a hH σ)
          fun i j hij => hω2.2 σ hσ.1 i j hij
      refine momentMonomial_le_pow (hX0' σ · ω) hξ fun k hk => ?_
      have := hBad ω hω1 hH σ ⟨hσ.1, by simp only [a]; linarith [hσ.2]⟩ hsimp k (hS σ hσ k hk)
      rw [hq, mul_one] at this
      exact this
    · simp only [w, indicator_of_notMem hS, zero_mul]; exact hb0
  -- a countable dense set of times
  obtain ⟨Dt, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc a c₀)
  have : Countable Dt := hDc.to_subtype
  have hsec : (sector N r : Set (Occ N)).Countable := (sector N r).countable_toSet
  have hae : ∀ᵐ ω ∂μ, ∀ d : Dt, ∀ ξ : sector N r,
      (∑ _j : Unit, w ξ ω * (μ[X ((d : Icc a c₀) : ℝ) ξ | pathSigma F a a c₀]) ω ≤
        b + Fintype.card Unit * 1 * B₁ ^ r *
          (μ[Bad'.indicator (fun _ => (1 : ℝ)) | pathSigma F a a c₀]) ω) ∧
      0 ≤ (μ[X ((d : Icc a c₀) : ℝ) ξ | pathSigma F a a c₀]) ω ∧
      (μ[X ((d : Icc a c₀) : ℝ) ξ | pathSigma F a a c₀]) ω = Φ ((d : Icc a c₀) : ℝ) ξ ω := by
    refine ae_all_iff.2 fun d => ae_all_iff.2 fun ξ => ?_
    have hd := (d : Icc a c₀).2
    have h1 := condExp_weighted_sum_le (μ := μ) hm (fun _ : Unit => w ξ)
      (fun _ : Unit => X ((d : Icc a c₀) : ℝ) ξ) hb0 zero_le_one (by positivity)
      (fun _ => (stronglyMeasurable_const.indicator (hSm ξ) :
        StronglyMeasurable[pathSigma F a a c₀] (w ξ)))
      (fun _ ω => indicator_nonneg (fun _ _ => zero_le_one) ω)
      (fun _ ω => indicator_le_self' (fun _ _ => zero_le_one) ω |>.trans (le_of_eq rfl) |>.trans
        (by simp))
      (fun _ => hXm _ _) (fun _ ω => hX0 _ _ ω) (fun _ ω => hXB _ _ ξ.2 ω) hBad'm
      (hgood _ hd ξ ξ.2)
    have h2 : 0 ≤ᵐ[μ] μ[X ((d : Icc a c₀) : ℝ) ξ | pathSigma F a a c₀] :=
      condExp_nonneg (Eventually.of_forall fun ω => hX0 _ _ ω)
    have h3 := (hΦ.1 _ hd ξ ξ.2)
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    exact ⟨h1, h2, by rw [h3]; rfl⟩
  filter_upwards [hae, hΦ.2] with ω hω hsol hωB ξ hξ σ hσ
  have hcont : ContinuousOn (fun σ => Φ σ ξ ω) (Icc a c₀) := (hsol ξ hξ).1
  have hsmall := hoff ω hωB
  refine ⟨?_, fun hbulk => ?_⟩
  · refine le_of_dense_open hDd continuousOn_const hcont continuousOn_const
      (u := fun _ => (0 : ℝ)) (δ := 1) (fun x hx _ => ?_) σ hσ zero_lt_one
    obtain ⟨-, h2, h3⟩ := hω ⟨x, hx⟩ ⟨ξ, hξ⟩
    rw [← h3]; exact h2
  · have hS : ω ∈ S ξ := fun v hv k hk => hbulk k hk v hv
    refine le_of_dense_open hDd hcont continuousOn_const continuousOn_const
      (u := fun _ => (0 : ℝ)) (δ := 1) (fun x hx _ => ?_) σ hσ zero_lt_one
    obtain ⟨h1, -, h3⟩ := hω ⟨x, hx⟩ ⟨ξ, hξ⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, w, indicator_of_mem hS, Pi.one_apply,
      one_mul, Fintype.card_unique, Nat.cast_one] at h1
    rw [h3] at h1
    refine h1.trans ?_
    have : (μ[Bad'.indicator (fun _ => (1 : ℝ)) | pathSigma F a a c₀]) ω ≤ (N : ℝ) ^ (-D) :=
      (hsmall).le
    have hB0 : 0 ≤ B₁ ^ r := by positivity
    nlinarith

end BlockBand.Palm.MomentFlow
