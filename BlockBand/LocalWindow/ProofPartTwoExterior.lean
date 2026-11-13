module

public import BlockBand.LocalWindow.ProofPartTwo
public import BlockBand.LocalWindow.ProofPartOneAssemblyEvents
public import BlockBand.LocalWindow.ProofNormEvent
public import BlockBand.LocalWindow.ProofCertificateRegular

/-!
# The exterior event `Ω_ext` of part (ii)

Construction of the exterior event of part (ii) of the physical local-window lemma, outside of
which the exterior data satisfy the deterministic conclusions and the joint events are
conditionally small.

## Main results

* the conditional-smallness bookkeeping `CondSmall μ ν Ω S a` (`MeasurableSet S`, `μ Ω ≤ a`,
  `ν(S_x) ≤ a` for `x ∉ Ω`), with `CondSmall.union`, `CondSmall.mono`, `condSmall_fst`;
* **`condSmall_of_prod_le`** (the measurable-superset device for *joint* events): every set `R`
  of the product with `(μ ⊗ ν)(R) ≤ c t` (outer measure) lies in a measurable `S`
  (`toMeasurable`) with `μ{x : ν(S_x) > t} ≤ c` (Markov for `x ↦ ν(S_x)`);
* the exterior sets `extHermSet`, `extCrowdSet`, `extNormSet`, `extCertSet` (sets of exterior
  data `ω = (H_R, C, V)` only) and `splitLaw_fst_preimage` (`splitLaw(Ω × M) = Pω(Ω)`);
* `ExteriorGood` (the deterministic exterior conclusions: Hermiticity, no crowding at radius
  `ε₀` on `[-2, 2]`, the norm bounds `‖C‖, ‖C*‖ ≤ nW`, `‖V‖ ≤ nW + C_G`, the certificate on a
  grid) and `JointGood` (`G` Hermitian, no selected energy is an exterior pole, rank location);
* **`partTwoExterior_le`**: fixed `b, T, ϑ, κ, κ', ε, D, M, A₀ ≥ D + 4`; then `C_G > 0`, `C ≥ 0`;
  for every admissible `p`, model, pair, splitting law and grid `Es ⊆ bulkInterval κ` with
  `|Es| ≤ W^M`, there are `Ω_ext` and a measurable `S` with `CondSmall Pω GUE Ω_ext S (C W^{-D})`,
  `ExteriorGood` off `Ω_ext` (at `ε₀ = W^{-A₀}`) and `JointGood` off `Ω_ext × M ∪ S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-!
## Conditional smallness
-/

section CondSmall

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- `(Ω, S)` is conditionally `a`-small for `μ ⊗ ν`: `S` is measurable, `μ(Ω) ≤ a`, and every
section `S_x`, `x ∉ Ω`, has `ν(S_x) ≤ a` (the form of `PartTwoConditionalStatement`). -/
def CondSmall (μ : Measure X) (ν : Measure Y) (Ω : Set X) (S : Set (X × Y)) (a : ℝ≥0∞) :
    Prop :=
  MeasurableSet S ∧ μ Ω ≤ a ∧ ∀ x ∉ Ω, ν (Prod.mk x ⁻¹' S) ≤ a

theorem CondSmall.mono {μ : Measure X} {ν : Measure Y} {Ω : Set X} {S : Set (X × Y)}
    {a b : ℝ≥0∞} (h : CondSmall μ ν Ω S a) (hab : a ≤ b) : CondSmall μ ν Ω S b :=
  ⟨h.1, h.2.1.trans hab, fun x hx => (h.2.2 x hx).trans hab⟩

/-- Unions of conditionally small pairs: the bounds add. -/
theorem CondSmall.union {μ : Measure X} {ν : Measure Y} {Ω₁ Ω₂ : Set X} {S₁ S₂ : Set (X × Y)}
    {a b : ℝ≥0∞} (h₁ : CondSmall μ ν Ω₁ S₁ a) (h₂ : CondSmall μ ν Ω₂ S₂ b) :
    CondSmall μ ν (Ω₁ ∪ Ω₂) (S₁ ∪ S₂) (a + b) := by
  refine ⟨h₁.1.union h₂.1, (measure_union_le _ _).trans (add_le_add h₁.2.1 h₂.2.1),
    fun x hx => ?_⟩
  have hx₁ : x ∉ Ω₁ := fun h => hx (Or.inl h)
  have hx₂ : x ∉ Ω₂ := fun h => hx (Or.inr h)
  rw [Set.preimage_union]
  exact (measure_union_le _ _).trans (add_le_add (h₁.2.2 x hx₁) (h₂.2.2 x hx₂))

/-- An exterior event alone: `(Ω, ∅)` is conditionally `μ(Ω)`-small. -/
theorem condSmall_fst {μ : Measure X} {ν : Measure Y} {Ω : Set X} {a : ℝ≥0∞} (h : μ Ω ≤ a) :
    CondSmall μ ν Ω ∅ a :=
  ⟨MeasurableSet.empty, h, fun x _ => by rw [Set.preimage_empty, measure_empty]; exact bot_le⟩

/-- **The measurable-superset device for joint events** (Fubini and Markov): if
`(μ ⊗ ν)(R) ≤ c t` (outer measure, `R` arbitrary) with `0 < t < ∞`, then `R ⊆ S` for the
measurable hull `S = toMeasurable (μ ⊗ ν) R`, and `Ω = {x | t < ν(S_x)}` has `μ(Ω) ≤ c`; off `Ω`
every section has `ν(S_x) ≤ t`. -/
theorem condSmall_of_prod_le (μ : Measure X) (ν : Measure Y) [SFinite ν] (R : Set (X × Y))
    {c t : ℝ≥0∞} (ht0 : t ≠ 0) (htop : t ≠ ⊤) (hR : μ.prod ν R ≤ c * t) :
    ∃ S : Set (X × Y), R ⊆ S ∧ MeasurableSet S ∧ μ {x | t < ν (Prod.mk x ⁻¹' S)} ≤ c ∧
      ∀ x ∉ {x | t < ν (Prod.mk x ⁻¹' S)}, ν (Prod.mk x ⁻¹' S) ≤ t := by
  set S := toMeasurable (μ.prod ν) R with hSdef
  have hS : MeasurableSet S := measurableSet_toMeasurable _ _
  have hf : Measurable fun x => ν (Prod.mk x ⁻¹' S) := measurable_measure_prodMk_left hS
  refine ⟨S, subset_toMeasurable _ _, hS, ?_, fun x hx => not_lt.mp hx⟩
  have hmk := mul_meas_ge_le_lintegral₀ (hf.aemeasurable (μ := μ)) t
  rw [← Measure.prod_apply hS, hSdef, measure_toMeasurable] at hmk
  have h1 : t * μ {x | t < ν (Prod.mk x ⁻¹' S)} ≤ t * c :=
    calc t * μ {x | t < ν (Prod.mk x ⁻¹' S)}
        ≤ t * μ {x | t ≤ ν (Prod.mk x ⁻¹' S)} :=
          mul_le_mul_right (measure_mono fun x (hx : t < ν (Prod.mk x ⁻¹' S)) => le_of_lt hx) t
      _ ≤ μ.prod ν R := hmk
      _ ≤ c * t := hR
      _ = t * c := mul_comm _ _
  exact (ENNReal.mul_le_mul_iff_right ht0 htop).mp h1

end CondSmall

/-!
## The exterior sets
-/

variable {p : Parameters} {i : ZMod p.n}

/-- Under the split law, a cylinder `Ω × M` has the `Pω`-probability of `Ω`. -/
theorem splitLaw_fst_preimage {model : p.GaussianRingModel} {Pω : Measure (SplitState p i)}
    (_hPω : IsPairSplitting p i model (splitS p) Pω) (A : Set (SplitState p i)) :
    splitLaw p i Pω (Prod.fst ⁻¹' A) = Pω A := by
  have hprob := isProbabilityMeasure_gueMeasure_pair (p := p) (i := i) (splitS p)
  unfold splitLaw
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]

/-- Exterior data with `H_R` or `V` not Hermitian. -/
def extHermSet (p : Parameters) (i : ZMod p.n) : Set (SplitState p i) :=
  {om | ¬ (om.1.IsHermitian ∧ om.2.2.IsHermitian)}

/-- Exterior crowding at radius `ε₀` on `[-2, 2]`: `∃ |E| ≤ 2, N_{H_R}([E - ε₀, E + ε₀]) ≥ 2`. -/
def extCrowdSet (p : Parameters) (i : ZMod p.n) (ε₀ : ℝ) : Set (SplitState p i) :=
  {om | ∃ E : ℝ, |E| ≤ 2 ∧ 2 ≤ spectralSum om.1 (ProofCrowding.iccInd (E - ε₀) (E + ε₀))}

/-- The exterior norm bounds `‖C‖, ‖C*‖ ≤ nW`, `‖V‖ ≤ nW + C_G` (as Euclidean maps). -/
def ExtNormBounds (p : Parameters) (i : ZMod p.n) (CG : ℝ) (om : SplitState p i) : Prop :=
  (∀ v, ‖Matrix.toEuclideanLin (𝕜 := ℂ) om.2.1 v‖ ≤ ((p.n : ℝ) * p.W) * ‖v‖) ∧
    (∀ w, ‖Matrix.toEuclideanLin (𝕜 := ℂ) om.2.1ᴴ w‖ ≤ ((p.n : ℝ) * p.W) * ‖w‖) ∧
    (∀ v, ‖Matrix.toEuclideanLin (𝕜 := ℂ) om.2.2 v‖ ≤ ((p.n : ℝ) * p.W + CG) * ‖v‖)

/-- Exterior data violating the norm bounds. -/
def extNormSet (p : Parameters) (i : ZMod p.n) (CG : ℝ) : Set (SplitState p i) :=
  {om | ¬ ExtNormBounds p i CG om}

/-- The certificate threshold `W^{-1+ε} + 4/(W s √κ)` of `gridCertificateHat_le`. -/
def certThreshold (p : Parameters) (ε κ : ℝ) : ℝ :=
  (p.W : ℝ) ^ (-1 + ε) + 4 / ((p.W : ℝ) * (splitS p * Real.sqrt κ))

/-- Certificate failure on the grid `Es`, off crowding. -/
def extCertSet (p : Parameters) (i : ZMod p.n) (ε₀ ε κ : ℝ) (Es : Finset ℝ) :
    Set (SplitState p i) :=
  {om | om ∉ extCrowdSet p i ε₀ ∧ ∃ E ∈ Es, certThreshold p ε κ < ProofCertificate.certErrHat ε₀ p i om E}

/-- **The deterministic exterior conclusions** off `Ω_ext`: `H_R, V` Hermitian; no crowding at
radius `ε₀` on `[-2, 2]`; the norm bounds; the truncated certificate at every grid energy. -/
def ExteriorGood (p : Parameters) (i : ZMod p.n) (CG ε₀ ε κ : ℝ) (Es : Finset ℝ)
    (om : SplitState p i) : Prop :=
  (om.1.IsHermitian ∧ om.2.2.IsHermitian) ∧
    (∀ E : ℝ, |E| ≤ 2 → spectralSum om.1 (ProofCrowding.iccInd (E - ε₀) (E + ε₀)) < 2) ∧
    ExtNormBounds p i CG om ∧
    ∀ E ∈ Es, ProofCertificate.certErrHat ε₀ p i om E ≤ certThreshold p ε κ

/-- **The joint conclusions** off `Ω_ext × M ∪ S`: `G` Hermitian, no selected energy `λ_α` is an
eigenvalue of `H_R` (pole avoidance), and every `ϑ`-bulk rank is within `κ'` of its classical
location. -/
def JointGood (p : Parameters) (i : ZMod p.n) (ϑ κ' : ℝ) (x : SplitState p i × PairMatrix p i) :
    Prop :=
  x.2.IsHermitian ∧
    (∀ α : Fin p.N, (x.1.1 - ((physicalOrderedEigenvalue p (assemble p i x.1 x.2) α : ℝ) : ℂ) •
      (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0) ∧
    ∀ α : Fin p.N, IsBulkRank p ϑ α →
      |physicalOrderedEigenvalue p (assemble p i x.1 x.2) α - classicalLocation p α| < κ'

theorem jointGood_of_not_mem {ϑ κ' : ℝ} {x : SplitState p i × PairMatrix p i}
    (hx : x ∉ ProofPartOne.partOneNullEvent p i ∪ ProofPartOne.partOneRankEvent p i ϑ κ') :
    JointGood p i ϑ κ' x := by
  have h1 : x ∉ ProofPartOne.partOneNullEvent p i := fun h => hx (Or.inl h)
  have h2 : x ∉ ProofPartOne.partOneRankEvent p i ϑ κ' := fun h => hx (Or.inr h)
  unfold ProofPartOne.partOneNullEvent at h1
  unfold ProofPartOne.partOneRankEvent at h2
  simp only [Set.mem_ofPred_eq, not_or, not_exists, not_not] at h1 h2
  refine ⟨h1.1.2.2, fun α => h1.2 α, fun α hα => ?_⟩
  exact not_le.mp fun h => h2 α ⟨hα, h⟩

theorem exteriorGood_of_not_mem {CG ε₀ ε κ : ℝ} {Es : Finset ℝ} {om : SplitState p i}
    (hH : om ∉ extHermSet p i) (hC : om ∉ extCrowdSet p i ε₀) (hN : om ∉ extNormSet p i CG)
    (hR : om ∉ extCertSet p i ε₀ ε κ Es) : ExteriorGood p i CG ε₀ ε κ Es om := by
  refine ⟨not_not.mp hH, fun E hE => not_le.mp fun h => hC ⟨E, hE, h⟩, not_not.mp hN,
    fun E hE => not_lt.mp fun h => hR ⟨hC, E, hE, h⟩⟩

/-- `ofReal (a b) = ofReal a * ofReal b` for `a ≥ 0`. -/
theorem ofReal_mul_rpow_split {W C D : ℝ} (hW : 0 < W) (hC : 0 ≤ C) :
    ENNReal.ofReal (C * W ^ (-(2 * D))) =
      ENNReal.ofReal (C * W ^ (-D)) * ENNReal.ofReal (W ^ (-D)) := by
  rw [← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hW.le _)), mul_assoc,
    ← Real.rpow_add hW]
  ring_nf

/-- **The exterior event of part (ii).** Fixed
`0 < b < 1/2`, `T`, `0 < ϑ < 1/2`, `κ, κ', ε > 0`, `D ≥ 0`, `M` and the crowding exponent
`A₀ ≥ D + 4`; then constants `C_G > 0`, `C ≥ 0`. For every admissible `p` (`p.b = b`,
`n ≤ TW`), model, pair `i`, splitting law `Pω` and grid `Es ⊆ bulkInterval κ` with
`|Es| ≤ W^M`, there are an exterior event `Ω_ext` and a measurable set `S` with
`Pω(Ω_ext) ≤ C W^{-D}`, `GUE_d(s/d)(S_ω) ≤ C W^{-D}` for `ω ∉ Ω_ext`, `ExteriorGood` at
`ε₀ = W^{-A₀}` for `ω ∉ Ω_ext`, and `JointGood ϑ κ'` for `x.1 ∉ Ω_ext`, `x ∉ S`. -/
theorem partTwoExterior_le (hPBC : PhysicalBlockConditionalCount)
    (hMT : MatchedTracesContract) (hRL : RankLocationContract) (hCo : CoareaContract)
    (b T ϑ κ κ' ε D M A₀ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2)
    (hκ : 0 < κ) (hκ' : 0 < κ') (hε : 0 < ε) (hD : 0 ≤ D) (hA₀ : D + 4 ≤ A₀) :
    ∃ CG C : ℝ, 0 < CG ∧ 0 ≤ C ∧ ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
        IsPairSplitting p i model (splitS p) Pω →
        ∀ Es : Finset ℝ, (∀ E ∈ Es, E ∈ bulkInterval κ) → (Es.card : ℝ) ≤ (p.W : ℝ) ^ M →
          ∃ (Ωext : Set (SplitState p i)) (S : Set (SplitState p i × PairMatrix p i)),
            CondSmall Pω (gueMeasure (PairSite p i) (pairTime p (splitS p))) Ωext S
              (ENNReal.ofReal (C * (p.W : ℝ) ^ (-D))) ∧
            (∀ om ∉ Ωext, ExteriorGood p i CG ((p.W : ℝ) ^ (-A₀)) ε κ Es om) ∧
            ∀ x : SplitState p i × PairMatrix p i, x.1 ∉ Ωext → x ∉ S → JointGood p i ϑ κ' x := by
  obtain ⟨Ccr, hCcr, hcr⟩ := ProofPartOne.splitLaw_crowding_rpow_le hPBC b T (A₀ - 4) hb'
    (by linarith)
  obtain ⟨CG, cG, hCG, hcG, hnorm⟩ := ProofNormEvent.normEvent_le
  obtain ⟨Cn, hCn, hnb⟩ := ProofNormEvent.normBound_le_rpow T D cG hcG
  obtain ⟨Cce, hCce, hcert⟩ := ProofCertificate.gridCertificateHat_le hMT hPBC b κ T hb hb' hκ
    ε D M hε hD
  obtain ⟨Crk, hCrk, hrank⟩ := ProofPartOne.splitLaw_partOneRank_le hRL b T ϑ κ' (2 * D) hb hb'
    hϑ hϑ' hκ' (by linarith)
  refine ⟨CG, Ccr + Cn + Cce + Crk + 1, hCG, by positivity,
    fun p hpb hn model i Pω hPω Es hEs hcard => ?_⟩
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hWD : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have hprob := isProbabilityMeasure_gueMeasure_pair (p := p) (i := i) (splitS p)
  set ν := gueMeasure (PairSite p i) (pairTime p (splitS p))
  set ε₀ := (p.W : ℝ) ^ (-A₀) with hε₀
  -- Hermiticity of the exterior data (a.s.)
  have hHerm : Pω (extHermSet p i) ≤ 0 := by
    have := BlockBand.Angular.FiberAngular.ae_hermitian_of_isPairSplitting p i hPω
    rw [ae_iff] at this
    exact this.le
  -- crowding
  have hCrowd : Pω (extCrowdSet p i ε₀) ≤ ENNReal.ofReal (Ccr * (p.W : ℝ) ^ (-D)) := by
    have h := hcr p hpb hn model i Pω hPω
    have e : -(A₀ - 4 + 4) = -A₀ := by ring
    rw [e] at h
    have hfst : Prod.fst ⁻¹' extCrowdSet p i ε₀ = ProofCrowding.crowdingEvent p i ε₀ 2 := rfl
    rw [← splitLaw_fst_preimage hPω, hfst]
    refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hCcr))
    exact Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  -- norm
  have hNorm : Pω (extNormSet p i CG) ≤ ENNReal.ofReal (Cn * (p.W : ℝ) ^ (-D)) := by
    rw [← splitLaw_fst_preimage hPω]
    refine (measure_mono fun x hx => ?_).trans ((hnorm p model i Pω hPω).trans
      (ENNReal.ofReal_le_ofReal (hnb p hn)))
    by_contra hx'
    rw [Set.mem_union, not_or] at hx'
    exact hx (ProofNormEvent.norm_bounds_of_not_mem hx'.1 hx'.2)
  -- certificate
  have hCert : Pω (extCertSet p i ε₀ ε κ Es) ≤ ENNReal.ofReal (Cce * (p.W : ℝ) ^ (-D)) := by
    rw [← splitLaw_fst_preimage hPω]
    exact (hcert p hpb hn model i Pω hPω Es hEs hcard ε₀)
  -- the joint events (null and rank), conditionalized by Markov
  set R := ProofPartOne.partOneNullEvent p i ∪ ProofPartOne.partOneRankEvent p i ϑ κ'
  have hRle : (Pω.prod ν) R ≤
      ENNReal.ofReal (Crk * (p.W : ℝ) ^ (-D)) * ENNReal.ofReal ((p.W : ℝ) ^ (-D)) := by
    rw [← ofReal_mul_rpow_split hW hCrk]
    refine (measure_union_le _ _).trans ?_
    have h0 := ProofPartOne.splitLaw_partOneNull_eq_zero hCo hPω
    have h1 := hrank p hpb hn model i Pω hPω
    unfold splitLaw at h0 h1
    rw [h0, zero_add]
    exact h1
  have ht0 : ENNReal.ofReal ((p.W : ℝ) ^ (-D)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.rpow_pos_of_pos hW _
  obtain ⟨S, hRS, hS, hΩR, hsecR⟩ := condSmall_of_prod_le Pω ν R ht0 ENNReal.ofReal_ne_top hRle
  set ΩR := {om : SplitState p i | ENNReal.ofReal ((p.W : ℝ) ^ (-D)) < ν (Prod.mk om ⁻¹' S)}
  have hJoint : CondSmall Pω ν ΩR S (ENNReal.ofReal (Crk * (p.W : ℝ) ^ (-D)) +
      ENNReal.ofReal ((p.W : ℝ) ^ (-D))) :=
    ⟨hS, hΩR.trans le_self_add, fun om hom => (hsecR om hom).trans le_add_self⟩
  -- assemble
  have hall := ((((condSmall_fst (ν := ν) hHerm).union (condSmall_fst (ν := ν) hCrowd)).union
    (condSmall_fst (ν := ν) hNorm)).union (condSmall_fst (ν := ν) hCert)).union hJoint
  refine ⟨extHermSet p i ∪ extCrowdSet p i ε₀ ∪ extNormSet p i CG ∪ extCertSet p i ε₀ ε κ Es ∪
    ΩR, ∅ ∪ ∅ ∪ ∅ ∪ ∅ ∪ S, hall.mono ?_, fun om hom => ?_, fun x hx1 hx2 => ?_⟩
  · simp only [zero_add]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
  · simp only [Set.mem_union, not_or] at hom
    exact exteriorGood_of_not_mem hom.1.1.1.1 hom.1.1.1.2 hom.1.1.2 hom.1.2
  · refine jointGood_of_not_mem fun hxR => hx2 ?_
    simp only [Set.empty_union]
    exact hRS hxR

end BlockBand.LocalWindow.ProofPartTwo
