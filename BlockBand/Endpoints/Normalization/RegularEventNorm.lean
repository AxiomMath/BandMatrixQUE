module

public import BlockBand.Endpoints.Normalization.RegularEventTraces
public import BlockBand.Endpoints.Normalization.RegularEventLinear
public import BlockBand.Density.CouplingEntries
public import BlockBand.Internal.Contracts.Inputs

/-!
# Regular prior event: polynomial norm of the deformation off a small event

Outside an event of polynomially small probability, the deformation `K(e)` has polynomial norm;
the pole bound uses PSSS at `r = 1` for `H_R` conditional on its bonds.

Proof (`F = V - C*(H_R - e)⁻¹C`, entrywise `ℓ¹` norms `ent`, `regularEventEnt`):
* pole: `law{H | ¬ ∀ y, ε‖y‖ ≤ ‖(H_RR - e) y‖} ≤ (C₁/√c) N · 2ε` for any set `R` of blocks
  (`regularEvent_pole_law`), from `Inputs.PhysicalBlockConditionalCount` at `Φ = 0`, `r = 1` on
  `[e-ε, e+ε]` (count `0` gives a spectral gap, `regularEvent_lower_of_count_zero`), transported to
  `H_R` by reindexing;
* Gaussian norm tails by first moments: `law{u ≤ ent H} ≤ 2N²/u`
  (`regularEvent_law_ent_tail`, from `Density.integral_norm_entry_le_two`) and
  `GUE_ι(τ){u ≤ ent G} ≤ 4|ι|²/u` for `τ ≤ 1` (`regularEvent_gue_ent_tail`);
* on the good event `ent F ≤ 2u + u² · d_R² ε⁻¹` (in the proofs of the two norm tails), and
  `l2Norm (F x) ≤ ent F · l2Norm x`.

Main results: `regularEvent_pair_norm_tail`, `regularEvent_block_norm_tail`. Constants and
quantifiers: `b`, `T` first, then for every `D > 0` the norm exponent `A = 3(D+5)+5` and a width
`W₀(b, T, D, C₁)`; for `W ≥ W₀`, `n ≤ TW`, every model, pair/block, splitting law, reindexing
`σ` and every real `e`: `Pω{¬ NormBound F(e) A} ≤ W^{-D}/2`. Measures of possibly
non-measurable events are outer measures.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Palm BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.Inputs (BlockSites withoutFreshBlocks subsystemCount
  PhysicalBlockConditionalCount)
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. Markov from a first moment
-/

theorem regularEvent_markov_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) {t : ℝ}
    (ht : 0 < t) : μ {x | t ≤ f x} ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / t) := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf) hfi t
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ ht, mul_comm]
  exact h

/-!
## 2. Gaussian first-moment tails
-/

theorem regularEvent_continuous_ent {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (fun M : Matrix ι κ ℂ => regularEventEnt M) := by
  unfold regularEventEnt
  fun_prop

/-- `P(u ≤ Σ_{x,y} |H_xy|) ≤ 2 N²/u` under the physical law. -/
theorem regularEvent_law_ent_tail (p : Parameters) (model : p.GaussianRingModel) {u : ℝ}
    (hu : 0 < u) :
    (model.law : Measure p.SiteMatrix) {H | u ≤ regularEventEnt H} ≤
      ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) := by
  have hint : Integrable (fun H : p.SiteMatrix => regularEventEnt H)
      (model.law : Measure p.SiteMatrix) := by
    unfold regularEventEnt
    exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
      BlockBand.Density.integrable_norm_entry p model x y
  refine (regularEvent_markov_integral _ regularEventEnt_nonneg hint hu).trans
    (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ hu.le
  have : ∫ H, regularEventEnt H ∂(model.law : Measure p.SiteMatrix) =
      ∑ x, ∑ y, ∫ H, ‖H x y‖ ∂(model.law : Measure p.SiteMatrix) := by
    unfold regularEventEnt
    rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
      BlockBand.Density.integrable_norm_entry p model x y]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact integral_finsetSum _ fun y _ => BlockBand.Density.integrable_norm_entry p model x y
  rw [this]
  calc ∑ x, ∑ y, ∫ H, ‖H x y‖ ∂(model.law : Measure p.SiteMatrix)
      ≤ ∑ _x : p.Site, ∑ _y : p.Site, (2 : ℝ) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
          BlockBand.Density.integral_norm_entry_le_two p model x y
    _ = 2 * (Fintype.card p.Site : ℝ) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

section GUE

variable {ι : Type*} [Fintype ι]

/-- The four real coordinates of the circular entries `X_ab, X_ba`. -/
def regularEventGueDom (a b : ι) (r : ((ι × ι) × Fin 2) → ℝ) : ℝ :=
  |r ((a, b), 0)| + |r ((a, b), 1)| + |r ((b, a), 0)| + |r ((b, a), 1)|

omit [Fintype ι] in
theorem regularEvent_norm_circ_le (r : ((ι × ι) × Fin 2) → ℝ) (u : ι × ι) :
    ‖BlockBand.SourceProcess.circularBrownianCoordinates r u‖ ≤ |r (u, 0)| + |r (u, 1)| := by
  unfold BlockBand.SourceProcess.circularBrownianCoordinates
  have hs : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have h1 : ‖(r (u, 0) : ℂ) + (r (u, 1) : ℂ) * Complex.I‖ ≤ |r (u, 0)| + |r (u, 1)| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have h0 : 0 ≤ ‖(r (u, 0) : ℂ) + (r (u, 1) : ℂ) * Complex.I‖ := norm_nonneg _
  rw [div_le_iff₀ (by linarith)]
  nlinarith [abs_nonneg (r (u, 0)), abs_nonneg (r (u, 1))]

omit [Fintype ι] in
theorem regularEvent_norm_gueSample_le {τ : ℝ≥0} (hτ : (τ : ℝ) ≤ 1)
    (r : ((ι × ι) × Fin 2) → ℝ) (a b : ι) :
    ‖gueSample τ (BlockBand.SourceProcess.circularBrownianCoordinates r) a b‖ ≤
      regularEventGueDom a b r := by
  unfold gueSample regularEventGueDom
  rw [Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs : Real.sqrt ((τ : ℝ) / 2) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith [τ.2])
  have h1 := regularEvent_norm_circ_le r (a, b)
  have h2 := regularEvent_norm_circ_le r (b, a)
  have h3 : ‖BlockBand.SourceProcess.circularBrownianCoordinates r (a, b) +
      conj (BlockBand.SourceProcess.circularBrownianCoordinates r (b, a))‖ ≤
      |r ((a, b), 0)| + |r ((a, b), 1)| + (|r ((b, a), 0)| + |r ((b, a), 1)|) := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_conj]
    exact add_le_add h1 h2
  have h0 := norm_nonneg (BlockBand.SourceProcess.circularBrownianCoordinates r (a, b) +
      conj (BlockBand.SourceProcess.circularBrownianCoordinates r (b, a)))
  calc Real.sqrt ((τ : ℝ) / 2) * ‖_‖ ≤ 1 * ‖BlockBand.SourceProcess.circularBrownianCoordinates
        r (a, b) + conj (BlockBand.SourceProcess.circularBrownianCoordinates r (b, a))‖ :=
        mul_le_mul_of_nonneg_right hs h0
    _ ≤ _ := by rw [one_mul]; linarith

theorem regularEvent_integrable_abs_coord (j : (ι × ι) × Fin 2) :
    Integrable (fun r : ((ι × ι) × Fin 2) → ℝ => |r j|)
      (Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1) ∧
    ∫ r, |r j| ∂(Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1) ≤ 1 := by
  have hmp := measurePreserving_eval (fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)) j
  have hint : Integrable (fun t : ℝ => |t|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  constructor
  · rw [← hmp.map_eq] at hint
    exact hint.comp_measurable (measurable_pi_apply j)
  · have h2 : ∫ r, |r j| ∂(Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1) =
        ∫ t, |t| ∂(Measure.map (Function.eval j)
          (Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1)) :=
      (integral_map (μ := Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 1)
        (φ := Function.eval j) (f := fun t : ℝ => |t|) (measurable_pi_apply j).aemeasurable
        continuous_abs.aestronglyMeasurable).symm
    rw [h2, hmp.map_eq]
    simpa using BlockBand.Density.integral_abs_gaussianReal_le (1 : ℝ≥0)

/-- `GUE_ι(τ){u ≤ Σ_{a,b} |G_ab|} ≤ 4|ι|²/u` for `τ ≤ 1`. -/
theorem regularEvent_gue_ent_tail {τ : ℝ≥0} (hτ : (τ : ℝ) ≤ 1) {u : ℝ} (hu : 0 < u) :
    gueMeasure ι τ {G | u ≤ regularEventEnt G} ≤
      ENNReal.ofReal (4 * (Fintype.card ι : ℝ) ^ 2 / u) := by
  set P := Measure.pi fun _ : (ι × ι) × Fin 2 => gaussianReal 0 (1 : ℝ≥0)
  have hS : MeasurableSet {G : Matrix ι ι ℂ | u ≤ regularEventEnt G} :=
    measurableSet_le measurable_const regularEvent_continuous_ent.measurable
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  rw [Measure.map_apply (GUELaw.measurable_gueSample τ) hS,
    Measure.map_apply GUELaw.measurable_circularBrownianCoordinates
      ((GUELaw.measurable_gueSample τ) hS)]
  set f : (((ι × ι) × Fin 2) → ℝ) → ℝ := fun r => ∑ a, ∑ b, regularEventGueDom a b r
  have hsub : BlockBand.SourceProcess.circularBrownianCoordinates ⁻¹'
      (gueSample τ ⁻¹' {G | u ≤ regularEventEnt G}) ⊆ {r | u ≤ f r} := by
    intro r hr
    change u ≤ regularEventEnt _ at hr
    change u ≤ f r
    refine hr.trans ?_
    unfold regularEventEnt
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      regularEvent_norm_gueSample_le hτ r a b
  have hdomi : ∀ a b : ι, Integrable (regularEventGueDom a b) P := by
    intro a b
    unfold regularEventGueDom
    exact (((regularEvent_integrable_abs_coord _).1.add (regularEvent_integrable_abs_coord _).1).add
      (regularEvent_integrable_abs_coord _).1).add (regularEvent_integrable_abs_coord _).1
  have hdom_le : ∀ a b : ι, ∫ r, regularEventGueDom a b r ∂P ≤ 4 := by
    intro a b
    unfold regularEventGueDom
    have i1 := (regularEvent_integrable_abs_coord (ι := ι) ((a, b), 0))
    have i2 := (regularEvent_integrable_abs_coord (ι := ι) ((a, b), 1))
    have i3 := (regularEvent_integrable_abs_coord (ι := ι) ((b, a), 0))
    have i4 := (regularEvent_integrable_abs_coord (ι := ι) ((b, a), 1))
    have j12 : Integrable (fun r : ((ι × ι) × Fin 2) → ℝ => |r ((a, b), 0)| + |r ((a, b), 1)|) P :=
      i1.1.add i2.1
    have j123 : Integrable (fun r : ((ι × ι) × Fin 2) → ℝ =>
        |r ((a, b), 0)| + |r ((a, b), 1)| + |r ((b, a), 0)|) P := j12.add i3.1
    rw [integral_add j123 i4.1, integral_add j12 i3.1, integral_add i1.1 i2.1]
    linarith [i1.2, i2.2, i3.2, i4.2]
  have hfi : Integrable f P :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hdomi a b
  have hf0 : ∀ r, 0 ≤ f r := fun r => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    unfold regularEventGueDom; positivity
  refine (measure_mono hsub).trans ((regularEvent_markov_integral P hf0 hfi hu).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hu.le)))
  have : ∫ r, f r ∂P = ∑ a, ∑ b, ∫ r, regularEventGueDom a b r ∂P := by
    simp only [f]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hdomi a b]
    exact Finset.sum_congr rfl fun a _ => integral_finsetSum _ fun b _ => hdomi a b
  rw [this]
  calc ∑ a, ∑ b, ∫ r, regularEventGueDom a b r ∂P ≤ ∑ _a : ι, ∑ _b : ι, (4 : ℝ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hdom_le a b
    _ = 4 * (Fintype.card ι : ℝ) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end GUE

/-!
## 3. The pole bound: PSSS conditional on bonds at `r = 1`
-/

section Pole

/-- A Hermitian matrix with no eigenvalue in `[e-ε, e+ε]` has `ε‖y‖ ≤ ‖(A - e) y‖`. -/
theorem regularEvent_lower_of_count_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : BlockBand.External.PSSS.HermitianMatrix ι) {e ε : ℝ} (hε : 0 ≤ ε)
    (h0 : BlockBand.External.PSSS.eigenCount A (Icc (e - ε) (e + ε)) = 0) (y : ι → ℂ) :
    ε * l2Norm y ≤ l2Norm ((A.1 - (e : ℂ) • 1) *ᵥ y) := by
  refine regularEvent_spectral_lower A.2 hε (fun j => ?_) y
  by_contra hlt'
  have hlt := not_le.mp hlt'
  unfold BlockBand.External.PSSS.eigenCount at h0
  have hempty := Finset.card_eq_zero.mp h0
  set i := ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm j).rev
  have hval : BlockBand.Foundations.Spectral.increasingEigenvalue A.2 i = A.2.eigenvalues j := by
    unfold BlockBand.Foundations.Spectral.increasingEigenvalue
    simp only [i, Fin.rev_rev]
    rfl
  have hmem : BlockBand.Foundations.Spectral.increasingEigenvalue A.2 i ∈ Icc (e - ε) (e + ε) := by
    rw [hval]
    have := abs_lt.mp hlt
    exact ⟨by linarith, by linarith⟩
  exact Finset.eq_empty_iff_forall_notMem.mp hempty i
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem)

/-- **Pole bound** (from `PhysicalBlockConditionalCount` at `Φ = 0`, `r = 1`).
One `C₁ > 0` first; for every `p`, model, set `R` of blocks, `e` and `ε > 0`, the physical
probability that `H_RR - e` fails the lower bound `ε‖y‖ ≤ ‖(H_RR - e)y‖` is at most
`C₁/√c · |R|W · 2ε`.
-/
theorem regularEvent_pole_law (hPC : PhysicalBlockConditionalCount) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (p : Parameters) (model : p.GaussianRingModel)
      (R : Finset (ZMod p.n)) (e ε : ℝ), 0 < ε →
      (model.law : Measure p.SiteMatrix) {H | ¬ ∀ y : BlockSites p R → ℂ,
          ε * l2Norm y ≤ l2Norm ((H.submatrix (Subtype.val : BlockSites p R → p.Site) Subtype.val -
            (e : ℂ) • 1) *ᵥ y)} ≤
        ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε)) := by
  obtain ⟨C₁, hC₁, hall⟩ := hPC
  refine ⟨C₁, hC₁, fun p model R e ε hε => ?_⟩
  set Φ₀ : p.SiteMatrix → BlockBand.External.PSSS.HermitianMatrix (BlockSites p R) :=
    fun _ => ⟨0, isHermitian_zero⟩
  obtain ⟨hint, hbound⟩ := hall p model R Φ₀ measurable_const (e - ε) (e + ε) (by linarith) 1
    le_rfl
  set fc := BlockBand.External.PSSS.factorialCount (subsystemCount p R Φ₀ (Icc (e - ε) (e + ε))) 1
  have hfc0 : ∀ H, 0 ≤ fc H := fun H => Nat.cast_nonneg _
  have hsub : {H : p.SiteMatrix | ¬ ∀ y : BlockSites p R → ℂ,
      ε * l2Norm y ≤ l2Norm ((H.submatrix (Subtype.val : BlockSites p R → p.Site) Subtype.val -
        (e : ℂ) • 1) *ᵥ y)} ⊆ {H | ¬ H.IsHermitian} ∪ {H | 1 ≤ fc H} := by
    intro H hH
    by_contra hcon
    have hHerm : H.IsHermitian := by
      by_contra h
      exact hcon (Or.inl h)
    have hlt : fc H < 1 := by
      by_contra h
      exact hcon (Or.inr (not_lt.mp h))
    apply hH
    have hcount : subsystemCount p R Φ₀ (Icc (e - ε) (e + ε)) H = 0 := by
      have : (subsystemCount p R Φ₀ (Icc (e - ε) (e + ε)) H : ℝ) < 1 := by
        simpa [fc, BlockBand.External.PSSS.factorialCount, Nat.descFactorial_one] using hlt
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    have hlow := regularEvent_lower_of_count_zero _ hε.le hcount
    have hHV : (p.physicalHermitianVersion H).1 = H :=
      p.gaussianReconstruction_gaussianExtraction H hHerm
    intro y
    have := hlow y
    simp only [Φ₀, add_zero] at this
    rwa [hHV] at this
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hH0 : (model.law : Measure p.SiteMatrix) {H | ¬ H.IsHermitian} = 0 := by
    have := model.isPhysical.1
    rwa [ae_iff] at this
  rw [hH0, zero_add]
  refine (regularEvent_markov_integral _ hfc0 hint one_pos).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_one]
  refine hbound.trans (le_of_eq ?_)
  rw [pow_one]
  ring

end Pole

/-!
## 4. Transport from the pair splitting law
-/

section PairTransport

variable {p : Parameters} {i : ZMod p.n}

/-- **Outer-measure transport** from the pair splitting law: if for every `ω ∈ B` and every
fresh `G` either the reassembly lies in `S` or `G ∈ S'`, then `Pω B ≤ P(S) + GUE(S')`. -/
theorem regularEvent_pair_le_law {model : p.GaussianRingModel} {s : ℝ}
    {Pω : Measure (SplitState p i)} (h : IsPairSplitting p i model s Pω)
    (B : Set (SplitState p i)) (S : Set p.SiteMatrix) (S' : Set (PairMatrix p i))
    (hBS : ∀ ω ∈ B, ∀ G, assemble p i ω G ∈ S ∨ G ∈ S') :
    Pω B ≤ (model.law : Measure p.SiteMatrix) S + gueMeasure (PairSite p i) (pairTime p s) S' := by
  have := regularEvent_isProbabilityMeasure_gue (PairSite p i) (pairTime p s)
  have := PoleExclusion.isProbabilityMeasure_of_splitting h
  set ν := gueMeasure (PairSite p i) (pairTime p s)
  have hB : Pω B = (Pω.prod ν) (B ×ˢ Set.univ) := by
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hsub : B ×ˢ Set.univ ⊆ (fun x : SplitState p i × PairMatrix p i => assemble p i x.1 x.2) ⁻¹' S ∪
      (Set.univ ×ˢ S') := by
    rintro ⟨ω, G⟩ ⟨hω, -⟩
    rcases hBS ω hω G with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ⟨Set.mem_univ _, h2⟩
  rw [hB]
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · rw [← h]
    exact Measure.le_map_apply (ContractClauses.measurable_assemble p i).aemeasurable S
  · rw [Measure.prod_prod, measure_univ, one_mul]

end PairTransport

/-!
## 5. Deterministic norm of the deformation on the good event
-/

section Deterministic

theorem regularEvent_ent_subtype_le {α : Type*} [Fintype α] (P Q : α → Prop) [DecidablePred P]
    [DecidablePred Q] (H : Matrix α α ℂ) :
    regularEventEnt (fun (x : {a // P a}) (y : {a // Q a}) => H x.1 y.1) ≤ regularEventEnt H := by
  unfold regularEventEnt
  calc ∑ x : {a // P a}, ∑ y : {a // Q a}, ‖H x.1 y.1‖ ≤ ∑ x : {a // P a}, ∑ b, ‖H x.1 b‖ := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← Finset.sum_subtype (Finset.univ.filter Q) (by simp) (fun b => ‖H x.1 b‖)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ a, ∑ b, ‖H a b‖ := by
        rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) (fun a => ∑ b, ‖H a b‖)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- `ent(V - C*(H_R - e)⁻¹C) ≤ ent V + ent(C)² · d_R² ε⁻¹` when `ε‖y‖ ≤ ‖(H_R - e)y‖`. -/
theorem regularEvent_ent_physicalCoareaF_le {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (H_R : Matrix α α ℂ) (C : Matrix α β ℂ) (V : Matrix β β ℂ) (e : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hlow : ∀ y, ε * l2Norm y ≤ l2Norm ((H_R - (e : ℂ) • 1) *ᵥ y)) :
    regularEventEnt (physicalCoareaF H_R C V e) ≤
      regularEventEnt V + regularEventEnt C ^ 2 * ((Fintype.card α : ℝ) ^ 2 * ε⁻¹) := by
  unfold physicalCoareaF physicalCoareaResolvent
  have hR : regularEventEnt (H_R - (e : ℂ) • 1)⁻¹ ≤ (Fintype.card α : ℝ) ^ 2 * ε⁻¹ :=
    regularEventEnt_le_card_sq_mul (regularEvent_norm_inv_entry_le hε hlow)
  refine (regularEventEnt_sub_le _ _).trans (add_le_add le_rfl ?_)
  refine (regularEventEnt_mul_le _ _).trans ?_
  have h1 := regularEventEnt_mul_le Cᴴ (H_R - (e : ℂ) • 1)⁻¹
  rw [regularEventEnt_conjTranspose] at h1
  have h0 := regularEventEnt_nonneg C
  have h0R := regularEventEnt_nonneg (H_R - (e : ℂ) • 1)⁻¹
  calc regularEventEnt (Cᴴ * (H_R - (e : ℂ) • 1)⁻¹) * regularEventEnt C
      ≤ regularEventEnt C * regularEventEnt (H_R - (e : ℂ) • 1)⁻¹ * regularEventEnt C :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ regularEventEnt C * ((Fintype.card α : ℝ) ^ 2 * ε⁻¹) * regularEventEnt C := by gcongr
    _ = _ := by ring

theorem regularEvent_normBound_reindex {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α ≃ Fin (Fintype.card α)) (F : Matrix α α ℂ) {A : ℝ}
    (h : regularEventEnt F ≤ (Fintype.card α : ℝ) ^ A) :
    NormBound (Matrix.reindex σ σ F) A := by
  intro x
  refine (regularEvent_l2Norm_mulVec_le _ x).trans ?_
  rw [Matrix.reindex_apply, regularEventEnt_submatrix_equiv]
  exact mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)

/-- Real arithmetic of the norm exponent: `u = w^{D+5}`, `2u + u² (T' w²)² u ≤ w^{3(D+5)+5}`. -/
theorem regularEvent_norm_arith {w T' D : ℝ} (hw1 : 1 ≤ w) (hD : 0 < D) (hwT : 2 + T' ^ 2 ≤ w) :
    2 * w ^ (D + 5) + (w ^ (D + 5)) ^ 2 * ((T' * w ^ 2) ^ 2 * w ^ (D + 5)) ≤
      w ^ (3 * (D + 5) + 5) := by
  have hw0 : 0 < w := by linarith
  set u := w ^ (D + 5) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hw1 (by linarith)
  have hA : w ^ (3 * (D + 5) + 5) = u ^ 3 * w ^ 5 := by
    rw [Real.rpow_add hw0, mul_comm 3 (D + 5), Real.rpow_mul hw0.le, hu]
    norm_cast
  rw [hA]
  have hw4 : 1 ≤ w ^ 4 := one_le_pow₀ hw1
  have hu3 : u ≤ u ^ 3 := by nlinarith [sq_nonneg u]
  have hT2 : 0 ≤ T' ^ 2 := sq_nonneg _
  have key : 2 + T' ^ 2 * w ^ 4 ≤ w ^ 5 := by
    have : w ^ 5 = w * w ^ 4 := by ring
    nlinarith
  calc 2 * u + u ^ 2 * ((T' * w ^ 2) ^ 2 * u) = 2 * u + u ^ 3 * (T' ^ 2 * w ^ 4) := by ring
    _ ≤ 2 * u ^ 3 + u ^ 3 * (T' ^ 2 * w ^ 4) := by linarith
    _ = u ^ 3 * (2 + T' ^ 2 * w ^ 4) := by ring
    _ ≤ u ^ 3 * w ^ 5 := mul_le_mul_of_nonneg_left key (by positivity)

/-- Real arithmetic of the probability: `K₀ w⁴ / w^{D+5} ≤ w^{-D}/2` once `2K₀ ≤ w`. -/
theorem regularEvent_prob_arith {w K₀ D : ℝ} (hw1 : 1 ≤ w) (hwK : 2 * K₀ ≤ w) :
    K₀ * w ^ 4 / w ^ (D + 5) ≤ w ^ (-D) / 2 := by
  have hw0 : 0 < w := by linarith
  have hP : 0 < w ^ D := Real.rpow_pos_of_pos hw0 D
  rw [Real.rpow_add hw0, Real.rpow_neg hw0.le]
  have h5 : w ^ (5 : ℝ) = w ^ 4 * w := by
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  rw [h5, div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (w ^ D)⁻¹ * (w ^ D * (w ^ 4 * w)) = w ^ 4 * w := by field_simp
  rw [this]
  nlinarith [pow_pos hw0 4]

end Deterministic

/-!
## 6. The norm tails
-/

section Tails

theorem regularEvent_card_site (p : Parameters) :
    (Fintype.card p.Site : ℝ) = (p.n : ℝ) * p.W := by
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
  push_cast
  ring

theorem regularEvent_card_site_le (p : Parameters) {T : ℝ} (hn : (p.n : ℝ) ≤ T * p.W) :
    (Fintype.card p.Site : ℝ) ≤ max T 1 * (p.W : ℝ) ^ 2 := by
  rw [regularEvent_card_site]
  have hW : (0 : ℝ) ≤ p.W := Nat.cast_nonneg _
  have : (p.n : ℝ) ≤ max T 1 * p.W := hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW)
  nlinarith

theorem regularEvent_c_eq (p : Parameters) {b : ℝ} (h : p.b = b) : p.c = 1 - 2 * b := by
  unfold Parameters.c
  rw [h]

/-- The exterior blocks of the pair, as a set of blocks. -/
def regularEventPairR (p : Parameters) (i : ZMod p.n) : Finset (ZMod p.n) :=
  Finset.univ.filter fun j => ¬ (j = i ∨ j = i + 1)

/-- The exterior sites of the pair are the sites of `regularEventPairR`. -/
def regularEventPairEquiv (p : Parameters) (i : ZMod p.n) :
    ExteriorSite p i ≃ BlockSites p (regularEventPairR p i) :=
  Equiv.subtypeEquivRight fun x => by simp [regularEventPairR]

/-- The sites off block `k`, as a set of blocks. -/
def regularEventBlockR (p : Parameters) (k : ZMod p.n) : Finset (ZMod p.n) :=
  Finset.univ.filter fun j => j ≠ k

def regularEventBlockEquiv (p : Parameters) (k : ZMod p.n) :
    OffBlockSite p k ≃ BlockSites p (regularEventBlockR p k) :=
  Equiv.subtypeEquivRight fun x => by simp [regularEventBlockR]

theorem regularEvent_pair_exterior_sub (p : Parameters) (i : ZMod p.n) (H : p.SiteMatrix) (e : ℝ) :
    exteriorBlock p i H - (e : ℂ) • 1 =
      (H.submatrix (Subtype.val : BlockSites p (regularEventPairR p i) → p.Site) Subtype.val -
        (e : ℂ) • 1).submatrix (regularEventPairEquiv p i) (regularEventPairEquiv p i) := by
  ext x y
  simp [exteriorBlock, Matrix.one_apply, regularEventPairEquiv, Subtype.ext_iff]

theorem regularEvent_block_exterior_sub (p : Parameters) (k : ZMod p.n) (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) (e : ℝ) :
    ω.1 - (e : ℂ) • 1 =
      ((assembleBlock p k ω G).submatrix
          (Subtype.val : BlockSites p (regularEventBlockR p k) → p.Site) Subtype.val -
        (e : ℂ) • 1).submatrix (regularEventBlockEquiv p k) (regularEventBlockEquiv p k) := by
  ext x y
  simp [assembleBlock, x.2, y.2, Matrix.one_apply, regularEventBlockEquiv, Subtype.ext_iff]

theorem regularEvent_couplingBlock_assemble (p : Parameters) (i : ZMod p.n) (ω : SplitState p i)
    (G : PairMatrix p i) : couplingBlock p i (assemble p i ω G) = ω.2.1 := by
  ext x y
  simp [couplingBlock, assemble, x.2, y.2]

theorem regularEvent_card_lt (p : Parameters) (R : Finset (ZMod p.n)) :
    (((R.card * p.W : ℕ)) : ℝ) ≤ Fintype.card p.Site := by
  rw [regularEvent_card_site]
  have : R.card ≤ p.n := (Finset.card_le_univ R).trans (le_of_eq (ZMod.card p.n))
  push_cast
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (Nat.cast_nonneg _)

theorem regularEvent_pairTime_le (p : Parameters) :
    ((pairTime p (pairS p) : ℝ≥0) : ℝ) ≤ 1 := by
  unfold pairTime
  rw [Real.coe_toNNReal']
  have hs : pairS p ≤ 1 := (min_le_left _ _).trans (by linarith [p.b_lt_half])
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  refine max_le ?_ zero_le_one
  rw [div_le_one (by linarith)]
  linarith

/-- **Pair norm tail**, from `PhysicalBlockConditionalCount`. `b`, `T` first; for every `D > 0` a width `W₀`; with the norm
exponent `A = 3(D+5)+5`, for `W ≥ W₀`, `n ≤ TW`, every model, pair, splitting law at `pairS p`,
reindexing `σ` and every real `e`:
`Pω{¬ NormBound (pairDeformation σ ω e) A} ≤ W^{-D}/2`.
-/
theorem regularEvent_pair_norm_tail (hPC : PhysicalBlockConditionalCount) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (T : ℝ) :
    ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (pairS p) Pω →
    ∀ (σ : PairSite p i ≃ Fin (Fintype.card (PairSite p i))) (e : ℝ),
      Pω {ω | ¬ NormBound (pairDeformation p i σ ω e) (3 * (D + 5) + 5)} ≤
        ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) := by
  obtain ⟨C₁, hC₁, hpole⟩ := regularEvent_pole_law hPC
  intro D hD
  have hc : 0 < 1 - 2 * b := by linarith
  set T' := max T 1
  set K₀ : ℝ := 2 * C₁ / Real.sqrt (1 - 2 * b) * T' + 4 * T' ^ 2 + 16
  refine ⟨⌈max (2 + T' ^ 2) (2 * K₀)⌉₊ + 1, ?_⟩
  intro p hpb hW hn model i Pω hsplit σ e
  set w : ℝ := (p.W : ℝ) with hwdef
  have hWx : max (2 + T' ^ 2) (2 * K₀) ≤ w := by
    have h1 := Nat.le_ceil (max (2 + T' ^ 2) (2 * K₀))
    have h2 : ((⌈max (2 + T' ^ 2) (2 * K₀)⌉₊ : ℕ) : ℝ) ≤ w := by
      rw [hwdef]; exact_mod_cast (Nat.le_succ _).trans hW
    linarith
  have hT1 : 1 ≤ T' := le_max_right _ _
  have hw1 : 1 ≤ w := by
    have := le_max_left (2 + T' ^ 2) (2 * K₀)
    nlinarith
  have hw0 : 0 < w := by linarith
  set u : ℝ := w ^ (D + 5)
  have hu1 : 1 ≤ u := Real.one_le_rpow hw1 (by linarith)
  have hu0 : 0 < u := by linarith
  set ε : ℝ := u⁻¹
  have hε : 0 < ε := inv_pos.mpr hu0
  have hN := regularEvent_card_site_le p hn
  have hNpos : (0 : ℝ) ≤ Fintype.card p.Site := Nat.cast_nonneg _
  set R := regularEventPairR p i
  set SR : Set p.SiteMatrix := {H | ¬ ∀ y : BlockSites p R → ℂ,
      ε * l2Norm y ≤ l2Norm ((H.submatrix (Subtype.val : BlockSites p R → p.Site) Subtype.val -
        (e : ℂ) • 1) *ᵥ y)}
  set B1 : Set (SplitState p i) :=
    {ω | ¬ ∀ y, ε * l2Norm y ≤ l2Norm ((ω.1 - (e : ℂ) • 1) *ᵥ y)}
  set B2 : Set (SplitState p i) := {ω | u ≤ regularEventEnt ω.2.1}
  set B3 : Set (SplitState p i) := {ω | 2 * u ≤ regularEventEnt ω.2.2}
  have hcardP : (Fintype.card (PairSite p i) : ℝ) = 2 * w := by
    rw [ContractClauses.card_pairSite]; push_cast; ring
  -- the bad event is covered by the three elementary events
  have hcover : {ω | ¬ NormBound (pairDeformation p i σ ω e) (3 * (D + 5) + 5)} ⊆
      B1 ∪ B2 ∪ B3 := by
    intro ω hω
    by_contra hcon
    have h1 : ∀ y, ε * l2Norm y ≤ l2Norm ((ω.1 - (e : ℂ) • 1) *ᵥ y) := by
      by_contra h; exact hcon (Or.inl (Or.inl h))
    have h2 : regularEventEnt ω.2.1 < u := by
      by_contra h; exact hcon (Or.inl (Or.inr (not_lt.mp h)))
    have h3 : regularEventEnt ω.2.2 < 2 * u := by
      by_contra h; exact hcon (Or.inr (not_lt.mp h))
    apply hω
    unfold pairDeformation
    refine regularEvent_normBound_reindex σ _ ?_
    have hF := regularEvent_ent_physicalCoareaF_le ω.1 ω.2.1 ω.2.2 e hε h1
    have hdR : (Fintype.card (ExteriorSite p i) : ℝ) ≤ T' * w ^ 2 :=
      (by exact_mod_cast Fintype.card_subtype_le _ : (Fintype.card (ExteriorSite p i) : ℝ) ≤
        Fintype.card p.Site).trans hN
    have hC2 : regularEventEnt ω.2.1 ^ 2 ≤ u ^ 2 :=
      pow_le_pow_left₀ (regularEventEnt_nonneg _) h2.le 2
    have hR2 : (Fintype.card (ExteriorSite p i) : ℝ) ^ 2 * ε⁻¹ ≤ (T' * w ^ 2) ^ 2 * u := by
      rw [inv_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hdR 2) hu0.le
    have hmain := regularEvent_norm_arith (T' := T') hw1 hD ((le_max_left _ _).trans hWx)
    have hA0 : (0 : ℝ) ≤ 3 * (D + 5) + 5 := by linarith
    calc regularEventEnt (physicalCoareaF ω.1 ω.2.1 ω.2.2 e)
        ≤ 2 * u + u ^ 2 * ((T' * w ^ 2) ^ 2 * u) := by
          refine hF.trans (add_le_add h3.le ?_)
          exact mul_le_mul hC2 hR2 (by positivity) (by positivity)
      _ ≤ w ^ (3 * (D + 5) + 5) := hmain
      _ ≤ (Fintype.card (PairSite p i) : ℝ) ^ (3 * (D + 5) + 5) := by
          rw [hcardP]
          exact Real.rpow_le_rpow hw0.le (by linarith) hA0
  -- the three probabilities
  have hP1 : Pω B1 ≤ ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε)) := by
    refine le_trans (regularEvent_pair_le_law hsplit B1 SR ∅ fun ω hω G => ?_) ?_
    · left
      intro hlow
      apply hω
      intro y
      rw [← PoleExclusion.exteriorBlock_assemble p i ω G, regularEvent_pair_exterior_sub]
      exact regularEvent_lower_submatrix _ hlow y
    · rw [measure_empty, add_zero]
      exact hpole p model R e ε hε
  have hP2 : Pω B2 ≤ ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) := by
    refine le_trans (regularEvent_pair_le_law hsplit B2 {H | u ≤ regularEventEnt H} ∅
      fun ω hω G => ?_) ?_
    · left
      change u ≤ regularEventEnt _
      refine le_trans hω ?_
      rw [← regularEvent_couplingBlock_assemble p i ω G]
      exact regularEvent_ent_subtype_le _ _ _
    · rw [measure_empty, add_zero]
      exact regularEvent_law_ent_tail p model hu0
  have hP3 : Pω B3 ≤ ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) +
      ENNReal.ofReal (4 * (Fintype.card (PairSite p i) : ℝ) ^ 2 / u) := by
    refine le_trans (regularEvent_pair_le_law hsplit B3 {H | u ≤ regularEventEnt H}
      {G | u ≤ regularEventEnt G} fun ω hω G => ?_) (add_le_add
        (regularEvent_law_ent_tail p model hu0)
        (regularEvent_gue_ent_tail (regularEvent_pairTime_le p) hu0))
    have hV : ω.2.2 = pairBlock p i (assemble p i ω G) - G := by
      rw [PoleExclusion.pairBlock_assemble]; abel
    have hle : regularEventEnt ω.2.2 ≤ regularEventEnt (assemble p i ω G) + regularEventEnt G := by
      rw [hV]
      exact (regularEventEnt_sub_le _ _).trans (add_le_add (regularEvent_ent_subtype_le _ _ _) le_rfl)
    change 2 * u ≤ regularEventEnt ω.2.2 at hω
    by_contra hcon
    have ha : regularEventEnt (assemble p i ω G) < u := by
      by_contra h; exact hcon (Or.inl (not_lt.mp h))
    have hb : regularEventEnt G < u := by
      by_contra h; exact hcon (Or.inr (not_lt.mp h))
    linarith
  -- the sum
  have hsum : C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) +
      2 * (Fintype.card p.Site : ℝ) ^ 2 / u + (2 * (Fintype.card p.Site : ℝ) ^ 2 / u +
        4 * (Fintype.card (PairSite p i) : ℝ) ^ 2 / u) ≤ K₀ * w ^ 4 / u := by
    rw [regularEvent_c_eq p hpb, hcardP]
    have hRc := (regularEvent_card_lt p R).trans hN
    have hs : 0 < Real.sqrt (1 - 2 * b) := Real.sqrt_pos.mpr hc
    have hw2 : w ^ 2 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
    have hk : 0 ≤ C₁ / Real.sqrt (1 - 2 * b) := by positivity
    have e1 : C₁ / Real.sqrt (1 - 2 * b) * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) ≤
        2 * C₁ / Real.sqrt (1 - 2 * b) * T' * w ^ 4 / u := by
      have : C₁ / Real.sqrt (1 - 2 * b) * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) =
          2 * (C₁ / Real.sqrt (1 - 2 * b)) * ((R.card * p.W : ℕ) : ℝ) / u := by
        simp only [ε]; field_simp
      rw [this, show 2 * C₁ / Real.sqrt (1 - 2 * b) * T' * w ^ 4 =
        2 * (C₁ / Real.sqrt (1 - 2 * b)) * (T' * w ^ 4) by ring]
      refine div_le_div_of_nonneg_right ?_ hu0.le
      refine mul_le_mul_of_nonneg_left (hRc.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left hw2 (by linarith)
    have e2 : 2 * (Fintype.card p.Site : ℝ) ^ 2 / u ≤ 2 * T' ^ 2 * w ^ 4 / u := by
      refine div_le_div_of_nonneg_right ?_ hu0.le
      have := pow_le_pow_left₀ hNpos hN 2
      nlinarith
    have e3 : 4 * (2 * w) ^ 2 / u ≤ 16 * w ^ 4 / u := by
      refine div_le_div_of_nonneg_right ?_ hu0.le
      nlinarith
    have : K₀ * w ^ 4 / u = 2 * C₁ / Real.sqrt (1 - 2 * b) * T' * w ^ 4 / u +
        2 * T' ^ 2 * w ^ 4 / u + (2 * T' ^ 2 * w ^ 4 / u + 16 * w ^ 4 / u) := by
      simp only [K₀]; ring
    rw [this]
    linarith
  have hK0 : 2 * K₀ ≤ w := (le_max_right _ _).trans hWx
  calc Pω {ω | ¬ NormBound (pairDeformation p i σ ω e) (3 * (D + 5) + 5)}
      ≤ Pω (B1 ∪ B2 ∪ B3) := measure_mono hcover
    _ ≤ Pω B1 + Pω B2 + Pω B3 :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε)) +
          ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) +
          (ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) +
            ENNReal.ofReal (4 * (Fintype.card (PairSite p i) : ℝ) ^ 2 / u)) := by
        gcongr
    _ = ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) +
          2 * (Fintype.card p.Site : ℝ) ^ 2 / u + (2 * (Fintype.card p.Site : ℝ) ^ 2 / u +
            4 * (Fintype.card (PairSite p i) : ℝ) ^ 2 / u)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (K₀ * w ^ 4 / u) := ENNReal.ofReal_le_ofReal hsum
    _ ≤ ENNReal.ofReal (w ^ (-D) / 2) :=
        ENNReal.ofReal_le_ofReal (regularEvent_prob_arith hw1 hK0)

theorem regularEvent_block_coupling_assemble (p : Parameters) (k : ZMod p.n) (ω : BlockState p k)
    (G : Matrix (BlockSite p k) (BlockSite p k) ℂ) :
    (fun (x : OffBlockSite p k) (y : BlockSite p k) => assembleBlock p k ω G x.1 y.1) = ω.2 := by
  funext x y
  simp [assembleBlock, x.2, y.2]

/-- **One-block norm tail**, from `PhysicalBlockConditionalCount`. `b`, `T` first; for every `D > 0` a width `W₀`; with
`A = 3(D+5)+5`, for `W ≥ W₀`, `n ≤ TW`, every model, block `k`, one-block splitting law,
reindexing `σ` and every real `e`:
`Pω{¬ NormBound (blockDeformation σ ω e) A} ≤ W^{-D}/2`.
-/
theorem regularEvent_block_norm_tail (hPC : PhysicalBlockConditionalCount) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (T : ℝ) :
    ∀ D : ℝ, 0 < D → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (k : ZMod p.n) (Pω : Measure (BlockState p k)),
      IsBlockSplitting p k model Pω →
    ∀ (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (e : ℝ),
      Pω {ω | ¬ NormBound (blockDeformation p k σ ω e) (3 * (D + 5) + 5)} ≤
        ENNReal.ofReal ((p.W : ℝ) ^ (-D) / 2) := by
  obtain ⟨C₁, hC₁, hpole⟩ := regularEvent_pole_law hPC
  intro D hD
  have hc : 0 < 1 - 2 * b := by linarith
  set T' := max T 1
  set K₀ : ℝ := 2 * C₁ / Real.sqrt (1 - 2 * b) * T' + 4 * T' ^ 2 + 16
  refine ⟨⌈max (2 + T' ^ 2) (2 * K₀)⌉₊ + 1, ?_⟩
  intro p hpb hW hn model k Pω hsplit σ e
  set w : ℝ := (p.W : ℝ) with hwdef
  have hWx : max (2 + T' ^ 2) (2 * K₀) ≤ w := by
    have h1 := Nat.le_ceil (max (2 + T' ^ 2) (2 * K₀))
    have h2 : ((⌈max (2 + T' ^ 2) (2 * K₀)⌉₊ : ℕ) : ℝ) ≤ w := by
      rw [hwdef]; exact_mod_cast (Nat.le_succ _).trans hW
    linarith
  have hT1 : 1 ≤ T' := le_max_right _ _
  have hw1 : 1 ≤ w := by
    have := le_max_left (2 + T' ^ 2) (2 * K₀)
    nlinarith
  have hw0 : 0 < w := by linarith
  set u : ℝ := w ^ (D + 5)
  have hu1 : 1 ≤ u := Real.one_le_rpow hw1 (by linarith)
  have hu0 : 0 < u := by linarith
  set ε : ℝ := u⁻¹
  have hε : 0 < ε := inv_pos.mpr hu0
  have hN := regularEvent_card_site_le p hn
  have hNpos : (0 : ℝ) ≤ Fintype.card p.Site := Nat.cast_nonneg _
  set R := regularEventBlockR p k
  set SR : Set p.SiteMatrix := {H | ¬ ∀ y : BlockSites p R → ℂ,
      ε * l2Norm y ≤ l2Norm ((H.submatrix (Subtype.val : BlockSites p R → p.Site) Subtype.val -
        (e : ℂ) • 1) *ᵥ y)}
  set B1 : Set (BlockState p k) :=
    {ω | ¬ ∀ y, ε * l2Norm y ≤ l2Norm ((ω.1 - (e : ℂ) • 1) *ᵥ y)}
  set B2 : Set (BlockState p k) := {ω | u ≤ regularEventEnt ω.2}
  have hcardB : (Fintype.card (BlockSite p k) : ℝ) = w := by
    rw [regularEvent_card_blockSite]
  have hcover : {ω | ¬ NormBound (blockDeformation p k σ ω e) (3 * (D + 5) + 5)} ⊆ B1 ∪ B2 := by
    intro ω hω
    by_contra hcon
    have h1 : ∀ y, ε * l2Norm y ≤ l2Norm ((ω.1 - (e : ℂ) • 1) *ᵥ y) := by
      by_contra h; exact hcon (Or.inl h)
    have h2 : regularEventEnt ω.2 < u := by
      by_contra h; exact hcon (Or.inr (not_lt.mp h))
    apply hω
    unfold blockDeformation blockF
    refine regularEvent_normBound_reindex σ _ ?_
    have hF := regularEvent_ent_physicalCoareaF_le ω.1 ω.2 0 e hε h1
    have hdR : (Fintype.card (OffBlockSite p k) : ℝ) ≤ T' * w ^ 2 :=
      (by exact_mod_cast Fintype.card_subtype_le _ : (Fintype.card (OffBlockSite p k) : ℝ) ≤
        Fintype.card p.Site).trans hN
    have hC2 : regularEventEnt ω.2 ^ 2 ≤ u ^ 2 :=
      pow_le_pow_left₀ (regularEventEnt_nonneg _) h2.le 2
    have hR2 : (Fintype.card (OffBlockSite p k) : ℝ) ^ 2 * ε⁻¹ ≤ (T' * w ^ 2) ^ 2 * u := by
      rw [inv_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hdR 2) hu0.le
    have hmain := regularEvent_norm_arith (T' := T') hw1 hD ((le_max_left _ _).trans hWx)
    have hA0 : (0 : ℝ) ≤ 3 * (D + 5) + 5 := by linarith
    have h0 : regularEventEnt (0 : Matrix (BlockSite p k) (BlockSite p k) ℂ) = 0 := by
      simp [regularEventEnt]
    calc regularEventEnt (physicalCoareaF ω.1 ω.2 0 e)
        ≤ 2 * u + u ^ 2 * ((T' * w ^ 2) ^ 2 * u) := by
          refine hF.trans ?_
          rw [h0]
          exact add_le_add (by linarith) (mul_le_mul hC2 hR2 (by positivity) (by positivity))
      _ ≤ w ^ (3 * (D + 5) + 5) := hmain
      _ = (Fintype.card (BlockSite p k) : ℝ) ^ (3 * (D + 5) + 5) := by rw [hcardB]
  have hP1 : Pω B1 ≤ ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε)) := by
    refine le_trans (regularEvent_block_le_law hsplit B1 SR fun ω hω G => ?_) ?_
    · intro hlow
      apply hω
      intro y
      rw [regularEvent_block_exterior_sub p k ω G]
      exact regularEvent_lower_submatrix _ hlow y
    · exact hpole p model R e ε hε
  have hP2 : Pω B2 ≤ ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) := by
    refine le_trans (regularEvent_block_le_law hsplit B2 {H | u ≤ regularEventEnt H}
      fun ω hω G => ?_) (regularEvent_law_ent_tail p model hu0)
    change u ≤ regularEventEnt _
    refine le_trans hω ?_
    rw [← regularEvent_block_coupling_assemble p k ω G]
    exact regularEvent_ent_subtype_le _ _ _
  have hsum : C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) +
      2 * (Fintype.card p.Site : ℝ) ^ 2 / u ≤ K₀ * w ^ 4 / u := by
    rw [regularEvent_c_eq p hpb]
    have hRc := (regularEvent_card_lt p R).trans hN
    have hs : 0 < Real.sqrt (1 - 2 * b) := Real.sqrt_pos.mpr hc
    have hw2 : w ^ 2 ≤ w ^ 4 := pow_le_pow_right₀ hw1 (by norm_num)
    have e1 : C₁ / Real.sqrt (1 - 2 * b) * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) ≤
        2 * C₁ / Real.sqrt (1 - 2 * b) * T' * w ^ 4 / u := by
      have : C₁ / Real.sqrt (1 - 2 * b) * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) =
          2 * (C₁ / Real.sqrt (1 - 2 * b)) * ((R.card * p.W : ℕ) : ℝ) / u := by
        simp only [ε]; field_simp
      rw [this, show 2 * C₁ / Real.sqrt (1 - 2 * b) * T' * w ^ 4 =
        2 * (C₁ / Real.sqrt (1 - 2 * b)) * (T' * w ^ 4) by ring]
      refine div_le_div_of_nonneg_right ?_ hu0.le
      refine mul_le_mul_of_nonneg_left (hRc.trans ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left hw2 (by linarith)
    have e2 : 2 * (Fintype.card p.Site : ℝ) ^ 2 / u ≤ 2 * T' ^ 2 * w ^ 4 / u := by
      refine div_le_div_of_nonneg_right ?_ hu0.le
      have := pow_le_pow_left₀ hNpos hN 2
      nlinarith
    have e3 : 0 ≤ (2 * T' ^ 2 * w ^ 4 + 16 * w ^ 4) / u := by positivity
    have : K₀ * w ^ 4 / u = 2 * C₁ / Real.sqrt (1 - 2 * b) * T' * w ^ 4 / u +
        2 * T' ^ 2 * w ^ 4 / u + (2 * T' ^ 2 * w ^ 4 + 16 * w ^ 4) / u := by
      simp only [K₀]; ring
    rw [this]
    linarith
  have hK0 : 2 * K₀ ≤ w := (le_max_right _ _).trans hWx
  calc Pω {ω | ¬ NormBound (blockDeformation p k σ ω e) (3 * (D + 5) + 5)}
      ≤ Pω (B1 ∪ B2) := measure_mono hcover
    _ ≤ Pω B1 + Pω B2 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε)) +
          ENNReal.ofReal (2 * (Fintype.card p.Site : ℝ) ^ 2 / u) := add_le_add hP1 hP2
    _ = ENNReal.ofReal (C₁ / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (2 * ε) +
          2 * (Fintype.card p.Site : ℝ) ^ 2 / u) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (K₀ * w ^ 4 / u) := ENNReal.ofReal_le_ofReal hsum
    _ ≤ ENNReal.ofReal (w ^ (-D) / 2) :=
        ENNReal.ofReal_le_ofReal (regularEvent_prob_arith hw1 hK0)

end Tails

end BlockBand.Endpoints.Normalization
