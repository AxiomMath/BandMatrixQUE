module

public import BlockBand.Endpoints.Poisson.PoissonEndpointDefs
public import BlockBand.Endpoints.Sine.LocalMassFlatDensity
public import BlockBand.Counting.PhysicalFactorialConsequences

/-!
# The Laplace functional of independent rings

We compare the Laplace functional of a direct sum of independent physical rings with the unit
Poisson Laplace functional.

* `pe_charpoly_directSum`, `pe_rawSum_directSum`: the spectrum of `⊕ᵢ Hᵢ` is the union of the
  spectra, so `Tr f(Λ(⊕ᵢHᵢ - E)) = Σᵢ Tr f(Λ(Hᵢ - E))` on Hermitian blocks.
* `pe_bonferroni`, `pe_pairSum_le`: the Bonferroni bound for one ring, with
  `Σ_{j<l} h_j h_l ≤ (k)₂/2`.
* `pe_oneRing_linear`: the linearization for one ring at every finite width, from the factorial
  bound of the counting theorem (`physicalUnfoldedIntervalCount_factorialBound`, PSSS
  `SourceContract`), with the global unfolding `Λ = Nρ(E)` of the whole system.
* `pe_ringMean_tendsto`: the critical mean of one ring, from the critical-density theorem.
* `pe_independentRingLaplace`: the independent-ring Laplace bound
  `limsup_W |E e^{-Σᵢ Yᵢ} - exp(-∫(1 - e^{-f}))| ≤ C_f Σᵢ aᵢ²`, for a partition fixed before
  `W → ∞`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix Polynomial
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.InputsRing
open BlockBand.Internal.Contracts.Clocks (microCoord)
open BlockBand.Model.Construction
open scoped ENNReal

/-!
## 1. The spectrum of a direct sum
-/

def pe_blockIndex {r W : ℕ} (n : Fin r → ℕ) (x : Fin (∑ i, n i) × Fin W) : Fin r :=
  (finSigmaFinEquiv.symm x.1).1

def pe_blockEmbed {r W : ℕ} (n : Fin r → ℕ) (k : Fin r) :
    Fin (n k) × Fin W ≃ {x : Fin (∑ i, n i) × Fin W // pe_blockIndex n x = k} where
  toFun a := ⟨(finSigmaFinEquiv ⟨k, a.1⟩, a.2), by simp [pe_blockIndex]⟩
  invFun x := (Fin.cast (congrArg n x.2) (finSigmaFinEquiv.symm x.1.1).2, x.1.2)
  left_inv a := by
    refine Prod.ext (Fin.ext ?_) rfl
    exact congrArg (fun s : (Σ i, Fin (n i)) => (s.2 : ℕ)) (Equiv.symm_apply_apply _ _)
  right_inv x := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := x
    simp only [pe_blockIndex] at hx
    subst hx
    refine Subtype.ext (Prod.ext ?_ rfl)
    simp only
    conv_rhs => rw [← finSigmaFinEquiv.apply_symm_apply x1]
    rfl

theorem pe_directSum_apply_embed {r W : ℕ} (n : Fin r → ℕ)
    (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) (k : Fin r)
    (a c : Fin (n k) × Fin W) :
    directSumBlockCoords n H (finSigmaFinEquiv ⟨k, a.1⟩, a.2) (finSigmaFinEquiv ⟨k, c.1⟩, c.2) =
      H k a c := by
  have key : ∀ u v : (Σ i, Fin (n i)), u = ⟨k, a.1⟩ → v = ⟨k, c.1⟩ →
      (if h : u.1 = v.1 then H u.1 (u.2, a.2) (Fin.cast (congrArg n h).symm v.2, c.2) else 0) =
        H k a c := by
    rintro u v rfl rfl
    simp
  exact key _ _ (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _)

theorem pe_charpoly_directSum {r W : ℕ} (n : Fin r → ℕ)
    (H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ) :
    (directSumBlockCoords n H).charpoly = ∏ k, (H k).charpoly := by
  have hbt : (charmatrix (directSumBlockCoords n H)).BlockTriangular (pe_blockIndex n) := by
    intro x y hxy
    have hne : x ≠ y := fun h => by rw [h] at hxy; exact lt_irrefl _ hxy
    have hne' : (finSigmaFinEquiv.symm y.1).1 ≠ (finSigmaFinEquiv.symm x.1).1 :=
      fun h => by simp only [pe_blockIndex] at hxy; rw [h] at hxy; exact lt_irrefl _ hxy
    simp [charmatrix_apply, diagonal_apply_ne _ hne, directSumBlockCoords, hne'.symm]
  unfold Matrix.charpoly
  rw [hbt.det_fintype]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← det_submatrix_equiv_self (pe_blockEmbed n k)]
  congr 1
  refine Matrix.ext fun a c => ?_
  simp only [submatrix_apply, toSquareBlock, toSquareBlockProp, toBlock_apply, charmatrix_apply,
    pe_blockEmbed, Equiv.coe_fn_mk, pe_directSum_apply_embed]
  by_cases h : a = c
  · subst h; simp
  · have h' : ((finSigmaFinEquiv ⟨k, a.1⟩, a.2) : Fin (∑ i, n i) × Fin W) ≠
        (finSigmaFinEquiv ⟨k, c.1⟩, c.2) := by
      intro h''
      apply h
      have h1 := congrArg Prod.fst h''
      have h2 := congrArg Prod.snd h''
      simp only [EmbeddingLike.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h1
      exact Prod.ext h1 h2
    rw [diagonal_apply_ne _ h', diagonal_apply_ne _ h]

theorem pe_rawSum_directSum {r W : ℕ} (n : Fin r → ℕ) (b : ℝ) (hn : ∀ i, 4 ≤ n i) (hW : 0 < W)
    (hb : 0 < b) (hb' : b < 1 / 2)
    (H : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix)
    (hH : ∀ i, (H i).IsHermitian) (E Λ : ℝ) (f : ℝ → ℝ) :
    rawUnfoldedSpectralSum (directSumBlockCoords n
        (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))) E Λ f =
      ∑ i, rawUnfoldedSpectralSum (H i) E Λ f := by
  have hX : (directSumBlockCoords n
      (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))).IsHermitian :=
    directSumBlockCoords_isHermitian n fun i =>
      (hH i).submatrix (siteBlockEquiv (ringParameters (n i) W b (hn i) hW hb hb')).symm
  rw [rawUnfoldedSpectralSum_eq hX, unfoldedSpectralSum_eq_roots_sum]
  have hd := pe_charpoly_directSum n
    (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))
  erw [hd]
  have hprod : (∏ k, Matrix.charpoly (n := Fin (n k) × Fin W)
      (toBlockCoords (ringParameters (n k) W b (hn k) hW hb hb') (H k))) =
      ∏ k, (H k).charpoly :=
    Finset.prod_congr rfl fun k _ => Matrix.charpoly_reindex _ _
  erw [hprod]
  rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun i _ => (Matrix.charpoly_monic _).ne_zero),
    Multiset.map_bind, Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  rw [rawUnfoldedSpectralSum_eq (hH i), unfoldedSpectralSum_eq_roots_sum]

/-!
## 2. The Bonferroni bound and the linearization for one ring
-/

/-- The Bonferroni bound in product form. For `0 ≤ x ≤ 1` on a finite set `s`:
`0 ≤ Σ x - (1 - Π(1 - x)) ≤ ((Σ x)² - Σ x²)/2 = Σ_{j<l} x_j x_l`, and `0 ≤ Π(1 - x) ≤ 1`. -/
theorem pe_bonferroni {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i)
    (h1 : ∀ i, x i ≤ 1) :
    (0 ≤ ∏ i ∈ s, (1 - x i) ∧ ∏ i ∈ s, (1 - x i) ≤ 1) ∧
      0 ≤ (∑ i ∈ s, x i) - (1 - ∏ i ∈ s, (1 - x i)) ∧
      (∑ i ∈ s, x i) - (1 - ∏ i ∈ s, (1 - x i)) ≤
        ((∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, x i ^ 2) / 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨⟨hP0, hP1⟩, hg0, hgP⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have ha0 := h0 a
    have ha1 := h1 a
    refine ⟨⟨mul_nonneg (by linarith) hP0, ?_⟩, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith

/-- `Σ_{j≠l} x_j x_l ≤ k(k-1)` for `0 ≤ x ≤ 1` on a set of `k` points. -/
theorem pe_pairSum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i, 0 ≤ x i)
    (h1 : ∀ i, x i ≤ 1) :
    (∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, x i ^ 2 ≤ (s.card : ℝ) * ((s.card : ℝ) - 1) := by
  classical
  have hsum : ∀ t : Finset ι, ∑ i ∈ t, x i ≤ t.card := fun t => by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ t) => h1 i
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have ha0 := h0 a
    have ha1 := h1 a
    have hs := hsum s
    have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => h0 i
    push_cast
    nlinarith

theorem pe_increasingEigenvalue_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    BlockBand.Foundations.Spectral.increasingEigenvalue hA =
      BlockBand.Foundations.Spectral.increasingEigenvalue hB := by
  subst h; rfl

open BlockBand.External.PSSS in
/-- **Linearization for one ring** at a fixed finite width. For a physical ring
`p` (any realization), an unfolding `Λ > 0` and `f ≥ 0` continuous vanishing off `[-L, L]`,
with `Y = Tr f(Λ(H - E))` and `h = 1 - e^{-f}`:
`|E(1 - e^{-Y}) - E Tr h(Λ(H - E))| ≤ E (k)₂/2 ≤ (K · 2L · N/Λ)²/2`, `K = C_PSSS/√c`
(the counting theorem, `physicalUnfoldedIntervalCount_factorialBound`). -/
theorem pe_oneRing_linear (source : SourceContract.{0}) (p : Parameters)
    (model : p.GaussianRingModel) (E Λ L : ℝ) (hΛ : 0 < Λ) (hL : 0 ≤ L) (f : ℝ → ℝ)
    (hfc : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hfL : ∀ x, L < |x| → f x = 0) :
    |(∫ H, (1 - Real.exp (-rawUnfoldedSpectralSum H E Λ f))
        ∂(model.law : Measure p.SiteMatrix)) -
      ∫ H, rawUnfoldedSpectralSum H E Λ (fun x => 1 - Real.exp (-f x))
        ∂(model.law : Measure p.SiteMatrix)| ≤
      (source.C / Real.sqrt p.c * (2 * L) * (p.N / Λ)) ^ 2 / 2 := by
  classical
  set h : ℝ → ℝ := fun x => 1 - Real.exp (-f x) with hh_def
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    simp only [hh_def]; linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 (hf0 x))]
  have hh1 : ∀ x, h x ≤ 1 := fun x => by simp only [hh_def]; linarith [Real.exp_pos (-f x)]
  have hNpos : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  set rho : ℝ := Λ / p.N with hrho_def
  have hrho : 0 < rho := div_pos hΛ hNpos
  set k : p.SiteMatrix → ℕ := p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E rho (-L) L with hk_def
  -- pointwise Bonferroni on Hermitian matrices
  have hpt : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      |(1 - Real.exp (-rawUnfoldedSpectralSum H E Λ f)) - rawUnfoldedSpectralSum H E Λ h| ≤
        (Nat.descFactorial (k H) 2 : ℝ) / 2 := by
    filter_upwards [model.isPhysical.1] with H hH
    set x : Fin (Fintype.card p.Site) → ℝ := fun i =>
      h (Λ * (BlockBand.Model.Construction.rawIncreasingEigenvalue i H - E)) with hx_def
    set S : Finset (Fin (Fintype.card p.Site)) := Finset.univ.filter fun i =>
      Λ * (BlockBand.Model.Construction.rawIncreasingEigenvalue i H - E) ∈ Set.Icc (-L) L
    have hxS : ∀ i ∉ S, x i = 0 := by
      intro i hi
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc, not_and_or,
        not_le] at hi
      have : L < |Λ * (BlockBand.Model.Construction.rawIncreasingEigenvalue i H - E)| := by
        rcases hi with hi | hi
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact hi
      simp only [hx_def, hh_def, hfL _ this, neg_zero, Real.exp_zero, sub_self]
    have hexp : Real.exp (-rawUnfoldedSpectralSum H E Λ f) = ∏ i, (1 - x i) := by
      unfold rawUnfoldedSpectralSum
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hx_def, hh_def, sub_sub_cancel]
    have hraw : rawUnfoldedSpectralSum H E Λ h = ∑ i, x i := rfl
    obtain ⟨-, hg0, hgP⟩ := pe_bonferroni Finset.univ x (fun i => hh0 _) (fun i => hh1 _)
    have hsumS : ∑ i, x i = ∑ i ∈ S, x i :=
      (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => hxS i hi).symm
    have hsqS : ∑ i, x i ^ 2 = ∑ i ∈ S, x i ^ 2 :=
      (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by rw [hxS i hi]; ring).symm
    have hpair := pe_pairSum_le S x (fun i => hh0 _) (fun i => hh1 _)
    have hkS : k H = S.card := by
      have hv : (p.physicalHermitianVersion H).1 = H :=
        p.gaussianReconstruction_gaussianExtraction H hH
      have hfun : p.physicalUnfoldedEigenvalue ⟨0, Matrix.isHermitian_zero⟩ E rho H =
          fun i => Λ * (BlockBand.Model.Construction.rawIncreasingEigenvalue i H - E) := by
        funext i
        have he : BlockBand.Foundations.Spectral.increasingEigenvalue
            (p.physicalDeformedVersion ⟨0, Matrix.isHermitian_zero⟩ H).2 i =
            BlockBand.Model.Construction.rawIncreasingEigenvalue i H := by
          rw [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ H hH]
          exact congrFun (pe_increasingEigenvalue_congr
            (by simp [Parameters.physicalDeformedVersion, hv]) _ hH) i
        simp only [Parameters.physicalUnfoldedEigenvalue]
        rw [he, hrho_def, mul_div_cancel₀ _ hNpos.ne']
      simp only [hk_def, Parameters.physicalUnfoldedIntervalCount, hfun]
      unfold Counting.eigenvalueCount
      congr 1
      simp only [S]
    rw [hexp, hraw, Nat.cast_descFactorial_two, hkS]
    rw [hsumS, hsqS] at hgP
    rw [hsumS] at hg0 ⊢
    rw [abs_le]
    constructor <;> linarith
  -- integration
  have hfm : Measurable f := hfc.measurable
  have hhm : Measurable h := (measurable_const.sub (Real.measurable_exp.comp hfm.neg))
  have hu : Integrable (fun H => 1 - Real.exp (-rawUnfoldedSpectralSum H E Λ f))
      (model.law : Measure p.SiteMatrix) := by
    refine Integrable.of_bound ((measurable_const.sub (Real.measurable_exp.comp
      (measurable_rawUnfoldedSpectralSum E Λ hfm).neg)).aestronglyMeasurable) 1
      (Eventually.of_forall fun H => ?_)
    have h0 : 0 ≤ rawUnfoldedSpectralSum H E Λ f := Finset.sum_nonneg fun i _ => hf0 _
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [Real.exp_pos (-rawUnfoldedSpectralSum H E Λ f),
      Real.exp_le_one_iff.2 (neg_nonpos.2 h0)]
  have hv : Integrable (fun H => rawUnfoldedSpectralSum H E Λ h)
      (model.law : Measure p.SiteMatrix) := by
    refine Integrable.of_bound (measurable_rawUnfoldedSpectralSum E Λ hhm).aestronglyMeasurable
      (Fintype.card p.Site) (Eventually.of_forall fun H => ?_)
    unfold rawUnfoldedSpectralSum
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => hh0 _)]
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hh1
      (Λ * (BlockBand.Model.Construction.rawIncreasingEigenvalue i H - E))
  have hkint := model.physicalUnfoldedIntervalCount_integrable ⟨0, Matrix.isHermitian_zero⟩ E rho (-L) L 2
  have hbound := model.physicalUnfoldedIntervalCount_factorialBound source ⟨0, Matrix.isHermitian_zero⟩ E rho hrho (-L) L
    (by linarith) 2 (by norm_num)
  rw [← integral_sub hu hv]
  refine (abs_integral_le_integral_abs).trans ?_
  calc (∫ H, |(1 - Real.exp (-rawUnfoldedSpectralSum H E Λ f)) - rawUnfoldedSpectralSum H E Λ h|
        ∂(model.law : Measure p.SiteMatrix))
      ≤ ∫ H, (Nat.descFactorial (k H) 2 : ℝ) / 2 ∂(model.law : Measure p.SiteMatrix) :=
        integral_mono_ae (hu.sub hv).abs (hkint.div_const 2) hpt
    _ = (∫ H, BlockBand.External.PSSS.factorialCount k 2 H
          ∂(model.law : Measure p.SiteMatrix)) / 2 := by
        rw [integral_div]; rfl
    _ ≤ (p.physicalUnfoldedConstant source rho * (L - -L)) ^ 2 / 2 := by
        gcongr
    _ = (source.C / Real.sqrt p.c * (2 * L) * (p.N / Λ)) ^ 2 / 2 := by
        congr 1
        unfold Parameters.physicalUnfoldedConstant
        rw [hrho_def]
        have hc : 0 < Real.sqrt p.c := Real.sqrt_pos.2 p.c_pos
        field_simp
        ring

/-!
## 3. The critical mean of one ring (the critical-density theorem)
-/

/-- **Critical mean of a ring carrying a fraction of the unfolding** (from the critical-density
theorem). Rings with `n_j` blocks of width `W_j → ∞`, `n_j/W_j → σ > 0`, bond
`b`, and unfoldings `Λ_j > 0` with `N_j ρ(E)/Λ_j → a`: `E Tr h(Λ_j(H - E)) → a ∫ h` for every
continuous compactly supported `h`. -/
theorem pe_ringMean_tendsto (hDens : CriticalDensityEstimate) (b : ℝ) (hb : 0 < b)
    (hb' : b < 1 / 2) (E : ℝ) (hE : -2 < E) (hE' : E < 2) (h : ℝ → ℝ) (hc : Continuous h)
    (hcs : HasCompactSupport h) (σ a : ℝ) (hσ : 0 < σ) (ha : 0 < a) (n W : ℕ → ℕ) (hn : ∀ j, 4 ≤ n j)
    (hW : ∀ j, 0 < W j) (hWt : Tendsto W atTop atTop)
    (hratio : Tendsto (fun j => (n j : ℝ) / (W j : ℝ)) atTop (𝓝 σ))
    (models : ∀ j, (ringParameters (n j) (W j) b (hn j) (hW j) hb hb').GaussianRingModel)
    (Λ : ℕ → ℝ) (hΛ : ∀ j, 0 < Λ j)
    (hΛr : Tendsto (fun j => ((n j * W j : ℕ) : ℝ) * Parameters.semicircleDensity E / Λ j)
      atTop (𝓝 a)) :
    Tendsto (fun j => ∫ H, rawUnfoldedSpectralSum H E (Λ j) h
        ∂((models j).law : Measure (ringParameters (n j) (W j) b (hn j) (hW j) hb hb').SiteMatrix))
      atTop (𝓝 (a * ∫ x, h x)) := by
  set ρE := Parameters.semicircleDensity E with hρE_def
  have hρE : 0 < ρE := lmf_semicircleDensity_pos hE hE'
  set P : ℕ → Parameters := fun j => ringParameters (n j) (W j) b (hn j) (hW j) hb hb' with hP
  have hN : ∀ j, (0 : ℝ) < (P j).N := fun j => by exact_mod_cast (P j).N_pos
  have hNeq : ∀ j, ((P j).N : ℝ) = ((n j * W j : ℕ) : ℝ) := fun j => rfl
  -- Step 1: the exact density formula
  choose ρn hρs hρ0 hρeq using fun j => hDens.1 (P j) (models j)
  have hρc : ∀ j, Continuous (ρn j) := fun j => (hρs j).continuous
  have hformula : ∀ j, ∫ H, rawUnfoldedSpectralSum H E (Λ j) h ∂((models j).law : Measure (P j).SiteMatrix) =
      ((P j).N / Λ j) * ∫ v, ρn j (E + v / Λ j) * h v := by
    intro j
    set c : ℝ := Λ j / ((P j).N * ρE) with hc_def
    have hcpos : 0 < c := div_pos (hΛ j) (mul_pos (hN j) hρE)
    set w : ℝ → ℝ := fun u => h (u * c) with hw_def
    have hwc : Continuous w := hc.comp (continuous_id.mul continuous_const)
    have hwcs : HasCompactSupport w := by
      have := hcs.comp_smul hcpos.ne'
      simpa [hw_def, smul_eq_mul, mul_comm] using this
    have h1 : (∫ H, rawUnfoldedSpectralSum H E (Λ j) h ∂((models j).law : Measure (P j).SiteMatrix)) =
        ∫ H, ∑ α : Fin (P j).N, w (microCoord (P j) E (physicalOrderedEigenvalue (P j) H α))
          ∂((models j).law : Measure (P j).SiteMatrix) := by
      refine integral_congr_ae (Eventually.of_forall fun H => ?_)
      unfold rawUnfoldedSpectralSum
      refine (Fintype.sum_equiv (finCongr (physicalSite_card (P j))) _ _ fun i => ?_)
      simp only [hw_def, microCoord, physicalOrderedEigenvalue, physicalSpectralRank, hc_def]
      congr 1
      have : (Fin.cast (physicalSite_card (P j)).symm (finCongr (physicalSite_card (P j)) i)) = i :=
        Fin.ext rfl
      rw [this, ← hρE_def]
      field_simp
      rw [mul_div_cancel_right₀ _ (hN j).ne']
    rw [h1, lmf_windowSum_eq_density (P j) (models j) E hρE w hwc hwcs (ρn j) (hρc j) (hρ0 j)
      (hρeq j)]
    have hcv := Measure.integral_comp_mul_left (fun v => ρn j (E + v / Λ j) * h v) c
    simp only [abs_of_pos (inv_pos.2 hcpos), smul_eq_mul] at hcv
    have hrw : (fun u => ρn j (E + u / ((P j).N * ρE)) * w u) =
        fun u => ρn j (E + c * u / Λ j) * h (c * u) := by
      funext u
      simp only [hw_def, hc_def, mul_comm u]
      congr 3
      field_simp
      rw [mul_div_mul_right _ _ (hΛ j).ne']
    rw [hrw, hcv, hc_def, ← hρE_def]
    field_simp
  -- Step 2: asymptotics of `N_j/Λ_j` and `Λ_j`
  have hΛr' : Tendsto (fun j => ((P j).N : ℝ) * ρE / Λ j) atTop (𝓝 a) := hΛr
  have hWr : Tendsto (fun j => (W j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hWt
  have hNW : ∀ j, (W j : ℝ) ≤ ((P j).N : ℝ) := by
    intro j
    have : W j ≤ n j * W j := Nat.le_mul_of_pos_left _ (by have := hn j; omega)
    exact_mod_cast this
  have hatop : Tendsto Λ atTop atTop := by
    have hNt : Tendsto (fun j => ((P j).N : ℝ) * ρE) atTop atTop :=
      (tendsto_atTop_mono hNW hWr).atTop_mul_const hρE
    have hinv : Tendsto (fun j => (((P j).N : ℝ) * ρE / Λ j)⁻¹) atTop (𝓝 a⁻¹) :=
      hΛr'.inv₀ ha.ne'
    refine (hNt.atTop_mul_pos (inv_pos.2 ha) hinv).congr fun j => ?_
    have := hN j
    have := hΛ j
    field_simp
  have hNΛ : Tendsto (fun j => ((P j).N : ℝ) / Λ j) atTop (𝓝 (a / ρE)) :=
    (hΛr'.div_const ρE).congr fun j => by field_simp
  -- Step 3: `∫ ρ_{n,W}(E + v/Λ) h(v) dv → ρ(E) ∫ h`
  have hint : Tendsto (fun j => ∫ v, ρn j (E + v / Λ j) * h v) atTop
      (𝓝 (ρE * ∫ v, h v)) := by
    set κ : ℝ := (2 - |E|) / 2 with hκ_def
    have hEabs : |E| < 2 := abs_lt.mpr ⟨hE, hE'⟩
    have hκ : 0 < κ := by rw [hκ_def]; linarith
    obtain ⟨C, hC0, hC⟩ := hDens.2 b κ (2 * σ) hb hb' hκ (by linarith)
    obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ u, h u ≠ 0 → |u| ≤ L := by
      obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
        hcs.isCompact.isBounded
      refine ⟨r, fun u hu => ?_⟩
      have := hr (subset_tsupport h hu)
      simpa [Metric.mem_closedBall, Real.dist_eq] using this
    have hLa : Tendsto (fun j => L / Λ j) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hatop
    have hhint : Integrable h volume := hc.integrable_of_hasCompactSupport hcs
    set M : ℝ := (∫ v, |h v|) + 1 with hM_def
    have hM : 0 < M := by
      have : 0 ≤ ∫ v, |h v| := integral_nonneg fun v => abs_nonneg _
      rw [hM_def]; exact add_pos_of_nonneg_of_pos this one_pos
    rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / (2 * M) with hη_def
    have hη : 0 < η := by positivity
    obtain ⟨r₀, hr₀, hcont⟩ := Metric.continuousAt_iff.1
      lmf_continuous_semicircleDensity.continuousAt (ε := η / 2) (by positivity)
    set r : ℝ := min r₀ κ with hr_def
    have hr : 0 < r := lt_min hr₀ hκ
    have hc1 : ∀ᶠ j in atTop, L / Λ j < r := (tendsto_order.1 hLa).2 r hr
    have hc2 : ∀ᶠ j in atTop, C * (W j : ℝ) ^ (-(1 : ℝ) / 32) < η / 2 := by
      have h0 : Tendsto (fun j => C * (W j : ℝ) ^ (-(1 : ℝ) / 32)) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (y := 1 / 32) (by norm_num)).comp hWr
        simpa [neg_div] using this.const_mul C
      exact (tendsto_order.1 h0).2 _ (by positivity)
    have hlo : ∀ᶠ j in atTop, σ / 2 < (n j : ℝ) / W j :=
      (tendsto_order.1 hratio).1 _ (by linarith)
    have hhi : ∀ᶠ j in atTop, (n j : ℝ) / W j < 2 * σ :=
      (tendsto_order.1 hratio).2 _ (by linarith)
    have hw16 : ∀ᶠ j in atTop, (W j : ℝ) ^ (-(1 / 16 : ℝ)) ≤ σ / 16 :=
      (tendsto_order.1 ((tendsto_rpow_neg_atTop (y := 1 / 16) (by norm_num)).comp hWr)).2 _
        (by positivity) |>.mono fun _ h => h.le
    have hwinv : ∀ᶠ j in atTop, (W j : ℝ)⁻¹ ≤ σ / 16 :=
      (tendsto_order.1 (tendsto_inv_atTop_zero.comp hWr)).2 _ (by positivity) |>.mono
        fun _ h => h.le
    filter_upwards [hc1, hc2, hlo, hhi, hw16, hwinv] with j h1 h2 h3 h4 h5 h6
    have hWj : (0 : ℝ) < W j := by exact_mod_cast hW j
    have hnW : (n j : ℝ) = (n j : ℝ) / W j * W j := by field_simp
    have hadm1 : 4 * ⌈(W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ ≤ n j := by
      have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (W j : ℝ) ^ ((15 : ℝ) / 16) by positivity)
      have hsplit : (W j : ℝ) ^ ((15 : ℝ) / 16) = W j * (W j : ℝ) ^ (-(1 / 16 : ℝ)) := by
        rw [← Real.rpow_one_add' hWj.le (by norm_num)]; norm_num
      have hA : 4 * (W j : ℝ) ^ ((15 : ℝ) / 16) ≤ σ / 4 * W j := by
        rw [hsplit]; nlinarith
      have hB : (4 : ℝ) ≤ σ / 4 * W j := by
        have := mul_le_mul_of_nonneg_right h6 hWj.le
        rw [inv_mul_cancel₀ hWj.ne'] at this
        nlinarith
      have hn' : σ / 2 * W j < n j := by
        rw [hnW]; exact mul_lt_mul_of_pos_right h3 hWj
      have : (4 * ⌈(W j : ℝ) ^ ((15 : ℝ) / 16)⌉₊ : ℝ) < n j := by
        nlinarith
      exact_mod_cast this.le
    have hadm2 : (n j : ℝ) ≤ 2 * σ * W j := by
      rw [hnW]; exact (mul_lt_mul_of_pos_right h4 hWj).le
    have hdens := hC (n j) (W j) (hn j) (hW j) hadm1 hadm2 (models j) (ρn j) (hρc j) (hρeq j)
    have hpt : ∀ u, h u ≠ 0 → |ρn j (E + u / Λ j) - ρE| < η := by
      intro u hu
      have hu' := hL u hu
      have hdist : |u / Λ j| < r := by
        rw [abs_div, abs_of_pos (hΛ j)]
        exact lt_of_le_of_lt (div_le_div_of_nonneg_right hu' (hΛ j).le) h1
      have he : |E + u / Λ j| ≤ 2 - κ := by
        have := abs_add_le E (u / Λ j)
        have hrk : r ≤ κ := min_le_right _ _
        rw [hκ_def] at hrk ⊢; linarith
      have hd1 := hdens (E + u / Λ j) he
      have hd2 : |Parameters.semicircleDensity (E + u / Λ j) - ρE| < η / 2 := by
        have := hcont (x := E + u / Λ j) (by
          rw [Real.dist_eq, add_sub_cancel_left]
          exact lt_of_lt_of_le hdist (min_le_left _ _))
        rwa [Real.dist_eq] at this
      calc |ρn j (E + u / Λ j) - ρE|
          ≤ |ρn j (E + u / Λ j) - Parameters.semicircleDensity (E + u / Λ j)| +
            |Parameters.semicircleDensity (E + u / Λ j) - ρE| := abs_sub_le _ _ _
        _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (hd1.trans h2.le) hd2
        _ = η := by ring
    have hFint : Integrable (fun u => ρn j (E + u / Λ j) * h u) volume :=
      ((hρc j).comp (continuous_const.add (continuous_id.div_const _))).mul hc
        |>.integrable_of_hasCompactSupport hcs.mul_left
    rw [Real.dist_eq, ← integral_const_mul, ← integral_sub hFint (hhint.const_mul _)]
    have hbound : ‖∫ u, (ρn j (E + u / Λ j) * h u - ρE * h u)‖ ≤ ∫ u, η * |h u| := by
      refine norm_integral_le_of_norm_le (hhint.abs.const_mul _)
        (Eventually.of_forall fun u => ?_)
      by_cases hu : h u = 0
      · simp [hu]
      · rw [← sub_mul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hpt u hu).le (abs_nonneg _)
    rw [integral_const_mul] at hbound
    rw [← Real.norm_eq_abs]
    calc ‖∫ u, (ρn j (E + u / Λ j) * h u - ρE * h u)‖ ≤ η * ∫ u, |h u| := hbound
      _ ≤ η * M := mul_le_mul_of_nonneg_left (by rw [hM_def]; exact le_add_of_nonneg_right zero_le_one) hη.le
      _ = ε / 2 := by rw [hη_def]; field_simp
      _ < ε := by linarith
  -- conclusion
  have hlim := hNΛ.mul hint
  have heq : a / ρE * (ρE * ∫ v, h v) = a * ∫ x, h x := by field_simp
  rw [heq] at hlim
  exact hlim.congr fun j => (hformula j).symm

/-!
## 4. The Laplace functional of independent rings
-/

/-- `|e^{-x} - (1 - x)| ≤ x²` for `x ≥ 0`. -/
theorem pe_abs_exp_neg_sub_le {x : ℝ} (hx : 0 ≤ x) : |Real.exp (-x) - (1 - x)| ≤ x ^ 2 := by
  rcases le_total x 1 with h1 | h1
  · have := Real.abs_exp_sub_one_sub_id_le (x := -x) (by rw [abs_neg, abs_of_nonneg hx]; exact h1)
    have he : Real.exp (-x) - 1 - -x = Real.exp (-x) - (1 - x) := by ring
    rw [he, neg_sq] at this
    exact this
  · have h0 : 0 ≤ Real.exp (-x) - (1 - x) := by linarith [Real.add_one_le_exp (-x)]
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg h0]
    nlinarith

/-- `|Π u - Π v| ≤ Σ |u - v|` for factors of modulus at most one. -/
theorem pe_abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i, |u i| ≤ 1) (hv : ∀ i, |v i| ≤ 1) :
    |∏ i ∈ s, u i - ∏ i ∈ s, v i| ≤ ∑ i ∈ s, |u i - v i| := by
  classical
  have hQ : ∀ t : Finset ι, |∏ i ∈ t, v i| ≤ 1 := fun t => by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => hv i
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have e : u a * ∏ i ∈ s, u i - v a * ∏ i ∈ s, v i =
        u a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) + (u a - v a) * ∏ i ∈ s, v i := by ring
    rw [e]
    calc |u a * (∏ i ∈ s, u i - ∏ i ∈ s, v i) + (u a - v a) * ∏ i ∈ s, v i|
        ≤ |u a| * |∏ i ∈ s, u i - ∏ i ∈ s, v i| + |u a - v a| * |∏ i ∈ s, v i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (∑ i ∈ s, |u i - v i|) + |u a - v a| * 1 := by
          gcongr
          · exact hu a
          · exact hQ s
      _ = |u a - v a| + ∑ i ∈ s, |u i - v i| := by ring

/-- For a probability measure and measurable `g ≥ 0`: `0 ≤ E e^{-g} ≤ 1`, `e^{-g}` integrable. -/
theorem pe_integral_exp_neg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun x => Real.exp (-g x)) μ ∧ 0 ≤ ∫ x, Real.exp (-g x) ∂μ ∧
      ∫ x, Real.exp (-g x) ∂μ ≤ 1 := by
  have hb : ∀ x, Real.exp (-g x) ≤ 1 := fun x => Real.exp_le_one_iff.2 (by linarith [hg0 x])
  have hi : Integrable (fun x => Real.exp (-g x)) μ :=
    Integrable.of_bound (Real.measurable_exp.comp hg.neg).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hb x)
  refine ⟨hi, integral_nonneg fun x => (Real.exp_pos _).le, ?_⟩
  calc ∫ x, Real.exp (-g x) ∂μ ≤ ∫ _x, (1 : ℝ) ∂μ :=
        integral_mono hi (integrable_const 1) hb
    _ = 1 := by simp

open BlockBand.External.PSSS in

/-- **Laplace functional of independent rings.** Fix `0 < b < 1/2`, bulk `E` and `f ≥ 0` continuous with compact
support; `h = 1 - e^{-f}`. There is `K = C_f ≥ 0` such that for every partition fixed before `W → ∞` (`m`
independent physical rings with `n_i ≥ 4` blocks of common width `W → ∞`, `n_i/W → a_i τ`, `a_i > 0`, `Σ a_i = 1`,
`τ > 0`, any realizations), with the global unfolding `Λ = (Σ n_i) W ρ(E)` and `Y_i = Tr f(Λ(H_i - E))` (so
`Σ_i Y_i` is the trace of the direct sum):
`limsup_W |E e^{-Σ_i Y_i} - exp(-∫(1 - e^{-f}))| ≤ K Σ_i a_i²`,
written `∀ ε > 0, ∀ᶠ W, · ≤ K Σ a_i² + ε`. Hypotheses: the PSSS counting bound `SourceContract` and
`CriticalDensityEstimate`. -/
theorem pe_independentRingLaplace (source : SourceContract.{0})
    (hDens : CriticalDensityEstimate) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (hE : -2 < E) (hE' : E < 2) (f : ℝ → ℝ) (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (τ : ℝ), 0 < τ → (∀ i, 0 < a i) →
      ∑ i, a i = 1 → ∀ (W : ℕ → ℕ) (hW : ∀ j, 0 < W j), Tendsto W atTop atTop →
      ∀ (nb : ℕ → Fin m → ℕ) (hnb : ∀ j i, 4 ≤ nb j i),
        (∀ i, Tendsto (fun j => (nb j i : ℝ) / (W j : ℝ)) atTop (𝓝 (a i * τ))) →
      ∀ boxes : ∀ j i,
          (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').GaussianRingModel,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        |(∫ X, Real.exp (-rawUnfoldedSpectralSum (directSumBlockCoords (nb j)
              (fun i => toBlockCoords (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb')
                (X i))) E ((((∑ i, nb j i) * W j : ℕ) : ℝ) * Parameters.semicircleDensity E) f)
            ∂(Measure.pi fun i => ((boxes j i).law :
              Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix))) -
          Real.exp (-∫ x, (1 - Real.exp (-f x)))| ≤ K * ∑ i, a i ^ 2 + ε := by
  set ρE := Parameters.semicircleDensity E with hρE_def
  have hρE : 0 < ρE := lmf_semicircleDensity_pos hE hE'
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ x, L < |x| → f x = 0 := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1
      hfs.isCompact.isBounded
    refine ⟨max r 0, le_max_right _ _, fun x hx => ?_⟩
    by_contra hne
    have := hr (subset_tsupport f hne)
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith [le_max_left r 0]
  set h : ℝ → ℝ := fun x => 1 - Real.exp (-f x) with hh_def
  have hhc : Continuous h := continuous_const.sub (Real.continuous_exp.comp hfc.neg)
  have hhcs : HasCompactSupport h := hfs.mono fun x hx => by
    intro h0; apply hx; simp only [hh_def, h0, neg_zero, Real.exp_zero, sub_self]
  set Ih : ℝ := ∫ x, h x with hIh_def
  have hh0 : ∀ x, 0 ≤ h x := fun x => by
    simp only [hh_def]; linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 (hf0 x))]
  have hIh0 : 0 ≤ Ih := integral_nonneg hh0
  set K₀ : ℝ := source.C / Real.sqrt (1 - 2 * b) * (2 * L) with hK₀_def
  refine ⟨K₀ ^ 2 / (2 * ρE ^ 2) + Ih ^ 2, by positivity, ?_⟩
  intro m a τ hτ ha hsum W hW hWt nb hnb hratio boxes ε hε
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hsum
    · exact h0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set Λ : ℕ → ℝ := fun j => (((∑ i, nb j i) * W j : ℕ) : ℝ) * ρE with hΛ_def
  have hsumpos : ∀ j, 0 < ∑ i, nb j i := fun j =>
    lt_of_lt_of_le (by have := hnb j ⟨0, hm⟩; omega)
      (Finset.single_le_sum (fun i _ => Nat.zero_le (nb j i)) (Finset.mem_univ ⟨0, hm⟩))
  have hΛ : ∀ j, 0 < Λ j := fun j =>
    mul_pos (by exact_mod_cast Nat.mul_pos (hsumpos j) (hW j)) hρE
  -- ratios
  have hsumratio : Tendsto (fun j => ((∑ i, nb j i : ℕ) : ℝ) / (W j : ℝ)) atTop (𝓝 τ) := by
    have := tendsto_finsetSum Finset.univ fun i _ => hratio i
    rw [← Finset.sum_mul, hsum, one_mul] at this
    refine this.congr fun j => ?_
    push_cast
    rw [Finset.sum_div]
  have hfrac : ∀ i, Tendsto (fun j => ((nb j i * W j : ℕ) : ℝ) * ρE / Λ j) atTop
      (𝓝 (a i)) := by
    intro i
    have := (hratio i).div hsumratio hτ.ne'
    rw [mul_div_assoc, div_self hτ.ne', mul_one] at this
    refine this.congr fun j => ?_
    have hWj : (0 : ℝ) < W j := by exact_mod_cast hW j
    have hsj : (0 : ℝ) < ∑ i, (nb j i : ℝ) := by exact_mod_cast hsumpos j
    simp only [Pi.div_apply, hΛ_def]
    push_cast
    field_simp
  -- per-box quantities
  set u : Fin m → ℕ → ℝ := fun i j => ∫ X, Real.exp (-rawUnfoldedSpectralSum X E (Λ j) f)
    ∂((boxes j i).law :
      Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix) with hu_def
  set mm : Fin m → ℕ → ℝ := fun i j => ∫ X, rawUnfoldedSpectralSum X E (Λ j) h
    ∂((boxes j i).law :
      Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix) with hmm_def
  have hfm : Measurable f := hfc.measurable
  have hraw0 : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (Λ' : ℝ),
      0 ≤ rawUnfoldedSpectralSum X E Λ' f := fun X Λ' => Finset.sum_nonneg fun i _ => hf0 _
  have hu1 : ∀ i j, |u i j| ≤ 1 := by
    intro i j
    obtain ⟨-, h0, h1⟩ := pe_integral_exp_neg ((boxes j i).law :
      Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix)
      (measurable_rawUnfoldedSpectralSum E (Λ j) hfm) (fun X => hraw0 X (Λ j))
    rw [abs_le]; constructor <;> linarith
  -- (1) the one-ring linear bound
  have hlin : ∀ i j, |(1 - u i j) - mm i j| ≤
      (K₀ * (((nb j i * W j : ℕ) : ℝ) / Λ j)) ^ 2 / 2 := by
    intro i j
    have := pe_oneRing_linear source (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb')
      (boxes j i) E (Λ j) L (hΛ j) hL0 f hfc hf0 hL
    obtain ⟨hi, -, -⟩ := pe_integral_exp_neg ((boxes j i).law :
      Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix)
      (measurable_rawUnfoldedSpectralSum E (Λ j) hfm) (fun X => hraw0 X (Λ j))
    rw [integral_sub (integrable_const 1) hi] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at this
    have hc : (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').c = 1 - 2 * b := rfl
    have hN : ((ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').N : ℝ) =
        ((nb j i * W j : ℕ) : ℝ) := rfl
    rw [hc, hN] at this
    exact this
  -- (2) the critical means
  have hmean : ∀ i, Tendsto (mm i) atTop (𝓝 (a i * Ih)) := fun i =>
    pe_ringMean_tendsto hDens b hb hb' E hE hE' h hhc hhcs (a i * τ) (a i)
      (mul_pos (ha i) hτ) (ha i) (fun j => nb j i) W (fun j => hnb j i) hW hWt (hratio i)
      (fun j => boxes j i) Λ hΛ (hfrac i)
  -- (3) the count constant
  have hcount : ∀ i, Tendsto (fun j => (K₀ * (((nb j i * W j : ℕ) : ℝ) / Λ j)) ^ 2 / 2) atTop
      (𝓝 ((K₀ * (a i / ρE)) ^ 2 / 2)) := by
    intro i
    have := ((((hfrac i).div_const ρE).const_mul K₀).pow 2).div_const 2
    refine this.congr fun j => ?_
    congr 3
    field_simp
  have hev1 : ∀ᶠ j in atTop, ∀ i, |mm i j - a i * Ih| < ε / (2 * m) :=
    eventually_all.2 fun i => (Metric.tendsto_nhds.1 (hmean i)) (ε / (2 * m)) (by positivity) |>.mono
      fun j hj => by rwa [Real.dist_eq] at hj
  have hev2 : ∀ᶠ j in atTop, ∀ i, (K₀ * (((nb j i * W j : ℕ) : ℝ) / Λ j)) ^ 2 / 2 <
      (K₀ * (a i / ρE)) ^ 2 / 2 + ε / (2 * m) :=
    eventually_all.2 fun i => (tendsto_order.1 (hcount i)).2 _ (by linarith [show 0 < ε / (2 * m) by positivity])
  filter_upwards [hev1, hev2] with j hj1 hj2
  -- the product identity
  have hprod : (∫ X, Real.exp (-rawUnfoldedSpectralSum (directSumBlockCoords (nb j)
        (fun i => toBlockCoords (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb')
          (X i))) E ((((∑ i, nb j i) * W j : ℕ) : ℝ) * ρE) f)
      ∂(Measure.pi fun i => ((boxes j i).law :
        Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix))) =
      ∏ i, u i j := by
    rw [hu_def]
    simp only
    rw [← integral_fintype_prod_eq_prod (fun i X => Real.exp (-rawUnfoldedSpectralSum X E (Λ j) f))]
    refine integral_congr_ae ?_
    have hae : ∀ᵐ X ∂(Measure.pi fun i => ((boxes j i).law :
        Measure (ringParameters (nb j i) (W j) b (hnb j i) (hW j) hb hb').SiteMatrix)),
        ∀ i, (X i).IsHermitian :=
      ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval _ i).ae (boxes j i).isPhysical.1
    filter_upwards [hae] with X hX
    rw [pe_rawSum_directSum (nb j) b (hnb j) (hW j) hb hb' X hX, ← Finset.sum_neg_distrib,
      Real.exp_sum]
  have hpois : Real.exp (-∫ x, (1 - Real.exp (-f x))) = ∏ i, Real.exp (-(a i * Ih)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hprod, hpois]
  have hv1 : ∀ i, |Real.exp (-(a i * Ih))| ≤ 1 := by
    intro i
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [ha i])
  refine (pe_abs_prod_sub_prod_le Finset.univ (fun i => u i j) _ (fun i => hu1 i j) hv1).trans ?_
  have hterm : ∀ i, |u i j - Real.exp (-(a i * Ih))| ≤
      (K₀ ^ 2 / (2 * ρE ^ 2) + Ih ^ 2) * a i ^ 2 + ε / m := by
    intro i
    have e1 := hlin i j
    have e2 := (hj1 i).le
    have e3 := pe_abs_exp_neg_sub_le (mul_nonneg (ha i).le hIh0)
    have e4 := (hj2 i).le
    have htri : |u i j - Real.exp (-(a i * Ih))| ≤ |(1 - u i j) - mm i j| +
        |mm i j - a i * Ih| + |Real.exp (-(a i * Ih)) - (1 - a i * Ih)| := by
      have e : u i j - Real.exp (-(a i * Ih)) = -((1 - u i j) - mm i j) - (mm i j - a i * Ih) -
          (Real.exp (-(a i * Ih)) - (1 - a i * Ih)) := by ring
      rw [e]
      have t1 := abs_sub (-((1 - u i j) - mm i j) - (mm i j - a i * Ih))
        (Real.exp (-(a i * Ih)) - (1 - a i * Ih))
      have t2 := abs_sub (-((1 - u i j) - mm i j)) (mm i j - a i * Ih)
      rw [abs_neg] at t2
      linarith
    have hK : (K₀ * (a i / ρE)) ^ 2 / 2 = K₀ ^ 2 / (2 * ρE ^ 2) * a i ^ 2 := by
      field_simp
    have hε2 : ε / (2 * m) + ε / (2 * m) = ε / m := by field_simp; ring
    nlinarith
  calc ∑ i, |u i j - Real.exp (-(a i * Ih))|
      ≤ ∑ i, ((K₀ ^ 2 / (2 * ρE ^ 2) + Ih ^ 2) * a i ^ 2 + ε / m) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (K₀ ^ 2 / (2 * ρE ^ 2) + Ih ^ 2) * ∑ i, a i ^ 2 + ε := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp

end BlockBand.Endpoints
