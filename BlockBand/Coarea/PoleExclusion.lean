module

public import BlockBand.Coarea.PoleExclusionSpectral
public import BlockBand.Coarea.PoleExclusionArea
public import BlockBand.Coarea.PoleExclusionLaw

/-!
# The pair pole exclusion lemma: `PairPoleExclusionContract`

* `pairPoleExclusion_averaging` (the weighted spectral averaging bound). Measure: for every
  admissible `p`, exact model, rank `α`, pair `S = {i, i+1}`, `0 < s ≤ min(c,b)` and every
  pair splitting law `Pω`, for `Pω ⊗ GUE_S(s/2W).map tracelessPart`-a.e.
  `(ω, G⁰)` and every Borel `B ⊂ ℝ`, the `ζ ~ N(0, s/(2W)²)` integral of
  `m_S 1{λ_α ∈ B}`, `H(ζ) = assemble ω (G⁰ + ζ I)`, is at most `2W/√(2πs) · |B|`.
  Proof: `H(ζ) = H(0) + ζ P_S` (`assemble_add_scalar`); `λ_α(ζ)` is nondecreasing
  (`rawInc_mono`); by the scalar-part decomposition (`ae_ae_shift_of_ae`), for a.e. `(ω, G⁰)`
  and a.e. `ζ` the matrix `H(ζ)` is Hermitian with separable characteristic polynomial, and
  there the Hellmann–Feynman bound (`rawInc_hf`, `le_deriv_of_left_bound`) gives
  `m_S(ζ) ≤ λ_α'(ζ)`; the one-dimensional area inequality and the Gaussian density bound
  (`averaging_core`) conclude.
* `pairPoleExclusion_pole_probability` (the pole probability bound). Uniformly in all
  admissible `p`, models, ranks, pairs, `0 < s ≤ min(c,b)`, `ε > 0`:
  `P♯_{α,S}{∃ μ, det(H_R - μ) = 0, |λ_α - μ| < ε} ≤ n d (d+1) ε / √(2πs)`, `d = 2W`. Proof:
  a real root of `det(H_R - μ)` is an exterior eigenvalue (`exists_eigenvalue_of_det`); Cauchy
  interlacing (`interlace_le`, `le_interlace`) puts `λ_α` within `ε` of an exterior eigenvalue
  of zero-based index `j` with `α - d ≤ j ≤ α` (at most `d + 1` indices); `P♯` has density
  `(n/2) m_S` against `model.law`; the scalar-part decomposition and the averaging bound with
  `B(ω) = ⋃_j (μ_j - ε, μ_j + ε)`, `|B| ≤ 2(d+1)ε`, give the bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.PoleExclusion

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction BlockBand.QUE.Fourier
  BlockBand.Coarea BlockBand.Coarea.GUELaw BlockBand.Coarea.ContractClauses
open scoped ENNReal NNReal ComplexConjugate

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- Real diagonal weight of the projection `P_S` onto the pair coordinates. -/
def pairWeight (x : p.Site) : ℝ := if x.1 = i ∨ x.1 = i + 1 then 1 else 0

/-- The projection `P_S`. -/
def pairProj : p.SiteMatrix := diagonal fun x => (pairWeight p i x : ℂ)

theorem pairWeight_nonneg (x : p.Site) : 0 ≤ pairWeight p i x := by
  unfold pairWeight; split_ifs <;> norm_num

theorem pairWeight_le_one (x : p.Site) : pairWeight p i x ≤ 1 := by
  unfold pairWeight; split_ifs <;> norm_num

/-- `H(ζ) = H(0) + ζ P_S`. -/
theorem assemble_add_scalar (ω : SplitState p i) (G : PairMatrix p i) (ζ : ℝ) :
    assemble p i ω (G + (ζ : ℂ) • (1 : PairMatrix p i)) =
      assemble p i ω G + (ζ : ℂ) • pairProj p i := by
  ext x y
  rw [Matrix.add_apply, Matrix.smul_apply, pairProj, diagonal_apply, smul_eq_mul]
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp only [assemble, hx, hy, dite_true, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, Subtype.mk.injEq, pairWeight]
    split_ifs <;> simp; ring
  · have hxy : x ≠ y := fun h => hy (h ▸ hx)
    simp [assemble, hx, hy, hxy]
  · have hxy : x ≠ y := fun h => hx (h ▸ hy)
    simp [assemble, hx, hy, hxy]
  · simp only [assemble, hx, hy, dite_false, pairWeight]
    split_ifs <;> simp_all

theorem pairProj_isHermitian : (pairProj p i).IsHermitian := diag_isHermitian _

/-- The pair mass is the `P_S` quadratic form of the selected eigenvector. -/
theorem pairMass_eq_sum (α : Fin p.N) (H : p.SiteMatrix) :
    pairMass p i α H = ∑ x, pairWeight p i x * ‖physicalOrderedEigenvector p H α x‖ ^ 2 := by
  unfold pairMass physicalOrderedBlockMass
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_add i (i + 1) (pair_ne_succ p i) (fun k hk => ?_)]
  · simp [pairWeight, pair_ne_succ p i, (pair_ne_succ p i).symm]
  · refine Finset.sum_eq_zero fun a _ => ?_
    simp [pairWeight, hk.1, hk.2]

end Pair

theorem sqrt_const_eq (W s : ℝ) (hW : 0 < W) (hs : 0 < s) :
    (Real.sqrt (2 * Real.pi * (Real.toNNReal (s / W ^ 2) : ℝ)))⁻¹ =
      W / Real.sqrt (2 * Real.pi * s) := by
  rw [Real.coe_toNNReal _ (by positivity),
    show 2 * Real.pi * (s / W ^ 2) = (2 * Real.pi * s) / W ^ 2 by ring,
    Real.sqrt_div (by positivity), Real.sqrt_sq hW.le, inv_div]

/-- **The weighted spectral averaging bound** (`PairPoleExclusionContract.averaging`). -/
theorem pairPoleExclusion_averaging : ∀ (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ᵐ x ∂(Pω.prod ((gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart)),
      ∀ B : Set ℝ, MeasurableSet B →
        (∫⁻ ζ : ℝ, ENNReal.ofReal (pairMass p i α (assemble p i x.1 (x.2 + (ζ : ℂ) • 1))) *
            B.indicator 1 (physicalOrderedEigenvalue p (assemble p i x.1 (x.2 + (ζ : ℂ) • 1)) α)
          ∂(gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2)))) ≤
          ENNReal.ofReal (2 * (p.W : ℝ) / Real.sqrt (2 * Real.pi * s)) * volume B := by
  intro p model α i s hs _hsc Pω hsplit
  have : IsProbabilityMeasure Pω := isProbabilityMeasure_of_splitting hsplit
  set κ := (gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart with hκ
  set v := Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2) with hv
  have hW : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  have hvpos : (0 : ℝ) < v := by rw [hv, Real.coe_toNNReal _ (by positivity)]; positivity
  have hv0 : v ≠ 0 := by intro h; rw [h] at hvpos; simp at hvpos
  have hgood := ae_ae_shift_of_ae hs hsplit (Q := fun H => H.IsHermitian ∧ H.charpoly.Separable)
    (by filter_upwards [model.isPhysical.1, model.ae_charpoly_separable] with H h1 h2
        exact ⟨h1, h2⟩)
  have hω := (Measure.quasiMeasurePreserving_fst (μ := Pω) (ν := κ)).ae
    (ae_blocks_isHermitian hsplit)
  have hκH : ∀ᵐ G ∂κ, G.IsHermitian := by
    rw [hκ, ae_map_iff measurable_tracelessPart.aemeasurable measurableSet_isHermitian]
    filter_upwards [ae_isHermitian_gueMeasure (ι := PairSite p i) (pairTime p s)] with G hG
    exact tracelessPart_isHermitian hG
  have hG := (Measure.quasiMeasurePreserving_snd (μ := Pω) (ν := κ)).ae hκH
  filter_upwards [hgood, hω, hG] with x hx hxω hxG
  intro B hB
  set H₀ := assemble p i x.1 x.2 with hH₀def
  have hH₀ : H₀.IsHermitian := assemble_isHermitian p i x.1 x.2 hxω.1 hxω.2 hxG
  set r := physicalSpectralRank p α with hr
  set f : ℝ → ℝ := fun ζ => rawIncreasingEigenvalue r (H₀ + (ζ : ℂ) • pairProj p i) with hfdef
  have hf : Monotone f := rawInc_mono hH₀ (pairWeight p i) (pairWeight_nonneg p i) r
  have hlamζ : ∀ ζ : ℝ,
      physicalOrderedEigenvalue p (assemble p i x.1 (x.2 + (ζ : ℂ) • 1)) α = f ζ := by
    intro ζ; rw [assemble_add_scalar]; rfl
  simp_rw [hlamζ]
  have hm : ∀ᵐ (ζ : ℝ), ENNReal.ofReal (pairMass p i α (assemble p i x.1 (x.2 + (ζ : ℂ) • 1))) ≤
      ENNReal.ofReal (deriv f ζ) := by
    have hx' := (gaussianReal_absolutelyContinuous' 0 hv0).ae_le hx
    filter_upwards [hx', hf.ae_differentiableAt] with ζ hζ hd
    rw [assemble_add_scalar] at hζ ⊢
    obtain ⟨hA, hsep⟩ := hζ
    set A := H₀ + (ζ : ℂ) • pairProj p i with hA_def
    set ψ := physicalOrderedEigenvector p A α
    have hψ : A *ᵥ ψ = (rawIncreasingEigenvalue r A : ℂ) • ψ := by
      funext y
      rw [physicalOrderedEigenvector_eigenvector p A hA hsep α y]; rfl
    obtain ⟨g, hg, hb⟩ := rawInc_hf hA hsep (pairWeight p i) (pairWeight_nonneg p i)
      (pairWeight_le_one p i) r ψ hψ (physicalOrderedEigenvector_totalMass p A hA hsep α)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pairMass_eq_sum]
    refine le_deriv_of_left_bound hd hg (fun δ hδ hδg => ?_)
    have heq : H₀ + ((ζ - δ : ℝ) : ℂ) • pairProj p i = A - (δ : ℂ) • pairProj p i := by
      rw [hA_def]; push_cast; rw [sub_smul]; abel
    show rawIncreasingEigenvalue r (H₀ + ((ζ - δ : ℝ) : ℂ) • pairProj p i) ≤ _
    rw [heq]; exact hb δ hδ hδg
  calc _ ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * v))⁻¹ * volume B :=
        averaging_core hf _ hm hv0 hB
    _ = _ := by rw [hv, sqrt_const_eq _ _ hW hs]

section InterlaceInc

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → Prop} [DecidablePred r]

/-- Cauchy interlacing, increasing ranks: `λ_a(H) ≤ μ_a(H_R)`. -/
theorem rawInc_le_sub {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hB : (H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val).IsHermitian)
    (a : Fin (Fintype.card ι)) (j : Fin (Fintype.card {x // r x})) (h : (a : ℕ) = j) :
    rawIncreasingEigenvalue a H ≤
      rawIncreasingEigenvalue j (H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val) := by
  rw [rawInc_eq _ hH, rawInc_eq _ hB]
  have hcard : Fintype.card {x // r x} ≤ Fintype.card ι := Fintype.card_subtype_le r
  have hj := j.2
  exact le_interlace hH hB j.rev a.rev (by simp only [Fin.val_rev]; omega)

/-- Cauchy interlacing, increasing ranks: `μ_j(H_R) ≤ λ_{j+d}(H)`. -/
theorem rawInc_sub_le {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hB : (H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val).IsHermitian)
    (a : Fin (Fintype.card ι)) (j : Fin (Fintype.card {x // r x}))
    (h : (a : ℕ) = j + (Fintype.card ι - Fintype.card {x // r x})) :
    rawIncreasingEigenvalue j (H.submatrix (Subtype.val : {x // r x} → ι) Subtype.val) ≤
      rawIncreasingEigenvalue a H := by
  rw [rawInc_eq _ hH, rawInc_eq _ hB]
  have hcard : Fintype.card {x // r x} ≤ Fintype.card ι := Fintype.card_subtype_le r
  have ha := a.2
  exact interlace_le hH hB j.rev a.rev (by simp only [Fin.val_rev]; omega)

theorem rawInc_mono_index {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {j k : Fin (Fintype.card ι)}
    (h : j ≤ k) : rawIncreasingEigenvalue j A ≤ rawIncreasingEigenvalue k A := by
  rw [rawIncreasingEigenvalue_eq _ A hA, rawIncreasingEigenvalue_eq _ A hA]
  exact BlockBand.Foundations.Spectral.increasingEigenvalue_monotone hA h

end InterlaceInc

section Pole

variable (p : Parameters) (i : ZMod p.n)

/-- Codimension `d = |S|` of the exterior. -/
abbrev pairCodim : ℕ := Fintype.card p.Site - Fintype.card (ExteriorSite p i)

theorem pairCodim_eq : pairCodim p i = 2 * p.W := by
  have h1 : Fintype.card (ExteriorSite p i) =
      Fintype.card p.Site - Fintype.card (PairSite p i) :=
    Fintype.card_subtype_compl (fun x : p.Site => x.1 = i ∨ x.1 = i + 1)
  have h2 : Fintype.card (PairSite p i) ≤ Fintype.card p.Site := Fintype.card_subtype_le _
  unfold pairCodim
  rw [h1, ← card_pairSite p i]
  omega

/-- Exterior ranks `j` (zero-based) with `α - d ≤ j ≤ α`: at most `d + 1` of them. -/
def poleIndices (α : Fin p.N) : Finset (Fin (Fintype.card (ExteriorSite p i))) :=
  Finset.univ.filter fun j =>
    ((physicalSpectralRank p α).val ≤ j.val + pairCodim p i ∧ j.val ≤ (physicalSpectralRank p α).val)

theorem card_poleIndices_le (α : Fin p.N) : (poleIndices p i α).card ≤ 2 * p.W + 1 := by
  rw [← pairCodim_eq p i]
  set a : ℕ := (physicalSpectralRank p α).val
  calc (poleIndices p i α).card ≤ (Finset.Icc (a - pairCodim p i) a).card := by
        refine Finset.card_le_card_of_injOn (fun j => (j : ℕ)) ?_ ?_
        · intro j hj
          simp only [poleIndices, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hj
          simp only [Finset.coe_Icc, Set.mem_Icc]
          omega
        · intro j _ k _ h; exact Fin.ext h
    _ ≤ pairCodim p i + 1 := by rw [Nat.card_Icc]; omega

/-- The exterior-measurable set `B(ω)`: `ε`-neighbourhoods of the admissible exterior
eigenvalues. -/
def poleBand (α : Fin p.N) (ε : ℝ)
    (R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) : Set ℝ :=
  ⋃ j ∈ poleIndices p i α,
    Set.Ioo (rawIncreasingEigenvalue j R - ε) (rawIncreasingEigenvalue j R + ε)

theorem measurableSet_poleBand (α : Fin p.N) (ε : ℝ)
    (R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) : MeasurableSet (poleBand p i α ε R) :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ioo

theorem volume_poleBand_le (α : Fin p.N) (ε : ℝ)
    (R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :
    volume (poleBand p i α ε R) ≤ ENNReal.ofReal (2 * (2 * p.W + 1) * ε) := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  simp only [Real.volume_Ioo, show ∀ y : ℝ, y + ε - (y - ε) = 2 * ε from fun y => by ring,
    Finset.sum_const, nsmul_eq_mul]
  have hc : ((poleIndices p i α).card : ℝ≥0∞) ≤ ((2 * p.W + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast card_poleIndices_le p i α
  calc ((poleIndices p i α).card : ℝ≥0∞) * ENNReal.ofReal (2 * ε)
      ≤ ((2 * p.W + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * ε) := mul_le_mul_left hc _
    _ = ENNReal.ofReal (2 * (2 * p.W + 1) * ε) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; push_cast; ring

theorem measurable_exteriorBlock : Measurable (exteriorBlock p i) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply

theorem measurableSet_poleEvent (α : Fin p.N) (ε : ℝ) :
    MeasurableSet {H : p.SiteMatrix |
      physicalOrderedEigenvalue p H α ∈ poleBand p i α ε (exteriorBlock p i H)} := by
  have h : {H : p.SiteMatrix |
      physicalOrderedEigenvalue p H α ∈ poleBand p i α ε (exteriorBlock p i H)} =
      ⋃ j ∈ poleIndices p i α,
        ({H | rawIncreasingEigenvalue j (exteriorBlock p i H) - ε < physicalOrderedEigenvalue p H α} ∩
          {H | physicalOrderedEigenvalue p H α < rawIncreasingEigenvalue j (exteriorBlock p i H) + ε}) := by
    ext H; simp [poleBand]
  rw [h]
  have hμ : ∀ j : Fin (Fintype.card (ExteriorSite p i)),
      Measurable fun H : p.SiteMatrix => rawIncreasingEigenvalue j (exteriorBlock p i H) :=
    fun j => (measurable_rawIncreasingEigenvalue j).comp (measurable_exteriorBlock p i)
  have hl := measurable_physicalOrderedEigenvalue p α
  exact Finset.measurableSet_biUnion _ fun j _ =>
    (measurableSet_lt ((hμ j).sub_const ε) hl).inter (measurableSet_lt hl ((hμ j).add_const ε))

/-- **Interlacing step**: if `λ_α` lies within `ε` of an exterior eigenvalue, it lies within
`ε` of one with admissible rank (Cauchy interlacing). -/
theorem mem_poleBand {H : p.SiteMatrix} (hH : H.IsHermitian) (α : Fin p.N) {ε μ : ℝ}
    (hdet : (exteriorBlock p i H - (μ : ℂ) • 1).det = 0)
    (hlt : |physicalOrderedEigenvalue p H α - μ| < ε) :
    physicalOrderedEigenvalue p H α ∈ poleBand p i α ε (exteriorBlock p i H) := by
  have hR : (exteriorBlock p i H).IsHermitian := exteriorBlock_isHermitian p i hH
  obtain ⟨k, hk⟩ := exists_eigenvalue_of_det hR μ hdet
  set a := physicalSpectralRank p α with ha
  set lam := physicalOrderedEigenvalue p H α with hlam
  have hlam' : lam = rawIncreasingEigenvalue a H := rfl
  have hRe : exteriorBlock p i H = H.submatrix
      (Subtype.val : ExteriorSite p i → p.Site) Subtype.val := rfl
  have hcard : Fintype.card (ExteriorSite p i) ≤ Fintype.card p.Site := Fintype.card_subtype_le _
  rw [abs_sub_lt_iff] at hlt
  have hmem : ∀ j ∈ poleIndices p i α, rawIncreasingEigenvalue j (exteriorBlock p i H) - ε < lam →
      lam < rawIncreasingEigenvalue j (exteriorBlock p i H) + ε →
      lam ∈ poleBand p i α ε (exteriorBlock p i H) := by
    intro j hj h1 h2
    simp only [poleBand, Set.mem_iUnion, Set.mem_Ioo]
    exact ⟨j, hj, h1, h2⟩
  have hka := a.2
  have hkk := k.2
  by_cases hk1 : (a : ℕ) ≤ k + pairCodim p i ∧ (k : ℕ) ≤ a
  · have hkI : k ∈ poleIndices p i α := by
      simp only [poleIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk1
    refine hmem k hkI ?_ ?_ <;> rw [hk] <;> linarith
  · rcases not_and_or.mp hk1 with h | h
    · -- `k + d < a`: use `j = a - d`
      have hjlt : (a : ℕ) - pairCodim p i < Fintype.card (ExteriorSite p i) := by
        unfold pairCodim at *; omega
      set j : Fin (Fintype.card (ExteriorSite p i)) := ⟨(a : ℕ) - pairCodim p i, hjlt⟩
      have hj : j ∈ poleIndices p i α := by
        simp only [poleIndices, Finset.mem_filter, Finset.mem_univ, true_and, j]
        omega
      have h1 : rawIncreasingEigenvalue j (exteriorBlock p i H) ≤ lam := by
        rw [hlam', hRe]
        have hce : Fintype.card {x : p.Site // ¬ (x.1 = i ∨ x.1 = i + 1)} =
            Fintype.card (ExteriorSite p i) := rfl
        exact rawInc_sub_le hH (hRe ▸ hR) a j (by
          simp only [j]; rw [hce]; unfold pairCodim at *; omega)
      have h2 : rawIncreasingEigenvalue k (exteriorBlock p i H) ≤
          rawIncreasingEigenvalue j (exteriorBlock p i H) :=
        rawInc_mono_index hR (by rw [Fin.le_def]; simp only [j]; omega)
      refine hmem j hj ?_ ?_ <;> linarith
    · -- `a < k`: use `j = a`
      have hjlt : (a : ℕ) < Fintype.card (ExteriorSite p i) := by omega
      set j : Fin (Fintype.card (ExteriorSite p i)) := ⟨(a : ℕ), hjlt⟩
      have hj : j ∈ poleIndices p i α := by
        simp only [poleIndices, Finset.mem_filter, Finset.mem_univ, true_and, j]
        omega
      have h1 : lam ≤ rawIncreasingEigenvalue j (exteriorBlock p i H) := by
        rw [hlam', hRe]
        exact rawInc_le_sub hH (hRe ▸ hR) a j rfl
      have h2 : rawIncreasingEigenvalue j (exteriorBlock p i H) ≤
          rawIncreasingEigenvalue k (exteriorBlock p i H) :=
        rawInc_mono_index hR (by rw [Fin.le_def]; simp only [j]; omega)
      refine hmem j hj ?_ ?_ <;> linarith

end Pole

theorem pairWeight_coe (p : Parameters) (α : Fin p.N) (i : ZMod p.n) (H : p.SiteMatrix) :
    (physicalPairWeight p α i H : ℝ≥0∞) =
      ENNReal.ofReal ((p.n : ℝ) / 2) * ENNReal.ofReal (pairMass p i α H) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
  rfl

/-- **The pole probability bound** (`PairPoleExclusionContract.pole_probability`). -/
theorem pairPoleExclusion_pole_probability : ∀ (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b → ∀ ε : ℝ, 0 < ε →
    physicalPairMeasure p model α i
        {H | ∃ μ : ℝ, (exteriorBlock p i H - (μ : ℂ) • 1).det = 0 ∧
          |physicalOrderedEigenvalue p H α - μ| < ε} ≤
      ENNReal.ofReal ((p.n : ℝ) * (2 * p.W) * (2 * p.W + 1) * ε /
        Real.sqrt (2 * Real.pi * s)) := by
  intro p model α i s hs hsc ε hε
  obtain ⟨Pω, hsplit⟩ := coarea_splitting_exists p model i s hs hsc
  have : IsProbabilityMeasure Pω := isProbabilityMeasure_of_splitting hsplit
  set κ := (gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart with hκ
  have : IsProbabilityMeasure κ :=
    (Measure.isProbabilityMeasure_map_iff measurable_tracelessPart.aemeasurable).2 inferInstance
  set F := {H : p.SiteMatrix |
      physicalOrderedEigenvalue p H α ∈ poleBand p i α ε (exteriorBlock p i H)} with hFdef
  have hF : MeasurableSet F := measurableSet_poleEvent p i α ε
  set C : ℝ≥0∞ := ENNReal.ofReal ((p.n : ℝ) / 2) *
    (ENNReal.ofReal (2 * (p.W : ℝ) / Real.sqrt (2 * Real.pi * s)) *
      ENNReal.ofReal (2 * (2 * p.W + 1) * ε)) with hC
  have hsub : {H : p.SiteMatrix | ∃ μ : ℝ, (exteriorBlock p i H - (μ : ℂ) • 1).det = 0 ∧
      |physicalOrderedEigenvalue p H α - μ| < ε} ≤ᵐ[physicalPairMeasure p model α i] F := by
    have hHerm : ∀ᵐ H ∂physicalPairMeasure p model α i, H.IsHermitian :=
      (withDensity_absolutelyContinuous _ _).ae_le model.isPhysical.1
    filter_upwards [hHerm] with H hH hE
    obtain ⟨μ, hdet, hlt⟩ := hE
    exact mem_poleBand p i hH α hdet hlt
  have hmeasW : Measurable (F.indicator fun H => (physicalPairWeight p α i H : ℝ≥0∞)) :=
    (measurable_coe_nnreal_ennreal.comp (measurable_physicalPairWeight p α i)).indicator hF
  have hav := pairPoleExclusion_averaging p model α i s hs hsc Pω hsplit
  calc physicalPairMeasure p model α i _ ≤ physicalPairMeasure p model α i F := measure_mono_ae hsub
    _ = ∫⁻ H, F.indicator (fun H => (physicalPairWeight p α i H : ℝ≥0∞)) H
          ∂(model.law : Measure p.SiteMatrix) := by
        rw [physicalPairMeasure, withDensity_apply _ hF, lintegral_indicator hF]
    _ = ∫⁻ x, ∫⁻ (ζ : ℝ), F.indicator (fun H => (physicalPairWeight p α i H : ℝ≥0∞))
          (assemble p i x.1 (x.2 + (ζ : ℂ) • (1 : PairMatrix p i)))
          ∂gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2)) ∂(Pω.prod κ) :=
        lintegral_law_eq hs hsplit hmeasW
    _ ≤ ∫⁻ _x, C ∂(Pω.prod κ) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hav] with x hx
        set B := poleBand p i α ε x.1.1 with hB
        have hpt : ∀ ζ : ℝ, F.indicator (fun H => (physicalPairWeight p α i H : ℝ≥0∞))
            (assemble p i x.1 (x.2 + (ζ : ℂ) • (1 : PairMatrix p i))) =
            ENNReal.ofReal ((p.n : ℝ) / 2) *
              (ENNReal.ofReal (pairMass p i α (assemble p i x.1 (x.2 + (ζ : ℂ) • 1))) *
                B.indicator 1 (physicalOrderedEigenvalue p
                  (assemble p i x.1 (x.2 + (ζ : ℂ) • 1)) α)) := by
          intro ζ
          have hiff : assemble p i x.1 (x.2 + (ζ : ℂ) • (1 : PairMatrix p i)) ∈ F ↔
              physicalOrderedEigenvalue p (assemble p i x.1 (x.2 + (ζ : ℂ) • 1)) α ∈ B := by
            rw [hFdef, Set.mem_ofPred_eq, exteriorBlock_assemble]
          by_cases hmem : physicalOrderedEigenvalue p (assemble p i x.1 (x.2 + (ζ : ℂ) • 1)) α ∈ B
          · rw [Set.indicator_of_mem (hiff.mpr hmem), Set.indicator_of_mem hmem, Pi.one_apply,
              mul_one, pairWeight_coe]
          · rw [Set.indicator_of_notMem (fun h => hmem (hiff.mp h)),
              Set.indicator_of_notMem hmem, mul_zero, mul_zero]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hC]
        refine mul_le_mul_right ?_ _
        refine (hx B (measurableSet_poleBand p i α ε _)).trans ?_
        exact mul_le_mul_right (volume_poleBand_le p i α ε _) _
    _ = C := by rw [lintegral_const, measure_univ, mul_one]
    _ = _ := by
        have hsq : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
        rw [hC, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **The pair pole exclusion lemma** (`PairPoleExclusionContract`). -/
theorem pairPoleExclusionContract_holds : PairPoleExclusionContract where
  averaging := pairPoleExclusion_averaging
  pole_probability := pairPoleExclusion_pole_probability

end BlockBand.Coarea.PoleExclusion
