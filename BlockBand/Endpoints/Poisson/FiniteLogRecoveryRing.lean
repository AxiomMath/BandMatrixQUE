module

public import BlockBand.Endpoints.Poisson.FiniteLogRecovery
public import BlockBand.Internal.Contracts.InputsRing
public import BlockBand.Model.Construction.SpectralEigenvalues

/-!
# Physical finite-log recovery on rings and direct sums of rings

Law/domain: the physical law `model.law` of `p.GaussianRingModel` on `p.SiteMatrix`
(`Site = ZMod n × Fin W`), resp. the product `Measure.pi` of `r` physical ring laws with
common `W, b`, pushed to block coordinates on `Fin (Σᵢ nᵢ) × Fin W` by
`InputsRing.directSumBlockCoords`. Absorber: a union of blocks `C`, projector
`physicalBlockProjector p C` (resp. `Inputs.blockProjector C`), `B = Cᶜ`. Global unfolding
`Λ = Nρ` with `N = nW` (resp. `(Σᵢ nᵢ) W`), `ρ > 0` standing for `ρ(E)`.

Hermitian convention. The physical law is only almost surely Hermitian (first clause of
`IsPhysicalGaussianRingLaw`). `𝓡_δ^C(H; f)` (`positiveLogStatistic`) is defined for every
matrix and is used on the raw `H`. For `Tr f(Λ(H - E))` we use the raw-matrix extension of
the increasing spectrum, `BlockBand.Model.Construction.rawIncreasingEigenvalue` (exact
increasing eigenvalues on Hermitian matrices, `0` elsewhere), through `rawUnfoldedSpectralSum`.
On every Hermitian matrix it equals `unfoldedSpectralSum` of that matrix
(`rawUnfoldedSpectralSum_eq`), hence it equals `Tr f(Λ(H - E))` `model.law`-a.s.
(`ae_rawUnfoldedSpectralSum_eq`), and it also equals the trace of the counting
convention `physicalHermitianVersion` (`rawUnfoldedSpectralSum_eq_physicalHermitianVersion`).

- reindexing: `positiveLogStatistic_submatrix`, `unfoldedSpectralSum_submatrix`,
  `rawUnfoldedSpectralSum_submatrix` (any equivalence of finite index types);
  `toBlockCoords_physicalBlockProjector`, `card_compl_physicalBlockFinset`;
- a.s. faithfulness: `ae_rawUnfoldedSpectralSum_eq` (ring),
  `ae_rawUnfoldedSpectralSum_directSum_eq` (direct sum, via `directSumBlockCoords_isHermitian`);
- transfer along `Presents`: `integrable_and_integral_comp_H_of_presents`;
- `finiteLogRecovery_ring_and_ringSum`: one constant for both scopes;
  `finiteLogRecovery_ring`, `finiteLogRecovery_ringSum`: the two clauses.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ContDiff
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.InputsRing

/-!
### Deterministic reindexing
-/

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `absorbedShift` commutes with simultaneous reindexing of `H` and `P` along `e : ι ≃ κ`. -/
theorem absorbedShift_submatrix (e : ι ≃ κ) (X P : Matrix κ κ ℂ) (E Λ x a : ℝ) :
    absorbedShift (X.submatrix e e) E Λ x a (P.submatrix e e) =
      (absorbedShift X E Λ x a P).submatrix e e := by
  ext i j
  simp [absorbedShift, Matrix.one_apply, e.injective.eq_iff]

/-- **Reindexing of `𝓡_δ^C`.** For every equivalence `e : ι ≃ κ` of finite index types,
every `X, P : Matrix κ κ ℂ` (no Hermitian hypothesis), real `E, Λ, δ` and `f`:
`positiveLogStatistic (X.submatrix e e) E Λ δ (P.submatrix e e) f =
positiveLogStatistic X E Λ δ P f`. -/
theorem positiveLogStatistic_submatrix (e : ι ≃ κ) (X P : Matrix κ κ ℂ) (E Λ δ : ℝ)
    (f : ℝ → ℝ) :
    positiveLogStatistic (X.submatrix e e) E Λ δ (P.submatrix e e) f =
      positiveLogStatistic X E Λ δ P f := by
  unfold positiveLogStatistic
  simp_rw [absorbedShift_submatrix, Matrix.det_submatrix_equiv_self]

/-- `Tr f(Λ(X - E))` as a sum over the characteristic roots of a Hermitian `X`, with
multiplicity. -/
theorem unfoldedSpectralSum_eq_roots_sum {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (E Λ : ℝ) (f : ℝ → ℝ) :
    unfoldedSpectralSum X hX E Λ f =
      ((X.charpoly.roots.map Complex.re).map (fun l => f (Λ * (l - E)))).sum := by
  have hr : X.charpoly.roots.map Complex.re =
      Multiset.map (fun i => BlockBand.Foundations.Spectral.increasingEigenvalue hX i)
        Finset.univ.val := by
    rw [hX.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def]
    change Multiset.map hX.eigenvalues₀ Finset.univ.val =
      Multiset.map (hX.eigenvalues₀ ∘ Fin.revPerm) Finset.univ.val
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [hr, Multiset.map_map]
  rfl

/-- Hermitian matrices with equal characteristic polynomials (on possibly different index
types) have equal `Tr f(Λ(· - E))`. -/
theorem unfoldedSpectralSum_eq_of_charpoly_eq {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : X.charpoly = Y.charpoly) (E Λ : ℝ)
    (f : ℝ → ℝ) : unfoldedSpectralSum X hX E Λ f = unfoldedSpectralSum Y hY E Λ f := by
  rw [unfoldedSpectralSum_eq_roots_sum, unfoldedSpectralSum_eq_roots_sum, h]

/-- **Reindexing of `Tr f(Λ(H - E))`.** For every equivalence `e : ι ≃ κ`, Hermitian
`X : Matrix κ κ ℂ` and any proof `h'` that `X.submatrix e e` is Hermitian:
`unfoldedSpectralSum (X.submatrix e e) h' E Λ f = unfoldedSpectralSum X hX E Λ f`
(eigenvalues with multiplicity are invariant, via `Matrix.charpoly_reindex`). -/
theorem unfoldedSpectralSum_submatrix (e : ι ≃ κ) {X : Matrix κ κ ℂ} (hX : X.IsHermitian)
    (h' : (X.submatrix e e).IsHermitian) (E Λ : ℝ) (f : ℝ → ℝ) :
    unfoldedSpectralSum (X.submatrix e e) h' E Λ f = unfoldedSpectralSum X hX E Λ f := by
  apply unfoldedSpectralSum_eq_of_charpoly_eq
  have h := Matrix.charpoly_reindex e.symm X
  rwa [Matrix.reindex_apply, Equiv.symm_symm] at h

/-- `Tr f(Λ(X - E))` through the raw-matrix extension
`BlockBand.Model.Construction.rawIncreasingEigenvalue` of the increasing spectrum (exact
eigenvalues on Hermitian `X`, `0` otherwise); defined for every square complex matrix. -/
def rawUnfoldedSpectralSum (X : Matrix ι ι ℂ) (E Λ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, f (Λ * (BlockBand.Model.Construction.rawIncreasingEigenvalue i X - E))

/-- On Hermitian matrices the raw extension is exactly `Tr f(Λ(X - E))`. -/
theorem rawUnfoldedSpectralSum_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (E Λ : ℝ)
    (f : ℝ → ℝ) : rawUnfoldedSpectralSum X E Λ f = unfoldedSpectralSum X hX E Λ f := by
  unfold rawUnfoldedSpectralSum unfoldedSpectralSum
  simp_rw [BlockBand.Model.Construction.rawIncreasingEigenvalue_eq _ X hX]

/-- For measurable `f`, `X ↦ rawUnfoldedSpectralSum X E Λ f` is Borel measurable. -/
theorem measurable_rawUnfoldedSpectralSum (E Λ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun X : Matrix ι ι ℂ => rawUnfoldedSpectralSum X E Λ f) :=
  Finset.measurable_sum _ fun i _ => hf.comp
    (((BlockBand.Model.Construction.measurable_rawIncreasingEigenvalue i).sub_const E).const_mul
      Λ)

/-- **Reindexing of the raw extension**, for every `X` (Hermitian or not) and every
equivalence `e : ι ≃ κ`. -/
theorem rawUnfoldedSpectralSum_submatrix (e : ι ≃ κ) (X : Matrix κ κ ℂ) (E Λ : ℝ)
    (f : ℝ → ℝ) :
    rawUnfoldedSpectralSum (X.submatrix e e) E Λ f = rawUnfoldedSpectralSum X E Λ f := by
  by_cases hX : X.IsHermitian
  · rw [rawUnfoldedSpectralSum_eq hX, rawUnfoldedSpectralSum_eq (hX.submatrix e),
      unfoldedSpectralSum_submatrix e hX]
  · have hX' : ¬ (X.submatrix e e).IsHermitian := by
      intro h
      apply hX
      have h2 := h.submatrix e.symm
      simpa [Matrix.submatrix_submatrix] using h2
    unfold rawUnfoldedSpectralSum
    simp only [BlockBand.Model.Construction.rawIncreasingEigenvalue, hX, hX', dite_false,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_congr e]

end Reindex

/-!
### The physical block projector
-/

section Physical

/-- The physical absorber projector `P_C = diag(1_{x.1 ∈ C})` of a union of cyclic blocks
`C ⊆ ZMod n`, on the physical sites. -/
def physicalBlockProjector (p : Parameters) (C : Finset (ZMod p.n)) : p.SiteMatrix :=
  Matrix.diagonal (fun x : p.Site => if x.1 ∈ C then 1 else 0)

/-- The block labels `C ⊆ ZMod n` in the block coordinates `Fin n` of `siteBlockEquiv`. -/
def physicalBlockFinset (p : Parameters) (C : Finset (ZMod p.n)) : Finset (Fin p.n) :=
  C.map (ZMod.finEquiv p.n).symm.toEquiv.toEmbedding

/-- `toBlockCoords p H = H.submatrix e e` with `e = (siteBlockEquiv p).symm`. -/
theorem toBlockCoords_eq_submatrix (p : Parameters) (H : p.SiteMatrix) :
    toBlockCoords p H = H.submatrix (siteBlockEquiv p).symm (siteBlockEquiv p).symm := rfl

/-- Under `siteBlockEquiv`, the physical block projector of `C` is
`Inputs.blockProjector (physicalBlockFinset p C)`. -/
theorem toBlockCoords_physicalBlockProjector (p : Parameters) (C : Finset (ZMod p.n)) :
    toBlockCoords p (physicalBlockProjector p C) =
      (blockProjector (physicalBlockFinset p C) :
        Matrix (Fin p.n × Fin p.W) (Fin p.n × Fin p.W) ℂ) := by
  unfold toBlockCoords physicalBlockProjector blockProjector physicalBlockFinset
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  have h : ((siteBlockEquiv p).symm x).1 ∈ C ↔ x.1 ∈ C.map
      (ZMod.finEquiv p.n).symm.toEquiv.toEmbedding := by
    rw [Finset.mem_map_equiv]
    simp [siteBlockEquiv]
  simp only [Function.comp_apply, h]

/-- The complement has the same cardinality: `|(physicalBlockFinset p C)ᶜ| = |Cᶜ|`. -/
theorem card_compl_physicalBlockFinset (p : Parameters) (C : Finset (ZMod p.n)) :
    (physicalBlockFinset p C)ᶜ.card = Cᶜ.card := by
  rw [Finset.card_compl, Finset.card_compl, physicalBlockFinset, Finset.card_map,
    Fintype.card_fin, ZMod.card]

/-- `toBlockCoords p` is Borel measurable. -/
theorem measurable_toBlockCoords (p : Parameters) : Measurable (toBlockCoords p) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [toBlockCoords, Matrix.submatrix_apply]
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- `directSumBlockCoords n` is Borel measurable in the family of block matrices. -/
theorem measurable_directSumBlockCoords {r W : ℕ} (n : Fin r → ℕ) :
    Measurable (fun H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ =>
      directSumBlockCoords n H) := by
  rw [Matrix.measurable_iff]
  intro x y
  unfold directSumBlockCoords
  by_cases h : (finSigmaFinEquiv.symm x.1).1 = (finSigmaFinEquiv.symm y.1).1
  · simp only [h, dite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [h, dite_false]
    exact measurable_const

/-- **Faithfulness of the convention.** `model.law`-a.s. the physical `H` is Hermitian and
`rawUnfoldedSpectralSum H E Λ f = Tr f(Λ(H - E))`. -/
theorem ae_rawUnfoldedSpectralSum_eq (p : Parameters) (model : p.GaussianRingModel)
    (E Λ : ℝ) (f : ℝ → ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), ∃ hH : H.IsHermitian,
      rawUnfoldedSpectralSum H E Λ f = unfoldedSpectralSum H hH E Λ f :=
  model.isPhysical.1.mono fun _H hH => ⟨hH, rawUnfoldedSpectralSum_eq hH E Λ f⟩

/-- On Hermitian `H`, the raw extension also equals `Tr f(Λ(H - E))` for the counting
convention `Parameters.physicalHermitianVersion` (used by `physicalUnfoldedEigenvalue`). -/
theorem rawUnfoldedSpectralSum_eq_physicalHermitianVersion (p : Parameters)
    {H : p.SiteMatrix} (hH : H.IsHermitian) (E Λ : ℝ) (f : ℝ → ℝ) :
    rawUnfoldedSpectralSum H E Λ f =
      unfoldedSpectralSum (p.physicalHermitianVersion H).1 (p.physicalHermitianVersion H).2
        E Λ f := by
  have h : (p.physicalHermitianVersion H).1 = H :=
    p.gaussianReconstruction_gaussianExtraction H hH
  rw [rawUnfoldedSpectralSum_eq hH]
  congr 1
  exact h.symm

/-- A direct sum of Hermitian block matrices is Hermitian. -/
theorem directSumBlockCoords_isHermitian {r W : ℕ} (n : Fin r → ℕ)
    {H : ∀ i, Matrix (Fin (n i) × Fin W) (Fin (n i) × Fin W) ℂ}
    (hH : ∀ i, (H i).IsHermitian) :
    (directSumBlockCoords n H).IsHermitian := by
  have key : ∀ (u v : (i : Fin r) × Fin (n i)) (a c : Fin W) (h : u.1 = v.1)
      (p1 : n u.1 = n v.1) (p2 : n v.1 = n u.1),
      star (H v.1 (v.2, c) (Fin.cast p1 u.2, a)) = H u.1 (u.2, a) (Fin.cast p2 v.2, c) := by
    rintro ⟨i, a'⟩ ⟨j, c'⟩ a c h p1 p2
    simp only at h
    subst h
    simp only [Fin.cast_eq_self]
    exact congrFun (congrFun (hH i) (a', a)) (c', c)
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [conjTranspose_apply, directSumBlockCoords]
  by_cases h : (finSigmaFinEquiv.symm x1).1 = (finSigmaFinEquiv.symm y1).1
  · rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h.symm)]
    exact key _ _ x2 y2 h _ _
  · rw [dite_eq_right_of_eq_false (eq_false h),
      dite_eq_right_of_eq_false (eq_false (Ne.symm h)), star_zero]

/-- Under the product of the physical ring laws, the direct sum `⊕ᵢ Hᵢ` in block coordinates
is a.s. Hermitian. -/
theorem ae_isHermitian_directSum {r W : ℕ} (n : Fin r → ℕ) (b : ℝ) (hn : ∀ i, 4 ≤ n i)
    (hW : 0 < W) (hb : 0 < b) (hb' : b < 1 / 2)
    (models : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').GaussianRingModel) :
    ∀ᵐ H ∂(Measure.pi (fun i => ((models i).law :
        Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))),
      (directSumBlockCoords n
        (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))).IsHermitian :=
      by
  have h : ∀ i, ∀ᵐ H ∂(Measure.pi (fun i => ((models i).law :
        Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))), (H i).IsHermitian :=
    fun i => (Measure.quasiMeasurePreserving_eval _ i).ae (models i).isPhysical.1
  filter_upwards [ae_all_iff.2 h] with H hH
  exact directSumBlockCoords_isHermitian n fun i => (hH i).submatrix _

/-- **Faithfulness of the convention, direct sums.** Under the product of the physical ring
laws, a.s. `X = ⊕ᵢ Hᵢ` is Hermitian and `rawUnfoldedSpectralSum X E Λ f = Tr f(Λ(X - E))`. -/
theorem ae_rawUnfoldedSpectralSum_directSum_eq {r W : ℕ} (n : Fin r → ℕ) (b : ℝ)
    (hn : ∀ i, 4 ≤ n i) (hW : 0 < W) (hb : 0 < b) (hb' : b < 1 / 2)
    (models : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').GaussianRingModel)
    (E Λ : ℝ) (f : ℝ → ℝ) :
    ∀ᵐ H ∂(Measure.pi (fun i => ((models i).law :
        Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))),
      ∃ hX : (directSumBlockCoords n
          (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))).IsHermitian,
        rawUnfoldedSpectralSum (directSumBlockCoords n
            (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))) E Λ f =
          unfoldedSpectralSum _ hX E Λ f :=
  (ae_isHermitian_directSum n b hn hW hb hb' models).mono fun _H hX =>
    ⟨hX, rawUnfoldedSpectralSum_eq hX E Λ f⟩

end Physical

/-!
### Transfer of expectations
-/

section Transfer

/-- For measurable `h : Ω → γ`, `φ : β → γ` with `P.map h = ν.map φ` and measurable
`g : γ → ℝ`: integrability of `g ∘ h` under `P` and a bound `∫ g ∘ h dP ≤ e` transfer to
`g ∘ φ` under `ν`. -/
theorem integrable_and_integral_le_of_map_eq {Ω β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableSpace γ] {P : Measure Ω} {ν : Measure β} {h : Ω → γ}
    {φ : β → γ} (hh : Measurable h) (hφ : Measurable φ) (hPν : P.map h = ν.map φ)
    {g : γ → ℝ} (hg : Measurable g) {e : ℝ} (hint : Integrable (fun w => g (h w)) P)
    (hle : ∫ w, g (h w) ∂P ≤ e) :
    Integrable (fun b => g (φ b)) ν ∧ ∫ b, g (φ b) ∂ν ≤ e := by
  have h1 : Integrable g (ν.map φ) := by
    rw [← hPν]
    exact (integrable_map_measure hg.aestronglyMeasurable hh.aemeasurable).2 hint
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hφ.aemeasurable).1 h1, ?_⟩
  rw [← integral_map hφ.aemeasurable hg.aestronglyMeasurable, ← hPν,
    integral_map hh.aemeasurable hg.aestronglyMeasurable]
  exact hle

/-- **Transfer along `Presents`.** If `M` presents `μ` (so `M.P.map M.H = μ`), then for
every measurable `g`, `g ∘ M.H` is `M.P`-integrable iff `g` is `μ`-integrable, and
`∫ g (M.H w) dM.P = ∫ g dμ`. -/
theorem integrable_and_integral_comp_H_of_presents {k W : ℕ} {M : BlockModel k W}
    {μ : Measure (Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ)} (hP : Presents M μ)
    {g : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ → ℝ} (hg : Measurable g) :
    (Integrable (fun w => g (M.H w)) M.P ↔ Integrable g μ) ∧
      ∫ w, g (M.H w) ∂M.P = ∫ X, g X ∂μ := by
  have hH := measurable_blockModel_H M
  rw [← hP.2.2]
  exact ⟨(integrable_map_measure hg.aestronglyMeasurable hH.aemeasurable).symm,
    (integral_map hH.aemeasurable hg.aestronglyMeasurable).symm⟩

end Transfer

/-!
### The lemma on rings and direct sums of rings
-/

section Main

/-- **Finite-log recovery on rings and direct sums of rings.** Fix `b ∈ (0, 1/2)` (so `c = 1 - 2b`), `ρ > 0` (standing for `ρ(E)`) and
`f ≥ 0` smooth with compact support. There is one `Cf ≥ 0`, depending only on `f, b, ρ`
(and the constants of the hypotheses), such that, for all real `E` and `δ > 0`:

1. (ring) for every `p : Parameters` with `p.b = b`, every realization `model` of the
   physical law and every union of blocks `C ⊆ ZMod p.n`, with `Λ = Nρ`, `N = p.N = nW`:
   `|𝓡_δ^C(H; f) - Tr f(Λ(H - E))|` is `model.law`-integrable and its expectation is
   `≤ Cf (δ(1 + |log δ|) + |Cᶜ|/n)`;
2. (direct sum) for all `r, W ≥ 1`, block numbers `nᵢ ≥ 4` with `0 < Σᵢ nᵢ`, realizations
   `models i` of the physical laws with parameters `(nᵢ, W, b)`, and every union of blocks
   `C ⊆ Fin (Σᵢ nᵢ)` of the direct sum: the same bound for `X = ⊕ᵢ Hᵢ` (block coordinates
   `directSumBlockCoords`, independent `Hᵢ`, law `Measure.pi`), with the global unfolding
   `Λ = (Σᵢ nᵢ) W ρ` and `|Cᶜ|/Σᵢ nᵢ` (the paper's `|B|/n`, `n` the total block number).

`𝓡` is `positiveLogStatistic` of the raw matrix; `Tr f(Λ(H - E))` is
`rawUnfoldedSpectralSum`, equal to `unfoldedSpectralSum` on Hermitian matrices, hence a.s. -/
theorem finiteLogRecovery_ring_and_ringSum (hRing : RingBlockModels)
    (hWegner : ProjectedWegner) (hCount : ConditionalBlockGUECount)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      (∀ (p : Parameters), p.b = b → ∀ (model : p.GaussianRingModel) (E δ : ℝ), 0 < δ →
        ∀ C : Finset (ZMod p.n),
          Integrable (fun H => |positiveLogStatistic H E ((p.N : ℝ) * ρ) δ
              (physicalBlockProjector p C) f -
            rawUnfoldedSpectralSum H E ((p.N : ℝ) * ρ) f|)
            (model.law : Measure p.SiteMatrix) ∧
          ∫ H, |positiveLogStatistic H E ((p.N : ℝ) * ρ) δ (physicalBlockProjector p C) f -
              rawUnfoldedSpectralSum H E ((p.N : ℝ) * ρ) f|
              ∂(model.law : Measure p.SiteMatrix) ≤
            Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / p.n)) ∧
      (∀ (r W : ℕ) (n : Fin r → ℕ) (hn : ∀ i, 4 ≤ n i) (hW : 0 < W)
        (models : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').GaussianRingModel),
        0 < ∑ i, n i → ∀ (E δ : ℝ), 0 < δ → ∀ C : Finset (Fin (∑ i, n i)),
          Integrable (fun H => |positiveLogStatistic (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) δ (blockProjector C) f -
            rawUnfoldedSpectralSum (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) f|)
            (Measure.pi (fun i => ((models i).law :
              Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))) ∧
          ∫ H, |positiveLogStatistic (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) δ (blockProjector C) f -
            rawUnfoldedSpectralSum (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) f|
              ∂(Measure.pi (fun i => ((models i).law :
                Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))) ≤
            Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / (∑ i, n i : ℕ))) := by
  have hc : 0 < 1 - 2 * b := by linarith
  obtain ⟨Cf, hCf, hrec⟩ :=
    finiteLogRecovery hWegner hCount (1 - 2 * b) hc ρ hρ f hf hfs hf0
  have hfm : Measurable f := hf.continuous.measurable
  -- the block-coordinate integrand
  have hg : ∀ (k W : ℕ) (E Λ δ : ℝ) (P : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ),
      Measurable (fun X : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
        |positiveLogStatistic X E Λ δ P f - rawUnfoldedSpectralSum X E Λ f|) :=
    fun k W E Λ δ P => ((measurable_positiveLogStatistic measurable_id E Λ δ P
      hf.continuous).sub (measurable_rawUnfoldedSpectralSum E Λ hfm)).abs
  have hHraw : ∀ {k W : ℕ} (M : BlockModel k W) (E Λ : ℝ) (w : M.Ω),
      unfoldedSpectralSum (M.H w) (BlockModelCount.isHermitian_H M w) E Λ f =
        rawUnfoldedSpectralSum (M.H w) E Λ f :=
    fun M E Λ w => (rawUnfoldedSpectralSum_eq (BlockModelCount.isHermitian_H M w) E Λ f).symm
  refine ⟨Cf, hCf, ?_, ?_⟩
  · intro p hpb model E δ hδ C
    obtain ⟨M, hM, hP⟩ := hRing.1 p model
    have hM' : M.IsIndependent (1 - 2 * b) := by
      have : p.c = 1 - 2 * b := by rw [Parameters.c, hpb]
      rwa [this] at hM
    obtain ⟨hint, hle⟩ := hrec p.n p.W p.n_pos p.W_pos M hM' E δ hδ (physicalBlockFinset p C)
    simp_rw [hHraw M] at hint hle
    rw [card_compl_physicalBlockFinset] at hle
    have key := integrable_and_integral_le_of_map_eq (measurable_blockModel_H M)
      (measurable_toBlockCoords p) hP.2.2 (hg _ _ E _ δ _) hint hle
    have hpt : ∀ (Λ : ℝ) (H : p.SiteMatrix),
        |positiveLogStatistic (toBlockCoords p H) E Λ δ
            (blockProjector (physicalBlockFinset p C)) f -
          rawUnfoldedSpectralSum (toBlockCoords p H) E Λ f| =
        |positiveLogStatistic H E Λ δ (physicalBlockProjector p C) f -
          rawUnfoldedSpectralSum H E Λ f| := by
      intro Λ H
      rw [← toBlockCoords_physicalBlockProjector, toBlockCoords_eq_submatrix,
        toBlockCoords_eq_submatrix, positiveLogStatistic_submatrix,
        rawUnfoldedSpectralSum_submatrix]
    simp_rw [hpt] at key
    exact key
  · intro r W n hn hW models hpos E δ hδ C
    obtain ⟨M, hM, hP⟩ := hRing.2 r W n b hn hW hb hb' models
    obtain ⟨hint, hle⟩ := hrec (∑ i, n i) W hpos hW M hM E δ hδ C
    simp_rw [hHraw M] at hint hle
    have hφ : Measurable (fun H : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix =>
        directSumBlockCoords n
          (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i))) := by
      have h0 : Measurable
          (fun H : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix =>
            fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)) :=
        Measurable.of_eval fun i => (measurable_toBlockCoords _).comp (measurable_pi_apply i)
      exact (measurable_directSumBlockCoords (W := W) n).comp h0
    exact integrable_and_integral_le_of_map_eq (measurable_blockModel_H M) hφ hP.2.2
      (hg _ _ E _ δ _) hint hle

/-- **Finite-log recovery on a ring.** Clause 1 of
`finiteLogRecovery_ring_and_ringSum` (same hypotheses and constant): for fixed
`b ∈ (0, 1/2)`, `ρ > 0`, `f ≥ 0` smooth compactly supported, one `Cf ≥ 0` such that for every
`p` with `p.b = b`, every physical `model`, `E`, `δ > 0` and `C ⊆ ZMod p.n`,
`E_{model.law} |𝓡_δ^C(H; f) - Tr f(Λ(H - E))| ≤ Cf (δ(1 + |log δ|) + |Cᶜ|/n)`,
`Λ = Nρ`, absorber `physicalBlockProjector p C`. -/
theorem finiteLogRecovery_ring (hRing : RingBlockModels)
    (hWegner : ProjectedWegner) (hCount : ConditionalBlockGUECount)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∀ (p : Parameters), p.b = b → ∀ (model : p.GaussianRingModel) (E δ : ℝ), 0 < δ →
        ∀ C : Finset (ZMod p.n),
          Integrable (fun H => |positiveLogStatistic H E ((p.N : ℝ) * ρ) δ
              (physicalBlockProjector p C) f -
            rawUnfoldedSpectralSum H E ((p.N : ℝ) * ρ) f|)
            (model.law : Measure p.SiteMatrix) ∧
          ∫ H, |positiveLogStatistic H E ((p.N : ℝ) * ρ) δ (physicalBlockProjector p C) f -
              rawUnfoldedSpectralSum H E ((p.N : ℝ) * ρ) f|
              ∂(model.law : Measure p.SiteMatrix) ≤
            Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / p.n) := by
  obtain ⟨Cf, hCf, h1, -⟩ :=
    finiteLogRecovery_ring_and_ringSum hRing hWegner hCount b hb hb' ρ hρ f hf hfs hf0
  exact ⟨Cf, hCf, h1⟩

/-- **Finite-log recovery on a direct sum of independent rings.** Clause 2 of
`finiteLogRecovery_ring_and_ringSum` (same hypotheses; the constant there serves both
clauses): for `r` independent physical rings with block numbers `nᵢ ≥ 4`, common `W ≥ 1`
and bond `b`, and `C ⊆ Fin (Σᵢ nᵢ)`, the bound holds for the direct sum in block
coordinates with `Λ = (Σᵢ nᵢ) W ρ` and `|Cᶜ|/Σᵢ nᵢ`. -/
theorem finiteLogRecovery_ringSum (hRing : RingBlockModels)
    (hWegner : ProjectedWegner) (hCount : ConditionalBlockGUECount)
    (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∀ (r W : ℕ) (n : Fin r → ℕ) (hn : ∀ i, 4 ≤ n i) (hW : 0 < W)
        (models : ∀ i, (ringParameters (n i) W b (hn i) hW hb hb').GaussianRingModel),
        0 < ∑ i, n i → ∀ (E δ : ℝ), 0 < δ → ∀ C : Finset (Fin (∑ i, n i)),
          Integrable (fun H => |positiveLogStatistic (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) δ (blockProjector C) f -
            rawUnfoldedSpectralSum (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) f|)
            (Measure.pi (fun i => ((models i).law :
              Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))) ∧
          ∫ H, |positiveLogStatistic (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) δ (blockProjector C) f -
            rawUnfoldedSpectralSum (directSumBlockCoords n
                (fun i => toBlockCoords (ringParameters (n i) W b (hn i) hW hb hb') (H i)))
              E ((((∑ i, n i) * W : ℕ) : ℝ) * ρ) f|
              ∂(Measure.pi (fun i => ((models i).law :
                Measure (ringParameters (n i) W b (hn i) hW hb hb').SiteMatrix))) ≤
            Cf * (δ * (1 + |Real.log δ|) + ((Cᶜ).card : ℝ) / (∑ i, n i : ℕ)) := by
  obtain ⟨Cf, hCf, -, h2⟩ :=
    finiteLogRecovery_ring_and_ringSum hRing hWegner hCount b hb hb' ρ hρ f hf hfs hf0
  exact ⟨Cf, hCf, h2⟩

end Main

end BlockBand.Endpoints
