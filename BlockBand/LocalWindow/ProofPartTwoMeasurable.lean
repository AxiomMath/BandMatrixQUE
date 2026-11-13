module

public import BlockBand.LocalWindow.ProofPartTwoPoint

/-!
# Measurability of the Dyson root, the window centre and the window bad sets

The Dyson root, the window centre and the window bad sets of part (ii) of the physical
local-window lemma are measurable functions and sets of the matrix data.

## Main results

* `measurable_matrixInverse`: `A ↦ A⁻¹` is Borel on `Matrix ι ι ℂ`.
* `polishSpace_matrix`: `Matrix ι ι ℂ` is Polish (as the Pi type).
* `dysonMap`, `dysonDomain`, `dysonGraph`: the root equation `m = N⁻¹ Tr(F - z - sm)⁻¹`, the
  domain `{F Hermitian, Im z ≥ 0}` and the (measurable) graph of Dyson roots over it.
* **`measurableSet_freshDyson_preimage`** (Lusin–Souslin): for `s > 0` and Borel `B ⊆ ℂ`,
  `{(F, z) | freshDyson F s z ∈ B} ∩ dysonDomain` is Borel. Proof: by uniqueness of the root
  (`ProofETH.dysonRoot_unique`) the projection of the graph is injective, so its images are Borel
  (`MeasurableSet.image_of_measurable_injOn`); off the projection `freshDyson = 0`.
* **`measurable_freshDyson_comp`**, `measurable_pairDyson_comp`, `measurable_windowGamma_comp`,
  **`measurable_pairCentre_comp`**: compositions with measurable `K(x)` (Hermitian for every `x`),
  `J(x)`, `λ(x)` (and `Im z(x) ≥ 0`) are measurable. This covers `K(ω) = K₀(ω, E) + ρ w(ω) w(ω)*`
  with a measurable pole direction `w(ω)`.
* `pairHermPart`, `pairEigvalH`, `pairEigvecH`: total (proof-free) versions of `pairEigval`,
  `pairEigvec`, equal to them on Hermitian matrices (`pairEigval_eq_H`, `pairEigvec_eq_H`).
* **`measurableSet_not_pairWindowGood`**: for a measurable space `X`, measurable `K : X → PairMatrix`
  with Hermitian values, measurable `J`, any `sel`, `s`, `E₀`, `β`, `ε`, the set
  `{(x, G) | ¬ PairWindowGood (K x) _ sel s E₀ β ε (J x) G}` is measurable in `X × PairMatrix`.
* **`measurableSet_not_windowCount_le`**: the same for the window-count bad set of
  `gue_windowCount_le` (count with selected eigenvalues).
* **`gridWindowBad`**: `gue_not_pairWindowGood_le` together with the measurability, in the form
  consumed by `PartTwoConditionalStatement` (a measurable `S` whose sections are `GUE`-small at
  every exterior point satisfying the norm bound and the root rectangle).

Measurability in `ω` of the grid deformation `K(ω) = K₀(ω, E) + ρ w(ω)w(ω)*`
and of the observable `B(ω, E)` (class (b): `spectralFn f (K₀(ω, E))`) is a hypothesis here
(`Measurable K`, `Measurable J` in the statements below).

Continuity of the centre in `λ` on the root rectangle is `ProofPartTwo.pairCentre_lipschitz`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.LawBridge
open scoped ENNReal Matrix.Norms.L2Operator

/-!
## Generic measurability of matrix operations
-/

section Generic

variable {X : Type*} [MeasurableSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_matrix_of_entries {κ : Type} {f : X → Matrix ι κ ℂ}
    (h : ∀ a b, Measurable fun x => f x a b) : Measurable f :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => h a b

/-- **Matrix inversion is Borel measurable** (`A⁻¹ = (det A)⁻¹ adj A`). -/
theorem measurable_matrixInverse : Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  refine measurable_matrix_of_entries fun a b => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (continuous_id.matrix_det.measurable.inv).mul
    ((continuous_apply_apply a b).comp continuous_id.matrix_adjugate).measurable

/-- `Matrix ι ι ℂ` is a Polish space (it is the Pi type `ι → ι → ℂ`). -/
theorem polishSpace_matrix : PolishSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (PolishSpace (ι → ι → ℂ))

theorem secondCountableTopology_matrix : SecondCountableTopology (Matrix ι ι ℂ) :=
  inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))

theorem measurableSet_isHermitian_matrix : MeasurableSet {M : Matrix ι ι ℂ | M.IsHermitian} :=
  (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet

end Generic

/-!
## The Dyson root is measurable
-/

section Dyson

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Dyson map `((F, z), m) ↦ N⁻¹ Tr (F - z - s m)⁻¹` (right side of `IsDysonRoot`). -/
def dysonMap (s : ℝ) (q : (Matrix ι ι ℂ × ℂ) × ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ *
    ((q.1.1 - (q.1.2 + (s : ℂ) * q.2) • (1 : Matrix ι ι ℂ))⁻¹).trace

theorem measurable_dysonMap (s : ℝ) : Measurable (dysonMap (ι := ι) s) := by
  have hc : Continuous fun q : (Matrix ι ι ℂ × ℂ) × ℂ =>
      q.1.1 - (q.1.2 + (s : ℂ) * q.2) • (1 : Matrix ι ι ℂ) :=
    (continuous_fst.comp continuous_fst).sub
      (((continuous_snd.comp continuous_fst).add (continuous_const.mul continuous_snd)).smul
        continuous_const)
  exact measurable_const.mul
    (continuous_id.matrix_trace.measurable.comp (measurable_matrixInverse.comp hc.measurable))

/-- The domain `{(F, z) | F Hermitian, Im z ≥ 0}` on which Dyson roots are unique. -/
def dysonDomain : Set (Matrix ι ι ℂ × ℂ) := {q | q.1.IsHermitian ∧ 0 ≤ q.2.im}

/-- The graph of Dyson roots over `dysonDomain`. -/
def dysonGraph (s : ℝ) : Set ((Matrix ι ι ℂ × ℂ) × ℂ) :=
  {q | q.1 ∈ dysonDomain ∧ IsDysonRoot q.1.1 s q.1.2 q.2}

theorem measurableSet_dysonDomain : MeasurableSet (dysonDomain (ι := ι)) :=
  (measurableSet_isHermitian_matrix.preimage measurable_fst).inter
    (measurableSet_le measurable_const (Complex.measurable_im.comp measurable_snd))

theorem measurableSet_dysonGraph (s : ℝ) : MeasurableSet (dysonGraph (ι := ι) s) := by
  have h1 : MeasurableSet {q : (Matrix ι ι ℂ × ℂ) × ℂ | 0 < q.2.im} :=
    measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  have h2 : MeasurableSet {q : (Matrix ι ι ℂ × ℂ) × ℂ | q.2 = dysonMap s q} :=
    measurableSet_eq_fun measurable_snd (measurable_dysonMap s)
  exact (measurableSet_dysonDomain.preimage measurable_fst).inter (h1.inter h2)

theorem injOn_fst_dysonGraph [Nonempty ι] {s : ℝ} (hs : 0 < s) :
    InjOn Prod.fst (dysonGraph (ι := ι) s) := by
  intro a ha b hb hab
  refine Prod.ext hab ?_
  have hb' : IsDysonRoot a.1.1 s a.1.2 b.2 := by rw [hab]; exact hb.2
  exact dysonRoot_unique ha.1.1 hs ha.1.2 ha.2 hb'

/-- `freshDyson = 0` when no Dyson root exists. -/
theorem freshDyson_eq_zero_of_not {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} {s : ℝ} {z : ℂ}
    (h : ¬ ∃ m : ℂ, IsDysonRoot F s z m) : freshDyson F s z = 0 := by
  have hn : ¬ ∃ m : ℂ, 0 < m.im ∧
      m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace := by
    rintro ⟨m, hm, he⟩
    exact h ⟨m, hm, by rw [Fintype.card_fin]; exact he⟩
  unfold freshDyson
  split_ifs
  rfl

/-- **The Dyson root is Borel on the uniqueness domain** (Lusin–Souslin): for `s > 0` and Borel
`B ⊆ ℂ`, `{(F, z) | freshDyson F s z ∈ B}` intersected with `{F Hermitian, Im z ≥ 0}` is Borel. -/
theorem measurableSet_freshDyson_preimage {N : ℕ} [NeZero N] {s : ℝ} (hs : 0 < s) {B : Set ℂ}
    (hB : MeasurableSet B) :
    MeasurableSet ((fun q : Matrix (Fin N) (Fin N) ℂ × ℂ => freshDyson q.1 s q.2) ⁻¹' B ∩
      dysonDomain) := by
  have := polishSpace_matrix (ι := Fin N)
  have hGr := measurableSet_dysonGraph (ι := Fin N) s
  have hinj := injOn_fst_dysonGraph (ι := Fin N) hs
  have h1 : MeasurableSet (Prod.fst '' (dysonGraph (ι := Fin N) s ∩ Prod.snd ⁻¹' B)) :=
    (hGr.inter (measurable_snd hB)).image_of_measurable_injOn measurable_fst
      (hinj.mono inter_subset_left)
  have h2 : MeasurableSet (Prod.fst '' dysonGraph (ι := Fin N) s) :=
    hGr.image_of_measurable_injOn measurable_fst hinj
  have e : (fun q : Matrix (Fin N) (Fin N) ℂ × ℂ => freshDyson q.1 s q.2) ⁻¹' B ∩
      dysonDomain = Prod.fst '' (dysonGraph (ι := Fin N) s ∩ Prod.snd ⁻¹' B) ∪
        ({_q | (0 : ℂ) ∈ B} ∩ (dysonDomain \ Prod.fst '' dysonGraph (ι := Fin N) s)) := by
    ext q
    simp only [mem_inter_iff, mem_preimage, mem_union, mem_image, mem_sdiff, mem_ofPred_eq]
    constructor
    · rintro ⟨hΦ, hD⟩
      by_cases hex : ∃ m : ℂ, IsDysonRoot q.1 s q.2 m
      · obtain ⟨m, hm⟩ := hex
        have hfd := freshDyson_eq_of_isDysonRoot hD.1 hs hD.2 hm
        refine Or.inl ⟨(q, m), ⟨⟨hD, hm⟩, ?_⟩, rfl⟩
        rw [← hfd]; exact hΦ
      · refine Or.inr ⟨?_, hD, ?_⟩
        · rw [← freshDyson_eq_zero_of_not hex]; exact hΦ
        · rintro ⟨x, hx, rfl⟩
          exact hex ⟨x.2, hx.2⟩
    · rintro (⟨x, ⟨hx, hxB⟩, rfl⟩ | ⟨h0, hD, hn⟩)
      · refine ⟨?_, hx.1⟩
        rw [freshDyson_eq_of_isDysonRoot hx.1.1 hs hx.1.2 hx.2]; exact hxB
      · refine ⟨?_, hD⟩
        have hex : ¬ ∃ m : ℂ, IsDysonRoot q.1 s q.2 m := by
          rintro ⟨m, hm⟩
          exact hn ⟨(q, m), ⟨hD, hm⟩, rfl⟩
        rw [freshDyson_eq_zero_of_not hex]; exact h0
  rw [e]
  exact h1.union ((MeasurableSet.const _).inter (measurableSet_dysonDomain.diff h2))

variable {X : Type*} [MeasurableSpace X]

/-- **`freshDyson` along measurable data** (`m_E(λ)`): if `F(x)` is Hermitian and
`Im z(x) ≥ 0` for every `x`, and `F, z` are measurable, then `x ↦ freshDyson (F x) s (z x)` is
measurable (`s > 0`). -/
theorem measurable_freshDyson_comp {N : ℕ} [NeZero N] {s : ℝ} (hs : 0 < s)
    {F : X → Matrix (Fin N) (Fin N) ℂ} {z : X → ℂ} (hF : Measurable F) (hz : Measurable z)
    (hH : ∀ x, (F x).IsHermitian) (hI : ∀ x, 0 ≤ (z x).im) :
    Measurable fun x => freshDyson (F x) s (z x) := by
  intro B hB
  have h := (hF.prodMk hz) (measurableSet_freshDyson_preimage (N := N) hs hB)
  convert h using 1
  ext x
  simp [dysonDomain, hH x, hI x]

end Dyson

/-!
## The pair centre is measurable
-/

section Pair

variable {p : Parameters} {i : ZMod p.n} {X : Type*} [MeasurableSpace X]

theorem measurable_reindex_comp {κ : Type} [Fintype κ] [DecidableEq κ] (e : PairSite p i ≃ κ) {K : X → PairMatrix p i}
    (hK : Measurable K) : Measurable fun x => reindex e e (K x) := by
  refine measurable_matrix_of_entries fun a b => ?_
  simp only [reindex_apply, submatrix_apply]
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hK)

/-- `pairDyson` along measurable Hermitian data. -/
theorem measurable_pairDyson_comp {s : ℝ} (hs : 0 < s) {K : X → PairMatrix p i} {z : X → ℂ}
    (hK : Measurable K) (hz : Measurable z) (hH : ∀ x, (K x).IsHermitian)
    (hI : ∀ x, 0 ≤ (z x).im) :
    Measurable fun x => BlockBand.LocalWindow.pairDyson p i (K x) s (z x) := by
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have : NeZero (Fintype.card (PairSite p i)) := ⟨Fintype.card_ne_zero⟩
  unfold BlockBand.LocalWindow.pairDyson
  refine measurable_freshDyson_comp hs (measurable_reindex_comp _ hK) hz (fun x => ?_) hI
  rw [reindex_apply]; exact (hH x).submatrix _

/-- `windowGamma` along measurable Hermitian data. -/
theorem measurable_windowGamma_comp {s : ℝ} (hs : 0 < s) {K : X → PairMatrix p i} {lam : X → ℝ}
    (hK : Measurable K) (hlam : Measurable lam) (hH : ∀ x, (K x).IsHermitian) :
    Measurable fun x => BlockBand.LocalWindow.windowGamma p i (K x) s (lam x) := by
  have hm := measurable_pairDyson_comp hs hK (Complex.measurable_ofReal.comp hlam) hH
    (fun x => by simp)
  have hc : Measurable fun x => ((lam x : ℂ) + (s : ℂ) *
      BlockBand.LocalWindow.pairDyson p i (K x) s (lam x)) :=
    (Complex.measurable_ofReal.comp hlam).add (measurable_const.mul hm)
  have hcont1 : Continuous fun q : PairMatrix p i × ℂ => q.1 - q.2 • (1 : PairMatrix p i) :=
    continuous_fst.sub (continuous_snd.smul continuous_const)
  have hXm := hcont1.measurable.comp (hK.prodMk hc)
  have hcont2 : Continuous fun Y : PairMatrix p i => Yᴴ * Y :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hcont3 : Continuous fun Y : PairMatrix p i => (s : ℂ) • Y := continuous_const_smul _
  unfold BlockBand.LocalWindow.windowGamma
  exact hcont3.measurable.comp (measurable_matrixInverse.comp (hcont2.measurable.comp hXm))

/-- **The real-axis window centre is measurable**: for measurable `J, K, λ` with `K(x)`
Hermitian for every `x`, `x ↦ pairCentre (J x) (K x) s (λ x)` is measurable (`s > 0`). -/
theorem measurable_pairCentre_comp {s : ℝ} (hs : 0 < s) {J K : X → PairMatrix p i}
    {lam : X → ℝ} (hJ : Measurable J) (hK : Measurable K) (hlam : Measurable lam)
    (hH : ∀ x, (K x).IsHermitian) :
    Measurable fun x => pairCentre (J x) (K x) s (lam x) := by
  have hΓ := measurable_windowGamma_comp hs hK hlam hH
  have hT : Measurable fun x => (J x * BlockBand.LocalWindow.windowGamma p i (K x) s (lam x)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => ?_
    exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hJ)).mul
      ((measurable_pi_apply a).comp ((measurable_pi_apply b).comp hΓ))
  exact measurable_const.mul hT

/-- `windowCenter` along measurable Hermitian data. -/
theorem measurable_windowCenter_comp {s : ℝ} (hs : 0 < s) {J K : X → PairMatrix p i}
    {lam : X → ℝ} (hJ : Measurable J) (hK : Measurable K) (hlam : Measurable lam)
    (hH : ∀ x, (K x).IsHermitian) :
    Measurable fun x => BlockBand.LocalWindow.windowCenter p i (J x) (K x) s (lam x) := by
  have h := Complex.measurable_re.comp (measurable_pairCentre_comp hs hJ hK hlam hH)
  have e : (fun x => BlockBand.LocalWindow.windowCenter p i (J x) (K x) s (lam x)) =
      fun x => (pairCentre (J x) (K x) s (lam x)).re :=
    funext fun x => (re_pairCentre _ _ _ _).symm
  rw [e]; exact h

end Pair

/-!
## Proof-free selected eigenpairs and the measurable window bad sets
-/

section Window

variable {p : Parameters} {i : ZMod p.n}

/-- The Hermitian part `(X + X*)/2` of a pair matrix as an element of `CEH.SourceHermitian`; it is
`toSourceHermitian X` when `X` is Hermitian (`pairHermPart_eq`), and it needs no proof. -/
def pairHermPart (X : PairMatrix p i) : CEH.SourceHermitian (2 * p.W) :=
  ⟨reindex (pairEquiv p i) (pairEquiv p i) ((1 / 2 : ℂ) • (X + Xᴴ)),
    isHermitian_reindex _ (by
      unfold Matrix.IsHermitian
      rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
      congr 1
      simp)⟩

theorem pairHermPart_eq {X : PairMatrix p i} (hX : X.IsHermitian) :
    pairHermPart X = toSourceHermitian X hX := by
  apply Subtype.ext
  change reindex (pairEquiv p i) (pairEquiv p i) ((1 / 2 : ℂ) • (X + Xᴴ)) =
    reindex (pairEquiv p i) (pairEquiv p i) X
  rw [hX.eq, ← two_smul ℂ X, smul_smul]
  norm_num

theorem measurable_pairHermPart : Measurable (pairHermPart (p := p) (i := i)) := by
  refine Measurable.subtype_mk ?_
  have hc : Continuous fun X : PairMatrix p i => (1 / 2 : ℂ) • (X + Xᴴ) :=
    (continuous_const_smul (1 / 2 : ℂ)).comp (continuous_id.add continuous_id.matrix_conjTranspose)
  exact measurable_reindex_comp _ hc.measurable

/-- The selected eigenvalue of `pairHermPart X` (pair labels); `pairEigval` without the proof. -/
def pairEigvalH (sel : CEH.EigenpairSelection (2 * p.W)) (X : PairMatrix p i)
    (k : PairSite p i) : ℝ :=
  sel.eigenvalue (pairHermPart X) (pairEquiv p i k)

/-- The selected eigenvector of `pairHermPart X` (pair coordinates and labels). -/
def pairEigvecH (sel : CEH.EigenpairSelection (2 * p.W)) (X : PairMatrix p i)
    (k : PairSite p i) : PairSite p i → ℂ :=
  fun a => sel.eigenvector (pairHermPart X) (pairEquiv p i k) (pairEquiv p i a)

theorem pairEigval_eq_H (sel : CEH.EigenpairSelection (2 * p.W)) {X : PairMatrix p i}
    (hX : X.IsHermitian) : pairEigval sel X hX = pairEigvalH sel X := by
  funext k
  unfold pairEigval pairEigvalH
  rw [pairHermPart_eq hX]

theorem pairEigvec_eq_H (sel : CEH.EigenpairSelection (2 * p.W)) {X : PairMatrix p i}
    (hX : X.IsHermitian) : pairEigvec sel X hX = pairEigvecH sel X := by
  funext k
  unfold pairEigvec pairEigvecH
  rw [pairHermPart_eq hX]

/-- The window radius `h = (2W)^{-1+β}` of `PairWindowGood`. -/
def windowRadius (p : Parameters) (β : ℝ) : ℝ := ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)

/-- `PairWindowGood` in proof-free form: `G` Hermitian and the window bounds for the selected
eigenpairs of `pairHermPart (K + G)`. -/
theorem pairWindowGood_iff (K : PairMatrix p i) (hK : K.IsHermitian)
    (sel : CEH.EigenpairSelection (2 * p.W)) (s E₀ β ε : ℝ) (J G : PairMatrix p i) :
    PairWindowGood K hK sel s E₀ β ε J G ↔ G.IsHermitian ∧ ∀ k l : PairSite p i,
      pairEigvalH sel (K + G) k ∈ Icc (E₀ - windowRadius p β) (E₀ + windowRadius p β) →
      pairEigvalH sel (K + G) l ∈ Icc (E₀ - windowRadius p β) (E₀ + windowRadius p β) →
      ‖star (pairEigvecH sel (K + G) k) ⬝ᵥ (J *ᵥ pairEigvecH sel (K + G) l) -
          (if k = l then pairCentre J K s (pairEigvalH sel (K + G) k) else 0)‖ ≤
        2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
  constructor
  · rintro ⟨hG, h⟩
    refine ⟨hG, ?_⟩
    rw [← pairEigval_eq_H sel (hK.add hG), ← pairEigvec_eq_H sel (hK.add hG)]
    exact h
  · rintro ⟨hG, h⟩
    refine ⟨hG, ?_⟩
    rw [pairEigval_eq_H sel (hK.add hG), pairEigvec_eq_H sel (hK.add hG)]
    exact h

variable {X : Type*} [MeasurableSpace X]

theorem measurable_add_snd {K : X → PairMatrix p i} (hK : Measurable K) :
    Measurable fun x : X × PairMatrix p i => K x.1 + x.2 := by
  refine measurable_matrix_of_entries fun a b => ?_
  simp only [Matrix.add_apply]
  exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hK.comp measurable_fst))).add
    ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd))

theorem measurable_pairEigvalH_comp (sel : CEH.EigenpairSelection (2 * p.W))
    {Y : X → PairMatrix p i} (hY : Measurable Y) (k : PairSite p i) :
    Measurable fun x => pairEigvalH sel (Y x) k :=
  (sel.measurable_eigenvalue _).comp (measurable_pairHermPart.comp hY)

theorem measurable_pairEigvecH_comp (sel : CEH.EigenpairSelection (2 * p.W))
    {Y : X → PairMatrix p i} (hY : Measurable Y) (k a : PairSite p i) :
    Measurable fun x => pairEigvecH sel (Y x) k a :=
  (sel.measurable_eigenvector _ _).comp (measurable_pairHermPart.comp hY)

/-- The overlap `u* J v` along measurable data. -/
theorem measurable_overlap_comp {J : X → PairMatrix p i} {u v : X → PairSite p i → ℂ}
    (hJ : Measurable J) (hu : ∀ a, Measurable fun x => u x a)
    (hv : ∀ a, Measurable fun x => v x a) :
    Measurable fun x => star (u x) ⬝ᵥ (J x *ᵥ v x) := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  refine Finset.measurable_sum _ fun a _ => ?_
  refine (Complex.continuous_conj.measurable.comp (hu a)).mul ?_
  exact Finset.measurable_sum _ fun b _ =>
    ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hJ)).mul (hv b)

/-- **The window ETH bad set is measurable**. For a measurable space `X` (e.g. the exterior data
`SplitState`), measurable `K : X → PairMatrix` with Hermitian values (e.g.
`K₀(ω, E) + ρ w(ω) w(ω)*` at a grid point), measurable `J`, `s > 0` and any eigenpair
selection, the set `{(x, G) | ¬ PairWindowGood (K x) _ sel s E₀ β ε (J x) G}` is measurable.
Its
section at `x` is the set bounded by `gue_not_pairWindowGood_le`.
-/
theorem measurableSet_not_pairWindowGood {K J : X → PairMatrix p i} (hKm : Measurable K)
    (hH : ∀ x, (K x).IsHermitian) (hJm : Measurable J) (sel : CEH.EigenpairSelection (2 * p.W))
    {s : ℝ} (hs : 0 < s) (E₀ β ε : ℝ) :
    MeasurableSet {x : X × PairMatrix p i |
      ¬ PairWindowGood (K x.1) (hH x.1) sel s E₀ β ε (J x.1) x.2} := by
  have hY := measurable_add_snd (p := p) (i := i) hKm
  have e : {x : X × PairMatrix p i |
      ¬ PairWindowGood (K x.1) (hH x.1) sel s E₀ β ε (J x.1) x.2} =
      ({x : X × PairMatrix p i | x.2.IsHermitian} ∩ {x | ∀ k l : PairSite p i,
        pairEigvalH sel (K x.1 + x.2) k ∈ Icc (E₀ - windowRadius p β) (E₀ + windowRadius p β) →
        pairEigvalH sel (K x.1 + x.2) l ∈ Icc (E₀ - windowRadius p β) (E₀ + windowRadius p β) →
        ‖star (pairEigvecH sel (K x.1 + x.2) k) ⬝ᵥ
              (J x.1 *ᵥ pairEigvecH sel (K x.1 + x.2) l) -
            (if k = l then pairCentre (J x.1) (K x.1) s (pairEigvalH sel (K x.1 + x.2) k)
              else 0)‖ ≤
          2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff]
    rw [pairWindowGood_iff]
  rw [e]
  refine MeasurableSet.compl ((measurableSet_isHermitian_matrix.preimage measurable_snd).inter ?_)
  refine measurableSet_setOfPred.mpr (Measurable.forall fun k => Measurable.forall fun l => ?_)
  have hwin : ∀ k : PairSite p i, Measurable fun x : X × PairMatrix p i =>
      pairEigvalH sel (K x.1 + x.2) k ∈ Icc (E₀ - windowRadius p β) (E₀ + windowRadius p β) :=
    fun k => measurableSet_setOfPred.mp
      (measurableSet_Icc.preimage (measurable_pairEigvalH_comp sel hY k))
  refine (hwin k).imp ((hwin l).imp (measurableSet_setOfPred.mp ?_))
  refine measurableSet_le (continuous_norm.measurable.comp ?_) measurable_const
  refine (measurable_overlap_comp (hJm.comp measurable_fst)
    (measurable_pairEigvecH_comp sel hY k) (measurable_pairEigvecH_comp sel hY l)).sub ?_
  by_cases hkl : k = l
  · simp only [hkl, ↓reduceIte]
    exact measurable_pairCentre_comp hs (hJm.comp measurable_fst) (hKm.comp measurable_fst)
      (measurable_pairEigvalH_comp sel hY l) (fun x => hH x.1)
  · simp only [hkl, ↓reduceIte]
    exact measurable_const

/-- **The window-count bad set is measurable** (the event of `gue_windowCount_le`
with an arbitrary window `[a, b]` and bound `c`). -/
theorem measurableSet_not_windowCount_le {K : X → PairMatrix p i} (hKm : Measurable K)
    (hH : ∀ x, (K x).IsHermitian) (sel : CEH.EigenpairSelection (2 * p.W)) (a b c : ℝ) :
    MeasurableSet {x : X × PairMatrix p i | ¬ ∃ hG : x.2.IsHermitian,
      ((Finset.univ.filter fun k => pairEigval sel (K x.1 + x.2) ((hH x.1).add hG) k ∈
          Icc a b).card : ℝ) ≤ c} := by
  have hY := measurable_add_snd (p := p) (i := i) hKm
  have e : {x : X × PairMatrix p i | ¬ ∃ hG : x.2.IsHermitian,
      ((Finset.univ.filter fun k => pairEigval sel (K x.1 + x.2) ((hH x.1).add hG) k ∈
          Icc a b).card : ℝ) ≤ c} =
      ({x : X × PairMatrix p i | x.2.IsHermitian} ∩ {x |
        (∑ k : PairSite p i, if pairEigvalH sel (K x.1 + x.2) k ∈ Icc a b then (1 : ℝ) else 0)
          ≤ c})ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h ⟨hG, hc⟩
      refine h ⟨hG, ?_⟩
      rw [pairEigval_eq_H sel ((hH x.1).add hG), Finset.card_filter]
      push_cast
      exact hc
    · rintro h ⟨hG, hc⟩
      refine h ⟨hG, ?_⟩
      rw [pairEigval_eq_H sel ((hH x.1).add hG), Finset.card_filter] at hc
      push_cast at hc
      exact hc
  rw [e]
  refine MeasurableSet.compl ((measurableSet_isHermitian_matrix.preimage measurable_snd).inter ?_)
  refine measurableSet_le (Finset.measurable_sum _ fun k _ => ?_) measurable_const
  exact Measurable.ite (measurableSet_Icc.preimage (measurable_pairEigvalH_comp sel hY k))
    measurable_const measurable_const

end Window

/-!
## The measurable window bad set at one grid point
-/

section Grid

variable {p : Parameters} {i : ZMod p.n}

/-- **The measurable, GUE-small window ETH bad set at one grid point**
(`gue_not_pairWindowGood_le` with `measurableSet_not_pairWindowGood`). Same constants and order of
quantifiers as `gue_not_pairWindowGood_le`. Uniformly in `p, i` with `2W ≥ N₀`, `s ∈ [sLo, sHi]`,
measurable spaces `X`, measurable `K, J : X → PairMatrix` with `K x` Hermitian and `J x` a
Hermitian contraction, `E₀` and eigenpair selections, the set
`S = {(x, G) | ¬ PairWindowGood (K x) _ sel s E₀ β ε (J x) G}` is measurable, and its section at
every `x` with `s^{-1/2}‖K x‖ ≤ C (2W)^A` and `PairRootRectangle (K x) s E₀ r v₀` has
`GUE_{2W}(s/2W)`-probability at most `(2W)^{-D}`. -/
theorem gridWindowBad (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hBridge : PairGUELawBridgeStatement)
    (A C sLo sHi r v₀ : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ ∀ β : ℝ, 0 < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s ∈ Icc sLo sHi,
        ∀ (X : Type) [MeasurableSpace X] (K J : X → PairMatrix p i), Measurable K →
          ∀ hH : ∀ x, (K x).IsHermitian, Measurable J → (∀ x, (J x).IsHermitian) →
          (∀ x, ‖J x‖ ≤ 1) → ∀ (E₀ : ℝ) (sel : CEH.EigenpairSelection (2 * p.W)),
          MeasurableSet {y : X × PairMatrix p i |
            ¬ PairWindowGood (K y.1) (hH y.1) sel s E₀ β ε (J y.1) y.2} ∧
          ∀ x : X, (Real.sqrt s)⁻¹ * ‖K x‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
            PairRootRectangle (K x) s E₀ r v₀ →
            gueMeasure (PairSite p i) (pairTime p s)
                (Prod.mk x ⁻¹' {y : X × PairMatrix p i |
                  ¬ PairWindowGood (K y.1) (hH y.1) sel s E₀ β ε (J y.1) y.2}) ≤
              ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨β₀, hβ₀, hβ₀2, h⟩ := gue_not_pairWindowGood_le inputs hAd hMDE hETH hBridge A C sLo sHi
    r v₀ hsLo hsHi hr hv₀
  refine ⟨β₀, hβ₀, hβ₀2, fun β hβ hββ ε D hε hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h β hβ hββ ε D hε hD
  refine ⟨N₀, fun p i hN s hsI X _ K J hKm hH hJm hJH hJn E₀ sel => ⟨?_, fun x hKx hR => ?_⟩⟩
  · exact measurableSet_not_pairWindowGood hKm hH hJm sel (hsLo.trans_le hsI.1) E₀ β ε
  · exact hN₀ p i hN s hsI (K x) (hH x) hKx E₀ hR sel (J x) (hJH x) (hJn x)

end Grid

end BlockBand.LocalWindow.ProofPartTwo
