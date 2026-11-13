module

public import BlockBand.LocalWindow.ProofPartTwoMeasurable
public import BlockBand.LocalWindow.ProofPartTwoCompressETH
public import BlockBand.LocalWindow.ProofPartTwoPoleMeasurable
public import BlockBand.LocalWindow.ProofPartTwoPoleCompl

/-!
# A measurable bad set for the large-`ρ` branch

The large-`ρ` window event of part (ii) has a measurable complement, whose sections are controlled
by the compressed window estimate; the small-`ρ` grid deformations are made measurable from the
basis-free pole data.

## Main results

* `measurable_schurK0`, `schurK0H` (Hermitian part `(K + K*)/2`), `measurable_schurK0H`,
  `isHermitian_schurK0H`, `schurK0H_eq` (`= schurK0` for Hermitian `H_R`, `V`).
* **`LargeRhoGridGood K sel s E₀ h tol J G`**: `G` Hermitian and every selected eigenpair
  `(λ_k, v_k)` of `K + G` with `λ_k ∈ [E₀ - h, E₀ + h]` has
  `‖v_k* J v_k - pairCentre J K s λ_k‖ ≤ tol`.
* **`measurableSet_not_largeRhoGridGood`**: for measurable `K` (Hermitian values) and `J`, the
  set `{(x, G) | ¬ LargeRhoGridGood (K x) sel s E₀ h tol (J x) G}` is measurable.
* **`largeRhoGridGood_of_compress`** (deterministic, one exterior point): `K = M' + ρww*` with
  `M'` Hermitian, `U` an isometry onto `w^⊥`, `‖M' + G‖ ≤ K_b`, `4K_b ≤ |ρ|`, the compressed
  window bound `NatWindowGood F sel' s' E₀ β ε (U*JU) (U*GU)` (`F = U*M'U`, `N = 2W - 1`,
  `h_N = N^{-1+β}`), at most `n_S` compressed eigenvalues in `[E₀ - h_N, E₀ + h_N]`, and the
  compressed centre within `η` of `pairCentre J K s λ` give `LargeRhoGridGood` on the half
  window with the explicit tolerance `largeRhoTol` (`largeRho_window_transfer`).
* **`largeRho_section_subset`**: the same as an inclusion of the section into
  `{G not Hermitian} ∪ {¬ NatWindowGood} ∪ {K_b < ‖M' + G‖} ∪ {compressed count > n_S}`, the
  form in which `gue_not_compressWindowGood_le` bounds the section pointwise in `x`.

For the small-`ρ` branch (grids in `(e, ρ)` and pole labels `j₀`), the grid
deformation `F_reg(e) + ρ_g ww* - e` is itself made measurable from the basis-free pole data
(`regFm`, `poleWW`):

* **`poleGridK ε j₀ e ρ_g ω`** (Hermitian part of `regFm(e) - e + ρ_g poleWW`),
  **`measurable_poleGridK`**, `isHermitian_poleGridK`, **`poleGridK_eq`** (`= F_reg(e) - e +
  ρ_g ww*` with `regF`, `poleDir` on the label event), and the label event
  **`measurableSet_poleLabel`** `{ω | H_R Hermitian, j₀ simple, PoleSeparated ε j₀ e}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped ENNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

/-!
## The deformation at a fixed grid energy is measurable
-/

section Schur

/-- `ω ↦ K₀(ω, e) = F(e) - e` is Borel measurable (fixed `e`). -/
theorem measurable_schurK0 (e : ℝ) : Measurable fun om : SplitState p i => schurK0 p i om e := by
  have hC : Measurable fun om : SplitState p i => om.2.1 := measurable_fst.comp measurable_snd
  have hR : Measurable fun om : SplitState p i => physicalCoareaResolvent om.1 e := by
    unfold physicalCoareaResolvent
    have hc : Continuous fun H : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ =>
        H - (e : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ) :=
      continuous_id.sub continuous_const
    exact measurable_matrixInverse.comp (hc.measurable.comp measurable_fst)
  unfold schurK0 physicalCoareaF
  exact ((measurable_snd.comp measurable_snd).sub (measurable_matrix_mul'
    (measurable_matrix_mul' (measurable_conjTranspose' hC) hR) hC)).sub measurable_const

/-- The Hermitian part `(K₀ + K₀*)/2` of the deformation `K₀(ω, e)` at fixed `e` (Hermitian for
every `ω`). -/
def schurK0H (om : SplitState p i) (e : ℝ) : PairMatrix p i :=
  (1 / 2 : ℂ) • (schurK0 p i om e + (schurK0 p i om e)ᴴ)

theorem isHermitian_schurK0H (om : SplitState p i) (e : ℝ) : (schurK0H om e).IsHermitian := by
  unfold schurK0H Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem measurable_schurK0H (e : ℝ) : Measurable fun om : SplitState p i => schurK0H om e := by
  have hc : Continuous fun X : PairMatrix p i => (1 / 2 : ℂ) • (X + Xᴴ) :=
    (continuous_const_smul (1 / 2 : ℂ)).comp (continuous_id.add continuous_id.matrix_conjTranspose)
  exact hc.measurable.comp (measurable_schurK0 e)

/-- For Hermitian `H_R` and `V`, `schurK0H = schurK0`. -/
theorem schurK0H_eq {om : SplitState p i} (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian)
    (e : ℝ) : schurK0H om e = schurK0 p i om e := by
  have hK : (schurK0 p i om e).IsHermitian := by
    unfold schurK0
    refine (hV.sub (isHermitian_conjTranspose_mul_mul om.2.1 ?_)).sub ?_
    · unfold physicalCoareaResolvent
      refine IsHermitian.inv (hH.sub ?_)
      rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    · rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
  unfold schurK0H
  rw [hK.eq, ← two_smul ℂ (schurK0 p i om e), smul_smul]
  norm_num

end Schur

/-!
## The large-`ρ` window event and its measurability
-/

section Event

/-- **The large-`ρ` window event at one grid point**: `G` is
Hermitian and every selected eigenpair `(λ_k, v_k)` of `K + G` with `λ_k ∈ [E₀ - h, E₀ + h]` has
`‖v_k* J v_k - pairCentre J K s λ_k‖ ≤ tol`. Proof-free selected eigenpairs (`pairEigvalH`,
`pairEigvecH`), so no pole datum enters. -/
def LargeRhoGridGood (K : PairMatrix p i) (sel : CEH.EigenpairSelection (2 * p.W))
    (s E₀ h tol : ℝ) (J G : PairMatrix p i) : Prop :=
  G.IsHermitian ∧ ∀ k : PairSite p i,
    pairEigvalH sel (K + G) k ∈ Icc (E₀ - h) (E₀ + h) →
    ‖star (pairEigvecH sel (K + G) k) ⬝ᵥ (J *ᵥ pairEigvecH sel (K + G) k) -
        pairCentre J K s (pairEigvalH sel (K + G) k)‖ ≤ tol

variable {X : Type*} [MeasurableSpace X]

/-- **The large-`ρ` bad set is measurable**: for measurable `K : X → PairMatrix` with Hermitian
values (e.g. `schurK0H · e`), measurable `J` (e.g. `B(·, e)`), `s > 0` and any eigenpair
selection, `{(x, G) | ¬ LargeRhoGridGood (K x) sel s E₀ h tol (J x) G}` is
measurable.
-/
theorem measurableSet_not_largeRhoGridGood {K J : X → PairMatrix p i} (hKm : Measurable K)
    (hH : ∀ x, (K x).IsHermitian) (hJm : Measurable J) (sel : CEH.EigenpairSelection (2 * p.W))
    {s : ℝ} (hs : 0 < s) (E₀ h tol : ℝ) :
    MeasurableSet {y : X × PairMatrix p i |
      ¬ LargeRhoGridGood (K y.1) sel s E₀ h tol (J y.1) y.2} := by
  have hY := measurable_add_snd (p := p) (i := i) hKm
  have e : {y : X × PairMatrix p i | ¬ LargeRhoGridGood (K y.1) sel s E₀ h tol (J y.1) y.2} =
      ({y : X × PairMatrix p i | y.2.IsHermitian} ∩ {y | ∀ k : PairSite p i,
        pairEigvalH sel (K y.1 + y.2) k ∈ Icc (E₀ - h) (E₀ + h) →
        ‖star (pairEigvecH sel (K y.1 + y.2) k) ⬝ᵥ (J y.1 *ᵥ pairEigvecH sel (K y.1 + y.2) k) -
            pairCentre (J y.1) (K y.1) s (pairEigvalH sel (K y.1 + y.2) k)‖ ≤ tol})ᶜ := by
    ext y
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, LargeRhoGridGood]
  rw [e]
  refine MeasurableSet.compl ((measurableSet_isHermitian_matrix.preimage measurable_snd).inter ?_)
  refine measurableSet_setOfPred.mpr (Measurable.forall fun k => ?_)
  refine (measurableSet_setOfPred.mp
    (measurableSet_Icc.preimage (measurable_pairEigvalH_comp sel hY k))).imp
    (measurableSet_setOfPred.mp ?_)
  refine measurableSet_le (continuous_norm.measurable.comp ?_) measurable_const
  exact (measurable_overlap_comp (hJm.comp measurable_fst) (measurable_pairEigvecH_comp sel hY k)
    (measurable_pairEigvecH_comp sel hY k)).sub
    (measurable_pairCentre_comp hs (hJm.comp measurable_fst) (hKm.comp measurable_fst)
      (measurable_pairEigvalH_comp sel hY k) (fun x => hH x.1))

end Event

/-!
## The pointwise section bound from the compressed window
-/

section Section

/-- The compressed window radius `h_N = N^{-1+β}`, `N = 2W - 1`. -/
def compressRadius (p : Parameters) (β : ℝ) : ℝ := ((2 * p.W - 1 : ℕ) : ℝ) ^ (-1 + β)

/-- The compressed ETH tolerance `2 N^ε N^{-1/2}`, `N = 2W - 1`. -/
def compressTol (p : Parameters) (ε : ℝ) : ℝ :=
  2 * (((2 * p.W - 1 : ℕ) : ℝ) ^ ε * ((2 * p.W - 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))

/-- The tolerance of `largeRhoGridGood_of_compress`:
`n_S · 2N^εN^{-1/2} + η + 2τ + (1 + C₀)τ² + q(2 + q) + 2qC₀`, `q = 2K_b/|ρ|`,
`τ = (4K_b²/|ρ|)/(h_N/2)`. -/
def largeRhoTol (p : Parameters) (β ε nS η C₀ Kb ρ : ℝ) : ℝ :=
  nS * compressTol p ε + η + 2 * ((0 + 4 * Kb ^ 2 / |ρ|) / (compressRadius p β / 2)) +
    (1 + C₀) * ((0 + 4 * Kb ^ 2 / |ρ|) / (compressRadius p β / 2)) ^ 2 +
    2 * Kb / |ρ| * (2 + 2 * Kb / |ρ|) + 2 * (2 * Kb / |ρ|) * C₀

theorem isHermitian_real_smul_vecMulVec (ρ : ℝ) (w : PairSite p i → ℂ) :
    (((ρ : ℝ) : ℂ) • vecMulVec w (star w)).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_vecMulVec, star_star, Complex.star_def,
    Complex.conj_ofReal]

theorem sqNorm_eq_one_of_orthonormalFamily {ι : Type} [Fintype ι] [DecidableEq ι] {e : ι → ι → ℂ}
    (he : IsOrthonormalFamily e) (k : ι) : sqNorm (e k) = 1 := by
  have h := he k k
  simp only [↓reduceIte, star_dotProduct_self] at h
  exact_mod_cast h

/-- **The large-`ρ` window event from the compressed window** (deterministic,
at one exterior point). Let `M'` be Hermitian, `w` a unit vector, `U` an isometry onto `w^⊥`,
`ρ` real, `K = M' + ρww*`, `J` a contraction, `G` Hermitian with `‖M' + G‖ ≤ K_b`,
`4K_b ≤ |ρ|`, `|E₀| + h_N ≤ K_b`, and `F` the compressed regular part (`F = U*M'U`). If the
compressed window bound `NatWindowGood F sel' s' E₀ β ε (U*JU) (U*GU)` holds, at most `n_S`
compressed eigenvalues lie in `[E₀ - h_N, E₀ + h_N]`, the compressed centre at every `λ'` of that
window is within `η` of `pairCentre J K s λ` for `λ` in the half window and
`‖pairCentre J K s λ‖ ≤ C₀` there, then `LargeRhoGridGood K sel s E₀ (h_N/2) tol J G` with
`tol = largeRhoTol`. -/
theorem largeRhoGridGood_of_compress {M' J G : PairMatrix p i} (hM' : M'.IsHermitian)
    (hJn : ‖J‖ ≤ 1) (hG : G.IsHermitian) {w : PairSite p i → ℂ}
    (hw : sqNorm w = 1) {U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ} (hUU : Uᴴ * U = 1)
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) {ρ Kb : ℝ} (hKb : 0 < Kb)
    (hMG : ‖M' + G‖ ≤ Kb) (hρ : 4 * Kb ≤ |ρ|) (F : CEH.SourceHermitian (2 * p.W - 1))
    (hF : F.1 = Uᴴ * M' * U) (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {s s' E₀ β ε nS η C₀ : ℝ}
    (hE₀ : |E₀| + compressRadius p β ≤ Kb)
    (hwin : NatWindowGood F sel' s' E₀ β ε (Uᴴ * J * U) (Uᴴ * G * U))
    (hcount : ∀ hX : (Uᴴ * G * U).IsHermitian,
      ((Finset.univ.filter fun k => sel'.eigenvalue (natDeformed F (Uᴴ * G * U) hX) k ∈
        Icc (E₀ - compressRadius p β) (E₀ + compressRadius p β)).card : ℝ) ≤ nS)
    (hcen : ∀ lam ∈ Icc (E₀ - compressRadius p β / 2) (E₀ + compressRadius p β / 2),
      ∀ lam' ∈ Icc (E₀ - compressRadius p β) (E₀ + compressRadius p β),
        ‖nativeCentre (Uᴴ * J * U) F.1 s' lam' -
          pairCentre J (M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) s lam‖ ≤ η)
    (hc₀ : ∀ lam ∈ Icc (E₀ - compressRadius p β / 2) (E₀ + compressRadius p β / 2),
      ‖pairCentre J (M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) s lam‖ ≤ C₀) :
    LargeRhoGridGood (M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) sel s E₀
      (compressRadius p β / 2) (largeRhoTol p β ε nS η C₀ Kb ρ) J G := by
  set K := M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w) with hKdef
  set hN := compressRadius p β with hhN
  have hN0 : 0 < hN := by
    have : (0 : ℝ) < ((2 * p.W - 1 : ℕ) : ℝ) := by
      have := p.W_pos
      exact_mod_cast (by omega : 0 < 2 * p.W - 1)
    exact Real.rpow_pos_of_pos this _
  have hKH : K.IsHermitian := hM'.add (isHermitian_real_smul_vecMulVec ρ w)
  have hA : (K + G).IsHermitian := hKH.add hG
  obtain ⟨hX, hwin'⟩ := hwin
  refine ⟨hG, fun k hk => ?_⟩
  set lam := pairEigvalH sel (K + G) k with hlamdef
  set v := pairEigvecH sel (K + G) k with hvdef
  have hv1 : sqNorm v = 1 := by
    rw [hvdef, ← pairEigvec_eq_H sel hA]
    exact sqNorm_eq_one_of_orthonormalFamily (isOrthonormalFamily_pairEigvec sel _ hA) k
  have heig : (M' + G + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) *ᵥ v = (lam : ℂ) • v := by
    have h := mulVec_pairEigvec sel (K + G) hA k
    rw [pairEigvec_eq_H sel hA, pairEigval_eq_H sel hA] at h
    rw [show M' + G + ((ρ : ℝ) : ℂ) • vecMulVec w (star w) = K + G by rw [hKdef]; abel]
    exact h
  have hlam : |lam| ≤ Kb :=
    abs_le.mpr ⟨by linarith [neg_abs_le E₀, hk.1], by linarith [le_abs_self E₀, hk.2]⟩
  -- the compressed grid matrix and its selected eigenpairs
  set Y := natDeformed F (Uᴴ * G * U) hX with hYdef
  set ek := sel'.eigenvector Y with hekdef
  set mu := sel'.eigenvalue Y with hmudef
  have he : IsOrthonormalFamily ek := fun a b => sel'.orthonormal Y a b
  have heigA : ∀ a, Y.1 *ᵥ ek a = (mu a : ℂ) • ek a := fun a => sel'.eigen_equation Y a
  have hYeq : Y.1 = Uᴴ * (M' + G) * U := by
    rw [hYdef]
    show F.1 + Uᴴ * G * U = _
    rw [hF, Matrix.mul_add, Matrix.add_mul]
  set S := Finset.univ.filter fun a => |mu a - lam| < hN / 2 with hSdef
  have hS : ∀ a ∉ S, hN / 2 ≤ |mu a - lam| := by
    intro a ha
    simpa [hSdef] using ha
  have hSwin : ∀ a ∈ S, mu a ∈ Icc (E₀ - hN) (E₀ + hN) := by
    intro a ha
    have h1 : |mu a - lam| < hN / 2 := by simpa [hSdef] using ha
    have h2 := abs_lt.mp h1
    exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hcard : (S.card : ℝ) ≤ nS := by
    refine le_trans ?_ (hcount hX)
    exact_mod_cast Finset.card_le_card fun a ha =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hSwin a ha⟩
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      ‖star (ek a) ⬝ᵥ ((Uᴴ * J * U) *ᵥ ek b) -
          (if a = b then nativeCentre (Uᴴ * J * U) F.1 s' (mu a) else 0)‖ ≤
        compressTol p ε := fun a ha b hb => hwin' a b (hSwin a ha) (hSwin b hb)
  have hcen' : ∀ a ∈ S, ‖nativeCentre (Uᴴ * J * U) F.1 s' (mu a) - pairCentre J K s lam‖ ≤ η :=
    fun a ha => hcen lam ⟨by linarith [hk.1], by linarith [hk.2]⟩ (mu a) (hSwin a ha)
  have hε1 : 0 ≤ compressTol p ε := by unfold compressTol; positivity
  have hη : 0 ≤ η := by
    rcases S.eq_empty_or_nonempty with hSe | ⟨a, ha⟩
    · exact le_trans (norm_nonneg _) (hcen lam ⟨by linarith [hk.1], by linarith [hk.2]⟩ E₀
        ⟨by linarith, by linarith⟩)
    · exact le_trans (norm_nonneg _) (hcen' a ha)
  have hMG' : ‖M' + G‖ ≤ Kb := hMG
  have hBA : ‖Uᴴ * (M' + G) * U - Y.1‖ ≤ 0 := by rw [hYeq, sub_self, norm_zero]
  have hT := largeRho_window_transfer hKb hMG' hUU hUw hcompl hw hv1 hρ hlam heig hJn
    (Y.2) he heigA le_rfl (half_pos hN0) hBA hS hε1 hη hpair hcen'
  have hc0 : ‖pairCentre J K s lam‖ ≤ C₀ := hc₀ lam ⟨by linarith [hk.1], by linarith [hk.2]⟩
  refine hT.trans ?_
  unfold largeRhoTol
  rw [← hhN]
  have hq : 0 ≤ 2 * Kb / |ρ| := by positivity
  have hτ : 0 ≤ ((0 + 4 * Kb ^ 2 / |ρ|) / (hN / 2)) ^ 2 := sq_nonneg _
  gcongr

/-- **The section inclusion** (pointwise in the exterior): under the
deterministic hypotheses of `largeRhoGridGood_of_compress` other than those on `G`, the set of
`G` violating `LargeRhoGridGood` lies in the union of `{G not Hermitian}`, the compressed window
bad set `{¬ NatWindowGood F sel' s' E₀ β ε (U*JU) (U*GU)}` (bounded by
`gue_not_compressWindowGood_le`), the norm event `{K_b < ‖M' + G‖}` and the compressed-count
event. -/
theorem largeRho_section_subset {M' J : PairMatrix p i} (hM' : M'.IsHermitian)
    (hJn : ‖J‖ ≤ 1) {w : PairSite p i → ℂ}
    (hw : sqNorm w = 1) {U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ} (hUU : Uᴴ * U = 1)
    (hUw : Uᴴ *ᵥ w = 0) (hcompl : U * Uᴴ + vecMulVec w (star w) = 1) {ρ Kb : ℝ} (hKb : 0 < Kb)
    (hρ : 4 * Kb ≤ |ρ|) (F : CEH.SourceHermitian (2 * p.W - 1))
    (hF : F.1 = Uᴴ * M' * U) (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {s s' E₀ β ε nS η C₀ : ℝ}
    (hE₀ : |E₀| + compressRadius p β ≤ Kb)
    (hcen : ∀ lam ∈ Icc (E₀ - compressRadius p β / 2) (E₀ + compressRadius p β / 2),
      ∀ lam' ∈ Icc (E₀ - compressRadius p β) (E₀ + compressRadius p β),
        ‖nativeCentre (Uᴴ * J * U) F.1 s' lam' -
          pairCentre J (M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) s lam‖ ≤ η)
    (hc₀ : ∀ lam ∈ Icc (E₀ - compressRadius p β / 2) (E₀ + compressRadius p β / 2),
      ‖pairCentre J (M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) s lam‖ ≤ C₀) :
    {G : PairMatrix p i | ¬ LargeRhoGridGood (M' + ((ρ : ℝ) : ℂ) • vecMulVec w (star w)) sel s
        E₀ (compressRadius p β / 2) (largeRhoTol p β ε nS η C₀ Kb ρ) J G} ⊆
      {G | ¬ G.IsHermitian} ∪
        {G | ¬ NatWindowGood F sel' s' E₀ β ε (Uᴴ * J * U) (Uᴴ * G * U)} ∪
        {G | Kb < ‖M' + G‖} ∪
        {G | ¬ ∀ hX : (Uᴴ * G * U).IsHermitian,
          ((Finset.univ.filter fun k => sel'.eigenvalue (natDeformed F (Uᴴ * G * U) hX) k ∈
            Icc (E₀ - compressRadius p β) (E₀ + compressRadius p β)).card : ℝ) ≤ nS} := by
  intro G hG
  by_contra hno
  simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_lt] at hno
  obtain ⟨⟨⟨hGH, hwin⟩, hMG⟩, hcount⟩ := hno
  exact hG (largeRhoGridGood_of_compress hM' hJn hGH hw hUU hUw hcompl hKb hMG hρ F hF sel
    sel' hE₀ hwin hcount hcen hc₀)

end Section

/-!
## The small-`ρ` grid deformation and the pole-label event
-/

section SmallGrid

attribute [local instance] pairSite_nonempty

/-- **The small-`ρ` grid deformation in measurable form**: the Hermitian part of
`regFm(e) - e + ρ_g poleWW` (basis-free `F_reg(e) + ρ_g ww* - e`). -/
def poleGridK (ε : ℝ) (j₀ : ExteriorSite p i) (e ρg : ℝ) (om : SplitState p i) :
    PairMatrix p i :=
  (1 / 2 : ℂ) • ((regFm ε j₀ om.1 om.2.1 om.2.2 e - (e : ℂ) • 1 +
      ((ρg : ℝ) : ℂ) • poleWW j₀ om.1 om.2.1) +
    (regFm ε j₀ om.1 om.2.1 om.2.2 e - (e : ℂ) • 1 + ((ρg : ℝ) : ℂ) • poleWW j₀ om.1 om.2.1)ᴴ)

theorem isHermitian_poleGridK (ε : ℝ) (j₀ : ExteriorSite p i) (e ρg : ℝ) (om : SplitState p i) :
    (poleGridK ε j₀ e ρg om).IsHermitian := by
  unfold poleGridK Matrix.IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

theorem measurable_poleGridK {ε : ℝ} (hε : 0 < ε) (j₀ : ExteriorSite p i) (e ρg : ℝ) :
    Measurable (poleGridK (p := p) (i := i) ε j₀ e ρg) := by
  have h1 : Measurable fun om : SplitState p i => regFm ε j₀ om.1 om.2.1 om.2.2 e -
      (e : ℂ) • (1 : PairMatrix p i) + ((ρg : ℝ) : ℂ) • poleWW j₀ om.1 om.2.1 :=
    ((measurable_regFm hε j₀ e).sub measurable_const).add
      (measurable_smul_matrix measurable_const (measurable_poleWW j₀))
  have hc : Continuous fun X : PairMatrix p i => (1 / 2 : ℂ) • (X + Xᴴ) :=
    (continuous_const_smul (1 / 2 : ℂ)).comp (continuous_id.add continuous_id.matrix_conjTranspose)
  exact hc.measurable.comp h1

/-- **On the label event the measurable grid deformation is `F_reg(e) + ρ_g ww* - e`** (with
`regF`, `poleDir`). -/
theorem poleGridK_eq {ε : ℝ} {om : SplitState p i} (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) {j₀ : ExteriorSite p i} (hs : PoleSimple hH j₀) {e : ℝ}
    (hsep : PoleSeparated ε hH j₀ e) (ρg : ℝ) :
    poleGridK ε j₀ e ρg om = regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • 1 +
      ((ρg : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) := by
  have hX : (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) +
      ((ρg : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ om.2.1)
        (star (poleDir hH j₀ om.2.1))).IsHermitian :=
    (isHermitian_regK om hH hV j₀ e).add (isHermitian_real_smul_vecMulVec ρg _)
  unfold poleGridK
  rw [← regF_eq_regFm ε hH hs om.2.1 om.2.2 hsep, poleWW_eq hH hs, hX.eq,
    ← two_smul ℂ (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i) +
      ((ρg : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1))),
    smul_smul]
  norm_num

/-- **The pole-label event is measurable**: `{ω | H_R Hermitian, j₀ simple, every other exterior
eigenvalue at distance > ε from e}`. -/
theorem measurableSet_poleLabel (ε : ℝ) (j₀ : ExteriorSite p i) (e : ℝ) :
    MeasurableSet {om : SplitState p i |
      ∃ hH : om.1.IsHermitian, PoleSimple hH j₀ ∧ PoleSeparated ε hH j₀ e} := by
  have hm : ∀ j, Measurable fun om : SplitState p i => herEig om.1 j :=
    fun j => (measurable_herEig j).comp measurable_fst
  have e' : {om : SplitState p i |
      ∃ hH : om.1.IsHermitian, PoleSimple hH j₀ ∧ PoleSeparated ε hH j₀ e} =
      {om | om.1.IsHermitian} ∩ ⋂ j ∈ (Finset.univ.erase j₀ : Finset (ExteriorSite p i)),
        ({om | herEig om.1 j ≠ herEig om.1 j₀} ∩ {om | ε < |herEig om.1 j - e|}) := by
    ext om
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_erase, Finset.mem_univ,
      and_true]
    constructor
    · rintro ⟨hH, hs, hsep⟩
      refine ⟨hH, fun j hj => ?_⟩
      rw [herEig_eq hH, herEig_eq hH]
      exact ⟨hs j hj, hsep j hj⟩
    · rintro ⟨hH, h⟩
      refine ⟨hH, fun j hj => ?_, fun j hj => ?_⟩
      · have := (h j hj).1
        rwa [herEig_eq hH, herEig_eq hH] at this
      · have := (h j hj).2
        rwa [herEig_eq hH] at this
  rw [e']
  refine (measurableSet_isHermitian'.preimage measurable_fst).inter
    (MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_)
  exact (measurableSet_eq_fun (hm j) (hm j₀)).compl.inter
    (measurableSet_lt measurable_const (((hm j).sub measurable_const).abs))

end SmallGrid

end BlockBand.LocalWindow.ProofPartTwo
