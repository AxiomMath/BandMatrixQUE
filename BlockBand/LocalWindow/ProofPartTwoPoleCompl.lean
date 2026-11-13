module

public import BlockBand.LocalWindow.ProofPartTwoPole

/-!
# The pole decomposition in the form of the large-`ρ` step

The pole decomposition of the Schur matrix together with an isometry onto the orthogonal
complement of the pole direction, as used by the large-`ρ` branch.

## Main results

* **`exists_isometry_compl`**: for a unit vector `w ∈ ℂ^β`, `|β| = n + 1`, there is
  `U : ℂ^n → ℂ^β` with `U*U = 1`, `U*w = 0`, `UU* + ww* = 1` (an isometry onto `w^⊥`).
* `pairSite_nonempty`; `exists_pairIsometry_compl` (`n = 2W - 1`, the index of
  `CompressedGUELawBridgeStatement`).
* **`schurK0_pole_decomp`**: at a nonpole energy, `schurK0 ω E = M' + ρ(E) ww*` with
  `M' = F_reg(E) - E` (the hypothesis `hdec` of the large-`ρ` window transfer
  `largeRho_window_transfer` / the class (b) compression step).
* `isHermitian_regK`, **`opNorm_regK_le`** (`‖F_reg(E) - E‖ ≤ ‖V‖ + ‖C‖²/ε + |E|`),
  `opNorm_regK_sub_le`.
* **`schurK0_largeRho_data`**: everything at once (the existential package of `M'`, `w`, `ρ`,
  `U` with `M'` Hermitian, the norm bound, `w` unit, `hdec`, and the isometry identities).
* **`pairRootRectangle_regF_family`**, **`pairRootRectangle_schurK0_pole`**: the root rectangle of
  `F_reg(e) + ρww* - e` for every real `ρ` (uniformly in `ρ`, on the pole interval) and of
  `schurK0 ω e` (nonpole `e`), from the certificate of `F̂(e)`
  (`pairRootRectangle_rankOne_family`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Coarea BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator ComplexConjugate InnerProductSpace

/-!
## An isometry onto `w^⊥`
-/

section Isometry

variable {β : Type} [Fintype β] [DecidableEq β]

/-- **An isometry onto `w^⊥`**: for a unit vector `w ∈ ℂ^β` with `|β| = n + 1`, there is
`U : ℂ^n → ℂ^β` with `U*U = 1`, `U*w = 0` and `UU* + ww* = 1`. -/
theorem exists_isometry_compl (n : ℕ) (hn : Fintype.card β = n + 1) {w : β → ℂ}
    (hw : sqNorm w = 1) :
    ∃ U : Matrix β (Fin n) ℂ, Uᴴ * U = 1 ∧ Uᴴ *ᵥ w = 0 ∧
      U * Uᴴ + vecMulVec w (star w) = 1 := by
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ β) = Fintype.card (Option (Fin n)) := by
    rw [finrank_euclideanSpace, hn, Fintype.card_option, Fintype.card_fin]
  have hwn : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ β)‖ = 1 := by
    rw [← vnorm_eq, vnorm_of_sqNorm_one hw]
  have hon : Orthonormal ℂ (({none} : Set (Option (Fin n))).domRestrict
      fun _ => (WithLp.toLp 2 w : EuclideanSpace ℂ β)) :=
    ⟨fun _ => hwn, fun a b hab => absurd (Subsingleton.elim a b) hab⟩
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hon
  set e : Option (Fin n) → β → ℂ := fun o => WithLp.ofLp (b o) with hedef
  have he0 : e none = w := by
    simp only [hedef]; rw [hb none (Set.mem_singleton _)]
  have horth : ∀ o o', star (e o) ⬝ᵥ e o' = if o = o' then 1 else 0 := by
    intro o o'
    have h := orthonormal_iff_ite.mp b.orthonormal o o'
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  have hcomp : ∀ x y : β, ∑ o, e o x * star (e o y) = if x = y then 1 else 0 := by
    intro x y
    have h := congrArg (fun v : EuclideanSpace ℂ β => WithLp.ofLp v x)
      (b.sum_repr' (WithLp.toLp 2 (Pi.single y (1 : ℂ))))
    simp only [EuclideanSpace.inner_eq_star_dotProduct, single_dotProduct,
      one_mul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.star_apply] at h
    rw [Pi.single_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [hedef]; ring
  refine ⟨Matrix.of fun x m => e (some m) x, ?_, ?_, ?_⟩
  · ext k l
    have h := horth (some k) (some l)
    simp only [Option.some.injEq] at h
    rw [Matrix.one_apply, ← h]
    simp [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
  · funext k
    have h := horth (some k) none
    rw [he0] at h
    simp only [reduceCtorEq, ite_false] at h
    rw [Pi.zero_apply, ← h]
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  · ext x y
    rw [Matrix.add_apply, Matrix.one_apply, ← hcomp x y, Fintype.sum_option, he0, add_comm]
    simp [Matrix.mul_apply, vecMulVec_apply, Matrix.conjTranspose_apply]

end Isometry

/-!
## The pair level
-/

section Pair

variable {p : Parameters} {i : ZMod p.n}

/-- The pair is nonempty. -/
theorem pairSite_nonempty (p : Parameters) (i : ZMod p.n) : Nonempty (PairSite p i) :=
  ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩

attribute [local instance] pairSite_nonempty

/-- An isometry `U : ℂ^{2W-1} → w^⊥` for a unit pair vector `w`. -/
theorem exists_pairIsometry_compl {w : PairSite p i → ℂ} (hw : sqNorm w = 1) :
    ∃ U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ, Uᴴ * U = 1 ∧ Uᴴ *ᵥ w = 0 ∧
      U * Uᴴ + vecMulVec w (star w) = 1 := by
  refine exists_isometry_compl _ ?_ hw
  rw [BlockBand.Angular.FiberAngular.card_pairSite]
  have := p.W_pos
  omega

/-- **`hdec`**: at a nonpole energy, `schurK0 ω E = M' + ρ(E) ww*` with
`M' = F_reg(E) - E`, `ρ = poleRho`, `w = poleDir`. -/
theorem schurK0_pole_decomp (om : SplitState p i) (hH : om.1.IsHermitian)
    (j₀ : ExteriorSite p i) {E : ℝ} (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0) :
    schurK0 p i om E = (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1) +
      ((poleRho hH j₀ om.2.1 E : ℝ) : ℂ) •
        vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) := by
  rw [schurK0, physicalCoareaF_pole_decomp hH j₀ om.2.1 om.2.2 hdet]
  abel

/-- `M' = F_reg(E) - E` is Hermitian for Hermitian `V`. -/
theorem isHermitian_regK (om : SplitState p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) (j₀ : ExteriorSite p i) (E : ℝ) :
    (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i)).IsHermitian := by
  refine (isHermitian_regF hH j₀ om.2.1 hV E).sub ?_
  rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- **`‖M'‖ ≤ ‖V‖ + ‖C‖²/ε + |E|`** on the pole interval. -/
theorem opNorm_regK_le {ε : ℝ} (hε : 0 < ε) (om : SplitState p i) (hH : om.1.IsHermitian)
    (j₀ : ExteriorSite p i) {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) :
    ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i)‖ ≤
      ‖om.2.2‖ + ‖om.2.1‖ ^ 2 / ε + |E| := by
  have h1 := opNorm_regF_le hε hH j₀ om.2.1 om.2.2 hsep
  have h2 : ‖(E : ℂ) • (1 : PairMatrix p i)‖ = |E| := by
    rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  linarith [norm_sub_le (regF hH j₀ om.2.1 om.2.2 E) ((E : ℂ) • (1 : PairMatrix p i))]

/-- `M'(E) - M'(E')` is controlled by the Lipschitz bound of `F_reg` plus `|E - E'|`. -/
theorem opNorm_regK_sub_le {ε : ℝ} (hε : 0 < ε) (om : SplitState p i) (hH : om.1.IsHermitian)
    (j₀ : ExteriorSite p i) {E E' : ℝ} (hsep : PoleSeparated ε hH j₀ E)
    (hsep' : PoleSeparated ε hH j₀ E') :
    ‖(regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i)) -
        (regF hH j₀ om.2.1 om.2.2 E' - (E' : ℂ) • (1 : PairMatrix p i))‖ ≤
      (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - E'| := by
  have h1 := opNorm_regF_sub_le hε hH j₀ om.2.1 om.2.2 hsep hsep'
  have hd : (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i)) -
      (regF hH j₀ om.2.1 om.2.2 E' - (E' : ℂ) • (1 : PairMatrix p i)) =
      (regF hH j₀ om.2.1 om.2.2 E - regF hH j₀ om.2.1 om.2.2 E') -
        ((E - E' : ℝ) : ℂ) • (1 : PairMatrix p i) := by
    rw [Complex.ofReal_sub, sub_smul]; abel
  have h2 : ‖((E - E' : ℝ) : ℂ) • (1 : PairMatrix p i)‖ = |E - E'| := by
    rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hd]
  have h3 : ‖om.2.1‖ ^ 2 * (|E - E'| / ε ^ 2) = ‖om.2.1‖ ^ 2 / ε ^ 2 * |E - E'| := by ring
  nlinarith [norm_sub_le (regF hH j₀ om.2.1 om.2.2 E - regF hH j₀ om.2.1 om.2.2 E')
    (((E - E' : ℝ) : ℂ) • (1 : PairMatrix p i))]

/-- **The large-`ρ` data at a pole** (the hypotheses `hM'h`,
`hM'`, `hw`, `hdec`, `hUU`, `hUw`, `hcompl` of the large-`ρ` window transfer and of the class (b)
compression step): at a nonpole energy `E` of the pole interval (`PoleSeparated ε hH j₀ E`,
`ε > 0`) with Hermitian `H_R`, `V`, there are `M'`, `w`, `ρ`, `U` with `M' = F_reg(E) - E`
Hermitian, `‖M'‖ ≤ ‖V‖ + ‖C‖²/ε + |E|`, `w` unit, `ρ = -‖C*φ‖²/(μ - E)`,
`schurK0 ω E = M' + ρww*`, and `U : ℂ^{2W-1} → ℂ^{pair}` with `U*U = 1`, `U*w = 0`,
`UU* + ww* = 1`. -/
theorem schurK0_largeRho_data {ε : ℝ} (hε : 0 < ε) (om : SplitState p i)
    (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian) (j₀ : ExteriorSite p i) {E : ℝ}
    (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0) (hsep : PoleSeparated ε hH j₀ E) :
    ∃ (M' : PairMatrix p i) (w : PairSite p i → ℂ) (ρ : ℝ)
      (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ),
      M'.IsHermitian ∧ ‖M'‖ ≤ ‖om.2.2‖ + ‖om.2.1‖ ^ 2 / ε + |E| ∧ sqNorm w = 1 ∧
      ρ = poleRho hH j₀ om.2.1 E ∧
      schurK0 p i om E = M' + (ρ : ℂ) • vecMulVec w (star w) ∧
      Uᴴ * U = 1 ∧ Uᴴ *ᵥ w = 0 ∧ U * Uᴴ + vecMulVec w (star w) = 1 := by
  obtain ⟨U, hUU, hUw, hcompl⟩ := exists_pairIsometry_compl (sqNorm_poleDir hH j₀ om.2.1)
  exact ⟨_, _, _, U, isHermitian_regK om hH hV j₀ E, opNorm_regK_le hε om hH j₀ hsep,
    sqNorm_poleDir hH j₀ om.2.1, rfl, schurK0_pole_decomp om hH j₀ hdet, hUU, hUw, hcompl⟩

/-- **The root rectangle of the regular family, uniformly in `ρ`**: with the
constants of `pairRootRectangle_rankOne_family`, on the pole interval of a grid energy `e`
(`PoleSeparated ε hH j₀ e`) with `certErrHat ε p i ω e ≤ ε_c`, for every real `ρ` the deformation
`F_reg(e) + ρww* - e` has `PairRootRectangle · s' 0 r v₀` for every `s' ∈ [s - s₀, s]`. -/
theorem pairRootRectangle_regF_family (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ (hH : om.1.IsHermitian) (j₀ : ExteriorSite p i), PoleSeparated ε hH j₀ e →
        ∀ (ρ : ℝ) (s' : ℝ), splitS p - s₀ ≤ s' → s' ≤ splitS p →
          PairRootRectangle (regF hH j₀ om.2.1 om.2.2 e +
            (ρ : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
              (e : ℂ) • (1 : PairMatrix p i)) s' 0 r v₀ := by
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, h⟩ :=
    pairRootRectangle_rankOne_family b κ hb hb' hκ
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert hW hH j₀ hsep ρ s'
    hs1 hs2 => ?_⟩
  have heq : regF hH j₀ om.2.1 om.2.2 e +
      (ρ : ℂ) • vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) =
      truncF ε om.1 om.2.1 om.2.2 e +
        ((ρ - poleRhoHat ε hH j₀ om.2.1 e : ℝ) : ℂ) •
          vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) := by
    rw [truncF_pole_decomp ε hH j₀ om.2.1 om.2.2 hsep, Complex.ofReal_sub, sub_smul]
    abel
  rw [heq]
  exact h p hpb i om hV ε e he hcert hW _ _ s' hs1 hs2

/-- **The root rectangle of the exact deformation at a pole**: with the same constants, at a
nonpole grid energy `e` of the pole interval, `PairRootRectangle (schurK0 ω e) s' 0 r v₀`. -/
theorem pairRootRectangle_schurK0_pole (b κ : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (hκ : 0 < κ) :
    ∃ εc r s₀ v₀ : ℝ, 0 < εc ∧ 0 < r ∧ 0 < s₀ ∧ 0 < v₀ ∧
      ∀ p : Parameters, p.b = b → ∀ (i : ZMod p.n) (om : SplitState p i)
        (_hV : om.2.2.IsHermitian) (ε e : ℝ), e ∈ bulkInterval κ → certErrHat ε p i om e ≤ εc →
        2 / ((p.W : ℝ) * splitS p * Real.sqrt κ) ≤ εc →
        ∀ (hH : om.1.IsHermitian) (j₀ : ExteriorSite p i), PoleSeparated ε hH j₀ e →
        (om.1 - (e : ℂ) • 1).det ≠ 0 →
        ∀ s' : ℝ, splitS p - s₀ ≤ s' → s' ≤ splitS p →
          PairRootRectangle (schurK0 p i om e) s' 0 r v₀ := by
  obtain ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, h⟩ :=
    pairRootRectangle_regF_family b κ hb hb' hκ
  refine ⟨εc, r, s₀, v₀, hεc, hr, hs₀, hv₀, fun p hpb i om hV ε e he hcert hW hH j₀ hsep hdet s'
    hs1 hs2 => ?_⟩
  have heq : schurK0 p i om e = regF hH j₀ om.2.1 om.2.2 e +
      ((poleRho hH j₀ om.2.1 e : ℝ) : ℂ) •
        vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) -
          (e : ℂ) • (1 : PairMatrix p i) := by
    rw [schurK0, physicalCoareaF_pole_decomp hH j₀ om.2.1 om.2.2 hdet]
  rw [heq]
  exact h p hpb i om hV ε e he hcert hW hH j₀ hsep _ s' hs1 hs2

end Pair

end BlockBand.LocalWindow.ProofPartTwo
