module

public import BlockBand.LocalWindow.ProofPartTwoRankOne
public import BlockBand.LocalWindow.ProofPartTwoLargeRho
public import BlockBand.LocalWindow.ProofTruncationBounds

/-!
# The pole decomposition of the Schur deformation

Near a single exterior eigenvalue `μ = λ_{j₀}`, the Schur deformation splits as a regular part
plus a rank-one pole part, `F(E) = F_reg(E) + ρ(E) ww*`.

Generic finite index types (`α` exterior, `β` pair); `H_R` Hermitian with Mathlib's spectral
data `hH.eigenvalues`, `hH.eigenvectorUnitary`; a distinguished index `j₀` (the pole
`μ = λ_{j₀}`, eigenvector `φ = U e_{j₀}`).

## Main results

* `PoleSeparated ε hH j₀ E`: every exterior eigenvalue other than `μ` is at distance `> ε` from
  `E` (the pole interval). `poleSeparated_iff_nearSet_subset`, **`exists_poleSeparated`**: off
  the crowding event (`(nearSet ε hH E).card ≤ 1`) such a `j₀` exists.
* `regResolvent` (`(H_R - E)⁻¹` on `φ^⊥`), **`regF`** (`F_reg(E) = V - C* (H_R - E)⁻¹_{⊥φ} C`),
  `poleCoupling` (`c = C*φ`), **`poleRho`** (`ρ(E) = -‖c‖²/(μ - E)`), `poleRhoHat`
  (`-‖c‖² g_ε(μ - E)`, the truncated parameter), **`poleDir`** (`w = c/‖c‖`; a fixed unit vector
  when `c = 0`, where `ρ = 0`).
* **`physicalCoareaF_pole_decomp`**: at a nonpole energy, `F(E) = F_reg(E) + ρ(E) ww*`.
* **`truncF_pole_decomp`**: on the pole interval, `F̂(E) = F_reg(E) + ρ̂(E) ww*`; hence
  **`physicalCoareaF_eq_truncF_add`** (`F = F̂ + (ρ - ρ̂) ww*`) and
  **`regF_add_rankOne_sub_truncF`** (`F_reg + ρww* - F̂ = ((ρ - ρ̂)w) w*` for every real `ρ`).
* **`opNorm_regF_le`** (`‖F_reg(E)‖ ≤ ‖V‖ + ‖C‖²/ε`), **`opNorm_regF_sub_le`**
  (`‖F_reg(E) - F_reg(E')‖ ≤ ‖C‖²|E - E'|/ε²` when both energies are in the pole interval),
  `isHermitian_regF`, `sqNorm_poleDir`.
* `measurable_poleRho`, `continuousOn_poleRho`: `E ↦ ρ(E)` (fixed exterior data).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Finset
open BlockBand.Coarea BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.LocalWindow.ProofETH BlockBand.DeterminantScore.MinorTailInverse
open scoped Matrix.Norms.L2Operator ComplexConjugate

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

/-!
## The pole interval
-/

section Separated

variable {α : Type} [Fintype α] [DecidableEq α] {H : Matrix α α ℂ}

/-- **The pole interval**: every exterior eigenvalue other
than the `j₀`-th lies at distance `> ε` from `E`. -/
def PoleSeparated (ε : ℝ) (hH : H.IsHermitian) (j₀ : α) (E : ℝ) : Prop :=
  ∀ j, j ≠ j₀ → ε < |hH.eigenvalues j - E|

theorem poleSeparated_iff_nearSet_subset (ε : ℝ) (hH : H.IsHermitian) (j₀ : α) (E : ℝ) :
    PoleSeparated ε hH j₀ E ↔ nearSet ε hH E ⊆ {j₀} := by
  constructor
  · intro h j hj
    have hj' : |hH.eigenvalues j - E| ≤ ε := by simpa [nearSet] using hj
    by_contra hne
    exact absurd hj' (not_le.mpr (h j (by simpa using hne)))
  · intro h j hj
    by_contra hle
    have hmem : j ∈ nearSet ε hH E := by simp [nearSet, not_lt.mp hle]
    exact hj (by simpa using h hmem)

/-- **A single pole off the crowding event**: if at most one exterior eigenvalue lies within `ε`
of `E`, some index `j₀` has all other eigenvalues at distance `> ε`. -/
theorem exists_poleSeparated [Nonempty α] {ε : ℝ} (hH : H.IsHermitian) {E : ℝ}
    (hnear : (nearSet ε hH E).card ≤ 1) : ∃ j₀, PoleSeparated ε hH j₀ E := by
  rcases (nearSet ε hH E).eq_empty_or_nonempty with he | ⟨j₀, hj₀⟩
  · refine ⟨Classical.arbitrary α, (poleSeparated_iff_nearSet_subset ε hH _ E).mpr ?_⟩
    rw [he]; exact Finset.empty_subset _
  · refine ⟨j₀, (poleSeparated_iff_nearSet_subset ε hH _ E).mpr fun j hj => ?_⟩
    rw [Finset.mem_singleton]
    exact Finset.card_le_one.mp hnear j hj j₀ hj₀

end Separated

/-!
## The regular part and the rank-one part
-/

section Decomp

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {H : Matrix α α ℂ}

/-- The pole eigenvector `φ = U e_{j₀}` (column `j₀` of the eigenvector unitary). -/
def poleVec (hH : H.IsHermitian) (j₀ : α) : α → ℂ :=
  fun a => (hH.eigenvectorUnitary : Matrix α α ℂ) a j₀

/-- The resolvent restricted to `φ^⊥`: `U diag((λ_j - E)⁻¹ 1_{j ≠ j₀}) U*`. -/
def regResolvent (hH : H.IsHermitian) (j₀ : α) (E : ℝ) : Matrix α α ℂ :=
  (hH.eigenvectorUnitary : Matrix α α ℂ) *
    diagonal (fun j => if j = j₀ then 0 else (((hH.eigenvalues j - E)⁻¹ : ℝ) : ℂ)) *
      star (hH.eigenvectorUnitary : Matrix α α ℂ)

/-- **The regular part** `F_reg(E) = V - C* (H_R - E)⁻¹_{⊥φ} C`. -/
def regF (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) (V : Matrix β β ℂ) (E : ℝ) :
    Matrix β β ℂ :=
  V - Cᴴ * regResolvent hH j₀ E * C

/-- The pole coupling `c = C*φ`. -/
def poleCoupling (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) : β → ℂ :=
  Cᴴ *ᵥ poleVec hH j₀

/-- **The rank-one parameter** `ρ(E) = -‖C*φ‖²/(μ - E)`, `μ = λ_{j₀}`. -/
def poleRho (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) (E : ℝ) : ℝ :=
  -sqNorm (poleCoupling hH j₀ C) * (hH.eigenvalues j₀ - E)⁻¹

/-- The truncated parameter `ρ̂(E) = -‖C*φ‖² g_ε(μ - E)`. -/
def poleRhoHat (ε : ℝ) (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) (E : ℝ) : ℝ :=
  -sqNorm (poleCoupling hH j₀ C) * truncInv ε (hH.eigenvalues j₀ - E)

/-- **The pole direction** `w = C*φ/‖C*φ‖`; a fixed unit vector if `C*φ = 0` (then `ρ = 0`). -/
def poleDir [Nonempty β] (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) : β → ℂ :=
  if poleCoupling hH j₀ C = 0 then Pi.single (Classical.arbitrary β) 1
  else (((vnorm (poleCoupling hH j₀ C))⁻¹ : ℝ) : ℂ) • poleCoupling hH j₀ C

theorem conj_add_conj (U : Matrix.unitaryGroup α ℂ) (d e : α → ℂ) :
    (U : Matrix α α ℂ) * diagonal d * star (U : Matrix α α ℂ) +
        (U : Matrix α α ℂ) * diagonal e * star (U : Matrix α α ℂ) =
      (U : Matrix α α ℂ) * diagonal (d + e) * star (U : Matrix α α ℂ) := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]; rfl

/-- `U diag(x 1_{j₀}) U* = x φφ*`. -/
theorem conj_single_eq (hH : H.IsHermitian) (j₀ : α) (x : ℂ) :
    (hH.eigenvectorUnitary : Matrix α α ℂ) * diagonal (fun j => if j = j₀ then x else 0) *
        star (hH.eigenvectorUnitary : Matrix α α ℂ) =
      x • vecMulVec (poleVec hH j₀) (star (poleVec hH j₀)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.smul_apply, vecMulVec_apply,
    poleVec, Matrix.star_apply, Pi.star_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j₀]
  · rw [Finset.sum_eq_single j₀]
    · simp only [ite_true]; ring
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    · simp
    · intro l _
      by_cases hlk : l = k
      · subst hlk; simp [hk]
      · simp [hlk]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The split of a diagonal symbol into its regular and pole parts. -/
theorem diag_split (hH : H.IsHermitian) (j₀ : α) (E : ℝ) (f : α → ℂ)
    (hf : ∀ j, j ≠ j₀ → f j = (((hH.eigenvalues j - E)⁻¹ : ℝ) : ℂ)) :
    f = (fun j => if j = j₀ then 0 else (((hH.eigenvalues j - E)⁻¹ : ℝ) : ℂ)) +
      (fun j => if j = j₀ then f j₀ else 0) := by
  funext j
  by_cases hj : j = j₀
  · subst hj; simp
  · simp [hj, hf j hj]

/-- `(H - E)⁻¹ = (H - E)⁻¹_{⊥φ} + (μ - E)⁻¹ φφ*` at a nonpole energy. -/
theorem resolvent_eq_regResolvent_add (hH : H.IsHermitian) (j₀ : α) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) :
    physicalCoareaResolvent H E = regResolvent hH j₀ E +
      ((((hH.eigenvalues j₀ - E)⁻¹ : ℝ) : ℂ)) • vecMulVec (poleVec hH j₀) (star (poleVec hH j₀)) := by
  rw [resolvent_eq_conj hH hdet, ← conj_single_eq hH j₀, regResolvent, conj_add_conj]
  congr 3
  exact diag_split hH j₀ E _ fun j _ => rfl

/-- `g_ε(H - E) = (H - E)⁻¹_{⊥φ} + g_ε(μ - E) φφ*` on the pole interval. -/
theorem truncResolvent_eq_regResolvent_add (ε : ℝ) (hH : H.IsHermitian) (j₀ : α) {E : ℝ}
    (hsep : PoleSeparated ε hH j₀ E) :
    truncResolvent ε H E = regResolvent hH j₀ E +
      ((truncInv ε (hH.eigenvalues j₀ - E) : ℝ) : ℂ) •
        vecMulVec (poleVec hH j₀) (star (poleVec hH j₀)) := by
  unfold truncResolvent
  simp only [hH, ↓reduceDIte]
  rw [← conj_single_eq hH j₀, regResolvent, conj_add_conj]
  congr 3
  refine diag_split hH j₀ E _ fun j hj => ?_
  unfold truncInv
  split_ifs with h
  · exact absurd h (not_le.mpr (hsep j hj))
  · rfl

/-- `C* (φφ*) C = c c*`, `c = C*φ`. -/
theorem conjTranspose_mul_vecMulVec_mul (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) :
    Cᴴ * vecMulVec (poleVec hH j₀) (star (poleVec hH j₀)) * C =
      vecMulVec (poleCoupling hH j₀ C) (star (poleCoupling hH j₀ C)) := by
  rw [mul_vecMulVec_mul, poleCoupling, star_mulVec, conjTranspose_conjTranspose]

/-- `F(E) = F_reg(E) - (μ - E)⁻¹ c c*` at a nonpole energy. -/
theorem physicalCoareaF_eq_regF_sub (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ)
    (V : Matrix β β ℂ) {E : ℝ} (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) :
    physicalCoareaF H C V E = regF hH j₀ C V E -
      ((((hH.eigenvalues j₀ - E)⁻¹ : ℝ) : ℂ)) •
        vecMulVec (poleCoupling hH j₀ C) (star (poleCoupling hH j₀ C)) := by
  unfold physicalCoareaF regF
  rw [resolvent_eq_regResolvent_add hH j₀ hdet, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul_vecMulVec_mul]
  abel

/-- `F̂(E) = F_reg(E) - g_ε(μ - E) c c*` on the pole interval. -/
theorem truncF_eq_regF_sub (ε : ℝ) (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ)
    (V : Matrix β β ℂ) {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) :
    truncF ε H C V E = regF hH j₀ C V E -
      ((truncInv ε (hH.eigenvalues j₀ - E) : ℝ) : ℂ) •
        vecMulVec (poleCoupling hH j₀ C) (star (poleCoupling hH j₀ C)) := by
  unfold truncF regF
  rw [truncResolvent_eq_regResolvent_add ε hH j₀ hsep, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul_vecMulVec_mul]
  abel

theorem sqNorm_eq_vnorm_sq (v : β → ℂ) : sqNorm v = vnorm v ^ 2 := (vnorm_sq v).symm

theorem sqNorm_eq_zero_iff (v : β → ℂ) : sqNorm v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖v k‖)).mp h
    funext k
    have := h' k (Finset.mem_univ k)
    simpa using this
  · rintro rfl; simp [sqNorm]

/-- `w` is a unit vector. -/
theorem sqNorm_poleDir [Nonempty β] (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) :
    sqNorm (poleDir hH j₀ C) = 1 := by
  unfold poleDir
  split_ifs with hc
  · unfold sqNorm
    rw [Finset.sum_eq_single (Classical.arbitrary β)]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  · set c := poleCoupling hH j₀ C
    have hpos : 0 < vnorm c := by
      rcases (vnorm_nonneg c).eq_or_lt with h0 | h0
      · exfalso; apply hc
        rw [← sqNorm_eq_zero_iff, sqNorm_eq_vnorm_sq, ← h0]; ring
      · exact h0
    rw [sqNorm_eq_vnorm_sq, vnorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne', one_pow]

/-- `(-‖c‖² t) ww* = -t cc*` for every real `t`. -/
theorem smul_vecMulVec_poleDir [Nonempty β] (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ)
    (t : ℝ) :
    (((-sqNorm (poleCoupling hH j₀ C) * t : ℝ) : ℂ)) •
        vecMulVec (poleDir hH j₀ C) (star (poleDir hH j₀ C)) =
      -(((t : ℝ) : ℂ) • vecMulVec (poleCoupling hH j₀ C) (star (poleCoupling hH j₀ C))) := by
  set c := poleCoupling hH j₀ C with hcdef
  unfold poleDir
  rw [← hcdef]
  split_ifs with hc
  · have : sqNorm c = 0 := (sqNorm_eq_zero_iff c).mpr hc
    rw [this, hc]; simp
  · have hn : sqNorm c ≠ 0 := fun h => hc ((sqNorm_eq_zero_iff c).mp h)
    rw [star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul, ← neg_smul]
    congr 1
    have hv : (vnorm c) ^ 2 = sqNorm c := vnorm_sq c
    have hv0 : vnorm c ≠ 0 := fun h => hn (by rw [← hv, h]; ring)
    rw [show (star ((((vnorm c)⁻¹ : ℝ) : ℂ))) = (((vnorm c)⁻¹ : ℝ) : ℂ) from
      Complex.conj_ofReal _]
    have hv0' : ((vnorm c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv0
    rw [← hv]
    push_cast
    field_simp

/-- **The pole decomposition**: at a nonpole energy
`F(E) = F_reg(E) + ρ(E) ww*`, `ρ(E) = -‖C*φ‖²/(μ - E)`, `w = C*φ/‖C*φ‖` (`ρ = 0` if `C*φ = 0`). -/
theorem physicalCoareaF_pole_decomp [Nonempty β] (hH : H.IsHermitian) (j₀ : α)
    (C : Matrix α β ℂ) (V : Matrix β β ℂ) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) :
    physicalCoareaF H C V E = regF hH j₀ C V E +
      ((poleRho hH j₀ C E : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ C) (star (poleDir hH j₀ C)) := by
  rw [physicalCoareaF_eq_regF_sub hH j₀ C V hdet, poleRho, smul_vecMulVec_poleDir, ← sub_eq_add_neg]

/-- **The truncated deformation in pole form**: on the pole interval
`F̂(E) = F_reg(E) + ρ̂(E) ww*`, `ρ̂(E) = -‖C*φ‖² g_ε(μ - E)`. -/
theorem truncF_pole_decomp [Nonempty β] (ε : ℝ) (hH : H.IsHermitian) (j₀ : α)
    (C : Matrix α β ℂ) (V : Matrix β β ℂ) {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) :
    truncF ε H C V E = regF hH j₀ C V E +
      ((poleRhoHat ε hH j₀ C E : ℝ) : ℂ) •
        vecMulVec (poleDir hH j₀ C) (star (poleDir hH j₀ C)) := by
  rw [truncF_eq_regF_sub ε hH j₀ C V hsep, poleRhoHat, smul_vecMulVec_poleDir, ← sub_eq_add_neg]

/-- **`F = F̂ + (ρ - ρ̂) ww*`** at a nonpole energy of the pole interval. -/
theorem physicalCoareaF_eq_truncF_add [Nonempty β] (ε : ℝ) (hH : H.IsHermitian) (j₀ : α)
    (C : Matrix α β ℂ) (V : Matrix β β ℂ) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) (hsep : PoleSeparated ε hH j₀ E) :
    physicalCoareaF H C V E = truncF ε H C V E +
      ((poleRho hH j₀ C E - poleRhoHat ε hH j₀ C E : ℝ) : ℂ) •
        vecMulVec (poleDir hH j₀ C) (star (poleDir hH j₀ C)) := by
  rw [physicalCoareaF_pole_decomp hH j₀ C V hdet, truncF_pole_decomp ε hH j₀ C V hsep,
    Complex.ofReal_sub, sub_smul]
  abel

/-- **`F_reg + ρww*` is a rank-one change of `F̂`**, for every real `ρ`:
`F_reg(E) + ρww* - F̂(E) = ((ρ - ρ̂(E)) w) w*` on the pole interval. -/
theorem regF_add_rankOne_sub_truncF [Nonempty β] (ε : ℝ) (hH : H.IsHermitian) (j₀ : α)
    (C : Matrix α β ℂ) (V : Matrix β β ℂ) {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) (ρ : ℝ) :
    regF hH j₀ C V E + ((ρ : ℝ) : ℂ) • vecMulVec (poleDir hH j₀ C) (star (poleDir hH j₀ C)) -
        truncF ε H C V E =
      vecMulVec (((ρ - poleRhoHat ε hH j₀ C E : ℝ) : ℂ) • poleDir hH j₀ C)
        (star (poleDir hH j₀ C)) := by
  rw [truncF_pole_decomp ε hH j₀ C V hsep, smul_vecMulVec, Complex.ofReal_sub, sub_smul]
  abel

/-- `(H - E)⁻¹_{⊥φ}` is Hermitian. -/
theorem isHermitian_regResolvent (hH : H.IsHermitian) (j₀ : α) (E : ℝ) :
    (regResolvent hH j₀ E).IsHermitian := by
  unfold regResolvent
  rw [star_eq_conjTranspose]
  refine isHermitian_mul_mul_conjTranspose _ ?_
  refine isHermitian_diagonal_of_self_adjoint _ ?_
  ext j
  by_cases hj : j = j₀ <;> simp [hj]

/-- `F_reg(E)` is Hermitian for Hermitian `V`. -/
theorem isHermitian_regF (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) {V : Matrix β β ℂ}
    (hV : V.IsHermitian) (E : ℝ) : (regF hH j₀ C V E).IsHermitian :=
  hV.sub (isHermitian_conjTranspose_mul_mul C (isHermitian_regResolvent hH j₀ E))

end Decomp

/-!
## Norm and Lipschitz bounds for the regular part
-/

section Bounds

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {H : Matrix α α ℂ}

/-- An `L²` operator norm bound from a pointwise Euclidean bound. -/
theorem opNorm_le_of_toE {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, ‖T A x‖ ≤ c * ‖x‖) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hc h

/-- `‖(H - E)⁻¹_{⊥φ}‖ ≤ ε⁻¹` on the pole interval. -/
theorem opNorm_regResolvent_le {ε : ℝ} (hε : 0 < ε) (hH : H.IsHermitian) (j₀ : α) {E : ℝ}
    (hsep : PoleSeparated ε hH j₀ E) : ‖regResolvent hH j₀ E‖ ≤ ε⁻¹ := by
  refine opNorm_le_of_toE _ (by positivity) fun x => ?_
  refine norm_toE_conj_le _ _ (by positivity) (fun j => ?_) x
  by_cases hj : j = j₀
  · simp [hj]; positivity
  · simp only [hj, ite_false, Complex.norm_real, Real.norm_eq_abs, abs_inv]
    exact inv_anti₀ hε (hsep j hj).le

/-- **`‖F_reg(E)‖ ≤ ‖V‖ + ‖C‖²/ε`** on the pole interval. -/
theorem opNorm_regF_le {ε : ℝ} (hε : 0 < ε) (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ)
    (V : Matrix β β ℂ) {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) :
    ‖regF hH j₀ C V E‖ ≤ ‖V‖ + ‖C‖ ^ 2 / ε := by
  unfold regF
  have hR := opNorm_regResolvent_le hε hH j₀ hsep
  have h2 : ‖Cᴴ * regResolvent hH j₀ E * C‖ ≤ ‖C‖ * ε⁻¹ * ‖C‖ := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)
  have h3 : ‖C‖ * ε⁻¹ * ‖C‖ = ‖C‖ ^ 2 / ε := by ring
  linarith [norm_sub_le V (Cᴴ * regResolvent hH j₀ E * C)]

/-- **`F_reg` is `ε⁻²`-Lipschitz on the pole interval**:
`‖F_reg(E) - F_reg(E')‖ ≤ ‖C‖² |E - E'|/ε²`. -/
theorem opNorm_regF_sub_le {ε : ℝ} (hε : 0 < ε) (hH : H.IsHermitian) (j₀ : α)
    (C : Matrix α β ℂ) (V : Matrix β β ℂ) {E E' : ℝ} (hsep : PoleSeparated ε hH j₀ E)
    (hsep' : PoleSeparated ε hH j₀ E') :
    ‖regF hH j₀ C V E - regF hH j₀ C V E'‖ ≤ ‖C‖ ^ 2 * (|E - E'| / ε ^ 2) := by
  have hd : regF hH j₀ C V E - regF hH j₀ C V E' =
      Cᴴ * (regResolvent hH j₀ E' - regResolvent hH j₀ E) * C := by
    unfold regF; rw [Matrix.mul_sub, Matrix.sub_mul]; abel
  have hR : ‖regResolvent hH j₀ E' - regResolvent hH j₀ E‖ ≤ |E - E'| / ε ^ 2 := by
    unfold regResolvent
    rw [conj_sub_conj]
    refine opNorm_le_of_toE _ (by positivity) fun x => ?_
    refine norm_toE_conj_le _ _ (by positivity) (fun j => ?_) x
    by_cases hj : j = j₀
    · simp [hj]; positivity
    · simp only [Pi.sub_apply, hj, ite_false]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have := abs_inv_sub_inv_le hε (hsep' j hj).le (hsep j hj).le
      rwa [show hH.eigenvalues j - E' - (hH.eigenvalues j - E) = E - E' by ring] at this
  rw [hd]
  calc ‖Cᴴ * (regResolvent hH j₀ E' - regResolvent hH j₀ E) * C‖
      ≤ ‖C‖ * (|E - E'| / ε ^ 2) * ‖C‖ := by
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = ‖C‖ ^ 2 * (|E - E'| / ε ^ 2) := by ring

end Bounds

/-!
## Measurability of the rank-one parameter in the energy
-/

section Measurable

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {H : Matrix α α ℂ}

/-- For fixed exterior data, `E ↦ ρ(E)` is measurable (Lean's `0⁻¹ = 0` at the pole). -/
theorem measurable_poleRho (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) :
    Measurable (poleRho hH j₀ C) := by
  unfold poleRho
  exact measurable_const.mul (measurable_const.sub measurable_id).inv

/-- For fixed exterior data, `E ↦ ρ(E)` is continuous off the pole `μ`. -/
theorem continuousOn_poleRho (hH : H.IsHermitian) (j₀ : α) (C : Matrix α β ℂ) :
    ContinuousOn (poleRho hH j₀ C) {E | E ≠ hH.eigenvalues j₀} := by
  unfold poleRho
  refine continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id) ?_)
  intro E hE
  exact sub_ne_zero.mpr (Ne.symm hE)

end Measurable

end BlockBand.LocalWindow.ProofPartTwo
