module

public import BlockBand.LocalWindow.ProofPartTwoPole
public import BlockBand.LocalWindow.ProofPartOneMeasurable
public import BlockBand.DeterminantScore.Sector.Inertia

/-!
# Basis-free, measurable pole data

`PartTwoConditionalStatement` needs a measurable bad set; the pole data
(`regF`, `poleDir`, `poleRho`) are built from Mathlib's `eigenvectorUnitary` (a choice) and are
not known to be measurable in the exterior. On the label event "the `j₀`-th exterior eigenvalue is
simple" (`PoleSimple`; it holds on the pole interval as soon as the pole is within `ε` of `E`,
`poleSimple_of_poleSeparated`) everything they enter is a **basis-free polynomial** in
`(H_R, C, V)` and the (continuous) ordered eigenvalues.

## Main results

* `herEig` (total eigenvalue), **`measurable_herEig`**.
* `polePoly`, **`poleProj`** `= (∏_{j≠j₀}(μ - λ_j))⁻¹ ∏_{j≠j₀}(H - λ_j)` (an ordered list product
  of commuting factors), **`measurable_poleProj_comp`**, **`poleProj_eq`**: on `PoleSimple`,
  `poleProj = φφ*` (`φ = poleVec`).
* **`poleQ`** `= C* poleProj C`, **`poleQ_eq`** (`= cc*`, `c = C*φ`), `measurable_poleQ`.
* **`regFm`** `= F̂(e) + g_ε(μ - e) poleQ`, **`regF_eq_regFm`** (on `PoleSimple` and the pole
  interval of `e`), **`measurable_regFm`**.
* **`poleWW`** (the projector `ww*` in basis-free form), **`poleWW_eq`**, `measurable_poleWW`.
* **`poleRhoM`** `= -Re Tr(poleQ)/(μ - E)`, **`poleRhoM_eq`**, `measurable_poleRhoM`.
* `measurableSet_poleSimple`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open Matrix Finset MeasureTheory
open BlockBand.Coarea BlockBand.LocalWindow.ProofCount BlockBand.LocalWindow.ProofCertificate
open BlockBand.LocalWindow.ProofETH
open scoped Matrix.Norms.L2Operator ComplexConjugate

/-!
## Measurable eigenvalues
-/

section Eig

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The `j`-th Mathlib eigenvalue of a Hermitian matrix, `0` off the Hermitian set. -/
def herEig (H : Matrix α α ℂ) (j : α) : ℝ :=
  if hH : H.IsHermitian then hH.eigenvalues j else 0

theorem herEig_eq {H : Matrix α α ℂ} (hH : H.IsHermitian) (j : α) :
    herEig H j = hH.eigenvalues j := by
  rw [herEig, dite_eq_left_of_eq_true (eq_true hH)]

theorem measurableSet_isHermitian' : MeasurableSet {H : Matrix α α ℂ | H.IsHermitian} :=
  (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet

/-- **The eigenvalues are Borel measurable** (continuous on the closed Hermitian set,
`Sector.continuous_eigenvalues_comp`). -/
theorem measurable_herEig (j : α) : Measurable (fun H : Matrix α α ℂ => herEig H j) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_isHermitian' ?_ ?_
  · have hc : Continuous fun H : {H : Matrix α α ℂ // H.IsHermitian} =>
        H.2.eigenvalues j :=
      BlockBand.DeterminantScore.Sector.continuous_eigenvalues_comp
        (fun H : {H : Matrix α α ℂ // H.IsHermitian} => H.1) continuous_subtype_val
        (fun H : {H : Matrix α α ℂ // H.IsHermitian} => H.2) j
    have e : (fun H : {H : Matrix α α ℂ // H.IsHermitian} => H.2.eigenvalues j) =
        ({H : Matrix α α ℂ | H.IsHermitian}.domRestrict fun H => herEig H j) :=
      funext fun H => (herEig_eq H.2 j).symm
    rw [e] at hc
    exact hc.measurable
  · have : (({H : Matrix α α ℂ | H.IsHermitian}ᶜ).domRestrict fun H => herEig H j) =
        fun _ => 0 := by
      funext H
      exact dite_eq_right_of_eq_false (eq_false H.2)
    rw [this]
    exact measurable_const

/-- **The pole label is simple**: the `j₀`-th eigenvalue has multiplicity one. -/
def PoleSimple {H : Matrix α α ℂ} (hH : H.IsHermitian) (j₀ : α) : Prop :=
  ∀ j, j ≠ j₀ → hH.eigenvalues j ≠ hH.eigenvalues j₀

/-- On the pole interval, a pole within `ε` of `E` is simple. -/
theorem poleSimple_of_poleSeparated {ε : ℝ} {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α}
    {E : ℝ} (hsep : PoleSeparated ε hH j₀ E) (hnear : |hH.eigenvalues j₀ - E| ≤ ε) :
    PoleSimple hH j₀ := by
  intro j hj he
  have := hsep j hj
  rw [he] at this
  linarith

/-- The label event `{H Hermitian, j₀ simple}` is measurable. -/
theorem measurableSet_poleSimple (j₀ : α) :
    MeasurableSet {H : Matrix α α ℂ | ∃ hH : H.IsHermitian, PoleSimple hH j₀} := by
  have e : {H : Matrix α α ℂ | ∃ hH : H.IsHermitian, PoleSimple hH j₀} =
      {H | H.IsHermitian} ∩ ⋂ j ∈ (univ.erase j₀ : Finset α), {H | herEig H j ≠ herEig H j₀} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hH, h⟩
      refine ⟨hH, fun j hj => ?_⟩
      rw [herEig_eq hH, herEig_eq hH]
      exact h j hj
    · rintro ⟨hH, h⟩
      refine ⟨hH, fun j hj => ?_⟩
      have := h j hj
      rwa [herEig_eq hH, herEig_eq hH] at this
  rw [e]
  refine measurableSet_isHermitian'.inter (MeasurableSet.biInter (Set.to_countable _) fun j _ => ?_)
  exact (measurableSet_eq_fun (measurable_herEig j) (measurable_herEig j₀)).compl

end Eig

/-!
## The basis-free pole projector
-/

section Proj

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Entrywise measurability of `c(x) • M(x)`. -/
theorem measurable_smul_matrix {X : Type*} [MeasurableSpace X] {γ δ : Type} {c : X → ℂ}
    {M : X → Matrix γ δ ℂ} (hc : Measurable c) (hM : Measurable M) :
    Measurable fun x => c x • M x := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hc.mul ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hM))

/-- `π(x) = ∏_{j ≠ j₀} (x - λ_j)`. -/
def polePoly (lam : α → ℝ) (j₀ : α) (x : ℝ) : ℝ := ∏ j ∈ univ.erase j₀, (x - lam j)

/-- The ordered product `∏_{j ∈ l} (H - λ_j)` (the factors commute). -/
def poleProdList (H : Matrix α α ℂ) (lam : α → ℝ) (l : List α) : Matrix α α ℂ :=
  (l.map fun j => H - ((lam j : ℝ) : ℂ) • (1 : Matrix α α ℂ)).prod

/-- **The basis-free pole projector** `P = π(μ)⁻¹ ∏_{j ≠ j₀} (H - λ_j)`, `μ = λ_{j₀}`. -/
def poleProj (j₀ : α) (H : Matrix α α ℂ) : Matrix α α ℂ :=
  (((polePoly (herEig H) j₀ (herEig H j₀))⁻¹ : ℝ) : ℂ) •
    poleProdList H (herEig H) (univ.erase j₀).toList

theorem measurable_poleProdList {X : Type*} [MeasurableSpace X] {H : X → Matrix α α ℂ}
    {lam : X → α → ℝ} (hH : Measurable H) (hlam : ∀ j, Measurable fun x => lam x j)
    (l : List α) : Measurable fun x => poleProdList (H x) (lam x) l := by
  induction l with
  | nil =>
    simp only [poleProdList, List.map_nil, List.prod_nil]
    exact measurable_const
  | cons j l ih =>
    simp only [poleProdList, List.map_cons, List.prod_cons] at ih ⊢
    refine measurable_matrix_mul' ?_ ih
    have hc : Continuous fun q : Matrix α α ℂ × ℝ => q.1 - ((q.2 : ℝ) : ℂ) • (1 : Matrix α α ℂ) :=
      continuous_fst.sub ((Complex.continuous_ofReal.comp continuous_snd).smul continuous_const)
    exact hc.measurable.comp (hH.prodMk (hlam j))

theorem measurable_polePoly {X : Type*} [MeasurableSpace X] {lam : X → α → ℝ} {y : X → ℝ}
    (hlam : ∀ j, Measurable fun x => lam x j) (hy : Measurable y) (j₀ : α) :
    Measurable fun x => polePoly (lam x) j₀ (y x) := by
  unfold polePoly
  exact Finset.measurable_prod _ fun j _ => hy.sub (hlam j)

/-- **The pole projector along measurable data is measurable.** -/
theorem measurable_poleProj_comp {X : Type*} [MeasurableSpace X] {H : X → Matrix α α ℂ}
    (hH : Measurable H) (j₀ : α) : Measurable fun x => poleProj j₀ (H x) := by
  have hlam : ∀ j, Measurable fun x => herEig (H x) j := fun j => (measurable_herEig j).comp hH
  unfold poleProj
  refine measurable_smul_matrix ?_ (measurable_poleProdList hH hlam _)
  exact Complex.measurable_ofReal.comp (measurable_polePoly hlam (hlam j₀) j₀).inv

theorem measurable_poleProj (j₀ : α) : Measurable (poleProj (α := α) j₀) :=
  measurable_poleProj_comp measurable_id j₀

/-- `∏_{j ∈ l} (H - λ_j) = U diag(∏_{j ∈ l} (λ_k - λ_j)) U*`. -/
theorem poleProdList_eq_conj {H : Matrix α α ℂ} (hH : H.IsHermitian) (l : List α) :
    poleProdList H hH.eigenvalues l =
      (hH.eigenvectorUnitary : Matrix α α ℂ) *
        diagonal (fun k => (((l.map fun j => hH.eigenvalues k - hH.eigenvalues j).prod : ℝ) : ℂ)) *
          star (hH.eigenvectorUnitary : Matrix α α ℂ) := by
  induction l with
  | nil =>
    simp only [poleProdList, List.map_nil, List.prod_nil, Complex.ofReal_one]
    rw [diagonal_one, Matrix.mul_one]
    exact (Unitary.coe_mul_star_self _).symm
  | cons j l ih =>
    simp only [poleProdList, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, sub_eq_conj hH, conj_mul_conj]
    refine congrArg (fun d => (hH.eigenvectorUnitary : Matrix α α ℂ) * diagonal d *
      star (hH.eigenvectorUnitary : Matrix α α ℂ)) (funext fun k => ?_)
    simp only [Pi.mul_apply, Complex.ofReal_mul]

theorem list_prod_eq_polePoly (lam : α → ℝ) (j₀ : α) (x : ℝ) :
    ((univ.erase j₀).toList.map fun j => x - lam j).prod = polePoly lam j₀ x := by
  rw [polePoly, Finset.prod_map_toList]

theorem polePoly_ne_zero {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α}
    (hs : PoleSimple hH j₀) : polePoly hH.eigenvalues j₀ (hH.eigenvalues j₀) ≠ 0 := by
  unfold polePoly
  refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr ?_
  exact Ne.symm (hs j (Finset.ne_of_mem_erase hj))

theorem polePoly_eigen_eq_zero {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ k : α}
    (hk : k ≠ j₀) : polePoly hH.eigenvalues j₀ (hH.eigenvalues k) = 0 := by
  unfold polePoly
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)

/-- **The pole projector is `φφ*` at a simple pole** (`φ = poleVec`). -/
theorem poleProj_eq {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α} (hs : PoleSimple hH j₀) :
    poleProj j₀ H = vecMulVec (poleVec hH j₀) (star (poleVec hH j₀)) := by
  have hlam : herEig H = hH.eigenvalues := funext (herEig_eq hH)
  unfold poleProj
  rw [hlam, poleProdList_eq_conj hH, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul]
  rw [← one_smul ℂ (vecMulVec (poleVec hH j₀) (star (poleVec hH j₀))), ← conj_single_eq hH j₀]
  refine congrArg (fun d => (hH.eigenvectorUnitary : Matrix α α ℂ) * diagonal d *
    star (hH.eigenvectorUnitary : Matrix α α ℂ)) (funext fun k => ?_)
  simp only [Pi.smul_apply]
  rw [list_prod_eq_polePoly]
  by_cases hk : k = j₀
  · subst hk
    simp only [ite_true, smul_eq_mul]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (polePoly_ne_zero hH hs), Complex.ofReal_one]
  · simp only [hk, ite_false, smul_eq_mul, polePoly_eigen_eq_zero hH hk, Complex.ofReal_zero,
      mul_zero]

end Proj

/-!
## The coupled projector, the regular part, the direction and the parameter
-/

section Coupled

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `Q = C* P C` (`= cc*`, `c = C*φ`, at a simple pole). -/
def poleQ (j₀ : α) (H : Matrix α α ℂ) (C : Matrix α β ℂ) : Matrix β β ℂ :=
  Cᴴ * poleProj j₀ H * C

theorem poleQ_eq {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α} (hs : PoleSimple hH j₀)
    (C : Matrix α β ℂ) :
    poleQ j₀ H C = vecMulVec (poleCoupling hH j₀ C) (star (poleCoupling hH j₀ C)) := by
  rw [poleQ, poleProj_eq hH hs, conjTranspose_mul_vecMulVec_mul]

theorem measurable_conjTranspose' {X : Type*} [MeasurableSpace X] {γ δ : Type}
    {C : X → Matrix γ δ ℂ} (hC : Measurable C) : Measurable fun x => (C x)ᴴ := by
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
  simp only [conjTranspose_apply]
  exact Complex.continuous_conj.measurable.comp
    ((measurable_pi_apply a).comp ((measurable_pi_apply b).comp hC))

/-- `(H_R, C) ↦ C* P C` is measurable. -/
theorem measurable_poleQ (j₀ : α) :
    Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ => poleQ j₀ om.1 om.2.1 := by
  have hC : Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ => om.2.1 :=
    measurable_fst.comp measurable_snd
  unfold poleQ
  exact measurable_matrix_mul' (measurable_matrix_mul' (measurable_conjTranspose' hC)
    (measurable_poleProj_comp measurable_fst j₀)) hC

/-- **The regular part in basis-free form** `F̂(e) + g_ε(μ - e) C* P C`. -/
def regFm (ε : ℝ) (j₀ : α) (H : Matrix α α ℂ) (C : Matrix α β ℂ) (V : Matrix β β ℂ) (e : ℝ) :
    Matrix β β ℂ :=
  truncF ε H C V e + ((truncInv ε (herEig H j₀ - e) : ℝ) : ℂ) • poleQ j₀ H C

/-- **`F_reg(e) = regFm`** at a simple pole, on the pole interval of `e`. -/
theorem regF_eq_regFm (ε : ℝ) {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α}
    (hs : PoleSimple hH j₀) (C : Matrix α β ℂ) (V : Matrix β β ℂ) {e : ℝ}
    (hsep : PoleSeparated ε hH j₀ e) : regF hH j₀ C V e = regFm ε j₀ H C V e := by
  rw [regFm, truncF_eq_regF_sub ε hH j₀ C V hsep, poleQ_eq hH hs, herEig_eq hH]
  abel

/-- **`(H_R, C, V) ↦ regFm` is measurable** (`ε > 0`, fixed `e`). -/
theorem measurable_regFm {ε : ℝ} (hε : 0 < ε) (j₀ : α) (e : ℝ) :
    Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ =>
      regFm ε j₀ om.1 om.2.1 om.2.2 e := by
  unfold regFm
  refine (measurable_truncF hε e).add (measurable_smul_matrix ?_ (measurable_poleQ j₀))
  exact Complex.measurable_ofReal.comp ((continuous_truncInv hε).measurable.comp
    (((measurable_herEig j₀).comp measurable_fst).sub measurable_const))

theorem trace_vecMulVec_star (c : β → ℂ) :
    (vecMulVec c (star c)).trace = ((sqNorm c : ℝ) : ℂ) := by
  rw [trace_vecMulVec, dotProduct_comm, star_dotProduct_self]

/-- **The direction projector `ww*` in basis-free form**: `Q / Tr Q`, and the projector on the
fixed default vector when `Q = 0` (the convention of `poleDir`). -/
def poleWW [Nonempty β] (j₀ : α) (H : Matrix α α ℂ) (C : Matrix α β ℂ) : Matrix β β ℂ :=
  if (poleQ j₀ H C).trace = 0 then
    vecMulVec (Pi.single (Classical.arbitrary β) 1) (star (Pi.single (Classical.arbitrary β) 1))
  else ((poleQ j₀ H C).trace)⁻¹ • poleQ j₀ H C

theorem poleWW_eq [Nonempty β] {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α}
    (hs : PoleSimple hH j₀) (C : Matrix α β ℂ) :
    poleWW j₀ H C = vecMulVec (poleDir hH j₀ C) (star (poleDir hH j₀ C)) := by
  set c := poleCoupling hH j₀ C with hcdef
  have hQ := poleQ_eq hH hs C
  have htr : (poleQ j₀ H C).trace = ((sqNorm c : ℝ) : ℂ) := by
    rw [hQ, trace_vecMulVec_star]
  unfold poleWW
  rw [htr]
  by_cases hc : c = 0
  · have h0 : sqNorm c = 0 := (sqNorm_eq_zero_iff c).mpr hc
    have h0' : ((sqNorm c : ℝ) : ℂ) = 0 := by rw [h0, Complex.ofReal_zero]
    simp only [h0', ↓reduceIte]
    unfold poleDir
    rw [← hcdef]
    simp only [hc, ↓reduceIte]
  · have hn : sqNorm c ≠ 0 := fun h => hc ((sqNorm_eq_zero_iff c).mp h)
    have hn' : ((sqNorm c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [hn', ↓reduceIte]
    have h := smul_vecMulVec_poleDir hH j₀ C (-(sqNorm c)⁻¹)
    rw [← hcdef] at h
    rw [show -sqNorm c * -(sqNorm c)⁻¹ = 1 by field_simp, Complex.ofReal_one, one_smul] at h
    rw [h, hQ, Complex.ofReal_neg, neg_smul, neg_neg, Complex.ofReal_inv]

theorem measurable_poleWW [Nonempty β] (j₀ : α) :
    Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ => poleWW j₀ om.1 om.2.1 := by
  have hQ := measurable_poleQ (β := β) j₀
  have htr : Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ =>
      (poleQ j₀ om.1 om.2.1).trace := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.measurable_sum _ fun a _ => (measurable_pi_apply a).comp
      ((measurable_pi_apply a).comp hQ)
  unfold poleWW
  exact Measurable.ite (measurableSet_eq_fun htr measurable_const) measurable_const
    (measurable_smul_matrix htr.inv hQ)

/-- **The rank-one parameter in basis-free form** `ρ(E) = -Re Tr(Q)/(μ - E)`. -/
def poleRhoM (j₀ : α) (H : Matrix α α ℂ) (C : Matrix α β ℂ) (E : ℝ) : ℝ :=
  -(poleQ j₀ H C).trace.re * (herEig H j₀ - E)⁻¹

theorem poleRhoM_eq {H : Matrix α α ℂ} (hH : H.IsHermitian) {j₀ : α} (hs : PoleSimple hH j₀)
    (C : Matrix α β ℂ) (E : ℝ) : poleRhoM j₀ H C E = poleRho hH j₀ C E := by
  rw [poleRhoM, poleRho, poleQ_eq hH hs, trace_vecMulVec_star, Complex.ofReal_re, herEig_eq hH]

theorem measurable_poleRhoM (j₀ : α) (E : ℝ) :
    Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ =>
      poleRhoM j₀ om.1 om.2.1 E := by
  have hQ := measurable_poleQ (β := β) j₀
  have htr : Measurable fun om : Matrix α α ℂ × Matrix α β ℂ × Matrix β β ℂ =>
      (poleQ j₀ om.1 om.2.1).trace := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.measurable_sum _ fun a _ => (measurable_pi_apply a).comp
      ((measurable_pi_apply a).comp hQ)
  unfold poleRhoM
  exact (Complex.measurable_re.comp htr).neg.mul
    (((measurable_herEig j₀).comp measurable_fst).sub measurable_const).inv

end Coupled

end BlockBand.LocalWindow.ProofPartTwo
