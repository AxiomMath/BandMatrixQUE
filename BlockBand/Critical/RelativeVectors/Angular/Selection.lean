module

public import BlockBand.Critical.RelativeVectors.StochasticStatements
public import BlockBand.Internal.Contracts.TransmissionAngular
public import BlockBand.Palm.MomentFlow.BridgeRelabel
public import BlockBand.Palm.FreshPalmShift

/-!
# Eigenvector selection, frame scaling and eigenvalue σ-algebras

Pointwise identities relating `TransmissionAngular.ComplexAngularMartingaleProblem` to
`ComplexAngularMartingaleStatement`; no measure is involved.

* `isEigenSelection_revSelection`: `revSelection N H i = freshEigenvector H i.rev` is an
  `IsEigenSelection`: on simple spectrum the Lagrange product at the nonincreasing label `i` is
  `u u^*` for the selected unit eigenvector of increasing rank `i.rev`.
* `frameArray_eq_relabel`: the array `z_ℓ = √N V^* u_ℓ` is `angularArray (√N V)` of that selection
  with labels reversed (`relabelArray`).
* `measurable_dysonEigenvalue`; `eigenPathSigma_le_contract`: the increasing-rank eigenvalue path
  σ-algebra is contained in the nonincreasing-label one; `contractPathSigma_le_shift`: the path
  σ-algebra from `s` is contained in `𝓖_{s+w} ⊔` the path σ-algebra from `s + w`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.Foundations.Spectral BlockBand.Model.Construction BlockBand.Palm.MomentFlow
open scoped NNReal ComplexConjugate

variable {N r : ℕ}

/-!
## The selection
-/

/-- The eigenvector selection `ev H i = u_{i.rev}(H)` (nonincreasing label `i`, increasing rank
`i.rev`). -/
def revSelection (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : Fin N → ℂ :=
  freshEigenvector H i.rev

/-- On simple spectrum the Lagrange product at label `ℓ.rev` is the outer product of the
canonical increasing eigenvector of rank `ℓ`. -/
theorem dysonProjection_rev_eq_outer {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (hs : HasSimpleSpectrum N K) (ℓ : Fin N) :
    dysonProjection N K ℓ.rev =
      fun x y => increasingEigenvector hK (Fin.cast (Fintype.card_fin N).symm ℓ) x *
        conj (increasingEigenvector hK (Fin.cast (Fintype.card_fin N).symm ℓ) y) := by
  set m := Fin.cast (Fintype.card_fin N).symm ℓ
  apply matrix_eq_of_mulVec_increasingEigenvector_eq (⟨K, hK⟩ : HermitianMatrix (Fin N))
  intro q
  change dysonProjection N K ℓ.rev *ᵥ increasingEigenvector hK q =
    (fun x y => increasingEigenvector hK m x * conj (increasingEigenvector hK m y)) *ᵥ
      increasingEigenvector hK q
  have hq : increasingEigenvector hK q = ⇑(hK.eigenvectorBasis (increasingIndex q)) := by
    unfold increasingEigenvector; rw [increasingEigenbasis_apply]
  have hd : dysonLabel N (increasingIndex q) = (Fin.cast (Fintype.card_fin N) q).rev := by
    have := dysonLabel_increasingIndex (N := N) (Fin.cast (Fintype.card_fin N) q)
    simpa using this
  have hlab : dysonLabel N (increasingIndex q) = ℓ.rev ↔ q = m := by
    rw [hd]
    simp only [Fin.ext_iff, Fin.val_rev, Fin.val_cast, m]
    have := q.isLt
    have := ℓ.isLt
    simp only [Fintype.card_fin] at *
    omega
  rw [hq, dysonProjection_mulVec_eigenvectorBasis hK hs, ← hq]
  have horth := increasingEigenvector_orthonormal hK m q
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  have hsum : ∑ y, increasingEigenvector hK m x * conj (increasingEigenvector hK m y) *
      increasingEigenvector hK q y = increasingEigenvector hK m x *
        (∑ y, conj (increasingEigenvector hK m y) * increasingEigenvector hK q y) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
  rw [hsum, horth]
  by_cases h : q = m
  · subst h; simp [(hlab).2 rfl]
  · have h' : ¬ dysonLabel N (increasingIndex q) = ℓ.rev := fun e => h (hlab.1 e)
    have h'' : ¬ m = q := fun e => h e.symm
    simp [h', h'']

/-- `revSelection` spans the eigenprojections. -/
theorem isEigenSelection_revSelection (N : ℕ) : IsEigenSelection N (revSelection N) := by
  intro H hH hs i
  have hi : i = i.rev.rev := (Fin.rev_rev i).symm
  set ℓ := i.rev
  rw [hi, dysonProjection_rev_eq_outer hH hs ℓ]
  obtain ⟨z, hz, he⟩ := orderedColumnSelection_eq_phase (Fin.cast (Fintype.card_fin N).symm ℓ)
    ⟨H, hH⟩ (injective_orderedEigenvalue hH hs)
  have hfe : revSelection N H ℓ.rev =
      z • increasingEigenvector hH (Fin.cast (Fintype.card_fin N).symm ℓ) := by
    unfold revSelection
    rw [Fin.rev_rev]
    funext x
    simp only [freshEigenvector]
    rw [rawOrderedColumnSelection_eq _ H hH, he]
  rw [hfe]
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  funext x y
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, RCLike.star_def,
    map_mul]
  linear_combination (increasingEigenvector hH (Fin.cast (Fintype.card_fin N).symm ℓ) x *
    conj (increasingEigenvector hH (Fin.cast (Fintype.card_fin N).symm ℓ) y)) * (-hzz)

/-!
## Label reversal and frame scaling
-/

/-- Reverse the labels of an array: `(R Z)_ℓ = Z_{ℓ.rev}`. -/
def relabelArray (Z : Fin N → Fin r → ℂ) : Fin N → Fin r → ℂ := fun ℓ => Z ℓ.rev

@[simp] theorem relabelArray_relabelArray (Z : Fin N → Fin r → ℂ) :
    relabelArray (relabelArray Z) = Z := by
  funext ℓ; simp [relabelArray]

/-- The frame `V' = √N V`. -/
def scaledFrame (V : Matrix (Fin N) (Fin r) ℂ) : Matrix (Fin N) (Fin r) ℂ :=
  ((Real.sqrt N : ℝ) : ℂ) • V

/-- The array `frameArray V K` is `angularArray` of `√N V` and `revSelection`, with labels
reversed. -/
theorem frameArray_eq_relabel (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    frameArray V K = relabelArray (angularArray (scaledFrame V) (revSelection N K)) := by
  funext ℓ
  simp only [frameArray, relabelArray, angularArray, scaledFrame, revSelection, Fin.rev_rev,
    conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mulVec]

/-!
## Eigenvalues
-/

/-- `dysonEigenvalue N H i` is half the increasing eigenvalue of `H + Hᴴ` at the reversed rank,
for every matrix `H`.
-/
theorem dysonEigenvalue_eq_fresh_add (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    dysonEigenvalue N H i = freshEigenvalue (H + Hᴴ) i.rev / 2 := by
  rw [BlockBand.Palm.MomentFlow.freshEigenvalue_eq (Matrix.isHermitian_add_transpose_self H),
    cast_rev, Fin.rev_rev]
  rfl

theorem measurable_dysonEigenvalue (N : ℕ) :
    Measurable (fun H : Matrix (Fin N) (Fin N) ℂ => dysonEigenvalue N H) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp_rw [dysonEigenvalue_eq_fresh_add]
  have hc : Continuous fun H : Matrix (Fin N) (Fin N) ℂ => H + Hᴴ :=
    continuous_id.add continuous_id.matrix_conjTranspose
  exact ((measurable_rawIncreasingEigenvalue _).comp hc.measurable).div_const 2

theorem measurable_matrix_add {α : Type*} [MeasurableSpace α]
    {A B : α → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => A x + B x :=
  Measurable.of_eval_matrix _ fun i j =>
    (hA.eval_matrix (i := i) (j := j)).add (hB.eval_matrix (i := i) (j := j))

/-- For Hermitian `K`, the increasing eigenvalues are the `dysonEigenvalue`s at reversed labels. -/
theorem freshEigenvalue_fun_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) :
    (fun ℓ => freshEigenvalue K ℓ) = fun ℓ => dysonEigenvalue N K ℓ.rev :=
  funext fun ℓ => freshEigenvalue_eq_dyson hK ℓ

/-!
## Path σ-algebras
-/

/-- The eigenvalue path σ-algebra in increasing ranks is contained in the one in nonincreasing
labels (`dysonEigenvalue`) when every `F + G_t` is Hermitian. -/
theorem eigenPathSigma_le_contract {Ω : Type*} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ t ω, (F ω + G t ω).IsHermitian)
    (s : ℝ≥0) :
    BlockBand.Critical.RelativeVectors.eigenPathSigma F G s ≤
      BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G s := by
  refine iSup_le fun v => ?_
  have e : (fun ω => fun i => freshEigenvalue (F ω + G (s + v) ω) i) =
      (fun lam : Fin N → ℝ => fun i => lam i.rev) ∘
        (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) := by
    funext ω i
    exact freshEigenvalue_eq_dyson (hH _ ω) i
  rw [e, ← MeasurableSpace.comap_comp]
  refine (MeasurableSpace.comap_mono ?_).trans
    (le_iSup (fun v => MeasurableSpace.comap
      (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) inferInstance) v)
  exact (measurable_pi_iff.2 fun i => measurable_pi_apply i.rev).comap_le

/-- The eigenvalues at time `t` are `𝓖_t`-measurable. -/
theorem measurable_dysonEigenvalue_path {Ω : Type*} [MeasurableSpace Ω]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    {F : Ω → Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hF : Measurable[𝓖 0] F) (hG : ∀ t, Measurable[𝓖 t] (G t)) (t : ℝ≥0) :
    Measurable[𝓖 t] fun ω => dysonEigenvalue N (F ω + G t ω) :=
  (measurable_dysonEigenvalue N).comp
    (@measurable_matrix_add N Ω (𝓖 t) F (G t)
      (hF.mono (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t)) le_rfl) (hG t))

/-- The path σ-algebra after `s` is contained in `𝓖_{s+w} ⊔` the path σ-algebra after `s + w`:
the eigenvalues on `[s, s+w]` are adapted, the later ones are in the path. -/
theorem contractPathSigma_le_shift {Ω : Type*} [MeasurableSpace Ω]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    {F : Ω → Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hF : Measurable[𝓖 0] F) (hG : ∀ t, Measurable[𝓖 t] (G t)) (s w : ℝ≥0) :
    BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G s ≤
      𝓖 (s + w) ⊔
        BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G (s + w) := by
  refine iSup_le fun v => ?_
  rcases le_total w v with hwv | hvw
  · have e : s + v = s + w + (v - w) := by
      rw [add_assoc, add_tsub_cancel_of_le hwv]
    refine le_trans ?_ le_sup_right
    rw [e]
    exact le_iSup (fun v' => MeasurableSpace.comap
      (fun ω => dysonEigenvalue N (F ω + G (s + w + v') ω)) inferInstance) (v - w)
  · refine le_trans ?_ le_sup_left
    refine (measurable_dysonEigenvalue_path 𝓖 hF hG (s + v)).comap_le.trans ?_
    exact 𝓖.mono (add_le_add_right hvw s)

end BlockBand.Critical.RelativeVectors.Angular
