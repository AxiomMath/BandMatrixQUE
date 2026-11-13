module

public import BlockBand.SourceProcess.ComplexUnique.BridgeMain
public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The joint `(G, 𝒦)` coordinates and coefficients

Complex coordinates `JIdx c π = (Fin 2 × c × c) ⊕ (π × π)`: the Gram entries `gramEntry e G` and
the entries `𝒦_ij`. `jvec G 𝒦` is the coordinate vector, `gramOf`, `kOf` its inverses.
The coefficients of the joint martingale problem (`IsBornGramSolution` and
`IsComplexSourceExtension`):
* `jβ`: Gram drift `gramDriftEntry`, `𝒦` drift `0`;
* `jΓ` (bilinear brackets): Gram–Gram `gramCovEntry`, `𝒦–𝒦` `0` (holomorphic clause),
  `𝒦–Gram` `kgCov` (`crossM`, `crossB`);
* `jΓ'` (sesquilinear brackets): Gram–Gram `gramCovEntry e (gramSwap e')`, `𝒦–𝒦` `kkCov`
  (antiholomorphic clause), `𝒦–Gram` `kgCov (gramSwap e)`, Gram–`𝒦` its conjugate.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory Filter Topology Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

/-- Joint complex coordinates. -/
abbrev JIdx (c π : Type*) := (Fin 2 × c × c) ⊕ (π × π)

variable {K : ℕ} {π : Type*} [Fintype π]

/-- The coordinate vector of `(G, 𝒦)`. -/
def jvec (G : GramState (SrcCol K π)) (Kc : Matrix π π ℂ) : JIdx (SrcCol K π) π → ℂ :=
  Sum.elim (fun e => gramEntry e G) fun q => Kc q.1 q.2

/-- The Gram pair of a coordinate vector. -/
def gramOf (z : JIdx (SrcCol K π) π → ℂ) : GramState (SrcCol K π) :=
  (Matrix.of fun i j => z (Sum.inl (0, i, j)), Matrix.of fun i j => z (Sum.inl (1, i, j)))

/-- The `𝒦` matrix of a coordinate vector. -/
def kOf (z : JIdx (SrcCol K π) π → ℂ) : Matrix π π ℂ := Matrix.of fun i j => z (Sum.inr (i, j))

omit [Fintype π] in
theorem gramOf_jvec (G : GramState (SrcCol K π)) (Kc : Matrix π π ℂ) : gramOf (jvec G Kc) = G := by
  ext i j <;> simp [gramOf, jvec, gramEntry]

omit [Fintype π] in
theorem kOf_jvec (G : GramState (SrcCol K π)) (Kc : Matrix π π ℂ) : kOf (jvec G Kc) = Kc := by
  ext i j; simp [kOf, jvec]

omit [Fintype π] in
theorem jvec_add (G G' : GramState (SrcCol K π)) (Kc Kc' : Matrix π π ℂ) :
    jvec (G + G') (Kc + Kc') = jvec G Kc + jvec G' Kc' := by
  funext p; rcases p with e | q
  · simp only [jvec, Sum.elim_inl, Pi.add_apply, gramEntry]; split_ifs <;> rfl
  · simp [jvec]

omit [Fintype π] in
theorem jvec_sub_add (G J : GramState (SrcCol K π)) (Kc JK : Matrix π π ℂ) :
    jvec (G - J) (Kc - JK) + jvec J JK = jvec G Kc := by
  rw [← jvec_add, sub_add_cancel, sub_add_cancel]

omit [Fintype π] in
theorem continuous_jvec : Continuous fun x : GramState (SrcCol K π) × Matrix π π ℂ =>
    jvec x.1 x.2 := by
  refine continuous_pi fun p => ?_
  rcases p with e | q
  · exact (continuous_gramEntry e).comp continuous_fst
  · exact (continuous_apply q.2).comp ((continuous_apply q.1).comp continuous_snd)

omit [Fintype π] in
theorem continuous_gramOf : Continuous (gramOf (K := K) (π := π)) :=
  (continuous_pi fun _ => continuous_pi fun _ => continuous_apply _).prodMk
    (continuous_pi fun _ => continuous_pi fun _ => continuous_apply _)

variable (D0 η : ℝ) (D : Matrix (SrcCol K π) (SrcCol K π) ℂ)

/-- The joint drift. -/
def jβ (z : JIdx (SrcCol K π) π → ℂ) : JIdx (SrcCol K π) π → ℂ :=
  Sum.elim (fun e => gramDriftEntry D0 D e (gramOf z)) fun _ => 0

/-- The `𝒦–Gram` bracket `d𝒦_ij dG_e` (`crossM` for `e = (0,k,l)`, `crossB` for `(1,k,l)`). -/
def kgCov (z : JIdx (SrcCol K π) π → ℂ) (q : π × π) (e : Fin 2 × SrcCol K π × SrcCol K π) : ℂ :=
  -(Complex.I * ((η * D0 : ℝ) : ℂ)) * (gramOf z).2 (Sum.inr q.1) e.2.2 *
    (if e.1 = 0 then gramC0 (gramOf z).1 (gramOf z).2 D
      else (gramC1 (gramOf z).1 (gramOf z).2 D)ᴴ) e.2.1 (Sum.inr q.2)

/-- The `𝒦–\bar𝒦` bracket `d𝒦_ij d\bar𝒦_kl = 2η²D₀ B_ik (C₀)_lj`. -/
def kkCov (z : JIdx (SrcCol K π) π → ℂ) (q q' : π × π) : ℂ :=
  ((2 * η ^ 2 * D0 : ℝ) : ℂ) * (gramOf z).2 (Sum.inr q.1) (Sum.inr q'.1) *
    gramC0 (gramOf z).1 (gramOf z).2 D (Sum.inr q'.2) (Sum.inr q.2)

/-- The joint bilinear brackets. -/
def jΓ (z : JIdx (SrcCol K π) π → ℂ) : JIdx (SrcCol K π) π → JIdx (SrcCol K π) π → ℂ :=
  Sum.elim (fun e => Sum.elim (fun e' => gramCovEntry D0 D e e' (gramOf z))
      fun q => kgCov D0 η D z q e)
    fun q => Sum.elim (fun e => kgCov D0 η D z q e) fun _ => 0

/-- The joint sesquilinear brackets. -/
def jΓ' (z : JIdx (SrcCol K π) π → ℂ) : JIdx (SrcCol K π) π → JIdx (SrcCol K π) π → ℂ :=
  Sum.elim (fun e => Sum.elim (fun e' => gramCovEntry D0 D e (gramSwap e') (gramOf z))
      fun q => star (kgCov D0 η D z q (gramSwap e)))
    fun q => Sum.elim (fun e => kgCov D0 η D z q (gramSwap e)) fun q' => kkCov D0 η D z q q'

theorem continuous_gramC0_entry (x y : SrcCol K π) :
    Continuous fun G : GramState (SrcCol K π) => gramC0 G.1 G.2 D x y := by
  have h : Continuous fun G : GramState (SrcCol K π) => gramC0 G.1 G.2 D :=
    continuous_snd.add ((continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst)
  exact (continuous_apply y).comp ((continuous_apply x).comp h)

theorem continuous_gramC1H_entry (x y : SrcCol K π) :
    Continuous fun G : GramState (SrcCol K π) => (gramC1 G.1 G.2 D)ᴴ x y := by
  have h : Continuous fun G : GramState (SrcCol K π) => gramC1 G.1 G.2 D :=
    continuous_snd.add ((continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd)
  exact (continuous_apply y).comp ((continuous_apply x).comp h.matrix_conjTranspose)

theorem continuous_kgCov (q : π × π) (e : Fin 2 × SrcCol K π × SrcCol K π) :
    Continuous fun z => kgCov D0 η D z q e := by
  unfold kgCov
  have hB : Continuous fun z : JIdx (SrcCol K π) π → ℂ => (gramOf z).2 (Sum.inr q.1) e.2.2 :=
    (continuous_apply _).comp ((continuous_apply _).comp (continuous_snd.comp continuous_gramOf))
  split_ifs
  · exact (continuous_const.mul hB).mul
      ((continuous_gramC0_entry D _ _).comp continuous_gramOf)
  · exact (continuous_const.mul hB).mul
      ((continuous_gramC1H_entry D _ _).comp continuous_gramOf)

theorem continuous_kkCov (q q' : π × π) : Continuous fun z => kkCov D0 η D z q q' := by
  unfold kkCov
  exact (continuous_const.mul ((continuous_apply _).comp ((continuous_apply _).comp
    (continuous_snd.comp continuous_gramOf)))).mul
    ((continuous_gramC0_entry D _ _).comp continuous_gramOf)

theorem continuous_jβ : Continuous (jβ (K := K) (π := π) D0 D) := by
  refine continuous_pi fun p => ?_
  rcases p with e | q
  · exact (continuous_gramDriftEntry D0 D e).comp continuous_gramOf
  · exact continuous_const

theorem continuous_jΓ : Continuous (jΓ (K := K) (π := π) D0 η D) := by
  refine continuous_pi fun p => continuous_pi fun p' => ?_
  rcases p with e | q <;> rcases p' with e' | q'
  · exact (continuous_gramCovEntry D0 D e e').comp continuous_gramOf
  · exact continuous_kgCov D0 η D q' e
  · exact continuous_kgCov D0 η D q e'
  · exact continuous_const

theorem continuous_jΓ' : Continuous (jΓ' (K := K) (π := π) D0 η D) := by
  refine continuous_pi fun p => continuous_pi fun p' => ?_
  rcases p with e | q <;> rcases p' with e' | q'
  · exact (continuous_gramCovEntry D0 D e (gramSwap e')).comp continuous_gramOf
  · exact (continuous_kgCov D0 η D q' (gramSwap e)).star
  · exact continuous_kgCov D0 η D q (gramSwap e')
  · exact continuous_kkCov D0 η D q q'

end BlockBand.SourceProcess.ComplexUnique
