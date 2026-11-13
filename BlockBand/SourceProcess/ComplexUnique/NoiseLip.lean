module

public import BlockBand.SourceProcess.ComplexUnique.NoiseChart

/-!
# Local Lipschitz continuity of the joint chart noise and of the joint drift

`locallyLipschitz_jNoise`: `z ↦ jNoise D0 η δ D a z` is locally Lipschitz for `δ > 0` (the chart
frame is Lipschitz, `lipschitzWith_chartFrame`; the Gram and `𝒦` noises are polynomial in the
frame). `locallyLipschitz_jβ`: the joint drift is polynomial. Frobenius norms on matrices, as for
the Gram chart.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π]

theorem locallyLipschitz_pi_complex {X n : Type*} [PseudoMetricSpace X] [Fintype n]
    [DecidableEq n] {F : X → n → ℂ} (h : ∀ i, LocallyLipschitz fun x => F x i) :
    LocallyLipschitz F := by
  have e : F = fun x => ∑ i, Pi.single i (F x i) := by
    funext x; exact (Finset.univ_sum_single (F x)).symm
  rw [e]
  refine locallyLipschitz_sum _ fun i => ?_
  exact (ContinuousLinearMap.single ℝ (fun _ : n => ℂ) i).lipschitzWith.locallyLipschitz.comp (h i)

theorem lipschitzWith_entry {m n : Type*} [Fintype m] [Fintype n] (i : m) (j : n) :
    LipschitzWith 1 fun M : Matrix m n ℂ => M i j := by
  refine LipschitzWith.of_dist_le_mul fun M M' => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact norm_entry_le (M - M') i j

theorem lipschitzWith_gramEntry {c : Type*} [Fintype c] (e : Fin 2 × c × c) :
    LipschitzWith 1 (gramEntry (c := c) e) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have hlin : gramEntry e x - gramEntry e x' = gramEntry e (x - x') := by
    unfold gramEntry; split_ifs <;> simp
  rw [hlin]
  unfold gramEntry; split_ifs
  · exact (norm_entry_le _ _ _).trans (norm_fst_le _)
  · exact (norm_entry_le _ _ _).trans (norm_snd_le _)

/-- `gramOf` as a continuous linear map. -/
def gramOfL : (JIdx (SrcCol K π) π → ℂ) →ₗ[ℝ] GramState (SrcCol K π) where
  toFun := gramOf
  map_add' z z' := by ext i j <;> simp [gramOf]
  map_smul' r z := by ext i j <;> simp [gramOf]

omit [DecidableEq π] in
theorem lipschitzWith_gramOf :
    ∃ L, LipschitzWith L (gramOf (K := K) (π := π)) :=
  ⟨_, (LinearMap.toContinuousLinearMap (gramOfL (K := K) (π := π))).lipschitzWith⟩

theorem contDiff_kNoise {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] (D0 η : ℝ)
    (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => kNoise D0 η P D a V) := by
  have h : ContDiff ℝ k (fun V : Matrix ι c ℂ =>
      mulBil (mulBil (mulBil (ctCLM ι c V) Pᴴ) (Matrix.single a.1.1 a.1.2 (1 : ℂ)))
        (mulBil (ctCLM ι ι (gramProjection P V D)) V)) :=
    contDiff_bilin _ (contDiff_bilin _ (contDiff_bilin _ (ctCLM ι c).contDiff contDiff_const)
      contDiff_const) (contDiff_bilin _ ((ctCLM ι ι).contDiff.comp (contDiff_gramProjection P D))
        contDiff_id)
  exact h.const_smul _

variable (D0 η : ℝ) (D : Matrix (SrcCol K π) (SrcCol K π) ℂ)

theorem locallyLipschitz_jNoise {δ : ℝ} (hδ : 0 < δ) (a : SourceNoise (SrcCol K π ⊕ SrcCol K π)) :
    LocallyLipschitz (jNoise D0 η δ D a) := by
  classical
  obtain ⟨L, hL⟩ := lipschitzWith_gramOf (K := K) (π := π)
  have h1 : LocallyLipschitz fun z : JIdx (SrcCol K π) π → ℂ => chartFrame δ (gramOf z) :=
    ((lipschitzWith_chartFrame hδ).comp hL).locallyLipschitz
  refine locallyLipschitz_pi_complex fun p => ?_
  rcases p with e | q
  · exact (lipschitzWith_gramEntry e).locallyLipschitz.comp
      ((contDiff_gramNoise (k := 1) D0 P0 D a).locallyLipschitz.comp h1)
  · exact (lipschitzWith_entry _ _).locallyLipschitz.comp
      ((contDiff_kNoise (k := 1) D0 η P0 D a).locallyLipschitz.comp h1)

omit [DecidableEq π] in
theorem locallyLipschitz_jβ : LocallyLipschitz (jβ (K := K) (π := π) D0 D) := by
  classical
  obtain ⟨L, hL⟩ := lipschitzWith_gramOf (K := K) (π := π)
  refine locallyLipschitz_pi_complex fun p => ?_
  rcases p with e | q
  · have he : (fun z : JIdx (SrcCol K π) π → ℂ => jβ D0 D z (Sum.inl e)) =
        fun z => gramEntry e (gramDriftG D0 D (gramOf z)) := by
      funext z
      simp only [jβ, Sum.elim_inl, gramDriftEntry, gramDriftG, gramEntry]
      split_ifs <;> simp
    rw [he]
    exact (lipschitzWith_gramEntry e).locallyLipschitz.comp
      ((contDiff_gramDriftG (k := 1) D0 D).locallyLipschitz.comp hL.locallyLipschitz)
  · exact (LipschitzWith.const (0 : ℂ)).locallyLipschitz

end BlockBand.SourceProcess.ComplexUnique
