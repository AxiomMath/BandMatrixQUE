module

public import BlockBand.SourceProcess.ComplexUnique.NoiseTransfer
public import BlockBand.SourceProcess.ComplexUnique.Coeffs

/-!
# The joint chart noise and its brackets

`jNoise D₀ η δ 𝖣 a z` is the noise of the joint coordinates evaluated at the chart frame
`chartFrame δ (gramOf z)`: the Gram noise on the Gram coordinates and the `𝒦` noise on the probe
block. On good chart points (`ChartGood`) its bilinear and sesquilinear brackets are the joint
coefficients `jΓ` and `jΓ'` (`sum_jNoise_mul`, `sum_jNoise_mul_star`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open BlockBand.Internal.Contracts.TransmissionLaws

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π]

/-- **The joint chart noise.** -/
def jNoise (D0 η δ : ℝ) (D : Matrix (SrcCol K π) (SrcCol K π) ℂ)
    (a : SourceNoise (SrcCol K π ⊕ SrcCol K π)) (z : JIdx (SrcCol K π) π → ℂ) :
    JIdx (SrcCol K π) π → ℂ :=
  Sum.elim (fun e => gramEntry e (gramNoise D0 P0 D a (chartFrame δ (gramOf z))))
    fun q => kNoise D0 η P0 D a (chartFrame δ (gramOf z)) (Sum.inr q.1) (Sum.inr q.2)

variable {D0 η δ : ℝ} {D : Matrix (SrcCol K π) (SrcCol K π) ℂ} {z : JIdx (SrcCol K π) π → ℂ}

theorem gg_bracket (hD0 : 0 ≤ D0) (hD : IsSignature D) (hδ : 0 < δ) (hz : ChartGood D δ (gramOf z))
    (e e' : Fin 2 × SrcCol K π × SrcCol K π) :
    ∑ a, gramEntry e (gramNoise D0 P0 D a (chartFrame δ (gramOf z))) *
      gramEntry e' (gramNoise D0 P0 D a (chartFrame δ (gramOf z))) =
        gramCovEntry D0 D e e' (gramOf z) := by
  obtain ⟨n, N, P, V, hP, hV, hGe⟩ := exists_realization_of_feasible hz.1
  rw [bracket_transfer hD0 hD.1 P0_herm P0_idem hP.1 hP.2.1
    ((gramPair_chartFrame hδ hz).trans hGe.symm), gramNoise_cov_entry hD0 hP hD hV, hGe]

theorem star_gramEntry_noise (a : SourceNoise (SrcCol K π ⊕ SrcCol K π))
    (V : Matrix (SrcCol K π ⊕ SrcCol K π) (SrcCol K π) ℂ) (e : Fin 2 × SrcCol K π × SrcCol K π) :
    star (gramEntry e (gramNoise D0 P0 D a V)) = gramEntry (gramSwap e) (gramNoise D0 P0 D a V) :=
  star_gramEntry_of_herm (gramNoise_herm D0 P0_herm D a V).1 (gramNoise_herm D0 P0_herm D a V).2 e

theorem kg_bracket (hD0 : 0 ≤ D0) (hD : IsSignature D) (hδ : 0 < δ) (hz : ChartGood D δ (gramOf z))
    (q : π × π) (e : Fin 2 × SrcCol K π × SrcCol K π) :
    ∑ a, kNoise D0 η P0 D a (chartFrame δ (gramOf z)) (Sum.inr q.1) (Sum.inr q.2) *
      gramEntry e (gramNoise D0 P0 D a (chartFrame δ (gramOf z))) = kgCov D0 η D z q e := by
  have hVG := gramPair_chartFrame hδ hz
  simp only [gramEntry_gramNoise]
  rw [sum_kNoise_mul_gram hD0, raw_B P0_herm P0_idem hVG]
  unfold kgCov qOf
  by_cases h : e.1 = 0
  · simp only [h, ite_true, Matrix.mul_one]
    rw [raw_C0 hD.1 P0_herm P0_idem hz.1 hVG]
  · simp only [h, ite_false]
    rw [raw_C1 hD.1 P0_herm P0_idem hz.1 hVG]

/-- **Bilinear brackets of the joint chart noise.** -/
theorem sum_jNoise_mul (hD0 : 0 ≤ D0) (hD : IsSignature D) (hδ : 0 < δ)
    (hz : ChartGood D δ (gramOf z)) (p p' : JIdx (SrcCol K π) π) :
    ∑ a, jNoise D0 η δ D a z p * jNoise D0 η δ D a z p' = jΓ D0 η D z p p' := by
  rcases p with e | q <;> rcases p' with e' | q'
  · exact gg_bracket hD0 hD hδ hz e e'
  · simp only [jNoise, jΓ, Sum.elim_inl, Sum.elim_inr]
    simp_rw [mul_comm (gramEntry e _)]
    exact kg_bracket hD0 hD hδ hz q' e
  · exact kg_bracket hD0 hD hδ hz q e'
  · simp only [jNoise, jΓ, Sum.elim_inr]
    exact sum_kNoise_mul _ _ _ _ _ _ _ _ _

/-- **Sesquilinear brackets of the joint chart noise.** -/
theorem sum_jNoise_mul_star (hD0 : 0 ≤ D0) (hD : IsSignature D) (hδ : 0 < δ)
    (hz : ChartGood D δ (gramOf z)) (p p' : JIdx (SrcCol K π) π) :
    ∑ a, jNoise D0 η δ D a z p * star (jNoise D0 η δ D a z p') = jΓ' D0 η D z p p' := by
  rcases p with e | q <;> rcases p' with e' | q'
  · simp only [jNoise, jΓ', Sum.elim_inl, star_gramEntry_noise]
    exact gg_bracket hD0 hD hδ hz e (gramSwap e')
  · simp only [jNoise, jΓ', Sum.elim_inl, Sum.elim_inr]
    rw [← kg_bracket hD0 hD hδ hz q' (gramSwap e), star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [star_mul', ← star_gramEntry_noise, star_star, mul_comm]
  · simp only [jNoise, jΓ', Sum.elim_inl, Sum.elim_inr, star_gramEntry_noise]
    exact kg_bracket hD0 hD hδ hz q (gramSwap e')
  · simp only [jNoise, jΓ', Sum.elim_inr]
    rw [sum_kNoise_mul_star hD0, raw_B P0_herm P0_idem (gramPair_chartFrame hδ hz),
      raw_C0 hD.1 P0_herm P0_idem hz.1 (gramPair_chartFrame hδ hz)]
    rfl

end BlockBand.SourceProcess.ComplexUnique
