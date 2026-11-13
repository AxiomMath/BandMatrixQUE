module

public import BlockBand.SourceProcess.PhysApprox.B3DecayStep
public import BlockBand.SourceProcess.PhysApprox.B3FeasMain
public import BlockBand.SourceProcess.ClosingAux.Contraction
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# The alive closed contracting coordinates are bounded

**The closed near-port scattering is a contraction.** Pure algebra on a finite index type: with
`𝕊𝕊ᴴ = 1`, `P` and `A` orthogonal projections, `ΠΠᴴ = A`, `ΠP = 0`, `|z| = 1` and `1 - zN`
invertible, `C = C(z)` the closing map and `Q = ΠᴴΠ`,

  `Cᴴ𝕊ᴴP𝕊C = (1 - A) - Cᴴ𝕊ᴴ(1 - Q - P)𝕊C`

(`closed_omitted_current` gives `CᴴAC = Cᴴ𝕊ᴴQ𝕊C`, and `(1 - A)C = 1 - A`). Since `1 - Q - P` is
an orthogonal projection (`PQ = 0`), `‖P𝕊Cx‖² ≤ ‖(1 - A)x‖² ≤ ‖x‖²` for **every** `x`, so
`‖P𝕊C‖ ≤ 1` (`closedNearPS_opNorm_le`). Only the near rows are bounded: the full `𝕊C` is not a
contraction (its omitted far rows carry `(1 - zN)⁻¹`), and the argument never uses `‖𝕊C‖`.

**The bound `B3ClosedContrBound`.** The four closed separators `P𝕊C, (P𝕊C)ᴴ, P𝕊CP, P(P𝕊C)ᴴ` have
operator norm `≤ 1`, so
`|Q^σ_{kl}| = |⟨V e_k, Σ_σ V e_l⟩| ≤ ‖V e_k‖‖V e_l‖ ≤ Re Tr VᴴV = Re Tr M_j < R` on the alive set
(`b3ClosedContrBound_holds`, with `C = max R 0`). The almost-sure set is that of
`ae_scattering_unitary` and `ae_isUnit_closingResolvent`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3DecayIn

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.PhysApprox.B3 BlockBand.SourceProcess.PhysApprox.B3Cur
open BlockBand.SourceProcess.PhysApprox.B3Feas
open BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

/-!
## Quadratic forms
-/

section Algebra

variable {ι : Type*} [Fintype ι]

theorem quad_sandwich (Y Z : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ ((Yᴴ * Z * Y) *ᵥ x) = star (Y *ᵥ x) ⬝ᵥ (Z *ᵥ (Y *ᵥ x)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- For an orthogonal projection `D`, `⟨w, Dw⟩ ≥ 0`. -/
theorem re_quad_proj_nonneg {D : Matrix ι ι ℂ} (hDH : Dᴴ = D) (hDD : D * D = D) (w : ι → ℂ) :
    0 ≤ (star w ⬝ᵥ (D *ᵥ w)).re := by
  have h := quad_mulVec D w
  rw [hDH, hDD] at h
  rw [← h]
  exact (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg _)).1

variable [DecidableEq ι] {S P A Pi : Matrix ι ι ℂ} {z : ℂ}

/-- **The near rows of the closed scattering**: `Cᴴ𝕊ᴴP𝕊C = (1 - A) - Cᴴ𝕊ᴴ(1 - ΠᴴΠ - P)𝕊C`. -/
theorem closedNear_gram (hS : S * Sᴴ = 1) (hAH : Aᴴ = A) (hAA : A * A = A)
    (hPi : Pi * Piᴴ = A) (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : ‖z‖ = 1) :
    (closingMap S A Pi z)ᴴ * (Sᴴ * P * S) * closingMap S A Pi z =
      (1 - A) - (closingMap S A Pi z)ᴴ * (Sᴴ * (1 - Piᴴ * Pi - P) * S) *
        closingMap S A Pi z := by
  set C := closingMap S A Pi z with hCdef
  have hAPi : A * Pi = Pi := mul_self_of_mul_conj hAA hPi
  have hSS : Sᴴ * S = 1 := mul_eq_one_comm.mp hS
  have h1AC : (1 - A) * C = 1 - A := compl_mul_closingMap hAA hAPi
  have h1AH : (1 - A)ᴴ = 1 - A := by rw [conjTranspose_sub, conjTranspose_one, hAH]
  have h1A1A : (1 - A) * (1 - A) = 1 - A := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hAA, sub_self, sub_zero]
  have hC1A : Cᴴ * (1 - A) * C = 1 - A := by
    calc Cᴴ * (1 - A) * C = ((1 - A) * C)ᴴ * ((1 - A) * C) := by
          rw [conjTranspose_mul, h1AH, Matrix.mul_assoc, Matrix.mul_assoc,
            ← Matrix.mul_assoc (1 - A), h1A1A]
      _ = 1 - A := by rw [h1AC, h1AH, h1A1A]
  have hom := closed_omitted_current (S := S) hAH hAA hAPi hU hz
  rw [← hCdef] at hom
  have hCAC : Cᴴ * A * C = Cᴴ * (Sᴴ * (Piᴴ * Pi) * S) * C := by
    have e : Cᴴ * ((Pi * S)ᴴ * (Pi * S)) * C = Cᴴ * (Sᴴ * (Piᴴ * Pi) * S) * C := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [← e, ← sub_eq_zero, ← Matrix.sub_mul, ← Matrix.mul_sub, hom]
  have hsplit : Sᴴ * P * S = Sᴴ * S - Sᴴ * (Piᴴ * Pi) * S - Sᴴ * (1 - Piᴴ * Pi - P) * S := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  rw [hsplit, hSS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, ← hCAC,
    Matrix.mul_one]
  have hCC : Cᴴ * C = (1 - A) + Cᴴ * A * C := by
    rw [← hC1A, ← Matrix.add_mul, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_one]
  rw [hCC]
  abel

/-- **The closed near-port scattering is a contraction**: `‖P𝕊C(z)‖ ≤ 1`. -/
theorem closedNearPS_opNorm_le (hS : S * Sᴴ = 1) (hPH : Pᴴ = P) (hPP : P * P = P)
    (hAH : Aᴴ = A) (hAA : A * A = A) (hPi : Pi * Piᴴ = A) (hPiP : Pi * P = 0)
    (hU : IsUnit (1 - z • closingN S A Pi).det) (hz : ‖z‖ = 1) :
    ‖P * S * closingMap S A Pi z‖ ≤ 1 := by
  set C := closingMap S A Pi z with hCdef
  have hAPi : A * Pi = Pi := mul_self_of_mul_conj hAA hPi
  set Q := Piᴴ * Pi with hQdef
  have hQH : Qᴴ = Q := by rw [hQdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hPiA : Piᴴ * A = Piᴴ := by rw [← hAH, ← conjTranspose_mul, hAPi]
  have hQQ : Q * Q = Q := by
    calc Q * Q = Piᴴ * (Pi * Piᴴ) * Pi := by simp only [hQdef, Matrix.mul_assoc]
      _ = Q := by rw [hPi, hPiA]
  have hQP : Q * P = 0 := by rw [hQdef, Matrix.mul_assoc, hPiP, Matrix.mul_zero]
  have hPQ : P * Q = 0 := by
    rw [← hPH, ← hQH, ← conjTranspose_mul, hQP, conjTranspose_zero]
  set D := 1 - Q - P with hDdef
  have hDH : Dᴴ = D := by rw [hDdef, conjTranspose_sub, conjTranspose_sub, conjTranspose_one, hQH,
    hPH]
  have hDD : D * D = D := by
    simp only [hDdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ, hPP,
      hPQ, hQP]
    abel
  have hAA' : Aᴴ * A = A := by rw [hAH, hAA]
  have hG := closedNear_gram (P := P) hS hAH hAA hPi hU hz
  rw [← hCdef, ← hQdef, ← hDdef] at hG
  have hMM : (P * S * C)ᴴ * (P * S * C) = Cᴴ * (Sᴴ * P * S) * C := by
    simp only [conjTranspose_mul, hPH, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P P, hPP]
  refine opNorm_le_of_vec _ zero_le_one fun x => ?_
  have hq : star ((P * S * C) *ᵥ x) ⬝ᵥ ((P * S * C) *ᵥ x) =
      star x ⬝ᵥ x - star x ⬝ᵥ (A *ᵥ x) - star ((S * C) *ᵥ x) ⬝ᵥ (D *ᵥ ((S * C) *ᵥ x)) := by
    rw [quad_mulVec, hMM, hG, sub_mulVec, sub_mulVec, one_mulVec, dotProduct_sub, dotProduct_sub,
      ← quad_sandwich]
    congr 3
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have hA0 : 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := re_quad_proj_nonneg hAH hAA x
  have hD0 := re_quad_proj_nonneg hDH hDD ((S * C) *ᵥ x)
  have hre := congrArg Complex.re hq
  rw [star_self_eq, star_self_eq, Complex.sub_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_re] at hre
  have hle : vecNorm ((P * S * C) *ᵥ x) ^ 2 ≤ vecNorm x ^ 2 := by linarith
  have h1 := vecNorm_nonneg ((P * S * C) *ᵥ x)
  have h2 := vecNorm_nonneg x
  nlinarith

/-- An orthogonal projection has operator norm `≤ 1`. -/
theorem opNorm_proj_le {P : Matrix ι ι ℂ} (hPH : Pᴴ = P) (hPP : P * P = P) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hPH, hPP] at h
  rcases (norm_nonneg P).eq_or_lt with h0 | h0
  · rw [← h0]; exact zero_le_one
  · nlinarith

end Algebra

/-!
## Entries and columns
-/

section Entries

variable {ι c : Type*} [Fintype ι]

/-- `(VᴴΣV)_{kl} = ⟨V e_k, Σ V e_l⟩`. -/
theorem sandwich_apply (V : Matrix ι c ℂ) (X : Matrix ι ι ℂ) (k l : c) :
    (Vᴴ * X * V) k l = bilinear (fun x => V x k) X (fun x => V x l) := by
  simp only [bilinear, Matrix.mul_apply, conjTranspose_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `Re Tr VᴴV = Σ_k ‖V e_k‖²`. -/
theorem re_trace_gram [Fintype c] (V : Matrix ι c ℂ) :
    ((Vᴴ * V).trace).re = ∑ k, vecNorm (fun x => V x k) ^ 2 := by
  refine (Complex.re_sum _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [vecNorm, Real.sq_sqrt (by positivity)]
  simp only [diag, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Complex.conj_mul',
    Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- `|(VᴴΣV)_{kl}| ≤ ‖Σ‖ Re Tr VᴴV`. -/
theorem norm_sandwich_le [Fintype c] [DecidableEq ι] (V : Matrix ι c ℂ) (X : Matrix ι ι ℂ)
    (k l : c) : ‖(Vᴴ * X * V) k l‖ ≤ ‖X‖ * ((Vᴴ * V).trace).re := by
  rw [sandwich_apply, re_trace_gram]
  set a := vecNorm fun x => V x k
  set b := vecNorm fun x => V x l
  set T := ∑ k, vecNorm (fun x => V x k) ^ 2
  have ha : a ^ 2 ≤ T := Finset.single_le_sum (f := fun k => vecNorm (fun x => V x k) ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ k)
  have hb : b ^ 2 ≤ T := Finset.single_le_sum (f := fun k => vecNorm (fun x => V x k) ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ l)
  have ha0 : 0 ≤ a := vecNorm_nonneg _
  have hb0 : 0 ≤ b := vecNorm_nonneg _
  have hab : a * b ≤ T := by nlinarith [sq_nonneg (a - b)]
  calc ‖bilinear (fun x => V x k) X (fun x => V x l)‖ ≤ a * ‖X‖ * b := norm_bilinear_le _ _ _
    _ = ‖X‖ * (a * b) := by ring
    _ ≤ ‖X‖ * T := mul_le_mul_of_nonneg_left hab (norm_nonneg X)

end Entries

/-!
## The four closed separators
-/

variable {W : ℕ}

/-- **The four closed contracting separators have operator norm `≤ 1`** (deterministic, given
`𝕊_j` unitary and `1 - zN_j` invertible, `|z| = 1`, `h² < 1`). -/
theorem opNorm_b3ContrSep_le {b E s h : ℝ} (hh : h ^ 2 < 1) {j : ℕ} {ω : GrowthPath W} {z : ℂ}
    (hS : scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1)
    (hU : IsUnit (1 - z • closingN (scatteringMatrix b E W j ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) (hz : ‖z‖ = 1) (σ : Fin 4) :
    ‖b3ContrSep b E s h W j ω z σ‖ ≤ 1 := by
  have hAH : (farEmbed (omittedProj b E h W (closeLen s W) ω))ᴴ =
      farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAA : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      farEmbed (omittedProj b E h W (closeLen s W) ω) =
      farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_mul, omittedProj_mul_self]
  have hPi : farEmbed (closingPairing b E h W (closeLen s W) ω) *
      (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ =
      farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have h0 : ‖b3ClosedPS b E s h W j ω z‖ ≤ 1 :=
    closedNearPS_opNorm_le hS nearPortProj_conjTranspose nearPortProj_mul_self hAH hAA hPi
      (farEmbed_mul_nearPortProj _) hU hz
  have hP : ‖nearPortProj W‖ ≤ 1 := opNorm_proj_le nearPortProj_conjTranspose nearPortProj_mul_self
  have h0' : ‖(b3ClosedPS b E s h W j ω z)ᴴ‖ ≤ 1 := by rw [l2_opNorm_conjTranspose]; exact h0
  have hn0 := norm_nonneg (b3ClosedPS b E s h W j ω z)
  have hnP := norm_nonneg (nearPortProj W)
  have h2 : ‖b3ClosedPS b E s h W j ω z * nearPortProj W‖ ≤ 1 :=
    (l2_opNorm_mul _ _).trans (by nlinarith)
  have h3 : ‖nearPortProj W * (b3ClosedPS b E s h W j ω z)ᴴ‖ ≤ 1 := by
    refine (l2_opNorm_mul _ _).trans ?_
    rw [l2_opNorm_conjTranspose]
    nlinarith
  fin_cases σ
  · exact h0
  · exact h0'
  · exact h2
  · exact h3

/-!
## The bound `B3ClosedContrBound`
-/

/-- **`B3ClosedContrBound` holds**, with `C = max R 0`. -/
theorem b3ClosedContrBound_holds : B3ClosedContrBound := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, hh1, -⟩ := hFD
  have hh : h ^ 2 < 1 := by nlinarith
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  filter_upwards [eventually_ge_atTop 1, B3Cur.eventually_one_le_closeLen hs]
    with W hW hsW j hj _ σ k l
  have hgood : ∀ᵐ ω ∂growthPathLaw W b,
      (∀ n, scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1) ∧
      (∀ n, 1 ≤ n → ∀ z : ℂ, ‖z‖ ≤ 1 →
        IsUnit (1 - z • closingN (scatteringMatrix b E W n ω)
          (farEmbed (omittedProj b E h W (closeLen s W) ω))
          (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) := by
    filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
      ae_isUnit_closingResolvent (h := h) hb0 hb hE1 hE2 hW hh (closeLen s W)] with ω hU hR
    exact ⟨fun n => (hU n).1, hR⟩
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
    (ν := Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W))).ae hgood
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b)
    (ν := phaseLaw)).ae h1
  filter_upwards [h2] with y hg
  obtain ⟨hU, hR⟩ := hg
  by_cases hy : y ∈ b3Alive b E s h τ m R W j (Vs W)
  · rw [Set.indicator_of_mem hy]
    have hz : ‖phase y.2‖ = 1 := by rw [phase]; exact Complex.norm_exp_ofReal_mul_I y.2
    have hR' : ((b3ClosedGramAt b E s h τ m W j (Vs W) y).1.trace).re < R := hy.2 j hj le_rfl
    have hsep := opNorm_b3ContrSep_le (s := s) hh (hU j) (hR j (hsW.trans hj) _ hz.le) hz σ
    have hb := norm_sandwich_le (b3ClosedFrameAt b E s h τ m W j (Vs W) y)
      (b3ContrSep b E s h W j y.1.1 (phase y.2) σ) k l
    have htr0 : 0 ≤ (((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
        b3ClosedFrameAt b E s h τ m W j (Vs W) y).trace).re := by
      rw [re_trace_gram]; positivity
    change ‖((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
      b3ContrSep b E s h W j y.1.1 (phase y.2) σ * b3ClosedFrameAt b E s h τ m W j (Vs W) y) k l‖
      ≤ max R 0
    refine hb.trans ?_
    have htr : (((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
        b3ClosedFrameAt b E s h τ m W j (Vs W) y).trace).re < R := hR'
    calc _ ≤ 1 * (((b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ *
          b3ClosedFrameAt b E s h τ m W j (Vs W) y).trace).re :=
          mul_le_mul_of_nonneg_right hsep htr0
      _ ≤ max R 0 := by rw [one_mul]; exact htr.le.trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hy, norm_zero]
    exact le_max_right _ _

end BlockBand.SourceProcess.PhysApprox.B3DecayIn

