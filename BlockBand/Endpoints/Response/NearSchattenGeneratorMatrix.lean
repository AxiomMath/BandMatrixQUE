module

public import BlockBand.Endpoints.Response.NearSchattenGeneratorScalar
public import BlockBand.Endpoints.Response.NearSchattenUpper
public import BlockBand.Endpoints.Response.TaggedConvexOrderStepDrift
public import BlockBand.Endpoints.Response.ResponseVariancePath
public import BlockBand.Endpoints.Response.NearSchattenLimit

/-!
# The finite-width trace generator of `Tr f_ε(A)` is dissipative

Setting (deterministic, any width `W`): a unitary `U` (`U*U = 1`, at the path: `𝕊`), the near
projection `P = diag(I_W, 0)`, `P' = U*PU`, the current `J = P' - P` and the conductance
`g = ½ Re Tr J²` (`gPoly`). The projected block `Σ' = (P'){near,near}` (`= PP'P` on the
near port; `Tr(A^b Σ') = Tr (QP)^b + Tr((QP)^b J P)` is the word combination `BP'` of
`pairTerm` on clock words) is read in a unitary frame `V` (the eigenvector frame of the clock
`A`): `S_ii = Re (V*Σ'V)_ii`.

* `nsg_frameDiag_nonneg`, `nsg_frameDiag_le_one`: `0 ≤ S_ii ≤ 1`.
* `nsg_sum_one_sub_frameDiag`: `Σ_i (1 - S_ii) = g` (`Tr P' = Tr P = W` by unitarity).
* `nsg_one_sub_frameDiag_le`, `nsg_conductance_nonneg`: `T_ii = 1 - S_ii ≤ g` and `g ≥ 0`.
* `nsgGenExpr`: the right side of the Schatten trace generator for `f_ε` at the path of length
  `j`, in the eigenvector frame of the near clock (`nsgSpecGen`, eigenvalues of
  `A = nearClock`, `S_ii` of `P' = 𝕊*P𝕊`, `g` of `J = pathCurrent`, `D = transportD0`).
* `nsg_genExpr_le`, `nsg_ae_genExpr_le`: dissipativity, pointwise and almost surely.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix Finset MeasureTheory
open scoped ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-- The near-port block of `P' = U*PU`. -/
def nsgProjBlock (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  portBlock (Uᴴ * nearProjection W * U) 0 0

/-- `S_ii = Re (V*Σ'V)_ii`, the diagonal of the projected block in the frame `V`. -/
def nsgFrameDiag (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (V : Matrix (Fin W) (Fin W) ℂ)
    (i : Fin W) : ℝ :=
  ((Vᴴ * nsgProjBlock U * V) i i).re

/-- The conductance `g = ½ Re Tr J²`, `J = U*PU - P`. -/
def nsgConductance (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  (((Uᴴ * nearProjection W * U - nearProjection W) ^ 2).trace).re / 2

theorem nsg_nearProjection_psd (W : ℕ) : (nearProjection W).PosSemidef := by
  have h : nearProjection W = (nearProjection W)ᴴ * nearProjection W := by
    rw [tcs_nearProjection_hermitian, tcs_nearProjection_idem]
  rw [h]; exact posSemidef_conjTranspose_mul_self _

theorem nsg_one_sub_nearProjection_psd (W : ℕ) : (1 - nearProjection W).PosSemidef := by
  have hh : (1 - nearProjection W)ᴴ = 1 - nearProjection W := by
    rw [conjTranspose_sub, conjTranspose_one, tcs_nearProjection_hermitian]
  have hi : (1 - nearProjection W) * (1 - nearProjection W) = 1 - nearProjection W := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, tcs_nearProjection_idem]
    abel
  have h : 1 - nearProjection W = (1 - nearProjection W)ᴴ * (1 - nearProjection W) := by
    rw [hh, hi]
  rw [h]; exact posSemidef_conjTranspose_mul_self _

/-- `0 ≤ S_ii`. -/
theorem nsg_frameDiag_nonneg (U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin W) (Fin W) ℂ) (i : Fin W) : 0 ≤ nsgFrameDiag U V i := by
  have h1 : (Uᴴ * nearProjection W * U).PosSemidef :=
    (nsg_nearProjection_psd W).conjTranspose_mul_mul_same U
  have h2 : (nsgProjBlock U).PosSemidef := by
    unfold nsgProjBlock; rw [ns_portBlock_eq]; exact h1.conjTranspose_mul_mul_same _
  have h3 := (h2.conjTranspose_mul_mul_same V).diag_nonneg (i := i)
  exact (Complex.nonneg_iff.mp h3).1

/-- `S_ii ≤ 1` (unitary `U`, `V`). -/
theorem nsg_frameDiag_le_one {U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hU : Uᴴ * U = 1)
    {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) (i : Fin W) : nsgFrameDiag U V i ≤ 1 := by
  have h1 : (Uᴴ * (1 - nearProjection W) * U).PosSemidef :=
    (nsg_one_sub_nearProjection_psd W).conjTranspose_mul_mul_same U
  have e1 : Uᴴ * (1 - nearProjection W) * U = 1 - Uᴴ * nearProjection W * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
  rw [e1] at h1
  have h2 : (1 - nsgProjBlock U).PosSemidef := by
    have := h1.conjTranspose_mul_mul_same (nsNearIncl W)
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ns_nearIncl_conj_mul] at this
    unfold nsgProjBlock; rw [ns_portBlock_eq]; exact this
  have h3 := h2.conjTranspose_mul_mul_same V
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV] at h3
  have h4 := h3.diag_nonneg (i := i)
  have h5 := (Complex.nonneg_iff.mp h4).1
  rw [Matrix.sub_apply, one_apply_eq, Complex.sub_re, Complex.one_re] at h5
  unfold nsgFrameDiag; linarith

theorem nsg_trace_nearProjection (W : ℕ) : (nearProjection W).trace = (W : ℂ) := by
  rw [ns_nearProjection_eq, trace_mul_comm, ns_nearIncl_conj_mul, trace_one, Fintype.card_fin]

/-- `Σ_i (1 - S_ii) = g` (unitary `U`, `V`). -/
theorem nsg_sum_one_sub_frameDiag {U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hU : Uᴴ * U = 1) {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) :
    ∑ i, (1 - nsgFrameDiag U V i) = nsgConductance U := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  set P := nearProjection W
  set P' := Uᴴ * P * U
  have hPP : P * P = P := tcs_nearProjection_idem W
  have hP'P' : P' * P' = P' := by
    simp only [P']
    calc Uᴴ * P * U * (Uᴴ * P * U) = Uᴴ * P * (U * Uᴴ) * P * U := by
          simp only [Matrix.mul_assoc]
      _ = P' := by rw [hU', Matrix.mul_one, Matrix.mul_assoc Uᴴ P P, hPP]
  have htrP' : P'.trace = P.trace := by
    simp only [P']
    rw [trace_mul_cycle, hU', Matrix.one_mul]
  have hsumS : ∑ i, nsgFrameDiag U V i = (P' * P).trace.re := by
    unfold nsgFrameDiag
    rw [← Complex.re_sum]
    have : ∑ i, (Vᴴ * nsgProjBlock U * V) i i = (Vᴴ * nsgProjBlock U * V).trace := rfl
    rw [this, trace_mul_cycle, hV', Matrix.one_mul]
    unfold nsgProjBlock
    rw [ns_portBlock_eq, trace_mul_cycle, ← ns_nearProjection_eq, trace_mul_comm]
  have hJ : ((P' - P) ^ 2).trace = P'.trace - 2 * (P' * P).trace + P.trace := by
    rw [sq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP'P', hPP, trace_sub, trace_sub,
      trace_sub, trace_mul_comm P P']
    ring
  unfold nsgConductance
  rw [sum_sub_distrib, hsumS]
  rw [hJ, htrP', nsg_trace_nearProjection, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
    Complex.re_ofNat, Complex.im_ofNat]
  ring

/-- `T_ii = 1 - S_ii ≤ g`. -/
theorem nsg_one_sub_frameDiag_le {U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hU : Uᴴ * U = 1) {V : Matrix (Fin W) (Fin W) ℂ} (hV : Vᴴ * V = 1) (i : Fin W) :
    1 - nsgFrameDiag U V i ≤ nsgConductance U := by
  rw [← nsg_sum_one_sub_frameDiag hU hV]
  exact single_le_sum (f := fun k => 1 - nsgFrameDiag U V k)
    (fun k _ => sub_nonneg.2 (nsg_frameDiag_le_one hU hV k)) (mem_univ i)

theorem nsg_conductance_nonneg {U : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hU : Uᴴ * U = 1) : 0 ≤ nsgConductance U := by
  have hV : ((1 : Matrix (Fin W) (Fin W) ℂ))ᴴ * 1 = 1 := by simp
  rw [← nsg_sum_one_sub_frameDiag hU hV]
  exact sum_nonneg fun k _ => sub_nonneg.2 (nsg_frameDiag_le_one hU hV k)

/-!
## The generator expression at the path
-/

/-- The right side of the Schatten trace generator for `f_ε` at the path of length `j`
(`f_ε(x) = (x+ε)^p - ε^p`): the spectral form `nsgSpecGen` with `D = transportD0 b E`, the
eigenvalues of the near clock `A = nearClock b E W j q ω`, the diagonal `S_ii` of the projected
block of `P' = 𝕊*P𝕊` in the eigenvector frame of `A`, and `g = ½ Re Tr J²`,
`J = pathCurrent b E W j ω`. (For polynomial `f` vanishing at `0` this is the evaluation of
`wordGenerator` on `Σ_k c_k Tr (QP)^k` after the injection ends: `wordDrift` of `(QP)^k` is
`-(D/2) g k Tr A^k + (D/2) k Σ_{a+b=k} Tr A^a Tr(A^b Σ')`; see
`nsf_polyValue_wordGenerator_path`.) -/
def nsgGenExpr (b E p ε : ℝ) (q : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ :=
  if hA : (nearClock b E W j q ω).IsHermitian then
    nsgSpecGen (transportD0 b E) p ε (nsgConductance (scatteringMatrix b E W j ω))
      hA.eigenvalues
      (nsgFrameDiag (scatteringMatrix b E W j ω) (hA.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))
  else 0

theorem nsg_pathCurrent_eq (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) :
    nsgConductance (scatteringMatrix b E W j ω) =
      ((pathCurrent b E W j ω ^ 2).trace).re / 2 := rfl

/-- Dissipativity of the regularized trace generator at a path with unitary `𝕊`:
`𝒢 Tr f_ε(A) ≤ -κ Σ_i λ_i²(λ_i+ε)^{p-2}`, `κ = D₀p(1-p)/2`. -/
theorem nsg_genExpr_le {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    nsgGenExpr b E p ε q W j ω ≤
      -nsDecayRate b E p * nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  unfold nsgGenExpr
  rw [dite_eq_left hpsd.1, ns_clockSum_eq _ hpsd.1]
  have hV : ((hpsd.1.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))ᴴ *
      (hpsd.1.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have h := nsg_specGen_le (ι := Fin W) (D := transportD0 b E) (p := p) (ε := ε)
    (g := nsgConductance (scatteringMatrix b E W j ω)) (lam := hpsd.1.eigenvalues)
    (s := nsgFrameDiag (scatteringMatrix b E W j ω)
      (hpsd.1.eigenvectorUnitary : Matrix (Fin W) (Fin W) ℂ))
    (ns_transportD0_pos hb hE hE').le hp0 hp1 hε (fun i => hpsd.eigenvalues_nonneg i)
    (fun i => nsg_frameDiag_nonneg _ _ i) (nsg_conductance_nonneg hS)
    (fun i => nsg_one_sub_frameDiag_le hS hV i)
  refine h.trans_eq ?_
  unfold nsDecayRate
  ring

/-- `𝕊` is unitary almost surely under `growthPathLaw` (Hermitian GUE blocks; invertible `𝓜`
from the `ConditionalBlockGUECount`).
-/
theorem nsg_ae_scattering_unitary (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount) {b E : ℝ} (hb1 : b < 1 / 2)
    (hE : -2 < E) (hE' : E < 2) (hW : 0 < W) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1 := by
  filter_upwards [ae_growthPath_isHermitian W b,
    rv_ae_isUnit_fullPathMatrix hCount hb1 hE hE' hW j] with ω hH hM
  rw [rvD_scattering_eq]
  exact rvD_scattering_unitary hH hM

/-- Almost-sure dissipativity of the regularized trace generator at every length. -/
theorem nsg_ae_genExpr_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount) {b E p ε : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (hW : 0 < W) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, nsgGenExpr b E p ε q W j ω ≤
      -nsDecayRate b E p * nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω) := by
  filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW j] with ω hS
  exact nsg_genExpr_le hb hE hE' hp0 hp1 hε hq hS

end BlockBand.Endpoints
