module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKFresh
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormExplicit

/-!
# The closed-frame algebra of the `𝒦` brackets and the current Gram identity

At a no-birth step `j`, on the alive set, with `X_cl = b3ClosedX`, the closed frame
`V_cl = C_j(z)ᴴX_j` (`b3ClosedFrameAt`), its probe columns `c_k`, the closed near frames
`u_k = closedNearU`, `v_k = closedNearV` and `P𝕊_cl = P𝕊_jC_j(z)` (`b3ClosedPS`), three facts are
used:

* (a) the explicit step form `d𝒦_ij = u_i*Δ(X_cl, F_j)v_j` and (b) the near-rows identity
  `v_l = ι*(P𝕊_cl c_l)` (`closedStep_indicator`, `ae_closedNearV_eq_closedPS`);
* (c) the current Gram identity `ClosedCurrentGram`, stated here (it follows from
  `B3Cur.closed_current_frame` at length `j` and `closingMap_conj_near`):
  `V_clᴴ(P𝕊_cl)ᴴ(P𝕊_cl)V_cl = B + M𝖣M = C₀` (`gramC0`).

Proved here (deterministic): `closedNearU_eq_nearSel`, `dot_nearSel`, and the three leading-term
identities `bilinear_uv_eq_contr` (`u_i*v_l = Q⁰_{il}` from (b)), `bilinear_uu_eq_B`
(`u_i*u_k = B_ik`), `bilinear_vv_eq_C0` (`v_l*v_j = (C₀)_lj` from (b), (c)).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Bridge

variable {W np K : ℕ}

/-- Column `d` of the closed frame at length `j`. -/
def clCol (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) : Fin 2 × Fin W → ℂ :=
  fun a => b3ClosedFrameAt b E s h τ m W j Vs y a d

/-!
## The current Gram identity (c)
-/

/-- (c) at one step. -/
def CurrentGramAt (b E s h : ℝ) (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) : Prop :=
  ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j Vs →
    (b3ClosedFrameAt b E s h τ m W j Vs y)ᴴ *
        ((b3ClosedPS b E s h W j y.1.1 (phase y.2))ᴴ * b3ClosedPS b E s h W j y.1.1 (phase y.2)) *
        b3ClosedFrameAt b E s h τ m W j Vs y =
      gramC0 (b3ClosedGramAt b E s h τ m W j Vs y).1 (b3ClosedGramAt b E s h τ m W j Vs y).2
        (srcSignature K (Fin np))

/-- **(c) `ClosedCurrentGram`**: eventually, at every no-birth step, (c) holds. -/
def ClosedCurrentGram : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      CurrentGramAt b E s h τ m R W j (Vs W)

/-!
## Deterministic algebra
-/

theorem clCol_inr (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    clCol b E s h τ m W j Vs (Sum.inr k) y =
      (physClosingMapAt b E s h W j y.1.1 (phase y.2))ᴴ *ᵥ probeCol b E τ m W j k y.1 := by
  funext a
  simp [clCol, b3ClosedFrameAt, b3OpenFrameAt, Matrix.mul_apply, mulVec, dotProduct, probeCol]

theorem closedNearU_eq_nearSel (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    closedNearU b E s h τ m W j k y = nearSel W *ᵥ clCol b E s h τ m W j Vs (Sum.inr k) y := by
  rw [clCol_inr]; rfl

theorem nearSel_mulVec_apply' (w : Fin 2 × Fin W → ℂ) (x : Fin W) :
    (nearSel W *ᵥ w) x = w (0, x) := by
  simp [nearSel, mulVec, dotProduct]

theorem dot_nearSel (a c : Fin 2 × Fin W → ℂ) :
    star (nearSel W *ᵥ a) ⬝ᵥ (nearSel W *ᵥ c) = star a ⬝ᵥ (nearPortProj W *ᵥ c) := by
  simp only [dotProduct, Pi.star_apply, nearPortProj, mulVec_diagonal, nearSel_mulVec_apply',
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

theorem bilinear_one (u v : Fin W → ℂ) : bilinear u 1 v = star u ⬝ᵥ v := by
  simp [bilinear]

theorem nearPortProj_mul_b3ClosedPS (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    nearPortProj W * b3ClosedPS b E s h W j ω z = b3ClosedPS b E s h W j ω z := by
  simp only [b3ClosedPS, ← Matrix.mul_assoc, nearPortProj_mul_self]

theorem star_mulVec_dot {n : Type*} [Fintype n] (M : Matrix n n ℂ) (a c : n → ℂ) :
    star (M *ᵥ a) ⬝ᵥ (M *ᵥ c) = star a ⬝ᵥ ((Mᴴ * M) *ᵥ c) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- `u_i*u_k = B_ik`. -/
theorem bilinear_uu_eq_B (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (i k : Fin np)
    (y : ProbedPath W np × ℝ) :
    bilinear (closedNearU b E s h τ m W j i y) 1 (closedNearU b E s h τ m W j k y) =
      (b3ClosedGramAt b E s h τ m W j Vs y).2 (Sum.inr i) (Sum.inr k) := by
  rw [bilinear_one, closedNearU_eq_nearSel b E s h τ m W j Vs,
    closedNearU_eq_nearSel b E s h τ m W j Vs, dot_nearSel]
  simp only [b3ClosedGramAt, gramPair, nearGram]
  rw [entry_eq_dot]
  rfl

/-- `u_i*v_l = Q⁰_{il}` under (b). -/
theorem bilinear_uv_eq_contr (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (i l : Fin np)
    (y : ProbedPath W np × ℝ)
    (hv : closedNearV b E s h τ m W j l y =
      nearSel W *ᵥ (b3ClosedPS b E s h W j y.1.1 (phase y.2) *ᵥ
        clCol b E s h τ m W j Vs (Sum.inr l) y)) :
    bilinear (closedNearU b E s h τ m W j i y) 1 (closedNearV b E s h τ m W j l y) =
      b3ContrCoord b E s h τ m W j Vs 0 (Sum.inr i) (Sum.inr l) y := by
  rw [bilinear_one, closedNearU_eq_nearSel b E s h τ m W j Vs, hv, dot_nearSel, mulVec_mulVec,
    nearPortProj_mul_b3ClosedPS, b3ContrCoord, entry_eq_dot]
  rfl

/-- `v_l*v_j = (C₀)_lj` under (b) and (c). -/
theorem bilinear_vv_eq_C0 (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (l j' : Fin np)
    (y : ProbedPath W np × ℝ)
    (hv : ∀ l, closedNearV b E s h τ m W j l y =
      nearSel W *ᵥ (b3ClosedPS b E s h W j y.1.1 (phase y.2) *ᵥ
        clCol b E s h τ m W j Vs (Sum.inr l) y))
    (hc : (b3ClosedFrameAt b E s h τ m W j Vs y)ᴴ *
        ((b3ClosedPS b E s h W j y.1.1 (phase y.2))ᴴ * b3ClosedPS b E s h W j y.1.1 (phase y.2)) *
        b3ClosedFrameAt b E s h τ m W j Vs y =
      gramC0 (b3ClosedGramAt b E s h τ m W j Vs y).1 (b3ClosedGramAt b E s h τ m W j Vs y).2
        (srcSignature K (Fin np))) :
    bilinear (closedNearV b E s h τ m W j l y) 1 (closedNearV b E s h τ m W j j' y) =
      gramC0 (b3ClosedGramAt b E s h τ m W j Vs y).1 (b3ClosedGramAt b E s h τ m W j Vs y).2
        (srcSignature K (Fin np)) (Sum.inr l) (Sum.inr j') := by
  rw [bilinear_one, hv l, hv j', dot_nearSel, mulVec_mulVec, nearPortProj_mul_b3ClosedPS,
    star_mulVec_dot, ← hc, entry_eq_dot]
  rfl

end BlockBand.SourceProcess.PhysApprox.B3
